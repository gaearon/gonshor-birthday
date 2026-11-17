/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import Lean.CoreM
import Lean.Util.CollectAxioms

/-!
# Exact transitive axiom gate for every project declaration

Enumerate source modules, including otherwise unimported modules, and Solution.
Walk the union of their kernel declaration-dependency graphs with one visited set.
This detects forbidden axioms in types and proofs without a provisional recursive
cache, including mutually recursive dependency clusters. Challenge is excluded:
its sole advertised hole is checked separately by the exact wrapper gate.
-/

open Lean

-- Adapted from ImportGraph.Lean.WithImportModules (Kim Morrison and Paul Lezeau).
private def withImportedModules {α} (modules : Array Name) (f : CoreM α) : IO α := do
  initSearchPath (← findSysroot)
  unsafe Lean.withImportModules (modules.map (fun m => {module := m})) {} (trustLevel := 1024)
    fun env => Prod.fst <$> Core.CoreM.toIO
      (ctx := {fileName := "<audit>", fileMap := default}) (s := {env := env}) f


private def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

private def pathToModule (path : System.FilePath) : Name :=
  (path.withExtension "").components.foldl (fun name part => Name.mkStr name part) .anonymous

private partial def collectLeanModules (directory : System.FilePath) : IO (Array Name) := do
  let mut modules := #[]
  for entry in (← directory.readDir) do
    if ← entry.path.isDir then
      modules := modules ++ (← collectLeanModules entry.path)
    else if entry.path.extension == some "lean" then
      modules := modules.push (pathToModule entry.path)
  return modules

private def declarationDependencies (info : ConstantInfo) : Array Name := Id.run do
  let mut result := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    result := result ++ value.getUsedConstants
  match info with
  | .inductInfo value => result := result ++ value.ctors ++ value.all.toArray
  | .ctorInfo value => result := result.push value.induct
  | .recInfo value =>
      for rule in value.rules do
        result := result.push rule.ctor ++ rule.rhs.getUsedConstants
  | _ => pure ()
  return result

private def audit : CoreM (Nat × Nat × Array String × String) := do
  let env ← getEnv
  let candidates := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some index =>
        match env.allImportedModuleNames[index.toNat]? with
        | some owner =>
            if owner == `Solution || (`GonshorBirthday).isPrefixOf owner then names.push name
            else names
        | none => names
    | none => names
  let mut pending := candidates
  let mut seen : NameSet := {}
  let mut violations := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.checked.get.find? name
      | violations := violations.push s!"missing dependency declaration {name}"
        continue
    if let .axiomInfo _ := info then
      unless allowedAxioms.contains name do
        violations := violations.push s!"forbidden axiom {name}"
    pending := pending ++ declarationDependencies info
  let finalAxioms ← collectAxioms `Surreal.birthday_mul_le
  unless finalAxioms.size == allowedAxioms.length &&
      allowedAxioms.all (fun name => finalAxioms.contains name) do
    violations := violations.push s!"unexpected final theorem axiom set: {finalAxioms}"
  return (candidates.size, seen.size, violations, s!"{finalAxioms}")

public def main : IO UInt32 := do
  try
    let modules := #[`GonshorBirthday, `Solution] ++
      (← collectLeanModules ("GonshorBirthday" : System.FilePath))
    let (count, closureCount, violations, finalAxioms) ← withImportedModules modules audit
    if count == 0 then
      IO.eprintln "axioms: no project declarations found"
      return 1
    unless violations.isEmpty do
      for violation in violations do IO.eprintln s!"axioms: {violation}"
      return 1
    IO.println s!"axioms: checked {count} declarations and {closureCount} dependencies"
    IO.println s!"axioms: only {allowedAxioms} are permitted"
    IO.println s!"axioms: Surreal.birthday_mul_le uses exactly {finalAxioms}"
    return 0
  catch error =>
    IO.eprintln s!"axioms: {error}"
    return 1
