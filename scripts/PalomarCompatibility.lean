/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Copyright (c) 2023 Kim Morrison. All rights reserved.
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import Lean.CoreM
import Lean.PrivateName

/-!
# Independent statement and declaration-closure comparison

Local explicit statement definitions are allowed, but their complete kernel
constant information must match in Challenge and Solution. The advertised proof
is the sole comparison hole. Project module-private dependencies are rejected.
The two environments remain alive throughout comparison; imported expressions
are never returned from a callback that frees their memory regions.
-/

open Lean

-- Adapted from ImportGraph.Lean.WithImportModules (Kim Morrison and Paul Lezeau).
private def withImportedModules {α} (modules : Array Name) (f : CoreM α) : IO α := do
  initSearchPath (← findSysroot)
  unsafe Lean.withImportModules (modules.map (fun m => {module := m})) {} (trustLevel := 1024)
    fun env => Prod.fst <$> Core.CoreM.toIO
      (ctx := {fileName := "<audit>", fileMap := default}) (s := {env := env}) f

private def dependencies (info : ConstantInfo) : Array Name := Id.run do
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

-- Match LeanExport.Basic.removeMData exactly: erase metadata and normalize the
-- optimization-only letE.nonDep flag. No logical reduction or proof erasure occurs.
private def exportExpr : Expr → Expr
  | .mdata _ body => exportExpr body
  | .app fn arg => .app (exportExpr fn) (exportExpr arg)
  | .lam name type body bi => .lam name (exportExpr type) (exportExpr body) bi
  | .forallE name type body bi => .forallE name (exportExpr type) (exportExpr body) bi
  | .letE name type value body _ =>
      .letE name (exportExpr type) (exportExpr value) (exportExpr body) false
  | .proj name index value => .proj name index (exportExpr value)
  | expr => expr

private def exportInfo : ConstantInfo → ConstantInfo
  | .axiomInfo v => .axiomInfo {v with type := exportExpr v.type}
  | .defnInfo v => .defnInfo {v with type := exportExpr v.type, value := exportExpr v.value}
  | .thmInfo v => .thmInfo {v with type := exportExpr v.type, value := exportExpr v.value}
  | .opaqueInfo v => .opaqueInfo {v with type := exportExpr v.type, value := exportExpr v.value}
  | .quotInfo v => .quotInfo {v with type := exportExpr v.type}
  | .inductInfo v => .inductInfo {v with type := exportExpr v.type}
  | .ctorInfo v => .ctorInfo {v with type := exportExpr v.type}
  | .recInfo v => .recInfo
      {v with
        type := exportExpr v.type
        rules := v.rules.map (fun rule => {rule with rhs := exportExpr rule.rhs})}

private def projectPrivate (env : Environment) (wrapper name : Name) : Bool :=
  if !isPrivateName name then false else
  match env.getModuleIdxFor? name with
  | none => true
  | some index => match env.allImportedModuleNames[index.toNat]? with
    | none => true
    | some owner => owner == wrapper || (`GonshorBirthday).isPrefixOf owner

private def projectDeclaration (env : Environment) (wrapper name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | none => false
  | some index => match env.allImportedModuleNames[index.toNat]? with
    | none => false
    | some owner => owner == wrapper || (`GonshorBirthday).isPrefixOf owner

private def auditPrivateClosure (env : Environment) (wrapper : Name) (roots : Array Name) :
    Except String Unit := do
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    if projectPrivate env wrapper name then
      throw s!"module-private statement dependency: {name}"
    if projectDeclaration env wrapper name then
      let some info := env.checked.get.find? name
        | throw s!"missing project statement dependency: {name}"
      pending := pending ++ dependencies info

private def theoremInfo (env : Environment) (wrapper target : Name) : Except String TheoremVal := do
  let some (.thmInfo info) := env.checked.get.find? target
    | throw s!"missing advertised theorem {target} in {wrapper}"
  let some index := env.getModuleIdxFor? target
    | throw s!"cannot determine defining module of {target}"
  unless env.allImportedModuleNames[index.toNat]? == some wrapper do
    throw s!"advertised theorem {target} is not defined in {wrapper}"
  return info

private def compareClosure (left right : Environment) (challenge solution target : Name) :
    Except String Nat := do
  let leftRoot ← theoremInfo left challenge target
  let rightRoot ← theoremInfo right solution target
  auditPrivateClosure left challenge leftRoot.type.getUsedConstants
  auditPrivateClosure right solution rightRoot.type.getUsedConstants
  unless {leftRoot.toConstantVal with type := exportExpr leftRoot.type} ==
      {rightRoot.toConstantVal with type := exportExpr rightRoot.type} do
    throw "independently compiled theorem types or universe parameters differ"
  let mut pending := leftRoot.type.getUsedConstants
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some leftInfo := left.checked.get.find? name
      | throw s!"constant not found in Challenge statement closure: {name}"
    let some rightInfo := right.checked.get.find? name
      | throw s!"constant not found in Solution statement closure: {name}"
    if projectPrivate left challenge name || projectPrivate right solution name then
      throw s!"module-private statement dependency: {name}"
    if name == target then
      pending := pending ++ rightInfo.type.getUsedConstants
    else
      unless leftInfo == rightInfo || exportInfo leftInfo == exportInfo rightInfo do
        throw s!"statement declaration does not match: {name}"
      pending := pending ++ dependencies rightInfo
  return seen.size

private def parseConfig : List String → Except String (Name × Name × Name)
  | [] => .ok (`Challenge, `Solution, `GonshorBirthday.Palomar.birthday_mul_le)
  | [challenge, solution, target] =>
      .ok (challenge.toName, solution.toName, target.toName)
  | _ => .error "usage: palomar-compatibility [CHALLENGE_MODULE SOLUTION_MODULE THEOREM]"

public def main (args : List String) : IO UInt32 := do
  match parseConfig args with
  | .error message =>
      IO.eprintln message
      return 2
  | .ok config =>
      try
        let result ← withImportedModules #[config.1] do
          let left ← getEnv
          Core.liftIOCore <| withImportedModules #[config.2.1] do
            let right ← getEnv
            -- Only a count or freshly rendered error text leaves these callbacks.
            return compareClosure left right config.1 config.2.1 config.2.2
        match result with
        | .ok count =>
            IO.println s!"palomar-compatibility: exact types and {count} dependencies agree"
            return 0
        | .error message =>
            IO.eprintln s!"palomar-compatibility: {message}"
            return 1
      catch error =>
        IO.eprintln s!"palomar-compatibility: {error}"
        return 1
