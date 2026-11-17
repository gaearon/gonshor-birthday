# Working rules

- Preserve the exact unrestricted native CG multiplication birthday theorem.
- No admitted proofs or additional axioms in `GonshorBirthday/` or `Solution.lean`.
  Only `propext`, `Classical.choice`, and `Quot.sound` are permitted transitively.
  The sole deliberate hole is the advertised theorem in `Challenge.lean`.
- Search the pinned Mathlib and CG APIs first. Do not modify dependency sources or
  change their pins during a mathematical change.
- Use the Lean module system, direct imports, opaque public interfaces with
  characteristic lemmas, and separate compiled clients. Keep standard linters and
  warnings enabled. A new definition needs a distinguishing nondegenerate example.
- The `GonshorBirthday.*` Lake glob builds every library module. Keep the root
  module free of re-exports; audits enumerate the source tree independently.
- The Challenge imports only Mathlib. Regenerate it with
  `scripts/check-palomar-challenge.sh --update`; preserve its proved equivalence to
  the native statement. Named public proof constants keep its declaration closure
  portable across independent compilation.
- Run `scripts/verify.sh` and `scripts/audit-probes.sh` before a green checkpoint.
  Audit changes require a negative control. Before submission also run
  `scripts/verify-comparator.sh` and inspect the exact diff.
- Keep PROOF.md aligned with the current Lean proof. Use one mathematical account,
  without versioned manuscripts or agent review reports.
- Commit coherent changes only; do not stage unrelated work. Publishing or submitting
  the repository requires an explicit user instruction.
