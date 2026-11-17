/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.NatOrdinal.FiniteBlocks
public import Mathlib.Data.Fin.VecNotation

import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite-block clients

Descending blocks of lengths omega and one have type omega plus one. Reversing those blocks
gives type omega, demonstrating the need for the exponent-order hypothesis. The final client
combines the two public theorems to represent every ordinal by actual consecutive blocks.
-/

universe u

public noncomputable section

namespace Tests

open Ordinal NatOrdinal

/-- Putting the infinite block first retains the final singleton. -/
theorem descending_two_blocks :
    of (typeLT (Σₗ i : Fin 2, (ω^ (![1, 0] i : NatOrdinal.{0})).val.ToType)) =
      of Ordinal.omega0 + 1 := by
  have h := of_type_fin_sigma_wpow (![1, 0] : Fin 2 → NatOrdinal.{0}) (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all)
  simpa [Fin.sum_univ_two] using h

/-- Reversing those two blocks absorbs the singleton. -/
theorem ascending_two_blocks :
    typeLT (Σₗ i : Fin 2, (ω^ (![0, 1] i : NatOrdinal.{0})).val.ToType) =
      Ordinal.omega0 := by
  rw [Ordinal.type_fin_sigma]
  simp only [List.ofFn_succ, List.ofFn_zero, List.sum_cons, List.sum_nil, Ordinal.type_toType]
  simp

/-- Every ordinal is realized by a finite sequence of descending omega-power blocks. -/
theorem ordinal_has_decreasing_blocks (a : NatOrdinal.{u}) :
    ∃ n : ℕ, ∃ f : Fin n → NatOrdinal.{u}, Antitone f ∧
      of (typeLT (Σₗ i : Fin n, (ω^ (f i)).val.ToType)) = a := by
  obtain ⟨n, f, hf, ha⟩ := exists_antitone_wpow_sum a
  exact ⟨n, f, hf, (of_type_fin_sigma_wpow f hf).trans ha.symm⟩

end Tests
