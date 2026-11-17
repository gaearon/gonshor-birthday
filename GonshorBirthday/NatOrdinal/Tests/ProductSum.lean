/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.NatOrdinal.ProductSum

/-!
# Ordered product-sum clients

The global inequality applies to infinitely many rows and columns with arbitrary ordinal block
lengths. A grid of singleton cells has type omega squared in row order, so its ordinary ordered
sum cannot be replaced by a cardinal count of the cells.
-/

public noncomputable section

namespace Tests

open Ordinal NatOrdinal

/-- Infinite rows and columns may have arbitrary ordinal lengths, including zero. -/
theorem infinite_grid_bound (a b : ℕ → NatOrdinal.{0}) :
    of (typeLT (Σₗ k : ℕ ×ₗ ℕ, (a (ofLex k).1 * b (ofLex k).2).val.ToType)) ≤
      of (typeLT (Σₗ i : ℕ, (a i).val.ToType)) *
        of (typeLT (Σₗ j : ℕ, (b j).val.ToType)) :=
  of_type_sigma_mul_le a b ofLex Prod.Lex.toLex_mono

private def sigmaOneIso (I : Type) [LinearOrder I] :
    (Σₗ _ : I, (1 : Ordinal.{0}).ToType) ≃o I where
  toFun x := (ofLex x).1
  invFun i := toLex ⟨i, default⟩
  left_inv x := by
    obtain ⟨i, x⟩ := x
    change (toLex ⟨i, default⟩ : Σₗ _ : I, (1 : Ordinal.{0}).ToType) = toLex ⟨i, x⟩
    congr
    exact Subsingleton.elim _ _
  right_inv _ := rfl
  map_rel_iff' := by
    rintro ⟨i, x⟩ ⟨j, y⟩
    change i ≤ j ↔ Sigma.Lex ((· < ·) : I → I → Prop)
      (fun _ (x y : (1 : Ordinal.{0}).ToType) ↦ x ≤ y) ⟨i, x⟩ ⟨j, y⟩
    simp only [Sigma.lex_iff, le_of_subsingleton]
    simpa using (le_iff_lt_or_eq (a := i) (b := j))

/-- Singleton cells arranged in infinitely many infinite rows have type omega squared. -/
theorem unit_grid_length :
    of (typeLT (Σₗ _ : ℕ ×ₗ ℕ, (1 : Ordinal.{0}).ToType)) = ω^ (2 : NatOrdinal.{0}) := by
  rw [(sigmaOneIso (ℕ ×ₗ ℕ)).toRelIsoLT.ordinalType_congr,
    type_lt_prod_lex, type_nat_lt]
  have h : (Ordinal.omega0 : Ordinal.{0}) * Ordinal.omega0 =
      Ordinal.omega0 ^ (2 : Ordinal.{0}) := by
    simpa only [Ordinal.opow_one, one_add_one_eq_two] using
      (Ordinal.opow_add_one (Ordinal.omega0 : Ordinal.{0}) 1).symm
  rw [h, of_omega0_opow]
  congr 1

end Tests
