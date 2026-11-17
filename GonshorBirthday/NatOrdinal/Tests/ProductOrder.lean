/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.NatOrdinal.ProductOrder

import Mathlib.Tactic.NormNum

/-!
# Product-order clients

The lexicographic order on two successive copies of omega attains the natural-product bound.
The public theorem applies through an equivalence, without exposing the induction predicate.
-/

public noncomputable section

namespace Tests

open Ordinal NatOrdinal

/-- The two-row lexicographic grid is covered by the general product-order theorem. -/
theorem two_rows_omega_bound :
    of (typeLT (Fin 2 ×ₗ ℕ)) ≤ (2 : NatOrdinal.{0}) * of Ordinal.omega0 := by
  have h := of_type_le_mul_of_monotone_equiv (ofLex : (Fin 2 ×ₗ ℕ) ≃ Fin 2 × ℕ)
    Prod.Lex.toLex_mono
  norm_num only [type_fin, type_nat_lt, of_natCast] at h ⊢
  exact h

/-- For this grid the bound is attained, including both infinite rows. -/
theorem two_rows_omega_exact :
    of (typeLT (Fin 2 ×ₗ ℕ)) = (2 : NatOrdinal.{0}) * of Ordinal.omega0 := by
  rw [type_lt_prod_lex, type_fin, type_nat_lt]
  simpa only [Ordinal.opow_one, of_one, wpow_one, Nat.cast_ofNat, mul_comm] using
    of_omega0_opow_mul_natCast (1 : Ordinal.{0}) 2

end Tests
