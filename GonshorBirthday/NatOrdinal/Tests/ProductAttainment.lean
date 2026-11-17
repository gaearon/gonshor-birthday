/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.NatOrdinal.ProductAttainment

import Mathlib.Tactic.Ring

/-!
# Clients for maximal product orders

The square of the well order `ω^(ω+1)` has a linear extension attaining its natural square.
Either ordinary lexicographic square is strictly shorter, so the example distinguishes the
general extension from simply choosing an order for the two coordinate loops.
The `WithTop ℕ` client also includes all lower Cantor terms in the product.
-/

public noncomputable section

namespace Tests

open Ordinal NatOrdinal

/-- Equal mixed exponents are allowed, including a shared infinite leading term. -/
theorem mixed_exponent_square_attained :
    ∃ e : (ω^ (of Ordinal.omega0 + 1 : NatOrdinal.{0})).val.ToType ×
        (ω^ (of Ordinal.omega0 + 1 : NatOrdinal.{0})).val.ToType ≃
        (ω^ ((of Ordinal.omega0 + 1 : NatOrdinal.{0}) + (of Ordinal.omega0 + 1))).val.ToType,
      Monotone e :=
  exists_monotone_equiv_wpow_product _ _

/-- The ordinary lexicographic square does not attain the natural square in this example. -/
theorem lex_square_lt_natural_square :
    of ((ω^ (of Ordinal.omega0 + 1 : NatOrdinal.{0})).val *
      (ω^ (of Ordinal.omega0 + 1 : NatOrdinal.{0})).val) <
      ω^ ((of Ordinal.omega0 + 1 : NatOrdinal.{0}) + (of Ordinal.omega0 + 1)) := by
  rw [val_wpow, ← Ordinal.opow_add, of_omega0_opow, wpow_lt_wpow]
  have ho : (Ordinal.omega0 + 1) + (Ordinal.omega0 + 1) =
      Ordinal.omega0 * 2 + 1 := by
    rw [add_assoc Ordinal.omega0 1, ← add_assoc 1 Ordinal.omega0 1,
      Ordinal.one_add_omega0, ← add_assoc, Ordinal.mul_two]
  rw [val_add_one, val_of, ho, of_add_one]
  have hn : of (Ordinal.omega0 * 2) = (of Ordinal.omega0 : NatOrdinal.{0}) * 2 := by
    simpa only [Ordinal.opow_one, of_one, wpow_one, Nat.cast_ofNat] using
      of_omega0_opow_mul_natCast (1 : Ordinal.{0}) 2
  rw [hn]
  calc
    (of Ordinal.omega0 : NatOrdinal.{0}) * 2 + 1 < of Ordinal.omega0 * 2 + (1 + 1) :=
      add_lt_add_of_le_of_lt le_rfl (lt_add_one 1)
    _ = (of Ordinal.omega0 + 1) + (of Ordinal.omega0 + 1) := by
      rw [mul_two]
      ac_rfl

/-- A product with non-pure factors has an extension realizing its full natural product. -/
theorem withTop_nat_product_extension :
    ∃ e : WithTop ℕ × WithTop ℕ ≃
        (of (typeLT (WithTop ℕ)) * of (typeLT (WithTop ℕ))).val.ToType,
      Monotone e :=
  exists_monotone_equiv_product

/-- The non-pure square retains two linear terms and its constant term. -/
theorem withTop_nat_natural_square :
    of (typeLT (WithTop ℕ)) * of (typeLT (WithTop ℕ)) =
      ω^ (2 : NatOrdinal.{0}) + of Ordinal.omega0 * 2 + 1 := by
  rw [type_lt_withTop, type_nat_lt, of_add_one]
  have hpow : (of Ordinal.omega0 : NatOrdinal.{0}) * of Ordinal.omega0 = ω^ 2 := by
    simpa only [wpow_one, one_add_one_eq_two] using (wpow_add (1 : NatOrdinal.{0}) 1).symm
  calc
    (of Ordinal.omega0 + 1 : NatOrdinal.{0}) * (of Ordinal.omega0 + 1) =
        of Ordinal.omega0 * of Ordinal.omega0 + of Ordinal.omega0 * 2 + 1 := by ring
    _ = _ := by rw [hpow]

end Tests
