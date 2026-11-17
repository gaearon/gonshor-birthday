/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostBlocks

import Mathlib.SetTheory.Ordinal.Principal

/-!
# Arbitrary ordinal minus-block clients

The all-minus expansion includes the empty word and every transfinite ordinal length.
At minus omega its length is omega squared, demonstrating the ordinary limit multiplication.
-/

public noncomputable section

namespace Tests

open Surreal Ordinal

/-- An arbitrary ordinal-length minus word expands into that many omega blocks. -/
theorem negative_ordinal_expansion (o : NatOrdinal.{0}) :
    omegaExpansionLength (-o.toSurreal) Set.univ = NatOrdinal.of (1 + Ordinal.omega0 * o.val) := by
  simpa only [birthday_neg, birthday_toSurreal] using
    omegaExpansionLength_univ_eq_of_plusCount_zero (plusCount_neg_toSurreal o)

/-- The first infinite minus block expands to omega squared. -/
theorem negative_omega_expansion :
    omegaExpansionLength (-(NatOrdinal.of Ordinal.omega0 : NatOrdinal.{0}).toSurreal) Set.univ =
      ω^ (2 : NatOrdinal.{0}) := by
  rw [negative_ordinal_expansion, NatOrdinal.val_of]
  have hp : (ω^ (2 : NatOrdinal.{0})).val = Ordinal.omega0 * Ordinal.omega0 := by
    simp [NatOrdinal.val_wpow, ← one_add_one_eq_two, Ordinal.opow_add_one]
  have h1 : (1 : Ordinal.{0}) < (ω^ (2 : NatOrdinal.{0})).val := by
    simpa only [NatOrdinal.wpow_zero, NatOrdinal.val_one] using
      NatOrdinal.val.strictMono (NatOrdinal.wpow_lt_wpow.mpr
        (zero_lt_two : (0 : NatOrdinal.{0}) < 2))
  have he : 1 + (ω^ (2 : NatOrdinal.{0})).val = (ω^ (2 : NatOrdinal.{0})).val := by
    rw [NatOrdinal.val_wpow] at h1 ⊢
    exact Ordinal.add_omega0_opow h1
  rw [← hp, he, NatOrdinal.of_val]

end Tests
