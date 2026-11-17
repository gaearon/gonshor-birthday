/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostPlus
public import GonshorBirthday.Surreal.Birthday.ExpansionLength

import GonshorBirthday.Surreal.Birthday.ReducedCostBlocks

/-!
# Final plus portions after transfinite minus blocks

The expanded word with an omega-length minus block followed by one plus has length
omega squared plus omega. Its final plus contribution survives after the limit block.
The retained-minus budget client permits an arbitrary mixed-sign head.
-/

public noncomputable section

namespace Tests

open Surreal Ordinal

/-- An arbitrary minus block followed by a nonempty plus block has two ordered contributions. -/
theorem minus_then_plus_expansion (o : NatOrdinal.{0}) (a : Ordinal.{0}) (ha : a ≠ 0) :
    omegaExpansionLength (appendPluses (-o.toSurreal) a) Set.univ =
      NatOrdinal.of (1 + Ordinal.omega0 * o.val + Ordinal.omega0 ^ a) := by
  let x : Surreal.{0} := -o.toSurreal
  let y := appendPluses x a
  have hb : x.birthday ≤ y.birthday := by
    rw [birthday_appendPluses]
    exact NatOrdinal.of.monotone le_self_add
  have h := reducedOmegaCost_appendPluses y.birthday.toSurreal x ha
  rw [reducedOmegaCost_eq_omegaExpansionLength_univ (le_refl y.birthday.toSurreal),
    reducedOmegaCost_eq_omegaExpansionLength_univ (NatOrdinal.toSurreal.monotone hb),
    omegaExpansionLength_univ_eq_of_plusCount_zero (plusCount_neg_toSurreal o),
    plusCount_appendPluses, plusCount_neg_toSurreal, NatOrdinal.val_zero, zero_add,
    NatOrdinal.val_of, NatOrdinal.val_wpow, NatOrdinal.val_of] at h
  simpa only [x, birthday_neg, birthday_toSurreal] using h

/-- One plus after an omega-length minus block adds omega after omega squared. -/
theorem limit_minus_then_plus_expansion :
    omegaExpansionLength (appendPlus
      (-(NatOrdinal.of Ordinal.omega0 : NatOrdinal.{0}).toSurreal)) Set.univ =
      NatOrdinal.of (Ordinal.omega0 ^ (2 : Ordinal.{0}) + Ordinal.omega0) := by
  have h := minus_then_plus_expansion (NatOrdinal.of Ordinal.omega0) 1 one_ne_zero
  rw [appendPluses_one, NatOrdinal.val_of, Ordinal.opow_one] at h
  have he : Ordinal.omega0 * Ordinal.omega0 = Ordinal.omega0 ^ (2 : Ordinal.{0}) := by
    simp only [← one_add_one_eq_two, Ordinal.opow_add_one, Ordinal.opow_one]
  have hω : Ordinal.omega0 ≤ Ordinal.omega0 ^ (2 : Ordinal.{0}) := by
    simpa only [Ordinal.opow_one] using (Ordinal.opow_le_opow_right Ordinal.omega0_pos
      (one_le_two : (1 : Ordinal.{0}) ≤ 2))
  rw [he, Ordinal.one_add_of_omega0_le hω] at h
  exact h

/-- A retained minus after any head and its following plus both retain their full block budgets. -/
theorem minus_then_plus_budget (C x : Surreal.{0}) (hC : x ≤ C) :
    NatOrdinal.of ((reducedOmegaCost C x).val + (ω^ (plusCount x + 1)).val +
      (ω^ (plusCount x + 1)).val) ≤ reducedOmegaCost C (appendPlus (appendMinus x)) := by
  have hx : x ∈ rightPrefixes (appendPlus (appendMinus x)) := by
    rw [rightPrefixes_appendPlus]
    exact mem_rightPrefixes_iff.mpr ⟨birthdayTruncation_appendMinus x, appendMinus_lt x⟩
  have hp : plusCount x < plusCount (appendPlus (appendMinus x)) := by
    rw [plusCount_appendPlus, plusCount_appendMinus]
    exact lt_add_one _
  simpa only [plusCount_appendPlus, plusCount_appendMinus] using
    reducedOmegaCost_add_block_add_wpow_le_of_mem_rightPrefixes hx hC hp

end Tests
