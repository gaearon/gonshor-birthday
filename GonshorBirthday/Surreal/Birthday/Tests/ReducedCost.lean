/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCost
public import GonshorBirthday.Surreal.Birthday.ReducedCostPrefix
public import GonshorBirthday.Surreal.Birthday.Append

import Mathlib.SetTheory.Ordinal.Principal

/-!
# Reduced-cost cutoff clients

For the actual surreal exponent minus one, a margin of one retains its minus and costs omega.
Every smaller positive margin deletes that minus and leaves cost one. The endpoint omega also
distinguishes ordinary concatenation of the initial unit from natural addition, which gives
omega plus one. Canonical left prefixes have strictly smaller costs at every cutoff.
-/

public noncomputable section

namespace Tests

open Surreal Ordinal

/-- The cost of the empty exponent word is one, not zero. -/
theorem empty_exponent_cost (C : Surreal.{0}) : reducedOmegaCost C 0 = 1 :=
  reducedOmegaCost_zero C

/-- The margin threshold for the actual exponent minus one is exactly one. -/
theorem minus_one_margin (d : Surreal.{0}) :
    reducedOmegaCost (-1 + d) (-1) =
      if 1 ≤ d then NatOrdinal.of Ordinal.omega0 else 1 := by
  rw [reducedOmegaCost_neg_one]
  have h : (0 : Surreal.{0}) ≤ -1 + d ↔ 1 ≤ d := by
    simpa only [sub_eq_add_neg, add_comm] using
      (sub_nonneg : (0 : Surreal.{0}) ≤ d - 1 ↔ 1 ≤ d)
  simp only [h]

/-- Moving a positive margin just below one removes the whole omega block. -/
theorem margin_cutoff_jump {η : Surreal.{0}} (hη : 0 < η) (hη1 : η < 1) :
    0 < 1 - η ∧
      reducedOmegaCost ((-1 : Surreal.{0}) + 1) (-1) = NatOrdinal.of Ordinal.omega0 ∧
      reducedOmegaCost (-1 + (1 - η)) (-1) = 1 := by
  refine ⟨sub_pos.mpr hη1, ?_, ?_⟩
  · rw [minus_one_margin, ite_eq_left le_rfl]
  · rw [minus_one_margin, ite_eq_right (not_le.mpr (sub_lt_self _ hη))]

/-- A later retained plus strictly increases the cost, independently of the cutoff. -/
theorem one_plus_before_two (C : Surreal.{0}) :
    NatOrdinal.of Ordinal.omega0 < reducedOmegaCost C 2 := by
  simpa only [reducedOmegaCost_one] using
    reducedOmegaCost_lt_of_mem_leftPrefixes C one_mem_leftPrefixes_two

/-- After any ordinal block of minuses, one plus has the same pure omega baseline. -/
theorem baseline_after_negative_ordinal (o : NatOrdinal.{0}) :
    reducedOmegaCost (appendPlus (-o.toSurreal)) (appendPlus (-o.toSurreal)) =
      NatOrdinal.of Ordinal.omega0 := by
  rw [reducedOmegaCost_self_eq_wpow, plusCount_appendPlus, plusCount_neg_toSurreal,
    zero_add, NatOrdinal.wpow_one]

/-- The complete ordinal exponent omega has baseline omega-to-omega. -/
theorem omega_exponent_baseline :
    reducedOmegaCost (NatOrdinal.of Ordinal.omega0 : NatOrdinal.{0}).toSurreal
      (NatOrdinal.of Ordinal.omega0 : NatOrdinal.{0}).toSurreal =
        ω^ (NatOrdinal.of Ordinal.omega0 : NatOrdinal.{0}) := by
  rw [reducedOmegaCost_self_eq_wpow, plusCount_toSurreal]

/-- At a limit exponent, every cost term has exponent at least omega at any cutoff. -/
theorem omega_exponent_no_finite_cantor_term (C : Surreal.{0}) :
    ∀ e ∈ NatOrdinal.cantorSupport
      (reducedOmegaCost C (NatOrdinal.of Ordinal.omega0 : NatOrdinal.{0}).toSurreal),
      NatOrdinal.of Ordinal.omega0 ≤ e := by
  simpa only [plusCount_toSurreal] using plusCount_le_cantorSupport_reducedOmegaCost C
    (NatOrdinal.of Ordinal.omega0 : NatOrdinal.{0}).toSurreal

/-- One plus after an arbitrarily long minus block leaves a whole omega block after each prefix. -/
theorem room_after_negative_ordinal_and_plus (C : Surreal.{0}) (o : NatOrdinal.{0})
    {h : NatOrdinal.{0}} (hh : h < reducedOmegaCost C (appendPlus (-o.toSurreal))) :
    NatOrdinal.of (h.val + Ordinal.omega0) ≤ reducedOmegaCost C (appendPlus (-o.toSurreal)) := by
  simpa only [plusCount_appendPlus, plusCount_neg_toSurreal, zero_add, NatOrdinal.wpow_one,
    NatOrdinal.val_of] using oadd_wpow_plusCount_le_reducedOmegaCost hh

/-- The first minus after one contributes omega squared, using its original plus rank. -/
theorem retained_minus_after_one :
    ω^ (2 : NatOrdinal.{0}) ≤ reducedOmegaCost 1 (appendMinus (1 : Surreal.{0})) := by
  have hp : (1 : Surreal.{0}) ∈ rightPrefixes (appendMinus 1) := by
    apply mem_rightPrefixes.mpr
    refine ⟨(1 : Surreal.{0}).birthday, ?_, birthdayTruncation_appendMinus 1, appendMinus_lt 1⟩
    rw [birthday_appendMinus]
    exact lt_add_one _
  have h := reducedOmegaCost_add_block_le_of_mem_rightPrefixes hp (le_refl (1 : Surreal.{0}))
  have hp1 : plusCount (1 : Surreal.{0}) = 1 := by
    simpa using plusCount_toSurreal (1 : NatOrdinal.{0})
  simp only [reducedOmegaCost_one, hp1, one_add_one_eq_two, NatOrdinal.val_of] at h
  have hs : Ordinal.omega0 < (ω^ (2 : NatOrdinal.{0})).val := by
    simpa only [NatOrdinal.wpow_one, NatOrdinal.val_of] using
      NatOrdinal.val.strictMono (NatOrdinal.wpow_lt_wpow.mpr
        (one_lt_two : (1 : NatOrdinal.{0}) < 2))
  have he : Ordinal.omega0 + (ω^ (2 : NatOrdinal.{0})).val =
      (ω^ (2 : NatOrdinal.{0})).val := by
    rw [NatOrdinal.val_wpow] at hs ⊢
    exact Ordinal.add_omega0_opow hs
  rw [he, NatOrdinal.of_val] at h
  exact h

end Tests
