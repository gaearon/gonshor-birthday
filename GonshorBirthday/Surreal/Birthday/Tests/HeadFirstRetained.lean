/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadFirstRetained

/-!
# A zero-coefficient retained boundary with a nonempty higher head
-/

universe u
public section
open Surreal Set
namespace Tests

/-- An omega head retains the whole reciprocal-omega boundary block at coefficient zero. -/
theorem omega_head_reciprocal_capacity :
    (ω^ (1 : Surreal.{u})).birthday.val + Ordinal.omega0 ≤
      (ω^ (1 : Surreal.{u}) + ω^ (-1 : Surreal)).birthday.val := by
  have hH : (ω^ (1 : Surreal.{u})).support ⊆ Ici (0 : Surreal) := by
    simp only [support_wpow, singleton_subset_iff, mem_Ici]
    exact zero_le_one
  have hw : (0 : Surreal.{u}) ∈ rightPrefixes (-1 : Surreal) := by
    apply mem_rightPrefixes_iff.mpr
    constructor
    · simp only [birthday_zero, birthdayTruncation_zero]
    · exact neg_lt_zero.mpr (zero_lt_one : (0 : Surreal.{u}) < 1)
  have hf : ((ω^ (1 : Surreal.{u})).coeff 0 : Surreal.{u}).birthday <
      NatOrdinal.of Ordinal.omega0 := by
    simp only [coeff_wpow, Pi.single_eq_of_ne zero_ne_one, Real.toSurreal_zero, birthday_zero]
    exact_mod_cast Ordinal.omega0_pos
  have hfirst : ∀ v ∈ rightPrefixes (0 : Surreal.{u}),
      ¬ ((ω^ (1 : Surreal.{u})).support ⊆ Ici v ∧
        ((ω^ (1 : Surreal.{u})).coeff v : Surreal.{u}).birthday <
          NatOrdinal.of Ordinal.omega0) := by
    intro v hv
    simp only [rightPrefixes_zero, mem_empty_iff_false] at hv
  have h := birthday_add_wpow_mul_omega0_le_of_first_retained hH hw hf hfirst
  simpa only [plusCount_zero, NatOrdinal.wpow_zero, NatOrdinal.val_one, one_mul] using h

end Tests
