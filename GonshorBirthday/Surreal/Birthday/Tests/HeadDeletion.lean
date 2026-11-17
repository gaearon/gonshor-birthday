/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadDeletion

/-!
# Boundary scale separation clients

A unit coefficient retains a uniform gap at its own exponent. An earlier smaller
exponent removes that gap even with a dyadic coefficient. A nondyadic coefficient
removes it without any smaller earlier exponent.
-/

universe u
public section
open Surreal Set

namespace Tests

/-- A unit monomial has a uniform old-right gap at its own exponent. -/
theorem wpow_uniform_right_gap (w : Surreal.{u}) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ rightPrefixes (ω^ w), (ε : Surreal) * ω^ w < p - ω^ w := by
  apply exists_uniform_head_rightPrefix_gap_of_coeff_birthday_lt_omega0
  · simp only [support_wpow, singleton_subset_iff, mem_Ici, le_refl]
  · simp only [coeff_wpow, Pi.single_eq_same]
    simp only [Real.toSurreal_one, birthday_one]
    exact_mod_cast NatOrdinal.natCast_lt_omega0 1

/-- An earlier lower exponent makes the boundary raw omega options redundant. -/
theorem lower_head_exponent_dominates_raw_right_option
    {s v w : Surreal.{u}} (hsv : s < v) (hvw : v < w) (hw : w ∈ rightPrefixes s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ rightPrefixes (ω^ v), p + ω^ s < ω^ v + (ε : Surreal) * ω^ w := by
  exact exists_head_rightPrefix_add_wpow_lt_of_support_lt
    (by simpa only [support_wpow, singleton_subset_iff, mem_Ioi] using hsv)
    (by simp only [support_wpow, mem_singleton_iff]) hvw hw hε

/-- A nondyadic coefficient has no uniform positive gap at its own last exponent. -/
theorem nondyadic_boundary_no_uniform_right_gap (K w : Surreal.{u})
    (hK : K.support ⊆ Ioi w) {r : ℝ}
    (hr : (r : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0) :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ rightPrefixes (K + (r : Surreal) * ω^ w),
      (ε : Surreal) * ω^ w < p - (K + (r : Surreal) * ω^ w) := by
  rintro ⟨ε, hε, hgap⟩
  obtain ⟨q, hq, hqt⟩ := exists_head_real_mul_wpow_rightPrefix_lt K w hK hr
    (lt_add_of_pos_right r hε)
  have hlt : (q : Surreal.{u}) < (r : Surreal) + (ε : Surreal) := by
    simpa only [Real.toSurreal_add] using Real.toSurreal_lt_iff.mpr hqt
  have hm := mul_lt_mul_of_pos_right hlt (wpow_pos w)
  have hh := hgap _ hq
  rw [add_mul] at hm
  linarith

end Tests
