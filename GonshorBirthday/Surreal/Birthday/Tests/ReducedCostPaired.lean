/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostPaired

import GonshorBirthday.Surreal.Birthday.DyadicCoefficient
import GonshorBirthday.Surreal.Birthday.Minus

/-!
# Paired prefix-gap clients

The input and output heads are unrelated. The negative-unit output attains
the coefficient-step bound; the positive half coefficient has a smaller gap.
A separate positive-unit input client has a nonempty higher head.
-/

universe u
public noncomputable section
namespace Tests
open Surreal Set

/-- The larger head does not create right-prefix gaps on the final positive monomial's scale. -/
theorem positive_unit_with_nonempty_head (s : Surreal.{u}) (r : ℝ)
    {w : Surreal.{u}} (hw : w ∈ rightPrefixes (ω^ (s + 1) + ω^ s)) :
    (r : Surreal) * ω^ s < w - (ω^ (s + 1) + ω^ s) := by
  apply real_mul_wpow_lt_rightPrefix_gap_head_add_wpow (ω^ (s + 1)) s ?_ r hw
  rw [support_wpow]
  intro i hi
  rw [mem_singleton_iff] at hi
  subst i
  exact lt_add_one s

/-- Identical negative-unit coefficients transfer deletion across arbitrary different heads. -/
theorem negative_unit_to_negative_unit (K H s d : Surreal.{u})
    (hK : K.support ⊆ Ioi s) (hH : H.support ⊆ Ioi s)
    (hdel : ∀ w ∈ rightPrefixes (K - ω^ s), K - ω^ s + d < w) :
    ∀ w ∈ rightPrefixes (H - ω^ s), H - ω^ s + d < w := by
  have hsrc : ((-1 : ℝ) : Surreal.{u}) = appendMinus ((0 : ℝ) : Surreal.{u}) := by
    norm_num only [Real.toSurreal_zero, Real.toSurreal_neg, Real.toSurreal_one]
    apply eq_appendMinus_of_birthdayTruncation_eq
    · simp
    · simp
    · norm_num
  apply rightPrefixes_gt_shifted_cutoff_of_last_minus_head K H s hK hH hsrc
  simpa only [Real.toSurreal_neg, Real.toSurreal_one, neg_one_mul, sub_eq_add_neg] using hdel

/-- A positive half-coefficient output also deletes the whole negative-unit input family. -/
theorem positive_half_to_negative_unit (K H s d : Surreal.{u})
    (hK : K.support ⊆ Ioi s) (hH : H.support ⊆ Ioi s)
    (hdel : ∀ w ∈ rightPrefixes (K + (2 : Surreal)⁻¹ * ω^ s),
      K + (2 : Surreal)⁻¹ * ω^ s + d < w) :
    ∀ w ∈ rightPrefixes (H - ω^ s), H - ω^ s + d < w := by
  have hsrc : ((1 / 2 : ℝ) : Surreal.{u}) = appendMinus ((1 : ℝ) : Surreal.{u}) := by
    have hh := half_mul_wpow_eq_appendMinuses (0 : Surreal.{u})
    simpa [appendMinuses_one] using hh
  apply rightPrefixes_gt_shifted_cutoff_of_last_minus_head K H s hK hH hsrc
  simpa using hdel

end Tests
