/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Head
public import GonshorBirthday.Surreal.Birthday.ReducedCost

import GonshorBirthday.Surreal.Birthday.CoefficientStep
import GonshorBirthday.Surreal.Birthday.HeadPerturbation
import GonshorBirthday.Surreal.Birthday.OmegaBlock
import GonshorBirthday.Surreal.Birthday.ReducedCostLower

/-!
# Comparing input and output canonical prefix gaps

A positive unit last monomial has no canonical right gap on its own scale.
For a negative unit last monomial, reflected lower-monomial prefixes are
coinitial in value. Pairing these with the output's coefficient-prefix family
transfers deletion to every input right prefix. No birthday-cofinality or
exact perturbation-length hypothesis is needed for this comparison.
-/

universe u
public noncomputable section
namespace Surreal
open Set

/-- A margin on a strictly lower scale deletes every canonical right prefix of a higher head. -/
theorem rightPrefixes_gt_shifted_cutoff_of_support_gt {K s d : Surreal.{u}}
    (hK : K.support ⊆ Ioi s) (hd : d ≤ ω^ s) :
    ∀ w ∈ rightPrefixes K, K + d < w := by
  intro w hw
  have hg := real_mul_wpow_lt_abs_sub_of_birthday_lt hK
    (birthday_lt_of_mem_rightPrefixes hw) (1 : ℝ)
  rw [Real.toSurreal_one, one_mul,
    abs_of_pos (sub_pos.mpr (mem_rightPrefixes_iff.mp hw).2)] at hg
  linarith only [hg, hd]

/-- A margin at most the final monomial deletes every right prefix of a positive unit last term. -/
theorem rightPrefixes_gt_shifted_cutoff_head_add_wpow {K s d : Surreal.{u}}
    (hK : K.support ⊆ Ioi s) (hd : d ≤ ω^ s) :
    ∀ w ∈ rightPrefixes (K + ω^ s), K + ω^ s + d < w := by
  intro w hw
  have hg := real_mul_wpow_lt_rightPrefix_gap_head_add_wpow K s hK (1 : ℝ) hw
  rw [Real.toSurreal_one, one_mul] at hg
  linarith only [hg, hd]

/-- Deleting a coefficient right prefix with a step at most one bounds the common margin. -/
theorem shifted_cutoff_lt_wpow_of_head_coefficient_rightPrefix
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {r t : ℝ}
    (hrt : r < t)
    (hp : birthdayTruncation (r : Surreal.{u}) (t : Surreal).birthday = t)
    (hstep : t - r ≤ 1) {d : Surreal.{u}}
    (hdel : ∀ w ∈ rightPrefixes (K + (r : Surreal) * ω^ s),
      K + (r : Surreal) * ω^ s + d < w) : d < ω^ s := by
  have hw := hdel _ (head_real_mul_wpow_sub_leftPrefix_mem_rightPrefixes K s hK
    hrt hp (zero_mem_leftPrefixes (wpow_pos s)))
  simp only [sub_zero] at hw
  have hscale := mul_le_mul_of_nonneg_right (Real.toSurreal_le_iff.mpr hstep)
    (wpow_nonneg s)
  rw [Real.toSurreal_sub, Real.toSurreal_one, sub_mul, one_mul] at hscale
  linarith only [hw, hscale]

/-- Paired coefficient-prefix families transfer output deletion to a negative unit input. -/
theorem rightPrefixes_gt_shifted_cutoff_of_paired_head_families
    (K H s : Surreal.{u}) (hK : K.support ⊆ Ioi s) (hH : H.support ⊆ Ioi s)
    {r t : ℝ} (hrt : r < t)
    (hp : birthdayTruncation (r : Surreal.{u}) (t : Surreal).birthday = t)
    (hstep : t - r ≤ 1) {d : Surreal.{u}}
    (hdel : ∀ w ∈ rightPrefixes (K + (r : Surreal) * ω^ s),
      K + (r : Surreal) * ω^ s + d < w) :
    ∀ w ∈ rightPrefixes (H - ω^ s), H - ω^ s + d < w := by
  have hscale := mul_le_mul_of_nonneg_right (Real.toSurreal_le_iff.mpr hstep)
    (wpow_nonneg s)
  rw [Real.toSurreal_sub, Real.toSurreal_one, sub_mul, one_mul] at hscale
  intro w hw
  rcases exists_head_sub_natCast_mul_wpow_le_of_mem_rightPrefixes H s hH hw with
    hHw | ⟨v, hv, n, hn⟩
  · have hz := hdel _ (head_real_mul_wpow_sub_leftPrefix_mem_rightPrefixes K s hK
      hrt hp (zero_mem_leftPrefixes (wpow_pos s)))
    simp only [sub_zero] at hz
    linarith only [hHw, hscale, hz]
  · have hz := hdel _ (head_real_mul_wpow_sub_leftPrefix_mem_rightPrefixes K s hK
      hrt hp (natCast_mul_wpow_mem_leftPrefixes hv n))
    linarith only [hn, hscale, hz]

/-- A final real coefficient minus bounds a fully deleted output's margin by its monomial. -/
theorem shifted_cutoff_lt_wpow_of_last_minus_head
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {r t : ℝ}
    (hsrc : (r : Surreal.{u}) = appendMinus (t : Surreal.{u})) {d : Surreal.{u}}
    (hdel : ∀ w ∈ rightPrefixes (K + (r : Surreal) * ω^ s),
      K + (r : Surreal) * ω^ s + d < w) : d < ω^ s := by
  have hrt : r < t := Real.toSurreal_lt_iff.mp (by rw [hsrc]; exact appendMinus_lt _)
  have hp : birthdayTruncation (r : Surreal.{u}) (t : Surreal).birthday = t := by
    rw [hsrc]
    exact birthdayTruncation_appendMinus _
  exact shifted_cutoff_lt_wpow_of_head_coefficient_rightPrefix K s hK hrt hp
    (real_sub_le_one_of_eq_appendMinus hsrc) hdel

/-- Deleting every output right prefix deletes every right prefix of a negative unit input. -/
theorem rightPrefixes_gt_shifted_cutoff_of_last_minus_head
    (K H s : Surreal.{u}) (hK : K.support ⊆ Ioi s) (hH : H.support ⊆ Ioi s)
    {r t : ℝ} (hsrc : (r : Surreal.{u}) = appendMinus (t : Surreal.{u}))
    {d : Surreal.{u}}
    (hdel : ∀ w ∈ rightPrefixes (K + (r : Surreal) * ω^ s),
      K + (r : Surreal) * ω^ s + d < w) :
    ∀ w ∈ rightPrefixes (H - ω^ s), H - ω^ s + d < w := by
  have hrt : r < t := Real.toSurreal_lt_iff.mp (by rw [hsrc]; exact appendMinus_lt _)
  have hp : birthdayTruncation (r : Surreal.{u}) (t : Surreal).birthday = t := by
    rw [hsrc]
    exact birthdayTruncation_appendMinus _
  exact rightPrefixes_gt_shifted_cutoff_of_paired_head_families K H s hK hH hrt hp
    (real_sub_le_one_of_eq_appendMinus hsrc) hdel

end Surreal
