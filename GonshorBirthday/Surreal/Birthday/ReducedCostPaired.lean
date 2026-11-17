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

/-- Every canonical right gap of a positive unit last term exceeds each real monomial multiple. -/
theorem real_mul_wpow_lt_rightPrefix_gap_head_add_wpow
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) (r : ℝ)
    {w : Surreal.{u}} (hw : w ∈ rightPrefixes (K + ω^ s)) :
    (r : Surreal) * ω^ s < w - (K + ω^ s) := by
  let t : ℝ := |r| + 1
  have ht : 0 < t := by dsimp [t]; positivity
  have hreal : birthdayTruncation (t : Surreal.{u}) (1 : Surreal).birthday = 1 := by
    simpa using birthdayTruncation_real_mul_wpow t ht (0 : Surreal.{u})
  have hp : birthdayTruncation (K + (t : Surreal) * ω^ s) (K + ω^ s).birthday =
      K + ω^ s := by
    simpa only [Real.toSurreal_one, one_mul] using
      birthdayTruncation_head_real_mul_wpow_of_prefix K s hK (r := t) (s := 1)
        (by simpa only [Real.toSurreal_one] using hreal)
  have hw' := (mem_rightPrefixes_iff.mp
    (rightPrefixes_subset_of_birthdayTruncation_eq hp hw)).2
  have hc : (r : Surreal.{u}) ≤ (|r| : ℝ) := Real.toSurreal_le_iff.mpr (le_abs_self r)
  have hm := mul_le_mul_of_nonneg_right hc (wpow_nonneg s)
  dsimp [t] at hw'
  rw [Real.toSurreal_add, Real.toSurreal_one, add_mul, one_mul] at hw'
  linarith only [hw', hm]

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

/-- A negative unit input with a retained right prefix cannot realize the pure-cost endpoint. -/
theorem not_pure_endpoint_of_negative_unit_input
    (a b d K H s : Surreal.{u}) {r t : ℝ} (hd : 0 ≤ d)
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ m : Surreal.{u}, 0 < m → reducedOmegaCost (x + y + m) (x + y) ≤
        reducedOmegaCost (x + m) x * reducedOmegaCost (y + m) y)
    (hK : K.support ⊆ Ioi s) (hH : H.support ⊆ Ioi s)
    (hsrc : (r : Surreal.{u}) = appendMinus (t : Surreal.{u}))
    (ha : a = H - ω^ s) (hz : K + (r : Surreal) * ω^ s ∈ leftPrefixes (a + b))
    {p : NatOrdinal.{u}} (hp : plusCount (K + (r : Surreal) * ω^ s) < p)
    (hcost : reducedOmegaCost (a + b + d) (K + (r : Surreal) * ω^ s) = ω^ p)
    (hbudget : reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b = ω^ p)
    (hret : ∃ w ∈ rightPrefixes a, w ≤ a + d) : False := by
  have hdel := rightPrefixes_gt_shifted_cutoff_of_pure_eq hd ih hz hp hcost hbudget
  have hinput := rightPrefixes_gt_shifted_cutoff_of_last_minus_head K H s hK hH hsrc hdel
  rw [← ha] at hinput
  obtain ⟨w, hw, hwd⟩ := hret
  exact (hinput w hw).not_ge hwd

end Surreal
