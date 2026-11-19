/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Head

import GonshorBirthday.Surreal.Birthday.HeadRun
import GonshorBirthday.Surreal.Birthday.ReciprocalCoefficient
import GonshorBirthday.Surreal.Birthday.SupportGap

/-!
# Right gaps above a final positive unit monomial

After an arbitrary higher head, every right prefix reaching the head's birthday has
a gap that can be halved.
-/

universe u
public noncomputable section
namespace Surreal
open Set

private theorem realCast_inv_two_pow (n : ℕ) :
    Real.toSurreal ((2 : ℝ)⁻¹ ^ n) = (2 : Surreal.{u})⁻¹ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Real.toSurreal_mul, ih, Real.toSurreal_inv]
    norm_num only [Real.toSurreal_ofNat]
    rw [pow_succ]

/-- Every right prefix reaching the head's birthday admits a strictly halved gap. -/
theorem exists_rightPrefix_half_gap_of_late_head_add_wpow
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {v : Surreal.{u}}
    (hv : v ∈ rightPrefixes (K + ω^ s)) (hlate : K.birthday ≤ v.birthday) :
    ∃ p ∈ rightPrefixes (K + ω^ s),
      2 * (p - (K + ω^ s)) < v - (K + ω^ s) := by
  have hhead : birthdayTruncation (K + ω^ s) K.birthday = K := by
    apply birthdayTruncation_add_of_support_lt
    simpa only [wlog_wpow] using hK
  have hs : s ∈ (K + ω^ s).support := by
    simpa only [Real.toSurreal_one, one_mul] using
      mem_support_head_real_mul_wpow K s hK (r := 1) one_ne_zero
  rcases exists_rightPrefixes_add_le hv with ⟨p, hp, hpv⟩ | ⟨q, hq, hqv⟩
  · have hpZ := rightPrefixes_subset_of_birthdayTruncation_eq hhead hp
    have hlow := birthdayTruncation_lt
      ((birthday_lt_of_mem_rightPrefixes hp).trans_le hlate)
      (mem_rightPrefixes_iff.mp hpZ).2
    rw [(mem_rightPrefixes_iff.mp hv).1] at hlow
    have hpos := wpow_pos s
    linarith only [hlow, hpv, hpos]
  · obtain ⟨u, hu, n, hnq⟩ := exists_inv_two_pow_mul_wpow_le_of_mem_rightPrefixes hq
    let c : ℝ := (2 : ℝ)⁻¹ ^ n
    have hc : 0 < c := by dsimp only [c]; positivity
    have hcof : K + (c : Surreal) * ω^ u ≤ v := by
      dsimp only [c]
      rw [realCast_inv_two_pow]
      exact (add_le_add le_rfl hnq).trans hqv
    obtain ⟨p, hp, hgap⟩ := exists_rightPrefix_sub_lt_real_mul_wpow_of_support hs hu
      (show 0 < c / 4 by positivity)
    have hsmall : ω^ s < ((c / 2 : ℝ) : Surreal) * ω^ u :=
      wpow_lt_mul_wpow (by positivity) (mem_rightPrefixes_iff.mp hu).2
    have htwo : ((c / 2 : ℝ) : Surreal) * ω^ u =
        2 * (((c / 4 : ℝ) : Surreal) * ω^ u) := by
      rw [Real.toSurreal_div, Real.toSurreal_div]
      norm_num only [Real.toSurreal_ofNat]
      ring
    have hfour : (c : Surreal) * ω^ u =
        4 * (((c / 4 : ℝ) : Surreal) * ω^ u) := by
      rw [Real.toSurreal_div]
      norm_num only [Real.toSurreal_ofNat]
      ring
    rw [htwo] at hsmall
    rw [hfour] at hcof
    refine ⟨p, hp, ?_⟩
    linarith only [hgap, hsmall, hcof]

end Surreal
