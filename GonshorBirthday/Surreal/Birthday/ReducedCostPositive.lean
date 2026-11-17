/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostHead

import GonshorBirthday.Surreal.Birthday.HeadRun
import GonshorBirthday.Surreal.Birthday.ReciprocalCoefficient
import GonshorBirthday.Surreal.Birthday.SupportGap

/-!
# Excluding positive unit last coefficients at reduced-cost endpoints

For a positive unit monomial after an arbitrary higher head, every canonical
right prefix whose birthday reaches the head has a gap that can be halved.
Canonical addition inverse cofinality eliminates the old head options; the
supported-gap theorem supplies a sufficiently close replacement prefix.
Cofinal right-prefix birthdays therefore exclude the lowered-cutoff gap window.
No boundary restriction on the higher head or the exponent is needed.
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

/-- Cofinal right-prefix birthdays give gap halving after any positive unit last monomial. -/
theorem exists_rightPrefix_half_gap_of_head_add_wpow_cofinal
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s)
    (hcof : ∀ a < (K + ω^ s).birthday,
      ∃ v ∈ rightPrefixes (K + ω^ s), a < v.birthday)
    {w : Surreal.{u}} (hw : w ∈ rightPrefixes (K + ω^ s)) :
    ∃ p ∈ rightPrefixes (K + ω^ s),
      2 * (p - (K + ω^ s)) < w - (K + ω^ s) := by
  have hhead : K ∈ leftPrefixes (K + ω^ s) := by
    apply mem_leftPrefixes_iff.mpr
    refine ⟨?_, lt_add_of_pos_right _ (wpow_pos s)⟩
    apply birthdayTruncation_add_of_support_lt
    simpa only [wlog_wpow] using hK
  obtain ⟨v, hv, hav⟩ := hcof (max K.birthday w.birthday)
    (max_lt (birthday_lt_of_mem_leftPrefixes hhead) (birthday_lt_of_mem_rightPrefixes hw))
  have hlate : K.birthday ≤ v.birthday := (le_max_left _ _).trans hav.le
  have hwv : w.birthday < v.birthday := (le_max_right _ _).trans_lt hav
  have hvw : v < w := by
    have h := birthdayTruncation_lt hwv (mem_rightPrefixes_iff.mp hw).2
    rwa [(mem_rightPrefixes_iff.mp hv).1] at h
  obtain ⟨p, hp, hgap⟩ := exists_rightPrefix_half_gap_of_late_head_add_wpow K s hK hv hlate
  exact ⟨p, hp, hgap.trans (sub_lt_sub_right hvw _)⟩

/-- A positive unit last monomial with cofinal right prefixes cannot satisfy the gap window. -/
theorem not_gap_window_of_head_add_wpow_cofinal
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s)
    (hcof : ∀ a < (K + ω^ s).birthday,
      ∃ v ∈ rightPrefixes (K + ω^ s), a < v.birthday)
    {e d : Surreal.{u}}
    (hz : birthdayTruncation e (K + ω^ s).birthday = K + ω^ s)
    (hdel : ∀ w ∈ rightPrefixes (K + ω^ s), K + ω^ s + d < w)
    (hne : ∃ w ∈ rightPrefixes (K + ω^ s), w ≤ e + d) : False := by
  apply not_coinitial_halving_rightPrefixes_of_gap_window hz hdel hne
    (rightPrefixes (K + ω^ s)) (Subset.refl _) ?_ ?_
  · exact fun w hw ↦ ⟨w, hw, le_rfl⟩
  · exact fun w hw ↦ exists_rightPrefix_half_gap_of_head_add_wpow_cofinal K s hK hcof hw

/-- A pure endpoint with cofinal right prefixes cannot have a positive unit last coefficient. -/
theorem not_pure_endpoint_of_head_add_wpow_cofinal
    (a b d K s : Surreal.{u}) (hd : 0 ≤ d)
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ t : Surreal.{u}, 0 < t → reducedOmegaCost (x + y + t) (x + y) ≤
        reducedOmegaCost (x + t) x * reducedOmegaCost (y + t) y)
    (hK : K.support ⊆ Ioi s)
    (hcof : ∀ c < (K + ω^ s).birthday,
      ∃ v ∈ rightPrefixes (K + ω^ s), c < v.birthday)
    (hz : K + ω^ s ∈ leftPrefixes (a + b)) {p : NatOrdinal.{u}}
    (hp : plusCount (K + ω^ s) < p)
    (hH : reducedOmegaCost (a + b + d) (K + ω^ s) = ω^ p)
    (hM : reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b = ω^ p)
    (hne : ∃ w ∈ rightPrefixes (K + ω^ s), w ≤ a + b + d) : False :=
  not_gap_window_of_head_add_wpow_cofinal K s hK hcof (mem_leftPrefixes_iff.mp hz).1
    (rightPrefixes_gt_shifted_cutoff_of_pure_eq hd ih hz hp hH hM) hne

end Surreal
