/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.CoefficientBlock

import GonshorBirthday.Surreal.Birthday.SupportGap
import GonshorBirthday.Surreal.Birthday.ReciprocalCoefficient
import GonshorBirthday.Surreal.Birthday.CoefficientCofinality

/-!
# Right prefixes through a final real coefficient plus

A final coefficient plus with nonzero real predecessor introduces no new canonical
right prefixes, even after an arbitrary higher head. Normal-form support gaps and
canonical product/addition cofinality prove this without a left-cofinality hypothesis.
Thus cofinal right-prefix birthdays force a nonzero dyadic last coefficient either
to be the positive unit or to end in a real coefficient minus, including predecessor zero.
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

/-- Every old right monomial option bounds a canonical right prefix after a nonzero last term. -/
theorem exists_rightPrefix_head_real_mul_wpow_le_add (K s : Surreal.{u})
    (hK : K.support ⊆ Ioi s) {t : ℝ} (ht : t ≠ 0) {b : Surreal.{u}}
    (hb : b ∈ rightPrefixes (ω^ s)) :
    ∃ p ∈ rightPrefixes (K + (t : Surreal) * ω^ s), p ≤ K + b := by
  obtain ⟨w, hw, n, hnb⟩ := exists_inv_two_pow_mul_wpow_le_of_mem_rightPrefixes hb
  have hε : 0 < (2 : ℝ)⁻¹ ^ (n + 1) := by positivity
  obtain ⟨p, hp, hgap⟩ := exists_rightPrefix_sub_lt_real_mul_wpow_of_support
    (mem_support_head_real_mul_wpow K s hK ht) hw hε
  have hcoef := mul_wpow_lt_mul_wpow_of_pos t hε (mem_rightPrefixes_iff.mp hw).2
  rw [realCast_inv_two_pow] at hgap hcoef
  have he : 2 * ((2 : Surreal.{u})⁻¹ ^ (n + 1) * ω^ w) =
      (2 : Surreal)⁻¹ ^ n * ω^ w := by
    rw [pow_succ]
    field_simp
  refine ⟨p, hp, ?_⟩
  linarith only [hgap, hcoef, he, hnb]

/-- A prefix and its extension have equal right-prefix sets when old right
prefixes are coinitial. -/
theorem rightPrefixes_eq_of_prefix_of_coinitial {W Z : Surreal.{u}}
    (hpre : birthdayTruncation Z W.birthday = W)
    (hcof : ∀ p ∈ rightPrefixes Z, ∃ q ∈ rightPrefixes W, q ≤ p) :
    rightPrefixes Z = rightPrefixes W := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨q, hq, hqp⟩ := hcof p hp
    have hqZ := rightPrefixes_subset_of_birthdayTruncation_eq hpre hq
    have hpPre := (mem_rightPrefixes_iff.mp hp).1
    have htr := birthdayTruncation_eq_of_right_between (birthday_lt_of_mem_rightPrefixes hp).le
      (mem_rightPrefixes_iff.mp hqZ).2.le (by rwa [hpPre])
    rw [hpPre] at htr
    exact mem_rightPrefixes_iff.mpr
      ⟨birthdayTruncation_eq_trans (mem_rightPrefixes_iff.mp hq).1 htr,
        (mem_rightPrefixes_iff.mp hq).2.trans_le hqp⟩
  · exact rightPrefixes_subset_of_birthdayTruncation_eq hpre

/-- A final real coefficient plus with nonzero predecessor preserves all headed right prefixes. -/
theorem rightPrefixes_head_real_mul_wpow_appendPlus
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {r t : ℝ} (ht : t ≠ 0)
    (hsrc : (r : Surreal.{u}) = appendPlus (t : Surreal.{u})) :
    rightPrefixes (K + (r : Surreal) * ω^ s) =
      rightPrefixes (K + (t : Surreal) * ω^ s) := by
  have htr : t < r := Real.toSurreal_lt_iff.mp (by rw [hsrc]; exact lt_appendPlus _)
  have hpcoef : birthdayTruncation (r : Surreal.{u}) (t : Surreal).birthday = t := by
    rw [hsrc]
    exact birthdayTruncation_appendPlus _
  have hpre := birthdayTruncation_head_real_mul_wpow_of_prefix K s hK hpcoef
  have hRc : rightPrefixes (r : Surreal.{u}) = rightPrefixes (t : Surreal.{u}) := by
    rw [hsrc, rightPrefixes_appendPlus]
  have htS : (t : Surreal.{u}) ≠ 0 := by exact_mod_cast ht
  have hKpre : birthdayTruncation (K + (t : Surreal) * ω^ s) K.birthday = K := by
    apply birthdayTruncation_add_of_support_lt
    rw [wlog_mul htS (wpow_ne_zero _), wlog_realCast, wlog_wpow, zero_add]
    exact hK
  apply rightPrefixes_eq_of_prefix_of_coinitial hpre
  intro p hp
  rcases exists_rightPrefixes_add_le hp with ⟨q, hq, hqp⟩ | ⟨q, hq, hqp⟩
  · by_cases hrpos : 0 < r
    · have hqW := rightPrefixes_subset_of_birthdayTruncation_eq hKpre hq
      refine ⟨q, hqW, ?_⟩
      have hr0 := mul_nonneg (Real.toSurreal_pos_iff.mpr hrpos).le (wpow_nonneg s)
      exact (le_add_of_nonneg_right hr0).trans hqp
    · have htneg : t < 0 := htr.trans_le (le_of_not_gt hrpos)
      have hKW : K ∈ rightPrefixes (K + (t : Surreal) * ω^ s) := by
        apply mem_rightPrefixes_iff.mpr
        refine ⟨hKpre, ?_⟩
        have htn := mul_neg_of_neg_of_pos (Real.toSurreal_neg_iff.mpr htneg) (wpow_pos s)
        linarith only [htn]
      have hg := real_mul_wpow_lt_abs_sub_of_birthday_lt hK
        (birthday_lt_of_mem_rightPrefixes hq) (-r)
      rw [abs_of_pos (sub_pos.mpr (mem_rightPrefixes_iff.mp hq).2), Real.toSurreal_neg,
        neg_mul] at hg
      refine ⟨K, hKW, ?_⟩
      linarith only [hg, hqp]
  · by_cases hrpos : 0 < r
    · rcases exists_rightPrefixes_real_mul_wpow_le hrpos hq with ⟨b, hb, hbq⟩ |
          ⟨c, hc, hcr, a, ha, hca⟩
      · obtain ⟨p0, hp0, hp0b⟩ := exists_rightPrefix_head_real_mul_wpow_le_add K s hK ht hb
        exact ⟨p0, hp0, hp0b.trans ((add_le_add_right hbq K).trans hqp)⟩
      · have hct : (c : Surreal.{u}) ∈ rightPrefixes (t : Surreal.{u}) := by rwa [← hRc]
        have htc : t < c := Real.toSurreal_lt_iff.mp (mem_rightPrefixes_iff.mp hct).2
        have hp0 := head_real_mul_wpow_sub_leftPrefix_mem_rightPrefixes K s hK htc
          (mem_rightPrefixes_iff.mp hct).1 ha
        exact ⟨_, hp0, (add_le_add_right hca K).trans hqp⟩
    · have hrne : r ≠ 0 := by
        intro he
        have htp : (t : Surreal.{u}) ∈ leftPrefixes (r : Surreal.{u}) :=
          mem_leftPrefixes_iff.mpr ⟨hpcoef, Real.toSurreal_lt_iff.mpr htr⟩
        simp only [he, Real.toSurreal_zero, leftPrefixes_zero, Set.mem_empty_iff_false] at htp
      have hrneg : r < 0 := lt_of_le_of_ne (le_of_not_gt hrpos) hrne
      have htneg : t < 0 := htr.trans hrneg
      have hqn : -q ∈ leftPrefixes (((-r : ℝ) : Surreal.{u}) * ω^ s) := by
        simpa only [Real.toSurreal_neg, neg_mul] using neg_mem_leftPrefixes_iff.mpr hq
      rcases exists_leftPrefixes_real_mul_wpow_ge (neg_pos.mpr hrneg) hqn with
          ⟨a, ha, hqa⟩ | ⟨c, hc, hcr, a, ha, hca⟩
      · have hp0 := head_real_mul_wpow_sub_leftPrefix_mem_rightPrefixes K s hK htneg
          (by simp) ha
        refine ⟨K - a, ?_, ?_⟩
        · simpa only [Real.toSurreal_zero, zero_mul, zero_sub, sub_eq_add_neg, zero_add] using hp0
        · linarith only [hqa, hqp]
      · have hcn : ((-c : ℝ) : Surreal.{u}) ∈ rightPrefixes (r : Surreal.{u}) := by
          have hh := neg_mem_rightPrefixes_iff.mpr hcr
          simpa only [Real.toSurreal_neg, neg_neg] using hh
        rw [hRc] at hcn
        have htc : t < -c := Real.toSurreal_lt_iff.mp (mem_rightPrefixes_iff.mp hcn).2
        have hp0 := head_real_mul_wpow_sub_leftPrefix_mem_rightPrefixes K s hK htc
          (mem_rightPrefixes_iff.mp hcn).1 ha
        refine ⟨_, hp0, ?_⟩
        rw [Real.toSurreal_neg, neg_mul]
        linarith only [hca, hqp]

/-- A final coefficient plus with nonzero predecessor precludes cofinal right-prefix birthdays. -/
theorem not_rightPrefixes_cofinal_head_real_mul_wpow_appendPlus
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {r t : ℝ} (ht : t ≠ 0)
    (hsrc : (r : Surreal.{u}) = appendPlus (t : Surreal.{u}))
    (hcof : ∀ a < (K + (r : Surreal) * ω^ s).birthday,
      ∃ p ∈ rightPrefixes (K + (r : Surreal) * ω^ s), a < p.birthday) : False := by
  have htr : t < r := Real.toSurreal_lt_iff.mp (by rw [hsrc]; exact lt_appendPlus _)
  have hpcoef : birthdayTruncation (r : Surreal.{u}) (t : Surreal).birthday = t := by
    rw [hsrc]
    exact birthdayTruncation_appendPlus _
  have hpre := birthdayTruncation_head_real_mul_wpow_of_prefix K s hK hpcoef
  have hW : K + (t : Surreal) * ω^ s ∈ leftPrefixes (K + (r : Surreal) * ω^ s) :=
    mem_leftPrefixes_iff.mpr ⟨hpre,
      add_lt_add_right (mul_lt_mul_of_pos_right (Real.toSurreal_lt_iff.mpr htr) (wpow_pos s)) K⟩
  obtain ⟨p, hp, hbp⟩ := hcof _ (birthday_lt_of_mem_leftPrefixes hW)
  rw [rightPrefixes_head_real_mul_wpow_appendPlus K s hK ht hsrc] at hp
  exact hbp.not_gt (birthday_lt_of_mem_rightPrefixes hp)

/-- Cofinal right-prefix birthdays force a dyadic last coefficient to be
one or a minus successor. -/
theorem real_coefficient_eq_one_or_minus_successor_of_head_rightPrefixes_cofinal
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {r : ℝ} (hr : r ≠ 0)
    (hf : (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    (hcof : ∀ a < (K + (r : Surreal) * ω^ s).birthday,
      ∃ p ∈ rightPrefixes (K + (r : Surreal) * ω^ s), a < p.birthday) :
    r = 1 ∨ ∃ t : ℝ, (r : Surreal.{u}) = appendMinus (t : Surreal.{u}) := by
  by_cases hr1 : r = 1
  · exact Or.inl hr1
  · right
    by_cases hrn1 : r = -1
    · refine ⟨0, ?_⟩
      rw [hrn1, Real.toSurreal_zero]
      apply eq_appendMinus_of_birthdayTruncation_eq
      · simp
      · simp
      · norm_num
    · obtain ⟨t, ht, hsrc⟩ := exists_nonzero_real_predecessor_of_finite_birthday hr hr1 hrn1 hf
      rcases hsrc with hsrc | hsrc
      · exact (not_rightPrefixes_cofinal_head_real_mul_wpow_appendPlus K s hK ht hsrc hcof).elim
      · exact ⟨t, hsrc⟩

end Surreal
