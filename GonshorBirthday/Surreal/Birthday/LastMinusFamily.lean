/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadPerturbation

import GonshorBirthday.Surreal.Birthday.CoefficientCofinality
import GonshorBirthday.Surreal.Birthday.OmegaBlock

/-!
# Cofinal headed families at a last coefficient minus

If one real coefficient is the canonical minus successor of another, the reflected
finite lower-monomial family is coinitial among right prefixes after any higher head.
Cofinal right-prefix birthdays imply cofinal birthdays for positive multipliers in
this family. Both coefficient signs and a zero predecessor are included.
-/

universe u
public noncomputable section
namespace Surreal
open Set

private theorem exists_head_real_mul_wpow_sub_leftPrefix_le_of_pos
    (K x : Surreal.{u}) (hK : K.support ⊆ Ioi x) {r s : ℝ} (hs : 0 < s)
    (hr : (r : Surreal.{u}) ∈ rightPrefixes (s : Surreal.{u}))
    (hmin : ∀ t : ℝ, (t : Surreal.{u}) ∈ rightPrefixes (s : Surreal.{u}) → r ≤ t)
    {w : Surreal.{u}} (hw : w ∈ rightPrefixes (K + (s : Surreal) * ω^ x)) :
    ∃ a ∈ leftPrefixes (ω^ x), K + ((r : Surreal) * ω^ x - a) ≤ w := by
  have hrs : s < r := Real.toSurreal_lt_iff.mp (mem_rightPrefixes_iff.mp hr).2
  rcases exists_rightPrefixes_add_le hw with ⟨p, hp, hpw⟩ | ⟨p, hp, hpw⟩
  · refine ⟨0, zero_mem_leftPrefixes (wpow_pos x), ?_⟩
    have hg := real_mul_wpow_lt_abs_sub_of_birthday_lt hK
      (birthday_lt_of_mem_rightPrefixes hp) (r - s)
    rw [abs_of_pos (sub_pos.mpr (mem_rightPrefixes_iff.mp hp).2),
      Real.toSurreal_sub, sub_mul] at hg
    simp only [sub_zero]
    linarith only [hg, hpw]
  · rcases exists_rightPrefixes_real_mul_wpow_le hs hp with ⟨a, ha, hap⟩ |
        ⟨t, ht, htp, a, ha, hap⟩
    · refine ⟨0, zero_mem_leftPrefixes (wpow_pos x), ?_⟩
      have hg := real_mul_wpow_lt_of_mem_rightPrefixes (r := r) ha
      simp only [sub_zero]
      exact (add_le_add_right (hg.le.trans hap) K).trans hpw
    · refine ⟨a, ha, ?_⟩
      have hrt : (r : Surreal.{u}) ≤ (t : Surreal) := Real.toSurreal_le_iff.mpr (hmin t htp)
      have hm := mul_le_mul_of_nonneg_right hrt (wpow_nonneg x)
      exact (add_le_add_right ((sub_le_sub_right hm a).trans hap) K).trans hpw

/-- The source of a minus successor is its least canonical right prefix. -/
theorem le_of_mem_rightPrefixes_appendMinus {x p : Surreal.{u}}
    (hp : p ∈ rightPrefixes (appendMinus x)) : x ≤ p := by
  have hbp := birthday_lt_of_mem_rightPrefixes hp
  have hxp := (mem_rightPrefixes_iff.mp hp).2
  rw [appendMinus_eq_ofSets] at hbp hxp
  obtain ⟨q, hq, hqp⟩ := exists_mem_right_le_of_birthday_lt hxp hbp
  obtain rfl := Set.mem_singleton_iff.mp hq
  exact hqp

private theorem exists_real_mul_wpow_sub_leftPrefix_le_of_neg {r s : ℝ} (hs : s < 0)
    (hr : r ≤ 0)
    (hmin : ∀ t : ℝ, (t : Surreal.{u}) ∈ rightPrefixes (s : Surreal.{u}) → r ≤ t)
    {x p : Surreal.{u}} (hp : p ∈ rightPrefixes ((s : Surreal) * ω^ x)) :
    ∃ a ∈ leftPrefixes (ω^ x), (r : Surreal) * ω^ x - a ≤ p := by
  have hpn : -p ∈ leftPrefixes (((-s : ℝ) : Surreal.{u}) * ω^ x) := by
    simpa only [Real.toSurreal_neg, neg_mul] using neg_mem_leftPrefixes_iff.mpr hp
  rcases exists_leftPrefixes_real_mul_wpow_ge (neg_pos.mpr hs) hpn with
      ⟨a, ha, hpa⟩ | ⟨t, ht, htp, a, ha, hpa⟩
  · refine ⟨a, ha, ?_⟩
    have hr0 := mul_nonpos_of_nonpos_of_nonneg (Real.toSurreal_nonpos_iff.mpr hr)
      (wpow_nonneg x)
    linarith only [hr0, hpa]
  · have htn : ((-t : ℝ) : Surreal.{u}) ∈ rightPrefixes (s : Surreal.{u}) := by
      have hh := neg_mem_rightPrefixes_iff.mpr htp
      simpa only [Real.toSurreal_neg, neg_neg] using hh
    have hrt := Real.toSurreal_le_iff.mpr (hmin (-t) htn)
    rw [Real.toSurreal_neg] at hrt
    have hm := mul_le_mul_of_nonneg_right hrt (wpow_nonneg x)
    rw [neg_mul] at hm
    refine ⟨a, ha, ?_⟩
    linarith only [hm, hpa]

/-- A least coefficient right prefix gives a coinitial reflected headed family. -/
theorem exists_head_real_mul_wpow_sub_leftPrefix_le
    (K x : Surreal.{u}) (hK : K.support ⊆ Ioi x) {r s : ℝ}
    (hr : (r : Surreal.{u}) ∈ rightPrefixes (s : Surreal.{u}))
    (hmin : ∀ t : ℝ, (t : Surreal.{u}) ∈ rightPrefixes (s : Surreal.{u}) → r ≤ t)
    {w : Surreal.{u}} (hw : w ∈ rightPrefixes (K + (s : Surreal) * ω^ x)) :
    ∃ a ∈ leftPrefixes (ω^ x), K + ((r : Surreal) * ω^ x - a) ≤ w := by
  by_cases hs : 0 < s
  · exact exists_head_real_mul_wpow_sub_leftPrefix_le_of_pos K x hK hs hr hmin hw
  have hrs : s < r := Real.toSurreal_lt_iff.mp (mem_rightPrefixes_iff.mp hr).2
  have hr0 : r ≤ 0 := by
    by_contra hn
    have hz := leftPrefixes_subset_of_birthdayTruncation_eq (mem_rightPrefixes_iff.mp hr).1
      (zero_mem_leftPrefixes (Real.toSurreal_pos_iff.mpr (lt_of_not_ge hn)))
    exact hs (Real.toSurreal_pos_iff.mp (mem_leftPrefixes_iff.mp hz).2)
  have hs0 : s < 0 := hrs.trans_le hr0
  rcases exists_rightPrefixes_add_le hw with ⟨p, hp, hpw⟩ | ⟨p, hp, hpw⟩
  · refine ⟨0, zero_mem_leftPrefixes (wpow_pos x), ?_⟩
    have hg := real_mul_wpow_lt_abs_sub_of_birthday_lt hK
      (birthday_lt_of_mem_rightPrefixes hp) (r - s)
    rw [abs_of_pos (sub_pos.mpr (mem_rightPrefixes_iff.mp hp).2),
      Real.toSurreal_sub, sub_mul] at hg
    simp only [sub_zero]
    linarith only [hg, hpw]
  · obtain ⟨a, ha, hap⟩ := exists_real_mul_wpow_sub_leftPrefix_le_of_neg hs0 hr0 hmin hp
    exact ⟨a, ha, (add_le_add_right hap K).trans hpw⟩

/-- A last real coefficient minus gives a coinitial finite lower-monomial family. -/
theorem exists_head_real_mul_wpow_sub_natCast_mul_wpow_le
    (K x : Surreal.{u}) (hK : K.support ⊆ Ioi x) {r s : ℝ}
    (hsrc : (s : Surreal.{u}) = appendMinus (r : Surreal.{u}))
    {w : Surreal.{u}} (hw : w ∈ rightPrefixes (K + (s : Surreal) * ω^ x)) :
    K + (r : Surreal) * ω^ x ≤ w ∨
      ∃ v ∈ leftPrefixes x, ∃ n : ℕ,
        K + ((r : Surreal) * ω^ x - (n : Surreal) * ω^ v) ≤ w := by
  have hr : (r : Surreal.{u}) ∈ rightPrefixes (s : Surreal.{u}) := by
    apply mem_rightPrefixes_iff.mpr
    rw [hsrc]
    exact ⟨birthdayTruncation_appendMinus _, appendMinus_lt _⟩
  have hmin (t : ℝ) (ht : (t : Surreal.{u}) ∈ rightPrefixes (s : Surreal.{u})) : r ≤ t := by
    apply Real.toSurreal_le_iff.mp
    rw [hsrc] at ht
    exact le_of_mem_rightPrefixes_appendMinus ht
  obtain ⟨a, ha, haw⟩ := exists_head_real_mul_wpow_sub_leftPrefix_le K x hK hr hmin hw
  rcases exists_natCast_mul_wpow_ge_of_mem_leftPrefixes ha with rfl | ⟨v, hv, n, han⟩
  · left
    simpa only [sub_zero] using haw
  · right
    refine ⟨v, hv, n, ?_⟩
    exact (add_le_add_right (sub_le_sub_left han ((r : Surreal) * ω^ x)) K).trans haw

/-- Cofinal right-prefix birthdays occur in the reflected finite lower-monomial family. -/
theorem head_real_mul_wpow_sub_natCast_mul_wpow_cofinal
    (K x : Surreal.{u}) (hK : K.support ⊆ Ioi x) {r s : ℝ}
    (hsrc : (s : Surreal.{u}) = appendMinus (r : Surreal.{u}))
    (hcof : ∀ a < (K + (s : Surreal) * ω^ x).birthday,
      ∃ w ∈ rightPrefixes (K + (s : Surreal) * ω^ x), a < w.birthday) :
    ∀ a < (K + (s : Surreal) * ω^ x).birthday,
      ∃ p ∈ rightPrefixes (K + (s : Surreal) * ω^ x), a < p.birthday ∧
        (p = K + (r : Surreal) * ω^ x ∨ ∃ v ∈ leftPrefixes x, ∃ n : ℕ,
          p = K + ((r : Surreal) * ω^ x - (n : Surreal) * ω^ v)) := by
  have hrs : s < r := by
    apply Real.toSurreal_lt_iff.mp
    rw [hsrc]
    exact appendMinus_lt _
  have hp : birthdayTruncation (s : Surreal.{u}) (r : Surreal).birthday = r := by
    rw [hsrc]
    exact birthdayTruncation_appendMinus _
  have hbase : K + (r : Surreal) * ω^ x ∈ rightPrefixes (K + (s : Surreal) * ω^ x) := by
    simpa only [sub_zero] using head_real_mul_wpow_sub_leftPrefix_mem_rightPrefixes
      K x hK hrs hp (zero_mem_leftPrefixes (wpow_pos x))
  intro a ha
  obtain ⟨w, hw, haw⟩ := hcof a ha
  have hb {p : Surreal.{u}} (hp : p ∈ rightPrefixes (K + (s : Surreal) * ω^ x))
      (hpw : p ≤ w) : w.birthday ≤ p.birthday := by
    have ht := birthday_le_of_left_between (neg_mem_leftPrefixes_iff.mpr hw)
      (neg_le_neg hpw) (neg_le_neg (mem_rightPrefixes_iff.mp hp).2.le)
    simpa only [birthday_neg] using ht
  rcases exists_head_real_mul_wpow_sub_natCast_mul_wpow_le K x hK hsrc hw with
    hbw | ⟨v, hv, n, hn⟩
  · exact ⟨_, hbase, haw.trans_le (hb hbase hbw), Or.inl rfl⟩
  · have hm := head_real_mul_wpow_sub_leftPrefix_mem_rightPrefixes K x hK hrs hp
      (natCast_mul_wpow_mem_leftPrefixes hv n)
    exact ⟨_, hm, haw.trans_le (hb hm hn), Or.inr ⟨v, hv, n, rfl⟩⟩

private theorem head_real_mul_wpow_sub_natCast_mul_wpow_pos_birthday_cofinal
    (K x : Surreal.{u}) (hK : K.support ⊆ Ioi x) {r s : ℝ}
    (hsrc : (s : Surreal.{u}) = appendMinus (r : Surreal.{u}))
    (hcof : ∀ a < (K + (s : Surreal) * ω^ x).birthday,
      ∃ w ∈ rightPrefixes (K + (s : Surreal) * ω^ x), a < w.birthday) :
    ∀ a < (K + (s : Surreal) * ω^ x).birthday,
      ∃ v ∈ leftPrefixes x, ∃ n : ℕ, 0 < n ∧
        a < (K + ((r : Surreal) * ω^ x - (n : Surreal) * ω^ v)).birthday := by
  have hrs : s < r := by
    apply Real.toSurreal_lt_iff.mp
    rw [hsrc]
    exact appendMinus_lt _
  have hp : birthdayTruncation (s : Surreal.{u}) (r : Surreal).birthday = r := by
    rw [hsrc]
    exact birthdayTruncation_appendMinus _
  have hbase : K + (r : Surreal) * ω^ x ∈ rightPrefixes (K + (s : Surreal) * ω^ x) := by
    simpa only [sub_zero] using head_real_mul_wpow_sub_leftPrefix_mem_rightPrefixes
      K x hK hrs hp (zero_mem_leftPrefixes (wpow_pos x))
  have hf := head_real_mul_wpow_sub_natCast_mul_wpow_cofinal K x hK hsrc hcof
  obtain ⟨p, _, hbp, hpf⟩ := hf _ (birthday_lt_of_mem_rightPrefixes hbase)
  have hv0 : ∃ v ∈ leftPrefixes x, True := by
    rcases hpf with rfl | ⟨v, hv, n, _⟩
    · exact (lt_irrefl _ hbp).elim
    · exact ⟨v, hv, trivial⟩
  obtain ⟨v0, hv0, _⟩ := hv0
  have hm := head_real_mul_wpow_sub_leftPrefix_mem_rightPrefixes K x hK hrs hp
    (natCast_mul_wpow_mem_leftPrefixes hv0 1)
  have hbbase : (K + (r : Surreal) * ω^ x).birthday ≤
      (K + ((r : Surreal) * ω^ x - ((1 : ℕ) : Surreal) * ω^ v0)).birthday := by
    have ht := birthday_le_of_left_between (neg_mem_leftPrefixes_iff.mpr hbase)
      (neg_le_neg (show K + ((r : Surreal) * ω^ x - ((1 : ℕ) : Surreal) * ω^ v0) ≤
        K + (r : Surreal) * ω^ x by simp [wpow_nonneg]))
      (neg_le_neg (mem_rightPrefixes_iff.mp hm).2.le)
    simpa only [birthday_neg] using ht
  intro a ha
  obtain ⟨p, _, hap, hpf⟩ := hf a ha
  rcases hpf with rfl | ⟨v, hv, n, rfl⟩
  · exact ⟨v0, hv0, 1, by omega, hap.trans_le hbbase⟩
  · cases n with
    | zero =>
      simp only [Nat.cast_zero, zero_mul, sub_zero] at hap
      exact ⟨v0, hv0, 1, by omega, hap.trans_le hbbase⟩
    | succ n => exact ⟨v, hv, n + 1, by omega, hap⟩

/-- A last real coefficient minus gives cofinal positive-multiplier canonical right prefixes. -/
theorem head_real_mul_wpow_sub_natCast_mul_wpow_pos_cofinal
    (K x : Surreal.{u}) (hK : K.support ⊆ Ioi x) {r s : ℝ}
    (hsrc : (s : Surreal.{u}) = appendMinus (r : Surreal.{u}))
    (hcof : ∀ a < (K + (s : Surreal) * ω^ x).birthday,
      ∃ w ∈ rightPrefixes (K + (s : Surreal) * ω^ x), a < w.birthday) :
    ∀ a < (K + (s : Surreal) * ω^ x).birthday,
      ∃ v ∈ leftPrefixes x, ∃ n : ℕ, 0 < n ∧
        K + ((r : Surreal) * ω^ x - (n : Surreal) * ω^ v) ∈
          rightPrefixes (K + (s : Surreal) * ω^ x) ∧
        a < (K + ((r : Surreal) * ω^ x - (n : Surreal) * ω^ v)).birthday := by
  intro a ha
  obtain ⟨v, hv, n, hn, hb⟩ :=
    head_real_mul_wpow_sub_natCast_mul_wpow_pos_birthday_cofinal K x hK hsrc hcof a ha
  have hrs : s < r := by
    apply Real.toSurreal_lt_iff.mp
    rw [hsrc]
    exact appendMinus_lt _
  have hp : birthdayTruncation (s : Surreal.{u}) (r : Surreal).birthday = r := by
    rw [hsrc]
    exact birthdayTruncation_appendMinus _
  exact ⟨v, hv, n, hn, head_real_mul_wpow_sub_leftPrefix_mem_rightPrefixes K x hK hrs hp
    (natCast_mul_wpow_mem_leftPrefixes hv n), hb⟩

end Surreal
