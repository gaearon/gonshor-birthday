/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.CoefficientWord

import GonshorBirthday.Surreal.Birthday.HeadCoefficientWord
import GonshorBirthday.Surreal.Birthday.Real

/-!
# Actual coefficient sign-block positions

The first positive coefficient sign contributes the monomial itself. Each later
coefficient sign contributes one pure-power block, in its original orientation.
-/

universe u
public noncomputable section
namespace Surreal
open Set Order

private theorem positive_real_prefix_data {r : ℝ} (hr : 0 < r) {a : NatOrdinal.{u}}
    (ha0 : 0 < a) (ha : a ≤ (r : Surreal.{u}).birthday) :
    ∃ s : ℝ, 0 < s ∧ (s : Surreal.{u}) = birthdayTruncation (r : Surreal.{u}) a ∧
      (s : Surreal.{u}).birthday = a := by
  obtain ⟨s, hs⟩ := birthdayTruncation_real_mem_range_real r a
  refine ⟨s, ?_, hs, ?_⟩
  · apply Real.toSurreal_pos_iff.mp
    rw [hs]
    apply (lt_birthdayTruncation_iff ha (by simpa only [birthday_zero] using ha0)).mpr
    exact Real.toSurreal_pos_iff.mpr hr
  · rw [hs, birthday_birthdayTruncation _ ha]

/-- Scaling a positive real prefix has the exact original coefficient-position birthday. -/
theorem birthday_real_prefix_mul_wpow {r : ℝ} (hr : 0 < r) {a : NatOrdinal.{u}}
    (ha0 : 0 < a) (ha : a ≤ (r : Surreal.{u}).birthday) (x : Surreal.{u}) :
    (birthdayTruncation (r : Surreal.{u}) a * ω^ x).birthday = NatOrdinal.of
      ((ω^ x).birthday.val + (ω^ plusCount x).val * (a.val - 1)) := by
  obtain ⟨s, hs, hsval, hsb⟩ := positive_real_prefix_data hr ha0 ha
  rw [← hsval, birthday_real_mul_wpow hs x, hsb]

/-- A later plus coefficient sign becomes exactly one pure-power plus block. -/
theorem real_mul_wpow_birthdayTruncation_add_one_plus {r : ℝ} (hr : 0 < r)
    {a : NatOrdinal.{u}} (ha0 : 0 < a) (ha : a + 1 ≤ (r : Surreal.{u}).birthday)
    (hl : birthdayTruncation (r : Surreal.{u}) a < (r : Surreal.{u})) (x : Surreal.{u}) :
    birthdayTruncation (r : Surreal.{u}) (a + 1) * ω^ x =
      appendPluses (birthdayTruncation (r : Surreal.{u}) a * ω^ x) (ω^ plusCount x).val := by
  have _ := hr
  simpa only [zero_add] using
    head_real_mul_wpow_birthdayTruncation_add_one_plus (0 : Surreal.{u}) x (by simp) r ha0 ha hl

/-- A later minus coefficient sign becomes exactly one pure-power minus block. -/
theorem real_mul_wpow_birthdayTruncation_add_one_minus {r : ℝ} (hr : 0 < r)
    {a : NatOrdinal.{u}} (ha0 : 0 < a) (ha : a + 1 ≤ (r : Surreal.{u}).birthday)
    (hl : (r : Surreal.{u}) < birthdayTruncation (r : Surreal.{u}) a)
    (x : Surreal.{u}) :
    birthdayTruncation (r : Surreal.{u}) (a + 1) * ω^ x =
      appendMinuses (birthdayTruncation (r : Surreal.{u}) a * ω^ x) (ω^ plusCount x).val := by
  have _ := hr
  simpa only [zero_add] using
    head_real_mul_wpow_birthdayTruncation_add_one_minus (0 : Surreal.{u}) x (by simp) r ha0 ha hl

/-- Every stage of a plus coefficient block is the corresponding actual product prefix. -/
theorem birthdayTruncation_real_mul_wpow_plus_block {r : ℝ} (hr : 0 < r)
    {a : NatOrdinal.{u}} (ha0 : 0 < a) (ha : a + 1 ≤ (r : Surreal.{u}).birthday)
    (hl : birthdayTruncation (r : Surreal.{u}) a < (r : Surreal.{u})) (x : Surreal.{u})
    {t : Ordinal.{u}} (ht : t ≤ (ω^ plusCount x).val) :
    birthdayTruncation ((r : Surreal.{u}) * ω^ x) (NatOrdinal.of
      ((ω^ x).birthday.val + (ω^ plusCount x).val * (a.val - 1) + t)) =
        appendPluses (birthdayTruncation (r : Surreal.{u}) a * ω^ x) t := by
  have hab : a ≤ (r : Surreal.{u}).birthday := (le_add_of_nonneg_right (by simp)).trans ha
  have hp : birthdayTruncation (r : Surreal.{u})
      (birthdayTruncation (r : Surreal.{u}) (a + 1)).birthday =
        birthdayTruncation (r : Surreal.{u}) (a + 1) := by
    rw [birthday_birthdayTruncation _ ha]
  have hpre := birthdayTruncation_real_mul_wpow_of_prefix hp x
  rw [real_mul_wpow_birthdayTruncation_add_one_plus hr ha0 ha hl x] at hpre
  have hstage : birthdayTruncation
      (appendPluses (birthdayTruncation (r : Surreal.{u}) a * ω^ x) (ω^ plusCount x).val)
      (appendPluses (birthdayTruncation (r : Surreal.{u}) a * ω^ x) t).birthday =
        appendPluses (birthdayTruncation (r : Surreal.{u}) a * ω^ x) t := by
    rw [birthday_appendPluses]
    exact birthdayTruncation_appendPluses_add _ ht
  have h := birthdayTruncation_eq_trans hpre hstage
  rwa [birthday_appendPluses, birthday_real_prefix_mul_wpow hr ha0 hab x,
    NatOrdinal.val_of] at h

/-- Every stage of a minus coefficient block is the corresponding actual product prefix. -/
theorem birthdayTruncation_real_mul_wpow_minus_block {r : ℝ} (hr : 0 < r)
    {a : NatOrdinal.{u}} (ha0 : 0 < a) (ha : a + 1 ≤ (r : Surreal.{u}).birthday)
    (hl : (r : Surreal.{u}) < birthdayTruncation (r : Surreal.{u}) a)
    (x : Surreal.{u})
    {t : Ordinal.{u}} (ht : t ≤ (ω^ plusCount x).val) :
    birthdayTruncation ((r : Surreal.{u}) * ω^ x) (NatOrdinal.of
      ((ω^ x).birthday.val + (ω^ plusCount x).val * (a.val - 1) + t)) =
        appendMinuses (birthdayTruncation (r : Surreal.{u}) a * ω^ x) t := by
  have hab : a ≤ (r : Surreal.{u}).birthday := (le_add_of_nonneg_right (by simp)).trans ha
  have hp : birthdayTruncation (r : Surreal.{u})
      (birthdayTruncation (r : Surreal.{u}) (a + 1)).birthday =
        birthdayTruncation (r : Surreal.{u}) (a + 1) := by
    rw [birthday_birthdayTruncation _ ha]
  have hpre := birthdayTruncation_real_mul_wpow_of_prefix hp x
  rw [real_mul_wpow_birthdayTruncation_add_one_minus hr ha0 ha hl x] at hpre
  have hstage : birthdayTruncation
      (appendMinuses (birthdayTruncation (r : Surreal.{u}) a * ω^ x) (ω^ plusCount x).val)
      (appendMinuses (birthdayTruncation (r : Surreal.{u}) a * ω^ x) t).birthday =
        appendMinuses (birthdayTruncation (r : Surreal.{u}) a * ω^ x) t := by
    rw [birthday_appendMinuses]
    exact birthdayTruncation_appendMinuses_add _ ht
  have h := birthdayTruncation_eq_trans hpre hstage
  rwa [birthday_appendMinuses, birthday_real_prefix_mul_wpow hr ha0 hab x,
    NatOrdinal.val_of] at h

/-- Every interior position of a plus coefficient block carries the original plus sign. -/
theorem birthdayTruncation_real_mul_wpow_plus_block_lt {r : ℝ} (hr : 0 < r)
    {a : NatOrdinal.{u}} (ha0 : 0 < a) (ha : a + 1 ≤ (r : Surreal.{u}).birthday)
    (hl : birthdayTruncation (r : Surreal.{u}) a < (r : Surreal.{u})) (x : Surreal.{u})
    {t : Ordinal.{u}} (ht : t < (ω^ plusCount x).val) :
    birthdayTruncation ((r : Surreal.{u}) * ω^ x) (NatOrdinal.of
      ((ω^ x).birthday.val + (ω^ plusCount x).val * (a.val - 1) + t)) <
        (r : Surreal.{u}) * ω^ x := by
  have hp : birthdayTruncation (r : Surreal.{u})
      (birthdayTruncation (r : Surreal.{u}) (a + 1)).birthday =
        birthdayTruncation (r : Surreal.{u}) (a + 1) := by
    rw [birthday_birthdayTruncation _ ha]
  have hpre := birthdayTruncation_real_mul_wpow_of_prefix hp x
  rw [real_mul_wpow_birthdayTruncation_add_one_plus hr ha0 ha hl x] at hpre
  have hstage : appendPluses (birthdayTruncation (r : Surreal.{u}) a * ω^ x) t ∈ leftPrefixes
      (appendPluses (birthdayTruncation (r : Surreal.{u}) a * ω^ x) (ω^ plusCount x).val) :=
    mem_leftPrefixes_iff.mpr
      ⟨birthdayTruncation_appendPluses_of_lt _ ht, strictMono_appendPluses _ ht⟩
  have hsource := leftPrefixes_subset_of_birthdayTruncation_eq hpre hstage
  rw [birthdayTruncation_real_mul_wpow_plus_block hr ha0 ha hl x ht.le]
  exact (mem_leftPrefixes_iff.mp hsource).2

/-- Every interior position of a minus coefficient block carries the original minus sign. -/
theorem lt_birthdayTruncation_real_mul_wpow_minus_block {r : ℝ} (hr : 0 < r)
    {a : NatOrdinal.{u}} (ha0 : 0 < a) (ha : a + 1 ≤ (r : Surreal.{u}).birthday)
    (hl : (r : Surreal.{u}) < birthdayTruncation (r : Surreal.{u}) a)
    (x : Surreal.{u})
    {t : Ordinal.{u}} (ht : t < (ω^ plusCount x).val) :
    (r : Surreal.{u}) * ω^ x < birthdayTruncation ((r : Surreal.{u}) * ω^ x) (NatOrdinal.of
      ((ω^ x).birthday.val + (ω^ plusCount x).val * (a.val - 1) + t)) := by
  have hp : birthdayTruncation (r : Surreal.{u})
      (birthdayTruncation (r : Surreal.{u}) (a + 1)).birthday =
        birthdayTruncation (r : Surreal.{u}) (a + 1) := by
    rw [birthday_birthdayTruncation _ ha]
  have hpre := birthdayTruncation_real_mul_wpow_of_prefix hp x
  rw [real_mul_wpow_birthdayTruncation_add_one_minus hr ha0 ha hl x] at hpre
  have hstage : appendMinuses (birthdayTruncation (r : Surreal.{u}) a * ω^ x) t ∈ rightPrefixes
      (appendMinuses (birthdayTruncation (r : Surreal.{u}) a * ω^ x) (ω^ plusCount x).val) :=
    mem_rightPrefixes_iff.mpr
      ⟨birthdayTruncation_appendMinuses_of_lt _ ht, strictAnti_appendMinuses _ ht⟩
  have hsource := rightPrefixes_subset_of_birthdayTruncation_eq hpre hstage
  rw [birthdayTruncation_real_mul_wpow_minus_block hr ha0 ha hl x ht.le]
  exact (mem_rightPrefixes_iff.mp hsource).2


/-- Every positive-real monomial sign comes from its initial monomial or a coefficient sign block.
-/
theorem real_mul_wpow_position {r : ℝ} (hr : 0 < r) (x : Surreal.{u}) {j : Ordinal.{u}}
    (hj : j < ((r : Surreal.{u}) * ω^ x).birthday.val) :
    (j < (ω^ x).birthday.val ∧
      birthdayTruncation ((r : Surreal.{u}) * ω^ x) (NatOrdinal.of j) =
        birthdayTruncation (ω^ x) (NatOrdinal.of j) ∧
      (birthdayTruncation ((r : Surreal.{u}) * ω^ x) (NatOrdinal.of j) < (r : Surreal.{u}) * ω^ x ↔
        birthdayTruncation (ω^ x) (NatOrdinal.of j) < ω^ x) ∧
      ((r : Surreal.{u}) * ω^ x < birthdayTruncation ((r : Surreal.{u}) * ω^ x) (NatOrdinal.of j) ↔
        ω^ x < birthdayTruncation (ω^ x) (NatOrdinal.of j))) ∨
    ∃ n : ℕ, ((n + 1 : ℕ) : NatOrdinal.{u}) < (r : Surreal.{u}).birthday ∧ ∃ t : Ordinal.{u},
      t < (ω^ plusCount x).val ∧
      j = (ω^ x).birthday.val + (ω^ plusCount x).val * (n : Ordinal) + t ∧
      (birthdayTruncation ((r : Surreal.{u}) * ω^ x) (NatOrdinal.of j) < (r : Surreal.{u}) * ω^ x ↔
        birthdayTruncation (r : Surreal.{u}) ((n + 1 : ℕ) : NatOrdinal) < (r : Surreal.{u})) ∧
      ((r : Surreal.{u}) * ω^ x < birthdayTruncation ((r : Surreal.{u}) * ω^ x) (NatOrdinal.of j) ↔
        (r : Surreal.{u}) < birthdayTruncation (r : Surreal.{u}) ((n + 1 : ℕ) : NatOrdinal)) := by
  have hpre := birthdayTruncation_real_mul_wpow r hr x
  have hAb : (ω^ x).birthday ≤ ((r : Surreal.{u}) * ω^ x).birthday := by
    have ht := birthday_birthdayTruncation_le_birthday
      ((r : Surreal.{u}) * ω^ x) (ω^ x).birthday
    rwa [hpre] at ht
  by_cases hjA : j < (ω^ x).birthday.val
  · left
    have hj' : NatOrdinal.of j < (ω^ x).birthday := NatOrdinal.of.lt_iff_lt.mpr hjA
    have ht := birthdayTruncation_birthdayTruncation ((r : Surreal.{u}) * ω^ x) hj'.le hAb
    rw [hpre] at ht
    have hbj : (birthdayTruncation (ω^ x) (NatOrdinal.of j)).birthday < (ω^ x).birthday := by
      rw [birthday_birthdayTruncation _ hj'.le]
      exact hj'
    have hp := lt_birthdayTruncation_iff hAb hbj
    have hm := birthdayTruncation_lt_iff hAb hbj
    rw [hpre] at hp hm
    refine ⟨hjA, ht.symm, ?_, ?_⟩
    · rw [← ht]
      exact hp.symm
    · rw [← ht]
      exact hm.symm
  · right
    have hAj : (ω^ x).birthday.val ≤ j := le_of_not_gt hjA
    rw [birthday_real_mul_wpow hr x, NatOrdinal.val_of] at hj
    have hQ : 0 < (ω^ plusCount x).val := by
      rw [NatOrdinal.val_wpow]
      exact Ordinal.opow_pos _ Ordinal.omega0_pos
    let k := (j - (ω^ x).birthday.val) / (ω^ plusCount x).val
    let t := (j - (ω^ x).birthday.val) % (ω^ plusCount x).val
    have ht : t < (ω^ plusCount x).val := Ordinal.mod_lt _ hQ.ne'
    have hk : k < (r : Surreal.{u}).birthday.val - 1 :=
      (Ordinal.lt_mul_iff_div_lt hQ.ne').mp ((Ordinal.sub_lt_of_le hAj).mpr hj)
    have hbr : (r : Surreal.{u}).birthday.val ≤ Ordinal.omega0 :=
      NatOrdinal.val.monotone (birthday_real_le_omega0 r)
    have hkω : k < Ordinal.omega0 := hk.trans_le ((Ordinal.sub_le_self _ _).trans hbr)
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hkω
    have ha : ((n + 1 : ℕ) : NatOrdinal.{u}) < (r : Surreal.{u}).birthday := by
      have h := Ordinal.lt_sub.mp hk
      rw [hn, ← Nat.cast_add_one_comm] at h
      apply NatOrdinal.val.lt_iff_lt.mp
      simpa only [NatOrdinal.val_add_one, NatOrdinal.val_natCast, Nat.cast_add,
        Nat.cast_one] using h
    have hpos : j = (ω^ x).birthday.val + (ω^ plusCount x).val * (n : Ordinal) + t := by
      have hdiv := Ordinal.div_add_mod (j - (ω^ x).birthday.val) (ω^ plusCount x).val
      change (ω^ plusCount x).val * k + t = j - (ω^ x).birthday.val at hdiv
      rw [hn] at hdiv
      calc
        j = (ω^ x).birthday.val + (j - (ω^ x).birthday.val) :=
          (Ordinal.add_sub_cancel_of_le hAj).symm
        _ = _ := by rw [← hdiv, add_assoc]
    refine ⟨n, ha, t, ht, hpos, ?_⟩
    have ha1 : (((n + 1 : ℕ) : NatOrdinal.{u}) + 1) ≤ (r : Surreal.{u}).birthday :=
      Order.add_one_le_of_lt ha
    have ha0 : (0 : NatOrdinal.{u}) < ((n + 1 : ℕ) : NatOrdinal) := by
      exact_mod_cast Nat.succ_pos n
    have he : (((n + 1 : ℕ) : NatOrdinal.{u}).val - 1) = (n : Ordinal) := by
      rw [NatOrdinal.val_natCast]
      simpa only [Nat.cast_one, Nat.add_sub_cancel] using
        (Ordinal.natCast_sub (n + 1) 1).symm
    have hne : birthdayTruncation (r : Surreal.{u}) ((n + 1 : ℕ) : NatOrdinal) ≠
        (r : Surreal.{u}) := by
      intro heq
      have hb := birthday_birthdayTruncation (r : Surreal.{u}) ha.le
      rw [heq] at hb
      exact ha.ne hb.symm
    obtain hl | hm := lt_or_gt_of_ne hne
    · have hsign := birthdayTruncation_real_mul_wpow_plus_block_lt hr ha0 ha1 hl x ht
      rw [he, ← hpos] at hsign
      exact ⟨iff_of_true hsign hl, iff_of_false hsign.not_gt hl.not_gt⟩
    · have hsign := lt_birthdayTruncation_real_mul_wpow_minus_block hr ha0 ha1 hm x ht
      rw [he, ← hpos] at hsign
      exact ⟨iff_of_false hsign.not_gt hm.not_gt, iff_of_true hsign hm⟩


/-- Negative real coefficients negate the initial monomial and retain their original tail signs. -/
theorem neg_real_mul_wpow_position {r : ℝ} (hr : r < 0) (x : Surreal.{u}) {j : Ordinal.{u}}
    (hj : j < ((r : Surreal) * ω^ x).birthday.val) :
    (j < (ω^ x).birthday.val ∧
      birthdayTruncation ((r : Surreal) * ω^ x) (NatOrdinal.of j) =
        -birthdayTruncation (ω^ x) (NatOrdinal.of j) ∧
      (birthdayTruncation ((r : Surreal) * ω^ x) (NatOrdinal.of j) < (r : Surreal) * ω^ x ↔
        ω^ x < birthdayTruncation (ω^ x) (NatOrdinal.of j)) ∧
      ((r : Surreal) * ω^ x < birthdayTruncation ((r : Surreal) * ω^ x) (NatOrdinal.of j) ↔
        birthdayTruncation (ω^ x) (NatOrdinal.of j) < ω^ x)) ∨
    ∃ n : ℕ, ((n + 1 : ℕ) : NatOrdinal.{u}) < (r : Surreal.{u}).birthday ∧
      ∃ t : Ordinal.{u}, t < (ω^ plusCount x).val ∧
      j = (ω^ x).birthday.val + (ω^ plusCount x).val * (n : Ordinal) + t ∧
      (birthdayTruncation ((r : Surreal) * ω^ x) (NatOrdinal.of j) < (r : Surreal) * ω^ x ↔
        birthdayTruncation (r : Surreal.{u}) ((n + 1 : ℕ) : NatOrdinal) < (r : Surreal.{u})) ∧
      ((r : Surreal) * ω^ x < birthdayTruncation ((r : Surreal) * ω^ x) (NatOrdinal.of j) ↔
        (r : Surreal.{u}) < birthdayTruncation (r : Surreal.{u}) ((n + 1 : ℕ) : NatOrdinal)) := by
  have ht := real_mul_wpow_position (neg_pos.mpr hr) x (j := j)
    (by simpa only [Real.toSurreal_neg, neg_mul, birthday_neg] using hj)
  simp only [Real.toSurreal_neg, neg_mul, birthday_neg, birthdayTruncation_neg,
    neg_lt_neg_iff] at ht
  rcases ht with ⟨hjA, hval, hplus, hminus⟩ | ⟨n, hn, t, ht, hpos, hplus, hminus⟩
  · left
    refine ⟨hjA, ?_, hminus, hplus⟩
    simpa only [neg_neg] using congrArg Neg.neg hval
  · exact Or.inr ⟨n, hn, t, ht, hpos, hminus, hplus⟩


end Surreal
