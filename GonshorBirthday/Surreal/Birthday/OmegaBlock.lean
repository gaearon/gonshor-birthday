/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReciprocalCoefficient
public import Mathlib.Order.SuccPred.Limit

/-!
# Constant-sign blocks under the omega-map
-/

universe u
public noncomputable section
namespace Surreal
open Set Order

/-- Natural multiples at canonical left exponent prefixes are canonical left omega options. -/
theorem natCast_mul_wpow_mem_leftPrefixes {x v : Surreal.{u}}
    (hv : v ∈ leftPrefixes x) (n : ℕ) : (n : Surreal) * ω^ v ∈ leftPrefixes (ω^ x) := by
  obtain ⟨a, ha, rfl, hvx⟩ := mem_leftPrefixes.mp hv
  apply mem_leftPrefixes_iff.mpr
  refine ⟨birthdayTruncation_natCast_mul_wpow_birthdayTruncation x a hvx n, ?_⟩
  have ht := mul_wpow_lt_wpow (n : ℝ) hvx
  simpa only [Real.toSurreal_natCast] using ht

/-- Adding one plus sign to an exponent introduces no new right omega prefixes. -/
theorem rightPrefixes_wpow_appendPlus (x : Surreal.{u}) :
    rightPrefixes (ω^ appendPlus x) = rightPrefixes (ω^ x) := by
  have hpre : birthdayTruncation (ω^ appendPlus x) (ω^ x).birthday = ω^ x := by
    have ht := birthdayTruncation_wpow_birthdayTruncation (appendPlus x) x.birthday
    rwa [birthdayTruncation_appendPlus] at ht
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨v, hv, n, hcz⟩ := exists_inv_two_pow_mul_wpow_le_of_mem_rightPrefixes hz
    have hvx := hv
    rw [rightPrefixes_appendPlus] at hvx
    have hc := inv_two_pow_mul_wpow_mem_rightPrefixes hvx n
    have hcy := inv_two_pow_mul_wpow_mem_rightPrefixes hv n
    have hzpre := (mem_rightPrefixes_iff.mp hz).1
    have ht := birthdayTruncation_eq_of_right_between
      (birthday_lt_of_mem_rightPrefixes hz).le (mem_rightPrefixes_iff.mp hcy).2.le
      (by rwa [hzpre])
    rw [hzpre] at ht
    exact mem_rightPrefixes_iff.mpr
      ⟨birthdayTruncation_eq_trans (mem_rightPrefixes_iff.mp hc).1 ht,
        (mem_rightPrefixes_iff.mp hc).2.trans_le hcz⟩
  · exact rightPrefixes_subset_of_birthdayTruncation_eq hpre

/-- One plus exponent sign appends a full omega-length block of pure-power plus signs. -/
theorem wpow_appendPlus (x : Surreal.{u}) :
    ω^ appendPlus x = appendPluses (ω^ x) ((ω^ plusCount x).val * Ordinal.omega0) := by
  have hpre : birthdayTruncation (ω^ appendPlus x) (ω^ x).birthday = ω^ x := by
    have ht := birthdayTruncation_wpow_birthdayTruncation (appendPlus x) x.birthday
    rwa [birthdayTruncation_appendPlus] at ht
  have hb : (ω^ x).birthday ≤ (ω^ appendPlus x).birthday := by
    have ht := birthday_birthdayTruncation_le_birthday
      (ω^ appendPlus x) (ω^ x).birthday
    rwa [hpre] at ht
  let d : Ordinal.{u} := (ω^ appendPlus x).birthday.val - (ω^ x).birthday.val
  have he : ω^ appendPlus x = appendPluses (ω^ x) d := by
    apply Eq.symm
    apply (appendPluses_eq_iff _ _ _).mpr
    constructor
    · rw [show (ω^ x).birthday.val + d = (ω^ appendPlus x).birthday.val from
        Ordinal.add_sub_cancel_of_le (NatOrdinal.val.monotone hb), NatOrdinal.of_val]
    · exact rightPrefixes_wpow_appendPlus x
  have hc := congrArg (fun z : Surreal.{u} ↦ (plusCount z).val) he
  rw [plusCount_wpow, plusCount_appendPlus, plusCount_appendPluses,
    NatOrdinal.val_of, plusCount_wpow] at hc
  have hc' : (ω^ plusCount x).val * Ordinal.omega0 = (ω^ plusCount x).val + d := by
    simpa only [NatOrdinal.val_wpow, NatOrdinal.val_add_one, Ordinal.opow_add,
      Ordinal.opow_one] using hc
  have habsorb : (ω^ plusCount x).val + (ω^ plusCount x).val * Ordinal.omega0 =
      (ω^ plusCount x).val * Ordinal.omega0 := by
    calc
      _ = (ω^ plusCount x).val * (1 + Ordinal.omega0) := by rw [mul_add, mul_one]
      _ = _ := by simp
  have hd : d = (ω^ plusCount x).val * Ordinal.omega0 :=
    add_left_cancel (hc'.symm.trans habsorb.symm)
  rwa [hd] at he

/-- The exact birthday increment for a plus exponent sign is its pure-power omega block. -/
theorem birthday_wpow_appendPlus (x : Surreal.{u}) :
    (ω^ appendPlus x).birthday = NatOrdinal.of
      ((ω^ x).birthday.val + (ω^ plusCount x).val * Ordinal.omega0) := by
  rw [wpow_appendPlus, birthday_appendPluses]


/-- Adding a minus sign preserves the canonical left-prefix set. -/
theorem leftPrefixes_appendMinus (x : Surreal.{u}) :
    leftPrefixes (appendMinus x) = leftPrefixes x := by
  rw [← appendMinuses_one, leftPrefixes_appendMinuses]

/-- Adding a minus sign inserts its source among the canonical right prefixes. -/
theorem rightPrefixes_appendMinus (x : Surreal.{u}) :
    rightPrefixes (appendMinus x) = insert x (rightPrefixes x) := by
  rw [← appendMinuses_one, appendMinuses_eq_neg, appendPluses_one, rightPrefixes_neg,
    leftPrefixes_appendPlus, Set.image_insert_eq, neg_neg, ← rightPrefixes_neg, neg_neg]

/-- Adding one minus sign to an exponent introduces no new left omega prefixes. -/
theorem leftPrefixes_wpow_appendMinus (x : Surreal.{u}) :
    leftPrefixes (ω^ appendMinus x) = leftPrefixes (ω^ x) := by
  have hpre : birthdayTruncation (ω^ appendMinus x) (ω^ x).birthday = ω^ x := by
    have ht := birthdayTruncation_wpow_birthdayTruncation (appendMinus x) x.birthday
    rwa [birthdayTruncation_appendMinus] at ht
  apply Set.Subset.antisymm
  · intro z hz
    obtain rfl | ⟨v, hv, n, hzc⟩ := exists_natCast_mul_wpow_ge_of_mem_leftPrefixes hz
    · exact zero_mem_leftPrefixes (wpow_pos x)
    have hvx := hv
    rw [leftPrefixes_appendMinus] at hvx
    have hc := natCast_mul_wpow_mem_leftPrefixes hvx n
    have hcy := natCast_mul_wpow_mem_leftPrefixes hv n
    have hzpre := (mem_leftPrefixes_iff.mp hz).1
    have ht := birthdayTruncation_eq_of_left_between
      (birthday_lt_of_mem_leftPrefixes hz).le (by rwa [hzpre])
      (mem_leftPrefixes_iff.mp hcy).2.le
    rw [hzpre] at ht
    exact mem_leftPrefixes_iff.mpr
      ⟨birthdayTruncation_eq_trans (mem_leftPrefixes_iff.mp hc).1 ht,
        hzc.trans_lt (mem_leftPrefixes_iff.mp hc).2⟩
  · exact leftPrefixes_subset_of_birthdayTruncation_eq hpre


/-- The exact birthday increment for a minus exponent sign is its pure-power omega block. -/
theorem birthday_wpow_appendMinus (x : Surreal.{u}) :
    (ω^ appendMinus x).birthday = NatOrdinal.of
      ((ω^ x).birthday.val + (ω^ plusCount x).val * Ordinal.omega0) := by
  have hQ : 0 < (ω^ plusCount x).val := by
    rw [NatOrdinal.val_wpow]
    exact Ordinal.opow_pos _ Ordinal.omega0_pos
  have hQw : 0 < (ω^ plusCount x).val * Ordinal.omega0 := mul_pos hQ Ordinal.omega0_pos
  have hx : x ∈ rightPrefixes (appendMinus x) := by
    rw [rightPrefixes_appendMinus]
    exact Set.mem_insert x _
  apply le_antisymm
  · apply (birthday_le_iff_forall_prefixes _ _).mpr
    constructor
    · intro p hp
      rw [leftPrefixes_wpow_appendMinus] at hp
      exact (birthday_lt_of_mem_leftPrefixes hp).trans_le (NatOrdinal.of.monotone le_self_add)
    · intro p hp
      obtain ⟨v, hv, n, hcp⟩ := exists_inv_two_pow_mul_wpow_le_of_mem_rightPrefixes hp
      have hc := inv_two_pow_mul_wpow_mem_rightPrefixes hv n
      have hneg : -p ∈ leftPrefixes (-(ω^ appendMinus x)) := neg_mem_leftPrefixes_iff.mpr hp
      have hpb := birthday_le_of_left_between hneg (neg_le_neg hcp)
        (neg_le_neg (mem_rightPrefixes_iff.mp hc).2.le)
      rw [birthday_neg, birthday_neg] at hpb
      rw [rightPrefixes_appendMinus] at hv
      rcases hv with rfl | hv
      · apply hpb.trans_lt
        rw [birthday_inv_two_pow_mul_wpow]
        exact NatOrdinal.of.strictMono (add_lt_add_right
          (mul_lt_mul_of_pos_left (Ordinal.natCast_lt_omega0 n) hQ) _)
      · have hc' := inv_two_pow_mul_wpow_mem_rightPrefixes hv n
        exact (hpb.trans_lt (birthday_lt_of_mem_rightPrefixes hc')).trans_le
          (NatOrdinal.of.monotone le_self_add)
  · apply NatOrdinal.val.le_iff_le.mp
    rw [NatOrdinal.val_of]
    apply (Ordinal.add_le_iff hQw.ne').mpr
    intro d hd
    obtain ⟨k, hk, hdk⟩ := (Ordinal.lt_mul_iff_of_isSuccLimit Ordinal.isSuccLimit_omega0).mp hd
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hk
    have hc := inv_two_pow_mul_wpow_mem_rightPrefixes hx n
    have hb := birthday_lt_of_mem_rightPrefixes hc
    rw [birthday_inv_two_pow_mul_wpow] at hb
    exact (add_le_add_right hdk.le _).trans_lt (by
      simpa only [NatOrdinal.val_of] using NatOrdinal.val.strictMono hb)

/-- One minus exponent sign appends a full omega-length block of pure-power minus signs. -/
theorem wpow_appendMinus (x : Surreal.{u}) :
    ω^ appendMinus x = appendMinuses (ω^ x) ((ω^ plusCount x).val * Ordinal.omega0) := by
  have he : appendPluses (-(ω^ x)) ((ω^ plusCount x).val * Ordinal.omega0) =
      -(ω^ appendMinus x) := by
    apply (appendPluses_eq_iff _ _ _).mpr
    constructor
    · rw [birthday_neg, birthday_neg, birthday_wpow_appendMinus]
    · rw [rightPrefixes_neg, rightPrefixes_neg, leftPrefixes_wpow_appendMinus]
  rw [appendMinuses_eq_neg, he, neg_neg]


/-- Every adjacent exponent prefix adds its exact sign-independent birthday block. -/
theorem birthday_wpow_birthdayTruncation_add_one (x : Surreal.{u}) {a : NatOrdinal.{u}}
    (ha : a + 1 ≤ x.birthday) :
    (ω^ birthdayTruncation x (a + 1)).birthday = NatOrdinal.of
      ((ω^ birthdayTruncation x a).birthday.val +
        (ω^ plusCount (birthdayTruncation x a)).val * Ordinal.omega0) := by
  have hal : a < x.birthday := (lt_add_one a).trans_le ha
  have hne : birthdayTruncation x a ≠ x := by
    intro he
    have ht := birthday_birthdayTruncation x hal.le
    rw [he] at ht
    exact hal.ne ht.symm
  obtain hl | hr := lt_or_gt_of_ne hne
  · rw [birthdayTruncation_add_one_eq_appendPlus x ha hl, birthday_wpow_appendPlus]
  · rw [birthdayTruncation_add_one_eq_appendMinus x ha hr, birthday_wpow_appendMinus]

/-- At a limit exponent birthday, omega birthdays are the supremum of prefix omega birthdays. -/
theorem birthday_wpow_le_iff_of_isSuccLimit (x : Surreal.{u})
    (hlim : IsSuccLimit x.birthday.val) (o : NatOrdinal.{u}) :
    (ω^ x).birthday ≤ o ↔
      ∀ a < x.birthday, (ω^ birthdayTruncation x a).birthday ≤ o := by
  constructor
  · intro h a ha
    have ht := birthdayTruncation_wpow_birthdayTruncation x a
    have hb := birthday_birthdayTruncation_le_birthday (ω^ x)
      (ω^ birthdayTruncation x a).birthday
    rw [ht] at hb
    exact hb.trans h
  · intro h
    have hb0 : (0 : NatOrdinal.{u}) < x.birthday :=
      NatOrdinal.val.lt_iff_lt.mp (by simpa only [NatOrdinal.val_zero] using hlim.pos)
    have ho : 0 < o := by
      have ht : (1 : NatOrdinal.{u}) ≤ o := by simpa using h 0 hb0
      exact lt_of_lt_of_le (by norm_num : (0 : NatOrdinal.{u}) < 1) ht
    have hcoeff : ∀ (v : Surreal.{u}), birthdayTruncation x v.birthday = v →
        v.birthday < x.birthday → ∀ n : ℕ,
        NatOrdinal.of ((ω^ v).birthday.val + (ω^ plusCount v).val * (n : Ordinal)) < o := by
      intro v hv hvb n
      have hb1 : v.birthday + 1 < x.birthday := by
        apply NatOrdinal.val.lt_iff_lt.mp
        rw [NatOrdinal.val_add_one]
        exact hlim.succ_lt (NatOrdinal.val.strictMono hvb)
      have hnext := birthday_wpow_birthdayTruncation_add_one x hb1.le
      rw [hv] at hnext
      have hQ : 0 < (ω^ plusCount v).val := by
        rw [NatOrdinal.val_wpow]
        exact Ordinal.opow_pos _ Ordinal.omega0_pos
      have ht := NatOrdinal.of.strictMono (add_lt_add_right
        (mul_lt_mul_of_pos_left (Ordinal.natCast_lt_omega0 n) hQ) (ω^ v).birthday.val)
      rw [← hnext] at ht
      exact ht.trans_le (h (v.birthday + 1) hb1)
    apply (birthday_le_iff_forall_prefixes _ _).mpr
    constructor
    · intro z hz
      obtain rfl | ⟨v, hv, n, hzn⟩ := exists_natCast_mul_wpow_ge_of_mem_leftPrefixes hz
      · simpa using ho
      have hnm : (n : Surreal.{u}) ≤ ((n + 1 : ℕ) : Surreal) := by exact_mod_cast Nat.le_succ n
      have hzn' := hzn.trans (mul_le_mul_of_nonneg_right hnm (wpow_nonneg v))
      have hc := natCast_mul_wpow_mem_leftPrefixes hv (n + 1)
      have hpb := birthday_le_of_left_between hz hzn' (mem_leftPrefixes_iff.mp hc).2.le
      rw [birthday_natCast_mul_wpow] at hpb
      exact hpb.trans_lt (hcoeff v (mem_leftPrefixes_iff.mp hv).1
        (birthday_lt_of_mem_leftPrefixes hv) n)
    · intro z hz
      obtain ⟨v, hv, n, hcz⟩ := exists_inv_two_pow_mul_wpow_le_of_mem_rightPrefixes hz
      have hc := inv_two_pow_mul_wpow_mem_rightPrefixes hv n
      have hneg : -z ∈ leftPrefixes (-(ω^ x)) := neg_mem_leftPrefixes_iff.mpr hz
      have hpb := birthday_le_of_left_between hneg (neg_le_neg hcz)
        (neg_le_neg (mem_rightPrefixes_iff.mp hc).2.le)
      rw [birthday_neg, birthday_neg, birthday_inv_two_pow_mul_wpow] at hpb
      exact hpb.trans_lt (hcoeff v (mem_rightPrefixes_iff.mp hv).1
        (birthday_lt_of_mem_rightPrefixes hv) n)


end Surreal
