/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.CoefficientCofinality
public import GonshorBirthday.Surreal.Birthday.Minus

import GonshorBirthday.Surreal.Birthday.Real

/-!
# Real coefficient word birthdays under monomial scaling
-/

universe u
public noncomputable section
namespace Surreal
open Set IGame

/-- A proper positive real coefficient prefix costs at least one complete monomial block. -/
theorem oadd_wpow_plusCount_le_birthday_real_mul_wpow {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hne : r ≠ s)
    (hp : birthdayTruncation (s : Surreal.{u}) (r : Surreal).birthday = (r : Surreal))
    (x : Surreal.{u}) : NatOrdinal.of
      (((r : Surreal) * ω^ x).birthday.val + (ω^ plusCount x).val) ≤
        ((s : Surreal) * ω^ x).birthday := by
  have hQ : 0 < (ω^ plusCount x).val := by
    rw [NatOrdinal.val_wpow]
    exact Ordinal.opow_pos _ Ordinal.omega0_pos
  apply NatOrdinal.val.le_iff_le.mp
  rw [NatOrdinal.val_of]
  apply (Ordinal.add_le_iff hQ.ne').mpr
  intro d hd
  have hd' : NatOrdinal.of d < plusCount (ω^ x) := by
    rw [plusCount_wpow]
    exact NatOrdinal.of.lt_iff_lt.mpr hd
  obtain ⟨a, ha, hda⟩ := exists_leftPrefixes_plusCount_ge hd'
  have hstrict : NatOrdinal.of
      (((r : Surreal) * ω^ x).birthday.val + (plusCount a).val) <
        ((s : Surreal) * ω^ x).birthday := by
    obtain hrs | hsr := lt_or_gt_of_ne hne
    · have ht := birthdayTruncation_real_mul_wpow_add_leftPrefix hr hrs hp ha
      have hsmall := lt_real_mul_wpow_of_mem_leftPrefixes (sub_pos.mpr hrs) ha
      rw [Real.toSurreal_sub, sub_mul] at hsmall
      have hval : (r : Surreal) * ω^ x + a < (s : Surreal) * ω^ x := by
        linarith only [hsmall]
      have hmember := mem_leftPrefixes_iff.mpr ⟨ht, hval⟩
      have hb := birthday_lt_of_mem_leftPrefixes hmember
      rwa [birthday_real_mul_wpow_add_leftPrefix hr hrs hp ha] at hb
    · have ht := birthdayTruncation_real_mul_wpow_sub_leftPrefix hs hsr hp ha
      have hsmall := lt_real_mul_wpow_of_mem_leftPrefixes (sub_pos.mpr hsr) ha
      rw [Real.toSurreal_sub, sub_mul] at hsmall
      have hval : (s : Surreal) * ω^ x < (r : Surreal) * ω^ x - a := by
        linarith only [hsmall]
      have hmember := mem_rightPrefixes_iff.mpr ⟨ht, hval⟩
      have hb := birthday_lt_of_mem_rightPrefixes hmember
      rwa [birthday_real_mul_wpow_sub_leftPrefix hs hsr hp ha] at hb
  have hda' : d ≤ (plusCount a).val := by
    simpa only [NatOrdinal.val_of] using NatOrdinal.val.monotone hda
  exact (add_le_add_right hda' _).trans_lt (by
    simpa only [NatOrdinal.val_of] using NatOrdinal.val.strictMono hstrict)

/-- Bounding all older coefficient-prefix stages bounds the full positive monomial birthday. -/
theorem birthday_real_mul_wpow_le_of_prefixes {r : ℝ} (hr : 0 < r)
    (x : Surreal.{u}) (M : NatOrdinal.{u}) (hA : (ω^ x).birthday ≤ M)
    (hcoeff : ∀ s : ℝ, 0 < s →
      ((s : Surreal.{u}) ∈ leftPrefixes (r : Surreal) ∨
        (s : Surreal.{u}) ∈ rightPrefixes (r : Surreal)) →
      ∀ a ∈ leftPrefixes (ω^ x), NatOrdinal.of
        (((s : Surreal) * ω^ x).birthday.val + (plusCount a).val) < M) :
    ((r : Surreal) * ω^ x).birthday ≤ M := by
  apply (birthday_le_iff_forall_prefixes _ _).mpr
  constructor
  · intro z hz
    obtain ⟨a, ha, hza⟩ | ⟨s, hs, hsr, a, ha, hza⟩ :=
      exists_leftPrefixes_real_mul_wpow_ge hr hz
    · have haS := leftPrefixes_subset_of_birthdayTruncation_eq
        (birthdayTruncation_real_mul_wpow r hr x) ha
      have hpb := birthday_le_of_left_between hz hza (mem_leftPrefixes_iff.mp haS).2.le
      exact (hpb.trans_lt (birthday_lt_of_mem_leftPrefixes ha)).trans_le hA
    · have hsr' : s < r := Real.toSurreal_lt_iff.mp (mem_leftPrefixes_iff.mp hsr).2
      have hp := (mem_leftPrefixes_iff.mp hsr).1
      have hsmall := lt_real_mul_wpow_of_mem_leftPrefixes (sub_pos.mpr hsr') ha
      rw [Real.toSurreal_sub, sub_mul] at hsmall
      have hval : (s : Surreal) * ω^ x + a < (r : Surreal) * ω^ x := by
        linarith only [hsmall]
      have hpb := birthday_le_of_left_between hz hza hval.le
      rw [birthday_real_mul_wpow_add_leftPrefix hs hsr' hp ha] at hpb
      exact hpb.trans_lt (hcoeff s hs (Or.inl hsr) a ha)
  · intro z hz
    obtain ⟨a, ha, haz⟩ | ⟨s, hs, hsr, a, ha, haz⟩ :=
      exists_rightPrefixes_real_mul_wpow_le hr hz
    · have haS := rightPrefixes_subset_of_birthdayTruncation_eq
        (birthdayTruncation_real_mul_wpow r hr x) ha
      have hneg : -z ∈ leftPrefixes (-((r : Surreal) * ω^ x)) :=
        neg_mem_leftPrefixes_iff.mpr hz
      have hpb := birthday_le_of_left_between hneg (neg_le_neg haz)
        (neg_le_neg (mem_rightPrefixes_iff.mp haS).2.le)
      rw [birthday_neg, birthday_neg] at hpb
      exact (hpb.trans_lt (birthday_lt_of_mem_rightPrefixes ha)).trans_le hA
    · have hrs : r < s := Real.toSurreal_lt_iff.mp (mem_rightPrefixes_iff.mp hsr).2
      have hp := (mem_rightPrefixes_iff.mp hsr).1
      have hsmall := lt_real_mul_wpow_of_mem_leftPrefixes (sub_pos.mpr hrs) ha
      rw [Real.toSurreal_sub, sub_mul] at hsmall
      have hval : (r : Surreal) * ω^ x < (s : Surreal) * ω^ x - a := by
        linarith only [hsmall]
      have hneg : -z ∈ leftPrefixes (-((r : Surreal) * ω^ x)) :=
        neg_mem_leftPrefixes_iff.mpr hz
      have hpb := birthday_le_of_left_between hneg (neg_le_neg haz) (neg_le_neg hval.le)
      rw [birthday_neg, birthday_neg, birthday_real_mul_wpow_sub_leftPrefix hr hrs hp ha] at hpb
      exact hpb.trans_lt (hcoeff s hs (Or.inr hsr) a ha)

private theorem exists_birthday_nat_tail {s : ℝ} (hs : 0 < s) {n : ℕ}
    (hb : (s : Surreal.{u}).birthday < ((n + 1 : ℕ) : NatOrdinal.{u})) :
    ∃ m < n, (s : Surreal.{u}).birthday = ((m + 1 : ℕ) : NatOrdinal.{u}) := by
  have hbval : (s : Surreal.{u}).birthday.val ≤ ((n + 1 : ℕ) : Ordinal.{u}) := by
    simpa only [NatOrdinal.val_natCast] using (NatOrdinal.val.strictMono hb).le
  obtain ⟨k, hk⟩ := Ordinal.eq_natCast_of_le_natCast hbval
  have hbk : (s : Surreal.{u}).birthday = (k : NatOrdinal.{u}) := by
    apply NatOrdinal.val.injective
    simpa only [NatOrdinal.val_natCast] using hk
  have hkp : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    rw [hk0, Nat.cast_zero, birthday_eq_zero] at hbk
    have hpos := Real.toSurreal_pos_iff.mpr hs
    rw [hbk] at hpos
    exact hpos.false
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hkp)
  refine ⟨m, ?_, by simpa only [Nat.succ_eq_add_one] using hbk⟩
  have ht : m + 1 < n + 1 := by rw [hbk] at hb; exact_mod_cast hb
  omega

/-- A positive finite real coefficient repeats one pure-power block per sign after its first. -/
theorem birthday_real_mul_wpow_of_birthday_nat {r : ℝ} (hr : 0 < r) {n : ℕ}
    (hb : (r : Surreal.{u}).birthday = ((n + 1 : ℕ) : NatOrdinal.{u})) (x : Surreal.{u}) :
    ((r : Surreal) * ω^ x).birthday = NatOrdinal.of
      ((ω^ x).birthday.val + (ω^ plusCount x).val * (n : Ordinal)) := by
  have aux : ∀ n : ℕ, ∀ r : ℝ, 0 < r →
      (r : Surreal.{u}).birthday = ((n + 1 : ℕ) : NatOrdinal.{u}) →
      ((r : Surreal) * ω^ x).birthday = NatOrdinal.of
        ((ω^ x).birthday.val + (ω^ plusCount x).val * (n : Ordinal)) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro r hr hbr
      cases n with
      | zero =>
        have h1 : (r : Surreal.{u}) = 1 := by
          have ht : (r : Surreal.{u}).birthday = 1 := by simpa using hbr
          obtain ht | ht := birthday_eq_one.mp ht
          · exact ht
          · have hpos := Real.toSurreal_pos_iff.mpr hr
            rw [ht] at hpos
            norm_num at hpos
        simp [h1]
      | succ n =>
        apply le_antisymm
        · apply birthday_real_mul_wpow_le_of_prefixes hr x _
            (NatOrdinal.of.monotone le_self_add)
          intro s hs hsp a ha
          have hsb : (s : Surreal.{u}).birthday < (r : Surreal).birthday := by
            rcases hsp with hsp | hsp
            · exact birthday_lt_of_mem_leftPrefixes hsp
            · exact birthday_lt_of_mem_rightPrefixes hsp
          rw [hbr] at hsb
          obtain ⟨m, hm, hbs⟩ := exists_birthday_nat_tail hs hsb
          have hi := ih m hm s hs hbs
          rw [hi, NatOrdinal.val_of]
          have hpa : (plusCount a).val < (ω^ plusCount x).val := by
            have ht := plusCount_lt_of_mem_leftPrefixes ha
            rw [plusCount_wpow] at ht
            exact NatOrdinal.val.strictMono ht
          have hlt := add_lt_add_right hpa
            ((ω^ x).birthday.val + (ω^ plusCount x).val * (m : Ordinal))
          have he : (ω^ x).birthday.val + (ω^ plusCount x).val * (m : Ordinal) +
              (ω^ plusCount x).val = (ω^ x).birthday.val +
                (ω^ plusCount x).val * ((m : Ordinal) + 1) := by
            rw [mul_add, mul_one, add_assoc]
          rw [he] at hlt
          apply (NatOrdinal.of.strictMono hlt).trans_le
          apply NatOrdinal.of.monotone
          apply add_le_add_right
          apply mul_le_mul_right
          exact_mod_cast (Nat.succ_le_of_lt hm)
        · have hplt : ((n + 1 : ℕ) : NatOrdinal.{u}) < (r : Surreal.{u}).birthday := by
            rw [hbr]
            exact_mod_cast Nat.lt_succ_self (n + 1)
          let y : Surreal.{u} := birthdayTruncation (r : Surreal) ((n + 1 : ℕ) : NatOrdinal)
          have hyb : y.birthday = ((n + 1 : ℕ) : NatOrdinal.{u}) :=
            birthday_birthdayTruncation _ hplt.le
          obtain ⟨s, hsval⟩ := birthdayTruncation_real_mem_range_real r
            (((n + 1 : ℕ) : NatOrdinal.{u}))
          change (s : Surreal.{u}) = y at hsval
          have hbs : (s : Surreal.{u}).birthday = ((n + 1 : ℕ) : NatOrdinal.{u}) := by
            rw [hsval, hyb]
          have hs : 0 < s := by
            apply Real.toSurreal_pos_iff.mp
            rw [hsval]
            apply (lt_birthdayTruncation_iff hplt.le (by simp)).mpr
            exact Real.toSurreal_pos_iff.mpr hr
          have hsr : s ≠ r := by
            intro he
            rw [he] at hbs
            exact hplt.ne hbs.symm
          have hp : birthdayTruncation (r : Surreal.{u}) (s : Surreal).birthday =
              (s : Surreal) := by
            rw [hsval, hyb]
          have hi := ih n (Nat.lt_succ_self n) s hs hbs
          have ht := oadd_wpow_plusCount_le_birthday_real_mul_wpow hs hr hsr hp x
          rw [hi, NatOrdinal.val_of] at ht
          simpa only [Nat.cast_succ, mul_add, mul_one, add_assoc] using ht
  exact aux n r hr hb


private theorem exists_birthday_nat_tail_of_lt_omega0 {s : ℝ} (hs : 0 < s)
    (hb : (s : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) :
    ∃ n : ℕ, (s : Surreal.{u}).birthday = ((n + 1 : ℕ) : NatOrdinal.{u}) := by
  obtain ⟨k, hk⟩ := Ordinal.lt_omega0.mp (NatOrdinal.val.strictMono hb)
  have hbk : (s : Surreal.{u}).birthday = (k : NatOrdinal.{u}) := by
    apply NatOrdinal.val.injective
    simpa only [NatOrdinal.val_natCast] using hk
  have hb' : (s : Surreal.{u}).birthday < ((k + 1 : ℕ) : NatOrdinal.{u}) := by
    rw [hbk]
    exact_mod_cast Nat.lt_succ_self k
  obtain ⟨n, hn, hbn⟩ := exists_birthday_nat_tail hs hb'
  exact ⟨n, hbn⟩

/-- A positive real of infinite birthday has an omega sequence of complete coefficient blocks. -/
theorem birthday_real_mul_wpow_of_birthday_omega0 {r : ℝ} (hr : 0 < r)
    (hb : (r : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0) (x : Surreal.{u}) :
    ((r : Surreal) * ω^ x).birthday = NatOrdinal.of
      ((ω^ x).birthday.val + (ω^ plusCount x).val * Ordinal.omega0) := by
  have hQ : 0 < (ω^ plusCount x).val := by
    rw [NatOrdinal.val_wpow]
    exact Ordinal.opow_pos _ Ordinal.omega0_pos
  apply le_antisymm
  · apply birthday_real_mul_wpow_le_of_prefixes hr x _
      (NatOrdinal.of.monotone le_self_add)
    intro s hs hsp a ha
    have hsb : (s : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 := by
      rw [← hb]
      rcases hsp with hsp | hsp
      · exact birthday_lt_of_mem_leftPrefixes hsp
      · exact birthday_lt_of_mem_rightPrefixes hsp
    obtain ⟨n, hbs⟩ := exists_birthday_nat_tail_of_lt_omega0 hs hsb
    rw [birthday_real_mul_wpow_of_birthday_nat hs hbs x, NatOrdinal.val_of]
    have hpa : (plusCount a).val < (ω^ plusCount x).val := by
      have ht := plusCount_lt_of_mem_leftPrefixes ha
      rw [plusCount_wpow] at ht
      exact NatOrdinal.val.strictMono ht
    have ht := add_lt_add_right hpa
      ((ω^ x).birthday.val + (ω^ plusCount x).val * (n : Ordinal))
    have he : (ω^ x).birthday.val + (ω^ plusCount x).val * (n : Ordinal) +
        (ω^ plusCount x).val = (ω^ x).birthday.val +
          (ω^ plusCount x).val * ((n : Ordinal) + 1) := by rw [mul_add, mul_one, add_assoc]
    rw [he] at ht
    apply (NatOrdinal.of.strictMono ht).trans
    apply NatOrdinal.of.strictMono
    apply add_lt_add_right
    apply mul_lt_mul_of_pos_left _ hQ
    simpa only [Nat.cast_add, Nat.cast_one] using Ordinal.natCast_lt_omega0 (n + 1)
  · apply NatOrdinal.val.le_iff_le.mp
    rw [NatOrdinal.val_of]
    have hQw := mul_pos hQ Ordinal.omega0_pos
    apply (Ordinal.add_le_iff hQw.ne').mpr
    intro d hd
    obtain ⟨k, hk, hdk⟩ := (Ordinal.lt_mul_iff_of_isSuccLimit Ordinal.isSuccLimit_omega0).mp hd
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hk
    have hplt : ((n + 1 : ℕ) : NatOrdinal.{u}) < (r : Surreal.{u}).birthday := by
      rw [hb]
      exact NatOrdinal.of.strictMono (Ordinal.natCast_lt_omega0 (n + 1))
    let y : Surreal.{u} := birthdayTruncation (r : Surreal) ((n + 1 : ℕ) : NatOrdinal)
    have hyb : y.birthday = ((n + 1 : ℕ) : NatOrdinal.{u}) :=
      birthday_birthdayTruncation _ hplt.le
    obtain ⟨s, hsval⟩ := birthdayTruncation_real_mem_range_real r
      (((n + 1 : ℕ) : NatOrdinal.{u}))
    change (s : Surreal.{u}) = y at hsval
    have hbs : (s : Surreal.{u}).birthday = ((n + 1 : ℕ) : NatOrdinal.{u}) := by
      rw [hsval, hyb]
    have hs : 0 < s := by
      apply Real.toSurreal_pos_iff.mp
      rw [hsval]
      apply (lt_birthdayTruncation_iff hplt.le (by simp)).mpr
      exact Real.toSurreal_pos_iff.mpr hr
    have hp : birthdayTruncation (r : Surreal.{u}) (s : Surreal).birthday = (s : Surreal) := by
      rw [hsval, hyb]
    have hscaled := birthdayTruncation_real_mul_wpow_of_prefix hp x
    have hbound := birthday_birthdayTruncation_le_birthday
      ((r : Surreal) * ω^ x) ((s : Surreal) * ω^ x).birthday
    rw [hscaled, birthday_real_mul_wpow_of_birthday_nat hs hbs x] at hbound
    have ht := NatOrdinal.val.monotone hbound
    exact (add_lt_add_right hdk _).trans_le (by simpa only [NatOrdinal.val_of] using ht)

/-- The exact birthday of every positive real coefficient monomial. -/
theorem birthday_real_mul_wpow {r : ℝ} (hr : 0 < r) (x : Surreal.{u}) :
    ((r : Surreal) * ω^ x).birthday = NatOrdinal.of
      ((ω^ x).birthday.val + (ω^ plusCount x).val * ((r : Surreal.{u}).birthday.val - 1)) := by
  obtain hb | hb := (birthday_real_le_omega0 r).lt_or_eq
  · obtain ⟨n, hbn⟩ := exists_birthday_nat_tail_of_lt_omega0 hr hb
    rw [birthday_real_mul_wpow_of_birthday_nat hr hbn x, hbn, NatOrdinal.val_natCast]
    have he : (((n + 1 : ℕ) : Ordinal.{u}) - 1) = (n : Ordinal) := by
      simpa only [Nat.cast_one, Nat.add_sub_cancel] using
        (Ordinal.natCast_sub (n + 1) 1).symm
    rw [he]
  · rw [birthday_real_mul_wpow_of_birthday_omega0 hr hb x, hb, NatOrdinal.val_of]
    have he : Ordinal.omega0 - 1 = Ordinal.omega0 := by
      calc
        _ = (1 + Ordinal.omega0) - 1 := by simp
        _ = _ := Ordinal.add_sub_cancel 1 _
    rw [he]


/-- The exact birthday of every nonzero real coefficient monomial, of either sign. -/
theorem birthday_real_mul_wpow_of_ne_zero {r : ℝ} (hr : r ≠ 0) (x : Surreal.{u}) :
    ((r : Surreal) * ω^ x).birthday = NatOrdinal.of
      ((ω^ x).birthday.val + (ω^ plusCount x).val * ((r : Surreal.{u}).birthday.val - 1)) := by
  obtain hrn | hrp := lt_or_gt_of_ne hr
  · have ht := birthday_real_mul_wpow (r := -r) (neg_pos.mpr hrn) x
    simpa only [Real.toSurreal_neg, neg_mul, birthday_neg] using ht
  · exact birthday_real_mul_wpow hrp x


/-- Adjacent positive real coefficient birthdays differ by exactly one monomial block. -/
theorem birthday_real_mul_wpow_of_birthday_add_one {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hb : (s : Surreal.{u}).birthday = (r : Surreal).birthday + 1) (x : Surreal.{u}) :
    ((s : Surreal) * ω^ x).birthday =
      NatOrdinal.of (((r : Surreal) * ω^ x).birthday.val + (ω^ plusCount x).val) := by
  have hrf : (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 :=
    ((lt_add_one _).trans_eq hb.symm).trans_le (birthday_real_le_omega0 s)
  obtain ⟨n, hrb⟩ := exists_birthday_nat_tail_of_lt_omega0 hr hrf
  have hsb : (s : Surreal.{u}).birthday = (((n + 1) + 1 : ℕ) : NatOrdinal.{u}) := by
    rw [hb, hrb]
    simp only [Nat.cast_add, Nat.cast_one]
  rw [birthday_real_mul_wpow_of_birthday_nat hr hrb x,
    birthday_real_mul_wpow_of_birthday_nat hs hsb x, NatOrdinal.val_of]
  simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one, add_assoc]


private theorem exists_leftPrefix_birthday_ge (x : Surreal.{u}) (H Z : NatOrdinal.{u})
    (hz : Z < NatOrdinal.of (H.val + (ω^ plusCount x).val)) :
    ∃ a ∈ leftPrefixes (ω^ x), Z ≤ NatOrdinal.of (H.val + (plusCount a).val) := by
  by_contra h
  have hQ : 0 < (ω^ plusCount x).val := by
    rw [NatOrdinal.val_wpow]
    exact Ordinal.opow_pos _ Ordinal.omega0_pos
  have hbound : NatOrdinal.of (H.val + (ω^ plusCount x).val) ≤ Z := by
    apply NatOrdinal.val.le_iff_le.mp
    rw [NatOrdinal.val_of]
    apply (Ordinal.add_le_iff hQ.ne').mpr
    intro d hd
    have hd' : NatOrdinal.of d < plusCount (ω^ x) := by
      rw [plusCount_wpow]
      exact NatOrdinal.of.lt_iff_lt.mpr hd
    obtain ⟨a, ha, hda⟩ := exists_leftPrefixes_plusCount_ge hd'
    have haZ : NatOrdinal.of (H.val + (plusCount a).val) < Z :=
      lt_of_not_ge (fun hza ↦ h ⟨a, ha, hza⟩)
    have hda' : d ≤ (plusCount a).val := by
      simpa only [NatOrdinal.val_of] using NatOrdinal.val.monotone hda
    exact (add_le_add_right hda' _).trans_lt (by
      simpa only [NatOrdinal.val_of] using NatOrdinal.val.strictMono haZ)
  exact hz.not_ge hbound

/-- One plus coefficient sign appends exactly one pure-power block after monomial scaling. -/
theorem real_mul_wpow_eq_appendPluses_of_coefficient_prefix {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r < s)
    (hp : birthdayTruncation (s : Surreal.{u}) (r : Surreal).birthday = (r : Surreal))
    (hb : (s : Surreal.{u}).birthday = (r : Surreal).birthday + 1) (x : Surreal.{u}) :
    (s : Surreal) * ω^ x = appendPluses ((r : Surreal) * ω^ x) (ω^ plusCount x).val := by
  have hpre := birthdayTruncation_real_mul_wpow_of_prefix hp x
  have hbirth := birthday_real_mul_wpow_of_birthday_add_one hr hs hb x
  have hR : rightPrefixes ((s : Surreal) * ω^ x) = rightPrefixes ((r : Surreal) * ω^ x) := by
    apply Set.Subset.antisymm
    · intro z hz
      have hzb := birthday_lt_of_mem_rightPrefixes hz
      rw [hbirth] at hzb
      obtain ⟨a, ha, hza⟩ := exists_leftPrefix_birthday_ge x _ z.birthday hzb
      have ht := birthdayTruncation_real_mul_wpow_add_leftPrefix hr hrs hp ha
      have hsmall := lt_real_mul_wpow_of_mem_leftPrefixes (sub_pos.mpr hrs) ha
      rw [Real.toSurreal_sub, sub_mul] at hsmall
      have hgap : (r : Surreal) * ω^ x + a < (s : Surreal) * ω^ x := by
        linarith only [hsmall]
      rw [← birthday_real_mul_wpow_add_leftPrefix hr hrs hp ha] at hza
      have hzstage := mem_rightPrefixes_of_birthdayTruncation_eq_of_birthday_le ht hz hza
        (hgap.trans (mem_rightPrefixes_iff.mp hz).2)
      rwa [rightPrefixes_real_mul_wpow_add_leftPrefix hr hrs hp ha] at hzstage
    · exact rightPrefixes_subset_of_birthdayTruncation_eq hpre
  exact ((appendPluses_eq_iff _ _ _).mpr ⟨hbirth, hR⟩).symm

/-- One minus coefficient sign appends exactly one pure-power block after monomial scaling. -/
theorem real_mul_wpow_eq_appendMinuses_of_coefficient_prefix {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hsr : s < r)
    (hp : birthdayTruncation (s : Surreal.{u}) (r : Surreal).birthday = (r : Surreal))
    (hb : (s : Surreal.{u}).birthday = (r : Surreal).birthday + 1) (x : Surreal.{u}) :
    (s : Surreal) * ω^ x = appendMinuses ((r : Surreal) * ω^ x) (ω^ plusCount x).val := by
  have hpre := birthdayTruncation_real_mul_wpow_of_prefix hp x
  have hbirth := birthday_real_mul_wpow_of_birthday_add_one hr hs hb x
  have hL : leftPrefixes ((s : Surreal) * ω^ x) = leftPrefixes ((r : Surreal) * ω^ x) := by
    apply Set.Subset.antisymm
    · intro z hz
      have hzb := birthday_lt_of_mem_leftPrefixes hz
      rw [hbirth] at hzb
      obtain ⟨a, ha, hza⟩ := exists_leftPrefix_birthday_ge x _ z.birthday hzb
      have ht := birthdayTruncation_real_mul_wpow_sub_leftPrefix hs hsr hp ha
      have hsmall := lt_real_mul_wpow_of_mem_leftPrefixes (sub_pos.mpr hsr) ha
      rw [Real.toSurreal_sub, sub_mul] at hsmall
      have hgap : (s : Surreal) * ω^ x < (r : Surreal) * ω^ x - a := by
        linarith only [hsmall]
      rw [← birthday_real_mul_wpow_sub_leftPrefix hs hsr hp ha] at hza
      have hzstage := mem_leftPrefixes_of_birthdayTruncation_eq_of_birthday_le ht hz hza
        ((mem_leftPrefixes_iff.mp hz).2.trans hgap)
      rwa [leftPrefixes_real_mul_wpow_sub_leftPrefix hs hsr hp ha] at hzstage
    · exact leftPrefixes_subset_of_birthdayTruncation_eq hpre
  have he : appendPluses (-((r : Surreal) * ω^ x)) (ω^ plusCount x).val =
      -((s : Surreal) * ω^ x) := by
    apply (appendPluses_eq_iff _ _ _).mpr
    constructor
    · rwa [birthday_neg, birthday_neg]
    · rw [rightPrefixes_neg, rightPrefixes_neg, hL]
  rw [appendMinuses_eq_neg, he, neg_neg]


end Surreal
