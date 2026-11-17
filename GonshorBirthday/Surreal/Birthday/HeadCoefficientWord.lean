/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.CoefficientRun

import GonshorBirthday.Surreal.Birthday.CoefficientCofinality

/-!
# Real coefficient tails after arbitrary higher heads

For a positive real r, the initial headed monomial K+omega^s is followed by the
original coefficient tail, with each sign expanded to omega^(plusCount s) positions.
For negative r the initial headed monomial is K-omega^s. Exact total birthdays
include both finite coefficients and nondyadic real coefficients of birthday omega.
Every later coefficient successor has its exact original-sign block, regardless
of coefficient sign. The initial headed monomial remains opaque here: no exponent
minus-deletion rule or earlier-history sign formula is assumed.
-/

universe u
public noncomputable section
namespace Surreal
open Set

private theorem head_add_leftPrefix_mem_leftPrefixes
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {r t : ℝ} (htr : t < r)
    (hp : birthdayTruncation (r : Surreal.{u}) (t : Surreal).birthday = t)
    {a : Surreal.{u}} (ha : a ∈ leftPrefixes (ω^ s)) :
    K + ((t : Surreal) * ω^ s + a) ∈ leftPrefixes (K + (r : Surreal) * ω^ s) := by
  have hKn : (-K).support ⊆ Ioi s := by simpa only [support_neg] using hK
  have hpn : birthdayTruncation ((-r : ℝ) : Surreal.{u})
      (((-t : ℝ) : Surreal.{u})).birthday = ((-t : ℝ) : Surreal.{u}) := by
    simpa only [Real.toSurreal_neg, birthday_neg] using birthdayTruncation_neg_of_eq hp
  have hh := head_real_mul_wpow_sub_leftPrefix_mem_rightPrefixes (-K) s hKn
    (neg_lt_neg_iff.mpr htr) hpn ha
  have hZ : -K + ((-r : ℝ) : Surreal.{u}) * ω^ s = -(K + (r : Surreal) * ω^ s) := by
    rw [Real.toSurreal_neg]
    ring
  have hA : -K + (((-t : ℝ) : Surreal.{u}) * ω^ s - a) =
      -(K + ((t : Surreal) * ω^ s + a)) := by
    rw [Real.toSurreal_neg]
    ring
  rw [hZ, hA] at hh
  exact neg_mem_rightPrefixes_iff.mp hh

private theorem initial_head_monomial_prefix
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {r : ℝ} (hr : 0 < r) :
    birthdayTruncation (K + (r : Surreal) * ω^ s) (K + ω^ s).birthday = K + ω^ s := by
  have hp : birthdayTruncation (r : Surreal.{u}) (1 : Surreal).birthday = 1 := by
    simpa using birthdayTruncation_real_mul_wpow r hr (0 : Surreal.{u})
  have hp' : birthdayTruncation (r : Surreal.{u}) (((1 : ℝ) : Surreal).birthday) =
      ((1 : ℝ) : Surreal) := by simpa only [Real.toSurreal_one] using hp
  simpa using birthdayTruncation_head_real_mul_wpow_of_prefix K s hK hp'

private theorem lift_rightPrefix {A Z p q : Surreal.{u}}
    (hpre : birthdayTruncation Z A.birthday = A) (hp : p ∈ rightPrefixes Z)
    (hq : q ∈ rightPrefixes A) (hqp : q ≤ p) : p ∈ rightPrefixes A := by
  have hqZ := rightPrefixes_subset_of_birthdayTruncation_eq hpre hq
  have hpPre := (mem_rightPrefixes_iff.mp hp).1
  have htr := birthdayTruncation_eq_of_right_between (birthday_lt_of_mem_rightPrefixes hp).le
    (mem_rightPrefixes_iff.mp hqZ).2.le (by rwa [hpPre])
  rw [hpPre] at htr
  exact mem_rightPrefixes_iff.mpr
    ⟨birthdayTruncation_eq_trans (mem_rightPrefixes_iff.mp hq).1 htr,
      (mem_rightPrefixes_iff.mp hq).2.trans_le hqp⟩

/-- Bounds on all coefficient prefix stages bound the entire headed monomial birthday. -/
theorem birthday_head_real_mul_wpow_le_of_prefixes
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {r : ℝ} (hr : 0 < r)
    (M : NatOrdinal.{u}) (hA : (K + ω^ s).birthday ≤ M)
    (hcoeff : ∀ t : ℝ, 0 < t →
      ((t : Surreal.{u}) ∈ leftPrefixes (r : Surreal) ∨
        (t : Surreal.{u}) ∈ rightPrefixes (r : Surreal)) →
      ∀ a ∈ leftPrefixes (ω^ s), NatOrdinal.of
        ((K + (t : Surreal) * ω^ s).birthday.val + (plusCount a).val) < M) :
    (K + (r : Surreal) * ω^ s).birthday ≤ M := by
  let Z := K + (r : Surreal) * ω^ s
  let A := K + ω^ s
  have hpre : birthdayTruncation Z A.birthday = A := initial_head_monomial_prefix K s hK hr
  have hKpre : birthdayTruncation Z K.birthday = K := by
    simpa using birthdayTruncation_head_real_mul_wpow_of_prefix K s hK
      (r := r) (s := (0 : ℝ)) (by simp)
  have hKpos : K ∈ leftPrefixes Z := mem_leftPrefixes_iff.mpr ⟨hKpre,
    lt_add_of_pos_right K (mul_pos (Real.toSurreal_pos_iff.mpr hr) (wpow_pos s))⟩
  have hKA : K.birthday ≤ A.birthday := by
    have hh : birthdayTruncation A K.birthday = K := by
      simpa using birthdayTruncation_head_real_mul_wpow_of_prefix K s hK
        (r := (1 : ℝ)) (s := (0 : ℝ)) (by simp)
    have hb := birthday_birthdayTruncation_le_birthday A K.birthday
    rwa [hh] at hb
  apply (birthday_le_iff_forall_prefixes _ _).mpr
  constructor
  · intro p hp
    rcases exists_leftPrefixes_add_ge hp with ⟨q, hq, hpq⟩ | ⟨q, hq, hpq⟩
    · have hg := real_mul_wpow_lt_abs_sub_of_birthday_lt hK
        (birthday_lt_of_mem_leftPrefixes hq) r
      rw [abs_of_neg (sub_neg.mpr (mem_leftPrefixes_iff.mp hq).2), neg_sub] at hg
      have hpK : p < K := by linarith only [hg, hpq]
      have hpKpre := mem_leftPrefixes_of_birthdayTruncation_eq_of_birthday_le hKpre hp
        (birthday_le_of_left_between hp hpK.le (mem_leftPrefixes_iff.mp hKpos).2.le) hpK
      exact ((birthday_lt_of_mem_leftPrefixes hpKpre).trans_le hKA).trans_le hA
    · rcases exists_leftPrefixes_real_mul_wpow_ge hr hq with ⟨a, ha, hqa⟩ |
          ⟨t, ht, htr, a, ha, hta⟩
      · have hz := head_add_leftPrefix_mem_leftPrefixes K s hK hr (by simp) ha
        have hzA := head_add_leftPrefix_mem_leftPrefixes K s hK (show (0 : ℝ) < 1 by norm_num)
          (by simp) ha
        simp only [Real.toSurreal_zero, Real.toSurreal_one, zero_mul, one_mul, zero_add] at hz hzA
        have hbp := birthday_le_of_left_between hp
          ((add_le_add_right hqa K).trans' hpq) (mem_leftPrefixes_iff.mp hz).2.le
        exact (hbp.trans_lt (birthday_lt_of_mem_leftPrefixes hzA)).trans_le hA
      · have htr' := Real.toSurreal_lt_iff.mp (mem_leftPrefixes_iff.mp htr).2
        have hz := head_add_leftPrefix_mem_leftPrefixes K s hK htr'
          (mem_leftPrefixes_iff.mp htr).1 ha
        have hbp := birthday_le_of_left_between hp
          (hpq.trans (add_le_add_right hta K)) (mem_leftPrefixes_iff.mp hz).2.le
        have hRun := appendPluses_eq_add_leftPrefix_wpow
          (support_head_real_mul_wpow_subset K s hK t)
          (mem_support_head_real_mul_wpow K s hK (ne_of_gt ht)) ha
        rw [← add_assoc] at hz hbp
        rw [← hRun, birthday_appendPluses] at hbp
        exact hbp.trans_lt (hcoeff t ht (Or.inl htr) a ha)
  · intro p hp
    rcases exists_rightPrefixes_add_le hp with ⟨q, hq, hqp⟩ | ⟨q, hq, hqp⟩
    · have hqA : q ∈ rightPrefixes A := by
        have hh : birthdayTruncation A K.birthday = K := by
          simpa using birthdayTruncation_head_real_mul_wpow_of_prefix K s hK
            (r := (1 : ℝ)) (s := (0 : ℝ)) (by simp)
        exact rightPrefixes_subset_of_birthdayTruncation_eq hh hq
      have hqz : q ≤ p := (le_add_of_nonneg_right
        (mul_nonneg (Real.toSurreal_pos_iff.mpr hr).le (wpow_nonneg s))).trans hqp
      exact (birthday_lt_of_mem_rightPrefixes (lift_rightPrefix hpre hp hqA hqz)).trans_le hA
    · rcases exists_rightPrefixes_real_mul_wpow_le hr hq with ⟨b, hb, hbq⟩ |
          ⟨t, ht, htr, a, ha, hta⟩
      · obtain ⟨q0, hq0, hq0b⟩ := exists_rightPrefix_head_real_mul_wpow_le_add K s hK
          (t := (1 : ℝ)) (by norm_num) hb
        have hq0A : q0 ∈ rightPrefixes A := by simpa using hq0
        have hq0p : q0 ≤ p := hq0b.trans ((add_le_add_right hbq K).trans hqp)
        exact (birthday_lt_of_mem_rightPrefixes (lift_rightPrefix hpre hp hq0A hq0p)).trans_le hA
      · have hrt := Real.toSurreal_lt_iff.mp (mem_rightPrefixes_iff.mp htr).2
        have hz := head_real_mul_wpow_sub_leftPrefix_mem_rightPrefixes K s hK hrt
          (mem_rightPrefixes_iff.mp htr).1 ha
        have hbp := birthday_le_of_left_between (neg_mem_leftPrefixes_iff.mpr hp)
          (neg_le_neg ((add_le_add_right hta K).trans hqp))
          (neg_le_neg (mem_rightPrefixes_iff.mp hz).2.le)
        simp only [birthday_neg] at hbp
        have hRun := appendMinuses_eq_sub_leftPrefix_wpow
          (support_head_real_mul_wpow_subset K s hK t)
          (mem_support_head_real_mul_wpow K s hK (ne_of_gt ht)) ha
        rw [← add_sub_assoc] at hz hbp
        rw [← hRun, birthday_appendMinuses] at hbp
        exact hbp.trans_lt (hcoeff t ht (Or.inr htr) a ha)

/-- A positive finite coefficient contributes its exact finite number of headed blocks. -/
theorem birthday_head_real_mul_wpow_of_birthday_nat
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {r : ℝ} (hr : 0 < r) {n : ℕ}
    (hbr : (r : Surreal.{u}).birthday = ((n + 1 : ℕ) : NatOrdinal.{u})) :
    (K + (r : Surreal) * ω^ s).birthday =
      NatOrdinal.of ((K + ω^ s).birthday.val + (ω^ (plusCount s)).val * (n : Ordinal)) := by
  induction n generalizing r with
  | zero =>
    have hbr1 : (r : Surreal.{u}).birthday = 1 := by simpa using hbr
    rcases birthday_eq_one.mp hbr1 with hr1 | hrn1
    · have hr' : r = 1 := Real.toSurreal_inj.{u}.mp (by simpa using hr1)
      subst r
      simp
    · have hrS := Real.toSurreal_pos_iff.mpr hr
      rw [hrn1] at hrS
      norm_num at hrS
  | succ n ih =>
    have ha : ((n + 1 : ℕ) : NatOrdinal.{u}) < (r : Surreal.{u}).birthday := by
      rw [hbr]
      exact_mod_cast Nat.lt_succ_self (n + 1)
    have hlast : ((n + 1 : ℕ) : NatOrdinal.{u}) + 1 = (r : Surreal.{u}).birthday := by
      rw [hbr]
      simp only [Nat.cast_add, Nat.cast_one]
    obtain ⟨t, ht⟩ := birthdayTruncation_real_mem_range_real r ((n + 1 : ℕ) : NatOrdinal.{u})
    have hbt : (t : Surreal.{u}).birthday = ((n + 1 : ℕ) : NatOrdinal.{u}) := by
      rw [ht, birthday_birthdayTruncation _ ha.le]
    have htpos : 0 < t := by
      apply Real.toSurreal_pos_iff.mp
      rw [ht]
      apply lt_birthdayTruncation _ (Real.toSurreal_pos_iff.mpr hr)
      simp only [birthday_zero]
      exact_mod_cast Nat.zero_lt_succ n
    have hneq : (t : Surreal.{u}) ≠ (r : Surreal.{u}) := by
      intro he
      have hh := congrArg birthday he
      rw [hbt] at hh
      exact ha.ne hh
    have hblock : (K + (r : Surreal) * ω^ s).birthday =
        NatOrdinal.of ((K + (t : Surreal) * ω^ s).birthday.val + (ω^ (plusCount s)).val) := by
      rcases lt_or_gt_of_ne hneq with htr | hrt
      · have hsrc := birthdayTruncation_add_one_eq_appendPlus (r : Surreal.{u}) hlast.le
          (by simpa only [← ht] using htr)
        rw [hlast, birthdayTruncation_birthday, ← ht] at hsrc
        rw [← appendPluses_head_real_mul_wpow_of_appendPlus K s hK (ne_of_gt htpos) hsrc,
          birthday_appendPluses]
      · have hsrc := birthdayTruncation_add_one_eq_appendMinus (r : Surreal.{u}) hlast.le
          (by simpa only [← ht] using hrt)
        rw [hlast, birthdayTruncation_birthday, ← ht] at hsrc
        rw [← appendMinuses_head_real_mul_wpow_of_appendMinus K s hK (ne_of_gt htpos) hsrc,
          birthday_appendMinuses]
    rw [hblock, ih htpos hbt, NatOrdinal.val_of]
    simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one, add_assoc]

private theorem exists_positive_birthday_nat_tail {r : ℝ} (hr : 0 < r)
    (hf : (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) :
    ∃ n : ℕ, (r : Surreal.{u}).birthday = ((n + 1 : ℕ) : NatOrdinal.{u}) := by
  obtain ⟨n, hn⟩ := NatOrdinal.lt_omega0.mp hf
  cases n with
  | zero =>
    have hz : (r : Surreal.{u}) = 0 := birthday_eq_zero.mp (by simpa using hn)
    have hp := Real.toSurreal_pos_iff.mpr hr
    rw [hz] at hp
    exact (lt_irrefl _ hp).elim
  | succ n => exact ⟨n, hn⟩

/-- A positive nondyadic real contributes omega many complete headed coefficient blocks. -/
theorem birthday_head_real_mul_wpow_of_birthday_omega0
    (K x : Surreal.{u}) (hK : K.support ⊆ Ioi x) {r : ℝ} (hr : 0 < r)
    (hb : (r : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0) :
    (K + (r : Surreal) * ω^ x).birthday = NatOrdinal.of
      ((K + ω^ x).birthday.val + (ω^ plusCount x).val * Ordinal.omega0) := by
  have hQ : 0 < (ω^ plusCount x).val := by
    rw [NatOrdinal.val_wpow]
    exact Ordinal.opow_pos _ Ordinal.omega0_pos
  apply le_antisymm
  · apply birthday_head_real_mul_wpow_le_of_prefixes K x hK hr _
      (NatOrdinal.of.monotone le_self_add)
    intro s hs hsp a ha
    have hsb : (s : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 := by
      rw [← hb]
      rcases hsp with hsp | hsp
      · exact birthday_lt_of_mem_leftPrefixes hsp
      · exact birthday_lt_of_mem_rightPrefixes hsp
    obtain ⟨n, hbs⟩ := exists_positive_birthday_nat_tail hs hsb
    rw [birthday_head_real_mul_wpow_of_birthday_nat K x hK hs hbs, NatOrdinal.val_of]
    have hpa : (plusCount a).val < (ω^ plusCount x).val := by
      have ht := plusCount_lt_of_mem_leftPrefixes ha
      rw [plusCount_wpow] at ht
      exact NatOrdinal.val.strictMono ht
    have ht := add_lt_add_right hpa
      ((K + ω^ x).birthday.val + (ω^ plusCount x).val * (n : Ordinal))
    have he : (K + ω^ x).birthday.val + (ω^ plusCount x).val * (n : Ordinal) +
        (ω^ plusCount x).val = (K + ω^ x).birthday.val +
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
    have hscaled := birthdayTruncation_head_real_mul_wpow_of_prefix K x hK hp
    have hbound := birthday_birthdayTruncation_le_birthday
      (K + (r : Surreal) * ω^ x) (K + (s : Surreal) * ω^ x).birthday
    rw [hscaled, birthday_head_real_mul_wpow_of_birthday_nat K x hK hs hbs] at hbound
    have ht := NatOrdinal.val.monotone hbound
    exact (add_lt_add_right hdk _).trans_le (by simpa only [NatOrdinal.val_of] using ht)


/-- Every positive real coefficient has its exact birthday after an arbitrary higher head. -/
theorem birthday_head_real_mul_wpow
    (K x : Surreal.{u}) (hK : K.support ⊆ Ioi x) {r : ℝ} (hr : 0 < r) :
    (K + (r : Surreal) * ω^ x).birthday = NatOrdinal.of
      ((K + ω^ x).birthday.val + (ω^ plusCount x).val *
        ((r : Surreal.{u}).birthday.val - 1)) := by
  obtain hb | hb := (birthday_real_le_omega0 r).lt_or_eq
  · obtain ⟨n, hbn⟩ := exists_positive_birthday_nat_tail hr hb
    rw [birthday_head_real_mul_wpow_of_birthday_nat K x hK hr hbn, hbn, NatOrdinal.val_natCast]
    have he : (((n + 1 : ℕ) : Ordinal.{u}) - 1) = (n : Ordinal) := by
      simpa only [Nat.cast_one, Nat.add_sub_cancel] using
        (Ordinal.natCast_sub (n + 1) 1).symm
    rw [he]
  · rw [birthday_head_real_mul_wpow_of_birthday_omega0 K x hK hr hb, hb, NatOrdinal.val_of]
    have he : Ordinal.omega0 - 1 = Ordinal.omega0 := by
      calc
        _ = (1 + Ordinal.omega0) - 1 := by simp
        _ = _ := Ordinal.add_sub_cancel 1 _
    rw [he]



/-- Every negative real coefficient has its exact birthday after an arbitrary higher head. -/
theorem birthday_head_real_mul_wpow_of_neg
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {r : ℝ} (hr : r < 0) :
    (K + (r : Surreal) * ω^ s).birthday = NatOrdinal.of
      ((K - ω^ s).birthday.val + (ω^ plusCount s).val *
        ((r : Surreal.{u}).birthday.val - 1)) := by
  have hKn : (-K).support ⊆ Ioi s := by simpa only [support_neg] using hK
  have hh := birthday_head_real_mul_wpow (-K) s hKn (neg_pos.mpr hr)
  have hS : -K + ((-r : ℝ) : Surreal.{u}) * ω^ s = -(K + (r : Surreal) * ω^ s) := by
    rw [Real.toSurreal_neg]
    ring
  have hB : -K + ω^ s = -(K - ω^ s) := by ring
  rw [hS, hB, birthday_neg, birthday_neg, Real.toSurreal_neg, birthday_neg] at hh
  exact hh

private theorem real_prefix_data {r : ℝ} {a : NatOrdinal.{u}}
    (ha0 : 0 < a) (ha : a ≤ (r : Surreal.{u}).birthday) :
    ∃ t : ℝ, (t : Surreal.{u}) = birthdayTruncation (r : Surreal.{u}) a ∧
      (t : Surreal.{u}).birthday = a ∧ t ≠ 0 := by
  obtain ⟨t, ht⟩ := birthdayTruncation_real_mem_range_real r a
  have hbt : (t : Surreal.{u}).birthday = a := by rw [ht, birthday_birthdayTruncation _ ha]
  refine ⟨t, ht, hbt, ?_⟩
  intro he
  have ha' : a = 0 := by simpa only [he, Real.toSurreal_zero, birthday_zero] using hbt.symm
  exact ha0.ne' ha'

/-- Every later original real coefficient plus becomes its exact headed pure-power plus block. -/
theorem head_real_mul_wpow_birthdayTruncation_add_one_plus
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) (r : ℝ) {a : NatOrdinal.{u}}
    (ha0 : 0 < a) (ha : a + 1 ≤ (r : Surreal.{u}).birthday)
    (hl : birthdayTruncation (r : Surreal.{u}) a < (r : Surreal.{u})) :
    K + birthdayTruncation (r : Surreal.{u}) (a + 1) * ω^ s =
      appendPluses (K + birthdayTruncation (r : Surreal.{u}) a * ω^ s)
        (ω^ (plusCount s)).val := by
  have hab : a ≤ (r : Surreal.{u}).birthday := (le_add_of_nonneg_right (by simp)).trans ha
  obtain ⟨t, ht, _, ht0⟩ := real_prefix_data ha0 hab
  obtain ⟨q, hq, _, _⟩ := real_prefix_data (ha0.trans_le (le_add_of_nonneg_right (by simp))) ha
  have hsrc : (q : Surreal.{u}) = appendPlus (t : Surreal.{u}) := by
    rw [hq, ht]
    exact birthdayTruncation_add_one_eq_appendPlus (r : Surreal.{u}) ha hl
  have hh := appendPluses_head_real_mul_wpow_of_appendPlus K s hK ht0 hsrc
  rw [ht, hq] at hh
  exact hh.symm

/-- Every later original real coefficient minus becomes its exact headed pure-power minus block. -/
theorem head_real_mul_wpow_birthdayTruncation_add_one_minus
    (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) (r : ℝ) {a : NatOrdinal.{u}}
    (ha0 : 0 < a) (ha : a + 1 ≤ (r : Surreal.{u}).birthday)
    (hl : (r : Surreal.{u}) < birthdayTruncation (r : Surreal.{u}) a) :
    K + birthdayTruncation (r : Surreal.{u}) (a + 1) * ω^ s =
      appendMinuses (K + birthdayTruncation (r : Surreal.{u}) a * ω^ s)
        (ω^ (plusCount s)).val := by
  have hab : a ≤ (r : Surreal.{u}).birthday := (le_add_of_nonneg_right (by simp)).trans ha
  obtain ⟨t, ht, _, ht0⟩ := real_prefix_data ha0 hab
  obtain ⟨q, hq, _, _⟩ := real_prefix_data (ha0.trans_le (le_add_of_nonneg_right (by simp))) ha
  have hsrc : (q : Surreal.{u}) = appendMinus (t : Surreal.{u}) := by
    rw [hq, ht]
    exact birthdayTruncation_add_one_eq_appendMinus (r : Surreal.{u}) ha hl
  have hh := appendMinuses_head_real_mul_wpow_of_appendMinus K s hK ht0 hsrc
  rw [ht, hq] at hh
  exact hh.symm

end Surreal
