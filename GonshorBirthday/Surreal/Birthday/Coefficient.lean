/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Omega
public import GonshorBirthday.Surreal.Birthday.Relative
public import GonshorBirthday.Surreal.HahnSeries.BirthdayGap

/-!
# Natural coefficient blocks of monomials
-/

universe u

public noncomputable section

namespace Surreal
open Set

/-- A prefix of a smaller monomial fits strictly within every left-prefix gap of a head. -/
theorem add_lt_of_mem_leftPrefixes_wpow_of_support {H x y p : Surreal.{u}}
    (hH : H.support ⊆ Ici x) (hy : y ∈ leftPrefixes (ω^ x)) (hp : p ∈ leftPrefixes H) :
    p + y < H := by
  rcases exists_natCast_mul_wpow_ge_of_mem_leftPrefixes hy with hy0 | ⟨v, hv, n, hyn⟩
  · rw [hy0, add_zero]
    exact (mem_leftPrefixes_iff.mp hp).2
  · have ht := natCast_mul_wpow_lt_abs_sub_of_birthday_lt hH
      (birthday_lt_of_mem_leftPrefixes hp) (mem_leftPrefixes_iff.mp hv).2 n
    have hlt : (n : Surreal) * ω^ v < H - p := by
      simpa only [abs_of_neg (sub_neg.mpr (mem_leftPrefixes_iff.mp hp).2), neg_sub] using ht
    have hsum : p + (n : Surreal) * ω^ v < H := by
      simpa only [add_comm] using (lt_sub_iff_add_lt.mp hlt)
    exact (add_le_add_right hyn p).trans_lt hsum

/-- Every translated monomial left prefix is a canonical left prefix in the next coefficient. -/
theorem natCast_mul_wpow_add_mem_leftPrefixes (x : Surreal.{u}) (n : ℕ)
    {y : Surreal.{u}} (hy : y ∈ leftPrefixes (ω^ x)) :
    ((n + 1 : ℕ) : Surreal) * ω^ x + y ∈
      leftPrefixes (((n + 1 : ℕ) : Surreal) * ω^ x + ω^ x) := by
  have hsum : ((n + 1 : ℕ) : Surreal) * ω^ x + ω^ x =
      ((n + 2 : ℕ) : Surreal) * ω^ x := by
    change _ = (((n + 1) + 1 : ℕ) : Surreal) * ω^ x
    rw [Nat.cast_add (n + 1) 1, Nat.cast_one, add_mul, one_mul]
  have hR : ∀ z ∈ rightPrefixes (((n + 1 : ℕ) : Surreal) * ω^ x),
      ((n + 1 : ℕ) : Surreal) * ω^ x + ω^ x < z := by
    intro z hz
    rw [rightPrefixes_natCast_mul_wpow] at hz
    rw [hsum]
    exact natCast_mul_wpow_lt_of_mem_rightPrefixes hz (n + 2)
  apply mem_leftPrefixes_iff.mpr
  exact ⟨birthdayTruncation_add_left_eq (mem_leftPrefixes_iff.mp hy).1
    (nonneg_of_mem_leftPrefixes (wpow_pos x) hy) (mem_leftPrefixes_iff.mp hy).2.le hR,
    add_lt_add_right (mem_leftPrefixes_iff.mp hy).2 _⟩

/-- Translating a monomial left prefix past a natural multiple gives its exact plus-count cost. -/
theorem birthday_natCast_mul_wpow_add_leftPrefix (x : Surreal.{u}) (n : ℕ)
    {y : Surreal.{u}} (hy : y ∈ leftPrefixes (ω^ x)) :
    (((n + 1 : ℕ) : Surreal) * ω^ x + y).birthday =
      NatOrdinal.of ((((n + 1 : ℕ) : Surreal) * ω^ x).birthday.val + (plusCount y).val) := by
  have hsum : ((n + 1 : ℕ) : Surreal) * ω^ x + ω^ x =
      ((n + 2 : ℕ) : Surreal) * ω^ x := by
    change _ = (((n + 1) + 1 : ℕ) : Surreal) * ω^ x
    rw [Nat.cast_add (n + 1) 1, Nat.cast_one, add_mul, one_mul]
  have hR : ∀ z ∈ rightPrefixes (((n + 1 : ℕ) : Surreal) * ω^ x),
      ((n + 1 : ℕ) : Surreal) * ω^ x + ω^ x < z := by
    intro z hz
    rw [rightPrefixes_natCast_mul_wpow] at hz
    rw [hsum]
    exact natCast_mul_wpow_lt_of_mem_rightPrefixes hz (n + 2)
  have hP : ∀ z ∈ leftPrefixes (ω^ x),
      birthdayTruncation (((n + 1 : ℕ) : Surreal) * ω^ x + ω^ x)
        (((n + 1 : ℕ) : Surreal) * ω^ x + z).birthday =
          ((n + 1 : ℕ) : Surreal) * ω^ x + z := by
    intro z hz
    exact birthdayTruncation_add_left_eq (mem_leftPrefixes_iff.mp hz).1
      (nonneg_of_mem_leftPrefixes (wpow_pos x) hz) (mem_leftPrefixes_iff.mp hz).2.le hR
  have hSupport : (((n + 1 : ℕ) : Surreal) * ω^ x).support ⊆ Ici x := by
    have he : ((n + 1 : ℕ) : Surreal) * ω^ x =
        (SurrealHahnSeries.single x ((n + 1 : ℕ) : ℝ)).toSurreal := by
      rw [SurrealHahnSeries.toSurreal_single, Real.toSurreal_natCast]
    rw [he, SurrealHahnSeries.support_toSurreal]
    intro z hz
    have hz' : z = x := mem_singleton_iff.mp (SurrealHahnSeries.support_single_subset hz)
    rw [hz']
    change x ≤ x
    exact le_rfl
  apply birthday_add_left_prefix_eq (wpow_pos x) _ hP _ hy
  · rw [hsum, rightPrefixes_natCast_mul_wpow, rightPrefixes_natCast_mul_wpow]
  · intro z hz p hp
    exact (add_lt_of_mem_leftPrefixes_wpow_of_support hSupport hz hp).le

/-- Increasing a natural monomial coefficient adds exactly its monomial plus count to birthday. -/
theorem birthday_natCast_mul_wpow_add_wpow (x : Surreal.{u}) (n : ℕ) :
    (((n + 1 : ℕ) : Surreal) * ω^ x + ω^ x).birthday =
      NatOrdinal.of
        ((((n + 1 : ℕ) : Surreal) * ω^ x).birthday.val + (plusCount (ω^ x)).val) := by
  have hsum : ((n + 1 : ℕ) : Surreal) * ω^ x + ω^ x =
      ((n + 2 : ℕ) : Surreal) * ω^ x := by
    change _ = (((n + 1) + 1 : ℕ) : Surreal) * ω^ x
    rw [Nat.cast_add (n + 1) 1, Nat.cast_one, add_mul, one_mul]
  have hR : rightPrefixes (((n + 1 : ℕ) : Surreal) * ω^ x + ω^ x) =
      rightPrefixes (((n + 1 : ℕ) : Surreal) * ω^ x) := by
    rw [hsum, rightPrefixes_natCast_mul_wpow, rightPrefixes_natCast_mul_wpow]
  have hcp : 0 < plusCount (ω^ x) := by
    simpa only [plusCount_zero] using
      plusCount_lt_of_mem_leftPrefixes (zero_mem_leftPrefixes (wpow_pos x))
  have hcp' : (0 : Ordinal.{u}) < (plusCount (ω^ x)).val := by
    simpa only [NatOrdinal.val_zero] using NatOrdinal.val.strictMono hcp
  apply le_antisymm
  · apply (birthday_le_iff_forall_prefixes _ _).mpr
    constructor
    · intro p hp
      have hp' := hp
      rw [hsum] at hp'
      obtain ⟨a, ha, hpa⟩ := exists_leftPrefixes_natCast_mul_ge (ω^ x) (n + 1) hp'
      have hab : ((n + 1 : ℕ) : Surreal) * ω^ x + a <
          ((n + 1 : ℕ) : Surreal) * ω^ x + ω^ x :=
        add_lt_add_right (mem_leftPrefixes_iff.mp ha).2 _
      apply (birthday_le_of_left_between hp hpa hab.le).trans_lt
      rw [birthday_natCast_mul_wpow_add_leftPrefix x n ha]
      exact NatOrdinal.of.strictMono (add_lt_add_right
        (NatOrdinal.val.strictMono (plusCount_lt_of_mem_leftPrefixes ha)) _)
    · intro p hp
      rw [hR] at hp
      apply (birthday_lt_of_mem_rightPrefixes hp).trans_le
      exact NatOrdinal.of.monotone le_self_add
  · apply NatOrdinal.val.le_iff_le.mp
    rw [NatOrdinal.val_of]
    apply (Ordinal.add_le_iff hcp'.ne').mpr
    intro d hd
    have hd' : NatOrdinal.of d < plusCount (ω^ x) := NatOrdinal.of.lt_iff_lt.mpr hd
    obtain ⟨a, ha, hda⟩ := exists_leftPrefixes_plusCount_ge hd'
    have hlt := birthday_lt_of_mem_leftPrefixes (natCast_mul_wpow_add_mem_leftPrefixes x n ha)
    rw [birthday_natCast_mul_wpow_add_leftPrefix x n ha] at hlt
    have hda' : d ≤ (plusCount a).val := by
      simpa only [NatOrdinal.val_of] using NatOrdinal.val.monotone hda
    have ht := NatOrdinal.val.strictMono hlt
    exact (add_le_add_right hda' _).trans_lt (by simpa only [NatOrdinal.val_of] using ht)

/-- A natural coefficient has exact birthday increment measured by monomial plus count. -/
theorem birthday_natCast_mul_wpow_eq_plusCount (x : Surreal.{u}) (n : ℕ) :
    (((n + 1 : ℕ) : Surreal) * ω^ x).birthday =
      NatOrdinal.of ((ω^ x).birthday.val + (plusCount (ω^ x)).val * (n : Ordinal)) := by
  induction n with
  | zero =>
    simp only [zero_add, Nat.cast_one, one_mul, Nat.cast_zero, mul_zero, add_zero,
      NatOrdinal.of_val]
  | succ n ih =>
    have he : ((n + 1 : ℕ) : Surreal) * ω^ x + ω^ x =
        ((n + 2 : ℕ) : Surreal) * ω^ x := by
      change _ = (((n + 1) + 1 : ℕ) : Surreal) * ω^ x
      rw [Nat.cast_add (n + 1) 1, Nat.cast_one, add_mul, one_mul]
    change (((n + 2 : ℕ) : Surreal) * ω^ x).birthday =
      NatOrdinal.of ((ω^ x).birthday.val + (plusCount (ω^ x)).val * ((n + 1 : ℕ) : Ordinal))
    rw [← he, birthday_natCast_mul_wpow_add_wpow, ih, NatOrdinal.val_of,
      Nat.cast_add, Nat.cast_one, mul_add_one, add_assoc]

/-- A natural coefficient appends plus blocks of length equal to the monomial plus count. -/
theorem natCast_mul_wpow_eq_appendPluses_plusCount (x : Surreal.{u}) (n : ℕ) :
    ((n + 1 : ℕ) : Surreal) * ω^ x =
      appendPluses (ω^ x) ((plusCount (ω^ x)).val * (n : Ordinal)) := by
  apply Eq.symm
  apply (appendPluses_eq_iff _ _ _).mpr
  exact ⟨birthday_natCast_mul_wpow_eq_plusCount x n, rightPrefixes_natCast_mul_wpow x n⟩

/-- Multiplication of a monomial by a natural number multiplies its plus count ordinarily. -/
theorem plusCount_natCast_mul_wpow (x : Surreal.{u}) (n : ℕ) :
    plusCount ((n : Surreal) * ω^ x) =
      NatOrdinal.of ((plusCount (ω^ x)).val * (n : Ordinal)) := by
  cases n with
  | zero => simp only [Nat.cast_zero, zero_mul, plusCount_zero, mul_zero, NatOrdinal.of_zero]
  | succ n =>
    rw [natCast_mul_wpow_eq_appendPluses_plusCount,
      plusCount_appendPluses, Nat.cast_add, Nat.cast_one, Nat.cast_add_one_comm, mul_add, mul_one]

/-- The omega-map transforms the canonical plus count by ordinary ordinal omega exponentiation. -/
theorem plusCount_wpow (x : Surreal.{u}) : plusCount (ω^ x) = ω^ plusCount x := by
  have aux : ∀ b : NatOrdinal.{u}, ∀ x : Surreal.{u}, x.birthday = b →
      plusCount (ω^ x) = ω^ plusCount x := by
    intro b
    induction b using NatOrdinal.lt_wf.induction with
    | h b ih =>
      intro x hxb
      have hI (v : Surreal.{u}) (hv : v ∈ leftPrefixes x) :
          plusCount (ω^ v) = ω^ plusCount v :=
        ih v.birthday ((birthday_lt_of_mem_leftPrefixes hv).trans_eq hxb) v rfl
      apply le_antisymm
      · apply (plusCount_le_iff_forall_birthdayTruncation _ _).mpr
        intro a ha hl
        have hz : birthdayTruncation (ω^ x) a ∈ leftPrefixes (ω^ x) :=
          mem_leftPrefixes.mpr ⟨a, ha, rfl, hl⟩
        rcases exists_natCast_mul_wpow_ge_of_mem_leftPrefixes hz with hz0 | ⟨v, hv, n, hzn⟩
        · rw [hz0, plusCount_zero]
          exact NatOrdinal.wpow_pos _
        · have hn : (n : Surreal) * ω^ v < ω^ x := by
            have ht := mul_wpow_lt_wpow (n : ℝ) (mem_leftPrefixes_iff.mp hv).2
            simpa only [Real.toSurreal_natCast] using ht
          have hc := plusCount_le_of_left_between ha.le hzn hn.le
          rw [plusCount_natCast_mul_wpow, hI v hv, NatOrdinal.val_wpow,
            NatOrdinal.of_omega0_opow_mul_natCast, NatOrdinal.of_val] at hc
          exact hc.trans_lt (NatOrdinal.wpow_mul_natCast_lt
            (plusCount_lt_of_mem_leftPrefixes hv) n)
      · obtain hx0 | hx0 := eq_or_ne (plusCount x) 0
        · rw [hx0, NatOrdinal.wpow_zero]
          have ht : 0 < plusCount (ω^ x) := by
            simpa only [plusCount_zero] using
              plusCount_lt_of_mem_leftPrefixes (zero_mem_leftPrefixes (wpow_pos x))
          exact NatOrdinal.one_le_iff_ne_zero.mpr ht.ne'
        · apply (NatOrdinal.wpow_le_iff hx0).mpr
          intro c hc n
          obtain ⟨v, hv, hcv⟩ := exists_leftPrefixes_plusCount_ge hc
          obtain ⟨a, ha, he, hvx⟩ := mem_leftPrefixes.mp hv
          have hp := birthdayTruncation_natCast_mul_wpow_birthdayTruncation x a
            (by rwa [he]) n
          rw [he] at hp
          have hb : ((n : Surreal) * ω^ v).birthday ≤ (ω^ x).birthday := by
            have ht := birthday_birthdayTruncation_le_birthday (ω^ x)
              ((n : Surreal) * ω^ v).birthday
            rwa [hp] at ht
          have hq := plusCount_birthdayTruncation_le (ω^ x) hb
          rw [hp, plusCount_natCast_mul_wpow, hI v hv, NatOrdinal.val_wpow,
            NatOrdinal.of_omega0_opow_mul_natCast, NatOrdinal.of_val] at hq
          exact (mul_le_mul_of_nonneg_right (NatOrdinal.wpow_le_wpow.mpr hcv) zero_le).trans hq
  exact aux x.birthday x rfl

/-- The exact birthday of every positive natural coefficient monomial. -/
theorem birthday_natCast_mul_wpow (x : Surreal.{u}) (n : ℕ) :
    (((n + 1 : ℕ) : Surreal) * ω^ x).birthday =
      NatOrdinal.of ((ω^ x).birthday.val + (ω^ plusCount x).val * (n : Ordinal)) := by
  rw [birthday_natCast_mul_wpow_eq_plusCount, plusCount_wpow]

/-- A positive natural coefficient appends its exact pure-power block of plus signs. -/
theorem natCast_mul_wpow_eq_appendPluses (x : Surreal.{u}) (n : ℕ) :
    ((n + 1 : ℕ) : Surreal) * ω^ x =
      appendPluses (ω^ x) ((ω^ plusCount x).val * (n : Ordinal)) := by
  rw [natCast_mul_wpow_eq_appendPluses_plusCount, plusCount_wpow]

end Surreal
