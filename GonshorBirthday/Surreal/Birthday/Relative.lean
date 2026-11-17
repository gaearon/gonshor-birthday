/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Addition
public import GonshorBirthday.Surreal.Birthday.Constant

/-!
# Relative birthdays of translated canonical prefixes
-/

universe u

public noncomputable section

namespace Surreal
open Set

/-- A translated left prefix has birthday given by the head birthday and its original plus count.
-/
theorem birthday_add_left_prefix_eq_of_stage_rightPrefixes {H x t : Surreal.{u}} (hx : 0 < x)
    (hR : ∀ z ∈ leftPrefixes x, rightPrefixes (H + z) = rightPrefixes H)
    (hP : ∀ y ∈ leftPrefixes x,
      birthdayTruncation t (H + y).birthday = H + y)
    (hB : ∀ y ∈ leftPrefixes x, H + y ≤ t)
    (hG : ∀ y ∈ leftPrefixes x, ∀ p ∈ leftPrefixes H, p + y ≤ H)
    {y : Surreal.{u}} (hy : y ∈ leftPrefixes x) :
    (H + y).birthday = NatOrdinal.of (H.birthday.val + (plusCount y).val) := by
  have hLz {z w : Surreal.{u}} (hz : z ∈ leftPrefixes x) (hw : w ∈ leftPrefixes z) :
      H + w ∈ leftPrefixes (H + z) := by
    have hwx := leftPrefixes_subset_of_birthdayTruncation_eq (mem_leftPrefixes_iff.mp hz).1 hw
    have hp := hP w hwx
    have hwb : (H + w).birthday ≤ t.birthday := by
      have ht := birthday_birthdayTruncation_le_birthday t (H + w).birthday
      rwa [hp] at ht
    have hwz : H + w < H + z := add_lt_add_right (mem_leftPrefixes_iff.mp hw).2 H
    have hzx : H + z ≤ t := hB z hz
    have ht := birthdayTruncation_eq_of_left_between hwb (by rw [hp]; exact hwz.le) hzx
    exact mem_leftPrefixes_iff.mpr ⟨ht.trans hp, hwz⟩
  have aux : ∀ o : NatOrdinal.{u}, ∀ z : Surreal.{u},
      z ∈ leftPrefixes x → z.birthday = o →
      (H + z).birthday = NatOrdinal.of (H.birthday.val + (plusCount z).val) := by
    intro o
    induction o using NatOrdinal.lt_wf.induction with
    | h o ih =>
      intro z hz hzo
      obtain rfl | hz0 := eq_or_ne z 0
      · simp only [add_zero, plusCount_zero, NatOrdinal.val_zero, NatOrdinal.of_val]
      have hzpos : 0 < z := lt_of_le_of_ne (nonneg_of_mem_leftPrefixes hx hz) hz0.symm
      have hcp : 0 < plusCount z := by
        simpa only [plusCount_zero] using
          plusCount_lt_of_mem_leftPrefixes (zero_mem_leftPrefixes hzpos)
      have hcp' : (0 : Ordinal.{u}) < (plusCount z).val := by
        simpa only [NatOrdinal.val_zero] using NatOrdinal.val.strictMono hcp
      apply le_antisymm
      · apply (birthday_le_iff_forall_prefixes _ _).mpr
        constructor
        · intro p hp
          rcases exists_leftPrefixes_add_ge hp with ⟨q, hq, hpq⟩ | ⟨w, hw, hpw⟩
          · have hpb := birthday_le_of_left_between hp (hpq.trans (hG z hz q hq))
              (le_add_of_nonneg_right hzpos.le)
            have ht := NatOrdinal.of.strictMono (add_lt_add_right hcp' H.birthday.val)
            have ht' : H.birthday < NatOrdinal.of (H.birthday.val + (plusCount z).val) := by
              simpa only [add_zero, NatOrdinal.of_val] using ht
            exact hpb.trans_lt ht'
          · have hwx := leftPrefixes_subset_of_birthdayTruncation_eq
              (mem_leftPrefixes_iff.mp hz).1 hw
            have hi := ih w.birthday ((birthday_lt_of_mem_leftPrefixes hw).trans_eq hzo)
              w hwx rfl
            have hpb := birthday_le_of_left_between hp hpw
              (add_le_add_right (mem_leftPrefixes_iff.mp hw).2.le H)
            apply hpb.trans_lt
            rw [hi]
            exact NatOrdinal.of.strictMono (add_lt_add_right
              (NatOrdinal.val.strictMono (plusCount_lt_of_mem_leftPrefixes hw)) _)
        · intro p hp
          rw [hR z hz] at hp
          apply (birthday_lt_of_mem_rightPrefixes hp).trans_le
          exact NatOrdinal.of.monotone le_self_add
      · apply NatOrdinal.val.le_iff_le.mp
        rw [NatOrdinal.val_of]
        apply (Ordinal.add_le_iff hcp'.ne').mpr
        intro d hd
        have hd' : NatOrdinal.of d < plusCount z := NatOrdinal.of.lt_iff_lt.mpr hd
        obtain ⟨w, hw, hwd⟩ := exists_leftPrefixes_plusCount_ge hd'
        have hwx := leftPrefixes_subset_of_birthdayTruncation_eq
          (mem_leftPrefixes_iff.mp hz).1 hw
        have hi := ih w.birthday ((birthday_lt_of_mem_leftPrefixes hw).trans_eq hzo) w hwx rfl
        have hlt := birthday_lt_of_mem_leftPrefixes (hLz hz hw)
        rw [hi] at hlt
        have hdw : d ≤ (plusCount w).val := by
          simpa only [NatOrdinal.val_of] using NatOrdinal.val.monotone hwd
        have ht := NatOrdinal.val.strictMono hlt
        exact (add_le_add_right hdw H.birthday.val).trans_lt (by
          simpa only [NatOrdinal.val_of] using ht)
  exact aux y.birthday y hy rfl

/-- A translated left prefix has birthday given by the head birthday and its original plus count.
-/
theorem birthday_add_left_prefix_eq_of_prefix_family {H x t : Surreal.{u}} (hx : 0 < x)
    (hR : rightPrefixes t = rightPrefixes H)
    (hP : ∀ y ∈ leftPrefixes x,
      birthdayTruncation t (H + y).birthday = H + y)
    (hB : ∀ y ∈ leftPrefixes x, H + y ≤ t)
    (hG : ∀ y ∈ leftPrefixes x, ∀ p ∈ leftPrefixes H, p + y ≤ H)
    {y : Surreal.{u}} (hy : y ∈ leftPrefixes x) :
    (H + y).birthday = NatOrdinal.of (H.birthday.val + (plusCount y).val) := by
  have h0 : birthdayTruncation t H.birthday = H := by
    simpa only [add_zero] using hP 0 (zero_mem_leftPrefixes hx)
  have hHb : H.birthday ≤ t.birthday := by
    have ht := birthday_birthdayTruncation_le_birthday t H.birthday
    rwa [h0] at ht
  have hH (z : Surreal.{u}) (hz : z ∈ leftPrefixes x) :
      birthdayTruncation (H + z) H.birthday = H := by
    have hHz : H ≤ H + z := le_add_of_nonneg_right (nonneg_of_mem_leftPrefixes hx hz)
    have hzx : H + z ≤ t := hB z hz
    have ht := birthdayTruncation_eq_of_left_between hHb (by rwa [h0]) hzx
    exact ht.trans h0
  have hRz (z : Surreal.{u}) (hz : z ∈ leftPrefixes x) :
      rightPrefixes (H + z) = rightPrefixes H := by
    apply Set.Subset.antisymm
    · have ht := rightPrefixes_subset_of_birthdayTruncation_eq (hP z hz)
      simpa only [hR] using ht
    · exact rightPrefixes_subset_of_birthdayTruncation_eq (hH z hz)
  exact birthday_add_left_prefix_eq_of_stage_rightPrefixes hx hRz hP hB hG hy

/-- A translated left prefix has birthday given by the head birthday and its original plus count.
-/
theorem birthday_add_left_prefix_eq {H x : Surreal.{u}} (hx : 0 < x)
    (hR : rightPrefixes (H + x) = rightPrefixes H)
    (hP : ∀ y ∈ leftPrefixes x,
      birthdayTruncation (H + x) (H + y).birthday = H + y)
    (hG : ∀ y ∈ leftPrefixes x, ∀ p ∈ leftPrefixes H, p + y ≤ H)
    {y : Surreal.{u}} (hy : y ∈ leftPrefixes x) :
    (H + y).birthday = NatOrdinal.of (H.birthday.val + (plusCount y).val) :=
  birthday_add_left_prefix_eq_of_prefix_family hx hR hP
    (fun _ hy ↦ add_le_add_right (mem_leftPrefixes_iff.mp hy).2.le H) hG hy

end Surreal
