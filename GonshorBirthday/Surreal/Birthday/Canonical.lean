/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Prefix

/-!
# Canonical prefix cuts of surreal numbers
-/

universe u

public noncomputable section

namespace Surreal
open Set

/-- The canonical left prefixes of a surreal number. -/
def leftPrefixes (x : Surreal.{u}) : Set Surreal.{u} :=
  {z | ∃ a < x.birthday, birthdayTruncation x a = z ∧ z < x}

/-- The canonical right prefixes of a surreal number. -/
def rightPrefixes (x : Surreal.{u}) : Set Surreal.{u} :=
  {z | ∃ a < x.birthday, birthdayTruncation x a = z ∧ x < z}

/-- Membership in the canonical left-prefix set. -/
theorem mem_leftPrefixes {x z : Surreal.{u}} : z ∈ leftPrefixes x ↔
    ∃ a < x.birthday, birthdayTruncation x a = z ∧ z < x := by
  unfold leftPrefixes
  rfl

/-- Membership in the canonical right-prefix set. -/
theorem mem_rightPrefixes {x z : Surreal.{u}} : z ∈ rightPrefixes x ↔
    ∃ a < x.birthday, birthdayTruncation x a = z ∧ x < z := by
  unfold rightPrefixes
  rfl

/-- Every canonical left prefix is younger than its source. -/
theorem birthday_lt_of_mem_leftPrefixes {x z : Surreal.{u}} (hz : z ∈ leftPrefixes x) :
    z.birthday < x.birthday := by
  obtain ⟨a, ha, rfl, _⟩ := mem_leftPrefixes.mp hz
  exact (birthday_birthdayTruncation_le x a).trans_lt ha

/-- Every canonical right prefix is younger than its source. -/
theorem birthday_lt_of_mem_rightPrefixes {x z : Surreal.{u}} (hz : z ∈ rightPrefixes x) :
    z.birthday < x.birthday := by
  obtain ⟨a, ha, rfl, _⟩ := mem_rightPrefixes.mp hz
  exact (birthday_birthdayTruncation_le x a).trans_lt ha

instance (x : Surreal.{u}) : Small.{u} (leftPrefixes x) :=
  small_subset (s := {z : Surreal | z.birthday < x.birthday})
    (fun _ hz ↦ birthday_lt_of_mem_leftPrefixes hz)

instance (x : Surreal.{u}) : Small.{u} (rightPrefixes x) :=
  small_subset (s := {z : Surreal | z.birthday < x.birthday})
    (fun _ hz ↦ birthday_lt_of_mem_rightPrefixes hz)

/-- Every canonical left prefix is less than every canonical right prefix. -/
theorem leftPrefixes_lt_rightPrefixes (x : Surreal.{u}) :
    ∀ y ∈ leftPrefixes x, ∀ z ∈ rightPrefixes x, y < z := by
  intro y hy z hz
  exact (mem_leftPrefixes.mp hy).choose_spec.2.2.trans
    (mem_rightPrefixes.mp hz).choose_spec.2.2

/-- A surreal number is the simplest number between its canonical prefixes. -/
theorem ofSets_leftPrefixes_rightPrefixes (x : Surreal.{u}) :
    !{leftPrefixes x | rightPrefixes x}'(leftPrefixes_lt_rightPrefixes x) = x := by
  apply ofSets_eq_of_forall_birthday_le
  · intro z hz
    exact (mem_leftPrefixes.mp hz).choose_spec.2.2
  · intro z hz
    exact (mem_rightPrefixes.mp hz).choose_spec.2.2
  · intro y hL hR
    by_contra h
    have hy : y.birthday < x.birthday := lt_of_not_ge h
    rcases lt_trichotomy y x with hyx | hyx | hyx
    · obtain ⟨a, ha, hya, hax⟩ := exists_birthdayTruncation_left_ge hy hyx
      exact (hL _ (mem_leftPrefixes.mpr ⟨a, ha, rfl, hax⟩)).not_ge hya
    · exact hy.ne (congrArg birthday hyx)
    · obtain ⟨a, ha, hxa, hay⟩ := exists_birthdayTruncation_right_le hy hyx
      exact (hR _ (mem_rightPrefixes.mpr ⟨a, ha, rfl, hxa⟩)).not_ge hay

/-- A birthday bound is equivalent to strict bounds for both canonical option sets. -/
theorem birthday_le_iff_forall_prefixes (x : Surreal.{u}) (o : NatOrdinal.{u}) :
    x.birthday ≤ o ↔ (∀ z ∈ leftPrefixes x, z.birthday < o) ∧
      (∀ z ∈ rightPrefixes x, z.birthday < o) := by
  constructor
  · intro h
    exact ⟨fun _ hz ↦ (birthday_lt_of_mem_leftPrefixes hz).trans_le h,
      fun _ hz ↦ (birthday_lt_of_mem_rightPrefixes hz).trans_le h⟩
  · rintro ⟨hL, hR⟩
    have ht := birthday_ofSets_le (s := leftPrefixes x) (t := rightPrefixes x)
      (H := leftPrefixes_lt_rightPrefixes x)
    rw [ofSets_leftPrefixes_rightPrefixes] at ht
    apply ht.trans
    apply max_le
    · apply csSup_le'
      rintro _ ⟨z, hz, rfl⟩
      exact Order.add_one_le_iff.mpr (hL z hz)
    · apply csSup_le'
      rintro _ ⟨z, hz, rfl⟩
      exact Order.add_one_le_iff.mpr (hR z hz)

/-- A left prefix is precisely an intrinsic birthday truncation lying below its source. -/
theorem mem_leftPrefixes_iff {x z : Surreal.{u}} :
    z ∈ leftPrefixes x ↔ birthdayTruncation x z.birthday = z ∧ z < x := by
  constructor
  · intro hz
    obtain ⟨a, ha, he, hl⟩ := mem_leftPrefixes.mp hz
    have hb : z.birthday = a := by
      rw [← he, birthday_birthdayTruncation x ha.le]
    exact ⟨hb.symm ▸ he, hl⟩
  · rintro ⟨he, hl⟩
    have hb : z.birthday ≤ x.birthday := by
      have ht := birthday_birthdayTruncation_le_birthday x z.birthday
      rwa [he] at ht
    have hb' : z.birthday < x.birthday := by
      apply hb.lt_of_ne
      intro h
      rw [h, birthdayTruncation_birthday] at he
      exact hl.ne he.symm
    exact mem_leftPrefixes.mpr ⟨z.birthday, hb', he, hl⟩

/-- Zero is a canonical left prefix of every positive surreal. -/
theorem zero_mem_leftPrefixes {x : Surreal.{u}} (hx : 0 < x) : 0 ∈ leftPrefixes x := by
  exact mem_leftPrefixes_iff.mpr ⟨by simp, hx⟩

/-- A canonical left prefix of a positive surreal is nonnegative. -/
theorem nonneg_of_mem_leftPrefixes {x z : Surreal.{u}} (hx : 0 < x)
    (hz : z ∈ leftPrefixes x) : 0 ≤ z := by
  obtain hb | hb := eq_or_ne z.birthday 0
  · rw [birthday_eq_zero.mp hb]
  · have hb' : (0 : Surreal.{u}).birthday < z.birthday := by
      simpa only [birthday_zero] using
        (zero_lt_one.trans_le (NatOrdinal.one_le_iff_ne_zero.mpr hb))
    have ht := lt_birthdayTruncation hb' hx
    rw [(mem_leftPrefixes_iff.mp hz).1] at ht
    exact ht.le

/-- A right prefix is precisely an intrinsic birthday truncation lying above its source. -/
theorem mem_rightPrefixes_iff {x z : Surreal.{u}} :
    z ∈ rightPrefixes x ↔ birthdayTruncation x z.birthday = z ∧ x < z := by
  constructor
  · intro hz
    obtain ⟨a, ha, he, hl⟩ := mem_rightPrefixes.mp hz
    have hb : z.birthday = a := by
      rw [← he, birthday_birthdayTruncation x ha.le]
    exact ⟨hb.symm ▸ he, hl⟩
  · rintro ⟨he, hl⟩
    have hb : z.birthday ≤ x.birthday := by
      have ht := birthday_birthdayTruncation_le_birthday x z.birthday
      rwa [he] at ht
    have hb' : z.birthday < x.birthday := by
      apply hb.lt_of_ne
      intro h
      rw [h, birthdayTruncation_birthday] at he
      exact hl.ne he
    exact mem_rightPrefixes.mpr ⟨z.birthday, hb', he, hl⟩

/-- Intrinsic canonical prefix equations compose. -/
theorem birthdayTruncation_eq_trans {x y z : Surreal.{u}}
    (hxy : birthdayTruncation x y.birthday = y)
    (hyz : birthdayTruncation y z.birthday = z) : birthdayTruncation x z.birthday = z := by
  have hy : y.birthday ≤ x.birthday := by
    have ht := birthday_birthdayTruncation_le_birthday x y.birthday
    rwa [hxy] at ht
  have hz : z.birthday ≤ y.birthday := by
    have ht := birthday_birthdayTruncation_le_birthday y z.birthday
    rwa [hyz] at ht
  have ht := birthdayTruncation_birthdayTruncation x hz hy
  rw [hxy, hyz] at ht
  exact ht.symm

/-- Every canonical left prefix of a canonical prefix remains a left prefix of the source. -/
theorem leftPrefixes_subset_of_birthdayTruncation_eq {x y : Surreal.{u}}
    (h : birthdayTruncation x y.birthday = y) : leftPrefixes y ⊆ leftPrefixes x := by
  have hb : y.birthday ≤ x.birthday := by
    have ht := birthday_birthdayTruncation_le_birthday x y.birthday
    rwa [h] at ht
  intro z hz
  apply mem_leftPrefixes_iff.mpr
  refine ⟨birthdayTruncation_eq_trans h (mem_leftPrefixes_iff.mp hz).1, ?_⟩
  apply (lt_birthdayTruncation_iff hb (birthday_lt_of_mem_leftPrefixes hz)).mp
  rw [h]
  exact (mem_leftPrefixes_iff.mp hz).2

/-- Every canonical right prefix of a canonical prefix remains a right prefix of the source. -/
theorem rightPrefixes_subset_of_birthdayTruncation_eq {x y : Surreal.{u}}
    (h : birthdayTruncation x y.birthday = y) : rightPrefixes y ⊆ rightPrefixes x := by
  have hb : y.birthday ≤ x.birthday := by
    have ht := birthday_birthdayTruncation_le_birthday x y.birthday
    rwa [h] at ht
  intro z hz
  apply mem_rightPrefixes_iff.mpr
  refine ⟨birthdayTruncation_eq_trans h (mem_rightPrefixes_iff.mp hz).1, ?_⟩
  apply (birthdayTruncation_lt_iff hb (birthday_lt_of_mem_rightPrefixes hz)).mp
  rw [h]
  exact (mem_rightPrefixes_iff.mp hz).2

/-- An older source left prefix remains a left prefix of a later prefix lying to its right. -/
theorem mem_leftPrefixes_of_birthdayTruncation_eq_of_birthday_le {x y z : Surreal.{u}}
    (hp : birthdayTruncation x y.birthday = y) (hz : z ∈ leftPrefixes x)
    (hb : z.birthday ≤ y.birthday) (hzy : z < y) : z ∈ leftPrefixes y := by
  have hyb : y.birthday ≤ x.birthday := by
    have ht := birthday_birthdayTruncation_le_birthday x y.birthday
    rwa [hp] at ht
  have ht := birthdayTruncation_birthdayTruncation x hb hyb
  rw [hp, (mem_leftPrefixes_iff.mp hz).1] at ht
  exact mem_leftPrefixes_iff.mpr ⟨ht, hzy⟩

/-- An older source right prefix remains a right prefix of a later prefix lying to its left. -/
theorem mem_rightPrefixes_of_birthdayTruncation_eq_of_birthday_le {x y z : Surreal.{u}}
    (hp : birthdayTruncation x y.birthday = y) (hz : z ∈ rightPrefixes x)
    (hb : z.birthday ≤ y.birthday) (hyz : y < z) : z ∈ rightPrefixes y := by
  have hyb : y.birthday ≤ x.birthday := by
    have ht := birthday_birthdayTruncation_le_birthday x y.birthday
    rwa [hp] at ht
  have ht := birthdayTruncation_birthdayTruncation x hb hyb
  rw [hp, (mem_rightPrefixes_iff.mp hz).1] at ht
  exact mem_rightPrefixes_iff.mpr ⟨ht, hyz⟩

/-- A number between a left prefix and its source is at least as old as that prefix. -/
theorem birthday_le_of_left_between {x z w : Surreal.{u}}
    (hz : z ∈ leftPrefixes x) (hzw : z ≤ w) (hwx : w ≤ x) : z.birthday ≤ w.birthday := by
  have hp := (mem_leftPrefixes_iff.mp hz).1
  have ht := birthdayTruncation_eq_of_left_between
    (birthday_lt_of_mem_leftPrefixes hz).le (by rwa [hp]) hwx
  have hb := birthday_birthdayTruncation_le_birthday w z.birthday
  rw [ht, hp] at hb
  exact hb

open IGame in
/-- Negation preserves intrinsic canonical prefix equations. -/
theorem birthdayTruncation_neg_of_eq {x y : Surreal.{u}}
    (h : birthdayTruncation x y.birthday = y) : birthdayTruncation (-x) y.birthday = -y := by
  have he := ofSets_eq_mk (s := leftPrefixes y) (t := rightPrefixes y)
    (H := leftPrefixes_lt_rightPrefixes y)
  generalize_proofs at he
  rw [ofSets_leftPrefixes_rightPrefixes] at he
  let g : IGame.{u} := !{out '' leftPrefixes y | out '' rightPrefixes y}
  have : Numeric g := by assumption
  change y = mk g at he
  have hf : Fits x.out g := by
    constructor
    · intro z hz
      change z ∈ (!{out '' leftPrefixes y | out '' rightPrefixes y} : IGame)ᴸ at hz
      rw [moves_left_ofSets] at hz
      obtain ⟨z, hz, rfl⟩ := hz
      have hzx := (mem_leftPrefixes_iff.mp (leftPrefixes_subset_of_birthdayTruncation_eq h hz)).2
      rw [← mk_le_mk, out_eq, out_eq]
      exact hzx.not_ge
    · intro z hz
      change z ∈ (!{out '' leftPrefixes y | out '' rightPrefixes y} : IGame)ᴿ at hz
      rw [moves_right_ofSets] at hz
      obtain ⟨z, hz, rfl⟩ := hz
      have hxz := (mem_rightPrefixes_iff.mp (rightPrefixes_subset_of_birthdayTruncation_eq h hz)).2
      rw [← mk_le_mk, out_eq, out_eq]
      exact hxz.not_ge
  have ht := hf.neg.birthdayTruncation_eq
  simpa only [mk_neg, ← he, out_eq, birthday_neg] using ht

/-- Negation commutes with every birthday truncation. -/
theorem birthdayTruncation_neg (x : Surreal.{u}) (a : NatOrdinal.{u}) :
    birthdayTruncation (-x) a = -birthdayTruncation x a := by
  rcases le_total a x.birthday with ha | ha
  · have hp : birthdayTruncation x (birthdayTruncation x a).birthday = birthdayTruncation x a := by
      rw [birthday_birthdayTruncation x ha]
    have ht := birthdayTruncation_neg_of_eq hp
    rwa [birthday_birthdayTruncation x ha] at ht
  · rw [birthdayTruncation_eq_self_of_birthday_le x ha,
      birthdayTruncation_eq_self_of_birthday_le (-x) (by simpa only [birthday_neg] using ha)]

/-- Negation exchanges canonical left and right prefix membership. -/
theorem neg_mem_leftPrefixes_iff {x z : Surreal.{u}} :
    -z ∈ leftPrefixes (-x) ↔ z ∈ rightPrefixes x := by
  rw [mem_leftPrefixes_iff, mem_rightPrefixes_iff, birthday_neg, birthdayTruncation_neg]
  simp only [neg_inj, neg_lt_neg_iff]

/-- Negation exchanges canonical right and left prefix membership. -/
theorem neg_mem_rightPrefixes_iff {x z : Surreal.{u}} :
    -z ∈ rightPrefixes (-x) ↔ z ∈ leftPrefixes x := by
  rw [mem_leftPrefixes_iff, mem_rightPrefixes_iff, birthday_neg, birthdayTruncation_neg]
  simp only [neg_inj, neg_lt_neg_iff]

/-- Canonical left prefixes of a negative are negatives of canonical right prefixes. -/
theorem leftPrefixes_neg (x : Surreal.{u}) : leftPrefixes (-x) = (- ·) '' rightPrefixes x := by
  ext z
  constructor
  · intro hz
    refine ⟨-z, ?_, neg_neg z⟩
    exact (neg_mem_leftPrefixes_iff (x := x) (z := -z)).mp (by simpa using hz)
  · rintro ⟨z, hz, rfl⟩
    exact neg_mem_leftPrefixes_iff.mpr hz

/-- Canonical right prefixes of a negative are negatives of canonical left prefixes. -/
theorem rightPrefixes_neg (x : Surreal.{u}) : rightPrefixes (-x) = (- ·) '' leftPrefixes x := by
  ext z
  constructor
  · intro hz
    refine ⟨-z, ?_, neg_neg z⟩
    exact (neg_mem_rightPrefixes_iff (x := x) (z := -z)).mp (by simpa using hz)
  · rintro ⟨z, hz, rfl⟩
    exact neg_mem_rightPrefixes_iff.mpr hz

/-- A birthday and the canonical right-prefix set determine a surreal number uniquely. -/
theorem eq_of_birthday_eq_of_rightPrefixes_eq {x y : Surreal.{u}}
    (hb : x.birthday = y.birthday) (hR : rightPrefixes x = rightPrefixes y) : x = y := by
  have aux : ∀ {x y : Surreal.{u}}, x.birthday = y.birthday →
      rightPrefixes x = rightPrefixes y → ¬ x < y := by
    intro x y hb hR hxy
    let z : Surreal.{u} := !{{x} | {y}}'(by simpa using hxy)
    have hxz : x < z := lt_ofSets_of_mem_left (mem_singleton x)
    have hzy : z < y := ofSets_lt_of_mem_right (mem_singleton y)
    have hzb : z.birthday < x.birthday :=
      birthday_ofSets_singleton_lt_of_birthday_eq rfl hb.symm hxy
    obtain ⟨a, ha, hxa, haz⟩ := exists_birthdayTruncation_right_le hzb hxz
    have hr : birthdayTruncation x a ∈ rightPrefixes x :=
      mem_rightPrefixes.mpr ⟨a, ha, rfl, hxa⟩
    rw [hR] at hr
    have hyr := (mem_rightPrefixes.mp hr).choose_spec.2.2
    exact ((hyr.trans_le haz).trans hzy).false
  exact le_antisymm (le_of_not_gt (aux hb.symm hR.symm)) (le_of_not_gt (aux hb hR))

/-- Zero has no canonical left prefixes. -/
@[simp]
theorem leftPrefixes_zero : leftPrefixes (0 : Surreal.{u}) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  simpa using birthday_lt_of_mem_leftPrefixes hz

/-- Zero has no canonical right prefixes. -/
@[simp]
theorem rightPrefixes_zero : rightPrefixes (0 : Surreal.{u}) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  simpa using birthday_lt_of_mem_rightPrefixes hz

/-- Ordinals have no canonical right prefixes. -/
@[simp]
theorem rightPrefixes_toSurreal (o : NatOrdinal.{u}) : rightPrefixes o.toSurreal = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨a, ha, he, hl⟩ := mem_rightPrefixes.mp hz
  have ha' : a < o := by simpa only [birthday_toSurreal] using ha
  rw [birthdayTruncation_toSurreal ha'.le] at he
  rw [← he] at hl
  exact (NatOrdinal.toSurreal.strictMono ha').not_gt hl

/-- Negative ordinals have no canonical left prefixes. -/
@[simp]
theorem leftPrefixes_neg_toSurreal (o : NatOrdinal.{u}) : leftPrefixes (-o.toSurreal) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hzb : z.birthday < o := by
    simpa only [birthday_neg, birthday_toSurreal] using birthday_lt_of_mem_leftPrefixes hz
  have hzx := (mem_leftPrefixes.mp hz).choose_spec.2.2
  have ht := z.neg_toSurreal_birthday_le.trans_lt hzx
  have ht' : o.toSurreal < z.birthday.toSurreal := neg_lt_neg_iff.mp ht
  exact hzb.not_gt (NatOrdinal.toSurreal.lt_iff_lt.mp ht')

/-- One is a canonical left prefix of two. -/
theorem one_mem_leftPrefixes_two : (1 : Surreal.{u}) ∈ leftPrefixes 2 := by
  apply mem_leftPrefixes.mpr
  exact ⟨1, by simp, birthdayTruncation_two_one, one_lt_two⟩

end Surreal
