/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Append

/-!
# Ordinal-length constant-sign extensions

Every extension is a cut of actual surreal numbers. Ordinal addition in the
birthday and plus-count formulas is ordinary concatenation, not natural addition.
-/

universe u
public noncomputable section
namespace Surreal
open Set

private def appendPlusesAux (x : Surreal.{u}) (a : Ordinal.{u}) :
    {y : Surreal.{u} // ∀ z ∈ rightPrefixes x, y < z} :=
  if ha : a = 0 then
    ⟨x, fun _ hz ↦ (mem_rightPrefixes.mp hz).choose_spec.2.2⟩
  else
    let s : Set Surreal.{u} := insert x
      (range (fun b : Iio a ↦ (appendPlusesAux x b.1).1))
    let H : ∀ z ∈ s, ∀ w ∈ rightPrefixes x, z < w := by
      rintro z (rfl | ⟨b, rfl⟩) w hw
      · exact (mem_rightPrefixes.mp hw).choose_spec.2.2
      · exact (appendPlusesAux x b.1).2 w hw
    ⟨!{s | rightPrefixes x}'H, fun _ hz ↦ ofSets_lt_of_mem_right hz⟩
termination_by a
decreasing_by all_goals exact b.2

/-- Append an ordinal-length block of plus signs to the canonical expansion. -/
def appendPluses (x : Surreal.{u}) (a : Ordinal.{u}) : Surreal.{u} :=
  (appendPlusesAux x a).1

/-- Appending an empty block preserves the number. -/
@[simp]
theorem appendPluses_zero (x : Surreal.{u}) : appendPluses x 0 = x := by
  unfold appendPluses appendPlusesAux
  simp

/-- A plus block remains below every original canonical right prefix. -/
theorem appendPluses_lt_of_mem_rightPrefixes (x : Surreal.{u}) (a : Ordinal.{u})
    {z : Surreal.{u}} (hz : z ∈ rightPrefixes x) : appendPluses x a < z :=
  (appendPlusesAux x a).2 z hz

/-- A nonempty plus block is the simplest number above all its earlier stages. -/
theorem appendPluses_eq_of_ne_zero (x : Surreal.{u}) {a : Ordinal.{u}} (ha : a ≠ 0) :
    appendPluses x a =
      !{insert x (range (fun b : Iio a ↦ appendPluses x b.1)) | rightPrefixes x}'(by
        rintro z (rfl | ⟨b, rfl⟩) w hw
        · exact (mem_rightPrefixes.mp hw).choose_spec.2.2
        · exact appendPluses_lt_of_mem_rightPrefixes x b.1 hw) := by
  unfold appendPluses
  rw [appendPlusesAux, dite_eq_right ha]
  rfl

/-- Appending a one-sign block gives the canonical plus successor. -/
@[simp]
theorem appendPluses_one (x : Surreal.{u}) : appendPluses x 1 = appendPlus x := by
  have hr : range (fun b : Iio (1 : Ordinal.{u}) ↦ appendPluses x b.1) = {x} := by
    ext z
    constructor
    · rintro ⟨b, rfl⟩
      have hb : b.1 = 0 := Order.lt_one_iff.mp b.2
      simp only [hb, appendPluses_zero, mem_singleton_iff]
    · intro hz
      have hz' : z = x := mem_singleton_iff.mp hz
      subst z
      exact ⟨⟨0, (show (0 : Ordinal.{u}) < 1 from zero_lt_one)⟩, appendPluses_zero x⟩
  rw [appendPluses_eq_of_ne_zero x one_ne_zero, appendPlus_eq_ofSets]
  congr 1
  rw [hr, insert_eq_of_mem (mem_singleton x)]

/-- Appending a block of plus signs does not decrease the number. -/
theorem le_appendPluses (x : Surreal.{u}) (a : Ordinal.{u}) : x ≤ appendPluses x a := by
  obtain rfl | ha := eq_or_ne a 0
  · rw [appendPluses_zero]
  · rw [appendPluses_eq_of_ne_zero x ha]
    exact (lt_ofSets_of_mem_left (mem_insert x _)).le

/-- Plus-block extensions increase strictly with their length. -/
theorem strictMono_appendPluses (x : Surreal.{u}) : StrictMono (appendPluses x) := by
  intro a b hab
  rw [appendPluses_eq_of_ne_zero x (ne_bot_of_gt hab)]
  exact lt_ofSets_of_mem_left (mem_insert_of_mem _ (mem_range_self (⟨a, hab⟩ : Iio b)))

/-- The original number is a canonical prefix of its plus-block extension. -/
theorem birthdayTruncation_appendPluses (x : Surreal.{u}) (a : Ordinal.{u}) :
    birthdayTruncation (appendPluses x a) x.birthday = x := by
  have ht := birthdayTruncation_eq_of_btwn
    (H := leftPrefixes_lt_rightPrefixes x)
    (fun z hz ↦ ((mem_leftPrefixes.mp hz).choose_spec.2.2).trans_le (le_appendPluses x a))
    (fun _ hz ↦ appendPluses_lt_of_mem_rightPrefixes x a hz)
  simpa only [ofSets_leftPrefixes_rightPrefixes] using ht

/-- Every earlier plus-block stage is a canonical prefix of every later stage. -/
theorem birthdayTruncation_appendPluses_of_lt (x : Surreal.{u}) {a b : Ordinal.{u}}
    (hab : a < b) : birthdayTruncation (appendPluses x b) (appendPluses x a).birthday =
      appendPluses x a := by
  obtain rfl | ha := eq_or_ne a 0
  · rw [appendPluses_zero]
    exact birthdayTruncation_appendPluses x b
  · rw [appendPluses_eq_of_ne_zero x ha]
    apply birthdayTruncation_eq_of_btwn
    · rintro z (hz | ⟨c, rfl⟩)
      · subst z
        exact (le_appendPluses x a).trans_lt (strictMono_appendPluses x hab)
      · exact strictMono_appendPluses x (c.2.trans hab)
    · exact fun _ hz ↦ appendPluses_lt_of_mem_rightPrefixes x b hz

/-- The birthdays of plus-block extensions increase strictly with the block length. -/
theorem strictMono_birthday_appendPluses (x : Surreal.{u}) :
    StrictMono (fun a : Ordinal.{u} ↦ (appendPluses x a).birthday) := by
  intro a b hab
  have hp := birthdayTruncation_appendPluses_of_lt x hab
  have hle : (appendPluses x a).birthday ≤ (appendPluses x b).birthday := by
    rw [← hp]
    exact birthday_birthdayTruncation_le_birthday _ _
  apply hle.lt_of_ne
  intro he
  rw [he, birthdayTruncation_birthday] at hp
  exact (strictMono_appendPluses x hab).ne hp.symm

/-- Appending a plus block concatenates its length to the birthday. -/
theorem birthday_appendPluses (x : Surreal.{u}) (a : Ordinal.{u}) :
    (appendPluses x a).birthday = NatOrdinal.of (x.birthday.val + a) := by
  induction a using Ordinal.lt_wf.induction with
  | ind a ih =>
    obtain rfl | ha := eq_or_ne a 0
    · simp only [appendPluses_zero, add_zero, NatOrdinal.of_val]
    · apply le_antisymm
      · rw [appendPluses_eq_of_ne_zero x ha]
        apply birthday_ofSets_le.trans
        apply max_le
        · apply csSup_le'
          rintro _ ⟨z, (hz | ⟨b, rfl⟩), rfl⟩
          · subst z
            have ht := NatOrdinal.of.monotone
              (add_le_add_right (Order.one_le_iff_ne_zero.mpr ha) x.birthday.val)
            simpa only [NatOrdinal.of_add_one, NatOrdinal.of_val] using ht
          · change (appendPluses x b.1).birthday + 1 ≤ _
            rw [ih b.1 b.2, ← NatOrdinal.of_add_one]
            apply NatOrdinal.of.monotone
            rw [add_assoc]
            exact add_le_add_right (Order.add_one_le_iff.mpr b.2) _
        · apply csSup_le'
          rintro _ ⟨z, hz, rfl⟩
          apply (Order.add_one_le_iff.mpr (birthday_lt_of_mem_rightPrefixes hz)).trans
          exact NatOrdinal.of.monotone le_self_add
      · apply NatOrdinal.val.le_iff_le.mp
        rw [NatOrdinal.val_of]
        apply (Ordinal.add_le_iff ha).mpr
        intro b hb
        have ht := strictMono_birthday_appendPluses x hb
        change (appendPluses x b).birthday < (appendPluses x a).birthday at ht
        rw [ih b hb] at ht
        exact NatOrdinal.val.strictMono ht

/-- Truncating a plus block at an earlier block length gives the earlier stage. -/
theorem birthdayTruncation_appendPluses_add (x : Surreal.{u}) {a b : Ordinal.{u}}
    (hb : b ≤ a) : birthdayTruncation (appendPluses x a)
      (NatOrdinal.of (x.birthday.val + b)) = appendPluses x b := by
  rw [← birthday_appendPluses x b]
  rcases hb.lt_or_eq with hb | hb
  · exact birthdayTruncation_appendPluses_of_lt x hb
  · rw [hb, birthdayTruncation_birthday]

/-- Truncating before the appended block gives the corresponding original prefix. -/
theorem birthdayTruncation_appendPluses_of_le (x : Surreal.{u}) (a : Ordinal.{u})
    {b : NatOrdinal.{u}} (hb : b ≤ x.birthday) :
    birthdayTruncation (appendPluses x a) b = birthdayTruncation x b := by
  have hx : x.birthday ≤ (appendPluses x a).birthday := by
    have ht := birthday_birthdayTruncation_le_birthday (appendPluses x a) x.birthday
    rwa [birthdayTruncation_appendPluses] at ht
  have ht := birthdayTruncation_birthdayTruncation (appendPluses x a) hb hx
  rw [birthdayTruncation_appendPluses] at ht
  exact ht.symm

/-- Every sign in the appended block is a plus sign. -/
theorem birthdayTruncation_appendPluses_lt {x : Surreal.{u}} {a : Ordinal.{u}}
    {b : NatOrdinal.{u}} (hxb : x.birthday ≤ b) (hb : b < (appendPluses x a).birthday) :
    birthdayTruncation (appendPluses x a) b < appendPluses x a := by
  let c : Ordinal.{u} := b.val - x.birthday.val
  have hc : x.birthday.val + c = b.val :=
    Ordinal.add_sub_cancel_of_le (NatOrdinal.val.monotone hxb)
  have hca : c < a := by
    have ht := NatOrdinal.val.strictMono hb
    rw [birthday_appendPluses, NatOrdinal.val_of, ← hc] at ht
    exact (add_lt_add_iff_left x.birthday.val).mp ht
  have ht := birthdayTruncation_appendPluses_add x hca.le
  rw [hc, NatOrdinal.of_val] at ht
  rw [ht]
  exact strictMono_appendPluses x hca

/-- Appending any block of plus signs preserves the set of canonical right prefixes. -/
theorem rightPrefixes_appendPluses (x : Surreal.{u}) (a : Ordinal.{u}) :
    rightPrefixes (appendPluses x a) = rightPrefixes x := by
  ext z
  constructor
  · intro hz
    obtain ⟨b, hb, he, hl⟩ := mem_rightPrefixes.mp hz
    rcases le_or_gt x.birthday b with hxb | hbx
    · have ht := birthdayTruncation_appendPluses_lt hxb hb
      rw [he] at ht
      exact False.elim (ht.not_gt hl)
    · apply mem_rightPrefixes.mpr
      refine ⟨b, hbx, ?_, (le_appendPluses x a).trans_lt hl⟩
      rw [← birthdayTruncation_appendPluses_of_le x a hbx.le]
      exact he
  · intro hz
    obtain ⟨b, hb, he, _⟩ := mem_rightPrefixes.mp hz
    have hx : x.birthday ≤ (appendPluses x a).birthday := by
      have ht := birthday_birthdayTruncation_le_birthday (appendPluses x a) x.birthday
      rwa [birthdayTruncation_appendPluses] at ht
    apply mem_rightPrefixes.mpr
    refine ⟨b, hb.trans_le hx, ?_, appendPluses_lt_of_mem_rightPrefixes x a hz⟩
    rw [birthdayTruncation_appendPluses_of_le x a hb.le]
    exact he

/-- Plus-block extensions are characterised by their birthday and unchanged right prefixes. -/
theorem appendPluses_eq_iff (x y : Surreal.{u}) (a : Ordinal.{u}) :
    appendPluses x a = y ↔ y.birthday = NatOrdinal.of (x.birthday.val + a) ∧
      rightPrefixes y = rightPrefixes x := by
  constructor
  · rintro rfl
    exact ⟨birthday_appendPluses x a, rightPrefixes_appendPluses x a⟩
  · rintro ⟨hb, hR⟩
    apply eq_of_birthday_eq_of_rightPrefixes_eq
    · exact (birthday_appendPluses x a).trans hb.symm
    · exact (rightPrefixes_appendPluses x a).trans hR.symm

/-- Appending a plus block to an ordinal gives ordinary ordinal addition. -/
theorem appendPluses_toSurreal (o : NatOrdinal.{u}) (a : Ordinal.{u}) :
    appendPluses o.toSurreal a = (NatOrdinal.of (o.val + a)).toSurreal := by
  apply eq_of_birthday_eq_of_rightPrefixes_eq
  · rw [birthday_appendPluses, birthday_toSurreal, birthday_toSurreal]
  · rw [rightPrefixes_appendPluses, rightPrefixes_toSurreal, rightPrefixes_toSurreal]

/-- Appending a plus block to zero gives that ordinal. -/
@[simp]
theorem appendPluses_zero_left (a : Ordinal.{u}) :
    appendPluses (0 : Surreal.{u}) a = (NatOrdinal.of a).toSurreal := by
  have ht := appendPluses_toSurreal (0 : NatOrdinal.{u}) a
  simpa using ht

/-- A one-plus successor preserves every canonical right prefix. -/
theorem rightPrefixes_appendPlus (x : Surreal.{u}) :
    rightPrefixes (appendPlus x) = rightPrefixes x := by
  simpa only [appendPluses_one] using rightPrefixes_appendPluses x 1

/-- A one-plus successor adds precisely its source to the canonical left-prefix set. -/
theorem leftPrefixes_appendPlus (x : Surreal.{u}) :
    leftPrefixes (appendPlus x) = insert x (leftPrefixes x) := by
  ext z
  constructor
  · intro hz
    have hzb : z.birthday ≤ x.birthday := by
      have ht := birthday_lt_of_mem_leftPrefixes hz
      rw [birthday_appendPlus] at ht
      exact Order.lt_add_one_iff.mp ht
    have hpz := (mem_leftPrefixes_iff.mp hz).1
    have hzx := (mem_leftPrefixes_iff.mp hz).2
    rcases hzb.lt_or_eq with hzb | hzb
    · right
      apply mem_leftPrefixes_iff.mpr
      constructor
      · rw [← birthdayTruncation_appendPlus_of_le x hzb.le]
        exact hpz
      · have hb : x.birthday ≤ (appendPlus x).birthday := by
          rw [birthday_appendPlus]
          exact le_add_of_nonneg_right zero_le
        have ht := (lt_birthdayTruncation_iff hb hzb).mpr hzx
        rwa [birthdayTruncation_appendPlus] at ht
    · left
      rw [hzb, birthdayTruncation_appendPlus] at hpz
      exact hpz.symm
  · rintro (hz | hz)
    · subst z
      exact mem_leftPrefixes_iff.mpr ⟨birthdayTruncation_appendPlus x, lt_appendPlus x⟩
    · apply mem_leftPrefixes_iff.mpr
      constructor
      · rw [birthdayTruncation_appendPlus_of_le x (birthday_lt_of_mem_leftPrefixes hz).le]
        exact (mem_leftPrefixes_iff.mp hz).1
      · exact (mem_leftPrefixes_iff.mp hz).2.trans (lt_appendPlus x)

/-- A larger number with unchanged right prefixes and no later left prefix is the plus successor. -/
theorem appendPlus_eq_of_rightPrefixes_eq {x y : Surreal.{u}} (hxy : x < y)
    (hR : rightPrefixes y = rightPrefixes x) (hL : ∀ z ∈ leftPrefixes y, z ≤ x) :
    appendPlus x = y := by
  have hR' : ∀ z ∈ rightPrefixes x, y < z := by
    intro z hz
    have hz' : z ∈ rightPrefixes y := by rwa [hR]
    exact (mem_rightPrefixes_iff.mp hz').2
  have hp : birthdayTruncation y (appendPlus x).birthday = appendPlus x := by
    rw [appendPlus_eq_ofSets]
    apply birthdayTruncation_eq_of_btwn
    · intro z hz
      have hz' : z = x := mem_singleton_iff.mp hz
      rwa [hz']
    · exact hR'
  rcases lt_trichotomy (appendPlus x) y with hy | hy | hy
  · have hz : appendPlus x ∈ leftPrefixes y := mem_leftPrefixes_iff.mpr ⟨hp, hy⟩
    exact False.elim ((lt_appendPlus x).not_ge (hL _ hz))
  · exact hy
  · have hz : appendPlus x ∈ rightPrefixes y := mem_rightPrefixes_iff.mpr ⟨hp, hy⟩
    rw [hR] at hz
    exact False.elim ((appendPlus_lt_of_mem_rightPrefixes hz).false)

/-- Plus counts increase strictly with the appended plus-block length. -/
theorem strictMono_plusCount_appendPluses (x : Surreal.{u}) :
    StrictMono (fun a : Ordinal.{u} ↦ plusCount (appendPluses x a)) := by
  intro a b hab
  have hp := birthdayTruncation_appendPluses_of_lt x hab
  have hb := strictMono_birthday_appendPluses x hab
  have hl : birthdayTruncation (appendPluses x b) (appendPluses x a).birthday <
      appendPluses x b := by
    rw [hp]
    exact strictMono_appendPluses x hab
  have ht := plusCount_birthdayTruncation_lt (appendPluses x b) hb hl
  simpa only [hp] using ht

/-- Appending a plus block concatenates its length to the plus count. -/
theorem plusCount_appendPluses (x : Surreal.{u}) (a : Ordinal.{u}) :
    plusCount (appendPluses x a) = NatOrdinal.of ((plusCount x).val + a) := by
  induction a using Ordinal.lt_wf.induction with
  | ind a ih =>
    obtain rfl | ha := eq_or_ne a 0
    · simp only [appendPluses_zero, add_zero, NatOrdinal.of_val]
    · apply le_antisymm
      · apply (plusCount_le_iff_forall_birthdayTruncation _ _).mpr
        intro c hc hl
        let z : Surreal.{u} := birthdayTruncation (appendPluses x a) c
        have hzl : z < appendPluses x a := hl
        have hzb : z.birthday < (appendPluses x a).birthday := by
          rw [birthday_birthdayTruncation _ hc.le]
          exact hc
        rw [appendPluses_eq_of_ne_zero x ha] at hzl hzb
        obtain ⟨w, hw, hzw⟩ := exists_mem_left_ge_of_birthday_lt hzl hzb
        rcases hw with hw | ⟨b, rfl⟩
        · subst w
          have ht := plusCount_le_of_left_between hc.le hzw (le_appendPluses x a)
          apply ht.trans_lt
          have hpos : (0 : Ordinal.{u}) < a := bot_lt_iff_ne_bot.mpr ha
          have ht' := NatOrdinal.of.strictMono (add_lt_add_right hpos (plusCount x).val)
          simpa only [add_zero, NatOrdinal.of_val] using ht'
        · have ht := plusCount_le_of_left_between hc.le hzw
            (strictMono_appendPluses x b.2).le
          apply ht.trans_lt
          rw [ih b.1 b.2]
          exact NatOrdinal.of.strictMono (add_lt_add_right b.2 _)
      · apply NatOrdinal.val.le_iff_le.mp
        rw [NatOrdinal.val_of]
        apply (Ordinal.add_le_iff ha).mpr
        intro b hb
        have ht := strictMono_plusCount_appendPluses x hb
        change plusCount (appendPluses x b) < plusCount (appendPluses x a) at ht
        rw [ih b hb] at ht
        exact NatOrdinal.val.strictMono ht

end Surreal
