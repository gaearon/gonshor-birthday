/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Constant

/-!
# Ordinal-length blocks of minus signs

Negation transports intrinsic canonical prefixes and gives the decreasing counterpart
of ordinal-length plus extensions.
-/

universe u
public noncomputable section
namespace Surreal

/-- Append an ordinal-length constant block of minus signs. -/
def appendMinuses (x : Surreal.{u}) (a : Ordinal.{u}) : Surreal.{u} :=
  -appendPluses (-x) a

/-- Minus-block extension is negated plus-block extension of the negative source. -/
theorem appendMinuses_eq_neg (x : Surreal.{u}) (a : Ordinal.{u}) :
    appendMinuses x a = -appendPluses (-x) a := by
  unfold appendMinuses
  rfl

/-- Appending an empty minus block fixes the source. -/
@[simp]
theorem appendMinuses_zero (x : Surreal.{u}) : appendMinuses x 0 = x := by
  rw [appendMinuses_eq_neg, appendPluses_zero, neg_neg]

/-- One minus sign agrees with the canonical minus successor. -/
@[simp]
theorem appendMinuses_one (x : Surreal.{u}) : appendMinuses x 1 = appendMinus x := by
  have hL : ∀ z ∈ leftPrefixes x, z < appendMinuses x 1 := by
    intro z hz
    rw [appendMinuses_eq_neg]
    have h := appendPluses_lt_of_mem_rightPrefixes (-x) 1
      (neg_mem_rightPrefixes_iff.mpr hz)
    simpa only [neg_neg] using neg_lt_neg_iff.mpr h
  have hR : ∀ z ∈ ({x} : Set Surreal.{u}), appendMinuses x 1 < z := by
    intro z hz
    have he : z = x := Set.mem_singleton_iff.mp hz
    subst z
    rw [appendMinuses_eq_neg]
    have h := strictMono_appendPluses (-x) (show (0 : Ordinal.{u}) < 1 from zero_lt_one)
    rw [appendPluses_zero] at h
    simpa only [neg_neg] using neg_lt_neg_iff.mpr h
  by_contra he
  have hb : (appendMinus x).birthday < (appendMinuses x 1).birthday := by
    rw [appendMinus_eq_ofSets] at he ⊢
    exact birthday_ofSets_lt_of_btwn hL hR (Ne.symm he)
  rw [birthday_appendMinus, appendMinuses_eq_neg, birthday_neg,
    birthday_appendPluses, birthday_neg] at hb
  rw [NatOrdinal.of_add_one, NatOrdinal.of_val] at hb
  exact hb.false

/-- Appending a minus block concatenates its length to the birthday. -/
theorem birthday_appendMinuses (x : Surreal.{u}) (a : Ordinal.{u}) :
    (appendMinuses x a).birthday = NatOrdinal.of (x.birthday.val + a) := by
  rw [appendMinuses_eq_neg, birthday_neg, birthday_appendPluses, birthday_neg]

/-- The source is a canonical prefix of its minus-block extension. -/
theorem birthdayTruncation_appendMinuses (x : Surreal.{u}) (a : Ordinal.{u}) :
    birthdayTruncation (appendMinuses x a) x.birthday = x := by
  rw [appendMinuses_eq_neg, birthdayTruncation_neg]
  have h := birthdayTruncation_appendPluses (-x) a
  rw [birthday_neg] at h
  rw [h, neg_neg]

/-- Minus-block stages decrease strictly with their ordinal lengths. -/
theorem strictAnti_appendMinuses (x : Surreal.{u}) : StrictAnti (appendMinuses x) := by
  intro a b hab
  rw [appendMinuses_eq_neg, appendMinuses_eq_neg, neg_lt_neg_iff]
  exact strictMono_appendPluses (-x) hab

/-- Every earlier minus-block stage is a canonical prefix of every later stage. -/
theorem birthdayTruncation_appendMinuses_of_lt (x : Surreal.{u}) {a b : Ordinal.{u}}
    (hab : a < b) : birthdayTruncation (appendMinuses x b) (appendMinuses x a).birthday =
      appendMinuses x a := by
  rw [appendMinuses_eq_neg, appendMinuses_eq_neg, birthday_neg, birthdayTruncation_neg,
    birthdayTruncation_appendPluses_of_lt (-x) hab]

/-- Truncating a minus block at an earlier length gives that earlier stage. -/
theorem birthdayTruncation_appendMinuses_add (x : Surreal.{u}) {a b : Ordinal.{u}}
    (hb : b ≤ a) : birthdayTruncation (appendMinuses x a)
      (NatOrdinal.of (x.birthday.val + b)) = appendMinuses x b := by
  rw [appendMinuses_eq_neg, birthdayTruncation_neg]
  have ht := birthdayTruncation_appendPluses_add (-x) hb
  rw [birthday_neg] at ht
  rw [ht, ← appendMinuses_eq_neg]

/-- Appending minus signs preserves every canonical left prefix. -/
theorem leftPrefixes_appendMinuses (x : Surreal.{u}) (a : Ordinal.{u}) :
    leftPrefixes (appendMinuses x a) = leftPrefixes x := by
  rw [appendMinuses_eq_neg, leftPrefixes_neg, rightPrefixes_appendPluses,
    ← leftPrefixes_neg, neg_neg]

/-- Appending minus signs preserves the plus count. -/
theorem plusCount_appendMinuses (x : Surreal.{u}) (a : Ordinal.{u}) :
    plusCount (appendMinuses x a) = plusCount x :=
  plusCount_eq_of_leftPrefixes_eq (leftPrefixes_appendMinuses x a)

end Surreal
