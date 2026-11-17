/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Canonical
public import Mathlib.SetTheory.Ordinal.Basic

import Mathlib.Order.Hom.Set

/-!
# Plus counts from intrinsic birthday truncations

The order type of the positions at which the intrinsic prefix is below the number
counts the plus signs without introducing a separate representation of surreal numbers.
-/

universe u

public noncomputable section

namespace Surreal
open Ordinal

/-- The ordinal number of plus positions in the canonical sign expansion. -/
def plusCount (x : Surreal.{u}) : NatOrdinal.{u} :=
  NatOrdinal.of (typeLT {i : x.birthday.val.ToType |
    birthdayTruncation x (NatOrdinal.of i.toOrd.1) < x})

/-- The plus count is the order type of the canonical left-prefix positions. -/
theorem plusCount_eq (x : Surreal.{u}) :
    plusCount x = NatOrdinal.of (typeLT {i : x.birthday.val.ToType |
      birthdayTruncation x (NatOrdinal.of i.toOrd.1) < x}) := by
  unfold plusCount
  rfl

/-- The plus-position type may be indexed by any ordinal equal to the birthday. -/
theorem plusCount_eq_of_birthday_eq {x : Surreal.{u}} {b : NatOrdinal.{u}}
    (hb : x.birthday = b) :
    plusCount x = NatOrdinal.of (typeLT {i : b.val.ToType |
      birthdayTruncation x (NatOrdinal.of i.toOrd.1) < x}) := by
  subst b
  exact plusCount_eq x

/-- The number of plus signs is at most the birthday. -/
theorem plusCount_le_birthday (x : Surreal.{u}) : plusCount x ≤ x.birthday := by
  unfold plusCount
  exact NatOrdinal.of.monotone ((Ordinal.type_set_le _).trans_eq (Ordinal.type_toType _))

/-- Every sign of an ordinal is a plus sign. -/
@[simp]
theorem plusCount_toSurreal (b : NatOrdinal.{u}) : plusCount b.toSurreal = b := by
  rw [plusCount_eq_of_birthday_eq (birthday_toSurreal b)]
  have hs : {i : b.val.ToType | birthdayTruncation b.toSurreal (NatOrdinal.of i.toOrd.1) <
      b.toSurreal} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    have hi : NatOrdinal.of i.toOrd.1 < b := NatOrdinal.of.lt_iff_lt.mpr i.toOrd.2
    change birthdayTruncation b.toSurreal (NatOrdinal.of i.toOrd.1) < b.toSurreal
    rw [birthdayTruncation_toSurreal hi.le]
    exact NatOrdinal.toSurreal.lt_iff_lt.mpr hi
  rw [hs, (OrderIso.Set.univ).ordinalType_congr, Ordinal.type_toType, NatOrdinal.of_val]

/-- The plus positions of a prefix are exactly the earlier plus positions of the source. -/
theorem plusCount_birthdayTruncation_eq (x : Surreal.{u}) {a : NatOrdinal.{u}}
    (ha : a ≤ x.birthday) :
    plusCount (birthdayTruncation x a) = NatOrdinal.of (typeLT {i : a.val.ToType |
      birthdayTruncation x (NatOrdinal.of i.toOrd.1) < x}) := by
  rw [plusCount_eq_of_birthday_eq (birthday_birthdayTruncation x ha)]
  have hs : {i : a.val.ToType |
      birthdayTruncation (birthdayTruncation x a) (NatOrdinal.of i.toOrd.1) <
        birthdayTruncation x a} =
      {i : a.val.ToType | birthdayTruncation x (NatOrdinal.of i.toOrd.1) < x} := by
    ext i
    have hi : NatOrdinal.of i.toOrd.1 < a := NatOrdinal.of.lt_iff_lt.mpr i.toOrd.2
    change birthdayTruncation (birthdayTruncation x a) (NatOrdinal.of i.toOrd.1) <
      birthdayTruncation x a ↔ birthdayTruncation x (NatOrdinal.of i.toOrd.1) < x
    rw [birthdayTruncation_birthdayTruncation x hi.le ha,
      birthdayTruncation_lt_birthdayTruncation_iff x hi ha]
  rw [hs]

/-- Taking a prefix cannot increase the number of plus signs. -/
theorem plusCount_birthdayTruncation_le (x : Surreal.{u}) {a : NatOrdinal.{u}}
    (ha : a ≤ x.birthday) : plusCount (birthdayTruncation x a) ≤ plusCount x := by
  rw [plusCount_birthdayTruncation_eq x ha, plusCount_eq]
  apply NatOrdinal.of.monotone
  let f : {i : a.val.ToType | birthdayTruncation x (NatOrdinal.of i.toOrd.1) < x} →
      {i : x.birthday.val.ToType | birthdayTruncation x (NatOrdinal.of i.toOrd.1) < x} :=
    fun i ↦ ⟨Ordinal.ToType.mk ⟨i.1.toOrd.1,
      i.1.toOrd.2.trans_le (NatOrdinal.val.monotone ha)⟩, by
        change birthdayTruncation x
          (NatOrdinal.of ((Ordinal.ToType.mk _).toOrd.1)) < x
        simpa only [Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, Set.mem_ofPred_eq] using i.2⟩
  have hf : StrictMono f := by
    intro i j hij
    change Ordinal.ToType.mk _ < Ordinal.ToType.mk _
    apply Ordinal.ToType.mk.strictMono
    exact Ordinal.ToType.mk.symm.strictMono hij
  exact (RelEmbedding.ofMonotone f hf).ordinal_type_le

/-- A canonical left prefix has strictly fewer plus signs. -/
theorem plusCount_birthdayTruncation_lt (x : Surreal.{u}) {a : NatOrdinal.{u}}
    (ha : a < x.birthday) (hl : birthdayTruncation x a < x) :
    plusCount (birthdayTruncation x a) < plusCount x := by
  rw [plusCount_birthdayTruncation_eq x ha.le, plusCount_eq]
  apply NatOrdinal.of.lt_iff_lt.mpr
  let j : {i : x.birthday.val.ToType |
      birthdayTruncation x (NatOrdinal.of i.toOrd.1) < x} :=
    ⟨Ordinal.ToType.mk ⟨a.val, NatOrdinal.val.strictMono ha⟩, by
      change birthdayTruncation x (NatOrdinal.of ((Ordinal.ToType.mk _).toOrd.1)) < x
      simpa only [Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val] using hl⟩
  let f : {i : a.val.ToType | birthdayTruncation x (NatOrdinal.of i.toOrd.1) < x} →
      Set.Iio j := fun i ↦ ⟨⟨Ordinal.ToType.mk ⟨i.1.toOrd.1,
        i.1.toOrd.2.trans (NatOrdinal.val.strictMono ha)⟩, by
          change birthdayTruncation x (NatOrdinal.of ((Ordinal.ToType.mk _).toOrd.1)) < x
          simpa only [Ordinal.ToType.toOrd, OrderIso.symm_apply_apply,
            Set.mem_ofPred_eq] using i.2⟩, by
              change Ordinal.ToType.mk _ < Ordinal.ToType.mk _
              exact Ordinal.ToType.mk.strictMono i.1.toOrd.2⟩
  have hf : StrictMono f := by
    intro i k hik
    change Ordinal.ToType.mk _ < Ordinal.ToType.mk _
    apply Ordinal.ToType.mk.strictMono
    exact Ordinal.ToType.mk.symm.strictMono hik
  exact ((RelEmbedding.ofMonotone f hf).ordinal_type_le.trans_eq
    (Ordinal.type_Iio_lt j)).trans_lt (Ordinal.typein_lt_type _ j)

/-- A plus-count bound is equivalent to strict bounds for all canonical left prefixes. -/
theorem plusCount_le_iff_forall_birthdayTruncation (x : Surreal.{u}) (o : NatOrdinal.{u}) :
    plusCount x ≤ o ↔ ∀ a < x.birthday, birthdayTruncation x a < x →
      plusCount (birthdayTruncation x a) < o := by
  refine ⟨fun h a ha hl ↦ (plusCount_birthdayTruncation_lt x ha hl).trans_le h, ?_⟩
  intro h
  by_contra ho
  have ho' : o.val < typeLT {i : x.birthday.val.ToType |
      birthdayTruncation x (NatOrdinal.of i.toOrd.1) < x} := by
    simpa only [plusCount_eq, NatOrdinal.val_of] using
      NatOrdinal.val.strictMono (lt_of_not_ge ho)
  obtain ⟨i, hi⟩ := Ordinal.typein_surj (· < ·) ho'
  let a : NatOrdinal.{u} := NatOrdinal.of i.1.toOrd.1
  have ha : a < x.birthday := NatOrdinal.of.lt_iff_lt.mpr i.1.toOrd.2
  have hl : birthdayTruncation x a < x := i.2
  let f : Set.Iio i → {j : a.val.ToType |
      birthdayTruncation x (NatOrdinal.of j.toOrd.1) < x} := fun k ↦
    ⟨Ordinal.ToType.mk ⟨k.1.1.toOrd.1,
      Ordinal.ToType.mk.symm.strictMono k.2⟩, by
        change birthdayTruncation x (NatOrdinal.of ((Ordinal.ToType.mk _).toOrd.1)) < x
        simpa only [Ordinal.ToType.toOrd, OrderIso.symm_apply_apply,
          Set.mem_ofPred_eq] using k.1.2⟩
  have hf : StrictMono f := by
    intro j k hjk
    change Ordinal.ToType.mk _ < Ordinal.ToType.mk _
    apply Ordinal.ToType.mk.strictMono
    exact Ordinal.ToType.mk.symm.strictMono hjk
  have he : o.val ≤ typeLT {j : a.val.ToType |
      birthdayTruncation x (NatOrdinal.of j.toOrd.1) < x} := by
    rw [← hi, ← Ordinal.type_Iio_lt i]
    exact (RelEmbedding.ofMonotone f hf).ordinal_type_le
  have hb : o ≤ plusCount (birthdayTruncation x a) := by
    rw [plusCount_birthdayTruncation_eq x ha.le]
    exact NatOrdinal.of.monotone he
  exact (h a ha hl).not_ge hb

/-- Every smaller ordinal is bounded by the plus count of some canonical left prefix. -/
theorem exists_leftPrefixes_plusCount_ge {x : Surreal.{u}} {o : NatOrdinal.{u}}
    (ho : o < plusCount x) : ∃ z ∈ leftPrefixes x, o ≤ plusCount z := by
  by_contra h
  have hb : plusCount x ≤ o := by
    apply (plusCount_le_iff_forall_birthdayTruncation x o).mpr
    intro a ha hl
    apply lt_of_not_ge
    intro hg
    exact h ⟨_, mem_leftPrefixes.mpr ⟨a, ha, rfl, hl⟩, hg⟩
  exact ho.not_ge hb

/-- A prefix has at most as many plus signs as any number between it and its source. -/
theorem plusCount_le_of_left_between {x y : Surreal.{u}} {a : NatOrdinal.{u}}
    (ha : a ≤ x.birthday) (hL : birthdayTruncation x a ≤ y) (hR : y ≤ x) :
    plusCount (birthdayTruncation x a) ≤ plusCount y := by
  have he : birthdayTruncation y a = birthdayTruncation x a :=
    birthdayTruncation_eq_of_left_between ha hL hR
  have hay : a ≤ y.birthday := by
    rw [← birthday_birthdayTruncation x ha, ← he]
    exact birthday_birthdayTruncation_le_birthday y a
  rw [← he]
  exact plusCount_birthdayTruncation_le y hay

/-- Every canonical left prefix has strictly fewer plus signs than its source. -/
theorem plusCount_lt_of_mem_leftPrefixes {x z : Surreal.{u}} (hz : z ∈ leftPrefixes x) :
    plusCount z < plusCount x := by
  obtain ⟨a, ha, rfl, hl⟩ := mem_leftPrefixes.mp hz
  exact plusCount_birthdayTruncation_lt x ha hl

/-- Equal canonical left-prefix sets have equal plus counts. -/
theorem plusCount_eq_of_leftPrefixes_eq {x y : Surreal.{u}}
    (h : leftPrefixes x = leftPrefixes y) : plusCount x = plusCount y := by
  have aux : ∀ {x y : Surreal.{u}}, leftPrefixes x = leftPrefixes y →
      plusCount x ≤ plusCount y := by
    intro x y h
    apply (plusCount_le_iff_forall_birthdayTruncation x (plusCount y)).mpr
    intro a ha hl
    apply plusCount_lt_of_mem_leftPrefixes
    rw [← h]
    exact mem_leftPrefixes.mpr ⟨a, ha, rfl, hl⟩
  exact le_antisymm (aux h) (aux h.symm)

/-- If a prefix retains every plus sign, the source is at most that prefix. -/
theorem le_birthdayTruncation_of_plusCount_eq (x : Surreal.{u}) {a : NatOrdinal.{u}}
    (ha : a ≤ x.birthday) (he : plusCount (birthdayTruncation x a) = plusCount x) :
    x ≤ birthdayTruncation x a := by
  by_contra h
  have hx : birthdayTruncation x a < x := lt_of_not_ge h
  obtain ha | ha := ha.lt_or_eq
  · exact (plusCount_birthdayTruncation_lt x ha hx).ne he
  · rw [ha, birthdayTruncation_birthday] at hx
    exact hx.false

/-- A surreal with zero plus count has no canonical left prefixes. -/
theorem leftPrefixes_eq_empty_of_plusCount_eq_zero {x : Surreal.{u}}
    (hx : plusCount x = 0) : leftPrefixes x = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have ht := plusCount_lt_of_mem_leftPrefixes hz
  rw [hx] at ht
  exact ht.not_ge zero_le

/-- Absence of canonical left prefixes is equivalent to zero plus count. -/
theorem plusCount_eq_zero_iff {x : Surreal.{u}} : plusCount x = 0 ↔ leftPrefixes x = ∅ := by
  refine ⟨leftPrefixes_eq_empty_of_plusCount_eq_zero, fun hx ↦ ?_⟩
  apply le_antisymm _ zero_le
  apply (plusCount_le_iff_forall_birthdayTruncation x 0).mpr
  intro a ha hl
  have hz : birthdayTruncation x a ∈ leftPrefixes x := mem_leftPrefixes.mpr ⟨a, ha, rfl, hl⟩
  rw [hx] at hz
  exact False.elim hz

/-- Negative ordinals have zero plus count. -/
@[simp]
theorem plusCount_neg_toSurreal (o : NatOrdinal.{u}) : plusCount (-o.toSurreal) = 0 :=
  plusCount_eq_zero_iff.mpr (leftPrefixes_neg_toSurreal o)

/-- Zero has no plus signs. -/
@[simp]
theorem plusCount_zero : plusCount (0 : Surreal.{u}) = 0 := by
  simpa using plusCount_toSurreal (0 : NatOrdinal.{u})

end Surreal
