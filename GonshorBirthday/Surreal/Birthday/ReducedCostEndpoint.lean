/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostPlus
public import GonshorBirthday.Surreal.Birthday.ReducedCostBlocks

/-!
# Endpoints of retained minus signs

If every minus is deleted, the cost is the plus-only baseline. A bound on the
birthdays of retained right prefixes bounds all right prefixes once any minus is
retained. Beyond that endpoint the original word is an actual plus-block extension.
-/

universe u

public noncomputable section

namespace Surreal

open Ordinal

/-- If no canonical right prefix survives the cutoff, the cost is the plus-only baseline. -/
theorem reducedOmegaCost_eq_wpow_of_no_retained_rightPrefixes (C x : Surreal.{u})
    (h : ∀ y ∈ rightPrefixes x, ¬ y ≤ C) : reducedOmegaCost C x = ω^ plusCount x := by
  rw [reducedOmegaCost_eq]
  have hs : {i : x.birthday.val.ToType |
      birthdayTruncation x (NatOrdinal.of i.toOrd.1) < x ∨
        birthdayTruncation x (NatOrdinal.of i.toOrd.1) ≤ C} =
      {i | birthdayTruncation x (NatOrdinal.of i.toOrd.1) < x} := by
    ext i
    change (_ ∨ _) ↔ _
    constructor
    · rintro (hl | hC)
      · exact hl
      · by_contra hn
        have hi : NatOrdinal.of i.toOrd.1 < x.birthday := NatOrdinal.of.strictMono i.toOrd.2
        have hne : birthdayTruncation x (NatOrdinal.of i.toOrd.1) ≠ x := by
          intro he
          have hb := birthday_birthdayTruncation x hi.le
          rw [he] at hb
          exact hi.ne hb.symm
        have hr : x < birthdayTruncation x (NatOrdinal.of i.toOrd.1) :=
          lt_of_le_of_ne (le_of_not_gt hn) hne.symm
        exact h _ (mem_rightPrefixes.mpr ⟨_, hi, rfl, hr⟩) hC
    · exact Or.inl
  rw [hs, omegaExpansionLength_plusPositions]

/-- After a retained right prefix, every later original right prefix is retained too. -/
theorem rightPrefix_le_cutoff_of_birthday_le {C x y z : Surreal.{u}}
    (hy : y ∈ rightPrefixes x) (hyC : y ≤ C)
    (hz : z ∈ rightPrefixes x) (hyz : y.birthday ≤ z.birthday) : z ≤ C := by
  have hy' := mem_rightPrefixes_iff.mp hy
  have hz' := mem_rightPrefixes_iff.mp hz
  have h := birthdayTruncation_le_cutoff_of_rightPrefix_le (C := C) hyz
    (birthday_lt_of_mem_rightPrefixes hz).le
    (by rw [hy'.1]; exact hy'.2) (by rw [hy'.1]; exact hyC)
  simpa only [hz'.1] using h

/-- Among canonical right prefixes, a smaller value occurs strictly later. -/
theorem birthday_lt_of_rightPrefixes_lt {x y z : Surreal.{u}}
    (hy : y ∈ rightPrefixes x) (hz : z ∈ rightPrefixes x) (hzy : z < y) :
    y.birthday < z.birthday := by
  apply lt_of_not_ge
  intro h
  exact hzy.not_ge (rightPrefix_le_cutoff_of_birthday_le hz le_rfl hy h)

/-- A nonempty bounded retained-minus family bounds every original minus position. -/
theorem rightPrefixes_birthday_lt_of_retained_bounded {C x : Surreal.{u}}
    {a : NatOrdinal.{u}} (hne : ∃ y ∈ rightPrefixes x, y ≤ C)
    (hbound : ∀ y ∈ rightPrefixes x, y ≤ C → y.birthday < a) :
    ∀ z ∈ rightPrefixes x, z.birthday < a := by
  obtain ⟨y, hy, hyC⟩ := hne
  intro z hz
  rcases le_total z.birthday y.birthday with hzy | hyz
  · exact hzy.trans_lt (hbound y hy hyC)
  · exact hbound z hz (rightPrefix_le_cutoff_of_birthday_le hy hyC hz hyz)

/-- If every original minus is before a prefix, the remaining word is its plus extension. -/
theorem appendPluses_birthdayTruncation_eq_of_rightPrefixes_before (x : Surreal.{u})
    {a : NatOrdinal.{u}} (ha : a ≤ x.birthday)
    (hR : ∀ y ∈ rightPrefixes x, y.birthday < a) :
    appendPluses (birthdayTruncation x a) (x.birthday.val - a.val) = x := by
  apply (appendPluses_eq_iff _ _ _).mpr
  constructor
  · rw [birthday_birthdayTruncation x ha,
      Ordinal.add_sub_cancel_of_le (NatOrdinal.val.monotone ha), NatOrdinal.of_val]
  · apply Set.Subset.antisymm
    · intro y hy
      have hy' := mem_rightPrefixes_iff.mp hy
      apply mem_rightPrefixes_iff.mpr
      constructor
      · rw [birthdayTruncation_birthdayTruncation x (hR y hy).le ha, hy'.1]
      · exact (birthdayTruncation_lt_iff ha (hR y hy)).mpr hy'.2
    · apply rightPrefixes_subset_of_birthdayTruncation_eq
      rw [birthday_birthdayTruncation x ha]

/-- A proper prefix after all minuses leaves a nonempty plus power in the reduced cost. -/
theorem reducedOmegaCost_eq_prefix_add_wpow_of_rightPrefixes_before (C x : Surreal.{u})
    {a : NatOrdinal.{u}} (ha : a < x.birthday)
    (hR : ∀ y ∈ rightPrefixes x, y.birthday < a) :
    plusCount (birthdayTruncation x a) < plusCount x ∧
      reducedOmegaCost C x = NatOrdinal.of
        ((reducedOmegaCost C (birthdayTruncation x a)).val + (ω^ plusCount x).val) := by
  have he := appendPluses_birthdayTruncation_eq_of_rightPrefixes_before x ha.le hR
  have hpos : 0 < x.birthday.val - a.val := by
    exact pos_iff_ne_zero.mpr (Ordinal.sub_ne_zero_iff_lt.mpr (NatOrdinal.val.strictMono ha))
  constructor
  · have hp := strictMono_plusCount_appendPluses (birthdayTruncation x a) hpos
    simpa only [appendPluses_zero, he] using hp
  · have hc := reducedOmegaCost_appendPluses C (birthdayTruncation x a) (ne_of_gt hpos)
    rwa [he] at hc

/-- A retained appended minus contributes exactly its original expanded block. -/
theorem reducedOmegaCost_appendMinus_of_le {C x : Surreal.{u}} (hC : x ≤ C) :
    reducedOmegaCost C (appendMinus x) = NatOrdinal.of
      ((reducedOmegaCost C x).val + (ω^ (plusCount x + 1)).val) := by
  have hx : x.birthday < (appendMinus x).birthday := by
    rw [birthday_appendMinus]
    exact lt_add_one _
  let j : reducedOmegaPositions C (appendMinus x) :=
    ⟨Ordinal.ToType.mk ⟨x.birthday.val, NatOrdinal.val.strictMono hx⟩, by
      apply mem_reducedOmegaPositions.mpr
      right
      simpa only [Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val,
        birthdayTruncation_appendMinus] using hC⟩
  have hjmax (i : reducedOmegaPositions C (appendMinus x)) : i ≤ j := by
    change i.1 ≤ Ordinal.ToType.mk _
    apply Ordinal.ToType.mk.symm.le_iff_le.mp
    rw [OrderIso.symm_apply_apply]
    change i.1.toOrd.1 ≤ x.birthday.val
    have he : (appendMinus x).birthday.val = x.birthday.val + 1 :=
      (congrArg NatOrdinal.val (birthday_appendMinus x)).trans (NatOrdinal.val_add_one _)
    exact Order.lt_add_one_iff.mp (i.1.toOrd.2.trans_eq he)
  let : Unique (Set.Ici j) :=
    { default := ⟨j, le_refl j⟩
      uniq := fun i ↦ Subtype.ext (le_antisymm (hjmax i.1) i.2) }
  have hp (i : Set.Ici j) :
      plusCount (birthdayTruncation (appendMinus x) (NatOrdinal.of i.1.1.toOrd.1)) =
        plusCount x := by
    have hi : i = ⟨j, le_refl j⟩ := Subsingleton.elim _ _
    rw [hi]
    simp only [j, Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val,
      birthdayTruncation_appendMinus]
  have h := reducedOmegaCost_eq_prefix_add_mul_of_constant_plusCount C (appendMinus x)
    j (plusCount x) hp
  rw [Ordinal.type_eq_one_of_unique, mul_one] at h
  simpa only [j, Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val,
    birthdayTruncation_appendMinus] using h

/-- At a last retained minus, the completed right-prefix budget is the exact whole cost. -/
theorem reducedOmegaCost_eq_of_last_retained_rightPrefix {C x y : Surreal.{u}}
    (hy : y ∈ rightPrefixes x) (hyC : y ≤ C)
    (hlast : ∀ z ∈ rightPrefixes x, z ≤ C → z.birthday ≤ y.birthday) :
    reducedOmegaCost C x = NatOrdinal.of
      ((reducedOmegaCost C y).val + (ω^ (plusCount y + 1)).val +
        if plusCount y < plusCount x then (ω^ plusCount x).val else 0) := by
  have ha : y.birthday + 1 ≤ x.birthday :=
    Order.add_one_le_iff.mpr (birthday_lt_of_mem_rightPrefixes hy)
  have hR : ∀ z ∈ rightPrefixes x, z.birthday < y.birthday + 1 :=
    rightPrefixes_birthday_lt_of_retained_bounded ⟨y, hy, hyC⟩
      (fun z hz hzC ↦ (hlast z hz hzC).trans_lt (lt_add_one _))
  have ht : birthdayTruncation x (y.birthday + 1) = appendMinus y := by
    have ht := birthdayTruncation_add_one_eq_appendMinus x ha
      (by rw [(mem_rightPrefixes_iff.mp hy).1]; exact (mem_rightPrefixes_iff.mp hy).2)
    simpa only [(mem_rightPrefixes_iff.mp hy).1] using ht
  have hp : plusCount (birthdayTruncation x (y.birthday + 1)) = plusCount y := by
    rw [ht, plusCount_appendMinus]
  have hc : reducedOmegaCost C (birthdayTruncation x (y.birthday + 1)) =
      NatOrdinal.of ((reducedOmegaCost C y).val + (ω^ (plusCount y + 1)).val) := by
    rw [ht, reducedOmegaCost_appendMinus_of_le hyC]
  rcases ha.lt_or_eq with ha | ha
  · obtain ⟨hp', he⟩ := reducedOmegaCost_eq_prefix_add_wpow_of_rightPrefixes_before C x ha hR
    rw [hp] at hp'
    rw [hc, NatOrdinal.val_of] at he
    rw [ite_eq_left hp']
    exact he
  · have he : birthdayTruncation x (y.birthday + 1) = x := by
      rw [ha, birthdayTruncation_birthday]
    rw [he] at hp hc
    rw [hp, ite_eq_right (lt_irrefl (plusCount y)), add_zero]
    exact hc

end Surreal
