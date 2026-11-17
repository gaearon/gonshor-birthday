/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadCost
public import GonshorBirthday.Surreal.Birthday.ReducedCostEndpoint

/-!
# Prefix recurrences for native head costs

One native retention cutoff represents the whole exponent and every canonical
prefix. Plus successors always add their original block; minus successors add
it exactly when retained. At a nonzero limit, proper-prefix bounds determine
the whole cost, including when the retained positions have a last member.
-/

universe u
public noncomputable section
namespace Surreal
open Set Ordinal

/-- A native cutoff for an exponent also represents every canonical prefix cost. -/
theorem headOmegaCost_prefix_eq_reducedOmegaCost (H x C : Surreal.{u})
    (hC : ∀ w ∈ rightPrefixes x,
      (H.support ⊆ Ici w ∧
        (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) ↔ w ≤ C)
    {v : Surreal.{u}} (hv : birthdayTruncation x v.birthday = v) :
    headOmegaCost H v = reducedOmegaCost C v :=
  headOmegaCost_eq_reducedOmegaCost H v C
    (fun w hw ↦ hC w (rightPrefixes_subset_of_birthdayTruncation_eq hv hw))

/-- The empty exponent contributes only the initial monomial sign. -/
theorem headOmegaCost_exponent_zero (H : Surreal.{u}) : headOmegaCost H 0 = 1 := by
  obtain ⟨C, _, _, _, hC⟩ := exists_headOmegaCost_eq_reducedOmegaCost H 0
  rw [hC, reducedOmegaCost_zero]

/-- An appended exponent plus always contributes its full original expanded block. -/
theorem headOmegaCost_appendPlus (H x : Surreal.{u}) :
    headOmegaCost H (appendPlus x) = NatOrdinal.of
      ((headOmegaCost H x).val + (ω^ (plusCount x + 1)).val) := by
  obtain ⟨C, _, _, hC⟩ := exists_head_rightPrefix_retention_cutoff H (appendPlus x)
  rw [headOmegaCost_eq_reducedOmegaCost H _ C hC,
    headOmegaCost_prefix_eq_reducedOmegaCost H _ C hC (birthdayTruncation_appendPlus x),
    reducedOmegaCost_appendPlus]

/-- A retained appended exponent minus contributes its full original expanded block. -/
theorem headOmegaCost_appendMinus_of_retained {H x : Surreal.{u}}
    (hret : H.support ⊆ Ici x ∧
      (H.coeff x : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) :
    headOmegaCost H (appendMinus x) = NatOrdinal.of
      ((headOmegaCost H x).val + (ω^ (plusCount x + 1)).val) := by
  obtain ⟨C, _, _, hC⟩ := exists_head_rightPrefix_retention_cutoff H (appendMinus x)
  have hx : x ∈ rightPrefixes (appendMinus x) :=
    mem_rightPrefixes_iff.mpr ⟨birthdayTruncation_appendMinus x, appendMinus_lt x⟩
  rw [headOmegaCost_eq_reducedOmegaCost H _ C hC,
    headOmegaCost_prefix_eq_reducedOmegaCost H _ C hC (birthdayTruncation_appendMinus x),
    reducedOmegaCost_appendMinus_of_le ((hC x hx).mp hret)]

private theorem reducedOmegaCost_appendMinus_of_lt {C x : Surreal.{u}} (hC : C < x) :
    reducedOmegaCost C (appendMinus x) = reducedOmegaCost C x := by
  have hx : ∀ w ∈ rightPrefixes x, ¬ w ≤ C := by
    intro w hw hwC
    exact ((hC.trans (mem_rightPrefixes_iff.mp hw).2).not_ge hwC)
  have hm : ∀ w ∈ rightPrefixes (appendMinus x), ¬ w ≤ C := by
    intro w hw hwC
    rw [rightPrefixes_appendMinus] at hw
    rcases mem_insert_iff.mp hw with rfl | hw
    · exact hC.not_ge hwC
    · exact hx w hw hwC
  rw [reducedOmegaCost_eq_wpow_of_no_retained_rightPrefixes C _ hm,
    reducedOmegaCost_eq_wpow_of_no_retained_rightPrefixes C _ hx, plusCount_appendMinus]

/-- A deleted appended exponent minus contributes no additional cost. -/
theorem headOmegaCost_appendMinus_of_deleted {H x : Surreal.{u}}
    (hdel : ¬ (H.support ⊆ Ici x ∧
      (H.coeff x : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)) :
    headOmegaCost H (appendMinus x) = headOmegaCost H x := by
  obtain ⟨C, _, _, hC⟩ := exists_head_rightPrefix_retention_cutoff H (appendMinus x)
  have hx : x ∈ rightPrefixes (appendMinus x) :=
    mem_rightPrefixes_iff.mpr ⟨birthdayTruncation_appendMinus x, appendMinus_lt x⟩
  rw [headOmegaCost_eq_reducedOmegaCost H _ C hC,
    headOmegaCost_prefix_eq_reducedOmegaCost H _ C hC (birthdayTruncation_appendMinus x),
    reducedOmegaCost_appendMinus_of_lt (lt_of_not_ge (fun h ↦ hdel ((hC x hx).mpr h)))]

/-- Canonical exponent truncation cannot increase the native head cost. -/
theorem headOmegaCost_birthdayTruncation_le (H x : Surreal.{u}) {a : NatOrdinal.{u}}
    (ha : a ≤ x.birthday) : headOmegaCost H (birthdayTruncation x a) ≤ headOmegaCost H x := by
  obtain ⟨C, _, _, hC⟩ := exists_head_rightPrefix_retention_cutoff H x
  rw [headOmegaCost_eq_reducedOmegaCost H _ C hC,
    headOmegaCost_prefix_eq_reducedOmegaCost H _ C hC (by
      rw [birthday_birthdayTruncation x ha])]
  exact reducedOmegaCost_birthdayTruncation_le C x ha

private theorem reducedOmegaCost_birthdayTruncation_add_one_of_retained
    (C x : Surreal.{u}) {a : NatOrdinal.{u}} (ha : a + 1 ≤ x.birthday)
    (hr : birthdayTruncation x a < x ∨ birthdayTruncation x a ≤ C) :
    reducedOmegaCost C (birthdayTruncation x (a + 1)) = NatOrdinal.of
      ((reducedOmegaCost C (birthdayTruncation x a)).val +
        (ω^ (plusCount (birthdayTruncation x a) + 1)).val) := by
  have hal : a < x.birthday := (lt_add_one a).trans_le ha
  by_cases hl : birthdayTruncation x a < x
  · rw [birthdayTruncation_add_one_eq_appendPlus x ha hl, reducedOmegaCost_appendPlus]
  · have hne : birthdayTruncation x a ≠ x := by
      intro he
      have hb := birthday_birthdayTruncation x hal.le
      rw [he] at hb
      exact hal.ne hb.symm
    have hh : x < birthdayTruncation x a := lt_of_le_of_ne (le_of_not_gt hl) hne.symm
    rw [birthdayTruncation_add_one_eq_appendMinus x ha hh,
      reducedOmegaCost_appendMinus_of_le (hr.resolve_left hl)]

private theorem reducedOmegaCost_eq_prefix_add_block_of_max
    (C x : Surreal.{u}) (j : reducedOmegaPositions C x)
    (hmax : ∀ i : reducedOmegaPositions C x, i ≤ j) :
    reducedOmegaCost C x = NatOrdinal.of
      ((reducedOmegaCost C (birthdayTruncation x (NatOrdinal.of j.1.toOrd.1))).val +
        (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of j.1.toOrd.1)) + 1)).val) := by
  let : Unique (Ici j) :=
    { default := ⟨j, le_refl j⟩
      uniq := fun i ↦ Subtype.ext (le_antisymm (hmax i.1) i.2) }
  have hp (i : Ici j) :
      plusCount (birthdayTruncation x (NatOrdinal.of i.1.1.toOrd.1)) =
        plusCount (birthdayTruncation x (NatOrdinal.of j.1.toOrd.1)) := by
    have hi : i = ⟨j, le_refl j⟩ := Subsingleton.elim _ _
    rw [hi]
  have h := reducedOmegaCost_eq_prefix_add_mul_of_constant_plusCount C x j
    (plusCount (birthdayTruncation x (NatOrdinal.of j.1.toOrd.1))) hp
  simpa only [Ordinal.type_eq_one_of_unique, mul_one] using h

/-- At a nonzero exponent limit, all proper-prefix bounds determine a reduced cost. -/
theorem reducedOmegaCost_le_iff_of_isSuccLimit (C x : Surreal.{u})
    (hlim : Order.IsSuccLimit x.birthday.val) (M : NatOrdinal.{u}) :
    reducedOmegaCost C x ≤ M ↔
      ∀ a < x.birthday, reducedOmegaCost C (birthdayTruncation x a) ≤ M := by
  constructor
  · exact fun h a ha ↦ (reducedOmegaCost_birthdayTruncation_le C x ha.le).trans h
  · intro h
    have hpos : (0 : NatOrdinal.{u}) < x.birthday :=
      NatOrdinal.val.lt_iff_lt.mp (by simpa only [NatOrdinal.val_zero] using hlim.pos)
    have hM : 1 ≤ M := by
      simpa only [birthdayTruncation_zero, reducedOmegaCost_zero] using h 0 hpos
    by_cases hcof : ∀ i : reducedOmegaPositions C x,
        ∃ j : reducedOmegaPositions C x, i < j
    · apply reducedOmegaCost_le_of_cofinal_prefixes C x M hM
      intro i
      obtain ⟨j, hij⟩ := hcof i
      exact ⟨j, hij, h _ (NatOrdinal.of.strictMono j.1.toOrd.2)⟩
    · push Not at hcof
      obtain ⟨j, hj⟩ := hcof
      let a : NatOrdinal.{u} := NatOrdinal.of j.1.toOrd.1
      have ha : a + 1 < x.birthday := by
        apply NatOrdinal.val.lt_iff_lt.mp
        rw [NatOrdinal.val_add_one, NatOrdinal.val_of]
        exact hlim.succ_lt j.1.toOrd.2
      have he := reducedOmegaCost_birthdayTruncation_add_one_of_retained C x ha.le
        (mem_reducedOmegaPositions.mp j.2)
      calc
        reducedOmegaCost C x = NatOrdinal.of
            ((reducedOmegaCost C (birthdayTruncation x a)).val +
              (ω^ (plusCount (birthdayTruncation x a) + 1)).val) :=
          reducedOmegaCost_eq_prefix_add_block_of_max C x j hj
        _ = reducedOmegaCost C (birthdayTruncation x (a + 1)) := he.symm
        _ ≤ M := h _ ha

/-- At a nonzero exponent limit, all proper-prefix bounds determine a native head cost. -/
theorem headOmegaCost_le_iff_of_isSuccLimit (H x : Surreal.{u})
    (hlim : Order.IsSuccLimit x.birthday.val) (M : NatOrdinal.{u}) :
    headOmegaCost H x ≤ M ↔
      ∀ a < x.birthday, headOmegaCost H (birthdayTruncation x a) ≤ M := by
  obtain ⟨C, _, _, hC⟩ := exists_head_rightPrefix_retention_cutoff H x
  rw [headOmegaCost_eq_reducedOmegaCost H x C hC,
    reducedOmegaCost_le_iff_of_isSuccLimit C x hlim M]
  apply forall_congr'
  intro a
  apply forall_congr'
  intro ha
  rw [headOmegaCost_prefix_eq_reducedOmegaCost H x C hC (by
    rw [birthday_birthdayTruncation x ha.le])]

/-- Native head costs are continuous at every nonzero canonical-prefix limit. -/
theorem headOmegaCost_birthdayTruncation_limit (H x : Surreal.{u})
    {a : NatOrdinal.{u}} (ha : a ≤ x.birthday) (hlim : Order.IsSuccLimit a.val)
    (M : NatOrdinal.{u}) :
    headOmegaCost H (birthdayTruncation x a) ≤ M ↔
      ∀ b < a, headOmegaCost H (birthdayTruncation x b) ≤ M := by
  have hy : (birthdayTruncation x a).birthday = a := birthday_birthdayTruncation x ha
  rw [headOmegaCost_le_iff_of_isSuccLimit H _ (by simpa only [hy] using hlim), hy]
  apply forall_congr'
  intro b
  apply forall_congr'
  intro hb
  rw [birthdayTruncation_birthdayTruncation x hb.le ha]

/-- Every native head cost contains the full original plus-count baseline. -/
theorem wpow_plusCount_le_headOmegaCost (H x : Surreal.{u}) :
    ω^ plusCount x ≤ headOmegaCost H x := by
  obtain ⟨C, _, _, _, hC⟩ := exists_headOmegaCost_eq_reducedOmegaCost H x
  rw [hC]
  exact wpow_plusCount_le_reducedOmegaCost C x

/-- A retained canonical right prefix is followed by its full original minus block. -/
theorem headOmegaCost_add_block_le_of_mem_rightPrefixes {H s w : Surreal.{u}}
    (hw : w ∈ rightPrefixes s)
    (hret : H.support ⊆ Ici w ∧
      (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) :
    (headOmegaCost H w).val + (ω^ (plusCount w + 1)).val ≤
      (headOmegaCost H s).val := by
  have hb : w.birthday + 1 ≤ s.birthday :=
    Order.add_one_le_of_lt (birthday_lt_of_mem_rightPrefixes hw)
  have hstep := birthdayTruncation_add_one_eq_appendMinus s hb
    (by rw [(mem_rightPrefixes_iff.mp hw).1]; exact (mem_rightPrefixes_iff.mp hw).2)
  rw [(mem_rightPrefixes_iff.mp hw).1] at hstep
  have hcost := headOmegaCost_birthdayTruncation_le H s hb
  rw [hstep, headOmegaCost_appendMinus_of_retained hret] at hcost
  simpa only [NatOrdinal.val_of] using NatOrdinal.val.monotone hcost

end Surreal
