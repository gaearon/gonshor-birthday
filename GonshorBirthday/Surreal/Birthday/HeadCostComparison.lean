/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadCost
public import GonshorBirthday.Surreal.Birthday.PlusCount
public import GonshorBirthday.Surreal.Birthday.Prefix

import GonshorBirthday.Surreal.Birthday.HeadCostPrefix

/-!
# Comparing head costs by the prefixes ending at restored blocks

A changed head can restore a minus block. It suffices to bound the entire
prefix ending at each such block by the available initial ordinal allowance.
The proof follows canonical exponent prefixes, including all limit stages.
-/

universe u
public noncomputable section
namespace Surreal
open Set

private theorem headOmegaCost_shifted_limit_bound (H t : Surreal.{u})
    (hlim : Order.IsSuccLimit t.birthday.val) (A M : Ordinal.{u}) (hAM : A ≤ M)
    (h : ∀ a < t.birthday,
      A + (headOmegaCost H (birthdayTruncation t a)).val ≤ M) :
    A + (headOmegaCost H t).val ≤ M := by
  apply (Ordinal.le_sub_of_le hAM).mp
  have hh : headOmegaCost H t ≤ NatOrdinal.of (M - A) := by
    apply (headOmegaCost_le_iff_of_isSuccLimit H t hlim _).mpr
    intro a ha
    apply NatOrdinal.val.le_iff_le.mp
    rw [NatOrdinal.val_of]
    exact (Ordinal.le_sub_of_le hAM).mpr (h a ha)
  simpa only [NatOrdinal.val_of] using NatOrdinal.val.monotone hh

/-- A bound for every prefix ending in a restored minus block controls the
whole head cost, even when restored blocks occur cofinally. -/
theorem headOmegaCost_add_le_add_of_restored_prefixes
    (H K t : Surreal.{u}) (A B : Ordinal.{u}) (hAB : A ≤ B)
    (hrest : ∀ w ∈ rightPrefixes t,
      (H.support ⊆ Ici w ∧
        (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) →
      ¬ (K.support ⊆ Ici w ∧
        (K.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) →
      A + (headOmegaCost H w).val + (ω^ (plusCount w + 1)).val ≤ B) :
    A + (headOmegaCost H t).val ≤ B + (headOmegaCost K t).val := by
  classical
  have aux : ∀ a : Ordinal.{u}, ∀ t : Surreal.{u}, t.birthday = NatOrdinal.of a →
      (∀ w ∈ rightPrefixes t,
        (H.support ⊆ Ici w ∧
          (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) →
        ¬ (K.support ⊆ Ici w ∧
          (K.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) →
        A + (headOmegaCost H w).val + (ω^ (plusCount w + 1)).val ≤ B) →
      A + (headOmegaCost H t).val ≤ B + (headOmegaCost K t).val := by
    intro a
    induction a using Ordinal.limitRecOn with
    | zero =>
      intro t ht _
      have ht0 : t = 0 := birthday_eq_zero.mp (by simpa only [NatOrdinal.of_zero] using ht)
      subst t
      rw [headOmegaCost_exponent_zero, headOmegaCost_exponent_zero]
      exact _root_.add_le_add_left hAB _
    | add_one a ih =>
      intro t ht hr
      let w := birthdayTruncation t (NatOrdinal.of a)
      have ha : NatOrdinal.of a < t.birthday := by
        rw [ht, NatOrdinal.of_add_one]
        exact lt_add_one _
      have hw : w.birthday = NatOrdinal.of a := birthday_birthdayTruncation t ha.le
      have hwt : birthdayTruncation t w.birthday = w := by rw [hw]
      have hip := ih w hw (fun z hz ↦ hr z
        (rightPrefixes_subset_of_birthdayTruncation_eq hwt hz))
      have hne : w ≠ t := fun he ↦ ha.ne (hw.symm.trans (congrArg birthday he))
      by_cases hl : w < t
      · have he : t = appendPlus w := by
          have hh := birthdayTruncation_add_one_eq_appendPlus t (by
            rw [ht, NatOrdinal.of_add_one]) hl
          simpa only [← ht, ← NatOrdinal.of_add_one, birthdayTruncation_birthday] using hh
        rw [he, headOmegaCost_appendPlus, headOmegaCost_appendPlus,
          NatOrdinal.val_of, NatOrdinal.val_of, ← add_assoc, ← add_assoc]
        exact _root_.add_le_add_left hip _
      · have hrw : t < w := lt_of_le_of_ne (le_of_not_gt hl) hne.symm
        have he : t = appendMinus w := by
          have hh := birthdayTruncation_add_one_eq_appendMinus t (by
            rw [ht, NatOrdinal.of_add_one]) hrw
          simpa only [← ht, ← NatOrdinal.of_add_one, birthdayTruncation_birthday] using hh
        have hwr : w ∈ rightPrefixes t := mem_rightPrefixes_iff.mpr ⟨hwt, hrw⟩
        by_cases hH : H.support ⊆ Ici w ∧
            (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0
        · by_cases hK : K.support ⊆ Ici w ∧
              (K.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0
          · rw [he, headOmegaCost_appendMinus_of_retained hH,
              headOmegaCost_appendMinus_of_retained hK, NatOrdinal.val_of,
              NatOrdinal.val_of, ← add_assoc, ← add_assoc]
            exact _root_.add_le_add_left hip _
          · calc
              A + (headOmegaCost H t).val =
                  A + (headOmegaCost H w).val + (ω^ (plusCount w + 1)).val := by
                rw [he, headOmegaCost_appendMinus_of_retained hH, NatOrdinal.val_of,
                  add_assoc]
              _ ≤ B := hr w hwr hH hK
              _ ≤ _ := le_self_add
        · calc
              A + (headOmegaCost H t).val = A + (headOmegaCost H w).val := by
                rw [he, headOmegaCost_appendMinus_of_deleted hH]
              _ ≤ B + (headOmegaCost K w).val := hip
              _ ≤ B + (headOmegaCost K t).val := by
                apply (Ordinal.isNormal_add_right B).monotone
                apply NatOrdinal.val.monotone
                have hm := headOmegaCost_birthdayTruncation_le K t
                  (show w.birthday ≤ t.birthday by rw [hw]; exact ha.le)
                rwa [hwt] at hm
    | limit a hlim ih =>
      intro t ht hr
      apply headOmegaCost_shifted_limit_bound H t
        (by simpa only [ht, NatOrdinal.val_of] using hlim)
        A (B + (headOmegaCost K t).val) (hAB.trans le_self_add)
      intro b hb
      have hba : b.val < a := by
        simpa only [ht, NatOrdinal.val_of] using NatOrdinal.val.strictMono hb
      have hp : birthdayTruncation t (birthdayTruncation t b).birthday =
          birthdayTruncation t b := by rw [birthday_birthdayTruncation t hb.le]
      exact (ih b.val hba (birthdayTruncation t b)
        (by rw [birthday_birthdayTruncation t hb.le, NatOrdinal.of_val])
        (fun w hw ↦ hr w (rightPrefixes_subset_of_birthdayTruncation_eq hp hw))).trans
          ((Ordinal.isNormal_add_right B).monotone (NatOrdinal.val.monotone
            (headOmegaCost_birthdayTruncation_le K t hb.le)))
  exact aux t.birthday.val t (NatOrdinal.of_val t.birthday).symm hrest

end Surreal
