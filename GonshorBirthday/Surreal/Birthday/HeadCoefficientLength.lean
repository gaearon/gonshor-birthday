/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadCoefficientCost
public import GonshorBirthday.Surreal.Birthday.HeadOmegaLength
public import GonshorBirthday.Surreal.Birthday.HeadCoefficientWord

import GonshorBirthday.Surreal.Birthday.HeadRun

/-!
# Exact birthday increments of normal-form terms

Appending any real multiple of a monomial below an arbitrary higher head adds
its complete native term cost by ordinary ordinal addition. Zero coefficients,
both signs, and nondyadic coefficients are included.
-/

universe u
public noncomputable section
namespace Surreal
open Set

/-- A lower real-coefficient term adds exactly its native cost to the head birthday. -/
theorem birthday_head_real_mul_wpow_eq_headCoefficientCost
    (H s : Surreal.{u}) (hH : H.support ⊆ Ioi s) (r : ℝ) :
    (H + (r : Surreal) * ω^ s).birthday =
      NatOrdinal.of (H.birthday.val + (headCoefficientCost H s r).val) := by
  by_cases hr : r = 0
  · rw [hr, Real.toSurreal_zero, zero_mul, add_zero, headCoefficientCost_zero,
      NatOrdinal.val_zero, add_zero, NatOrdinal.of_val]
  rw [headCoefficientCost_of_ne_zero H s hr, NatOrdinal.val_of, ← add_assoc]
  rcases lt_or_gt_of_ne hr with hneg | hpos
  · have hHn : (-H).support ⊆ Ioi s := by simpa only [support_neg] using hH
    have h := birthday_head_real_mul_wpow (-H) s hHn (neg_pos.mpr hneg)
    have he : -H + ((-r : ℝ) : Surreal) * ω^ s = -(H + (r : Surreal) * ω^ s) := by
      rw [Real.toSurreal_neg]
      ring
    rw [he, birthday_neg, birthday_head_wpow (-H) s hHn, birthday_neg,
      headOmegaCost_neg, NatOrdinal.val_of, Real.toSurreal_neg, birthday_neg] at h
    exact h
  · rw [birthday_head_real_mul_wpow H s hH hpos, birthday_head_wpow H s hH,
      NatOrdinal.val_of]

/-- Completing a normal-form truncation adds exactly the cost of its boundary term. -/
theorem birthday_trunc_add_coeff_mul_wpow (x s : Surreal.{u}) :
    (x.normalFormTrunc s + (x.coeff s : Surreal) * ω^ s).birthday =
      NatOrdinal.of ((x.normalFormTrunc s).birthday.val +
        (headCoefficientCost (x.normalFormTrunc s) s (x.coeff s)).val) := by
  apply birthday_head_real_mul_wpow_eq_headCoefficientCost
  rw [support_trunc]
  exact inter_subset_right

private theorem finite_tail_absorb (s : Surreal.{u}) {r : ℝ}
    (hr : (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) :
    (((ω^ plusCount s).val * ((r : Surreal.{u}).birthday.val - 1) +
      (ω^ plusCount s).val) + (ω^ plusCount s).val * Ordinal.omega0) =
      (ω^ plusCount s).val * Ordinal.omega0 := by
  have ht : (r : Surreal.{u}).birthday.val - 1 < Ordinal.omega0 :=
    (Ordinal.sub_le_self _ _).trans_lt (NatOrdinal.val.strictMono hr)
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp ht
  rw [hn]
  calc
    _ = (ω^ plusCount s).val * ((n : Ordinal) + 1 + Ordinal.omega0) := by
      simp only [mul_add, mul_one, add_assoc]
    _ = _ := by rw [add_assoc, Ordinal.one_add_omega0, Ordinal.natCast_add_omega0]

private theorem block_val (s : Surreal.{u}) :
    (ω^ (plusCount s + 1)).val = (ω^ plusCount s).val * Ordinal.omega0 := by
  rw [NatOrdinal.val_wpow, NatOrdinal.val_add_one, Ordinal.opow_add, Ordinal.opow_one]
  rfl

/-- Completing a finite nonzero coefficient before its boundary minus block
preserves the length of that block after the initial monomial. -/
theorem birthday_head_real_mul_wpow_add_block (H s : Surreal.{u})
    (hH : H.support ⊆ Ioi s) {r : ℝ} (hr : r ≠ 0)
    (hf : (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) :
    (H + (r : Surreal) * ω^ s).birthday.val +
      (headOmegaCost (H + (r : Surreal) * ω^ s) s).val +
      (ω^ (plusCount s + 1)).val =
    (H.birthday.val + (headOmegaCost H s).val) +
      (ω^ (plusCount s + 1)).val := by
  have hs := mem_support_head_real_mul_wpow H s hH hr
  rw [birthday_head_real_mul_wpow_eq_headCoefficientCost H s hH r,
    NatOrdinal.val_of, headCoefficientCost_of_ne_zero H s hr, NatOrdinal.val_of,
    headOmegaCost_eq_wpow_of_mem_support hs, block_val]
  simp only [add_assoc]
  rw [← add_assoc ((ω^ plusCount s).val * _) ((ω^ plusCount s).val),
    finite_tail_absorb s hf]

end Surreal
