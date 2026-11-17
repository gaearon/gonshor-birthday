/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.CoefficientCofinality
public import GonshorBirthday.Surreal.Birthday.Minus

import GonshorBirthday.Surreal.Birthday.CoefficientRun
import GonshorBirthday.Surreal.Birthday.HeadCoefficientWord
import GonshorBirthday.Surreal.Birthday.Real

/-!
# Real coefficient word birthdays under monomial scaling

The single-monomial formulas specialize the corresponding formulas for a normal-form
head to the empty head. Successive coefficient birthdays then differ by one block.
-/

universe u
public noncomputable section
namespace Surreal
open Set IGame

/-- Bounding all older coefficient-prefix stages bounds the full positive monomial birthday. -/
theorem birthday_real_mul_wpow_le_of_prefixes {r : ℝ} (hr : 0 < r)
    (x : Surreal.{u}) (M : NatOrdinal.{u}) (hA : (ω^ x).birthday ≤ M)
    (hcoeff : ∀ s : ℝ, 0 < s →
      ((s : Surreal.{u}) ∈ leftPrefixes (r : Surreal) ∨
        (s : Surreal.{u}) ∈ rightPrefixes (r : Surreal)) →
      ∀ a ∈ leftPrefixes (ω^ x), NatOrdinal.of
        (((s : Surreal) * ω^ x).birthday.val + (plusCount a).val) < M) :
    ((r : Surreal) * ω^ x).birthday ≤ M := by
  simpa only [zero_add] using birthday_head_real_mul_wpow_le_of_prefixes
    (0 : Surreal.{u}) x (by simp) hr M (by simpa only [zero_add] using hA)
    (by simpa only [zero_add] using hcoeff)

/-- A positive finite real coefficient repeats one pure-power block per sign after its first. -/
theorem birthday_real_mul_wpow_of_birthday_nat {r : ℝ} (hr : 0 < r) {n : ℕ}
    (hb : (r : Surreal.{u}).birthday = ((n + 1 : ℕ) : NatOrdinal.{u})) (x : Surreal.{u}) :
    ((r : Surreal) * ω^ x).birthday = NatOrdinal.of
      ((ω^ x).birthday.val + (ω^ plusCount x).val * (n : Ordinal)) := by
  simpa only [zero_add] using
    birthday_head_real_mul_wpow_of_birthday_nat (0 : Surreal.{u}) x (by simp) hr hb

/-- A positive real of infinite birthday has an omega sequence of complete coefficient blocks. -/
theorem birthday_real_mul_wpow_of_birthday_omega0 {r : ℝ} (hr : 0 < r)
    (hb : (r : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0) (x : Surreal.{u}) :
    ((r : Surreal) * ω^ x).birthday = NatOrdinal.of
      ((ω^ x).birthday.val + (ω^ plusCount x).val * Ordinal.omega0) := by
  simpa only [zero_add] using
    birthday_head_real_mul_wpow_of_birthday_omega0 (0 : Surreal.{u}) x (by simp) hr hb

/-- The exact birthday of every positive real coefficient monomial. -/
theorem birthday_real_mul_wpow {r : ℝ} (hr : 0 < r) (x : Surreal.{u}) :
    ((r : Surreal) * ω^ x).birthday = NatOrdinal.of
      ((ω^ x).birthday.val + (ω^ plusCount x).val * ((r : Surreal.{u}).birthday.val - 1)) := by
  simpa only [zero_add] using birthday_head_real_mul_wpow (0 : Surreal.{u}) x (by simp) hr

/-- The exact birthday of every nonzero real coefficient monomial, of either sign. -/
theorem birthday_real_mul_wpow_of_ne_zero {r : ℝ} (hr : r ≠ 0) (x : Surreal.{u}) :
    ((r : Surreal) * ω^ x).birthday = NatOrdinal.of
      ((ω^ x).birthday.val + (ω^ plusCount x).val * ((r : Surreal.{u}).birthday.val - 1)) := by
  obtain hrn | hrp := lt_or_gt_of_ne hr
  · have ht := birthday_real_mul_wpow (r := -r) (neg_pos.mpr hrn) x
    simpa only [Real.toSurreal_neg, neg_mul, birthday_neg] using ht
  · exact birthday_real_mul_wpow hrp x

/-- A proper positive real coefficient prefix costs at least one complete monomial block. -/
theorem oadd_wpow_plusCount_le_birthday_real_mul_wpow {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hne : r ≠ s)
    (hp : birthdayTruncation (s : Surreal.{u}) (r : Surreal).birthday = (r : Surreal))
    (x : Surreal.{u}) : NatOrdinal.of
      (((r : Surreal) * ω^ x).birthday.val + (ω^ plusCount x).val) ≤
        ((s : Surreal) * ω^ x).birthday := by
  have hlt : (r : Surreal.{u}).birthday < (s : Surreal.{u}).birthday := by
    obtain h | h := lt_or_gt_of_ne hne
    · exact birthday_lt_of_mem_leftPrefixes (mem_leftPrefixes_iff.mpr
        ⟨hp, Real.toSurreal_lt_iff.mpr h⟩)
    · exact birthday_lt_of_mem_rightPrefixes (mem_rightPrefixes_iff.mpr
        ⟨hp, Real.toSurreal_lt_iff.mpr h⟩)
  have hr1 : 1 ≤ (r : Surreal.{u}).birthday.val := NatOrdinal.val.monotone
    (one_le_birthday_real hr.ne')
  have htail : (r : Surreal.{u}).birthday.val - 1 < (s : Surreal.{u}).birthday.val - 1 := by
    rw [Ordinal.lt_sub, Ordinal.add_sub_cancel_of_le hr1]
    exact NatOrdinal.val.strictMono hlt
  rw [birthday_real_mul_wpow hr, birthday_real_mul_wpow hs, NatOrdinal.val_of,
    add_assoc, ← mul_add_one]
  exact NatOrdinal.of.monotone (add_le_add_right
    (mul_le_mul_right (Order.add_one_le_of_lt htail) _) _)

/-- Adjacent positive real coefficient birthdays differ by exactly one monomial block. -/
theorem birthday_real_mul_wpow_of_birthday_add_one {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hb : (s : Surreal.{u}).birthday = (r : Surreal).birthday + 1) (x : Surreal.{u}) :
    ((s : Surreal) * ω^ x).birthday =
      NatOrdinal.of (((r : Surreal) * ω^ x).birthday.val + (ω^ plusCount x).val) := by
  have hr1 : 1 ≤ (r : Surreal.{u}).birthday.val := NatOrdinal.val.monotone
    (one_le_birthday_real hr.ne')
  have htail : (s : Surreal.{u}).birthday.val - 1 = (r : Surreal.{u}).birthday.val - 1 + 1 := by
    apply Ordinal.sub_eq_of_add_eq
    rw [← add_assoc, Ordinal.add_sub_cancel_of_le hr1, hb, NatOrdinal.val_add_one]
  rw [birthday_real_mul_wpow hs, birthday_real_mul_wpow hr, NatOrdinal.val_of, htail,
    mul_add_one, add_assoc]

/-- One plus coefficient sign appends exactly one pure-power block after monomial scaling. -/
theorem real_mul_wpow_eq_appendPluses_of_coefficient_prefix {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r < s)
    (hp : birthdayTruncation (s : Surreal.{u}) (r : Surreal).birthday = (r : Surreal))
    (hb : (s : Surreal.{u}).birthday = (r : Surreal).birthday + 1) (x : Surreal.{u}) :
    (s : Surreal) * ω^ x = appendPluses ((r : Surreal) * ω^ x) (ω^ plusCount x).val := by
  have _ := hs
  have h := eq_appendPlus_of_birthdayTruncation_eq hp hb (Real.toSurreal_lt_iff.mpr hrs)
  simpa only [zero_add] using
    (appendPluses_head_real_mul_wpow_of_appendPlus (0 : Surreal.{u}) x (by simp) hr.ne' h).symm

/-- One minus coefficient sign appends exactly one pure-power block after monomial scaling. -/
theorem real_mul_wpow_eq_appendMinuses_of_coefficient_prefix {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hsr : s < r)
    (hp : birthdayTruncation (s : Surreal.{u}) (r : Surreal).birthday = (r : Surreal))
    (hb : (s : Surreal.{u}).birthday = (r : Surreal).birthday + 1) (x : Surreal.{u}) :
    (s : Surreal) * ω^ x = appendMinuses ((r : Surreal) * ω^ x) (ω^ plusCount x).val := by
  have _ := hs
  have h := eq_appendMinus_of_birthdayTruncation_eq hp hb (Real.toSurreal_lt_iff.mpr hsr)
  simpa only [zero_add] using
    (appendMinuses_head_real_mul_wpow_of_appendMinus (0 : Surreal.{u}) x (by simp) hr.ne' h).symm

end Surreal
