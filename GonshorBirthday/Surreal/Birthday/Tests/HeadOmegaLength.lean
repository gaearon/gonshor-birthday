/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadOmegaLength
import GonshorBirthday.Surreal.Birthday.HeadCostPrefix
import GonshorBirthday.Surreal.Birthday.OmegaBlock

/-!
# Exact arbitrary-head monomial birthday clients

At a dyadic real head the reciprocal-omega block has full omega length. At a
nondyadic real head it has length one, giving birthday omega+1. These distinguish
native history deletion from both an undeleted word and deletion of every minus.
-/

universe u
public section
open Surreal Set
namespace Tests

private theorem support_real_ge_zero (r : ℝ) :
    (r : Surreal.{u}).support ⊆ Ici (0 : Surreal) := by
  intro v hv
  by_cases hv0 : v = 0
  · rw [hv0]
    exact le_rfl
  · have hc : (r : Surreal.{u}).coeff v = 0 := by simp [coeff_realCast, hv0]
    exact (mem_support_iff.mp hv hc).elim

private theorem support_real_gt_neg_one (r : ℝ) :
    (r : Surreal.{u}).support ⊆ Ioi (-1 : Surreal) := by
  intro v hv
  exact mem_Ioi.mpr ((neg_lt_zero.mpr (zero_lt_one : (0 : Surreal.{u}) < 1)).trans_le
    (mem_Ici.mp (support_real_ge_zero r hv)))

private theorem neg_one_eq_appendMinus_zero :
    (-1 : Surreal.{u}) = appendMinus (0 : Surreal) := by
  apply eq_appendMinus_of_birthdayTruncation_eq
  · simp only [birthday_zero, birthdayTruncation_zero]
  · simp only [birthday_neg, birthday_one, birthday_zero, zero_add]
  · exact neg_lt_zero.mpr (zero_lt_one : (0 : Surreal.{u}) < 1)

/-- Every finite-birthday real head retains the reciprocal monomial's full omega block. -/
theorem finite_real_head_reciprocal_birthday (r : ℝ)
    (hf : (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) :
    ((r : Surreal.{u}) + ω^ (-1 : Surreal)).birthday = NatOrdinal.of Ordinal.omega0 := by
  have hret : (r : Surreal.{u}).support ⊆ Ici (0 : Surreal) ∧
      ((r : Surreal.{u}).coeff 0 : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 :=
    ⟨support_real_ge_zero r, by simpa only [coeff_realCast, Pi.single_eq_same] using hf⟩
  have hc : headOmegaCost (r : Surreal.{u}) (-1 : Surreal) =
      NatOrdinal.of Ordinal.omega0 := by
    rw [neg_one_eq_appendMinus_zero, headOmegaCost_appendMinus_of_retained hret,
      headOmegaCost_exponent_zero]
    simp only [plusCount_zero, zero_add, NatOrdinal.val_one, NatOrdinal.val_wpow,
      Ordinal.opow_one, Ordinal.one_add_omega0]
  rw [birthday_head_wpow _ _ (support_real_gt_neg_one r), hc, NatOrdinal.val_of]
  congr 1
  exact Ordinal.add_omega0 (NatOrdinal.val.strictMono hf)

/-- A nondyadic real head deletes that whole minus block, leaving one new plus sign. -/
theorem nondyadic_real_head_reciprocal_birthday (r : ℝ)
    (hr : (r : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0) :
    ((r : Surreal.{u}) + ω^ (-1 : Surreal)).birthday =
      NatOrdinal.of (Ordinal.omega0 + 1) := by
  have hdel : ∀ w ∈ rightPrefixes (-1 : Surreal.{u}),
      ¬ ((r : Surreal).support ⊆ Ici w ∧
        ((r : Surreal).coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) := by
    intro w hw
    have hb := birthday_lt_of_mem_rightPrefixes hw
    rw [birthday_neg, birthday_one] at hb
    have hbw : w.birthday ≤ 0 := Order.lt_add_one_iff.mp (by simpa only [zero_add] using hb)
    have hw0 : w = 0 := birthday_eq_zero.mp (le_antisymm hbw zero_le)
    rw [hw0, coeff_realCast, Pi.single_eq_same, hr]
    exact fun h ↦ h.2.false
  have hp : plusCount (-1 : Surreal.{u}) = 0 := by
    simpa only [NatOrdinal.toSurreal_one] using plusCount_neg_toSurreal (1 : NatOrdinal.{u})
  rw [birthday_head_wpow _ _ (support_real_gt_neg_one r),
    headOmegaCost_eq_wpow_of_no_retained_rightPrefix _ _ hdel, hp,
    NatOrdinal.wpow_zero, NatOrdinal.val_one, hr, NatOrdinal.val_of]

end Tests
