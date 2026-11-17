/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadAllDeleted

/-!
# Full deletion word clients

A nondyadic real followed by the reciprocal omega gains exactly one plus sign,
rather than the original reciprocal omega's omega-length sign word.
-/

universe u
public noncomputable section
open Surreal Set
namespace Tests

/-- All deleted exponent minuses give an exact actual birthday, not merely a budget. -/
theorem all_deleted_exact_birthday {H s : Surreal.{u}} (hH : H.support ⊆ Ioi s)
    (hdel : ∀ w ∈ rightPrefixes s, ¬ (H.support ⊆ Ici w ∧
      (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)) :
    (H + ω^ s).birthday = NatOrdinal.of (H.birthday.val + (ω^ (plusCount s)).val) := by
  rw [← appendPluses_head_add_wpow_of_no_retained_rightPrefix hH hdel,
    birthday_appendPluses]

/-- At a nondyadic real, the whole original reciprocal-omega minus block is deleted. -/
theorem nondyadic_real_add_reciprocal_wpow (r : ℝ)
    (hr : (r : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0) :
    (r : Surreal.{u}) + ω^ (-1 : Surreal) = appendPlus (r : Surreal.{u}) := by
  have hH : (r : Surreal.{u}).support ⊆ Ioi (-1 : Surreal) := by
    intro v hv
    by_cases hv0 : v = 0
    · rw [hv0]
      exact neg_lt_zero.mpr (zero_lt_one : (0 : Surreal.{u}) < 1)
    · have hc : (r : Surreal.{u}).coeff v = 0 := by
        simp [coeff_realCast, hv0]
      exact (mem_support_iff.mp hv hc).elim
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
  have h := appendPluses_head_add_wpow_of_no_retained_rightPrefix hH hdel
  have hp : plusCount (-1 : Surreal.{u}) = 0 := by
    simpa only [NatOrdinal.toSurreal_one] using plusCount_neg_toSurreal (1 : NatOrdinal.{u})
  rw [hp, NatOrdinal.wpow_zero, NatOrdinal.val_one, appendPluses_one] at h
  exact h.symm

end Tests
