/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module
public import GonshorBirthday.Surreal.Birthday.SubseriesBirthday
import GonshorBirthday.Surreal.Birthday.Real
public import GonshorBirthday.Surreal.Birthday.Tests.SupportGap
import GonshorBirthday.Surreal.HahnSeries.NormalFormAdd

/-!
# Coefficient decrease, restored boundary, and limit-head clients
-/

universe u
public noncomputable section
open Surreal Set
namespace Tests

/-- The comparison includes complete cancellation to zero. -/
theorem coefficient_comparison_zero (x : Surreal.{u}) : (0 : Surreal).birthday ≤ x.birthday := by
  apply birthday_le_of_coeff_birthday_le
  intro s
  rw [coeff_zero, Pi.zero_apply, Real.toSurreal_zero, birthday_zero]
  exact zero_le

/-- Removing any set of terms, including all or none, cannot increase birthday. -/
theorem arbitrary_subseries_birthday (x : Surreal.{u}) (S : Set Surreal.{u}) :
    (subseries x S).birthday ≤ x.birthday := birthday_subseries_le x S

/-- A finite coefficient greater than one before a reciprocal term fits the old
nondyadic coefficient tail, even though it restores the reciprocal exponent minus. -/
theorem carried_finite_tail_before_reciprocal (r : ℝ)
    (hr : (r : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0) :
    (((2 : ℝ) : Surreal.{u}) + ω^ (-1 : Surreal)).birthday ≤
      ((r : Surreal.{u}) + ω^ (-1 : Surreal)).birthday := by
  apply birthday_le_of_coeff_birthday_le
  intro s
  rw [coeff_add, coeff_add, Pi.add_apply, Pi.add_apply, coeff_realCast, coeff_realCast,
    coeff_wpow]
  by_cases hs : s = 0
  · subst s
    have hn : (0 : Surreal.{u}) ≠ -1 := by simp
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne hn, add_zero]
    rw [hr]
    exact birthday_real_le_omega0 2
  · simp only [Pi.single_eq_of_ne hs, zero_add]
    exact le_rfl

/-- A completely deleted target at a source exponent after an infinite head still
satisfies the augmented-truncation comparison used by the support induction. -/
theorem zero_target_body_after_infinite_head :
    (ω^ (-(NatOrdinal.of Ordinal.omega0 : Surreal.{u}))).birthday ≤
      ((decreasingOrdinalSeries (Ordinal.omega0 + 1)).normalFormTrunc
          (-(NatOrdinal.of Ordinal.omega0 : Surreal)) +
        ω^ (-(NatOrdinal.of Ordinal.omega0 : Surreal))).birthday := by
  have h := birthday_trunc_add_wpow_le_of_coeff_birthday_le
    (x := decreasingOrdinalSeries (Ordinal.omega0 + 1)) (y := (0 : Surreal.{u}))
    (fun s ↦ by
      rw [coeff_zero, Pi.zero_apply, Real.toSurreal_zero, birthday_zero]
      exact zero_le)
    (-(NatOrdinal.of Ordinal.omega0 : Surreal)) ?_
  · simpa only [trunc_zero, zero_add] using h
  rw [support_decreasingOrdinalSeries]
  exact ⟨⟨Ordinal.omega0, show Ordinal.omega0 < Ordinal.omega0 + 1 from lt_add_one _⟩, rfl⟩

end Tests
