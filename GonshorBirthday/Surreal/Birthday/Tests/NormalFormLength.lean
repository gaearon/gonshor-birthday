/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.NormalFormLength
public import GonshorBirthday.Surreal.Birthday.Tests.SupportGap

import GonshorBirthday.NatOrdinal.OrderedSumPosition
import GonshorBirthday.Surreal.Birthday.Tests.HeadOmegaLength

/-!
# Native normal-form birthday decomposition clients

The negative-ordinal series tests coverage of actual arbitrary support lengths.
The two-term series one plus reciprocal omega separates ordinary concatenation
from natural addition. The empty series has no initial-unit contribution.
-/

universe u
public noncomputable section
open Surreal Set
open scoped Ordinal
namespace Tests

/-- The birthday intervals cover every position of the genuine negative-ordinal series. -/
theorem decreasingOrdinalSeries_birthday_intervals (Λ : Ordinal.{u})
    {a : NatOrdinal.{u}} (ha : a < (decreasingOrdinalSeries Λ).birthday) :
    ∃ i : Iio Λ,
      ((decreasingOrdinalSeries Λ).normalFormTrunc
        (-(NatOrdinal.of i.val : Surreal))).birthday ≤ a ∧
        a < ((decreasingOrdinalSeries Λ).normalFormTrunc (-(NatOrdinal.of i.val : Surreal)) +
          ((decreasingOrdinalSeries Λ).coeff (-(NatOrdinal.of i.val : Surreal)) : Surreal) *
            ω^ (-(NatOrdinal.of i.val : Surreal))).birthday := by
  obtain ⟨s, hs, hleft, hright⟩ := exists_normalForm_birthday_interval ha
  rw [support_decreasingOrdinalSeries] at hs
  obtain ⟨i, rfl⟩ := hs
  exact ⟨i, hleft, hright⟩

/-- Empty support contributes exactly zero to the ordered term-cost sum. -/
theorem normalForm_cost_sum_zero :
    NatOrdinal.of (typeLT (Σₗ i : (0 : Surreal.{u}).toHahnSeries.length.ToType,
      (headCoefficientCost ((0 : Surreal).normalFormTrunc ((0 : Surreal).toHahnSeries.exp i.toOrd))
        ((0 : Surreal).toHahnSeries.exp i.toOrd)
        ((0 : Surreal).coeff ((0 : Surreal).toHahnSeries.exp i.toOrd))).val.ToType)) = 0 := by
  simpa only [birthday_zero] using (birthday_eq_ordered_term_costs (0 : Surreal.{u})).symm

/-- The actual two-term sum has ordered cost omega, strictly below its natural-sum budget. -/
theorem normalForm_cost_sum_one_add_reciprocal :
    let x : Surreal.{u} := 1 + ω^ (-1 : Surreal)
    let C := NatOrdinal.of (typeLT (Σₗ i : x.toHahnSeries.length.ToType,
      (headCoefficientCost (x.normalFormTrunc (x.toHahnSeries.exp i.toOrd))
        (x.toHahnSeries.exp i.toOrd) (x.coeff (x.toHahnSeries.exp i.toOrd))).val.ToType))
    C = NatOrdinal.of Ordinal.omega0 ∧ C < 1 + NatOrdinal.of Ordinal.omega0 := by
  dsimp only
  have hfin : ((1 : ℝ) : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 := by
    rw [Real.toSurreal_one, birthday_one]
    apply NatOrdinal.val.lt_iff_lt.mp
    simpa only [Nat.cast_one, NatOrdinal.val_one, NatOrdinal.val_of] using
      (Ordinal.natCast_lt_omega0 1 : (1 : ℕ) < Ordinal.omega0)
  have hb := finite_real_head_reciprocal_birthday (1 : ℝ) hfin
  rw [Real.toSurreal_one] at hb
  have he := (birthday_eq_ordered_term_costs (1 + ω^ (-1 : Surreal.{u}))).symm.trans hb
  refine ⟨he, ?_⟩
  rw [he, add_comm]
  exact lt_add_one _

end Tests
