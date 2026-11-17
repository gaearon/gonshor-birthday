/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.NormalFormLimit
public import GonshorBirthday.Surreal.Birthday.Tests.SupportGap

/-!
# Limit-support birthday clients

The negative-ordinal series tests arbitrary genuine limit supports. The zero
case is included, while the single-term series one shows why a last term must
be excluded from the proper-truncation criterion.
-/

universe u
public noncomputable section
open Surreal Set
namespace Tests

/-- On an actual infinite normal form, proper truncations determine every birthday bound. -/
theorem decreasingOrdinalSeries_birthday_le_iff {Λ : Ordinal.{u}}
    (hΛ : Order.IsSuccLimit Λ) (B : NatOrdinal.{u}) :
    (decreasingOrdinalSeries Λ).birthday ≤ B ↔
      ∀ i : Iio Λ,
        ((decreasingOrdinalSeries Λ).normalFormTrunc
          (-(NatOrdinal.of i.val : Surreal))).birthday ≤ B := by
  rw [birthday_le_iff_trunc_of_no_min_support _ (decreasingOrdinalSeries_no_min hΛ),
    support_decreasingOrdinalSeries]
  simp only [forall_mem_range]

/-- The empty normal form satisfies the same limit criterion. -/
theorem zero_birthday_limit_criterion (B : NatOrdinal.{u}) :
    (0 : Surreal.{u}).birthday ≤ B ↔
      ∀ s ∈ (0 : Surreal.{u}).support, ((0 : Surreal).normalFormTrunc s).birthday ≤ B := by
  apply birthday_le_iff_trunc_of_no_min_support
  simp only [support_zero, mem_empty_iff_false, false_implies, forall_const]

/-- A successor support can have only zero proper truncations despite a positive birthday. -/
theorem one_separates_successor_support :
    (∀ s ∈ (1 : Surreal.{u}).support, ((1 : Surreal).normalFormTrunc s).birthday = 0) ∧
      (1 : Surreal.{u}).birthday = 1 := by
  refine ⟨?_, birthday_one⟩
  intro s hs
  have hs0 : s = 0 := by
    by_contra hn
    apply mem_support_iff.mp hs
    simp only [coeff_one, Pi.single_eq_of_ne hn]
  subst s
  have hz : (1 : Surreal.{u}).normalFormTrunc 0 = 0 := by
    apply toHahnSeries_inj.mp
    rw [toHahnSeries_trunc, toHahnSeries_one,
      SurrealHahnSeries.trunc_single_of_ge le_rfl, toHahnSeries_zero]
  rw [hz, birthday_zero]

end Tests
