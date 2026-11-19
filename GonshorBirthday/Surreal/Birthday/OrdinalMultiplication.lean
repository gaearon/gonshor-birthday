/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.HahnSeries.Transfer
import GonshorBirthday.Surreal.Birthday.ProductGrid
public import GonshorBirthday.Surreal.Birthday.OrdinalTranslation
import GonshorBirthday.Surreal.Birthday.ReducedCostEndpoint
import GonshorBirthday.NatOrdinal.FiniteBlocks
import GonshorBirthday.Surreal.HahnSeries.NormalFormAdd

/-!
# Multiplication by an ordinal

If the exponents in one factor are ordinals, the estimate for each term follows from
translation by an ordinal. In particular this proves the birthday bound for one ordinal
factor. Cantor normal form gives the support condition in that case.
-/

universe u
public noncomputable section
namespace Surreal

/-- The birthday bound when all exponents of the second factor are ordinals. -/
theorem birthday_mul_le_of_ordinal_exponents (x y : Surreal.{u})
    (hy : y.support ⊆ Set.range NatOrdinal.toSurreal) :
    (x * y).birthday ≤ x.birthday * y.birthday := by
  apply birthday_mul_le_of_exponent_bounds
  intro a _ b hb C _
  obtain ⟨γ, rfl⟩ := hy hb
  rw [reducedOmegaCost_eq_wpow_of_no_retained_rightPrefixes (C - a) γ.toSurreal (by simp),
    plusCount_toSurreal]
  simpa only [sub_add_cancel] using reducedOmegaCost_add_toSurreal_le a (C - γ.toSurreal) γ

/-- The birthday of an arbitrary surreal multiplied by an ordinal satisfies the product bound. -/
theorem birthday_mul_toSurreal_le (x : Surreal.{u}) (o : NatOrdinal.{u}) :
    (x * o.toSurreal).birthday ≤ x.birthday * o := by
  suffices h : o.toSurreal.support ⊆ Set.range NatOrdinal.toSurreal by
    simpa only [birthday_toSurreal] using birthday_mul_le_of_ordinal_exponents x o.toSurreal h
  obtain ⟨n, f, _, rfl⟩ := NatOrdinal.exists_antitone_wpow_sum o
  have hs (S : Finset (Fin n)) : (NatOrdinal.toSurreal (∑ i ∈ S, ω^ (f i))).support ⊆
      Set.range NatOrdinal.toSurreal := by
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | insert i S hi ih =>
      rw [Finset.sum_insert hi, NatOrdinal.toSurreal_add, toSurreal_wpow]
      apply support_add_subset.trans (Set.union_subset _ ih)
      rw [support_wpow, Set.singleton_subset_iff]
      exact ⟨f i, rfl⟩
  exact hs Finset.univ

end Surreal
