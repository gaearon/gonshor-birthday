/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module
public import GonshorBirthday.Surreal.HahnSeries.Transfer

/-!
# Conway normal-form subseries
-/

universe u
public noncomputable section
namespace Surreal
open Set

open Classical in
/-- Retain exactly the Conway normal-form terms whose exponents lie in a set. -/
def subseries (x : Surreal.{u}) (S : Set Surreal.{u}) : Surreal.{u} :=
  let f : Surreal.{u} → ℝ := fun s ↦ if s ∈ S then x.coeff s else 0
  have hf : Function.support f ⊆ x.support := by
    intro s hs
    apply mem_support_iff.mpr
    intro hx
    change f s ≠ 0 at hs
    exact hs (by simp only [f, hx, ite_self])
  (SurrealHahnSeries.mk f (small_subset hf)
    (Set.WellFoundedOn.subset x.wellFoundedOn_support hf)).toSurreal

open Classical in
/-- A subseries keeps the original coefficient at selected exponents and vanishes elsewhere. -/
theorem coeff_subseries (x : Surreal.{u}) (S : Set Surreal.{u}) (s : Surreal.{u}) :
    (subseries x S).coeff s = if s ∈ S then x.coeff s else 0 := by
  rw [subseries, SurrealHahnSeries.coeff_toSurreal, SurrealHahnSeries.coeff_mk]

/-- The support of a subseries is precisely the selected part of the original support. -/
theorem support_subseries (x : Surreal.{u}) (S : Set Surreal.{u}) :
    (subseries x S).support = x.support ∩ S := by
  classical
  ext s
  rw [mem_support_iff, coeff_subseries, mem_inter_iff, mem_support_iff]
  split_ifs with hs <;> simp only [hs, and_true, and_false, ne_eq, not_true_eq_false]

/-- Selecting no exponents gives zero. -/
@[simp] theorem subseries_empty (x : Surreal.{u}) : subseries x ∅ = 0 := by
  classical
  apply toHahnSeries_inj.mp
  apply SurrealHahnSeries.ext
  funext s
  simp only [coeff_toHahnSeries, coeff_subseries, mem_empty_iff_false, ite_false,
    coeff_zero, Pi.zero_apply]

/-- Selecting every exponent recovers the original surreal. -/
@[simp] theorem subseries_univ (x : Surreal.{u}) : subseries x univ = x := by
  classical
  apply toHahnSeries_inj.mp
  apply SurrealHahnSeries.ext
  funext s
  simp only [coeff_toHahnSeries, coeff_subseries, mem_univ, ite_true]

/-- Restricting the support commutes with every actual normal-form truncation. -/
theorem subseries_trunc (x : Surreal.{u}) (S : Set Surreal.{u}) (s : Surreal.{u}) :
    subseries (x.normalFormTrunc s) S = (subseries x S).normalFormTrunc s := by
  classical
  apply toHahnSeries_inj.mp
  apply SurrealHahnSeries.ext
  funext w
  simp only [coeff_toHahnSeries, coeff_subseries, coeff_trunc]
  split_ifs <;> rfl

/-- Repeated subseries selection is intersection of exponent sets. -/
theorem subseries_subseries (x : Surreal.{u}) (S T : Set Surreal.{u}) :
    subseries (subseries x S) T = subseries x (S ∩ T) := by
  classical
  apply toHahnSeries_inj.mp
  apply SurrealHahnSeries.ext
  funext s
  simp only [coeff_toHahnSeries, coeff_subseries, mem_inter_iff]
  split_ifs <;> simp_all

end Surreal
