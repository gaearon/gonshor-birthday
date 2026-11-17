/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module
public import GonshorBirthday.Surreal.Birthday.CoefficientComparison
public import GonshorBirthday.Surreal.Birthday.Subseries

/-!
# Birthday monotonicity for normal-form subseries
-/

universe u
public noncomputable section
namespace Surreal

/-- Selecting fewer normal-form terms cannot increase birthday. -/
theorem birthday_subseries_mono (x : Surreal.{u}) {S T : Set Surreal.{u}}
    (hST : S ⊆ T) : (subseries x S).birthday ≤ (subseries x T).birthday := by
  classical
  apply birthday_le_of_coeff_birthday_le
  intro s
  rw [coeff_subseries, coeff_subseries]
  by_cases hs : s ∈ S
  · rw [ite_eq_left hs, ite_eq_left (hST hs)]
  · rw [ite_eq_right hs, Real.toSurreal_zero, birthday_zero]
    exact zero_le

/-- Every normal-form subseries has birthday at most that of the full surreal. -/
theorem birthday_subseries_le (x : Surreal.{u}) (S : Set Surreal.{u}) :
    (subseries x S).birthday ≤ x.birthday := by
  simpa only [subseries_univ] using birthday_subseries_mono x (Set.subset_univ S)

end Surreal
