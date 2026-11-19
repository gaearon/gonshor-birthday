/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.OrdinalMultiplication
import GonshorBirthday.Surreal.HahnSeries.NormalFormAdd

/-!
# Products with ordinal exponents

The smaller proof applies to a factor with a real constant term of either sign.
-/

universe u
public noncomputable section
namespace Tests
open Surreal

/-- The constant term can be any real, including a negative or nondyadic one. -/
theorem birthday_mul_ordinal_power_add_real (x : Surreal.{u}) (γ : NatOrdinal.{u}) (r : ℝ) :
    (x * (ω^ γ.toSurreal + (r : Surreal))).birthday ≤
      x.birthday * (ω^ γ.toSurreal + (r : Surreal)).birthday := by
  apply birthday_mul_le_of_ordinal_exponents
  apply support_add_subset.trans (Set.union_subset _ _)
  · rw [support_wpow, Set.singleton_subset_iff]
    exact ⟨γ, rfl⟩
  · rw [← support_coeff, coeff_realCast]
    apply Pi.support_single_subset.trans
    rw [Set.singleton_subset_iff]
    exact ⟨0, NatOrdinal.toSurreal_zero⟩

end Tests
