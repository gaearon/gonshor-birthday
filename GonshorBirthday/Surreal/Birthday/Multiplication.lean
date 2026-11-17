/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Birthday.Basic

public import Mathlib.Algebra.Order.Ring.Abs

import GonshorBirthday.Surreal.Birthday.CoefficientComparison
import GonshorBirthday.Surreal.Birthday.ProductCoefficientCost
import GonshorBirthday.Surreal.Birthday.ProductGrid

/-!
# The multiplication birthday bound

In each exponent fibre a coefficient of greatest birthday majorizes the actual
product coefficient. Its term fits the sum of that fibre's cell bounds. Whole-series
coefficient comparison and the ordering of the grid give the intrinsic birthday bound.
-/

universe u

public noncomputable section

namespace Surreal

/-- Absolute value preserves the intrinsic birthday. -/
@[simp]
theorem birthday_abs (x : Surreal.{u}) : (abs x).birthday = x.birthday := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, birthday_neg]

/-- The unrestricted multiplication bound is equivalent to its nonnegative case. -/
theorem birthday_mul_le_iff_nonneg :
    (∀ x y : Surreal.{u}, (x * y).birthday ≤ x.birthday * y.birthday) ↔
    (∀ x y : Surreal.{u}, 0 ≤ x → 0 ≤ y →
      (x * y).birthday ≤ x.birthday * y.birthday) := by
  constructor
  · exact fun h x y _ _ ↦ h x y
  · intro h x y
    simpa only [← abs_mul, birthday_abs] using h (abs x) (abs y) (abs_nonneg x) (abs_nonneg y)

/-- Multiplication by a natural number satisfies the natural-product birthday bound. -/
theorem birthday_natCast_mul_le (n : ℕ) (x : Surreal.{u}) :
    ((n : Surreal) * x).birthday ≤ (n : NatOrdinal) * x.birthday := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Nat.cast_add, Nat.cast_one, add_mul,
      one_mul]
    exact (birthday_add_le _ _).trans (add_le_add_left ih _)

/-- Multiplication by an integer satisfies the natural-product birthday bound. -/
theorem birthday_intCast_mul_le (n : ℤ) (x : Surreal.{u}) :
    ((n : Surreal) * x).birthday ≤ (n.natAbs : NatOrdinal) * x.birthday := by
  induction n using Int.negInduction with
  | nat n => simpa using birthday_natCast_mul_le n x
  | neg ih n => simpa using ih n

/-- **Gonshor's conjecture**: the birthday of a product of surreal numbers is at most the
natural product of their birthdays. -/
theorem birthday_mul_le (x y : Surreal) : (x * y).birthday ≤ x.birthday * y.birthday := by
  obtain ⟨Z, hcoeff, hs, hf⟩ := exists_product_fibre_bound x y
  exact (birthday_le_of_coeff_birthday_le hcoeff).trans
    (birthday_le_of_product_fibre_costs x y Z hs hf)

end Surreal
