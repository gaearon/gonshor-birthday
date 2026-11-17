/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Multiplication
public import GonshorBirthday.Surreal.Birthday.Tests.SupportGap

/-!
# Clients of the unrestricted multiplication birthday theorem

The exact original statement is used in an arbitrary universe. Separate clients
include an empty input, two arbitrary ordinal support lengths with a negative
input, and sharpness on all ordinal inputs. The bound uses natural multiplication
on `NatOrdinal`, with the original intrinsic `Surreal.birthday`.
-/

universe u
public noncomputable section
namespace Tests
open Surreal

/-- The public theorem has the unrestricted universe-polymorphic CG target type. -/
theorem unrestricted_mul_birthday (x y : Surreal.{u}) :
    (x * y).birthday ≤ x.birthday * y.birthday :=
  Surreal.birthday_mul_le x y

/-- The full multiplication theorem includes the empty-support case. -/
theorem zero_product_birthday (x : Surreal.{u}) : (0 * x).birthday = 0 := by
  apply le_antisymm ?_ zero_le
  simpa only [birthday_zero, zero_mul] using Surreal.birthday_mul_le 0 x

/-- Both original supports may have arbitrary ordinal lengths and a negative input. -/
theorem original_ordinal_series_product_budget (Λ Μ : Ordinal.{u}) :
    let x := decreasingOrdinalSeries Λ
    let y := decreasingOrdinalSeries Μ
    x.length = Λ ∧ y.length = Μ ∧ (-x * y).birthday ≤ x.birthday * y.birthday := by
  refine ⟨length_decreasingOrdinalSeries Λ, length_decreasingOrdinalSeries Μ, ?_⟩
  simpa only [birthday_neg] using Surreal.birthday_mul_le
    (-decreasingOrdinalSeries Λ) (decreasingOrdinalSeries Μ)

/-- Ordinal surreal inputs attain the natural-product birthday bound. -/
theorem ordinal_product_attains_birthday_bound (a b : NatOrdinal.{u}) :
    ((a : Surreal.{u}) * (b : Surreal.{u})).birthday = a * b := by
  rw [← NatOrdinal.toSurreal_mul, birthday_toSurreal]

end Tests
