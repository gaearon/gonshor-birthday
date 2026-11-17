/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.NormalFormReplacement
public import GonshorBirthday.Surreal.HahnSeries.NormalFormMul

/-!
# Actual normal-form replacement and convolution clients

Two distinct exponent pairs contribute to the same fibre. The replacement acts on
the existing surreal type, including a negative fractional real and zero. Its
coefficient comparison permits arbitrary supports and negative factors.
-/

universe u
public noncomputable section
namespace Tests
open Surreal

/-- Both crossed pairs appear in the middle coefficient fibre of a two-term square. -/
theorem two_pairs_in_convolution :
    let x : SurrealHahnSeries.{u} :=
      SurrealHahnSeries.single 0 1 + SurrealHahnSeries.single 1 1
    (0, 1) ∈ SurrealHahnSeries.supportAntidiagonal x x 1 ∧
      (1, 0) ∈ SurrealHahnSeries.supportAntidiagonal x x 1 := by
  dsimp only
  norm_num [SurrealHahnSeries.mem_supportAntidiagonal, SurrealHahnSeries.mem_support_iff,
    SurrealHahnSeries.coeff_add_apply, SurrealHahnSeries.coeff_single]

example (τ : ℝ) : normalFormBirthdayReplacement τ (0 : Surreal.{u}) = 0 :=
  normalFormBirthdayReplacement_zero τ

/-- The negative-half surreal is replaced by the positive integer two. -/
theorem normal_replacement_negative_half (τ : ℝ) :
    normalFormBirthdayReplacement τ
      (((((-1 : Dyadic) >>> 1).toRat : ℝ)) : Surreal.{u}) = 2 := by
  rw [normalFormBirthdayReplacement_realCast, birthdayReplacement_dyadic]
  rw [show Dyadic.birthday ((-1 : Dyadic) >>> 1) = 2 from rfl]
  norm_num

/-- Actual products with a negated factor satisfy the coefficient comparison. -/
theorem replacement_product_with_neg (τ : ℝ) (hτpos : 0 < τ)
    (hτ : Transcendental ℚ τ) (x y s : Surreal.{u}) :
    (((x * -y).coeff s : ℝ) : Surreal.{u}).birthday ≤
      (((normalFormBirthdayReplacement τ x * normalFormBirthdayReplacement τ (-y)).coeff s : ℝ) :
        Surreal.{u}).birthday :=
  birthday_coeff_mul_le_normalFormBirthdayReplacement hτpos hτ x (-y) s

end Tests
