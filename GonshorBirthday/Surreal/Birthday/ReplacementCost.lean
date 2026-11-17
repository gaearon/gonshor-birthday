/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadCost
public import GonshorBirthday.Surreal.Birthday.NormalFormReplacement

/-!
# Invariance of native monomial costs under positive replacement

Normal-form replacement commutes with truncation. It preserves the support and
the dyadicness of every boundary coefficient, so it preserves each original
retained exponent position and its expanded cost.
-/

universe u
public noncomputable section
namespace Surreal

/-- Coefficientwise birthday replacement commutes with normal-form truncation. -/
theorem normalFormBirthdayReplacement_trunc (τ : ℝ) (x s : Surreal.{u}) :
    normalFormBirthdayReplacement τ (x.normalFormTrunc s) =
      (normalFormBirthdayReplacement τ x).normalFormTrunc s := by
  apply toHahnSeries_inj.mp
  apply SurrealHahnSeries.ext
  funext w
  simp only [coeff_toHahnSeries, coeff_normalFormBirthdayReplacement, coeff_trunc]
  split_ifs <;> simp only [birthdayReplacement_zero]

/-- Positive transcendental replacement preserves every original retained exponent position. -/
theorem headOmegaPositions_normalFormBirthdayReplacement {τ : ℝ}
    (hτpos : 0 < τ) (hτ : Transcendental ℚ τ) (H s : Surreal.{u}) :
    headOmegaPositions (normalFormBirthdayReplacement τ H) s = headOmegaPositions H s := by
  apply headOmegaPositions_congr (support_normalFormBirthdayReplacement hτpos H)
  intro w
  rw [birthday_coeff_normalFormBirthdayReplacement hτ]

/-- Positive transcendental replacement preserves every native monomial cost. -/
theorem headOmegaCost_normalFormBirthdayReplacement {τ : ℝ}
    (hτpos : 0 < τ) (hτ : Transcendental ℚ τ) (H s : Surreal.{u}) :
    headOmegaCost (normalFormBirthdayReplacement τ H) s = headOmegaCost H s := by
  rw [headOmegaCost_eq_positions,
    headOmegaPositions_normalFormBirthdayReplacement hτpos hτ, headOmegaCost_eq_positions]

/-- The earlier normal-form head of each term has the same cost after replacement. -/
theorem headOmegaCost_trunc_normalFormBirthdayReplacement {τ : ℝ}
    (hτpos : 0 < τ) (hτ : Transcendental ℚ τ) (x s : Surreal.{u}) :
    headOmegaCost ((normalFormBirthdayReplacement τ x).normalFormTrunc s) s =
      headOmegaCost (x.normalFormTrunc s) s := by
  rw [← normalFormBirthdayReplacement_trunc,
    headOmegaCost_normalFormBirthdayReplacement hτpos hτ]

end Surreal
