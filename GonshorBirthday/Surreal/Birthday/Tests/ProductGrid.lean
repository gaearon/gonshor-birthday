/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ProductGrid
public import GonshorBirthday.Surreal.Birthday.Tests.SupportGap

import GonshorBirthday.NatOrdinal.ProductFibre
import GonshorBirthday.Surreal.Birthday.Tests.HeadOmegaLength
import GonshorBirthday.Surreal.HahnSeries.NormalFormAdd

/-!
# Whole product-grid clients

Two genuine ordinal-indexed series test arbitrary support lengths with a negated
input. Zero tests the empty grid. The square of one plus reciprocal omega is an
actual product fixed by replacement and has a repeated middle exponent sum.
-/

universe u
public noncomputable section
namespace Tests
open Surreal

/-- Both whole input supports may have arbitrary ordinal lengths, with a negative input. -/
theorem ordinal_series_product_budget {τ : ℝ} (hτpos : 0 < τ)
    (hτ : Transcendental ℚ τ) (Λ Μ : Ordinal.{u}) :
    let x := decreasingOrdinalSeries Λ
    let y := decreasingOrdinalSeries Μ
    x.length = Λ ∧ y.length = Μ ∧
      (normalFormBirthdayReplacement τ (-x) * normalFormBirthdayReplacement τ y).birthday ≤
        x.birthday * y.birthday := by
  refine ⟨length_decreasingOrdinalSeries Λ, length_decreasingOrdinalSeries Μ, ?_⟩
  simpa only [birthday_neg] using birthday_mul_normalFormBirthdayReplacement_le hτpos hτ
    (-decreasingOrdinalSeries Λ) (decreasingOrdinalSeries Μ)

/-- An empty input gives a zero whole product birthday through the grid bound. -/
theorem empty_product_grid {τ : ℝ} (hτpos : 0 < τ)
    (hτ : Transcendental ℚ τ) (x : Surreal.{u}) :
    (normalFormBirthdayReplacement τ 0 * normalFormBirthdayReplacement τ x).birthday = 0 := by
  apply le_antisymm ?_ zero_le
  simpa only [birthday_zero, zero_mul] using
    birthday_mul_normalFormBirthdayReplacement_le hτpos hτ 0 x

/-- The actual two-term square satisfies the whole omega-by-omega birthday bound. -/
theorem reciprocal_two_term_square_budget :
    ((1 + ω^ (-1 : Surreal.{u})) * (1 + ω^ (-1 : Surreal.{u}))).birthday ≤
      NatOrdinal.of Ordinal.omega0 * NatOrdinal.of Ordinal.omega0 := by
  obtain ⟨τ, hτpos, hτ⟩ := exists_pos_transcendental_real
  let x : Surreal.{u} := 1 + ω^ (-1 : Surreal)
  have h1 : birthdayReplacement τ 1 = 1 := by
    simpa [show Dyadic.birthday 1 = 1 from rfl] using birthdayReplacement_dyadic τ 1
  have hr : normalFormBirthdayReplacement τ x = x := by
    apply toHahnSeries_inj.mp
    apply SurrealHahnSeries.ext
    funext s
    rw [coeff_toHahnSeries, coeff_toHahnSeries, coeff_normalFormBirthdayReplacement]
    dsimp only [x]
    simp only [coeff_add, coeff_one, coeff_wpow, Pi.add_apply]
    by_cases hs : s = 0 <;> by_cases ht : s = -1 <;> simp_all
  have hfin : ((1 : ℝ) : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 := by
    rw [Real.toSurreal_one, birthday_one]
    apply NatOrdinal.val.lt_iff_lt.mp
    simpa only [Nat.cast_one, NatOrdinal.val_one, NatOrdinal.val_of] using
      (Ordinal.natCast_lt_omega0 1 : (1 : ℕ) < Ordinal.omega0)
  have hb : x.birthday = NatOrdinal.of Ordinal.omega0 := by
    simpa only [Real.toSurreal_one] using finite_real_head_reciprocal_birthday (1 : ℝ) hfin
  have h := birthday_mul_normalFormBirthdayReplacement_le hτpos hτ x x
  rwa [hr, hb] at h

end Tests
