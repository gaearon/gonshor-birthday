/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ProductCoefficientCost

import GonshorBirthday.Surreal.HahnSeries.NormalFormAdd

/-!
# Actual finite product-fibre clients

The products of one minus reciprocal omega and one plus reciprocal omega have
exactly two contributing cells at exponent minus one. Their original coefficients
cancel there. The same actual two-cell fibre supplies the replacement product's
full coefficient cost.
-/

universe u
public noncomputable section
namespace Tests
open Surreal Set
open scoped Ordinal

/-- A genuinely cancelled two-cell fibre supplies the replacement coefficient budget. -/
theorem opposite_two_term_product_fibre {τ : ℝ}
    (hτpos : 0 < τ) (hτ : Transcendental ℚ τ) :
    let x : Surreal.{u} := 1 - ω^ (-1 : Surreal)
    let y : Surreal.{u} := 1 + ω^ (-1 : Surreal)
    let Z := normalFormBirthdayReplacement τ x * normalFormBirthdayReplacement τ y
    ∃ e : Fin 2 ≃ (SurrealHahnSeries.supportAntidiagonal x.toHahnSeries y.toHahnSeries (-1)),
      headCoefficientCost (Z.normalFormTrunc (-1)) (-1) (Z.coeff (-1)) ≤
        NatOrdinal.of (typeLT (Σₗ i : Fin 2,
          (headCoefficientCost (x.normalFormTrunc (e i).1.1) (e i).1.1 (x.coeff (e i).1.1) *
            headCoefficientCost (y.normalFormTrunc (e i).1.2) (e i).1.2
              (y.coeff (e i).1.2)).val.ToType)) ∧ (x * y).coeff (-1) = 0 := by
  let x : Surreal.{u} := 1 - ω^ (-1 : Surreal)
  let y : Surreal.{u} := 1 + ω^ (-1 : Surreal)
  have hx : x.support = ({0, -1} : Set Surreal.{u}) := by
    ext s
    simp only [mem_support_iff, x, sub_eq_add_neg, coeff_add, coeff_neg,
      coeff_one, coeff_wpow, Pi.add_apply, Pi.neg_apply]
    by_cases hs : s = 0 <;> by_cases ht : s = -1 <;>
      simp_all
  have hy : y.support = ({0, -1} : Set Surreal.{u}) := by
    ext s
    simp only [mem_support_iff, y, coeff_add, coeff_one, coeff_wpow, Pi.add_apply]
    by_cases hs : s = 0 <;> by_cases ht : s = -1 <;>
      simp_all
  have hanti : SurrealHahnSeries.supportAntidiagonal x.toHahnSeries y.toHahnSeries (-1) =
      ({(0, -1), (-1, 0)} : Finset (Surreal.{u} × Surreal.{u})) := by
    ext ⟨a, b⟩
    rw [SurrealHahnSeries.mem_supportAntidiagonal, support_toHahnSeries,
      support_toHahnSeries, hx, hy]
    simp only [mem_insert_iff, mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨ha | ha, hb | hb, he⟩ <;> simp_all
    · rintro (h | h) <;> rcases Prod.mk.inj h with ⟨rfl, rfl⟩ <;> simp
  have hc : Fintype.card
      (SurrealHahnSeries.supportAntidiagonal x.toHahnSeries y.toHahnSeries (-1)) = 2 := by
    rw [Fintype.card_coe, hanti]
    norm_num
  let e := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨e, headCoefficientCost_mul_replacement_fibre_le hτpos hτ x y (-1) e, ?_⟩
  rw [coeff_mul, hanti]
  simp only [sub_eq_add_neg, coeff_add, coeff_neg, coeff_one, coeff_wpow,
    Pi.add_apply, Pi.neg_apply]
  norm_num

end Tests
