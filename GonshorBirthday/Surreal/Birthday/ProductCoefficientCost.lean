/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadCoefficientCost
public import GonshorBirthday.Surreal.Birthday.NormalFormReplacement
public import GonshorBirthday.Surreal.HahnSeries.NormalFormMul

import GonshorBirthday.Surreal.Birthday.ProductHeadCost

/-!
# Complete native costs of actual product coefficients

For every supported exponent pair, the actual replacement-product head and its
real coefficient product fit the natural product of the two original term costs.
A whole finite exponent-sum fibre fits the ordinary ordered sum of those cell
budgets, in any finite enumeration. All original signs and supports are allowed.
-/

universe u
public noncomputable section
namespace Surreal
open scoped Ordinal

/-- Each complete replacement-product cell cost fits its two original input term costs. -/
theorem headCoefficientCost_mul_replacement_le {τ : ℝ}
    (hτpos : 0 < τ) (hτ : Transcendental ℚ τ) (x y : Surreal.{u})
    {a b : Surreal.{u}} (ha : a ∈ x.support) (hb : b ∈ y.support) :
    headCoefficientCost
      ((normalFormBirthdayReplacement τ x * normalFormBirthdayReplacement τ y).normalFormTrunc
        (a + b))
      (a + b) ((normalFormBirthdayReplacement τ x).coeff a *
        (normalFormBirthdayReplacement τ y).coeff b) ≤
      headCoefficientCost (x.normalFormTrunc a) a (x.coeff a) *
        headCoefficientCost (y.normalFormTrunc b) b (y.coeff b) := by
  have h := headCoefficientCost_mul_le
    (headOmegaCost_mul_replacement_le hτpos hτ x y ha hb)
    ((normalFormBirthdayReplacement τ x).coeff a)
    ((normalFormBirthdayReplacement τ y).coeff b)
  simpa only [headCoefficientCost_trunc_normalFormBirthdayReplacement hτpos hτ] using h

/-- The term at exponent `s` of a product of replaced series costs at most the ordered sum,
over any enumeration of the pairs of exponents with sum `s`, of the natural products of the two
input term costs. -/
theorem headCoefficientCost_mul_replacement_fibre_le {τ : ℝ}
    (hτpos : 0 < τ) (hτ : Transcendental ℚ τ) (x y s : Surreal.{u}) {n : ℕ}
    (e : Fin n ≃ (SurrealHahnSeries.supportAntidiagonal x.toHahnSeries y.toHahnSeries s)) :
    headCoefficientCost
      ((normalFormBirthdayReplacement τ x * normalFormBirthdayReplacement τ y).normalFormTrunc s) s
      ((normalFormBirthdayReplacement τ x * normalFormBirthdayReplacement τ y).coeff s) ≤
        NatOrdinal.of (typeLT (Σₗ i : Fin n,
          (headCoefficientCost (x.normalFormTrunc (e i).1.1) (e i).1.1 (x.coeff (e i).1.1) *
            headCoefficientCost (y.normalFormTrunc (e i).1.2) (e i).1.2
              (y.coeff (e i).1.2)).val.ToType)) := by
  let X := normalFormBirthdayReplacement τ x
  let Y := normalFormBirthdayReplacement τ y
  let H := (X * Y).normalFormTrunc s
  let r (i : Fin n) := X.coeff (e i).1.1 * Y.coeff (e i).1.2
  let c (i : Fin n) := headCoefficientCost H s (r i)
  let p (i : Fin n) :=
    headCoefficientCost (x.normalFormTrunc (e i).1.1) (e i).1.1 (x.coeff (e i).1.1) *
    headCoefficientCost (y.normalFormTrunc (e i).1.2) (e i).1.2 (y.coeff (e i).1.2)
  have hanti : SurrealHahnSeries.supportAntidiagonal X.toHahnSeries Y.toHahnSeries s =
      SurrealHahnSeries.supportAntidiagonal x.toHahnSeries y.toHahnSeries s := by
    apply SurrealHahnSeries.supportAntidiagonal_eq_of_support_eq
    · simp only [X, support_toHahnSeries, support_normalFormBirthdayReplacement hτpos]
    · simp only [Y, support_toHahnSeries, support_normalFormBirthdayReplacement hτpos]
  have hcoeff : (X * Y).coeff s = ∑ i, r i := by
    rw [coeff_mul, hanti]
    calc
      _ = ∑ q : (SurrealHahnSeries.supportAntidiagonal x.toHahnSeries y.toHahnSeries s),
          X.coeff q.1.1 * Y.coeff q.1.2 := (Finset.sum_coe_sort _ _).symm
      _ = _ := (Equiv.sum_comp e (fun q ↦ X.coeff q.1.1 * Y.coeff q.1.2)).symm
  have hcell (i : Fin n) : c i ≤ p i := by
    obtain ⟨ha, hb, he⟩ := (SurrealHahnSeries.mem_supportAntidiagonal _ _ _ _).mp (e i).2
    simp only [support_toHahnSeries] at ha hb
    have h := headCoefficientCost_mul_replacement_le hτpos hτ x y ha hb
    rw [he] at h
    exact h
  change headCoefficientCost H s ((X * Y).coeff s) ≤ _
  rw [hcoeff]
  apply (headCoefficientCost_fin_sum_le H s r).trans
  apply NatOrdinal.of.monotone
  let f : (Σₗ i : Fin n, (c i).val.ToType) → (Σₗ i : Fin n, (p i).val.ToType) :=
    fun z ↦ toLex ⟨(ofLex z).1, Ordinal.ToType.mk
      ⟨(ofLex z).2.toOrd.1,
        (ofLex z).2.toOrd.2.trans_le (NatOrdinal.val.monotone (hcell (ofLex z).1))⟩⟩
  have hf : StrictMono f := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    change Sigma.Lex ((· < ·) : Fin n → _ → Prop)
      (fun i (a b : (c i).val.ToType) ↦ a < b) ⟨i, a⟩ ⟨j, b⟩ at h
    cases h with
    | left a b h => exact Sigma.Lex.left _ _ h
    | right a b h =>
      exact Sigma.Lex.right _ _ (Ordinal.ToType.mk.strictMono
        (Ordinal.ToType.mk.symm.strictMono h))
  exact (RelEmbedding.ofMonotone f hf).ordinal_type_le

end Surreal
