/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadCoefficientCost
public import GonshorBirthday.Surreal.Birthday.NormalFormReplacement
public import GonshorBirthday.Surreal.HahnSeries.NormalFormMul

import GonshorBirthday.NatOrdinal.FiniteBlocks
import GonshorBirthday.Surreal.Birthday.ProductHeadCost
import GonshorBirthday.Surreal.Birthday.Real
import Mathlib.Algebra.Group.Pointwise.Set.Small
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Finset.MulAntidiagonal
import Mathlib.Data.List.FinRange

/-!
# Bounding one convolution fibre

At each exponent, choose a real of greatest birthday among the convolution coefficient
and the input coefficients contributing there. The resulting series contains every exponent
sum and inherits each input's nondyadic boundaries. Its chosen coefficient is paid for by
the finite sum of cells if it is the convolution, or by one cell if it is an input coefficient.
-/

universe u
public noncomputable section
namespace Surreal
open scoped Ordinal Pointwise
open Set

private theorem headCoefficientCost_sum_le_of_cells (H s : Surreal.{u}) {n : ℕ}
    (r : Fin n → ℝ) (p : Fin n → NatOrdinal.{u})
    (h : ∀ i, headCoefficientCost H s (r i) ≤ p i) :
    headCoefficientCost H s (∑ i, r i) ≤ NatOrdinal.of (typeLT (Σₗ i, (p i).val.ToType)) := by
  apply (headCoefficientCost_fin_sum_le H s r).trans
  apply NatOrdinal.of.monotone
  simp only [Ordinal.type_fin_sigma, Ordinal.type_toType, List.ofFn_eq_map]
  exact List.sum_le_sum fun i _ ↦ NatOrdinal.val.monotone (h i)

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
  change headCoefficientCost H s ((X * Y).coeff s) ≤ _
  rw [hcoeff]
  apply headCoefficientCost_sum_le_of_cells H s r p
  intro i
  obtain ⟨ha, hb, he⟩ := (SurrealHahnSeries.mem_supportAntidiagonal _ _ _ _).mp (e i).2
  simp only [support_toHahnSeries] at ha hb
  have h := headCoefficientCost_mul_replacement_le hτpos hτ x y ha hb
  rw [he] at h
  exact h

private theorem exists_maximal_fibre_coefficients (x y : Surreal.{u}) :
    ∃ Z : Surreal.{u},
      (∀ s, ((x * y).coeff s : Surreal.{u}).birthday ≤ (Z.coeff s : Surreal.{u}).birthday) ∧
      (∀ a ∈ x.support, ∀ b ∈ y.support,
        max (x.coeff a : Surreal.{u}).birthday (y.coeff b : Surreal.{u}).birthday ≤
          (Z.coeff (a + b) : Surreal.{u}).birthday) ∧
      ∀ s, Z.coeff s = (x * y).coeff s ∨
        ∃ p ∈ SurrealHahnSeries.supportAntidiagonal x.toHahnSeries y.toHahnSeries s,
          Z.coeff s = x.coeff p.1 ∨ Z.coeff s = y.coeff p.2 := by
  classical
  let F := SurrealHahnSeries.supportAntidiagonal x.toHahnSeries y.toHahnSeries
  let C (s : Surreal.{u}) := insert ((x * y).coeff s)
    ((F s).biUnion (fun p ↦ {x.coeff p.1, y.coeff p.2}))
  have hC (s : Surreal.{u}) (r : ℝ) : r ∈ C s ↔ r = (x * y).coeff s ∨
      ∃ p ∈ F s, r = x.coeff p.1 ∨ r = y.coeff p.2 := by
    simp only [C, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_singleton]
  choose f hmem hmax using fun s ↦
    (C s).exists_max_image (fun r ↦ (r : Surreal.{u}).birthday) (Finset.insert_nonempty _ _)
  have hs : Function.support f ⊆ x.support + y.support := by
    intro s h
    rcases (hC _ _).mp (hmem s) with he | ⟨⟨a, b⟩, hp, _⟩
    · change f s ≠ 0 at h
      have hn : s ∈ (x * y).support := mem_support_iff.mpr (he ▸ h)
      rw [← support_toHahnSeries, toHahnSeries_mul] at hn
      simpa only [Set.mem_add, support_toHahnSeries] using
        SurrealHahnSeries.exists_add_eq_of_mem_support_mul hn
    · simp only [F, SurrealHahnSeries.mem_supportAntidiagonal, support_toHahnSeries] at hp
      exact Set.mem_add.mpr ⟨a, hp.1, b, hp.2⟩
  have hwf := Set.IsWF.add (α := Surreal.{u}ᵒᵈ) x.wellFoundedOn_support y.wellFoundedOn_support
  let Z := (SurrealHahnSeries.mk f (small_subset hs) (hwf.subset hs)).toSurreal
  have hZ : Z.coeff = f :=
    (SurrealHahnSeries.coeff_toSurreal _).trans (SurrealHahnSeries.coeff_mk f _ _)
  refine ⟨Z, ?_⟩
  rw [hZ]
  refine ⟨fun s ↦ hmax s _ ((hC _ _).mpr (Or.inl rfl)), ?_, fun s ↦ (hC _ _).mp (hmem s)⟩
  intro a ha b hb
  have hp : (a, b) ∈ F (a + b) := by
    simpa only [F, SurrealHahnSeries.mem_supportAntidiagonal, support_toHahnSeries] using
      And.intro ha (And.intro hb (Eq.refl (a + b)))
  exact max_le (hmax _ _ ((hC _ _).mpr (Or.inr ⟨_, hp, Or.inl rfl⟩)))
    (hmax _ _ ((hC _ _).mpr (Or.inr ⟨_, hp, Or.inr rfl⟩)))

private theorem head_retention_of_shift {x Z a b v : Surreal.{u}}
    (hs : ∀ w ∈ x.support, w + b ∈ Z.support)
    (hc : ∀ w ∈ x.support,
      (x.coeff w : Surreal.{u}).birthday ≤ (Z.coeff (w + b) : Surreal.{u}).birthday)
    (hv : a + b < v) (hhead : (Z.normalFormTrunc (a + b)).support ⊆ Ici v)
    (hfin : ((Z.normalFormTrunc (a + b)).coeff v : Surreal.{u}).birthday <
      NatOrdinal.of Ordinal.omega0) :
    (x.normalFormTrunc a).support ⊆ Ici (v - b) ∧
      ((x.normalFormTrunc a).coeff (v - b) : Surreal.{u}).birthday <
        NatOrdinal.of Ordinal.omega0 := by
  rw [coeff_trunc_of_lt hv] at hfin
  rw [support_trunc, coeff_trunc_of_lt (lt_sub_iff_add_lt.mpr hv)]
  constructor
  · intro w hw
    change v - b ≤ w
    apply sub_le_iff_le_add.mpr
    exact hhead (show w + b ∈ (Z.normalFormTrunc (a + b)).support by
      rw [support_trunc]; exact ⟨hs w hw.1, add_lt_add_left hw.2 b⟩)
  · by_cases hw : v - b ∈ x.support
    · exact (hc _ hw).trans_lt (by simpa only [sub_add_cancel] using hfin)
    · rw [notMem_support_iff.mp hw, Real.toSurreal_zero, birthday_zero]
      exact NatOrdinal.of.strictMono Ordinal.omega0_pos

/-- Exponent bounds on the two supports suffice to bound all coefficient fibres. -/
theorem exists_product_fibre_bound_of_exponent_bounds (x y : Surreal.{u})
    (hcut : ∀ a ∈ x.support, ∀ b ∈ y.support, ∀ C, a + b ≤ C →
      reducedOmegaCost C (a + b) ≤ reducedOmegaCost (C - b) a * reducedOmegaCost (C - a) b) :
    ∃ Z : Surreal.{u},
      (∀ s, ((x * y).coeff s : Surreal.{u}).birthday ≤ (Z.coeff s : Surreal.{u}).birthday) ∧
      (∀ a ∈ x.support, ∀ b ∈ y.support, a + b ∈ Z.support) ∧
      ∀ s, ∀ {n : ℕ},
        (e : Fin n ≃ SurrealHahnSeries.supportAntidiagonal x.toHahnSeries y.toHahnSeries s) →
        headCoefficientCost (Z.normalFormTrunc s) s (Z.coeff s) ≤ NatOrdinal.of (typeLT
          (Σₗ i : Fin n, (headCoefficientCost (x.normalFormTrunc (e i).1.1) (e i).1.1
            (x.coeff (e i).1.1) * headCoefficientCost (y.normalFormTrunc (e i).1.2) (e i).1.2
              (y.coeff (e i).1.2)).val.ToType)) := by
  classical
  obtain ⟨Z, hprod, hmax, hchoice⟩ := exists_maximal_fibre_coefficients x y
  have hs (a) (ha : a ∈ x.support) (b) (hb : b ∈ y.support) : a + b ∈ Z.support := by
    have h := (one_le_birthday_real (mem_support_iff.mp ha)).trans
      ((le_max_left _ _).trans (hmax a ha b hb))
    contrapose! h
    simp only [notMem_support_iff.mp h, Real.toSurreal_zero, birthday_zero, zero_lt_one]
  have hhead (a) (ha : a ∈ x.support) (b) (hb : b ∈ y.support) :
      headOmegaCost (Z.normalFormTrunc (a + b)) (a + b) ≤
        headOmegaCost (x.normalFormTrunc a) a * headOmegaCost (y.normalFormTrunc b) b := by
    apply headOmegaCost_add_le_of_exponent_bound (hcut a ha b hb)
    intro v hv hsup hfin
    have hlt := (mem_rightPrefixes_iff.mp hv).2
    refine ⟨head_retention_of_shift (fun w hw ↦ hs w hw b hb)
      (fun w hw ↦ (le_max_left _ _).trans (hmax w hw b hb)) hlt hsup hfin, ?_⟩
    apply head_retention_of_shift (b := a) (Z := Z)
    · exact fun w hw ↦ by simpa only [add_comm] using hs a ha w hw
    · exact fun w hw ↦ by simpa only [add_comm] using (le_max_right _ _).trans (hmax a ha w hw)
    · simpa only [add_comm] using hlt
    · simpa only [add_comm] using hsup
    · simpa only [add_comm] using hfin
  refine ⟨Z, hprod, hs, ?_⟩
  intro s n e
  let H := Z.normalFormTrunc s
  let P (i : Fin n) := headCoefficientCost (x.normalFormTrunc (e i).1.1) (e i).1.1
    (x.coeff (e i).1.1) * headCoefficientCost (y.normalFormTrunc (e i).1.2) (e i).1.2
      (y.coeff (e i).1.2)
  have hcell (i : Fin n) {r : ℝ} (hr : (r : Surreal.{u}).birthday ≤
      (x.coeff (e i).1.1 : Surreal.{u}).birthday * (y.coeff (e i).1.2 : Surreal.{u}).birthday) :
      headCoefficientCost H s r ≤ P i := by
    obtain ⟨ha, hb, he⟩ := (SurrealHahnSeries.mem_supportAntidiagonal _ _ _ _).mp (e i).2
    simp only [support_toHahnSeries] at ha hb
    simpa only [H, P, he] using headCoefficientCost_le_mul_of_birthday_le (hhead _ ha _ hb)
      (mem_support_iff.mp ha) (mem_support_iff.mp hb) hr
  change headCoefficientCost H s (Z.coeff s) ≤ NatOrdinal.of (typeLT (Σₗ i, (P i).val.ToType))
  rcases hchoice s with h | ⟨p, hp, h⟩
  · have heq : (x * y).coeff s = ∑ i, x.coeff (e i).1.1 * y.coeff (e i).1.2 := by
      rw [coeff_mul, ← Finset.sum_coe_sort]
      exact (e.sum_comp (fun p ↦ x.coeff p.1.1 * y.coeff p.1.2)).symm
    rw [h, heq]
    apply headCoefficientCost_sum_le_of_cells
    intro i
    exact hcell i (by simpa only [Real.toSurreal_mul] using birthday_real_mul_le _ _)
  · let i := e.symm ⟨p, hp⟩
    have hblock : P i ≤ NatOrdinal.of (typeLT (Σₗ j, (P j).val.ToType)) := by
      apply NatOrdinal.val.le_iff_le.mp
      simp only [NatOrdinal.val_of, Ordinal.type_fin_sigma, Ordinal.type_toType]
      exact List.le_sum_of_mem (List.mem_ofFn.mpr ⟨i, rfl⟩)
    obtain ⟨ha, hb, _⟩ := (SurrealHahnSeries.mem_supportAntidiagonal _ _ _ _).mp (e i).2
    simp only [support_toHahnSeries] at ha hb
    apply (hcell i ?_).trans hblock
    simp only [i, Equiv.apply_symm_apply] at ha hb ⊢
    rcases h with h | h
    · rw [h]
      exact le_mul_of_one_le_right' (one_le_birthday_real (mem_support_iff.mp hb))
    · rw [h]
      exact le_mul_of_one_le_left' (one_le_birthday_real (mem_support_iff.mp ha))

/-- A series majorizing the product coefficientwise whose terms fit their finite product fibres. -/
theorem exists_product_fibre_bound (x y : Surreal.{u}) :
    ∃ Z : Surreal.{u},
      (∀ s, ((x * y).coeff s : Surreal.{u}).birthday ≤ (Z.coeff s : Surreal.{u}).birthday) ∧
      (∀ a ∈ x.support, ∀ b ∈ y.support, a + b ∈ Z.support) ∧
      ∀ s, ∀ {n : ℕ},
        (e : Fin n ≃ SurrealHahnSeries.supportAntidiagonal x.toHahnSeries y.toHahnSeries s) →
        headCoefficientCost (Z.normalFormTrunc s) s (Z.coeff s) ≤ NatOrdinal.of (typeLT
          (Σₗ i : Fin n, (headCoefficientCost (x.normalFormTrunc (e i).1.1) (e i).1.1
            (x.coeff (e i).1.1) * headCoefficientCost (y.normalFormTrunc (e i).1.2) (e i).1.2
              (y.coeff (e i).1.2)).val.ToType)) :=
  exists_product_fibre_bound_of_exponent_bounds x y (fun a _ b _ ↦ reducedOmegaCost_add_at_le a b)

end Surreal
