/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadCoefficientCost
public import GonshorBirthday.Surreal.Birthday.NormalFormReplacement

import GonshorBirthday.Surreal.Birthday.NormalFormLength

import GonshorBirthday.NatOrdinal.OrderedSum

/-!
# Whole normal-form birthday invariance

A surreal's intrinsic birthday is determined by the birthday of each normal-form
coefficient at its actual exponent. Equal coefficient birthdays force equal
supports, the same native deletion decisions, and equal complete term costs.
The ordered term-cost formula then identifies the whole birthdays. Transcendental
coefficient replacement is a special case, with no sign hypothesis on the
transcendental needed for this equality.
-/

universe u
public noncomputable section
namespace Surreal
open Set
open scoped Ordinal

/-- Equal supports and equal native term costs give equal whole birthdays. -/
theorem birthday_eq_of_support_eq_of_term_cost_eq {x y : Surreal.{u}}
    (hs : x.support = y.support)
    (hc : ∀ s ∈ x.support, headCoefficientCost (x.normalFormTrunc s) s (x.coeff s) =
      headCoefficientCost (y.normalFormTrunc s) s (y.coeff s)) : x.birthday = y.birthday := by
  have hs' : x.toHahnSeries.support = y.toHahnSeries.support := by
    simpa only [support_toHahnSeries] using hs
  let f : x.toHahnSeries.length.ToType → y.toHahnSeries.length.ToType := fun i ↦
    Ordinal.ToType.mk (y.toHahnSeries.exp.symm
      ⟨x.toHahnSeries.exp i.toOrd, hs' ▸ (x.toHahnSeries.exp i.toOrd).2⟩)
  have hfe (i : x.toHahnSeries.length.ToType) :
      (y.toHahnSeries.exp (f i).toOrd).1 = (x.toHahnSeries.exp i.toOrd).1 := by
    simp [f]
  have hf : StrictMono f := by
    intro i j hij
    apply Ordinal.ToType.mk.symm.lt_iff_lt.mp
    apply y.toHahnSeries.exp_lt_exp_iff.mp
    change (y.toHahnSeries.exp (f j).toOrd).1 < (y.toHahnSeries.exp (f i).toOrd).1
    rw [hfe, hfe]
    exact x.toHahnSeries.exp_strictAnti (Ordinal.ToType.mk.symm.strictMono hij)
  have hsurj : Function.Surjective f := by
    intro j
    let i : x.toHahnSeries.length.ToType := Ordinal.ToType.mk (x.toHahnSeries.exp.symm
      ⟨y.toHahnSeries.exp j.toOrd, hs'.symm ▸ (y.toHahnSeries.exp j.toOrd).2⟩)
    have hi : (x.toHahnSeries.exp i.toOrd).1 = (y.toHahnSeries.exp j.toOrd).1 := by
      simp [i]
    refine ⟨i, ?_⟩
    apply Ordinal.ToType.mk.symm.injective
    apply y.toHahnSeries.exp.injective
    apply Subtype.ext
    exact (hfe i).trans hi
  rw [birthday_eq_ordered_term_costs x, birthday_eq_ordered_term_costs y]
  apply congrArg NatOrdinal.of
  apply Ordinal.type_sigma_congr _ _
    (OrderIso.ofSurjective (OrderEmbedding.ofStrictMono f hf) hsurj)
  intro i
  rw [Ordinal.type_toType, Ordinal.type_toType]
  change (headCoefficientCost (x.normalFormTrunc (x.toHahnSeries.exp i.toOrd))
      (x.toHahnSeries.exp i.toOrd) (x.coeff (x.toHahnSeries.exp i.toOrd))).val =
    (headCoefficientCost (y.normalFormTrunc (y.toHahnSeries.exp (f i).toOrd))
      (y.toHahnSeries.exp (f i).toOrd) (y.coeff (y.toHahnSeries.exp (f i).toOrd))).val
  rw [hfe]
  apply congrArg NatOrdinal.val
  apply hc
  simpa only [support_toHahnSeries] using (x.toHahnSeries.exp i.toOrd).2

/-- Coefficient birthdays at the same exponents determine the whole surreal birthday. -/
theorem birthday_eq_of_coeff_birthday_eq {x y : Surreal.{u}}
    (hc : ∀ s, (x.coeff s : Surreal.{u}).birthday =
      (y.coeff s : Surreal.{u}).birthday) : x.birthday = y.birthday := by
  have hz (s : Surreal.{u}) : x.coeff s = 0 ↔ y.coeff s = 0 := by
    rw [← Real.toSurreal_eq_zero_iff.{u}, ← birthday_eq_zero,
      ← Real.toSurreal_eq_zero_iff.{u}, ← birthday_eq_zero, hc s]
  have hs : x.support = y.support := by
    ext s
    rw [mem_support_iff, mem_support_iff]
    exact not_congr (hz s)
  apply birthday_eq_of_support_eq_of_term_cost_eq hs
  intro s _
  apply headCoefficientCost_congr
  · apply headOmegaCost_congr
    · simp only [support_trunc, hs]
    · intro w
      by_cases hsw : s < w
      · rw [coeff_trunc_of_lt hsw, coeff_trunc_of_lt hsw, hc w]
      · rw [coeff_trunc_of_ge (le_of_not_gt hsw), coeff_trunc_of_ge (le_of_not_gt hsw)]
  · exact hc s

/-- Transcendental normal-form coefficient replacement preserves the intrinsic birthday. -/
theorem birthday_normalFormBirthdayReplacement {τ : ℝ} (hτ : Transcendental ℚ τ)
    (x : Surreal.{u}) : (normalFormBirthdayReplacement τ x).birthday = x.birthday := by
  apply birthday_eq_of_coeff_birthday_eq
  exact birthday_coeff_normalFormBirthdayReplacement hτ x

end Surreal
