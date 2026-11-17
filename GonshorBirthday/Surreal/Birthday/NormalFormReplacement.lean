/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.CoefficientReplacement
public import GonshorBirthday.Surreal.HahnSeries.Transfer

import GonshorBirthday.Surreal.HahnSeries.NormalFormMul

/-!
# Positive replacements on actual Conway normal forms

Coefficientwise birthday replacement defines an actual surreal on the same arbitrary
support. It preserves every input coefficient birthday and eliminates cancellation
from the product support. The finite convolution formula identifies each product
coefficient with the scalar comparison in `CoefficientReplacement`.

The birthday conclusions here concern individual real coefficients; they do not
assert monotonicity of the birthday of an entire surreal normal form.
-/

universe u
public noncomputable section
namespace Surreal

/-- Apply `birthdayReplacement τ` to every coefficient of the Conway normal form of `x`. -/
def normalFormBirthdayReplacement (τ : ℝ) (x : Surreal.{u}) : Surreal.{u} :=
  let f : Surreal.{u} → ℝ := fun s ↦ birthdayReplacement τ (x.coeff s)
  have hf : Function.support f ⊆ x.support := by
    simpa only [Function.comp_def, support_coeff] using
      Function.support_comp_subset (birthdayReplacement_zero τ) x.coeff
  (SurrealHahnSeries.mk f (small_subset hf)
    (Set.WellFoundedOn.subset x.wellFoundedOn_support hf)).toSurreal

/-- The normal-form replacement acts coefficientwise. -/
theorem coeff_normalFormBirthdayReplacement (τ : ℝ) (x s : Surreal.{u}) :
    (normalFormBirthdayReplacement τ x).coeff s = birthdayReplacement τ (x.coeff s) := by
  rw [normalFormBirthdayReplacement, SurrealHahnSeries.coeff_toSurreal,
    SurrealHahnSeries.coeff_mk]

/-- Positive normal-form replacement preserves the entire support. -/
theorem support_normalFormBirthdayReplacement {τ : ℝ} (hτ : 0 < τ) (x : Surreal.{u}) :
    (normalFormBirthdayReplacement τ x).support = x.support := by
  rw [← support_coeff, ← support_coeff]
  ext s
  simp only [Function.mem_support, coeff_normalFormBirthdayReplacement,
    ne_eq, birthdayReplacement_eq_zero_iff hτ]

/-- Transcendental replacement preserves the birthday of every input coefficient. -/
theorem birthday_coeff_normalFormBirthdayReplacement {τ : ℝ} (hτ : Transcendental ℚ τ)
    (x s : Surreal.{u}) :
    (((normalFormBirthdayReplacement τ x).coeff s : ℝ) : Surreal.{u}).birthday =
      ((x.coeff s : ℝ) : Surreal.{u}).birthday := by
  rw [coeff_normalFormBirthdayReplacement, birthday_birthdayReplacement τ _ hτ]

/-- Every supported coefficient becomes positive. -/
theorem coeff_normalFormBirthdayReplacement_pos {τ : ℝ} (hτ : 0 < τ)
    (x : Surreal.{u}) {s : Surreal.{u}} (hs : s ∈ x.support) :
    0 < (normalFormBirthdayReplacement τ x).coeff s := by
  rw [coeff_normalFormBirthdayReplacement]
  apply birthdayReplacement_pos hτ
  rwa [← support_coeff] at hs

/-- Normal-form replacement of an embedded real is its scalar replacement. -/
theorem normalFormBirthdayReplacement_realCast (τ r : ℝ) :
    normalFormBirthdayReplacement τ (r : Surreal.{u}) =
      (birthdayReplacement τ r : Surreal.{u}) := by
  apply toHahnSeries_inj.mp
  apply SurrealHahnSeries.ext
  funext s
  rw [coeff_toHahnSeries, coeff_toHahnSeries, coeff_normalFormBirthdayReplacement,
    coeff_realCast, coeff_realCast]
  by_cases hs : s = 0
  · subst s
    simp
  · simp [hs]

/-- The zero surreal is fixed by normal-form replacement. -/
theorem normalFormBirthdayReplacement_zero (τ : ℝ) :
    normalFormBirthdayReplacement τ (0 : Surreal.{u}) = 0 := by
  simpa only [Real.toSurreal_zero, birthdayReplacement_zero] using
    normalFormBirthdayReplacement_realCast.{u} τ 0

/-- All coefficients of a positive normal-form replacement are nonnegative. -/
theorem coeff_normalFormBirthdayReplacement_nonneg {τ : ℝ} (hτ : 0 < τ)
    (x s : Surreal.{u}) : 0 ≤ (normalFormBirthdayReplacement τ x).coeff s := by
  rw [coeff_normalFormBirthdayReplacement]
  by_cases hs : x.coeff s = 0
  · rw [hs, birthdayReplacement_zero]
  · exact (birthdayReplacement_pos hτ hs).le

/-- Every sum of input support exponents survives in the replacement product. -/
theorem mem_support_mul_normalFormBirthdayReplacement {τ : ℝ} (hτ : 0 < τ)
    (x y s : Surreal.{u}) :
    s ∈ (normalFormBirthdayReplacement τ x * normalFormBirthdayReplacement τ y).support ↔
      ∃ a ∈ x.support, ∃ b ∈ y.support, a + b = s := by
  constructor
  · intro hs
    rw [← support_toHahnSeries, toHahnSeries_mul] at hs
    obtain ⟨a, ha, b, hb, he⟩ := SurrealHahnSeries.exists_add_eq_of_mem_support_mul hs
    simp only [support_toHahnSeries, support_normalFormBirthdayReplacement hτ] at ha hb
    exact ⟨a, ha, b, hb, he⟩
  · rintro ⟨a, ha, b, hb, he⟩
    rw [← support_coeff]
    change (normalFormBirthdayReplacement τ x * normalFormBirthdayReplacement τ y).coeff s ≠ 0
    apply ne_of_gt
    rw [coeff_mul]
    apply (Finset.sum_pos_iff_of_nonneg (fun p _ ↦ mul_nonneg
      (coeff_normalFormBirthdayReplacement_nonneg hτ x p.1)
      (coeff_normalFormBirthdayReplacement_nonneg hτ y p.2))).mpr
    refine ⟨(a, b), ?_, mul_pos
      (coeff_normalFormBirthdayReplacement_pos hτ x ha)
      (coeff_normalFormBirthdayReplacement_pos hτ y hb)⟩
    apply (SurrealHahnSeries.mem_supportAntidiagonal _ _ _ _).mpr
    simpa only [support_toHahnSeries, support_normalFormBirthdayReplacement hτ] using
      And.intro ha (And.intro hb he)

/-- Each original product coefficient has birthday at most its replacement product coefficient. -/
theorem birthday_coeff_mul_le_normalFormBirthdayReplacement {τ : ℝ}
    (hτpos : 0 < τ) (hτ : Transcendental ℚ τ) (x y s : Surreal.{u}) :
    (((x * y).coeff s : ℝ) : Surreal.{u}).birthday ≤
      (((normalFormBirthdayReplacement τ x * normalFormBirthdayReplacement τ y).coeff s : ℝ) :
        Surreal.{u}).birthday := by
  have he : SurrealHahnSeries.supportAntidiagonal
      (normalFormBirthdayReplacement τ x).toHahnSeries
      (normalFormBirthdayReplacement τ y).toHahnSeries s =
      SurrealHahnSeries.supportAntidiagonal x.toHahnSeries y.toHahnSeries s := by
    apply SurrealHahnSeries.supportAntidiagonal_eq_of_support_eq
    · simp only [support_toHahnSeries, support_normalFormBirthdayReplacement hτpos]
    · simp only [support_toHahnSeries, support_normalFormBirthdayReplacement hτpos]
  rw [coeff_mul, coeff_mul, he]
  simp only [coeff_normalFormBirthdayReplacement]
  apply birthday_sum_mul_le_replacement _ _ _ hτ
  intro p hp
  obtain ⟨ha, hb, _⟩ := (SurrealHahnSeries.mem_supportAntidiagonal _ _ _ _).mp hp
  simpa only [support_toHahnSeries, ← support_coeff, Function.mem_support] using And.intro ha hb

end Surreal
