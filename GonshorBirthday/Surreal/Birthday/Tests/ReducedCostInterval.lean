/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostInterval

import GonshorBirthday.Surreal.Birthday.DyadicCoefficient
import GonshorBirthday.Surreal.Birthday.CoefficientShift

/-!
# A sharp final-interval bound with a zero coefficient predecessor

For every surreal exponent, take the output prefix minus omega to that exponent,
the final value minus half that monomial, and the common margin half the monomial.
Every original right prefix is deleted at the lower cutoff, while zero is retained
at the upper cutoff. The final plus interval has exactly the asserted lower bound.
-/

universe u
public noncomputable section
namespace Tests
open Surreal Set

/-- The negative half-monomial supplies an actual gap window attaining the interval bound. -/
theorem negative_half_monomial_gap_window (s : Surreal.{u}) :
    appendPluses (-(ω^ s)) (ω^ (plusCount s)).val = -((2 : Surreal)⁻¹ * ω^ s) ∧
      (∀ w ∈ rightPrefixes (-(ω^ s)), -(ω^ s) + (2 : Surreal)⁻¹ * ω^ s < w) ∧
      ∃ w ∈ rightPrefixes (-(ω^ s)),
        w ≤ appendPluses (-(ω^ s)) (ω^ (plusCount s)).val + (2 : Surreal)⁻¹ * ω^ s := by
  have he : appendPluses (-(ω^ s)) (ω^ (plusCount s)).val =
      -((2 : Surreal)⁻¹ * ω^ s) := by
    have h := congrArg Neg.neg (half_mul_wpow_eq_appendMinuses s)
    simpa only [appendMinuses_eq_neg, neg_neg] using h.symm
  have htw : 2 * ((2 : Surreal)⁻¹ * ω^ s) = ω^ s := by field_simp
  refine ⟨he, ?_, ?_⟩
  · intro w hw
    have hw' : -w ∈ leftPrefixes (ω^ s) := by
      simpa only [neg_neg] using (neg_mem_leftPrefixes_iff.mpr hw)
    have h := lt_real_mul_wpow_of_mem_leftPrefixes (r := (2 : ℝ)⁻¹)
      (by positivity) hw'
    simp only [Real.toSurreal_inv, Real.toSurreal_ofNat] at h
    linarith only [h, htw]
  · refine ⟨0, ?_, ?_⟩
    · simpa only [neg_zero] using
        (neg_mem_rightPrefixes_iff.mpr (zero_mem_leftPrefixes (wpow_pos s)))
    · rw [he]
      simp

/-- An arbitrary extension of `-M` crosses an old right option under translation
exactly when it extends `-M/2`. Its signs after that point can be arbitrary. -/
theorem negative_half_prefix_iff_exists_margin (s : Surreal.{u}) {e : Surreal.{u}}
    (he : birthdayTruncation e (-(ω^ s)).birthday = -(ω^ s)) :
    birthdayTruncation e (-((2 : Surreal)⁻¹ * ω^ s)).birthday = -((2 : Surreal)⁻¹ * ω^ s) ↔
      ∃ d : Surreal, 0 < d ∧ (∀ w ∈ rightPrefixes (-(ω^ s)), -(ω^ s) + d < w) ∧
        ∃ w ∈ rightPrefixes (-(ω^ s)), w ≤ e + d := by
  have hm : ((-1 : ℝ) : Surreal.{u}) = appendMinus (0 : Surreal.{u}) := by
    apply eq_appendMinus_of_birthdayTruncation_eq <;> simp
  obtain ⟨q, _, hq, hblock⟩ := exists_dyadic_head_coefficient_plus_block (0 : Surreal.{u}) s
    (by simp) (r := -1) (by norm_num) (by simp [birthday_neg, birthday_one])
  have hp : ((q.toRat : ℝ) : Surreal.{u}) = appendPlus ((-1 : ℝ) : Surreal.{u}) := by
    simpa only [Real.toSurreal_ratCast] using hq
  have hy := hblock.symm.trans (by simpa only [Real.toSurreal_neg, Real.toSurreal_one,
    neg_one_mul, zero_add] using (negative_half_monomial_gap_window s).1)
  have h := coefficient_plus_prefix_iff_exists_margin (0 : Surreal.{u}) s (by simp)
    (by norm_num : (-1 : ℝ) ≠ 0) (t := 0) (by simpa using hm) hp
    (by simpa only [Real.toSurreal_neg, Real.toSurreal_one, neg_one_mul, zero_add] using he)
  simpa only [Real.toSurreal_ratCast, hy, Real.toSurreal_neg, Real.toSurreal_one,
    neg_one_mul, zero_add] using h

open Ordinal in
example : typeLT {i : (appendMinuses (1 : Surreal.{u}) Ordinal.omega0).birthday.val.ToType |
    (1 : Surreal.{u}).birthday ≤ NatOrdinal.of i.toOrd.1 ∧
      appendMinuses (1 : Surreal.{u}) Ordinal.omega0 <
        birthdayTruncation (appendMinuses (1 : Surreal.{u}) Ordinal.omega0)
          (NatOrdinal.of i.toOrd.1)} ≤ Ordinal.omega0 :=
  minus_suffix_le_of_eq_appendMinuses rfl

end Tests
