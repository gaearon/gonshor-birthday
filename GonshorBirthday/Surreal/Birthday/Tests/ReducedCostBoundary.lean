/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostBoundary

/-!
# Strict and equal-exponent boundary clients

A zero preceding coefficient covers a strict higher-head boundary. A negative
preceding coefficient tests the equal-exponent case with a nonempty higher head.
-/

universe u
public noncomputable section
namespace Tests
open Surreal Set

/-- Zero preceding coefficient gives the strict higher-head gap-halving conclusion. -/
theorem zero_coefficient_boundary (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s)
    {w : Surreal.{u}} (hw : w ∈ rightPrefixes (K + ω^ (appendMinus s))) :
    ∃ v ∈ rightPrefixes (K + ω^ (appendMinus s)),
      2 * (v - (K + ω^ (appendMinus s))) < w - (K + ω^ (appendMinus s)) := by
  simpa only [Real.toSurreal_zero, zero_mul, zero_add] using
    exists_rightPrefix_half_gap_of_dyadic_boundary K s hK (r := 0) (by simp)
      (by simpa only [Real.toSurreal_zero, zero_mul, zero_add] using hw)

/-- A negative preceding coefficient retains the same strict halving conclusion. -/
theorem negative_coefficient_boundary (s : Surreal.{u}) {w : Surreal.{u}}
    (hw : w ∈ rightPrefixes (ω^ (s + 1) + (-ω^ s + ω^ (appendMinus s)))) :
    ∃ v ∈ rightPrefixes (ω^ (s + 1) + (-ω^ s + ω^ (appendMinus s))),
      2 * (v - (ω^ (s + 1) + (-ω^ s + ω^ (appendMinus s)))) <
        w - (ω^ (s + 1) + (-ω^ s + ω^ (appendMinus s))) := by
  have hK : (ω^ (s + 1)).support ⊆ Ioi s := by
    rw [support_wpow]
    intro i hi
    rw [mem_singleton_iff] at hi
    subst i
    exact lt_add_one s
  simpa only [Real.toSurreal_neg, Real.toSurreal_one, neg_one_mul] using
    exists_rightPrefix_half_gap_of_dyadic_boundary (ω^ (s + 1)) s hK (r := -1)
      (by simp) (by simpa only [Real.toSurreal_neg, Real.toSurreal_one, neg_one_mul] using hw)

end Tests
