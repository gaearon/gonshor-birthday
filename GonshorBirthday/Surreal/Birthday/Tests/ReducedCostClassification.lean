/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostClassification

import GonshorBirthday.Surreal.Birthday.Tests.ReducedCostInterval
import GonshorBirthday.Surreal.Birthday.HeadPerturbation

/-!
# A final coefficient minus from an actual limit-prefix window

Minus omega has cofinal right-prefix birthdays. Its negative half-monomial gap
window therefore meets all hypotheses of the output classification, with no
assumed prefix-existence or sign-pattern premise.
-/

universe u
public noncomputable section
namespace Tests
open Surreal Set

/-- The negative omega monomial has cofinal right-prefix birthdays. -/
theorem negative_omega_rightPrefixes_cofinal :
    ∀ a < (-(ω^ (1 : Surreal.{u}))).birthday,
      ∃ p ∈ rightPrefixes (-(ω^ (1 : Surreal.{u}))), a < p.birthday := by
  have hw : -(ω^ (1 : Surreal.{u})) = appendMinuses (0 : Surreal) Ordinal.omega0 := by
    rw [appendMinuses_eq_neg, neg_zero, appendPluses_zero_left,
      ← NatOrdinal.wpow_one, toSurreal_wpow]
    simp
  rw [hw]
  intro a ha
  rw [birthday_appendMinuses] at ha
  have ha' := NatOrdinal.val.strictMono ha
  simp only [NatOrdinal.val_of] at ha'
  obtain ⟨β, hβ, haβ⟩ :=
    (Ordinal.lt_add_iff_of_isSuccLimit Ordinal.isSuccLimit_omega0).mp ha'
  refine ⟨appendMinuses 0 β,
    mem_rightPrefixes_iff.mpr ⟨birthdayTruncation_appendMinuses_of_lt 0 hβ,
      strictAnti_appendMinuses 0 hβ⟩, ?_⟩
  rw [birthday_appendMinuses]
  exact NatOrdinal.val.lt_iff_lt.mp (by simpa only [NatOrdinal.val_of] using haβ)

/-- The endpoint classification applies to the actual negative omega half-gap window. -/
theorem negative_omega_has_last_coefficient_minus :
    ∃ K s : Surreal.{u}, ∃ r t : ℝ,
      K.support ⊆ Ioi s ∧ r ≠ 0 ∧
      (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 ∧
      (r : Surreal.{u}) = appendMinus (t : Surreal.{u}) ∧
      -(ω^ (1 : Surreal.{u})) = K + (r : Surreal) * ω^ s := by
  have hwin := negative_half_monomial_gap_window (1 : Surreal.{u})
  exact exists_last_coefficient_minus_of_gap_window
    (birthdayTruncation_appendPluses _ _) negative_omega_rightPrefixes_cofinal hwin.2.1 hwin.2.2

/-- At the turn from `-M` to `-M/2`, every old right gap measured from the new point
exceeds a third of `M`, and the right prefix zero gives exactly half of `M`. -/
theorem negative_half_right_gaps (s : Surreal.{u}) :
    (∀ w ∈ rightPrefixes (-(ω^ s)), -(ω^ s) / 2 + (ω^ s) / 3 < w) ∧
      (0 : Surreal) ∈ rightPrefixes (-(ω^ s)) ∧ (0 : Surreal) - (-(ω^ s) / 2) = (ω^ s) / 2 := by
  constructor
  · intro w hw
    have h := fraction_wpow_lt_right_gap_head_sub_wpow (K := 0) (s := s) (by simp)
      (c := (5 / 6 : ℝ)) (by norm_num) (by simpa only [zero_sub] using hw)
    rw [zero_sub, Real.toSurreal_div,
      show ((5 : ℝ) : Surreal.{u}) = 5 from Real.toSurreal_natCast 5,
      show ((6 : ℝ) : Surreal.{u}) = 6 from Real.toSurreal_natCast 6] at h
    linarith only [h]
  · constructor
    · simpa only [zero_sub] using head_mem_rightPrefixes_sub_wpow (0 : Surreal) s (by simp)
    · ring

end Tests
