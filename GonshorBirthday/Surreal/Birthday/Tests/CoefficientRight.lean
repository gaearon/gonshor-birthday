/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import GonshorBirthday.Surreal.Birthday.CoefficientRight
import GonshorBirthday.Surreal.Birthday.ReciprocalCoefficient
import GonshorBirthday.Surreal.Birthday.Perturbation

/-!
# Right-prefix preservation at coefficient plus successors

A negative real predecessor and arbitrary higher head are included. The zero
predecessor is excluded necessarily: a positive infinitesimal introduces a right prefix.
-/

universe u
open Surreal Set

example (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) :
    ∃ r : ℝ, -1 < r ∧ r < 0 ∧ rightPrefixes (K + (r : Surreal) * ω^ s) =
      rightPrefixes (K - ω^ s) := by
  obtain ⟨r, hr⟩ := exists_real_appendPlus_of_birthday_lt_omega0
    (r := (-1 : ℝ)) (by simp)
  have hrl : (-1 : ℝ) < r := by
    apply Real.toSurreal_lt_iff.mp
    rw [hr]
    simpa using lt_appendPlus (-1 : Surreal.{u})
  have hr0 : r < 0 := by
    apply Real.toSurreal_neg_iff.mp
    rw [hr]
    apply appendPlus_lt_of_mem_rightPrefixes
    exact mem_rightPrefixes_iff.mpr ⟨by simp, by norm_num⟩
  refine ⟨r, hrl, hr0, ?_⟩
  have ht := rightPrefixes_head_real_mul_wpow_appendPlus K s hK
    (t := (-1 : ℝ)) (by norm_num) hr
  simpa [sub_eq_add_neg] using ht

example : ∃ p : Surreal.{u}, p ∈ rightPrefixes (ω^ (appendMinus (0 : Surreal))) ∧
    p ∉ rightPrefixes (0 : Surreal) := by
  have hw : (0 : Surreal.{u}) ∈ rightPrefixes (appendMinus 0) :=
    mem_rightPrefixes_iff.mpr ⟨birthdayTruncation_appendMinus 0, appendMinus_lt 0⟩
  have hp := inv_two_pow_mul_wpow_mem_rightPrefixes hw 0
  exact ⟨1, by simpa using hp, by simp⟩

example (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {r : ℝ} (hr : r ≠ 0)
    (hf : (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    (hcof : ∀ a < (K + (r : Surreal) * ω^ s).birthday,
      ∃ p ∈ rightPrefixes (K + (r : Surreal) * ω^ s), a < p.birthday) :
    r = 1 ∨ ∃ t : ℝ, (r : Surreal.{u}) = appendMinus (t : Surreal.{u}) :=
  real_coefficient_eq_one_or_minus_successor_of_head_rightPrefixes_cofinal K s hK hr hf hcof
