/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadBoundary

/-!
# Exact retained boundary words with zero and negative coefficients
-/

universe u
public section
open Surreal Set
namespace Tests

/-- Every negative dyadic real head uses the full word at its own plus successor. -/
theorem negative_real_head_reciprocal_word {r : ℝ} (hr : r < 0)
    (hf : (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) :
    appendMinuses (appendPlus (r : Surreal.{u})) Ordinal.omega0 =
      (r : Surreal.{u}) + ω^ (-1 : Surreal) := by
  have hH : (r : Surreal.{u}).support ⊆ Ici (0 : Surreal) := by
    intro v hv
    by_cases hv0 : v = 0
    · rw [hv0]
      exact le_rfl
    · have hc : (r : Surreal.{u}).coeff v = 0 := by simp [coeff_realCast, hv0]
      exact (mem_support_iff.mp hv hc).elim
  have hc : (r : Surreal.{u}).coeff 0 ≠ 0 := by
    simpa only [coeff_realCast, Pi.single_eq_same] using hr.ne
  have hf' : ((r : Surreal.{u}).coeff 0 : Surreal.{u}).birthday <
      NatOrdinal.of Ordinal.omega0 := by
    simpa only [coeff_realCast, Pi.single_eq_same] using hf
  have he : (-1 : Surreal.{u}) = appendMinus (0 : Surreal) := by
    apply eq_appendMinus_of_birthdayTruncation_eq
    · simp only [birthday_zero, birthdayTruncation_zero]
    · simp only [birthday_neg, birthday_one, birthday_zero, zero_add]
    · exact neg_lt_zero.mpr (zero_lt_one : (0 : Surreal.{u}) < 1)
  have h := head_boundary_appendMinus_word hH hc hf'
  simpa only [plusCount_zero, NatOrdinal.wpow_zero, NatOrdinal.val_one, one_mul,
    appendPluses_one, ← he] using h

/-- At coefficient zero the exact initial transition follows from earlier deletion. -/
theorem zero_coefficient_first_boundary_word {H w : Surreal.{u}}
    (hH : H.support ⊆ Ici w) (hc : H.coeff w = 0)
    (hfirst : ∀ v ∈ rightPrefixes w, ¬ (H.support ⊆ Ici v ∧
      (H.coeff v : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)) :
    appendMinuses (appendPluses H (ω^ (plusCount w)).val)
      ((ω^ (plusCount w)).val * Ordinal.omega0) = H + ω^ appendMinus w := by
  apply head_first_retained_appendMinus_word hH _ hfirst
  rw [hc, Real.toSurreal_zero, birthday_zero]
  exact_mod_cast Ordinal.omega0_pos

end Tests
