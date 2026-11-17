/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.CoefficientBlock

/-!
# Final coefficient block clients

The negative coefficient minus two has nonzero predecessor minus one. Its right
prefixes are genuinely cofinal, witnessed independently by the checked unheaded word.
-/

universe u
open Surreal Set

private theorem cofinal_minus_omega (W : Surreal.{u}) :
    ∀ a < (appendMinuses W Ordinal.omega0).birthday,
      ∃ p ∈ rightPrefixes (appendMinuses W Ordinal.omega0), a < p.birthday := by
  intro a ha
  rw [birthday_appendMinuses] at ha
  have ha' := NatOrdinal.val.strictMono ha
  simp only [NatOrdinal.val_of] at ha'
  obtain ⟨β, hβ, haβ⟩ :=
    (Ordinal.lt_add_iff_of_isSuccLimit Ordinal.isSuccLimit_omega0).mp ha'
  refine ⟨appendMinuses W β,
    mem_rightPrefixes_iff.mpr ⟨birthdayTruncation_appendMinuses_of_lt W hβ,
      strictAnti_appendMinuses W hβ⟩, ?_⟩
  rw [birthday_appendMinuses]
  exact NatOrdinal.val.lt_iff_lt.mp (by simpa only [NatOrdinal.val_of] using haβ)

/-- The negative coefficient minus two has a genuine omega-long final minus block. -/
public theorem Tests.negative_two_wpow_block :
    appendMinuses (-ω^ (1 : Surreal.{u})) Ordinal.omega0 =
    ((-2 : ℝ) : Surreal) * ω^ (1 : Surreal) := by
  have hpc : plusCount (1 : Surreal.{u}) = 1 := by
    simpa using plusCount_toSurreal (1 : NatOrdinal.{u})
  have h2 : (2 : Surreal.{u}) * ω^ (1 : Surreal) =
      appendPluses (ω^ (1 : Surreal)) Ordinal.omega0 := by
    simpa [hpc] using natCast_mul_wpow_eq_appendPluses (1 : Surreal.{u}) 1
  have hneg : ((-2 : ℝ) : Surreal.{u}) * ω^ (1 : Surreal) =
      appendMinuses (-ω^ (1 : Surreal)) Ordinal.omega0 := by
    rw [appendMinuses_eq_neg, neg_neg, ← h2]
    norm_num
  have hs : ((-2 : ℝ) : Surreal.{u}) = appendMinus ((-1 : ℝ) : Surreal.{u}) := by
    apply eq_appendMinus_of_birthdayTruncation_eq
    · have hp : birthdayTruncation (2 : Surreal.{u}) (1 : Surreal).birthday = 1 := by
        simpa only [birthday_one] using birthdayTruncation_two_one.{u}
      simpa using birthdayTruncation_neg_of_eq hp
    · norm_num
    · norm_num
  have hcof : ∀ a < (((-2 : ℝ) : Surreal.{u}) * ω^ (1 : Surreal)).birthday,
      ∃ p ∈ rightPrefixes (((-2 : ℝ) : Surreal.{u}) * ω^ (1 : Surreal)), a < p.birthday := by
    rw [hneg]
    exact cofinal_minus_omega _
  have ht := appendMinuses_head_real_mul_wpow_of_cofinal_rightPrefixes 0 1 (by simp)
    (t := (-1 : ℝ)) (by norm_num) hs (by simpa using hcof)
  simpa [hpc] using ht

example (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {r t : ℝ} (ht : t ≠ 0)
    (hsrc : (r : Surreal.{u}) = appendPlus (t : Surreal.{u}))
    (hcof : ∀ a < (K + (r : Surreal) * ω^ s).birthday,
      ∃ p ∈ leftPrefixes (K + (r : Surreal) * ω^ s), a < p.birthday) :
    appendPluses (K + (t : Surreal) * ω^ s) (ω^ (plusCount s)).val =
      K + (r : Surreal) * ω^ s :=
  appendPluses_head_real_mul_wpow_of_cofinal_leftPrefixes K s hK ht hsrc hcof

example : ∃ t : ℝ, t ≠ 0 ∧
    (((-2 : ℝ) : Surreal.{u}) = appendPlus (t : Surreal.{u}) ∨
      ((-2 : ℝ) : Surreal.{u}) = appendMinus (t : Surreal.{u})) := by
  apply exists_nonzero_real_predecessor_of_finite_birthday <;> norm_num
  exact_mod_cast NatOrdinal.natCast_lt_omega0 2

example (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {r : ℝ} (hr : r ≠ 0)
    (hf : (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    (hL : ∀ a < (K + (r : Surreal) * ω^ s).birthday,
      ∃ p ∈ leftPrefixes (K + (r : Surreal) * ω^ s), a < p.birthday)
    (hR : ∀ a < (K + (r : Surreal) * ω^ s).birthday,
      ∃ p ∈ rightPrefixes (K + (r : Surreal) * ω^ s), a < p.birthday) :
    r = 1 ∨ r = -1 :=
  head_real_coefficient_eq_one_or_neg_one_of_both_cofinal K s hK hr hf hL hR
