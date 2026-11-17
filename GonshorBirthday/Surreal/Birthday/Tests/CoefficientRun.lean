/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import GonshorBirthday.Surreal.Birthday.CoefficientRun

/-!
# Unconditional headed coefficient block clients

The one-sign case is a genuine successor birthday, where left birthdays are not
cofinal. Negative coefficients and actual dyadic endpoints are included as well.
-/

universe u
open Surreal Set

example : appendPluses (ω^ (1 : Surreal.{u}) + 1) 1 = ω^ (1 : Surreal) + 2 := by
  have hK : (ω^ (1 : Surreal.{u})).support ⊆ Ioi (0 : Surreal) := by
    rw [support_wpow]
    intro i hi
    rw [mem_singleton_iff] at hi
    subst i
    norm_num
  have hs : ((2 : ℝ) : Surreal.{u}) = appendPlus ((1 : ℝ) : Surreal.{u}) := by
    apply eq_appendPlus_of_birthdayTruncation_eq
    · simpa using birthdayTruncation_two_one.{u}
    · norm_num
    · norm_num
  have ht := appendPluses_head_real_mul_wpow_of_appendPlus (ω^ (1 : Surreal.{u})) 0 hK
    (t := (1 : ℝ)) (by norm_num) hs
  simpa using ht

example (W : Surreal.{u}) :
    ¬ (∀ a < (appendPlus W).birthday,
      ∃ p ∈ leftPrefixes (appendPlus W), a < p.birthday) := by
  intro hcof
  have hW : W.birthday < (appendPlus W).birthday := by
    rw [birthday_appendPlus]
    exact lt_add_one _
  obtain ⟨p, hp, hbp⟩ := hcof _ hW
  have hp' := birthday_lt_of_mem_leftPrefixes hp
  rw [birthday_appendPlus] at hp'
  exact hbp.not_ge (Order.lt_add_one_iff.mp hp')

example (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) :
    appendMinuses (K - ω^ s) (ω^ (plusCount s)).val =
      K + ((-2 : ℝ) : Surreal) * ω^ s := by
  have hs : ((-2 : ℝ) : Surreal.{u}) = appendMinus ((-1 : ℝ) : Surreal.{u}) := by
    apply eq_appendMinus_of_birthdayTruncation_eq
    · have hp : birthdayTruncation (2 : Surreal.{u}) (1 : Surreal).birthday = 1 := by
        simpa only [birthday_one] using birthdayTruncation_two_one.{u}
      simpa using birthdayTruncation_neg_of_eq hp
    · norm_num
    · norm_num
  have ht := appendMinuses_head_real_mul_wpow_of_appendMinus K s hK
    (t := (-1 : ℝ)) (by norm_num) hs
  simpa [sub_eq_add_neg] using ht

example (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) :
    ∃ q : Dyadic, q ≠ 0 ∧ (q : Surreal.{u}) = appendPlus ((-1 : ℝ) : Surreal.{u}) ∧
      appendPluses (K - ω^ s) (ω^ (plusCount s)).val = K + (q : Surreal) * ω^ s := by
  have ht := exists_dyadic_head_coefficient_plus_block K s hK (r := (-1 : ℝ))
    (by norm_num) (by simp)
  simpa [sub_eq_add_neg] using ht
