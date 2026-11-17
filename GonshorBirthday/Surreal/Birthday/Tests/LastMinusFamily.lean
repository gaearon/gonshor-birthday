/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import GonshorBirthday.Surreal.Birthday.LastMinusFamily

/-!
# Last coefficient minus family clients

The zero predecessor and an arbitrary nonzero predecessor use the same public family.
Every witness has a positive multiplier and is an actual canonical right prefix.
-/

universe u
open Surreal Set

example (K x : Surreal.{u}) (hK : K.support ⊆ Ioi x)
    (hcof : ∀ a < (K - ω^ x).birthday,
      ∃ w ∈ rightPrefixes (K - ω^ x), a < w.birthday)
    {a : NatOrdinal.{u}} (ha : a < (K - ω^ x).birthday) :
    ∃ v ∈ leftPrefixes x, ∃ n : ℕ, 0 < n ∧
      K - (n : Surreal) * ω^ v ∈ rightPrefixes (K - ω^ x) ∧
      a < (K - (n : Surreal) * ω^ v).birthday := by
  have hs : ((-1 : ℝ) : Surreal.{u}) = appendMinus (0 : Surreal.{u}) := by
    apply eq_appendMinus_of_birthdayTruncation_eq
    · simp
    · simp
    · norm_num
  have hh := head_real_mul_wpow_sub_natCast_mul_wpow_pos_cofinal K x hK
    (r := (0 : ℝ)) (s := (-1 : ℝ)) (by simpa using hs)
  simpa [sub_eq_add_neg] using hh (by simpa [sub_eq_add_neg] using hcof) a
    (by simpa [sub_eq_add_neg] using ha)

example (K x : Surreal.{u}) (hK : K.support ⊆ Ioi x) {r s : ℝ}
    (hsrc : (s : Surreal.{u}) = appendMinus (r : Surreal.{u}))
    (hcof : ∀ a < (K + (s : Surreal) * ω^ x).birthday,
      ∃ w ∈ rightPrefixes (K + (s : Surreal) * ω^ x), a < w.birthday)
    {a : NatOrdinal.{u}} (ha : a < (K + (s : Surreal) * ω^ x).birthday) :
    ∃ v ∈ leftPrefixes x, ∃ n : ℕ, 0 < n ∧
      K + ((r : Surreal) * ω^ x - (n : Surreal) * ω^ v) ∈
        rightPrefixes (K + (s : Surreal) * ω^ x) ∧
      a < (K + ((r : Surreal) * ω^ x - (n : Surreal) * ω^ v)).birthday :=
  head_real_mul_wpow_sub_natCast_mul_wpow_pos_cofinal K x hK hsrc hcof a ha
