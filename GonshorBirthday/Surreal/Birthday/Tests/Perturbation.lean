/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import GonshorBirthday.Surreal.Birthday.Perturbation

/-!
# Dyadic monomial perturbation clients

Both coefficient signs and both run orientations occur. The negative unit example
adds an infinite pure plus block, while the zero multiplier gives an empty run.
-/

universe u
open Surreal

example (r : ℝ) (s v : Surreal.{u}) :
    appendMinuses ((r : Surreal) * ω^ s) ((ω^ (plusCount v)).val * 0) =
      (r : Surreal) * ω^ s := by
  simp

example {s v : Surreal.{u}} (hv : v ∈ leftPrefixes s) (n : ℕ) :
    appendPluses (-ω^ s) ((ω^ (plusCount v)).val * (n : Ordinal)) =
      -ω^ s + (n : Surreal) * ω^ v := by
  have ht := appendPluses_real_mul_wpow_natCast_mul_wpow (r := (-1 : ℝ))
    (by norm_num) (by simp) hv n
  simpa using ht

example : appendPluses (-ω^ (2 : Surreal.{u})) Ordinal.omega0 =
    -ω^ (2 : Surreal) + ω^ (1 : Surreal) := by
  have ht := appendPluses_real_mul_wpow_natCast_mul_wpow (r := (-1 : ℝ))
    (by norm_num) (by simp)
    (s := (2 : Surreal.{u})) (v := (1 : Surreal.{u})) one_mem_leftPrefixes_two 1
  have hpc : plusCount (1 : Surreal.{u}) = 1 := by
    simpa using plusCount_toSurreal (1 : NatOrdinal.{u})
  simpa [hpc] using ht
