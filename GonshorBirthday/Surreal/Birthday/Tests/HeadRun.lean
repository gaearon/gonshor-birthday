/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import GonshorBirthday.Surreal.Birthday.HeadRun

/-!
# Exact arbitrary-head run clients

The last coefficient can be nondyadic or negative. The nonempty head is omega cubed;
an omega-length perturbation occurs below its last exponent two.
-/

universe u
open Surreal Set

example (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) {r : ℝ} (hr : r ≠ 0)
    {v : Surreal.{u}} (hv : v ∈ leftPrefixes s) :
    appendMinuses (K + (r : Surreal) * ω^ s) ((ω^ (plusCount v)).val * 0) =
      K + (r : Surreal) * ω^ s := by
  have ht := appendMinuses_head_real_mul_wpow K s hK hr hv 0
  simpa only [Nat.cast_zero, zero_mul, sub_zero] using ht

example : appendPluses
    (ω^ (3 : Surreal.{u}) + ((1 / 3 : ℝ) : Surreal) * ω^ (2 : Surreal)) Ordinal.omega0 =
      ω^ (3 : Surreal) + ((1 / 3 : ℝ) : Surreal) * ω^ (2 : Surreal) + ω^ (1 : Surreal) := by
  have hK : (ω^ (3 : Surreal.{u})).support ⊆ Ioi (2 : Surreal) := by
    rw [support_wpow]
    intro i hi
    rw [mem_singleton_iff] at hi
    subst i
    norm_num
  have ht := appendPluses_head_real_mul_wpow (ω^ (3 : Surreal.{u})) 2 hK
    (r := (1 / 3 : ℝ)) (by norm_num) (v := (1 : Surreal.{u})) one_mem_leftPrefixes_two 1
  have hpc : plusCount (1 : Surreal.{u}) = 1 := by
    simpa using plusCount_toSurreal (1 : NatOrdinal.{u})
  simpa [hpc] using ht

example (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s)
    {v : Surreal.{u}} (hv : v ∈ leftPrefixes s) (n : ℕ) :
    appendMinuses (K - ω^ s) ((ω^ (plusCount v)).val * (n : Ordinal)) =
      K - ω^ s - (n : Surreal) * ω^ v := by
  have ht := appendMinuses_head_real_mul_wpow K s hK (r := (-1 : ℝ)) (by norm_num) hv n
  simpa [sub_eq_add_neg] using ht
