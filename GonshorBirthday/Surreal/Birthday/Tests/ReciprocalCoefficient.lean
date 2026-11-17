/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import GonshorBirthday.Surreal.Birthday.ReciprocalCoefficient

/-!
# Public reciprocal-power coefficient clients
-/

universe u
open Surreal

example (x : Surreal.{u}) :
    (((1 : Dyadic) >>> 2) : Surreal) * ω^ x =
      appendMinuses (((1 : Dyadic) >>> 1 : Dyadic) * ω^ x) (ω^ plusCount x).val := by
  have ht := reciprocal_mul_wpow_eq_appendMinuses_step
    (r := (1 : Dyadic) >>> 2) (by decide) (by decide) x
  have he : ((1 : Dyadic) >>> 2) + ((1 : Dyadic) >>> 2) = (1 : Dyadic) >>> 1 := by decide
  simpa only [he] using ht

example (x : Surreal.{u}) :
    plusCount ((((1 : Dyadic) >>> 12) : Surreal) * ω^ x) = ω^ plusCount x :=
  plusCount_reciprocal_mul_wpow (by decide) x

example (n : ℕ) (x : Surreal.{u}) :
    (2 : Surreal)⁻¹ ^ n * ω^ x =
      appendMinuses (ω^ x) ((ω^ plusCount x).val * (n : Ordinal)) :=
  inv_two_pow_mul_wpow_eq_appendMinuses n x

example : (2 : Surreal.{u})⁻¹ ^ 12 * ω^ (appendPlus (-1 : Surreal)) =
    appendMinuses (ω^ (appendPlus (-1 : Surreal))) (Ordinal.omega0 * 12) := by
  rw [inv_two_pow_mul_wpow_eq_appendMinuses, plusCount_appendPlus]
  have he : plusCount (-(1 : Surreal.{u})) = 0 := by
    simpa using plusCount_neg_toSurreal (1 : NatOrdinal.{u})
  simp [he]

example {x v : Surreal.{u}} (hv : v ∈ rightPrefixes x) (n : ℕ) :
    (2 : Surreal)⁻¹ ^ n * ω^ v ∈ rightPrefixes (ω^ x) :=
  inv_two_pow_mul_wpow_mem_rightPrefixes hv n

example (n : ℕ) : (2 : Surreal.{u})⁻¹ ^ n ∈ rightPrefixes (ω^ (-1 : Surreal)) := by
  have hv : (0 : Surreal.{u}) ∈ rightPrefixes (-1 : Surreal) := by
    have ht := neg_mem_rightPrefixes_iff.mpr
      (zero_mem_leftPrefixes (by norm_num : (0 : Surreal.{u}) < 1))
    simpa only [neg_zero] using ht
  have ht := inv_two_pow_mul_wpow_mem_rightPrefixes hv n
  simpa only [wpow_zero, mul_one] using ht
