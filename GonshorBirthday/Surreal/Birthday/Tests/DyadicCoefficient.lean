/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import GonshorBirthday.Surreal.Birthday.DyadicCoefficient

/-!
# Public half-monomial prefix and plus-count clients
-/

universe u
open Surreal

example (x : Surreal.{u}) :
    birthdayTruncation ((2 : Surreal)⁻¹ * ω^ x) (ω^ x).birthday = ω^ x :=
  birthdayTruncation_half_mul_wpow x

example : plusCount ((2 : Surreal.{u})⁻¹ * ω^ (1 : Surreal)) =
    NatOrdinal.of Ordinal.omega0 := by
  rw [plusCount_half_mul_wpow]
  have he : plusCount (1 : Surreal.{u}) = 1 := by
    simpa using plusCount_toSurreal (1 : NatOrdinal.{u})
  rw [he]
  simp

example : plusCount ((2 : Surreal.{u})⁻¹ * ω^ (-(1 : Surreal))) = 1 := by
  rw [plusCount_half_mul_wpow]
  have he : plusCount (-(1 : Surreal.{u})) = 0 := by
    simpa using plusCount_neg_toSurreal (1 : NatOrdinal.{u})
  rw [he]
  simp

example (x : Surreal.{u}) :
    (2 : Surreal)⁻¹ * ω^ x = appendMinuses (ω^ x) (ω^ plusCount x).val :=
  half_mul_wpow_eq_appendMinuses x

example : (2 : Surreal.{u})⁻¹ * ω^ (-(1 : Surreal)) =
    appendMinuses (ω^ (-(1 : Surreal))) 1 := by
  rw [half_mul_wpow_eq_appendMinuses]
  have he : plusCount (-(1 : Surreal.{u})) = 0 := by
    simpa using plusCount_neg_toSurreal (1 : NatOrdinal.{u})
  simp [he]

example : (2 : Surreal.{u})⁻¹ * ω^ (appendPlus (-1 : Surreal)) =
    appendMinuses (ω^ (appendPlus (-1 : Surreal))) Ordinal.omega0 := by
  rw [half_mul_wpow_eq_appendMinuses, plusCount_appendPlus]
  have he : plusCount (-(1 : Surreal.{u})) = 0 := by
    simpa using plusCount_neg_toSurreal (1 : NatOrdinal.{u})
  simp [he]
