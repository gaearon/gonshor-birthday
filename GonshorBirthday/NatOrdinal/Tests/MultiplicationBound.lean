/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.NatOrdinal.MultiplicationBound

import Mathlib.Tactic.NormNum

/-!
# The product gap at omega

These estimates exhibit a strict gap between every product `n ⊗ (ω+1)`, for `n<ω`,
and `ω ⊗ (ω+1)`. They separate the uniform-bound argument from false continuity.
-/

universe u

public noncomputable section

namespace Tests

open NatOrdinal

/-- Every product below the first omega factor stays below omega squared. -/
theorem naturalProduct_below_omega (x : NatOrdinal.{u}) (hx : x < of Ordinal.omega0) :
    x * (of Ordinal.omega0 + 1) < ω^ (2 : NatOrdinal.{u}) := by
  have hω : of Ordinal.omega0 < ω^ (1 + 1 : NatOrdinal.{u}) := by
    simpa only [wpow_one] using (wpow_lt_wpow.mpr (show (1 : NatOrdinal.{u}) < 1 + 1 by simp))
  have h1 : (1 : NatOrdinal.{u}) < ω^ (1 + 1 : NatOrdinal.{u}) := by
    simpa only [wpow_zero] using (wpow_lt_wpow.mpr (show (0 : NatOrdinal.{u}) < 1 + 1 by simp))
  have htwo : (1 : NatOrdinal.{u}) + 1 = 2 := by norm_num
  simpa only [htwo] using mul_lt_wpow_add (a := 1) (d := 1) (by simpa using hx)
    (add_lt_wpow hω h1)

/-- The full natural product exceeds that same uniform bound. -/
theorem naturalProduct_omega_gap :
    ω^ (2 : NatOrdinal.{u}) < of Ordinal.omega0 * (of Ordinal.omega0 + 1) := by
  have htwo : (1 : NatOrdinal.{u}) + 1 = 2 := by norm_num
  simpa only [htwo, zero_mul, zero_add, wpow_one] using
    add_wpow_lt_mul_of_wpow_lt (a := 1) (d := 1) 0
    (show ω^ (1 : NatOrdinal.{u}) < of Ordinal.omega0 + 1 by simp)

end Tests
