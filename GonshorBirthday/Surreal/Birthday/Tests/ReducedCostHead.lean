/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import GonshorBirthday.Surreal.Birthday.ReducedCostHead

/-! # A supported-scale boundary for younger-prefix gaps -/

open Surreal

/-- A younger-prefix gap can have exactly a supported scale, so the comparison is non-strict. -/
example : ∃ s ∈ (-1 : Surreal.{0}).support, s = (0 - (-1 : Surreal.{0})).wlog := by
  simp
