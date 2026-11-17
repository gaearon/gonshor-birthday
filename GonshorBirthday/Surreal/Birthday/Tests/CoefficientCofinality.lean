/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import GonshorBirthday.Surreal.Birthday.CoefficientCofinality

/-!
# Public real coefficient product cofinality clients
-/

universe u
open Surreal

example {r : ℝ} (hr : 0 < r) {x z : Surreal.{u}}
    (hz : z ∈ rightPrefixes ((r : Surreal) * ω^ x)) :
    (∃ a ∈ rightPrefixes (ω^ x), a ≤ z) ∨
      ∃ s : ℝ, 0 < s ∧ (s : Surreal.{u}) ∈ rightPrefixes (r : Surreal.{u}) ∧
        ∃ a ∈ leftPrefixes (ω^ x), (s : Surreal) * ω^ x - a ≤ z :=
  exists_rightPrefixes_real_mul_wpow_le hr hz
