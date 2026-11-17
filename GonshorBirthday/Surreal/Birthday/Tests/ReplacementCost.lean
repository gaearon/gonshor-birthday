/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReplacementCost

import GonshorBirthday.Surreal.Birthday.Tests.HeadCost

/-!
# Replacement and native deletion clients

Replacing a nondyadic real by the common positive transcendental preserves the
deletion of the entire reciprocal-omega minus block.
-/

universe u
public noncomputable section
open Surreal
namespace Tests

/-- Positive replacement preserves the one-sign cost after every nondyadic real head. -/
theorem replacement_preserves_deleted_reciprocal_block {τ : ℝ}
    (hτpos : 0 < τ) (hτ : Transcendental ℚ τ) (r : ℝ)
    (hr : (r : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0) :
    headOmegaCost (normalFormBirthdayReplacement τ (r : Surreal.{u})) (-1) = 1 := by
  rw [headOmegaCost_normalFormBirthdayReplacement hτpos hτ]
  exact nondyadic_real_reciprocal_head_cost r hr

end Tests
