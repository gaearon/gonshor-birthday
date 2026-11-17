/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostAddition

import GonshorBirthday.Surreal.Birthday.Addition
import Mathlib.Tactic.NormNum

/-!
# Reduced addition estimates at a cutoff boundary

The common-margin estimate for a zero summand includes unequal cutoffs. At exponent
minus one, a unit margin on the zero summand puts the output exactly at the
minus-retention boundary. A zero margin drops the output cost from omega to one
while the input budget stays omega.
-/

public noncomputable section

namespace Tests

open Surreal

/-- A zero summand admits every unequal pair of nonnegative margins. -/
theorem zero_summand_unequal_cutoffs (a A B : Surreal.{0}) (ha : a ≤ A) (hB : 0 ≤ B) :
    reducedOmegaCost (min A (a + B)) a ≤ reducedOmegaCost A a := by
  have h : ∀ d : Surreal.{0}, 0 < d →
      reducedOmegaCost (a + 0 + d) (a + 0) ≤
        reducedOmegaCost (a + d) a * reducedOmegaCost (0 + d) 0 := by
    intro d _
    simp only [add_zero, reducedOmegaCost_zero, mul_one, le_refl]
  simpa only [add_zero, reducedOmegaCost_zero, mul_one] using
    (reducedOmegaCost_add_iff_common_margin a 0).mp h A B ha hB

/-- A vanishing second margin deletes the minus, while a unit margin retains it. -/
theorem zero_margin_changes_retention :
    reducedOmegaCost (min (0 : Surreal.{0}) (-1 + 0)) (-1) = 1 ∧
    reducedOmegaCost (min (0 : Surreal.{0}) (-1 + 1)) (-1) =
      NatOrdinal.of Ordinal.omega0 ∧
    reducedOmegaCost (0 : Surreal.{0}) (-1) = NatOrdinal.of Ordinal.omega0 := by
  simp only [reducedOmegaCost_neg_one]
  norm_num

/-- Cancellation leaves only the initial unit although one input still has an omega cost. -/
theorem cancelled_output_baseline :
    reducedOmegaCost ((1 : Surreal.{0}) + -1) (1 + -1) = 1 ∧
    reducedOmegaCost (1 : Surreal.{0}) 1 * reducedOmegaCost (-1) (-1) =
      NatOrdinal.of Ordinal.omega0 := by
  simp only [reducedOmegaCost_neg_one, reducedOmegaCost_one]
  norm_num

end Tests
