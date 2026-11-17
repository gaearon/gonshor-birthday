/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostBound

/-!
# Clients of the unrestricted reduced-cost addition bound

The cell interface permits a still smaller output cutoff. Further clients use an
arbitrary monomial margin and exact cancellation. Both zero input margins are
included in the unequal-cutoff theorem.
-/

universe u
public noncomputable section
namespace Tests
open Surreal

/-- An auxiliary output cutoff satisfying both input constraints obeys the same budget. -/
theorem reduced_cost_cell (a b A B C : Surreal.{u}) (ha : a ≤ A) (hb : b ≤ B)
    (hCa : C ≤ A + b) (hCb : C ≤ a + B) :
    reducedOmegaCost C (a + b) ≤ reducedOmegaCost A a * reducedOmegaCost B b :=
  (reducedOmegaCost_mono (a + b) (le_min hCa hCb)).trans
    (reducedOmegaCost_add_le a b A B ha hb)

example (a b s : Surreal.{u}) :
    reducedOmegaCost (a + b + ω^ (-s)) (a + b) ≤
      reducedOmegaCost (a + ω^ (-s)) a * reducedOmegaCost (b + ω^ (-s)) b :=
  reducedOmegaCost_add_common_margin_le a b _ (wpow_pos _)

example (a A B : Surreal.{u}) (ha : a ≤ A) (hb : -a ≤ B) :
    1 ≤ reducedOmegaCost A a * reducedOmegaCost B (-a) := by
  simpa only [add_neg_cancel, reducedOmegaCost_zero] using
    reducedOmegaCost_add_le a (-a) A B ha hb

example (a b : Surreal.{u}) :
    reducedOmegaCost (a + b) (a + b) ≤ reducedOmegaCost a a * reducedOmegaCost b b := by
  simpa only [min_self] using reducedOmegaCost_add_le a b a b le_rfl le_rfl

end Tests
