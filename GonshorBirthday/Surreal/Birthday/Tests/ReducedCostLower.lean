/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostLower

import Mathlib.Tactic.Linarith

/-!
# Output gap boundaries and unit-factor interface

The actual prefix minus one and its appended plus attain the upper gap-window
boundary. The normalized-failure interface also permits a cost-one input factor;
it does not impose positive exponents on both factors.
-/

public noncomputable section

namespace Tests

open Surreal

/-- A retained gap can equal the sum of the two thresholds. -/
theorem gap_window_attains_upper_boundary :
    ∃ w ∈ rightPrefixes (-1 : Surreal.{0}),
      max (-(appendPlus (-1))) (appendPlus (-1) - -1) < w - -1 ∧
      w - -1 = -(appendPlus (-1)) + (appendPlus (-1) - -1) := by
  let e := appendPlus (-1 : Surreal.{0})
  have hz : birthdayTruncation e (-1 : Surreal.{0}).birthday = -1 :=
    birthdayTruncation_appendPlus (-1)
  have hdel : ∀ w ∈ rightPrefixes (-1 : Surreal.{0}), -1 + -e < w := by
    intro w hw
    have hw0 : w = 0 := by
      have hb : w.birthday < 1 := by
        simpa only [birthday_neg, birthday_one] using birthday_lt_of_mem_rightPrefixes hw
      exact birthday_eq_zero.mp (NatOrdinal.lt_one_iff.mp hb)
    rw [hw0]
    have he := lt_appendPlus (-1 : Surreal.{0})
    change (-1 : Surreal.{0}) < e at he
    linarith
  have hzero : (0 : Surreal.{0}) ∈ rightPrefixes (-1) :=
    mem_rightPrefixes_iff.mpr ⟨by simp, neg_lt_zero.mpr zero_lt_one⟩
  have hne : ∃ w ∈ rightPrefixes (-1 : Surreal.{0}), w ≤ e + -e :=
    ⟨0, hzero, by simp⟩
  obtain ⟨w, hw, hlow, _, _⟩ := exists_rightPrefix_gap_window hz hdel hne
  have hw0 : w = 0 := by
    have hb : w.birthday < 1 := by
      simpa only [birthday_neg, birthday_one] using birthday_lt_of_mem_rightPrefixes hw
    exact birthday_eq_zero.mp (NatOrdinal.lt_one_iff.mp hb)
  refine ⟨w, hw, hlow, ?_⟩
  rw [hw0]
  change (0 : Surreal.{0}) - -1 = -e + (e - -1)
  linarith

/-- A pure cost-one factor is permitted in the lowered-cutoff conclusion. -/
theorem deleted_output_prefix_with_unit_factor
    (a b d : Surreal.{0}) (hd : 0 < d)
    (ih : ∀ x y : Surreal.{0}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ t : Surreal.{0}, 0 < t → reducedOmegaCost (x + y + t) (x + y) ≤
        reducedOmegaCost (x + t) x * reducedOmegaCost (y + t) y)
    {α : NatOrdinal.{0}} (hA : reducedOmegaCost (a + d) a = ω^ α)
    (hB : reducedOmegaCost (b + d) b = 1)
    (hfail : reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b <
      reducedOmegaCost (a + b + d) (a + b)) :
    ∃ c < (a + b).birthday, Order.IsSuccLimit c.val ∧
      reducedOmegaCost (a + b + d) (birthdayTruncation (a + b) c) = ω^ α ∧
      ∀ w ∈ rightPrefixes (birthdayTruncation (a + b) c),
        birthdayTruncation (a + b) c + d < w := by
  have hB' : reducedOmegaCost (b + d) b = ω^ (0 : NatOrdinal.{0}) := by
    simpa only [NatOrdinal.wpow_zero] using hB
  obtain ⟨c, hc, hlim, _, _, hcost, _, hdel, _⟩ :=
    exists_deleted_limit_prefix_of_pure_common_margin_failure a b d hd ih hA hB' hfail
  exact ⟨c, hc, hlim, by simpa only [add_zero] using hcost, hdel⟩

end Tests
