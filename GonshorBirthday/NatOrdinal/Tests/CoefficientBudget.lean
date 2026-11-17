/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.NatOrdinal.CoefficientBudget
public import GonshorBirthday.NatOrdinal.CantorSupport

import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.Tactic.NormNum

/-!
# Finite fibres and strict limit budgets

Three unit coefficient cells need two additional first-sign blocks after merging.
An infinite cell can absorb a finite earlier cell. Ordinary repeated-product
budgets can be strictly smaller than the natural product at their limit.
-/

public noncomputable section

namespace Tests

open NatOrdinal Ordinal

/-- Three coefficient-one cells supply two further coefficient signs when merged. -/
theorem three_unit_cells (G H : NatOrdinal.{0}) (hH : H ≤ G) :
    of (G.val + H.val * 2) ≤ of (G.val + G.val + G.val) := by
  have h := coefficient_fibre_natCast_le hH [0, 0, 0] (by simp)
  norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.cast_zero, mul_zero, add_zero] at h
  simpa only [add_assoc] using h

/-- A mixed fibre preserves its infinite cell despite an absorbed finite prefix. -/
theorem finite_infinite_finite_cells :
    (([2, Ordinal.omega0, 3].map (fun t : Ordinal.{0} ↦ 1 + t)).sum) =
      Ordinal.omega0 + 4 := by
  norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    Ordinal.one_add_omega0, ← add_assoc]
  rw [Ordinal.add_omega0 (by simp)]

/-- The ordinary limit of finite product blocks can be strictly below the natural product. -/
theorem repeated_product_limit_is_strict :
    (of ((2 : Ordinal.{0}) * Ordinal.omega0) : NatOrdinal.{0}) <
      of Ordinal.omega0 * 2 := by
  have he : (2 : Ordinal.{0}) * Ordinal.omega0 = Ordinal.omega0 := by
    exact Ordinal.mul_omega0 (by simp) (by simp)
  rw [he, mul_two]
  exact lt_add_of_pos_right _ (of.strictMono Ordinal.omega0_pos)

/-- An input with a lower Cantor term still admits the coefficient-cell estimate. -/
theorem lower_cantor_term_cell :
    let w : NatOrdinal.{0} := of Ordinal.omega0
    0 ∈ cantorSupport (w + 1) ∧
      (of (Ordinal.omega0 + 2) : NatOrdinal.{0}) ≤
        of (Ordinal.omega0 + Ordinal.omega0) := by
  let w : NatOrdinal.{0} := of Ordinal.omega0
  constructor
  · rw [cantorSupport_add]
    exact Finset.mem_union_right _ (by simp)
  · have h := coefficient_cell_natCast_le (A := w + 1) (B := 1)
      (P := w) (Q := 1) (G := w + 1) (H := 1)
      (le_add_of_nonneg_right bot_le) le_rfl (by simp)
      (by simpa only [mul_one, of_one] using of.monotone Ordinal.one_lt_omega0.le) 1 0
    simpa only [w, val_add_one, val_of, val_one, one_mul, mul_one, mul_zero, add_zero,
      Nat.cast_one, Nat.cast_zero, Nat.add_zero, Nat.mul_zero, add_assoc,
      Ordinal.one_add_omega0, one_add_one_eq_two, of_one] using h

end Tests
