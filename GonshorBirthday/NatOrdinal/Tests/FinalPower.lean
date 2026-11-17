/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.NatOrdinal.FinalPower

import Mathlib.Tactic.NormNum

/-!
# A final power below a leading term and a repeated lower term

The final-power decomposition of omega squared plus twice omega removes one
omega, preserving the leading term and the other copy of the lower term.
-/

public noncomputable section

namespace Tests

open NatOrdinal Ordinal

/-- The final copy is omega, not the leading omega squared or the whole lower Cantor term. -/
theorem final_copy_of_nonprincipal_limit :
    ∃ x₀ p : NatOrdinal.{0},
      (ω^ (2 : NatOrdinal.{0}) + ω^ (1 : NatOrdinal.{0}) * 2) =
        NatOrdinal.of (x₀.val + (ω^ p).val) ∧
      p = 1 ∧ x₀ = ω^ (2 : NatOrdinal.{0}) + ω^ (1 : NatOrdinal.{0}) := by
  let x : NatOrdinal.{0} := ω^ (2 : NatOrdinal.{0}) + ω^ (1 : NatOrdinal.{0}) * 2
  have hx : x ≠ 0 := by
    apply ne_of_gt
    exact (wpow_pos (2 : NatOrdinal.{0})).trans_le
      (le_add_of_nonneg_right (bot_le : (0 : NatOrdinal.{0}) ≤ ω^ (1 : NatOrdinal.{0}) * 2))
  obtain ⟨x₀, p, he, hadd, hp⟩ := exists_final_wpow hx
  have hs : cantorSupport x = {2, 1} := by
    simp only [x, mul_two, cantorSupport_add, cantorSupport_wpow, Finset.union_self,
      Finset.singleton_union]
  have hp1 : p = 1 := by
    have hmem := hp.1
    have hle : p ≤ 1 := hp.2 (by rw [hs]; simp)
    change p ∈ cantorSupport x at hmem
    rw [hs] at hmem
    rcases Finset.mem_insert.mp hmem with h2 | h1
    · rw [h2] at hle
      norm_num at hle
    · exact Finset.mem_singleton.mp h1
  refine ⟨x₀, p, he, hp1, ?_⟩
  have he' : x = x₀ + ω^ (1 : NatOrdinal.{0}) := by
    rw [← hp1]
    exact he.trans hadd
  apply add_right_cancel (b := ω^ (1 : NatOrdinal.{0}))
  rw [← he']
  simp only [x, mul_two, add_assoc]

end Tests
