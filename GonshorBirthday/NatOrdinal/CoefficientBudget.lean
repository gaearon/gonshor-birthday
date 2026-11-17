/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.NatOrdinal.ProductSum

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Ring

/-!
# Coefficient tails in natural-product budgets

Natural multiplication bounds an ordinary concatenation of repeated product
blocks. This yields coefficient-cell bounds using only the monomial budget
and the two baseline sizes, without a least-Cantor-exponent assumption.
Limit steps use ordinary ordinal continuity and monotonicity of the natural product.
-/

universe u

public noncomputable section

namespace NatOrdinal

open Ordinal

/-- Ordinary repeated product blocks fit the natural product of their concatenated input. -/
theorem of_oadd_omul_mul_le (A P C : NatOrdinal.{u}) (t : Ordinal.{u}) :
    of ((A * C).val + (P * C).val * t) ≤ of (A.val + P.val * t) * C := by
  induction t using Ordinal.limitRecOn with
  | zero => simp
  | add_one t ih =>
    have h := of_oadd_mul_le (of (A.val + P.val * t)) P C
    rw [val_of] at h
    rw [mul_add_one, mul_add_one, ← add_assoc, ← add_assoc]
    exact (of.monotone (add_le_add (val.monotone ih) le_rfl)).trans h
  | limit t ht ih =>
    by_cases hzero : (P * C).val = 0
    · rw [hzero, zero_mul, add_zero, of_val]
      exact mul_le_mul' (of.monotone le_self_add) le_rfl
    · change (A * C).val + (P * C).val * t ≤ (of (A.val + P.val * t) * C).val
      apply (((Ordinal.isNormal_add_right (A * C).val).comp
        (Ordinal.isNormal_mul_right (pos_iff_ne_zero.mpr hzero))).le_iff_forall_le ht).mpr
      intro s hst
      apply (val.monotone (ih s hst)).trans
      apply val.monotone
      apply mul_le_mul' ?_ le_rfl
      exact of.monotone (add_le_add le_rfl (mul_le_mul_right hst.le P.val))

/-- A smaller first block and repeated block fit the same ordinary-input product budget. -/
theorem of_oadd_omul_le_mul_of_le {A P C G H : NatOrdinal.{u}}
    (hG : G ≤ A * C) (hH : H ≤ P * C) (t : Ordinal.{u}) :
    of (G.val + H.val * t) ≤ of (A.val + P.val * t) * C := by
  apply le_trans ?_ (of_oadd_omul_mul_le A P C t)
  exact of.monotone (add_le_add (val.monotone hG) (mul_le_mul_left (val.monotone hH) t))

/-- Finite coefficient tails fit a cell using its monomial bound and the two baseline sizes. -/
theorem coefficient_cell_natCast_le {A B P Q G H : NatOrdinal.{u}}
    (hP : P ≤ A) (hQ : Q ≤ B) (hG : G ≤ A * B) (hH : H ≤ P * Q)
    (m n : ℕ) :
    of (G.val + H.val * ((m + n + m * n : ℕ) : Ordinal.{u})) ≤
      of (A.val + P.val * (m : Ordinal)) * of (B.val + Q.val * (n : Ordinal)) := by
  have hHB : H ≤ A * Q := hH.trans (mul_le_mul' hP le_rfl)
  have hHP : H ≤ P * B := hH.trans (mul_le_mul' le_rfl hQ)
  have hrow : of (H.val * ((n + 1 : ℕ) : Ordinal.{u})) ≤
      P * of (B.val + Q.val * (n : Ordinal)) := by
    have h := of_oadd_omul_le_mul_of_le (A := B) (P := Q) (C := P)
      (by simpa only [mul_comm] using hHP) (by simpa only [mul_comm] using hH)
      (n : Ordinal.{u})
    have he : H.val + H.val * (n : Ordinal.{u}) = H.val * ((n + 1 : ℕ) : Ordinal.{u}) := by
      rw [show n + 1 = 1 + n by omega, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
    simpa only [he, mul_comm P] using h
  induction m with
  | zero =>
    have h := of_oadd_omul_le_mul_of_le (A := B) (P := Q) (C := A)
      (by simpa only [mul_comm] using hG) (by simpa only [mul_comm] using hHB)
      (n : Ordinal.{u})
    simpa only [zero_add, zero_mul, add_zero, Nat.cast_zero, mul_zero, of_val, mul_comm A] using h
  | succ m ih =>
    have he : m + 1 + n + (m + 1) * n = (m + n + m * n) + (n + 1) := by ring
    have h := of_oadd_mul_le (of (A.val + P.val * (m : Ordinal))) P
      (of (B.val + Q.val * (n : Ordinal)))
    rw [val_of] at h
    rw [he, Nat.cast_add, mul_add, ← add_assoc]
    simpa only [val_of, Nat.cast_add_one, mul_add_one, add_assoc] using
      (of.monotone (add_le_add (val.monotone ih) (val.monotone hrow))).trans h

/-- An infinite coefficient tail in either factor supplies the entire omega-length output tail. -/
theorem coefficient_cell_omega_le {A B P Q G H : NatOrdinal.{u}}
    (hP : P ≤ A) (hQ : Q ≤ B) (hG : G ≤ A * B) (hH : H ≤ P * Q)
    (t u : Ordinal.{u}) (hinf : Ordinal.omega0 ≤ t ∨ Ordinal.omega0 ≤ u) :
    of (G.val + H.val * Ordinal.omega0) ≤
      of (A.val + P.val * t) * of (B.val + Q.val * u) := by
  rcases hinf with ht | hu
  · have h := of_oadd_omul_le_mul_of_le hG
      (hH.trans (mul_le_mul' le_rfl hQ)) Ordinal.omega0
    apply h.trans
    apply mul_le_mul'
    · exact of.monotone (add_le_add le_rfl (mul_le_mul_right ht P.val))
    · exact of.monotone le_self_add
  · have h := of_oadd_omul_le_mul_of_le (A := B) (P := Q) (C := A)
      (by simpa only [mul_comm] using hG)
      (by simpa only [mul_comm] using hH.trans (mul_le_mul' hP le_rfl)) Ordinal.omega0
    rw [mul_comm] at h
    apply h.trans
    apply mul_le_mul'
    · exact of.monotone le_self_add
    · exact of.monotone (add_le_add le_rfl (mul_le_mul_right hu Q.val))

/-- A repeated first-sign budget supplies the extra coefficient unit when two cells merge. -/
theorem coefficient_two_cells_le {G H : NatOrdinal.{u}} (hH : H ≤ G) (m n : ℕ) :
    of (G.val + H.val * ((m + n + 1 : ℕ) : Ordinal.{u})) ≤
      of ((G.val + H.val * (m : Ordinal)) + (G.val + H.val * (n : Ordinal))) := by
  have he : G.val + H.val * ((m + n + 1 : ℕ) : Ordinal.{u}) =
      (G.val + H.val * (m : Ordinal)) + (H.val + H.val * (n : Ordinal)) := by
    rw [show m + n + 1 = m + (1 + n) by omega,
      Nat.cast_add, Nat.cast_add, Nat.cast_one, mul_add, mul_add, mul_one]
    simp only [add_assoc]
  rw [he]
  exact of.monotone (add_le_add le_rfl (add_le_add (val.monotone hH) le_rfl))

/-- A nonempty finite fibre fits its merged coefficient block into its consecutive cell blocks. -/
theorem coefficient_fibre_natCast_le {G H : NatOrdinal.{u}} (hH : H ≤ G)
    (l : List ℕ) (hne : l ≠ []) :
    of (G.val + H.val * (((l.map (fun n ↦ n + 1)).sum - 1 : ℕ) : Ordinal.{u})) ≤
      of ((l.map (fun n : ℕ ↦ G.val + H.val * (n : Ordinal.{u}))).sum) := by
  induction l with
  | nil => exact False.elim (hne rfl)
  | cons m l ih =>
    cases l with
    | nil => simp
    | cons n l =>
      have htail : (n :: l : List ℕ) ≠ [] := List.cons_ne_nil n l
      have hi := ih htail
      have hs : 0 < (((n :: l).map (fun n ↦ n + 1)).sum) := by
        simp only [List.map_cons, List.sum_cons]
        omega
      have he : (((m :: n :: l).map (fun n ↦ n + 1)).sum - 1) =
          m + (((n :: l).map (fun n ↦ n + 1)).sum - 1) + 1 := by
        simp only [List.map_cons, List.sum_cons]
        simp only [List.map_cons, List.sum_cons] at hs
        omega
      rw [he, List.map_cons, List.sum_cons]
      apply (coefficient_two_cells_le hH m _).trans
      exact of.monotone (add_le_add le_rfl (val.monotone hi))

/-- The finite-fibre coefficient bound as an ordered sum of actual ordinal blocks. -/
theorem coefficient_fibre_fin_le {G H : NatOrdinal.{u}} (hH : H ≤ G)
    {n : ℕ} (hn : n ≠ 0) (t : Fin n → ℕ) :
    of (G.val + H.val * (((∑ i, (t i + 1)) - 1 : ℕ) : Ordinal.{u})) ≤
      of (typeLT (Σₗ i : Fin n,
        (of (G.val + H.val * (t i : Ordinal.{u}))).val.ToType)) := by
  have hne : List.ofFn t ≠ [] := by
    intro he
    have hl := congrArg List.length he
    rw [List.length_ofFn, List.length_nil] at hl
    exact hn hl
  have h := coefficient_fibre_natCast_le hH (List.ofFn t) hne
  rw [Ordinal.type_fin_sigma]
  simp_rw [Ordinal.type_toType]
  simpa only [List.map_ofFn, List.sum_ofFn, val_of, Function.comp_def] using h

/-- One infinite coefficient tail already supplies the entire merged infinite tail. -/
theorem coefficient_fibre_omega_le (G H : NatOrdinal.{u}) (l : List Ordinal.{u})
    (hinf : ∃ t ∈ l, Ordinal.omega0 ≤ t) :
    of (G.val + H.val * Ordinal.omega0) ≤
      of ((l.map (fun t ↦ G.val + H.val * t)).sum) := by
  obtain ⟨t, ht, hω⟩ := hinf
  apply of.monotone
  apply (add_le_add le_rfl (mul_le_mul_right hω H.val)).trans
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨t, ht, rfl⟩)

end NatOrdinal
