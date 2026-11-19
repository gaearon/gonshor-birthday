/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.NatOrdinal.CantorSupport
public import GonshorBirthday.NatOrdinal.MultiplicationBound

import Mathlib.Algebra.BigOperators.Fin

/-!
# The final Cantor power and cofinal natural products

Splitting off one copy of the least Cantor power gives identical ordinary and
natural sums. A factor whose proper-prefix products are cofinal forces the other
nonzero factor to be a single omega power.
-/

universe u

public noncomputable section

namespace NatOrdinal

/-- Every nonzero ordinal ends in one copy of its least Cantor power. -/
theorem exists_final_wpow {x : NatOrdinal.{u}} (hx : x ≠ 0) :
    ∃ x₀ p : NatOrdinal.{u}, x = of (x₀.val + (ω^ p).val) ∧
      of (x₀.val + (ω^ p).val) = x₀ + ω^ p ∧
      IsLeast (cantorSupport x : Set NatOrdinal.{u}) p := by
  classical
  obtain ⟨n, f, hf, hs⟩ := exists_antitone_wpow_sum x
  cases n with
  | zero => exact False.elim (hx (by simpa only [Fin.sum_univ_zero] using hs))
  | succ n =>
    let x₀ : NatOrdinal.{u} := ∑ i : Fin n, ω^ (f i.castSucc)
    let p := f (Fin.last n)
    have hp : ∀ e ∈ cantorSupport x₀, p ≤ e := by
      intro e he
      simp only [x₀, cantorSupport_sum, cantorSupport_wpow, Finset.mem_biUnion,
        Finset.mem_univ, Finset.mem_singleton, true_and] at he
      obtain ⟨i, rfl⟩ := he
      exact hf (Fin.le_last _)
    have hadd : of (x₀.val + (ω^ p).val) = x₀ + ω^ p :=
      of_oadd_wpow_of_le_cantorSupport hp
    refine ⟨x₀, p, ?_, hadd, ?_, ?_⟩
    · rw [hadd, hs, Fin.sum_univ_castSucc]
    · rw [hs]
      exact mem_cantorSupport_sum_wpow f (Fin.last n)
    · intro e he
      change e ∈ cantorSupport x at he
      rw [hs] at he
      simp only [cantorSupport_sum, cantorSupport_wpow, Finset.mem_biUnion,
        Finset.mem_univ, Finset.mem_singleton, true_and] at he
      obtain ⟨i, rfl⟩ := he
      exact hf (Fin.le_last _)

/-- Adding an ordinal below the least Cantor power of a strict upper bound preserves strictness. -/
theorem add_lt_of_lt_last_power {h t n p : NatOrdinal.{u}} (hh : h < n)
    (ht : t < ω^ p) (hs : ∀ e ∈ cantorSupport n, p ≤ e) : h + t < n := by
  obtain ⟨k, q, he, ha, hq⟩ := exists_final_wpow (ne_of_gt (bot_le.trans_lt hh))
  have htq := ht.trans_le (wpow_le_wpow.mpr (hs q hq.1))
  obtain ⟨r, hr, hb⟩ := (Ordinal.lt_add_iff (wpow_ne_zero q)).mp (hh.trans_eq he)
  have hm := (of.monotone hb).trans (oadd_le_add k (of r))
  calc
    h + t ≤ k + of r + t := add_le_add hm le_rfl
    _ = k + (of r + t) := add_assoc ..
    _ < k + ω^ q := add_lt_add_of_le_of_lt le_rfl (add_lt_wpow hr htq)
    _ = n := (he.trans ha).symm

/-- A nonzero limit ordinal has a positive final Cantor exponent. -/
theorem exists_final_wpow_of_isSuccLimit {x : NatOrdinal.{u}}
    (hx : Order.IsSuccLimit x.val) :
    ∃ x₀ p : NatOrdinal.{u}, 0 < p ∧ x = of (x₀.val + (ω^ p).val) ∧
      of (x₀.val + (ω^ p).val) = x₀ + ω^ p ∧
      IsLeast (cantorSupport x : Set NatOrdinal.{u}) p := by
  have hx0 : x ≠ 0 := by
    intro he
    exact (Ordinal.isSuccLimit_iff.mp hx).1 (by rw [he, val_zero])
  obtain ⟨x₀, p, he, hadd, hp⟩ := exists_final_wpow hx0
  refine ⟨x₀, p, ?_, he, hadd, hp⟩
  by_contra hn
  have hp0 : p = 0 := le_antisymm (le_of_not_gt hn) bot_le
  rw [hp0, wpow_zero, val_one] at he
  have hv : x.val = x₀.val + 1 := congrArg val he
  exact hx.succ_ne x₀.val (by simpa only [Order.succ_eq_add_one] using hv.symm)

/-- Cofinality in a nonzero natural product forces the fixed factor to be a pure omega power. -/
theorem exists_eq_wpow_of_products_cofinal {x y : NatOrdinal.{u}} (hx : x ≠ 0) (hy : y ≠ 0)
    (hcof : ∀ S < x * y, ∃ z < x, S ≤ z * y) : ∃ p, y = ω^ p := by
  obtain ⟨x₀, p, hx₀, hadd, _⟩ := exists_final_wpow hx
  have he : x = x₀ + ω^ p := hx₀.trans hadd
  apply exists_eq_wpow_of_mul_cofinal x₀ hadd hy
  simpa only [← he] using hcof

/-- Every suffix starting inside a final omega power has that whole power as its order type. -/
theorem final_wpow_osub {x₀ z p : NatOrdinal.{u}} (hlo : x₀ ≤ z)
    (hhi : z < of (x₀.val + (ω^ p).val)) :
    of ((x₀.val + (ω^ p).val) - z.val) = ω^ p := by
  have ht : z.val - x₀.val < (ω^ p).val :=
    (Ordinal.sub_lt_of_le (val.monotone hlo)).mpr (val.strictMono hhi)
  have hs : x₀.val + (z.val - x₀.val) = z.val :=
    Ordinal.add_sub_cancel_of_le (val.monotone hlo)
  calc
    of ((x₀.val + (ω^ p).val) - z.val) =
        of ((ω^ p).val - (z.val - x₀.val)) := by
      conv_lhs => rw [← hs, Ordinal.add_sub_add_cancel]
    _ = ω^ p := wpow_osub_of_lt (of.strictMono ht)

end NatOrdinal
