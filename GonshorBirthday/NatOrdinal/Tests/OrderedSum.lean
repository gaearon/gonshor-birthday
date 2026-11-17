/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.NatOrdinal.OrderedSum
public import GonshorBirthday.NatOrdinal.OrderedSumBound

import Mathlib.Order.Interval.Finset.Nat

/-!
# Ordered-sum limit clients

Finite blocks of unbounded size concatenate to omega, including an empty initial block.
Countably many omega blocks concatenate to omega squared. The first identity uses cofinal
prefix bounds; the second checks the orientation of ordinary multiplication.
-/

public noncomputable section

namespace Tests

open Ordinal

/-- Unbounded finite blocks have a countable limit, with no largest block. -/
theorem increasing_finite_blocks : typeLT (Σₗ n : ℕ, Fin n) = Ordinal.omega0 := by
  apply le_antisymm
  · apply Ordinal.type_sigma_le_of_cofinal_prefixes (fun n : ℕ ↦ Fin n)
    intro n
    refine ⟨n + 1, Nat.lt_succ_self n, ?_⟩
    let : Fintype (Σₗ k : Set.Iio (n + 1), Fin k.1) := Fintype.ofFinite _
    rw [Ordinal.type_fintype]
    exact (Ordinal.natCast_lt_omega0 _).le
  · apply Ordinal.omega0_le.mpr
    intro n
    simpa only [Ordinal.type_fin] using Ordinal.type_sigma_block_le (fun n : ℕ ↦ Fin n) n

/-- Constant omega blocks multiply on the left of their index order type. -/
theorem constant_omega_blocks :
    typeLT (Σₗ _n : ℕ, (Ordinal.omega0 : Ordinal.{0}).ToType) =
      Ordinal.omega0 ^ (2 : Ordinal.{0}) := by
  rw [Ordinal.type_sigma_const, Ordinal.type_toType, Ordinal.type_nat_lt]
  simp [← one_add_one_eq_two, Ordinal.opow_add_one]

/-- Uniform block bounds multiply the block length on the left of the index length. -/
theorem two_omega_blocks_uniform_bound :
    typeLT (Σₗ _i : Fin 2, (Ordinal.omega0 : Ordinal.{0}).ToType) ≤
      Ordinal.omega0 * 2 := by
  simpa using
    Ordinal.type_sigma_le_mul_of_le
      (fun _i : Fin 2 ↦ (Ordinal.omega0 : Ordinal.{0}).ToType) Ordinal.omega0
      (fun _ ↦ by rw [Ordinal.type_toType])

end Tests
