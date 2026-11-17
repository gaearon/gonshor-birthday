/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.NatOrdinal.PowerSum

/-!
# A cofinal limit of expanded power blocks

The ordinary ordered sum `1 + omega + omega^2 + ...` is `omega^omega`.
The index order has a genuine limit, rather than a final largest block.
-/

public noncomputable section

namespace Tests

open Ordinal NatOrdinal

/-- Expanding every finite rank gives the full limit power. -/
theorem finite_rank_blocks :
    of (1 + typeLT (Σₗ n : ℕ, (ω^ ((n : NatOrdinal.{0}) + 1)).val.ToType)) =
      ω^ (of Ordinal.omega0 : NatOrdinal.{0}) := by
  apply of_one_add_type_sigma_wpow_eq (fun n : ℕ ↦ (n : NatOrdinal.{0}))
  · intro i j hij
    exact Nat.cast_lt.mpr hij
  · intro i
    simpa only [of_natCast] using of.strictMono (Ordinal.natCast_lt_omega0 i)
  · intro b hb
    have hv : b.val < Ordinal.omega0 := hb
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hv
    refine ⟨n, ?_⟩
    have he : b = (n : NatOrdinal.{0}) := by
      simpa only [of_val, of_natCast] using congrArg of hn
    exact he.le

end Tests
