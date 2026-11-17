/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostSuffix
public import GonshorBirthday.Surreal.Birthday.ReducedCostPlus

import GonshorBirthday.Surreal.Birthday.Addition

/-!
# Full coefficient blocks from equality of reduced costs

The suffix bound and the plus-count bound squeeze the final interval to one
complete coefficient block. Equality also forces sharp plus-count addition
and the plus-only cost of each input. The exponent may be zero.
-/

universe u

public noncomputable section

namespace Surreal
open Ordinal

/-- A bounded minus suffix forces a full final block and plus-only input costs. -/
theorem full_block_and_baseline_of_pure_suffix
    (a b d z : Surreal.{u}) {α β q c : NatOrdinal.{u}} {ρ : Ordinal.{u}}
    (hA : reducedOmegaCost (a + d) a = ω^ α)
    (hB : reducedOmegaCost (b + d) b = ω^ β)
    (hH : reducedOmegaCost (a + b + d) z = ω^ (α + β))
    (he : a + b = appendPluses z ρ) (hρ : (ω^ q).val ≤ ρ)
    (hc : c < z.birthday)
    (hcof : ∀ j < z.birthday, ∃ y ∈ rightPrefixes z,
      j < y.birthday ∧ y ≤ a + b + d)
    (hminus : typeLT {i : z.birthday.val.ToType | c ≤ NatOrdinal.of i.toOrd.1 ∧
      z < birthdayTruncation z (NatOrdinal.of i.toOrd.1)} ≤ (ω^ q).val) :
    ρ = (ω^ q).val ∧ plusCount (a + b) = α + β ∧
      α = plusCount a ∧ β = plusCount b ∧
      reducedOmegaCost (a + d) a = ω^ plusCount a ∧
      reducedOmegaCost (b + d) b = ω^ plusCount b := by
  have ha : plusCount a ≤ α := by
    apply NatOrdinal.wpow_le_wpow.mp
    rw [← hA]
    exact wpow_plusCount_le_reducedOmegaCost (a + d) a
  have hb : plusCount b ≤ β := by
    apply NatOrdinal.wpow_le_wpow.mp
    rw [← hB]
    exact wpow_plusCount_le_reducedOmegaCost (b + d) b
  have hpc : plusCount (a + b) = NatOrdinal.of ((plusCount z).val + ρ) := by
    rw [he, plusCount_appendPluses]
  have hlo : (plusCount z).val + ρ ≤ (α + β).val := by
    have h := (plusCount_add_le a b).trans (add_le_add ha hb)
    rw [hpc] at h
    exact NatOrdinal.val.monotone h
  have hhi : (α + β).val ≤ (plusCount z).val + 1 + q.val :=
    NatOrdinal.val.monotone
      (pure_reducedOmegaCost_exponent_le_of_minus_suffix hH hc hcof hminus)
  have hqbound : 1 + q.val ≤ (ω^ q).val := by
    by_cases hq : q = 0
    · simp only [hq, NatOrdinal.val_zero, NatOrdinal.wpow_zero, NatOrdinal.val_one,
        add_zero, le_refl]
    have hq : 0 < q := pos_iff_ne_zero.mpr hq
    rw [NatOrdinal.val_wpow]
    calc
      1 + q.val ≤ 1 + Ordinal.omega0 ^ q.val :=
        (Ordinal.isNormal_add_right 1).monotone
          (Ordinal.right_le_opow q.val Ordinal.one_lt_omega0)
      _ = _ := Ordinal.one_add_of_omega0_le
        (Ordinal.left_le_opow _ (NatOrdinal.val.strictMono hq))
  have hupper : (α + β).val ≤ (plusCount z).val + (ω^ q).val := by
    exact hhi.trans (by
      rw [add_assoc]
      exact (Ordinal.isNormal_add_right _).monotone hqbound)
  have hρeq : ρ = (ω^ q).val :=
    le_antisymm ((add_le_add_iff_left _).mp (hlo.trans hupper)) hρ
  have hsum : (α + β).val = (plusCount z).val + ρ := le_antisymm
    (by simpa only [← hρeq] using hupper) hlo
  have heq : plusCount (a + b) = α + β := by
    apply NatOrdinal.val.injective
    rw [hpc, NatOrdinal.val_of, hsum]
  have hrev : α + β ≤ plusCount a + plusCount b := by
    rw [← heq]
    exact plusCount_add_le a b
  have haeq : α = plusCount a := by
    apply le_antisymm ?_ ha
    by_contra hn
    exact (add_lt_add_of_lt_of_le (lt_of_not_ge hn) hb).not_ge hrev
  have hbeq : β = plusCount b := by
    apply le_antisymm ?_ hb
    by_contra hn
    exact (add_lt_add_of_le_of_lt ha (lt_of_not_ge hn)).not_ge hrev
  refine ⟨hρeq, heq, haeq, hbeq, ?_, ?_⟩
  · simpa only [haeq] using hA
  · simpa only [hbeq] using hB

end Surreal
