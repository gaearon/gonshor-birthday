/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostPrefix

import GonshorBirthday.NatOrdinal.OrderedSum

/-!
# Constant-rank portions of reduced expanded words

When the original plus rank is constant, every retained block has the same weight. Its
contribution is ordinary left multiplication of that weight by the actual retained order type.
This applies to arbitrary deleted minus portions and arbitrary ordinal lengths.
-/

universe u

public noncomputable section

namespace Surreal

open Ordinal

/-- Constant original plus rank gives ordinary multiplication by the retained order type. -/
theorem omegaExpansionLength_eq_of_constant_plusCount (x : Surreal.{u})
    (S : Set x.birthday.val.ToType) (p : NatOrdinal.{u})
    (hp : ∀ i : S, plusCount (birthdayTruncation x (NatOrdinal.of i.1.toOrd.1)) = p) :
    omegaExpansionLength x S =
      NatOrdinal.of (1 + (ω^ (p + 1)).val * typeLT S) := by
  rw [omegaExpansionLength_eq]
  have he : typeLT (Σₗ i : S,
      (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of i.1.toOrd.1)) + 1)).val.ToType) =
      typeLT (Σₗ _i : S, (ω^ (p + 1)).val.ToType) := by
    apply Ordinal.type_sigma_congr _ _ (OrderIso.refl S)
    intro i
    simp only [Ordinal.type_toType, hp]
  rw [he, Ordinal.type_sigma_const, Ordinal.type_toType]

/-- A constant-rank retained tail contributes its block weight times its actual order type. -/
theorem reducedOmegaCost_eq_prefix_add_mul_of_constant_plusCount (C x : Surreal.{u})
    (j : reducedOmegaPositions C x) (p : NatOrdinal.{u})
    (hp : ∀ i : Set.Ici j,
      plusCount (birthdayTruncation x (NatOrdinal.of i.1.1.toOrd.1)) = p) :
    reducedOmegaCost C x = NatOrdinal.of
      ((reducedOmegaCost C (birthdayTruncation x (NatOrdinal.of j.1.toOrd.1))).val +
        (ω^ (p + 1)).val * typeLT (Set.Ici j)) := by
  rw [reducedOmegaCost_eq_prefix_add_tail C x j]
  have he : typeLT (Σₗ i : Set.Ici j,
      (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of i.1.1.toOrd.1)) + 1)).val.ToType) =
      typeLT (Σₗ _i : Set.Ici j, (ω^ (p + 1)).val.ToType) := by
    apply Ordinal.type_sigma_congr _ _ (OrderIso.refl (Set.Ici j))
    intro i
    simp only [Ordinal.type_toType, hp]
  rw [he, Ordinal.type_sigma_const, Ordinal.type_toType]

/-- With no plus signs, every retained exponent sign has weight omega. -/
theorem omegaExpansionLength_eq_of_plusCount_zero {x : Surreal.{u}}
    (hx : plusCount x = 0) (S : Set x.birthday.val.ToType) :
    omegaExpansionLength x S = NatOrdinal.of (1 + Ordinal.omega0 * typeLT S) := by
  have hp (i : S) : plusCount (birthdayTruncation x (NatOrdinal.of i.1.toOrd.1)) = 0 := by
    have h := plusCount_birthdayTruncation_le x (NatOrdinal.of.strictMono i.1.toOrd.2).le
    rw [hx] at h
    exact le_antisymm h bot_le
  simpa only [zero_add, NatOrdinal.wpow_one, NatOrdinal.val_of] using
    omegaExpansionLength_eq_of_constant_plusCount x S 0 hp

/-- The complete expansion of an all-minus word depends only on its original birthday. -/
theorem omegaExpansionLength_univ_eq_of_plusCount_zero {x : Surreal.{u}}
    (hx : plusCount x = 0) :
    omegaExpansionLength x Set.univ = NatOrdinal.of (1 + Ordinal.omega0 * x.birthday.val) := by
  rw [omegaExpansionLength_eq_of_plusCount_zero hx,
    (OrderIso.Set.univ).ordinalType_congr, Ordinal.type_toType]

/-- Arbitrary cutoff deletions in an all-minus word preserve the constant block weight. -/
theorem reducedOmegaCost_eq_of_plusCount_zero {x : Surreal.{u}}
    (hx : plusCount x = 0) (C : Surreal.{u}) :
    reducedOmegaCost C x =
      NatOrdinal.of (1 + Ordinal.omega0 * typeLT (reducedOmegaPositions C x)) := by
  rw [reducedOmegaCost_eq_positions, omegaExpansionLength_eq_of_plusCount_zero hx]

end Surreal
