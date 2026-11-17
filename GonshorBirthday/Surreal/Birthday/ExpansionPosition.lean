/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ExpansionLength

import GonshorBirthday.NatOrdinal.OrderedSumPosition

/-!
# Coverage by original exponent blocks

Every complete expanded-word position is either its initial sign or has coordinates in
one of the original exponent blocks. Its starting position is the complete expansion
length of the actual canonical exponent prefix. All lengths and cofinalities are unrestricted.
-/

universe u

public noncomputable section

namespace Surreal

open Ordinal

/-- Every expanded position is the initial sign or belongs to an original exponent block. -/
theorem omegaExpansionLength_univ_position (x : Surreal.{u}) {j : Ordinal.{u}}
    (hj : j < (omegaExpansionLength x Set.univ).val) :
    j = 0 ∨ ∃ a : NatOrdinal.{u}, a < x.birthday ∧ ∃ t : Ordinal.{u},
      t < (ω^ (plusCount (birthdayTruncation x a) + 1)).val ∧
      j = (omegaExpansionLength (birthdayTruncation x a) Set.univ).val + t := by
  by_cases hj0 : j = 0
  · exact Or.inl hj0
  right
  let C : Surreal.{u} := x.birthday.toSurreal
  let S := reducedOmegaPositions C x
  let W (i : S) :=
    (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of i.1.toOrd.1)) + 1)).val.ToType
  have hsum : (omegaExpansionLength x Set.univ).val = 1 + typeLT (Σₗ i : S, W i) := by
    rw [← reducedOmegaCost_eq_omegaExpansionLength_univ (le_refl x.birthday.toSurreal),
      reducedOmegaCost_eq_positions, omegaExpansionLength_eq, NatOrdinal.val_of]
  have h1j : (1 : Ordinal.{u}) ≤ j := by
    simpa only [zero_add] using Order.add_one_le_iff.mpr (pos_iff_ne_zero.mpr hj0)
  have hq : j - 1 < typeLT (Σₗ i : S, W i) := by
    apply (Ordinal.sub_lt_of_le h1j).mpr
    exact hj.trans_eq hsum
  obtain ⟨z, hz⟩ := Ordinal.typein_surj ((· < ·) : (Σₗ i : S, W i) → _ → Prop) hq
  obtain ⟨i, t⟩ := z
  change Ordinal.typein ((· < ·) : (Σₗ i : S, W i) → _ → Prop) (toLex ⟨i, t⟩) = j - 1 at hz
  have hi : NatOrdinal.of i.1.toOrd.1 < x.birthday := NatOrdinal.of.strictMono i.1.toOrd.2
  refine ⟨NatOrdinal.of i.1.toOrd.1, hi,
    Ordinal.typein ((· < ·) : W i → _ → Prop) t, Ordinal.typein_lt_self t, ?_⟩
  have hC : (birthdayTruncation x (NatOrdinal.of i.1.toOrd.1)).birthday.toSurreal ≤ C :=
    NatOrdinal.toSurreal.monotone (birthday_birthdayTruncation_le_birthday x _)
  have hp := reducedOmegaCost_birthdayTruncation_eq_iio C x i
  rw [reducedOmegaCost_eq_omegaExpansionLength_univ hC] at hp
  have hpv := congrArg NatOrdinal.val hp
  rw [NatOrdinal.val_of] at hpv
  calc
    j = 1 + (j - 1) := (Ordinal.add_sub_cancel_of_le h1j).symm
    _ = 1 + ((typeLT (Σₗ k : Set.Iio i, W k.1)) +
        Ordinal.typein ((· < ·) : W i → _ → Prop) t) := by
      rw [← hz, Ordinal.typein_sigma]
    _ = _ := by rw [← add_assoc, ← hpv]

end Surreal
