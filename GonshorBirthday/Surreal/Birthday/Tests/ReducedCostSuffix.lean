/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostSuffix

import GonshorBirthday.Surreal.Birthday.ReducedCostBlocks
public import GonshorBirthday.Surreal.Birthday.DyadicCoefficient
public import Mathlib.SetTheory.Ordinal.Veblen

/-!
# A sharp transfinite minus-suffix bound

The negative ordinal omega has omega many retained minuses and reduced cost
omega squared. Its plus rank is zero and the suffix estimate is attained.
-/

public noncomputable section

namespace Tests

open Surreal Ordinal

private theorem cost_negative_ordinal (o : NatOrdinal.{0}) :
    reducedOmegaCost 0 (-o.toSurreal) = NatOrdinal.of (1 + Ordinal.omega0 * o.val) := by
  rw [reducedOmegaCost_eq_of_plusCount_zero (plusCount_neg_toSurreal o)]
  have he : reducedOmegaPositions 0 (-o.toSurreal) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    apply mem_reducedOmegaPositions.mpr
    right
    have hi : NatOrdinal.of i.toOrd.1 ≤ o :=
      (NatOrdinal.of.strictMono i.toOrd.2).le.trans_eq (by simp)
    rw [birthdayTruncation_neg, birthdayTruncation_toSurreal hi]
    exact neg_nonpos.mpr (NatOrdinal.toSurreal_nonneg _)
  rw [he, (OrderIso.Set.univ).ordinalType_congr, Ordinal.type_toType,
    birthday_neg, birthday_toSurreal]

/-- The pure-cost suffix exponent estimate is attained at a genuine limit of minuses. -/
theorem negative_omega_suffix_bound_is_sharp :
    let x := -(NatOrdinal.of Ordinal.omega0 : NatOrdinal.{0}).toSurreal
    plusCount x = 0 ∧ reducedOmegaCost 0 x = ω^ (2 : NatOrdinal.{0}) ∧
      (2 : NatOrdinal.{0}) ≤ NatOrdinal.of ((plusCount x).val + 1 + (1 : Ordinal.{0})) := by
  let x := -(NatOrdinal.of Ordinal.omega0 : NatOrdinal.{0}).toSurreal
  have hb : x.birthday = NatOrdinal.of Ordinal.omega0 := by
    simp only [x, birthday_neg, birthday_toSurreal]
  have hp : plusCount x = 0 := plusCount_neg_toSurreal _
  have hcost : reducedOmegaCost 0 x = ω^ (2 : NatOrdinal.{0}) := by
    have h := cost_negative_ordinal (NatOrdinal.of Ordinal.omega0)
    rw [NatOrdinal.val_of] at h
    have he : Ordinal.omega0 * Ordinal.omega0 = Ordinal.omega0 ^ (2 : Ordinal.{0}) := by
      rw [← one_add_one_eq_two, Ordinal.opow_add_one, Ordinal.opow_one]
    rw [he, Ordinal.one_add_of_omega0_le
      (Ordinal.left_le_opow Ordinal.omega0 (by simp))] at h
    have htwo : (2 : NatOrdinal.{0}).val = (2 : Ordinal.{0}) := by
      rw [← one_add_one_eq_two, NatOrdinal.val_add_one, NatOrdinal.val_one,
        one_add_one_eq_two]
    simpa only [x, NatOrdinal.wpow_def, htwo] using h
  refine ⟨hp, hcost, ?_⟩
  let j : reducedOmegaPositions 0 x :=
    ⟨Ordinal.ToType.mk ⟨0, by rw [hb, NatOrdinal.val_of]; exact Ordinal.omega0_pos⟩, by
      apply mem_reducedOmegaPositions.mpr
      right
      simp only [Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_zero,
        birthdayTruncation_zero, le_refl]⟩
  apply pure_reducedOmegaCost_exponent_le_of_tail (q := 1) hcost j
  let M := {i : Set.Ici j | x < birthdayTruncation x (NatOrdinal.of i.1.1.toOrd.1)}
  let f : M → x.birthday.val.ToType := fun i ↦ i.1.1.1
  have hf : StrictMono f := fun _ _ h ↦ h
  have h := (RelEmbedding.ofMonotone f hf).ordinal_type_le
  simpa only [Ordinal.type_toType, hb, NatOrdinal.val_of, NatOrdinal.wpow_one] using h

/-- At any epsilon number, the minuses of `-ε` at cutoff zero have exactly the same
length as the plus contribution at `-ε/2`. -/
theorem minus_epsilon_and_its_next_coefficient (i : Ordinal.{0}) :
    let E := NatOrdinal.of (ε_ i)
    reducedOmegaCost 0 (-E.toSurreal) = E ∧
      ω^ (plusCount (-((2 : Surreal)⁻¹ * E.toSurreal))) = E := by
  let E := NatOrdinal.of (ε_ i)
  have hω := (Ordinal.omega0_lt_epsilon i).le
  have hmul : Ordinal.omega0 * ε_ i = ε_ i := by
    calc
      Ordinal.omega0 * ε_ i = Ordinal.omega0 * Ordinal.omega0 ^ ε_ i := by
        rw [Ordinal.omega0_opow_epsilon]
      _ = ε_ i := by rw [← Ordinal.opow_one_add, Ordinal.one_add_of_omega0_le hω,
        Ordinal.omega0_opow_epsilon]
  have hfixed : ω^ E = E := by simp only [E, NatOrdinal.wpow_def, NatOrdinal.val_of,
    Ordinal.omega0_opow_epsilon]
  have hM : ω^ E.toSurreal = E.toSurreal := by rw [← toSurreal_wpow, hfixed]
  have he := congrArg Neg.neg (half_mul_wpow_eq_appendMinuses E.toSurreal)
  rw [appendMinuses_eq_neg, neg_neg, plusCount_toSurreal, hfixed, hM] at he
  constructor
  · rw [cost_negative_ordinal, NatOrdinal.val_of, hmul, Ordinal.one_add_of_omega0_le hω]
  · rw [he, plusCount_appendPluses, plusCount_neg_toSurreal, NatOrdinal.val_zero, zero_add,
      NatOrdinal.of_val, hfixed]

end Tests
