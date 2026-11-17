/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostPrefix

import GonshorBirthday.NatOrdinal.OrderedSum
import Mathlib.Logic.Equiv.Prod

/-!
# Successor and limit identities for complete expanded lengths

A cutoff above the ordinal birthday retains every original sign. At that cutoff, reduced-cost
prefix splitting gives the exact successor recurrence for the complete weighted word.
Ordinary continuity bounds the length at arbitrary nonzero limits by all earlier prefixes.
-/

universe u

public noncomputable section

namespace Surreal

open Ordinal

/-- A cutoff above the ordinal birthday retains every sign position. -/
theorem reducedOmegaPositions_eq_univ_of_birthday_le {C x : Surreal.{u}}
    (hC : x.birthday.toSurreal ≤ C) : reducedOmegaPositions C x = Set.univ := by
  apply Set.eq_univ_of_forall
  intro i
  apply mem_reducedOmegaPositions.mpr
  right
  exact ((birthdayTruncation x (NatOrdinal.of i.toOrd.1)).le_toSurreal_birthday.trans
    (NatOrdinal.toSurreal.monotone (birthday_birthdayTruncation_le_birthday x _))).trans hC

/-- At a cutoff above the ordinal birthday, reduced cost is the complete expanded length. -/
theorem reducedOmegaCost_eq_omegaExpansionLength_univ {C x : Surreal.{u}}
    (hC : x.birthday.toSurreal ≤ C) :
    reducedOmegaCost C x = omegaExpansionLength x Set.univ := by
  rw [reducedOmegaCost_eq_positions, reducedOmegaPositions_eq_univ_of_birthday_le hC]

/-- The empty exponent word has complete expanded length one. -/
@[simp]
theorem omegaExpansionLength_univ_zero :
    omegaExpansionLength (0 : Surreal.{u}) Set.univ = 1 := by
  rw [← reducedOmegaCost_eq_omegaExpansionLength_univ (C := 0) (by simp),
    reducedOmegaCost_zero]

/-- Complete expanded length cannot increase when the exponent is truncated. -/
theorem omegaExpansionLength_univ_birthdayTruncation_le (x : Surreal.{u})
    {a : NatOrdinal.{u}} (ha : a ≤ x.birthday) :
    omegaExpansionLength (birthdayTruncation x a) Set.univ ≤
      omegaExpansionLength x Set.univ := by
  have hC := NatOrdinal.toSurreal.monotone (birthday_birthdayTruncation_le_birthday x a)
  rw [← reducedOmegaCost_eq_omegaExpansionLength_univ hC,
    ← reducedOmegaCost_eq_omegaExpansionLength_univ (le_refl x.birthday.toSurreal)]
  exact reducedOmegaCost_birthdayTruncation_le _ _ ha

/-- At a nonzero limit, the complete expanded length is bounded exactly when every prefix is. -/
theorem omegaExpansionLength_univ_birthdayTruncation_limit (x : Surreal.{u})
    {a : NatOrdinal.{u}} (ha : a ≤ x.birthday) (hla : Order.IsSuccLimit a.val)
    (M : NatOrdinal.{u}) :
    omegaExpansionLength (birthdayTruncation x a) Set.univ ≤ M ↔
      ∀ b < a, omegaExpansionLength (birthdayTruncation x b) Set.univ ≤ M := by
  constructor
  · intro h b hb
    have hb' : b ≤ (birthdayTruncation x a).birthday := by
      rw [birthday_birthdayTruncation x ha]
      exact hb.le
    have ht := omegaExpansionLength_univ_birthdayTruncation_le (birthdayTruncation x a) hb'
    rw [birthdayTruncation_birthdayTruncation x hb.le ha] at ht
    exact ht.trans h
  · intro h
    let C : Surreal.{u} := x.birthday.toSurreal
    let y := birthdayTruncation x a
    have hy : y.birthday = a := birthday_birthdayTruncation x ha
    have hyC : y.birthday.toSurreal ≤ C := NatOrdinal.toSurreal.monotone (hy.le.trans ha)
    rw [← reducedOmegaCost_eq_omegaExpansionLength_univ hyC]
    have hM : 1 ≤ M := by
      have ha0 : (0 : NatOrdinal.{u}) < a := NatOrdinal.val.lt_iff_lt.mp hla.bot_lt
      have he := congrArg (fun z : Surreal.{u} ↦ omegaExpansionLength z Set.univ)
        (birthdayTruncation_zero x)
      exact ((he.trans omegaExpansionLength_univ_zero).symm.le).trans (h 0 ha0)
    apply reducedOmegaCost_le_of_cofinal_prefixes C y M hM
    intro i
    have hi : i.1.toOrd.1 < a.val := i.1.toOrd.2.trans_eq (congrArg NatOrdinal.val hy)
    obtain ⟨b, hib, hba⟩ := hla.lt_iff_nonempty_Ioo.mp hi
    let j : reducedOmegaPositions C y :=
      ⟨Ordinal.ToType.mk ⟨b, hba.trans_eq (congrArg NatOrdinal.val hy).symm⟩, by
        rw [reducedOmegaPositions_eq_univ_of_birthday_le hyC]
        trivial⟩
    refine ⟨j, ?_, ?_⟩
    · change i.1 < Ordinal.ToType.mk _
      apply Ordinal.ToType.mk.symm.lt_iff_lt.mp
      rw [OrderIso.symm_apply_apply]
      exact hib
    · have hb : NatOrdinal.of b < a := by
        simpa only [NatOrdinal.of_val] using NatOrdinal.of.strictMono hba
      have hbC : (birthdayTruncation y (NatOrdinal.of b)).birthday.toSurreal ≤ C :=
        (NatOrdinal.toSurreal.monotone
          (birthday_birthdayTruncation_le_birthday y _)).trans hyC
      have hp : birthdayTruncation y (NatOrdinal.of b) =
          birthdayTruncation x (NatOrdinal.of b) :=
        birthdayTruncation_birthdayTruncation x hb.le ha
      have he := (reducedOmegaCost_eq_omegaExpansionLength_univ hbC).trans
        (congrArg (fun z : Surreal.{u} ↦ omegaExpansionLength z Set.univ) hp)
      simpa only [j, Ordinal.ToType.toOrd, OrderIso.symm_apply_apply] using
        he.le.trans (h (NatOrdinal.of b) hb)

private theorem type_sigma_unique_ord {I : Type u}
    [LinearOrder I] [WellFoundedLT I] [Unique I]
    (W : I → Ordinal.{u}) : typeLT (Σₗ i, (W i).ToType) = W default := by
  let e : (W default).ToType ≃o (Σₗ i, (W i).ToType) :=
    { toEquiv := (Equiv.uniqueSigma (fun i ↦ (W i).ToType)).symm.trans toLex
      map_rel_iff' := by
        intro a b
        change Sigma.Lex ((· < ·) : I → I → Prop)
          (fun (i : I) (a b : (W i).ToType) ↦ a ≤ b)
          ⟨default, a⟩ ⟨default, b⟩ ↔ a ≤ b
        simp [Sigma.lex_iff] }
  exact e.toRelIsoLT.ordinalType_congr.symm.trans (Ordinal.type_toType _)

/-- One further exponent sign appends exactly its original omega-power block to the length. -/
theorem omegaExpansionLength_univ_birthdayTruncation_add_one (x : Surreal.{u})
    {a : NatOrdinal.{u}} (ha : a + 1 ≤ x.birthday) :
    (omegaExpansionLength (birthdayTruncation x (a + 1)) Set.univ).val =
      (omegaExpansionLength (birthdayTruncation x a) Set.univ).val +
        (ω^ (plusCount (birthdayTruncation x a) + 1)).val := by
  let C : Surreal.{u} := x.birthday.toSurreal
  let y := birthdayTruncation x (a + 1)
  have hy : y.birthday = a + 1 := birthday_birthdayTruncation x ha
  have hyC : y.birthday.toSurreal ≤ C := NatOrdinal.toSurreal.monotone (hy.le.trans ha)
  have hay : a < y.birthday := (lt_add_one a).trans_eq hy.symm
  let j : reducedOmegaPositions C y :=
    ⟨Ordinal.ToType.mk ⟨a.val, NatOrdinal.val.strictMono hay⟩, by
      rw [reducedOmegaPositions_eq_univ_of_birthday_le hyC]
      trivial⟩
  have hjmax (i : reducedOmegaPositions C y) : i ≤ j := by
    change i.1 ≤ Ordinal.ToType.mk _
    apply Ordinal.ToType.mk.symm.le_iff_le.mp
    rw [OrderIso.symm_apply_apply]
    change i.1.toOrd.1 ≤ a.val
    have he : y.birthday.val = a.val + 1 :=
      (congrArg NatOrdinal.val hy).trans (NatOrdinal.val_add_one a)
    exact Order.lt_add_one_iff.mp (i.1.toOrd.2.trans_eq he)
  let : Unique (Set.Ici j) :=
    { default := ⟨j, le_refl j⟩
      uniq := fun i ↦ Subtype.ext (le_antisymm (hjmax i.1) i.2) }
  have he := reducedOmegaCost_eq_prefix_add_tail C y j
  rw [type_sigma_unique_ord] at he
  change reducedOmegaCost C y = NatOrdinal.of
    ((reducedOmegaCost C (birthdayTruncation y (NatOrdinal.of j.1.toOrd.1))).val +
      (ω^ (plusCount (birthdayTruncation y (NatOrdinal.of j.1.toOrd.1)) + 1)).val) at he
  have hp : birthdayTruncation y (NatOrdinal.of j.1.toOrd.1) = birthdayTruncation x a := by
    simp only [j, Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val]
    exact birthdayTruncation_birthdayTruncation x (le_add_of_nonneg_right bot_le) ha
  rw [hp, reducedOmegaCost_eq_omegaExpansionLength_univ hyC,
    reducedOmegaCost_eq_omegaExpansionLength_univ
      (NatOrdinal.toSurreal.monotone (birthday_birthdayTruncation_le_birthday x a))] at he
  exact congrArg NatOrdinal.val he

end Surreal
