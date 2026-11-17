/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.NatOrdinal.FiniteBlocks

import Mathlib.SetTheory.Ordinal.Principal

/-!
# Ordered sums of increasing omega powers

Expanding a strictly increasing cofinal family of ranks below `a` into blocks of type
`omega^(rank+1)`, with an initial unit, gives exactly `omega^a`. The upper bound embeds each
block at the offset `omega^rank`. The lower bound uses the cofinal individual blocks.
All sums are ordinary ordered sums and the index order has arbitrary cofinality.
-/

universe u

public noncomputable section

namespace NatOrdinal

open Ordinal

/-- Increasing exponents below `a` give an expanded ordered sum bounded by `omega^a`. -/
theorem of_one_add_type_sigma_wpow_le {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (p : I → NatOrdinal.{u}) (a : NatOrdinal.{u}) (hp : StrictMono p)
    (ha : ∀ i, p i < a) :
    of (1 + typeLT (Σₗ i, (ω^ (p i + 1)).val.ToType)) ≤ ω^ a := by
  obtain rfl | ha0 := eq_or_ne a 0
  · have : IsEmpty I := ⟨fun i ↦ (not_lt_of_ge (bot_le : (0 : NatOrdinal.{u}) ≤ p i)) (ha i)⟩
    have : IsEmpty (Σₗ i, (ω^ (p i + 1)).val.ToType) :=
      ⟨fun z ↦ isEmptyElim (ofLex z).1⟩
    simp only [Ordinal.type_eq_zero_of_empty, add_zero, of_one, wpow_zero, le_refl]
  let W := (Σₗ i, (ω^ (p i + 1)).val.ToType)
  have hsmall (i : I) (t : (ω^ (p i + 1)).val.ToType) :
      (ω^ (p i)).val + t.toOrd.1 < (ω^ (p i + 1)).val := by
    exact Ordinal.isPrincipal_add_omega0_opow _
      (val.strictMono (wpow_lt_wpow.mpr (lt_add_one (p i)))) t.toOrd.2
  let f : W → (ω^ a).val.ToType := fun z ↦ Ordinal.ToType.mk
    ⟨(ω^ (p (ofLex z).1)).val + (ofLex z).2.toOrd.1,
      (hsmall _ _).trans_le (val.monotone (wpow_le_wpow.mpr
        (Order.add_one_le_iff.mpr (ha _))))⟩
  have hf : StrictMono f := by
    rintro ⟨i, s⟩ ⟨j, t⟩ h
    change Sigma.Lex ((· < ·) : I → I → Prop)
      (fun (i : I) (a b : (ω^ (p i + 1)).val.ToType) ↦ a < b) ⟨i, s⟩ ⟨j, t⟩ at h
    apply Ordinal.ToType.mk.strictMono
    change (ω^ (p i)).val + s.toOrd.1 < (ω^ (p j)).val + t.toOrd.1
    cases h with
    | left s t h =>
      exact (hsmall _ _).trans_le ((val.monotone (wpow_le_wpow.mpr
        (Order.add_one_le_iff.mpr (hp h)))).trans le_self_add)
    | right s t h =>
      exact (Ordinal.isNormal_add_right _).strictMono (Ordinal.ToType.mk.symm.strictMono h)
  have ht : typeLT W ≤ (ω^ a).val :=
    (RelEmbedding.ofMonotone f hf).ordinal_type_le.trans_eq (Ordinal.type_toType _)
  have h1 : (1 : Ordinal.{u}) < (ω^ a).val := by
    have h : (1 : NatOrdinal.{u}) < ω^ a := by
      simpa only [wpow_zero] using wpow_lt_wpow.mpr (pos_iff_ne_zero.mpr ha0)
    simpa only [val_one] using val.strictMono h
  apply of.monotone
  calc
    1 + typeLT W ≤ 1 + (ω^ a).val := add_le_add_right ht _
    _ = (ω^ a).val := by simpa only [val_wpow] using Ordinal.add_omega0_opow h1

/-- Cofinal exponent ranks give the matching lower bound for an expanded ordered sum. -/
theorem wpow_le_of_one_add_type_sigma {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (p : I → NatOrdinal.{u}) (a : NatOrdinal.{u})
    (hc : ∀ b < a, ∃ i, b ≤ p i) :
    ω^ a ≤ of (1 + typeLT (Σₗ i, (ω^ (p i + 1)).val.ToType)) := by
  obtain rfl | ha0 := eq_or_ne a 0
  · simpa only [wpow_zero, of_one] using (of.monotone
      (le_self_add : (1 : Ordinal.{u}) ≤ 1 + typeLT (Σₗ i, (ω^ (p i + 1)).val.ToType)))
  apply (wpow_le_iff ha0).mpr
  intro b hb n
  obtain ⟨i, hi⟩ := hc b hb
  let W := (Σₗ i, (ω^ (p i + 1)).val.ToType)
  let f : (ω^ (p i + 1)).val.ToType → W := fun t ↦ toLex ⟨i, t⟩
  have hf : StrictMono f := fun _ _ h ↦ Sigma.Lex.right _ _ h
  have ht : (ω^ (p i + 1)).val ≤ typeLT W := by
    simpa only [Ordinal.type_toType] using (RelEmbedding.ofMonotone f hf).ordinal_type_le
  exact (wpow_mul_natCast_lt (hi.trans_lt (lt_add_one (p i))) n).le.trans
    (of.monotone (ht.trans le_add_self))

/-- Expanding a strictly increasing cofinal sequence of ranks gives exactly `omega^a`. -/
theorem of_one_add_type_sigma_wpow_eq {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (p : I → NatOrdinal.{u}) (a : NatOrdinal.{u}) (hp : StrictMono p)
    (ha : ∀ i, p i < a) (hc : ∀ b < a, ∃ i, b ≤ p i) :
    of (1 + typeLT (Σₗ i, (ω^ (p i + 1)).val.ToType)) = ω^ a :=
  le_antisymm (of_one_add_type_sigma_wpow_le p a hp ha)
    (wpow_le_of_one_add_type_sigma p a hc)

end NatOrdinal
