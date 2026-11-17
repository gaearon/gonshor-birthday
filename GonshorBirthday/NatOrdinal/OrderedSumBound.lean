/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.NatOrdinal.OrderedSum
public import GonshorBirthday.NatOrdinal.Shuffle

/-!
# Uniform bounds and partitions of ordered sums

An ordered family of blocks bounded by one ordinal is bounded by ordinary
left multiplication by that ordinal. Partitioning its index set bounds the
whole sum by the natural sum of the two restricted ordered sums.
-/

universe u

public noncomputable section

namespace Ordinal

/-- Increasing embeddings of the indices and their blocks embed the whole ordered sum. -/
theorem type_sigma_le_of_embedding {I J : Type u} {A : I → Type u} {B : J → Type u}
    [LinearOrder I] [WellFoundedLT I] [LinearOrder J] [WellFoundedLT J]
    [∀ i, LinearOrder (A i)] [∀ i, WellFoundedLT (A i)]
    [∀ j, LinearOrder (B j)] [∀ j, WellFoundedLT (B j)]
    (e : I ↪o J) (f : ∀ i, A i ↪o B (e i)) :
    typeLT (Σₗ i, A i) ≤ typeLT (Σₗ j, B j) := by
  let g : (Σₗ i, A i) → (Σₗ j, B j) := fun z ↦
    toLex ⟨e (ofLex z).1, f (ofLex z).1 (ofLex z).2⟩
  have hg : StrictMono g := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    change Sigma.Lex ((· < ·) : I → I → Prop)
      (fun i (a b : A i) ↦ a < b) ⟨i, a⟩ ⟨j, b⟩ at h
    cases h with
    | left a b h => exact Sigma.Lex.left _ _ (e.strictMono h)
    | right a b h => exact Sigma.Lex.right _ _ ((f _).strictMono h)
  exact (RelEmbedding.ofMonotone g hg).ordinal_type_le

/-- A uniform bound for the blocks gives an ordinary product bound for their ordered sum. -/
theorem type_sigma_le_mul_of_le {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (A : I → Type u) [∀ i, LinearOrder (A i)] [∀ i, WellFoundedLT (A i)]
    (m : Ordinal.{u}) (h : ∀ i, typeLT (A i) ≤ m) :
    typeLT (Σₗ i, A i) ≤ m * typeLT I := by
  let f : (Σₗ i, A i) → (I ×ₗ m.ToType) := fun z ↦ toLex
    ((ofLex z).1, Ordinal.ToType.mk
      ⟨typein ((· < ·) : A (ofLex z).1 → _ → Prop) (ofLex z).2,
        (typein_lt_type _ _).trans_le (h (ofLex z).1)⟩)
  have hf : StrictMono f := by
    rintro ⟨i, a⟩ ⟨j, b⟩ hab
    change Sigma.Lex ((· < ·) : I → I → Prop)
      (fun i (a b : A i) ↦ a < b) ⟨i, a⟩ ⟨j, b⟩ at hab
    cases hab with
    | left a b hij => exact Prod.Lex.left _ _ hij
    | right a b hab =>
      exact Prod.Lex.right _ (Ordinal.ToType.mk.strictMono ((typein_lt_typein _).mpr hab))
  simpa only [type_lt_prod_lex, type_toType] using
    (RelEmbedding.ofMonotone f hf).ordinal_type_le

private def sigmaIndexSubsetIso {I : Type u} [LinearOrder I]
    (A : I → Type u) [∀ i, LinearOrder (A i)] (S : Set I) :
    {z : (Σₗ i, A i) | (ofLex z).1 ∈ S} ≃o (Σₗ i : S, A i.1) where
  toFun z := toLex ⟨⟨(ofLex z.1).1, z.2⟩, (ofLex z.1).2⟩
  invFun z := ⟨toLex ⟨(ofLex z).1.1, (ofLex z).2⟩, (ofLex z).1.2⟩
  left_inv z := rfl
  right_inv z := rfl
  map_rel_iff' := by
    rintro ⟨⟨i, a⟩, hi⟩ ⟨⟨j, b⟩, hj⟩
    change Sigma.Lex ((· < ·) : S → S → Prop)
      (fun i (a b : A i.1) ↦ a ≤ b) ⟨⟨i, hi⟩, a⟩ ⟨⟨j, hj⟩, b⟩ ↔
      Sigma.Lex ((· < ·) : I → I → Prop)
      (fun i (a b : A i) ↦ a ≤ b) ⟨i, a⟩ ⟨j, b⟩
    by_cases hij : i = j
    · subst j
      simp only [Sigma.lex_iff, lt_self_iff_false, false_or, exists_true_left]
    · simp [Sigma.lex_iff, hij, Subtype.ext_iff]
      rfl

/-- Selecting whole blocks is the same as restricting their index set. -/
theorem type_sigma_index_subset {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (A : I → Type u) [∀ i, LinearOrder (A i)] [∀ i, WellFoundedLT (A i)] (S : Set I) :
    typeLT {z : (Σₗ i, A i) | (ofLex z).1 ∈ S} = typeLT (Σₗ i : S, A i.1) :=
  (sigmaIndexSubsetIso A S).toRelIsoLT.ordinalType_congr

end Ordinal

namespace NatOrdinal

open Ordinal

/-- The two restricted ordered sums bound a partitioned family by their natural sum. -/
theorem of_type_sigma_le_add_compl {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (A : I → Type u) [∀ i, LinearOrder (A i)] [∀ i, WellFoundedLT (A i)] (S : Set I) :
    of (typeLT (Σₗ i, A i)) ≤ of (typeLT (Σₗ i : S, A i.1)) +
      of (typeLT (Σₗ i : (Sᶜ : Set I), A i.1)) := by
  have h := of_type_le_add_of_type_compl {z : (Σₗ i, A i) | (ofLex z).1 ∈ S}
  rw [type_sigma_index_subset] at h
  have he : ({z : (Σₗ i, A i) | (ofLex z).1 ∈ S}ᶜ : Set (Σₗ i, A i)) =
      {z : (Σₗ i, A i) | (ofLex z).1 ∈ Sᶜ} := rfl
  rw [he, type_sigma_index_subset] at h
  exact h

end NatOrdinal
