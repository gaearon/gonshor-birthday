/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.NatOrdinal.ProductSum

/-!
# Product bounds assembled from finite ordered fibres

Each output block is bounded by the ordered cell budgets in one finite fibre.
If the whole fibre order is compatible with both input indices, concatenating
all output blocks fits the natural product of the two input ordered sums.
The source index sets and block lengths are arbitrary, including empty fibres.
-/

universe u
public noncomputable section
open scoped Ordinal

namespace NatOrdinal

/-- Finite output fibres bounded by cell products fit the product of the full input sums. -/
theorem of_type_sigma_mul_le_of_fibres {I J S : Type u}
    [LinearOrder I] [WellFoundedLT I] [LinearOrder J] [WellFoundedLT J]
    [LinearOrder S] [WellFoundedLT S]
    (a : I → NatOrdinal.{u}) (b : J → NatOrdinal.{u}) (c : S → NatOrdinal.{u})
    (n : S → ℕ) (e : (Σₗ s : S, Fin (n s)) ≃ I × J) (he : Monotone e.symm)
    (hc : ∀ s, c s ≤ of (typeLT (Σₗ i : Fin (n s),
      (a (e (toLex ⟨s, i⟩)).1 * b (e (toLex ⟨s, i⟩)).2).val.ToType))) :
    of (typeLT (Σₗ s : S, (c s).val.ToType)) ≤
      of (typeLT (Σₗ i : I, (a i).val.ToType)) *
        of (typeLT (Σₗ j : J, (b j).val.ToType)) := by
  let K := Σₗ s : S, Fin (n s)
  let p (k : K) := a (e k).1 * b (e k).2
  have hE (s : S) : Nonempty ((· < · : (c s).val.ToType → _ → Prop) ↪r
      (· < · : (Σₗ i : Fin (n s), (p (toLex ⟨s, i⟩)).val.ToType) → _ → Prop)) := by
    apply Ordinal.type_le_iff'.mp
    simpa only [Ordinal.type_toType, val_of] using val.monotone (hc s)
  let E (s : S) := Classical.choice (hE s)
  let f : (Σₗ s : S, (c s).val.ToType) → (Σₗ k : K, (p k).val.ToType) := fun z ↦
    toLex ⟨toLex ⟨(ofLex z).1, (ofLex (E (ofLex z).1 (ofLex z).2)).1⟩,
      (ofLex (E (ofLex z).1 (ofLex z).2)).2⟩
  have hf : StrictMono f := by
    rintro ⟨s, x⟩ ⟨t, y⟩ h
    change Sigma.Lex ((· < ·) : S → _ → Prop)
      (fun s (x y : (c s).val.ToType) ↦ x < y) ⟨s, x⟩ ⟨t, y⟩ at h
    cases h with
    | left x y h => exact Sigma.Lex.left _ _ (Sigma.Lex.left _ _ h)
    | @right s x y h =>
      have hg : StrictMono (fun z : (Σₗ i : Fin (n s), (p (toLex ⟨s, i⟩)).val.ToType) ↦
          (toLex ⟨toLex ⟨s, (ofLex z).1⟩, (ofLex z).2⟩ :
            Σₗ k : K, (p k).val.ToType)) := by
        rintro ⟨i, a⟩ ⟨j, b⟩ hab
        change Sigma.Lex ((· < ·) : Fin (n s) → _ → Prop)
          (fun i (a b : (p (toLex ⟨s, i⟩)).val.ToType) ↦ a < b) ⟨i, a⟩ ⟨j, b⟩ at hab
        cases hab with
        | left a b hij => exact Sigma.Lex.left _ _ (Sigma.Lex.right _ _ hij)
        | right a b hab => exact Sigma.Lex.right _ _ hab
      exact hg ((E s).map_rel_iff.mpr h)
  exact (of.monotone (RelEmbedding.ofMonotone f hf).ordinal_type_le).trans
    (of_type_sigma_mul_le a b e he)

end NatOrdinal
