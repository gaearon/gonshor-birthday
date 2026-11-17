/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.NatOrdinal.OrderedSum

/-!
# Positions inside dependent ordered sums

An initial segment ending inside a block consists of all earlier blocks followed by the
initial segment inside that block. Its ordinal position is their ordinary sum.
-/

universe u

public noncomputable section

namespace Ordinal
open Set

private def sigmaIioIso {I : Type u} [LinearOrder I] (A : I → Type u)
    [∀ i, LinearOrder (A i)] (j : I) (a : A j) :
    ((Σₗ i : Set.Iio j, A i.1) ⊕ₗ Set.Iio a) ≃o
      Set.Iio (toLex ⟨j, a⟩ : Σₗ i, A i) := by
  let f : ((Σₗ i : Set.Iio j, A i.1) ⊕ₗ Set.Iio a) →
      Set.Iio (toLex ⟨j, a⟩ : Σₗ i, A i) := fun z ↦
    Sum.elim
      (fun w ↦ ⟨toLex ⟨(ofLex w).1.1, (ofLex w).2⟩,
        Sigma.Lex.left _ _ (ofLex w).1.2⟩)
      (fun b ↦ ⟨toLex ⟨j, b.1⟩, Sigma.Lex.right _ _ b.2⟩) (ofLex z)
  have hf : StrictMono f := by
    intro z w h
    change Sum.Lex ((· < ·) : (Σₗ i : Set.Iio j, A i.1) → _ → Prop)
      ((· < ·) : Set.Iio a → _ → Prop) (ofLex z) (ofLex w) at h
    cases h with
    | inl h =>
      rename_i z w
      obtain ⟨⟨i, hi⟩, b⟩ := z
      obtain ⟨⟨k, hk⟩, c⟩ := w
      change Sigma.Lex ((· < ·) : Set.Iio j → Set.Iio j → Prop)
        (fun i (a b : A i.1) ↦ a < b) ⟨⟨i, hi⟩, b⟩ ⟨⟨k, hk⟩, c⟩ at h
      change Sigma.Lex ((· < ·) : I → I → Prop)
        (fun i (a b : A i) ↦ a < b) ⟨i, b⟩ ⟨k, c⟩
      cases h with
      | left a b h => exact Sigma.Lex.left _ _ h
      | right a b h => exact Sigma.Lex.right _ _ h
    | inr h => exact Sigma.Lex.right _ _ h
    | sep z w => exact Sigma.Lex.left _ _ (ofLex z).1.2
  apply OrderIso.ofSurjective (OrderEmbedding.ofStrictMono f hf)
  rintro ⟨⟨i, b⟩, h⟩
  change Sigma.Lex ((· < ·) : I → I → Prop)
    (fun i (a b : A i) ↦ a < b) ⟨i, b⟩ ⟨j, a⟩ at h
  cases h with
  | left b a h => exact ⟨toLex (Sum.inl (toLex ⟨⟨i, h⟩, b⟩)), rfl⟩
  | right b a h => exact ⟨toLex (Sum.inr ⟨b, h⟩), rfl⟩

/-- The position inside an ordered sum is the earlier block sum plus its position in its block. -/
theorem typein_sigma {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (A : I → Type u) [∀ i, LinearOrder (A i)] [∀ i, WellFoundedLT (A i)]
    (j : I) (a : A j) :
    typein ((· < ·) : (Σₗ i, A i) → _ → Prop) (toLex ⟨j, a⟩) =
      (typeLT (Σₗ i : Set.Iio j, A i.1)) + typein ((· < ·) : A j → _ → Prop) a := by
  rw [← Ordinal.type_Iio_lt, ← (sigmaIioIso A j a).toRelIsoLT.ordinalType_congr,
    Ordinal.type_lt_sum_lex, Ordinal.type_Iio_lt]

/-- The rank in a small ordinal type is its original ordinal coordinate. -/
theorem typein_toType_eq_toOrd {o : Ordinal.{u}} (t : o.ToType) :
    typein ((· < ·) : o.ToType → _ → Prop) t = t.toOrd.1 := by
  let f : o.ToType → Iio o := fun t ↦
    ⟨typein ((· < ·) : o.ToType → _ → Prop) t, by
      simpa only [type_toType, mem_Iio] using typein_lt_type ((· < ·) : o.ToType → _ → Prop) t⟩
  have hf : StrictMono f := fun _ _ h ↦ (typein_lt_typein _).mpr h
  have hsurj : Function.Surjective f := by
    intro a
    obtain ⟨s, hs⟩ := typein_surj ((· < ·) : o.ToType → _ → Prop)
      (by simpa only [type_toType, mem_Iio] using a.2)
    exact ⟨s, Subtype.ext hs⟩
  let e := OrderIso.ofSurjective (OrderEmbedding.ofStrictMono f hf) hsurj
  have he : e.toRelIsoLT.toInitialSeg = ToType.mk.symm.toRelIsoLT.toInitialSeg :=
    Subsingleton.elim _ _
  exact congrArg (fun g ↦ (g t).val) he


end Ordinal
