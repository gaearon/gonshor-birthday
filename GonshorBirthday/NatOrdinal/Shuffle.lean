/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.NatOrdinal.Basic

/-!
# The natural-sum bound for a two-colour shuffle

The increasing map sends each position to the natural sum of the order types of its two earlier
colour classes. The proof applies to arbitrary well orders, including cofinally interleaved colours.
-/

universe u

public noncomputable section

namespace NatOrdinal

open Set Ordinal

private theorem type_lt_of_forall_lt {α : Type u} [LinearOrder α] [WellFoundedLT α]
    {s t : Set α} (hst : s ⊆ t) {x : α} (hx : x ∈ t) (hl : ∀ y ∈ s, y < x) :
    typeLT s < typeLT t := by
  let f : s → Iio (⟨x, hx⟩ : t) := fun y ↦ ⟨⟨y, hst y.2⟩, hl y y.2⟩
  have hf : StrictMono f := fun _ _ h ↦ h
  exact ((RelEmbedding.ofMonotone f hf).ordinal_type_le.trans_eq
    (type_Iio_lt (⟨x, hx⟩ : t))).trans_lt (typein_lt_type _ _)

/-- The order type of a two-colour shuffle is at most the natural sum of its colour types. -/
theorem of_type_le_add_of_type_compl {α : Type u} [LinearOrder α] [WellFoundedLT α]
    (s : Set α) : of (typeLT α) ≤ of (typeLT s) + of (typeLT (sᶜ : Set α)) := by
  classical
  let F (x : α) : NatOrdinal.{u} :=
    of (typeLT {z : α | z ∈ s ∧ z < x}) + of (typeLT {z : α | z ∈ sᶜ ∧ z < x})
  have hpart (t : Set α) {x y : α} (hxy : x ≤ y) :
      of (typeLT {z : α | z ∈ t ∧ z < x}) ≤
        of (typeLT {z : α | z ∈ t ∧ z < y}) :=
    of.monotone (type_mono fun _ hz ↦ ⟨hz.1, hz.2.trans_le hxy⟩)
  have hstrict (t : Set α) {x y : α} (hxy : x < y) (hx : x ∈ t) :
      of (typeLT {z : α | z ∈ t ∧ z < x}) <
        of (typeLT {z : α | z ∈ t ∧ z < y}) :=
    of.strictMono (type_lt_of_forall_lt
      (fun _ hz ↦ ⟨hz.1, hz.2.trans hxy⟩) ⟨hx, hxy⟩ (fun _ hz ↦ hz.2))
  have hF : StrictMono F := by
    intro x y hxy
    by_cases hx : x ∈ s
    · exact add_lt_add_of_lt_of_le (hstrict s hxy hx) (hpart sᶜ hxy.le)
    · exact add_lt_add_of_le_of_lt (hpart s hxy.le) (hstrict sᶜ hxy hx)
  have hbound (x : α) : F x < of (typeLT s) + of (typeLT (sᶜ : Set α)) := by
    have hle (t : Set α) : of (typeLT {z : α | z ∈ t ∧ z < x}) ≤ of (typeLT t) :=
      of.monotone (type_mono fun _ hz ↦ hz.1)
    have hlt (t : Set α) (hx : x ∈ t) :
        of (typeLT {z : α | z ∈ t ∧ z < x}) < of (typeLT t) :=
      of.strictMono (type_lt_of_forall_lt (fun _ hz ↦ hz.1) hx (fun _ hz ↦ hz.2))
    by_cases hx : x ∈ s
    · exact add_lt_add_of_lt_of_le (hlt s hx) (hle sᶜ)
    · exact add_lt_add_of_le_of_lt (hle s) (hlt sᶜ hx)
  let f : α → (of (typeLT s) + of (typeLT (sᶜ : Set α))).val.ToType :=
    fun x ↦ Ordinal.ToType.mk ⟨(F x).val, val.strictMono (hbound x)⟩
  have hf : StrictMono f := by
    intro x y hxy
    exact Ordinal.ToType.mk.strictMono (val.strictMono (hF hxy))
  simpa only [type_toType, of_val] using
    of.monotone (RelEmbedding.ofMonotone f hf).ordinal_type_le

end NatOrdinal
