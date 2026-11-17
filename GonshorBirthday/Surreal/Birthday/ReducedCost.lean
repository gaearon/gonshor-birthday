/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.PlusCount
public import GonshorBirthday.NatOrdinal.FiniteBlocks
public import GonshorBirthday.NatOrdinal.CantorSupport

import Mathlib.Logic.Equiv.Prod
import GonshorBirthday.NatOrdinal.PowerSum

/-!
# Reduced omega-map lengths from intrinsic prefix positions

Each retained sign position has weight `omega^(p+1)`, where `p` is the original canonical plus
count before that position. The weights are summed in position order, with an initial unit added
ordinarily. A cutoff retains every plus and exactly those minuses whose right prefix is below
or equal to the cutoff. Prefixes preserve all earlier decisions and their original weights.
-/

universe u

public noncomputable section

namespace Surreal

open Ordinal Order

private theorem type_sigma_le_of_embedding {I J : Type u} {A : I → Type u} {B : J → Type u}
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
      (fun (i : I) (a b : A i) ↦ a < b) ⟨i, a⟩ ⟨j, b⟩ at h
    cases h with
    | left a b h => exact Sigma.Lex.left _ _ (e.strictMono h)
    | right a b h => exact Sigma.Lex.right _ _ ((f _).strictMono h)
  exact (RelEmbedding.ofMonotone g hg).ordinal_type_le

private theorem type_sigma_lt_of_embedding {I J : Type u} {A : I → Type u} {B : J → Type u}
    [LinearOrder I] [WellFoundedLT I] [LinearOrder J] [WellFoundedLT J]
    [∀ i, LinearOrder (A i)] [∀ i, WellFoundedLT (A i)]
    [∀ j, LinearOrder (B j)] [∀ j, WellFoundedLT (B j)]
    (e : I ↪o J) (f : ∀ i, A i ↪o B (e i)) (j : J) (b : B j)
    (hj : ∀ i, e i < j) : typeLT (Σₗ i, A i) < typeLT (Σₗ j, B j) := by
  let z : (Σₗ j, B j) := toLex ⟨j, b⟩
  let g : (Σₗ i, A i) → Set.Iio z := fun y ↦
    ⟨toLex ⟨e (ofLex y).1, f (ofLex y).1 (ofLex y).2⟩,
      Sigma.Lex.left _ _ (hj (ofLex y).1)⟩
  have hg : StrictMono g := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    change Sigma.Lex ((· < ·) : I → I → Prop)
      (fun (i : I) (a b : A i) ↦ a < b) ⟨i, a⟩ ⟨j, b⟩ at h
    cases h with
    | left a b h => exact Sigma.Lex.left _ _ (e.strictMono h)
    | right a b h => exact Sigma.Lex.right _ _ ((f _).strictMono h)
  exact ((RelEmbedding.ofMonotone g hg).ordinal_type_le.trans_eq
    (Ordinal.type_Iio_lt z)).trans_lt (Ordinal.typein_lt_type _ z)

private theorem type_sigma_of_isEmpty {I : Type u} (A : I → Type u)
    [LinearOrder I] [WellFoundedLT I] [IsEmpty I]
    [∀ i, LinearOrder (A i)] [∀ i, WellFoundedLT (A i)] :
    typeLT (Σₗ i, A i) = 0 := by
  have : IsEmpty (Σₗ i, A i) := ⟨fun z ↦ isEmptyElim (ofLex z).1⟩
  exact Ordinal.type_eq_zero_of_empty _

private theorem type_sigma_unique {I : Type u} [LinearOrder I] [WellFoundedLT I] [Unique I]
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

/-- The ordinal sum `1 + ∑ i ∈ S, ω^ (p i + 1)` over a set `S` of sign positions of `x`, in
increasing order, where `p i` is the number of plus signs before position `i`. For `S = univ`
this is the birthday of `ω^ x`. -/
def omegaExpansionLength (x : Surreal.{u}) (S : Set x.birthday.val.ToType) : NatOrdinal.{u} :=
  NatOrdinal.of (1 + typeLT (Σₗ i : S,
    (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of i.1.toOrd.1)) + 1)).val.ToType))

theorem omegaExpansionLength_eq (x : Surreal.{u}) (S : Set x.birthday.val.ToType) :
    omegaExpansionLength x S = NatOrdinal.of (1 + typeLT (Σₗ i : S,
      (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of i.1.toOrd.1)) + 1)).val.ToType)) := by
  unfold omegaExpansionLength
  rfl

/-- Deleting every exponent sign leaves the initial plus sign. -/
@[simp]
theorem omegaExpansionLength_empty (x : Surreal.{u}) : omegaExpansionLength x ∅ = 1 := by
  have : IsEmpty (Σₗ i : (∅ : Set x.birthday.val.ToType),
      (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of i.1.toOrd.1)) + 1)).val.ToType) :=
    ⟨fun z ↦ (ofLex z).1.2⟩
  rw [omegaExpansionLength_eq, Ordinal.type_eq_zero_of_empty, add_zero, NatOrdinal.of_one]

/-- Every expanded word retains its initial plus sign. -/
theorem one_le_omegaExpansionLength (x : Surreal.{u}) (S : Set x.birthday.val.ToType) :
    1 ≤ omegaExpansionLength x S := by
  rw [omegaExpansionLength_eq]
  exact NatOrdinal.of.monotone le_self_add

/-- Retaining additional original positions cannot shorten the expanded ordinal word. -/
theorem omegaExpansionLength_mono (x : Surreal.{u}) : Monotone (omegaExpansionLength x) := by
  intro S T hST
  rw [omegaExpansionLength_eq, omegaExpansionLength_eq]
  apply NatOrdinal.of.monotone
  apply add_le_add_right
  let W (i : x.birthday.val.ToType) :=
    (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of i.toOrd.1)) + 1)).val.ToType
  let f : (Σₗ i : S, W i.1) → (Σₗ i : T, W i.1) :=
    fun z ↦ toLex ⟨⟨(ofLex z).1.1, hST (ofLex z).1.2⟩, (ofLex z).2⟩
  have hf : StrictMono f := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    change Sigma.Lex ((· < ·) : S → S → Prop)
      (fun (i : S) (a b : W i.1) ↦ a < b) ⟨i, a⟩ ⟨j, b⟩ at h
    cases h with
    | left i j h => exact Sigma.Lex.left _ _ h
    | right a b h => exact Sigma.Lex.right _ _ h
  exact (RelEmbedding.ofMonotone f hf).ordinal_type_le

/-- The sign positions of `x` retained by the cutoff `C`: every plus, and each minus whose
right prefix is at most `C`. -/
def reducedOmegaPositions (C x : Surreal.{u}) : Set x.birthday.val.ToType :=
  {i | birthdayTruncation x (NatOrdinal.of i.toOrd.1) < x ∨
    birthdayTruncation x (NatOrdinal.of i.toOrd.1) ≤ C}

theorem mem_reducedOmegaPositions {C x : Surreal.{u}} {i : x.birthday.val.ToType} :
    i ∈ reducedOmegaPositions C x ↔ birthdayTruncation x (NatOrdinal.of i.toOrd.1) < x ∨
      birthdayTruncation x (NatOrdinal.of i.toOrd.1) ≤ C := by
  unfold reducedOmegaPositions
  rfl

/-- The expansion length of `x` over the sign positions retained by the cutoff `C`. See
`reducedOmegaPositions`. -/
def reducedOmegaCost (C x : Surreal.{u}) : NatOrdinal.{u} :=
  omegaExpansionLength x (reducedOmegaPositions C x)

theorem reducedOmegaCost_eq_positions (C x : Surreal.{u}) :
    reducedOmegaCost C x = omegaExpansionLength x (reducedOmegaPositions C x) := by
  unfold reducedOmegaCost
  rfl

theorem reducedOmegaCost_eq (C x : Surreal.{u}) :
    reducedOmegaCost C x = omegaExpansionLength x
      {i | birthdayTruncation x (NatOrdinal.of i.toOrd.1) < x ∨
        birthdayTruncation x (NatOrdinal.of i.toOrd.1) ≤ C} := by
  unfold reducedOmegaCost reducedOmegaPositions
  rfl

theorem reducedOmegaCost_eq_of_birthday_eq (C : Surreal.{u})
    {x : Surreal.{u}} {b : NatOrdinal.{u}} (hb : x.birthday = b) :
    reducedOmegaCost C x = NatOrdinal.of (1 + typeLT (Σₗ i :
      {i : b.val.ToType | birthdayTruncation x (NatOrdinal.of i.toOrd.1) < x ∨
        birthdayTruncation x (NatOrdinal.of i.toOrd.1) ≤ C},
      (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of i.1.toOrd.1)) + 1)).val.ToType)) := by
  subst b
  rw [reducedOmegaCost_eq, omegaExpansionLength_eq]

/-- Moving the cutoff upward can only retain additional signs. -/
theorem reducedOmegaCost_mono (x : Surreal.{u}) : Monotone (fun C ↦ reducedOmegaCost C x) := by
  intro C D hCD
  change reducedOmegaCost C x ≤ reducedOmegaCost D x
  rw [reducedOmegaCost_eq, reducedOmegaCost_eq]
  apply omegaExpansionLength_mono
  intro i hi
  exact hi.imp_right (fun h ↦ h.trans hCD)

/-- The reduced cost is nonzero, including the empty exponent word. -/
theorem one_le_reducedOmegaCost (C x : Surreal.{u}) : 1 ≤ reducedOmegaCost C x := by
  rw [reducedOmegaCost_eq]
  exact one_le_omegaExpansionLength x _

/-- The cost at the input value retains only its plus positions. -/
theorem reducedOmegaCost_self (x : Surreal.{u}) :
    reducedOmegaCost x x = omegaExpansionLength x
      {i | birthdayTruncation x (NatOrdinal.of i.toOrd.1) < x} := by
  rw [reducedOmegaCost_eq]
  congr 1
  ext i
  change (_ ∨ _) ↔ _
  have hi : NatOrdinal.of i.toOrd.1 < x.birthday := NatOrdinal.of.strictMono i.toOrd.2
  have hne : birthdayTruncation x (NatOrdinal.of i.toOrd.1) ≠ x := by
    intro he
    have hb := birthday_birthdayTruncation x hi.le
    rw [he] at hb
    exact hi.ne hb.symm
  exact ⟨fun h ↦ h.elim id (fun h ↦ h.lt_of_ne hne), Or.inl⟩

private theorem reducedOmegaCost_birthdayTruncation_bounds (C x : Surreal.{u})
    {a : NatOrdinal.{u}}
    (ha : a ≤ x.birthday) :
    reducedOmegaCost C (birthdayTruncation x a) ≤ reducedOmegaCost C x ∧
      (a < x.birthday → (birthdayTruncation x a < x ∨ birthdayTruncation x a ≤ C) →
        reducedOmegaCost C (birthdayTruncation x a) < reducedOmegaCost C x) := by
  rw [reducedOmegaCost_eq_of_birthday_eq C (birthday_birthdayTruncation x ha),
    reducedOmegaCost_eq_of_birthday_eq C rfl]
  let S := {i : a.val.ToType |
    birthdayTruncation (birthdayTruncation x a) (NatOrdinal.of i.toOrd.1) <
      birthdayTruncation x a ∨
    birthdayTruncation (birthdayTruncation x a) (NatOrdinal.of i.toOrd.1) ≤ C}
  let T := {i : x.birthday.val.ToType |
    birthdayTruncation x (NatOrdinal.of i.toOrd.1) < x ∨
    birthdayTruncation x (NatOrdinal.of i.toOrd.1) ≤ C}
  have hv (i : a.val.ToType) :
      birthdayTruncation (birthdayTruncation x a) (NatOrdinal.of i.toOrd.1) =
        birthdayTruncation x (NatOrdinal.of i.toOrd.1) :=
    birthdayTruncation_birthdayTruncation x (NatOrdinal.of.strictMono i.toOrd.2).le ha
  let f : S → T := fun i ↦
    ⟨Ordinal.ToType.mk ⟨i.1.toOrd.1, i.1.toOrd.2.trans_le (NatOrdinal.val.monotone ha)⟩, by
      change birthdayTruncation x (NatOrdinal.of ((Ordinal.ToType.mk _).toOrd.1)) < x ∨
        birthdayTruncation x (NatOrdinal.of ((Ordinal.ToType.mk _).toOrd.1)) ≤ C
      simp only [Ordinal.ToType.toOrd, OrderIso.symm_apply_apply]
      have h := i.2
      change _ ∨ _ at h
      rw [hv i.1] at h
      exact h.imp_left ((birthdayTruncation_lt_birthdayTruncation_iff x
        (NatOrdinal.of.strictMono i.1.toOrd.2) ha).mp)⟩
  have hf : StrictMono f := by
    intro i j hij
    change Ordinal.ToType.mk _ < Ordinal.ToType.mk _
    exact Ordinal.ToType.mk.strictMono (Ordinal.ToType.mk.symm.strictMono hij)
  let W (i : S) := (ω^ (plusCount (birthdayTruncation (birthdayTruncation x a)
    (NatOrdinal.of i.1.toOrd.1)) + 1)).val.ToType
  let V (i : T) := (ω^ (plusCount (birthdayTruncation x
    (NatOrdinal.of i.1.toOrd.1)) + 1)).val.ToType
  have hF (i : S) : Nonempty (W i ≃o V (f i)) := by
    have he : typeLT
      (ω^ (plusCount (birthdayTruncation (birthdayTruncation x a)
        (NatOrdinal.of i.1.toOrd.1)) + 1)).val.ToType = typeLT
      (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of (f i).1.toOrd.1)) + 1)).val.ToType := by
      simp only [Ordinal.type_toType, f, Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, hv]
    exact ⟨OrderIso.ofRelIsoLT (Classical.choice (Ordinal.type_eq.mp he))⟩
  let F : ∀ i : S, W i ↪o V (f i) := fun i ↦ (Classical.choice (hF i)).toOrderEmbedding
  constructor
  · apply NatOrdinal.of.monotone
    apply add_le_add_right
    exact type_sigma_le_of_embedding (OrderEmbedding.ofStrictMono f hf) F
  · intro ha' hr
    apply NatOrdinal.of.strictMono
    apply (Ordinal.isNormal_add_right 1).strictMono
    let j : T := ⟨Ordinal.ToType.mk ⟨a.val, NatOrdinal.val.strictMono ha'⟩, by
      change birthdayTruncation x (NatOrdinal.of ((Ordinal.ToType.mk _).toOrd.1)) < x ∨
        birthdayTruncation x (NatOrdinal.of ((Ordinal.ToType.mk _).toOrd.1)) ≤ C
      simpa only [Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val] using hr⟩
    let b : V j := Ordinal.ToType.mk ⟨0, NatOrdinal.wpow_pos _⟩
    apply type_sigma_lt_of_embedding (OrderEmbedding.ofStrictMono f hf) F j b
    intro i
    change Ordinal.ToType.mk _ < Ordinal.ToType.mk _
    exact Ordinal.ToType.mk.strictMono i.1.toOrd.2

/-- A canonical exponent prefix has no larger reduced cost at the same cutoff. -/
theorem reducedOmegaCost_birthdayTruncation_le (C x : Surreal.{u}) {a : NatOrdinal.{u}}
    (ha : a ≤ x.birthday) :
    reducedOmegaCost C (birthdayTruncation x a) ≤ reducedOmegaCost C x :=
  (reducedOmegaCost_birthdayTruncation_bounds C x ha).1

/-- A retained next sign makes the canonical-prefix cost strictly smaller. -/
theorem reducedOmegaCost_birthdayTruncation_lt (C x : Surreal.{u}) {a : NatOrdinal.{u}}
    (ha : a < x.birthday)
    (hr : birthdayTruncation x a < x ∨ birthdayTruncation x a ≤ C) :
    reducedOmegaCost C (birthdayTruncation x a) < reducedOmegaCost C x :=
  (reducedOmegaCost_birthdayTruncation_bounds C x ha.le).2 ha hr

/-- Every canonical left prefix has strictly smaller cost at the same cutoff. -/
theorem reducedOmegaCost_lt_of_mem_leftPrefixes (C : Surreal.{u})
    {x y : Surreal.{u}} (hy : y ∈ leftPrefixes x) :
    reducedOmegaCost C y < reducedOmegaCost C x := by
  obtain ⟨a, ha, rfl, hl⟩ := mem_leftPrefixes.mp hy
  exact reducedOmegaCost_birthdayTruncation_lt C x ha (Or.inl hl)

/-- A canonical right prefix below the cutoff has strictly smaller cost. -/
theorem reducedOmegaCost_lt_of_mem_rightPrefixes {C x y : Surreal.{u}}
    (hy : y ∈ rightPrefixes x) (hC : y ≤ C) :
    reducedOmegaCost C y < reducedOmegaCost C x := by
  obtain ⟨a, ha, rfl, _⟩ := mem_rightPrefixes.mp hy
  exact reducedOmegaCost_birthdayTruncation_lt C x ha (Or.inr hC)

/-- Zero has only the initial unit in its reduced expansion. -/
@[simp]
theorem reducedOmegaCost_zero (C : Surreal.{u}) : reducedOmegaCost C 0 = 1 := by
  rw [reducedOmegaCost_eq_of_birthday_eq C birthday_zero, NatOrdinal.val_zero]
  rw [type_sigma_of_isEmpty, add_zero, NatOrdinal.of_one]

/-- For a one-sign exponent, the one expanded block is retained exactly at its actual cutoff. -/
theorem reducedOmegaCost_of_birthday_one (C : Surreal.{u}) {x : Surreal.{u}}
    (hx : x.birthday = 1) :
    reducedOmegaCost C x = if 0 < x ∨ 0 ≤ C then NatOrdinal.of Ordinal.omega0 else 1 := by
  classical
  rw [reducedOmegaCost_eq_of_birthday_eq C hx]
  have hi (i : (1 : NatOrdinal.{u}).val.ToType) : NatOrdinal.of i.toOrd.1 = 0 := by
    have hz : i.toOrd.1 = 0 := by simpa using i.toOrd.2
    rw [hz, NatOrdinal.of_zero]
  let G (p : (1 : NatOrdinal.{u}).val.ToType → Surreal.{u}) : NatOrdinal.{u} :=
    NatOrdinal.of (1 + typeLT (Σₗ i : {i | p i < x ∨ p i ≤ C},
      (ω^ (plusCount (p i.1) + 1)).val.ToType))
  change G (fun i ↦ birthdayTruncation x (NatOrdinal.of i.toOrd.1)) = _
  have hp : (fun i : (1 : NatOrdinal.{u}).val.ToType ↦
      birthdayTruncation x (NatOrdinal.of i.toOrd.1)) = fun _ ↦ 0 := by
    funext i
    rw [hi, birthdayTruncation_zero]
  rw [hp]
  change NatOrdinal.of (1 + typeLT (Σₗ i :
    {i : (1 : NatOrdinal.{u}).val.ToType | 0 < x ∨ 0 ≤ C},
    (ω^ (plusCount (0 : Surreal.{u}) + 1)).val.ToType)) = _
  rw [plusCount_zero, zero_add, NatOrdinal.wpow_one, NatOrdinal.val_of]
  have hsingle : Subsingleton (1 : NatOrdinal.{u}).val.ToType := by
    constructor
    intro i j
    apply Ordinal.ToType.mk.symm.injective
    apply Subtype.ext
    have hz (k : (1 : NatOrdinal.{u}).val.ToType) : k.toOrd.1 = 0 := by
      simpa using k.toOrd.2
    exact (hz i).trans (hz j).symm
  by_cases h : 0 < x ∨ 0 ≤ C
  · rw [ite_eq_left h]
    let _ : Unique {i : (1 : NatOrdinal.{u}).val.ToType | 0 < x ∨ 0 ≤ C} :=
      { default := ⟨Ordinal.ToType.mk ⟨0, by simp⟩, h⟩
        uniq := fun i ↦ Subtype.ext (Subsingleton.elim _ _) }
    rw [type_sigma_unique, Ordinal.one_add_omega0]
  · rw [ite_eq_right h]
    have : IsEmpty {i : (1 : NatOrdinal.{u}).val.ToType | 0 < x ∨ 0 ≤ C} := ⟨fun i ↦ h i.2⟩
    rw [type_sigma_of_isEmpty, add_zero, NatOrdinal.of_one]

/-- For the exponent minus one, the cutoff zero is an exact jump from one to omega. -/
theorem reducedOmegaCost_neg_one (C : Surreal.{u}) :
    reducedOmegaCost C (-1) = if 0 ≤ C then NatOrdinal.of Ordinal.omega0 else 1 := by
  simpa only [neg_pos, not_lt_of_ge (zero_le_one : (0 : Surreal.{u}) ≤ 1), false_or] using
    reducedOmegaCost_of_birthday_one C (x := -1) (by simp)

/-- The plus in the exponent one is retained at every cutoff. -/
@[simp]
theorem reducedOmegaCost_one (C : Surreal.{u}) :
    reducedOmegaCost C 1 = NatOrdinal.of Ordinal.omega0 := by
  simpa only [zero_lt_one, true_or, ite_true] using
    reducedOmegaCost_of_birthday_one C (x := 1) birthday_one

/-- Once a right prefix is retained, every later prefix is below its cutoff. -/
theorem birthdayTruncation_le_cutoff_of_rightPrefix_le {C x : Surreal.{u}}
    {a b : NatOrdinal.{u}} (hab : a ≤ b) (hb : b ≤ x.birthday)
    (hra : x < birthdayTruncation x a) (hCa : birthdayTruncation x a ≤ C) :
    birthdayTruncation x b ≤ C := by
  rcases hab.lt_or_eq with hab | rfl
  · apply le_trans ?_ hCa
    apply le_of_not_gt
    intro h
    exact hra.not_gt ((birthdayTruncation_lt_birthdayTruncation_iff x hab hb).mp h)
  · exact hCa

/-- Keeping only the plus positions has exact expanded length `omega^(x⁺)`. -/
theorem omegaExpansionLength_plusPositions (x : Surreal.{u}) :
    omegaExpansionLength x {i | birthdayTruncation x (NatOrdinal.of i.toOrd.1) < x} =
      ω^ plusCount x := by
  rw [omegaExpansionLength_eq]
  let S := {i : x.birthday.val.ToType |
    birthdayTruncation x (NatOrdinal.of i.toOrd.1) < x}
  let p : S → NatOrdinal.{u} := fun i ↦
    plusCount (birthdayTruncation x (NatOrdinal.of i.1.toOrd.1))
  apply NatOrdinal.of_one_add_type_sigma_wpow_eq p (plusCount x)
  · intro i j hij
    have hri : NatOrdinal.of i.1.toOrd.1 < NatOrdinal.of j.1.toOrd.1 :=
      NatOrdinal.of.strictMono (Ordinal.ToType.mk.symm.strictMono hij)
    have hrj : NatOrdinal.of j.1.toOrd.1 < x.birthday :=
      NatOrdinal.of.strictMono j.1.toOrd.2
    have hv := birthdayTruncation_birthdayTruncation x hri.le hrj.le
    have hi : NatOrdinal.of i.1.toOrd.1 <
        (birthdayTruncation x (NatOrdinal.of j.1.toOrd.1)).birthday := by
      rw [birthday_birthdayTruncation x hrj.le]
      exact hri
    have hl : birthdayTruncation (birthdayTruncation x (NatOrdinal.of j.1.toOrd.1))
        (NatOrdinal.of i.1.toOrd.1) < birthdayTruncation x (NatOrdinal.of j.1.toOrd.1) := by
      rw [hv]
      exact (birthdayTruncation_lt_birthdayTruncation_iff x hri hrj.le).mpr i.2
    have h := plusCount_birthdayTruncation_lt _ hi hl
    rw [hv] at h
    exact h
  · intro i
    exact plusCount_birthdayTruncation_lt x (NatOrdinal.of.strictMono i.1.toOrd.2) i.2
  · intro b hb
    obtain ⟨z, hz, hbz⟩ := exists_leftPrefixes_plusCount_ge hb
    obtain ⟨a, ha, hxa, hl⟩ := mem_leftPrefixes.mp hz
    let i : S := ⟨Ordinal.ToType.mk ⟨a.val, NatOrdinal.val.strictMono ha⟩, by
      change birthdayTruncation x (NatOrdinal.of ((Ordinal.ToType.mk _).toOrd.1)) < x
      simpa only [Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val, hxa]
        using hl⟩
    refine ⟨i, ?_⟩
    change b ≤ plusCount (birthdayTruncation x (NatOrdinal.of i.1.toOrd.1))
    simpa only [i, Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val, hxa]
      using hbz

/-- At cutoff `x`, all and only plus signs survive, giving the exact pure-power baseline. -/
@[simp]
theorem reducedOmegaCost_self_eq_wpow (x : Surreal.{u}) :
    reducedOmegaCost x x = ω^ plusCount x := by
  rw [reducedOmegaCost_self, omegaExpansionLength_plusPositions]

/-- Every cutoff retains the full pure-power contribution of the plus signs. -/
theorem wpow_plusCount_le_reducedOmegaCost (C x : Surreal.{u}) :
    ω^ plusCount x ≤ reducedOmegaCost C x := by
  rw [← omegaExpansionLength_plusPositions x, reducedOmegaCost_eq]
  apply omegaExpansionLength_mono
  exact fun _ hi ↦ Or.inl hi

private theorem plusCount_prefix_mono (x : Surreal.{u}) {a b : NatOrdinal.{u}}
    (hab : a ≤ b) (hb : b ≤ x.birthday) :
    plusCount (birthdayTruncation x a) ≤ plusCount (birthdayTruncation x b) := by
  have ha : a ≤ (birthdayTruncation x b).birthday := by
    rw [birthday_birthdayTruncation x hb]
    exact hab
  simpa only [birthdayTruncation_birthdayTruncation x hab hb] using
    plusCount_birthdayTruncation_le (birthdayTruncation x b) ha

/-- Retaining every plus forces every Cantor exponent of the expanded length above its rank. -/
theorem plusCount_le_cantorSupport_omegaExpansionLength (x : Surreal.{u})
    (S : Set x.birthday.val.ToType)
    (hS : ∀ i, birthdayTruncation x (NatOrdinal.of i.toOrd.1) < x → i ∈ S) :
    ∀ e ∈ NatOrdinal.cantorSupport (omegaExpansionLength x S), plusCount x ≤ e := by
  intro e he
  by_contra h
  have he' : e < plusCount x := lt_of_not_ge h
  obtain ⟨z, hz, hez⟩ := exists_leftPrefixes_plusCount_ge he'
  obtain ⟨a, ha, hxa, hl⟩ := mem_leftPrefixes.mp hz
  let j : S := ⟨Ordinal.ToType.mk ⟨a.val, NatOrdinal.val.strictMono ha⟩, by
    apply hS
    simpa only [Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val, hxa]
      using hl⟩
  let p : S → NatOrdinal.{u} := fun i ↦
    plusCount (birthdayTruncation x (NatOrdinal.of i.1.toOrd.1)) + 1
  have hj : plusCount z + 1 ≤ e := by
    rw [omegaExpansionLength_eq] at he
    apply NatOrdinal.le_cantorSupport_of_type_sigma_wpow_tail
      p j (plusCount z + 1) 1 ?_ e he
    intro i hji
    have hri : NatOrdinal.of i.1.toOrd.1 ≤ x.birthday :=
      (NatOrdinal.of.strictMono i.1.toOrd.2).le
    have hji' : a ≤ NatOrdinal.of i.1.toOrd.1 := by
      have hh := NatOrdinal.of.monotone (Ordinal.ToType.mk.symm.monotone hji)
      simpa only [j, Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val] using hh
    change plusCount z + 1 ≤ plusCount (birthdayTruncation x (NatOrdinal.of i.1.toOrd.1)) + 1
    rw [← hxa]
    exact add_le_add (plusCount_prefix_mono x hji' hri) le_rfl
  exact (lt_add_one (plusCount z)).not_ge (hj.trans hez)

/-- Every Cantor exponent of a reduced cost is at least the original exponent's plus count. -/
theorem plusCount_le_cantorSupport_reducedOmegaCost (C x : Surreal.{u}) :
    ∀ e ∈ NatOrdinal.cantorSupport (reducedOmegaCost C x), plusCount x ≤ e := by
  rw [reducedOmegaCost_eq]
  exact plusCount_le_cantorSupport_omegaExpansionLength x _ (fun _ hi ↦ Or.inl hi)

/-- Every proper reduced-cost prefix leaves room for one full original plus-count power. -/
theorem oadd_wpow_plusCount_le_reducedOmegaCost {C x : Surreal.{u}} {h : NatOrdinal.{u}}
    (hh : h < reducedOmegaCost C x) :
    NatOrdinal.of (h.val + (ω^ plusCount x).val) ≤ reducedOmegaCost C x :=
  NatOrdinal.oadd_wpow_le_of_lt_of_le_cantorSupport hh
    (plusCount_le_cantorSupport_reducedOmegaCost C x)

/-- A nonempty retained set gives a limit length, regardless of which signs were deleted. -/
theorem isSuccLimit_omegaExpansionLength_of_nonempty (x : Surreal.{u})
    (S : Set x.birthday.val.ToType) (hS : S.Nonempty) :
    IsSuccLimit (omegaExpansionLength x S).val := by
  obtain ⟨j, hj⟩ := hS
  have hs : ∀ e ∈ NatOrdinal.cantorSupport (omegaExpansionLength x S),
      (1 : NatOrdinal.{u}) ≤ e := by
    rw [omegaExpansionLength_eq]
    exact NatOrdinal.le_cantorSupport_of_type_sigma_wpow_tail
      (fun i : S ↦ plusCount (birthdayTruncation x (NatOrdinal.of i.1.toOrd.1)) + 1)
      ⟨j, hj⟩ 1 1 (fun _ _ ↦ le_add_of_nonneg_left bot_le)
  obtain ⟨q, hq⟩ := NatOrdinal.wpow_dvd_val_of_le_cantorSupport hs
  have hpos : 0 < (omegaExpansionLength x S).val :=
    NatOrdinal.val.strictMono ((zero_lt_one : (0 : NatOrdinal.{u}) < 1).trans_le
      (one_le_omegaExpansionLength x S))
  have hqpos : 0 < q := by
    apply pos_iff_ne_zero.mpr
    intro hqz
    rw [hqz, mul_zero] at hq
    exact hpos.ne' hq
  rw [hq, NatOrdinal.wpow_one, NatOrdinal.val_of]
  exact Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 hqpos

/-- An expanded length is either the initial unit or a limit ordinal. -/
theorem omegaExpansionLength_eq_one_or_isSuccLimit (x : Surreal.{u})
    (S : Set x.birthday.val.ToType) :
    omegaExpansionLength x S = 1 ∨ IsSuccLimit (omegaExpansionLength x S).val := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · exact Or.inl (omegaExpansionLength_empty x)
  · exact Or.inr (isSuccLimit_omegaExpansionLength_of_nonempty x S hS)

/-- Every reduced cost is either one or a limit ordinal. -/
theorem reducedOmegaCost_eq_one_or_isSuccLimit (C x : Surreal.{u}) :
    reducedOmegaCost C x = 1 ∨ IsSuccLimit (reducedOmegaCost C x).val := by
  rw [reducedOmegaCost_eq]
  exact omegaExpansionLength_eq_one_or_isSuccLimit x _

end Surreal
