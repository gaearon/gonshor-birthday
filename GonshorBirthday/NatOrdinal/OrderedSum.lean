/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.NatOrdinal.FiniteBlocks
public import Mathlib.SetTheory.Ordinal.Family

import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Hom.Lex
import Mathlib.SetTheory.Ordinal.Principal

/-!
# Ordinary multiplication and divisibility of ordered sums

Ordinary left multiplication distributes over arbitrary well-ordered sums. Consequently a
common left divisor of all blocks divides their ordered sum. For an omega-power divisor, it
suffices that a nonempty final interval of blocks has that divisor: the first retained block
absorbs the remainder of the earlier part.
-/

universe u

public noncomputable section

namespace Ordinal

private def sigmaLexCongrRight {I : Type u} [LinearOrder I] {A B : I → Type u}
    [∀ i, LinearOrder (A i)] [∀ i, LinearOrder (B i)] (e : ∀ i, A i ≃o B i) :
    (Σₗ i, A i) ≃o (Σₗ i, B i) where
  toEquiv := ofLex.trans ((Equiv.sigmaCongrRight (fun i ↦ (e i).toEquiv)).trans toLex)
  map_rel_iff' := by
    rintro ⟨i, a⟩ ⟨j, b⟩
    change Sigma.Lex ((· < ·) : I → I → Prop)
      (fun i (a b : B i) ↦ a ≤ b) ⟨i, e i a⟩ ⟨j, e j b⟩ ↔
      Sigma.Lex ((· < ·) : I → I → Prop)
      (fun i (a b : A i) ↦ a ≤ b) ⟨i, a⟩ ⟨j, b⟩
    by_cases h : i = j
    · subst j
      simp [Sigma.lex_iff]
    · simp [Sigma.lex_iff, h]

private def sigmaProdLexIso {I : Type u} [LinearOrder I] (A : I → Type u) (B : Type u)
    [∀ i, LinearOrder (A i)] [LinearOrder B] :
    (Σₗ i, A i ×ₗ B) ≃o ((Σₗ i, A i) ×ₗ B) where
  toFun z := toLex (toLex ⟨(ofLex z).1, (ofLex (ofLex z).2).1⟩, (ofLex (ofLex z).2).2)
  invFun z := toLex ⟨(ofLex (ofLex z).1).1,
    toLex ((ofLex (ofLex z).1).2, (ofLex z).2)⟩
  left_inv z := rfl
  right_inv z := rfl
  map_rel_iff' := by
    rintro ⟨i, ⟨a, b⟩⟩ ⟨j, ⟨c, d⟩⟩
    change Prod.Lex
      (Sigma.Lex ((· < ·) : I → I → Prop) (fun i (a b : A i) ↦ a < b))
      ((· ≤ ·) : B → B → Prop) (⟨i, a⟩, b) (⟨j, c⟩, d) ↔
      Sigma.Lex ((· < ·) : I → I → Prop)
      (fun i ↦ Prod.Lex ((· < ·) : A i → A i → Prop) ((· ≤ ·) : B → B → Prop))
      ⟨i, (a, b)⟩ ⟨j, (c, d)⟩
    by_cases h : i = j
    · subst j
      simp [Prod.lex_def, Sigma.lex_iff]
    · simp [Prod.lex_def, Sigma.lex_iff, h]

/-- Ordinary left multiplication distributes over an arbitrary well-ordered sum. -/
theorem type_sigma_mul_left {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (a : Ordinal.{u}) (f : I → Ordinal.{u}) :
    typeLT (Σₗ i, (a * f i).ToType) = a * typeLT (Σₗ i, (f i).ToType) := by
  have h (i : I) : Nonempty ((a * f i).ToType ≃o ((f i).ToType ×ₗ a.ToType)) := by
    apply Nonempty.map OrderIso.ofRelIsoLT
    apply Ordinal.type_eq.mp
    simp only [type_toType, type_lt_prod_lex]
  let e := sigmaLexCongrRight (fun i ↦ Classical.choice (h i))
  rw [e.toRelIsoLT.ordinalType_congr,
    (sigmaProdLexIso (fun i ↦ (f i).ToType) a.ToType).toRelIsoLT.ordinalType_congr,
    type_lt_prod_lex, type_toType]

/-- A common ordinary left divisor divides every well-ordered sum of its multiples. -/
theorem dvd_type_sigma {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (a : Ordinal.{u}) (f : I → Ordinal.{u}) (h : ∀ i, a ∣ f i) :
    a ∣ typeLT (Σₗ i, (f i).ToType) := by
  choose q hq using h
  have he : f = fun i ↦ a * q i := funext hq
  rw [he, type_sigma_mul_left]
  exact dvd_mul_right _ _

private def sigmaSplitIso {I : Type u} [LinearOrder I] (A : I → Type u)
    [∀ i, LinearOrder (A i)] (j : I) :
    ((Σₗ i : Set.Iio j, A i.1) ⊕ₗ (Σₗ i : Set.Ici j, A i.1)) ≃o (Σₗ i, A i) := by
  let f : ((Σₗ i : Set.Iio j, A i.1) ⊕ₗ (Σₗ i : Set.Ici j, A i.1)) → (Σₗ i, A i) :=
    fun z ↦ Sum.elim (fun z ↦ toLex ⟨(ofLex z).1.1, (ofLex z).2⟩)
      (fun z ↦ toLex ⟨(ofLex z).1.1, (ofLex z).2⟩) (ofLex z)
  have hf : StrictMono f := by
    intro z w h
    change Sum.Lex ((· < ·) : (Σₗ i : Set.Iio j, A i.1) → _ → Prop)
      ((· < ·) : (Σₗ i : Set.Ici j, A i.1) → _ → Prop) (ofLex z) (ofLex w) at h
    cases h with
    | inl h =>
      rename_i z w
      obtain ⟨⟨i, hi⟩, a⟩ := z
      obtain ⟨⟨k, hk⟩, b⟩ := w
      change Sigma.Lex ((· < ·) : Set.Iio j → Set.Iio j → Prop)
        (fun i (a b : A i.1) ↦ a < b) ⟨⟨i, hi⟩, a⟩ ⟨⟨k, hk⟩, b⟩ at h
      change Sigma.Lex ((· < ·) : I → I → Prop)
        (fun i (a b : A i) ↦ a < b) ⟨i, a⟩ ⟨k, b⟩
      cases h with
      | left a b h => exact Sigma.Lex.left _ _ h
      | right a b h => exact Sigma.Lex.right _ _ h
    | inr h =>
      rename_i z w
      obtain ⟨⟨i, hi⟩, a⟩ := z
      obtain ⟨⟨k, hk⟩, b⟩ := w
      change Sigma.Lex ((· < ·) : Set.Ici j → Set.Ici j → Prop)
        (fun i (a b : A i.1) ↦ a < b) ⟨⟨i, hi⟩, a⟩ ⟨⟨k, hk⟩, b⟩ at h
      change Sigma.Lex ((· < ·) : I → I → Prop)
        (fun i (a b : A i) ↦ a < b) ⟨i, a⟩ ⟨k, b⟩
      cases h with
      | left a b h => exact Sigma.Lex.left _ _ h
      | right a b h => exact Sigma.Lex.right _ _ h
    | sep z w => exact Sigma.Lex.left _ _ ((ofLex z).1.2.trans_le (ofLex w).1.2)
  apply OrderIso.ofSurjective (OrderEmbedding.ofStrictMono f hf)
  rintro ⟨i, t⟩
  by_cases h : i < j
  · exact ⟨toLex (Sum.inl (toLex ⟨⟨i, h⟩, t⟩)), rfl⟩
  · exact ⟨toLex (Sum.inr (toLex ⟨⟨i, le_of_not_gt h⟩, t⟩)), rfl⟩

/-- An ordered sum splits at any index into its earlier and final blocks. -/
theorem type_sigma_eq_add_iio_ici {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (A : I → Type u) [∀ i, LinearOrder (A i)] [∀ i, WellFoundedLT (A i)] (j : I) :
    typeLT (Σₗ i, A i) =
      typeLT (Σₗ i : Set.Iio j, A i.1) + typeLT (Σₗ i : Set.Ici j, A i.1) := by
  rw [← (sigmaSplitIso A j).toRelIsoLT.ordinalType_congr, type_lt_sum_lex]

/-- Bounds on a strictly cofinal family of block prefixes bound the full ordered sum. -/
theorem type_sigma_le_of_cofinal_prefixes {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (A : I → Type u) [∀ i, LinearOrder (A i)] [∀ i, WellFoundedLT (A i)]
    (m : Ordinal.{u})
    (hm : ∀ i, ∃ j, i < j ∧ typeLT (Σₗ k : Set.Iio j, A k.1) ≤ m) :
    typeLT (Σₗ i, A i) ≤ m := by
  by_contra h
  obtain ⟨z, hz⟩ := Ordinal.typein_surj ((· < ·) : (Σₗ i, A i) → _ → Prop)
    (lt_of_not_ge h)
  obtain ⟨k, b⟩ := z
  let z : (Σₗ i, A i) := toLex ⟨k, b⟩
  change Ordinal.typein ((· < ·) : (Σₗ i, A i) → _ → Prop) z = m at hz
  obtain ⟨j, hj, hjm⟩ := hm k
  let z' : (Σₗ k : Set.Iio j, A k.1) := toLex ⟨⟨k, hj⟩, b⟩
  have hi (w : Set.Iio z) : (ofLex w.1).1 < j := by
    have hw := w.2
    change Sigma.Lex ((· < ·) : I → I → Prop)
      (fun i (a b : A i) ↦ a < b) (ofLex w.1) ⟨k, b⟩ at hw
    rcases Sigma.lex_iff.mp hw with hw | ⟨hw, _⟩
    · exact hw.trans hj
    · exact hw.le.trans_lt hj
  let f : Set.Iio z → Set.Iio z' := fun w ↦
    ⟨toLex ⟨⟨(ofLex w.1).1, hi w⟩, (ofLex w.1).2⟩, by
      obtain ⟨⟨i, a⟩, hw⟩ := w
      change Sigma.Lex ((· < ·) : I → I → Prop)
        (fun i (a b : A i) ↦ a < b) ⟨i, a⟩ ⟨k, b⟩ at hw
      change Sigma.Lex ((· < ·) : Set.Iio j → Set.Iio j → Prop)
        (fun i (a b : A i.1) ↦ a < b) ⟨⟨i, _⟩, a⟩ ⟨⟨k, hj⟩, b⟩
      cases hw with
      | left a b h => exact Sigma.Lex.left _ _ h
      | right a b h => exact Sigma.Lex.right _ _ h⟩
  have hf : StrictMono f := by
    rintro ⟨⟨i, a⟩, hi⟩ ⟨⟨k, b⟩, hk⟩ h
    change Sigma.Lex ((· < ·) : I → I → Prop)
      (fun i (a b : A i) ↦ a < b) ⟨i, a⟩ ⟨k, b⟩ at h
    cases h with
    | left a b h => exact Sigma.Lex.left _ _ h
    | right a b h => exact Sigma.Lex.right _ _ h
  have ht := (RelEmbedding.ofMonotone f hf).ordinal_type_le
  rw [Ordinal.type_Iio_lt, Ordinal.type_Iio_lt, hz] at ht
  exact (ht.trans_lt (Ordinal.typein_lt_type _ z')).not_ge hjm

/-- Restricting the index set of an ordered sum cannot increase its type. -/
theorem type_sigma_subtype_le {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (A : I → Type u) [∀ i, LinearOrder (A i)] [∀ i, WellFoundedLT (A i)] (S : Set I) :
    typeLT (Σₗ i : S, A i.1) ≤ typeLT (Σₗ i, A i) := by
  let f : (Σₗ i : S, A i.1) → (Σₗ i, A i) := fun z ↦ toLex ⟨(ofLex z).1.1, (ofLex z).2⟩
  have hf : StrictMono f := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    change Sigma.Lex ((· < ·) : S → S → Prop)
      (fun i (a b : A i.1) ↦ a < b) ⟨i, a⟩ ⟨j, b⟩ at h
    cases h with
    | left a b h => exact Sigma.Lex.left _ _ h
    | right a b h => exact Sigma.Lex.right _ _ h
  exact (RelEmbedding.ofMonotone f hf).ordinal_type_le

/-- Enlarging the retained index set cannot decrease an ordered sum. -/
theorem type_sigma_subtype_mono {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (A : I → Type u) [∀ i, LinearOrder (A i)] [∀ i, WellFoundedLT (A i)]
    {S T : Set I} (hST : S ⊆ T) :
    typeLT (Σₗ i : S, A i.1) ≤ typeLT (Σₗ i : T, A i.1) := by
  let f : (Σₗ i : S, A i.1) → (Σₗ i : T, A i.1) :=
    fun z ↦ toLex ⟨⟨(ofLex z).1.1, hST (ofLex z).1.2⟩, (ofLex z).2⟩
  have hf : StrictMono f := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    change Sigma.Lex ((· < ·) : S → S → Prop)
      (fun i (a b : A i.1) ↦ a < b) ⟨i, a⟩ ⟨j, b⟩ at h
    cases h with
    | left a b h => exact Sigma.Lex.left _ _ h
    | right a b h => exact Sigma.Lex.right _ _ h
  exact (RelEmbedding.ofMonotone f hf).ordinal_type_le

/-- At an index order with no last element, an ordered sum is the supremum of its prefixes. -/
theorem type_sigma_eq_iSup_iio {I : Type u} [LinearOrder I] [WellFoundedLT I] [NoMaxOrder I]
    (A : I → Type u) [∀ i, LinearOrder (A i)] [∀ i, WellFoundedLT (A i)] :
    typeLT (Σₗ i, A i) = ⨆ j : I, typeLT (Σₗ i : Set.Iio j, A i.1) := by
  apply le_antisymm
  · apply type_sigma_le_of_cofinal_prefixes
    intro i
    obtain ⟨j, hij⟩ := exists_gt i
    exact ⟨j, hij, Ordinal.le_iSup _ j⟩
  · exact Ordinal.iSup_le (fun j ↦ type_sigma_subtype_le A (Set.Iio j))

/-- Ordinary prefix addition preserves a bound supplied by cofinally many block prefixes. -/
theorem add_type_sigma_le_of_cofinal_prefixes {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (A : I → Type u) [∀ i, LinearOrder (A i)] [∀ i, WellFoundedLT (A i)]
    (c m : Ordinal.{u}) (hcm : c ≤ m)
    (hm : ∀ i, ∃ j, i < j ∧ c + typeLT (Σₗ k : Set.Iio j, A k.1) ≤ m) :
    c + typeLT (Σₗ i, A i) ≤ m := by
  by_cases hI : Nonempty I
  · let : Nonempty I := hI
    let : NoMaxOrder I := ⟨fun i ↦ ⟨(hm i).choose, (hm i).choose_spec.1⟩⟩
    rw [type_sigma_eq_iSup_iio, Ordinal.add_iSup]
    apply Ordinal.iSup_le
    intro i
    obtain ⟨j, hij, hjm⟩ := hm i
    exact (add_le_add_right (type_sigma_subtype_mono A (S := Set.Iio i) (T := Set.Iio j)
      (fun _ hk ↦ lt_trans hk hij)) c).trans hjm
  · have : IsEmpty I := not_nonempty_iff.mp hI
    have : IsEmpty (Σₗ i, A i) := ⟨fun z ↦ isEmptyElim (ofLex z).1⟩
    rwa [Ordinal.type_eq_zero_of_empty, add_zero]

/-- An ordered sum has a prefix followed by its final interval of blocks. -/
theorem exists_add_type_sigma_tail {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (f : I → Ordinal.{u}) (j : I) :
    ∃ c, typeLT (Σₗ i, (f i).ToType) = c + typeLT (Σₗ i : Set.Ici j, (f i.1).ToType) :=
  ⟨typeLT (Σₗ i : Set.Iio j, (f i.1).ToType),
    type_sigma_eq_add_iio_ici (fun i ↦ (f i).ToType) j⟩

/-- A nonzero ordinary multiple of an omega power absorbs any smaller remainder on its left. -/
theorem omega0_opow_dvd_add_of_dvd {p b : Ordinal.{u}} (a : Ordinal.{u})
    (hb : b ≠ 0) (hd : Ordinal.omega0 ^ p ∣ b) : Ordinal.omega0 ^ p ∣ a + b := by
  have hr : a % (Ordinal.omega0 ^ p) < Ordinal.omega0 ^ p :=
    Ordinal.mod_lt _ (Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero)
  have habs := Ordinal.add_of_omega0_opow_le hr (Ordinal.le_of_dvd hb hd)
  have he : a + b = (Ordinal.omega0 ^ p) * (a / (Ordinal.omega0 ^ p)) + b := by
    conv_lhs => rw [← Ordinal.div_add_mod a (Ordinal.omega0 ^ p)]
    rw [add_assoc, habs]
  rw [he]
  exact (Ordinal.dvd_add_iff (dvd_mul_right _ _)).mpr hd

/-- A nonempty tail of multiples of an omega power makes the entire concatenation divisible. -/
theorem omega0_opow_dvd_add_type_sigma_of_tail {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (f : I → Ordinal.{u}) (j : I) (p c : Ordinal.{u}) (hj : f j ≠ 0)
    (hd : ∀ i, j ≤ i → Ordinal.omega0 ^ p ∣ f i) :
    Ordinal.omega0 ^ p ∣ c + typeLT (Σₗ i, (f i).ToType) := by
  obtain ⟨a, ha⟩ := exists_add_type_sigma_tail f j
  rw [ha, ← add_assoc]
  apply omega0_opow_dvd_add_of_dvd
  · have : Nonempty (Σₗ i : Set.Ici j, (f i.1).ToType) :=
      ⟨toLex ⟨⟨j, le_rfl⟩, Ordinal.ToType.mk ⟨0, pos_iff_ne_zero.mpr hj⟩⟩⟩
    exact Ordinal.type_ne_zero_of_nonempty _
  · exact dvd_type_sigma _ _ (fun i ↦ hd i.1 i.2)

private def sigmaCongrIso {I J : Type u} [LinearOrder I] [LinearOrder J]
    {A : I → Type u} {B : J → Type u}
    [∀ i, LinearOrder (A i)] [∀ j, LinearOrder (B j)]
    (e : I ≃o J) (f : ∀ i, A i ≃o B (e i)) : (Σₗ i, A i) ≃o (Σₗ j, B j) where
  toEquiv := ofLex.trans ((Equiv.sigmaCongr e.toEquiv (fun i ↦ (f i).toEquiv)).trans toLex)
  map_rel_iff' := by
    rintro ⟨i, a⟩ ⟨j, b⟩
    change Sigma.Lex ((· < ·) : J → J → Prop)
      (fun j (a b : B j) ↦ a ≤ b) ⟨e i, f i a⟩ ⟨e j, f j b⟩ ↔
      Sigma.Lex ((· < ·) : I → I → Prop)
      (fun i (a b : A i) ↦ a ≤ b) ⟨i, a⟩ ⟨j, b⟩
    by_cases h : i = j
    · subst j
      simp [Sigma.lex_iff]
    · simp [Sigma.lex_iff, h]

/-- Order-isomorphic indices and blocks have the same ordered-sum type. -/
theorem type_sigma_congr {I J : Type u}
    [LinearOrder I] [WellFoundedLT I] [LinearOrder J] [WellFoundedLT J]
    (A : I → Type u) (B : J → Type u)
    [∀ i, LinearOrder (A i)] [∀ i, WellFoundedLT (A i)]
    [∀ j, LinearOrder (B j)] [∀ j, WellFoundedLT (B j)]
    (e : I ≃o J) (h : ∀ i, typeLT (A i) = typeLT (B (e i))) :
    typeLT (Σₗ i, A i) = typeLT (Σₗ j, B j) := by
  let f (i : I) := OrderIso.ofRelIsoLT (Classical.choice (Ordinal.type_eq.mp (h i)))
  exact (sigmaCongrIso e f).toRelIsoLT.ordinalType_congr

private def sigmaConstIso (I A : Type u) [LinearOrder I] [LinearOrder A] :
    (Σₗ _i : I, A) ≃o (I ×ₗ A) where
  toEquiv := ofLex.trans ((Equiv.sigmaEquivProd I A).trans toLex)
  map_rel_iff' := by
    rintro ⟨i, a⟩ ⟨j, b⟩
    change Prod.Lex ((· < ·) : I → I → Prop) ((· ≤ ·) : A → A → Prop)
      (i, a) (j, b) ↔ Sigma.Lex ((· < ·) : I → I → Prop)
      (fun _ (a b : A) ↦ a ≤ b) ⟨i, a⟩ ⟨j, b⟩
    by_cases h : i = j
    · subst j
      simp [Prod.lex_def, Sigma.lex_iff]
    · simp [Prod.lex_def, Sigma.lex_iff, h]

/-- A constant ordered family has type given by ordinary multiplication. -/
theorem type_sigma_const (I A : Type u)
    [LinearOrder I] [WellFoundedLT I] [LinearOrder A] [WellFoundedLT A] :
    typeLT (Σₗ _i : I, A) = (typeLT A) * typeLT I := by
  rw [(sigmaConstIso I A).toRelIsoLT.ordinalType_congr, type_lt_prod_lex]

/-- Each individual block embeds into the whole ordered sum. -/
theorem type_sigma_block_le {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (A : I → Type u) [∀ i, LinearOrder (A i)] [∀ i, WellFoundedLT (A i)] (j : I) :
    typeLT (A j) ≤ typeLT (Σₗ i, A i) := by
  let f : A j → (Σₗ i, A i) := fun a ↦ toLex ⟨j, a⟩
  have hf : StrictMono f := fun _ _ h ↦ Sigma.Lex.right _ _ h
  exact (RelEmbedding.ofMonotone f hf).ordinal_type_le

end Ordinal
