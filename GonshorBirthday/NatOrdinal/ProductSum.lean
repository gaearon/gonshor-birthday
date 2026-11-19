/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.NatOrdinal.ProductOrder
public import GonshorBirthday.NatOrdinal.ProductAttainment
import GonshorBirthday.NatOrdinal.OrderedSum

/-!
# Ordered sums of natural-product cell budgets

Let `a i` and `b j` be ordinal block lengths on two arbitrary well-ordered index sets. Order
all cells in any well order compatible with both indices. The ordinary ordered sum of the
natural products `a i * b j` is bounded by the natural product of the two input ordered sums.

For each cell, Carruth attainment gives a monotone bijection from its rectangle to its full
natural-product budget. The inverse maps global cell positions into the two input words and
reflects coordinatewise comparison. Carruth's upper bound then gives the global inequality.
No continuity of natural multiplication and no restriction on index cofinalities is used.
-/

universe u

public noncomputable section

namespace NatOrdinal

open Ordinal

private theorem of_type_le_mul_of_product_reflection {A B G : Type u}
    [LinearOrder A] [WellFoundedLT A] [LinearOrder B] [WellFoundedLT B]
    [LinearOrder G] [WellFoundedLT G] (p : G → A) (q : G → B)
    (hm : ∀ x y, p x ≤ p y → q x ≤ q y → x ≤ y) :
    of (typeLT G) ≤ of (typeLT A) * of (typeLT B) := by
  apply of_type_le_mul_of_coordinates (of (typeLT A)) (of (typeLT B))
    (fun x ↦ of (typein (α := A) (· < ·) (p x)))
    (fun x ↦ of (typein (α := B) (· < ·) (q x)))
  · exact fun x ↦ of.strictMono (typein_lt_type _ _)
  · exact fun x ↦ of.strictMono (typein_lt_type _ _)
  · intro x y hp hq
    exact hm x y
      (le_of_not_gt ((typein_le_typein (α := A) (· < ·)).mp (of.le_iff_le.mp hp)))
      (le_of_not_gt ((typein_le_typein (α := B) (· < ·)).mp (of.le_iff_le.mp hq)))

private theorem sigma_index_le {I : Type u} {A : I → Type u}
    [LinearOrder I] [∀ i, LE (A i)] {x y : Σₗ i, A i} (h : x ≤ y) :
    (ofLex x).1 ≤ (ofLex y).1 := by
  rcases Sigma.Lex.le_def.mp h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

private theorem sigma_same_le_iff {I : Type u} {A : I → Type u}
    [LinearOrder I] [∀ i, LE (A i)] (i : I) (a b : A i) :
    (toLex ⟨i, a⟩ : Σₗ i, A i) ≤ toLex ⟨i, b⟩ ↔ a ≤ b := by
  change Sigma.Lex ((· < ·) : I → I → Prop) (fun i a b ↦ a ≤ b) ⟨i, a⟩ ⟨i, b⟩ ↔ _
  simp [Sigma.lex_iff]

/-- A compatible ordered sum of cell products is bounded by the product of the input sums. -/
theorem of_type_sigma_mul_le {I J K : Type u}
    [LinearOrder I] [WellFoundedLT I] [LinearOrder J] [WellFoundedLT J]
    [LinearOrder K] [WellFoundedLT K]
    (a : I → NatOrdinal.{u}) (b : J → NatOrdinal.{u}) (e : K ≃ I × J)
    (he : Monotone e.symm) :
    of (typeLT (Σₗ k : K, (a (e k).1 * b (e k).2).val.ToType)) ≤
      of (typeLT (Σₗ i : I, (a i).val.ToType)) *
        of (typeLT (Σₗ j : J, (b j).val.ToType)) := by
  classical
  choose E hE using fun k : K ↦ exists_monotone_equiv_mul (a (e k).1) (b (e k).2)
  let p : (Σₗ k : K, (a (e k).1 * b (e k).2).val.ToType) →
      (Σₗ i : I, (a i).val.ToType) := fun z ↦
    toLex ⟨(e (ofLex z).1).1, ((E (ofLex z).1).symm (ofLex z).2).1⟩
  let q : (Σₗ k : K, (a (e k).1 * b (e k).2).val.ToType) →
      (Σₗ j : J, (b j).val.ToType) := fun z ↦
    toLex ⟨(e (ofLex z).1).2, ((E (ofLex z).1).symm (ofLex z).2).2⟩
  apply of_type_le_mul_of_product_reflection p q
  rintro ⟨k, x⟩ ⟨l, y⟩ hp hq
  have hi : (e k).1 ≤ (e l).1 := sigma_index_le hp
  have hj : (e k).2 ≤ (e l).2 := sigma_index_le hq
  have hkl : k ≤ l := by
    simpa only [Equiv.symm_apply_apply] using he ⟨hi, hj⟩
  rcases hkl.lt_or_eq with hkl | rfl
  · exact Sigma.Lex.left _ _ hkl
  · have hx : ((E k).symm x).1 ≤ ((E k).symm y).1 :=
      (sigma_same_le_iff _ _ _).mp hp
    have hy : ((E k).symm x).2 ≤ ((E k).symm y).2 :=
      (sigma_same_le_iff _ _ _).mp hq
    have hxy : x ≤ y := by
      simpa only [Equiv.apply_symm_apply] using hE k ⟨hx, hy⟩
    exact Sigma.Lex.right _ _ hxy

/-- Scaling every block of an ordered sum by the same natural product fits the scaled sum. -/
theorem of_type_sigma_mul_const_le {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (f : I → NatOrdinal.{u}) (c : NatOrdinal.{u}) :
    of (typeLT (Σₗ i, (f i * c).val.ToType)) ≤
      of (typeLT (Σₗ i, (f i).val.ToType)) * c := by
  let e : I ≃ I × PUnit.{u+1} := (Equiv.prodUnique I PUnit.{u+1}).symm
  have hm : Monotone e.symm := fun _ _ h ↦ h.1
  have h := of_type_sigma_mul_le f (fun _ : PUnit.{u+1} ↦ c) e hm
  change of (typeLT (Σₗ i : I, (f i * c).val.ToType)) ≤ _ at h
  simpa only [Ordinal.type_sigma_const, Ordinal.type_toType,
    Ordinal.type_eq_one_of_unique, mul_one, of_val] using h

/-- Natural multiplication is superadditive for ordinary ordinal concatenation. -/
theorem of_oadd_mul_le (a b c : NatOrdinal.{u}) :
    of ((a * c).val + (b * c).val) ≤ of (a.val + b.val) * c := by
  obtain ⟨e, he⟩ := exists_monotone_equiv_mul a c
  obtain ⟨f, hf⟩ := exists_monotone_equiv_mul b c
  let p : (a * c).val.ToType ⊕ₗ (b * c).val.ToType → a.val.ToType ⊕ₗ b.val.ToType :=
    fun z ↦ Sum.elim (fun x ↦ toLex (Sum.inl (e.symm x).1))
      (fun x ↦ toLex (Sum.inr (f.symm x).1)) (ofLex z)
  let q : (a * c).val.ToType ⊕ₗ (b * c).val.ToType → c.val.ToType :=
    fun z ↦ Sum.elim (fun x ↦ (e.symm x).2) (fun x ↦ (f.symm x).2) (ofLex z)
  have h : of (typeLT ((a * c).val.ToType ⊕ₗ (b * c).val.ToType)) ≤
      of (typeLT (a.val.ToType ⊕ₗ b.val.ToType)) * of (typeLT c.val.ToType) := by
    apply of_type_le_mul_of_product_reflection p q
    intro x y hp hq
    obtain x | x := x
    · obtain y | y := y
      · change (toLex (Sum.inl (e.symm x).1) : a.val.ToType ⊕ₗ b.val.ToType) ≤
          toLex (Sum.inl (e.symm y).1) at hp
        have hp' := Sum.Lex.inl_le_inl_iff.mp hp
        change (e.symm x).2 ≤ (e.symm y).2 at hq
        apply Sum.Lex.inl_le_inl_iff.mpr
        simpa only [Equiv.apply_symm_apply] using he ⟨hp', hq⟩
      · exact Sum.Lex.inl_le_inr _ _
    · obtain y | y := y
      · exact False.elim (Sum.Lex.not_inr_le_inl hp)
      · change (toLex (Sum.inr (f.symm x).1) : a.val.ToType ⊕ₗ b.val.ToType) ≤
          toLex (Sum.inr (f.symm y).1) at hp
        have hp' := Sum.Lex.inr_le_inr_iff.mp hp
        change (f.symm x).2 ≤ (f.symm y).2 at hq
        apply Sum.Lex.inr_le_inr_iff.mpr
        simpa only [Equiv.apply_symm_apply] using hf ⟨hp', hq⟩
  simpa only [Ordinal.type_lt_sum_lex, Ordinal.type_toType, of_val] using h

/-- Three ordinary consecutive product portions fit the product of their concatenated input. -/
theorem of_oadd_oadd_mul_le (a b c d : NatOrdinal.{u}) :
    of ((a * d).val + (b * d).val + (c * d).val) ≤ of (a.val + b.val + c.val) * d := by
  have h := of_oadd_mul_le (of (a.val + b.val)) c d
  rw [val_of] at h
  apply le_trans ?_ h
  exact of.monotone (add_le_add (val.monotone (of_oadd_mul_le a b d)) le_rfl)

end NatOrdinal
