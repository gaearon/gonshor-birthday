/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.NormalFormReplacement
public import GonshorBirthday.Surreal.Birthday.HeadCoefficientCost
public import GonshorBirthday.Surreal.HahnSeries.NormalFormMul

import GonshorBirthday.NatOrdinal.FiniteBlocks
import GonshorBirthday.NatOrdinal.ProductFibre
import GonshorBirthday.NatOrdinal.OrderedSum
import GonshorBirthday.Surreal.Birthday.ProductCoefficientCost
import GonshorBirthday.Surreal.Birthday.NormalFormLength

/-!
# Assembling birthday bounds over exponent pairs

Order every input exponent pair by its output exponent, then by any finite
ordering inside that exponent's finite convolution fibre. The coordinate grid is the disjoint
union of these fibres. Summing their bounds in this order gives the natural product bound
for any comparison series containing all pair sums.
-/

universe u
public noncomputable section
open scoped Ordinal

namespace Surreal

private def normalFormIndexEquiv (x : Surreal.{u}) :
    x.toHahnSeries.length.ToType ≃ x.support :=
  Ordinal.ToType.mk.symm.toEquiv |>.trans x.toHahnSeries.exp.toEquiv |>.trans
    (Equiv.subtypeEquivRight (fun s ↦ by rw [support_toHahnSeries]))

private theorem normalFormIndexEquiv_strictAnti (x : Surreal.{u}) :
    StrictAnti (fun i ↦ (normalFormIndexEquiv x i).1) := by
  intro i j hij
  exact x.toHahnSeries.exp_strictAnti (Ordinal.ToType.mk.symm.strictMono hij)

/-- Fibre bounds on a series containing every exponent sum give the whole product budget. -/
theorem birthday_le_of_product_fibre_costs (x y Z : Surreal.{u})
    (hsum : ∀ a ∈ x.support, ∀ b ∈ y.support, a + b ∈ Z.support)
    (hcost : ∀ s, ∀ {n : ℕ},
      (e : Fin n ≃ SurrealHahnSeries.supportAntidiagonal x.toHahnSeries y.toHahnSeries s) →
      headCoefficientCost (Z.normalFormTrunc s) s (Z.coeff s) ≤ NatOrdinal.of (typeLT
        (Σₗ i : Fin n, (headCoefficientCost (x.normalFormTrunc (e i).1.1) (e i).1.1
          (x.coeff (e i).1.1) * headCoefficientCost (y.normalFormTrunc (e i).1.2) (e i).1.2
            (y.coeff (e i).1.2)).val.ToType))) :
    Z.birthday ≤ x.birthday * y.birthday := by
  classical
  let I := x.toHahnSeries.length.ToType
  let J := y.toHahnSeries.length.ToType
  let S := Z.toHahnSeries.length.ToType
  let ex := normalFormIndexEquiv x
  let ey := normalFormIndexEquiv y
  let ez := normalFormIndexEquiv Z
  let A (s : S) := SurrealHahnSeries.supportAntidiagonal
    x.toHahnSeries y.toHahnSeries (ez s).1
  let n (s : S) := Fintype.card (A s)
  let E (s : S) : Fin (n s) ≃ (A s) := (Fintype.equivFin (A s)).symm
  let K := Σₗ s : S, Fin (n s)
  let key (p : x.support × y.support) : S := ez.symm ⟨p.1.1 + p.2.1, hsum _ p.1.2 _ p.2.2⟩
  have hkey (p : x.support × y.support) (s : S) : key p = s ↔ p.1.1 + p.2.1 = (ez s).1 := by
    exact ez.symm_apply_eq.trans Subtype.ext_iff
  have hmem (s : S) (p : Surreal.{u} × Surreal.{u}) :
      p ∈ A s ↔ p.1 ∈ x.support ∧ p.2 ∈ y.support ∧ p.1 + p.2 = (ez s).1 := by
    simp only [A, SurrealHahnSeries.mem_supportAntidiagonal, support_toHahnSeries]
  let fibre (s : S) : A s ≃ {p : x.support × y.support // key p = s} :=
    { toFun := fun p ↦
        let hp := (hmem s p.1).mp p.2
        ⟨(⟨p.1.1, hp.1⟩, ⟨p.1.2, hp.2.1⟩), (hkey _ s).mpr hp.2.2⟩
      invFun := fun p ↦ ⟨(p.1.1.1, p.1.2.1), (hmem _ _).mpr
        ⟨p.1.1.2, p.1.2.2, (hkey _ s).mp p.2⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let e : K ≃ I × J := ofLex.trans ((Equiv.sigmaCongrRight (fun s ↦ (E s).trans (fibre s))).trans
    ((Equiv.sigmaFiberEquiv key).trans (ex.symm.prodCongr ey.symm)))
  have hex (k : K) : (ex (e k).1).1 = (E (ofLex k).1 (ofLex k).2).1.1 :=
    congrArg Subtype.val (ex.apply_symm_apply _)
  have hey (k : K) : (ey (e k).2).1 = (E (ofLex k).1 (ofLex k).2).1.2 :=
    congrArg Subtype.val (ey.apply_symm_apply _)
  have he : Monotone e.symm := by
    intro p q hpq
    have hlt (h : (ex q.1).1 + (ey q.2).1 < (ex p.1).1 + (ey p.2).1) :
        e.symm p ≤ e.symm q := by
      apply Sigma.Lex.left
      apply (normalFormIndexEquiv_strictAnti Z).lt_iff_gt.mp
      change (ez (key (ex q.1, ey q.2))).1 < (ez (key (ex p.1, ey p.2))).1
      simpa only [key, Equiv.apply_symm_apply] using h
    rcases hpq.1.lt_or_eq with h | h
    · exact hlt (add_lt_add_of_lt_of_le (normalFormIndexEquiv_strictAnti x h)
        ((normalFormIndexEquiv_strictAnti y).antitone hpq.2))
    rcases hpq.2.lt_or_eq with h' | h'
    · exact hlt (add_lt_add_of_le_of_lt ((normalFormIndexEquiv_strictAnti x).antitone hpq.1)
        (normalFormIndexEquiv_strictAnti y h'))
    exact (congrArg e.symm (Prod.ext h h')).le
  let a (i : I) := headCoefficientCost (x.normalFormTrunc (ex i).1) (ex i).1 (x.coeff (ex i).1)
  let b (j : J) := headCoefficientCost (y.normalFormTrunc (ey j).1) (ey j).1 (y.coeff (ey j).1)
  let c (s : S) := headCoefficientCost (Z.normalFormTrunc (ez s).1) (ez s).1 (Z.coeff (ez s).1)
  have hc (s : S) : c s ≤ NatOrdinal.of (typeLT (Σₗ i : Fin (n s),
      (a (e (toLex ⟨s, i⟩)).1 * b (e (toLex ⟨s, i⟩)).2).val.ToType)) := by
    apply (hcost (ez s).1 (E s)).trans_eq
    apply congrArg (fun g : Fin (n s) → NatOrdinal.{u} ↦
      NatOrdinal.of (typeLT (Σₗ i : Fin (n s), (g i).val.ToType)))
    funext i
    dsimp only [a, b]
    rw [hex, hey]
    rfl
  have h := NatOrdinal.of_type_sigma_mul_le_of_fibres a b c n e he hc
  have hlen (w : Surreal.{u}) :
      NatOrdinal.of (typeLT (Σₗ i : w.toHahnSeries.length.ToType,
        (headCoefficientCost (w.normalFormTrunc (normalFormIndexEquiv w i).1)
          (normalFormIndexEquiv w i).1 (w.coeff (normalFormIndexEquiv w i).1)).val.ToType)) =
        w.birthday := by
    rw [birthday_eq_ordered_term_costs w]
    apply congrArg NatOrdinal.of
    apply Ordinal.type_sigma_congr _ _ (OrderIso.refl _)
    intro i
    rw [Ordinal.type_toType, Ordinal.type_toType]
    rfl
  exact (hlen Z) ▸ (hlen x) ▸ (hlen y) ▸ h

/-- The birthday of the product of the replaced series is at most the natural product of the
birthdays of the original surreals. -/
theorem birthday_mul_normalFormBirthdayReplacement_le {τ : ℝ}
    (hτpos : 0 < τ) (hτ : Transcendental ℚ τ) (x y : Surreal.{u}) :
    (normalFormBirthdayReplacement τ x * normalFormBirthdayReplacement τ y).birthday ≤
      x.birthday * y.birthday := by
  apply birthday_le_of_product_fibre_costs x y
  · intro a ha b hb
    exact (mem_support_mul_normalFormBirthdayReplacement hτpos x y _).mpr ⟨a, ha, b, hb, rfl⟩
  · exact fun s _ e ↦ headCoefficientCost_mul_replacement_fibre_le hτpos hτ x y s e

end Surreal
