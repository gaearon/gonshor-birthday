/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.NormalFormReplacement

import GonshorBirthday.NatOrdinal.ProductFibre
import GonshorBirthday.NatOrdinal.OrderedSum
import GonshorBirthday.Surreal.Birthday.ProductCoefficientCost
import GonshorBirthday.Surreal.Birthday.NormalFormLength

/-!
# Whole replacement-product birthday bounds

Order every input exponent pair by its output exponent, then by any finite
ordering inside that exponent's native convolution fibre. This well order is
compatible with both input support indices. The checked finite coefficient
bounds and ordinal product-grid theorem therefore bound the whole replacement
product by the original input birthdays. Arbitrary supports, signs, and zero
inputs are included. Transferring this bound to the original product additionally
requires the whole-series coefficient comparison.
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

/-- Positive replacement products fit the natural product of the original whole birthdays. -/
theorem birthday_mul_normalFormBirthdayReplacement_le {τ : ℝ}
    (hτpos : 0 < τ) (hτ : Transcendental ℚ τ) (x y : Surreal.{u}) :
    (normalFormBirthdayReplacement τ x * normalFormBirthdayReplacement τ y).birthday ≤
      x.birthday * y.birthday := by
  classical
  let Z := normalFormBirthdayReplacement τ x * normalFormBirthdayReplacement τ y
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
  have hmem (s : S) (i : Fin (n s)) :
      (E s i).1.1 ∈ x.support ∧ (E s i).1.2 ∈ y.support ∧
        (E s i).1.1 + (E s i).1.2 = (ez s).1 := by
    simpa only [support_toHahnSeries] using
      (SurrealHahnSeries.mem_supportAntidiagonal _ _ _ _).mp (E s i).2
  let f (k : K) : I × J :=
    (ex.symm ⟨(E (ofLex k).1 (ofLex k).2).1.1, (hmem _ _).1⟩,
      ey.symm ⟨(E (ofLex k).1 (ofLex k).2).1.2, (hmem _ _).2.1⟩)
  have hfa (k : K) : (ex (f k).1).1 = (E (ofLex k).1 (ofLex k).2).1.1 := by
    simp [f]
  have hfb (k : K) : (ey (f k).2).1 = (E (ofLex k).1 (ofLex k).2).1.2 := by
    simp [f]
  have hsum (k : K) : (ex (f k).1).1 + (ey (f k).2).1 = (ez (ofLex k).1).1 := by
    rw [hfa, hfb]
    exact (hmem _ _).2.2
  have hfinj : Function.Injective f := by
    rintro ⟨s, i⟩ ⟨t, j⟩ h
    have hst : s = t := by
      apply ez.injective
      apply Subtype.ext
      exact (hsum (toLex ⟨s, i⟩)).symm.trans
        ((congrArg (fun p : I × J ↦ (ex p.1).1 + (ey p.2).1) h).trans
          (hsum (toLex ⟨t, j⟩)))
    subst t
    have hij : i = j := by
      apply (E s).injective
      apply Subtype.ext
      apply Prod.ext
      · exact (hfa (toLex ⟨s, i⟩)).symm.trans
          ((congrArg (fun p : I × J ↦ (ex p.1).1) h).trans (hfa (toLex ⟨s, j⟩)))
      · exact (hfb (toLex ⟨s, i⟩)).symm.trans
          ((congrArg (fun p : I × J ↦ (ey p.2).1) h).trans (hfb (toLex ⟨s, j⟩)))
    exact congrArg (fun i : Fin (n s) ↦ (toLex ⟨s, i⟩ : K)) hij
  have hfsurj : Function.Surjective f := by
    rintro ⟨i, j⟩
    have hs : (ex i).1 + (ey j).1 ∈ Z.support := by
      apply (mem_support_mul_normalFormBirthdayReplacement hτpos x y _).mpr
      exact ⟨(ex i).1, (ex i).2, (ey j).1, (ey j).2, rfl⟩
    let s : S := ez.symm ⟨(ex i).1 + (ey j).1, hs⟩
    have hse : (ez s).1 = (ex i).1 + (ey j).1 := by simp [s]
    let q : A s := ⟨((ex i).1, (ey j).1),
      (SurrealHahnSeries.mem_supportAntidiagonal _ _ _ _).mpr
        ⟨by simpa only [support_toHahnSeries] using (ex i).2,
          by simpa only [support_toHahnSeries] using (ey j).2, hse.symm⟩⟩
    refine ⟨toLex ⟨s, (E s).symm q⟩, ?_⟩
    apply Prod.ext
    · apply ex.injective
      apply Subtype.ext
      exact (hfa (toLex ⟨s, (E s).symm q⟩)).trans
        (congrArg (fun q : A s ↦ q.1.1) ((E s).apply_symm_apply q))
    · apply ey.injective
      apply Subtype.ext
      exact (hfb (toLex ⟨s, (E s).symm q⟩)).trans
        (congrArg (fun q : A s ↦ q.1.2) ((E s).apply_symm_apply q))
  have hreflect (k l : K) (h : f k ≤ f l) : k ≤ l := by
    have hx := normalFormIndexEquiv_strictAnti x
    have hy := normalFormIndexEquiv_strictAnti y
    have hz := normalFormIndexEquiv_strictAnti Z
    rcases h.1.lt_or_eq with h₁ | h₁
    · have hh : (ez (ofLex l).1).1 < (ez (ofLex k).1).1 := by
        rw [← hsum, ← hsum]
        exact add_lt_add_of_lt_of_le (hx h₁) (hy.antitone h.2)
      exact Sigma.Lex.left _ _ (hz.lt_iff_gt.mp hh)
    · rcases h.2.lt_or_eq with h₂ | h₂
      · have hh : (ez (ofLex l).1).1 < (ez (ofLex k).1).1 := by
          rw [← hsum, ← hsum]
          exact add_lt_add_of_le_of_lt (hx.antitone h.1) (hy h₂)
        exact Sigma.Lex.left _ _ (hz.lt_iff_gt.mp hh)
      · exact (hfinj (Prod.ext h₁ h₂)).le
  let e : K ≃ I × J := Equiv.ofBijective f ⟨hfinj, hfsurj⟩
  have he : Monotone e.symm := by
    intro p q hpq
    apply hreflect
    change e (e.symm p) ≤ e (e.symm q)
    simpa only [Equiv.apply_symm_apply] using hpq
  let a (i : I) := headCoefficientCost (x.normalFormTrunc (ex i).1) (ex i).1 (x.coeff (ex i).1)
  let b (j : J) := headCoefficientCost (y.normalFormTrunc (ey j).1) (ey j).1 (y.coeff (ey j).1)
  let c (s : S) := headCoefficientCost (Z.normalFormTrunc (ez s).1) (ez s).1 (Z.coeff (ez s).1)
  have hc (s : S) : c s ≤ NatOrdinal.of (typeLT (Σₗ i : Fin (n s),
      (a (e (toLex ⟨s, i⟩)).1 * b (e (toLex ⟨s, i⟩)).2).val.ToType)) := by
    have h := headCoefficientCost_mul_replacement_fibre_le hτpos hτ x y (ez s).1 (E s)
    change c s ≤ NatOrdinal.of (typeLT (Σₗ i : Fin (n s),
      (a (f (toLex ⟨s, i⟩)).1 * b (f (toLex ⟨s, i⟩)).2).val.ToType))
    have hab :
        (fun i : Fin (n s) ↦ a (f (toLex ⟨s, i⟩)).1 * b (f (toLex ⟨s, i⟩)).2) =
        (fun i : Fin (n s) ↦
          headCoefficientCost (x.normalFormTrunc (E s i).1.1) (E s i).1.1 (x.coeff (E s i).1.1) *
          headCoefficientCost (y.normalFormTrunc (E s i).1.2)
            (E s i).1.2 (y.coeff (E s i).1.2)) := by
      funext i
      dsimp only [a, b]
      rw [hfa, hfb]
      rfl
    exact h.trans_eq (congrArg (fun g : Fin (n s) → NatOrdinal.{u} ↦
      NatOrdinal.of (typeLT (Σₗ i : Fin (n s), (g i).val.ToType))) hab).symm
  have h := NatOrdinal.of_type_sigma_mul_le_of_fibres a b c n e he hc
  have hcost (w : Surreal.{u}) :
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
  exact (hcost Z) ▸ (hcost x) ▸ (hcost y) ▸ h

end Surreal
