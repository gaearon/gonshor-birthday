/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.NatOrdinal.FiniteBlocks
public import Mathlib.SetTheory.Ordinal.Basic

import Mathlib.Order.Hom.Lex
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Product orders attaining the natural product

The coordinatewise product of arbitrary ordinal well orders admits a well-ordered linear
extension of type equal to their natural product. A monotone bijection to the canonical well
order states the result while preserving both coordinate orders.

This is Carruth, *Arithmetic of ordinals with applications to the theory of ordered Abelian
groups* (1942), Theorem 2.II, pp. 265–268. For two pure powers the proof here inducts on the
natural sum of the exponents, removes one copy of the larger exponent's leading omega power,
and lifts the smaller product order through a common lexicographic inner factor. For arbitrary
factors, finite descending decompositions into pure powers give a grid of cells. Ordering cells
by decreasing exponent sum, with a lexicographic tie order, preserves both coordinate orders
and realizes every term of the natural product.
-/

universe u v w

public noncomputable section

private def sigmaLexCongrLeft {ι : Type v} {κ : Type w}
    [LinearOrder ι] [LinearOrder κ] (e : ι ≃o κ) (A : κ → Type u)
    [∀ i, LinearOrder (A i)] : (Σₗ i, A (e i)) ≃o (Σₗ j, A j) where
  toEquiv := ofLex.trans ((Equiv.sigmaCongrLeft e.toEquiv).trans toLex)
  map_rel_iff' := by
    rintro ⟨i, a⟩ ⟨j, b⟩
    change Sigma.Lex ((· < ·) : κ → κ → Prop) (fun j a b ↦ a ≤ b)
      ⟨e i, a⟩ ⟨e j, b⟩ ↔
      Sigma.Lex ((· < ·) : ι → ι → Prop) (fun i (a b : A (e i)) ↦ a ≤ b) ⟨i, a⟩ ⟨j, b⟩
    by_cases h : i = j
    · subst j
      simp [Sigma.lex_iff]
    · simp [Sigma.lex_iff, h]

namespace NatOrdinal

open Ordinal

private def inflateEquiv {A B C H : Type u} (e : A × B ≃ C) :
    (A ×ₗ H) × B ≃ C ×ₗ H where
  toFun x := toLex (e ((ofLex x.1).1, x.2), (ofLex x.1).2)
  invFun y :=
    (toLex ((e.symm (ofLex y).1).1, (ofLex y).2), (e.symm (ofLex y).1).2)
  left_inv x := by simp
  right_inv y := by simp

private theorem monotone_inflateEquiv {A B C H : Type u}
    [LinearOrder A] [LinearOrder B] [LinearOrder C] [LinearOrder H]
    (e : A × B ≃ C) (he : Monotone e) : Monotone (inflateEquiv (H := H) e) := by
  intro x y hxy
  change toLex (e ((ofLex x.1).1, x.2), (ofLex x.1).2) ≤
    toLex (e ((ofLex y.1).1, y.2), (ofLex y.1).2)
  apply Prod.Lex.toLex_le_toLex'.mpr
  have hx := Prod.Lex.le_iff'.mp hxy.1
  refine ⟨he ⟨hx.1, hxy.2⟩, ?_⟩
  intro hh
  exact hx.2 (congrArg (fun z : A × B ↦ z.1) (e.injective hh))

private theorem nonempty_orderIso_of_type_eq {A B : Type u}
    [LinearOrder A] [WellFoundedLT A] [LinearOrder B] [WellFoundedLT B]
    (h : typeLT A = typeLT B) : Nonempty (A ≃o B) := by
  obtain ⟨e⟩ := Ordinal.type_eq.mp h
  exact ⟨OrderIso.ofRelIsoLT e⟩

private def PureAttain (a b : NatOrdinal.{u}) : Prop :=
  ∃ e : (ω^ a).val.ToType × (ω^ b).val.ToType ≃ (ω^ (a + b)).val.ToType,
    Monotone e

private theorem PureAttain.symm {a b : NatOrdinal.{u}} (h : PureAttain a b) :
    PureAttain b a := by
  obtain ⟨e, he⟩ := h
  obtain ⟨ez⟩ : Nonempty ((ω^ (a + b)).val.ToType ≃o (ω^ (b + a)).val.ToType) := by
    apply nonempty_orderIso_of_type_eq
    exact (type_toType _).trans ((congrArg (fun x : NatOrdinal ↦ (ω^ x).val)
      (add_comm a b)).trans (type_toType _).symm)
  let es : (ω^ b).val.ToType × (ω^ a).val.ToType ≃o
      (ω^ a).val.ToType × (ω^ b).val.ToType := OrderIso.prodComm
  refine ⟨es.toEquiv.trans (e.trans ez.toEquiv), ?_⟩
  exact ez.monotone.comp (he.comp es.monotone)

private theorem pureAttain_zero_left (b : NatOrdinal.{u}) : PureAttain 0 b := by
  obtain ⟨e₀⟩ : Nonempty ((ω^ (0 : NatOrdinal.{u})).val.ToType ≃o (1 : Ordinal.{u}).ToType) := by
    apply nonempty_orderIso_of_type_eq
    calc
      typeLT (ω^ (0 : NatOrdinal.{u})).val.ToType = (ω^ (0 : NatOrdinal.{u})).val := type_toType _
      _ = (1 : Ordinal.{u}) := by simp
      _ = typeLT (1 : Ordinal.{u}).ToType := (type_toType _).symm
  obtain ⟨ez⟩ : Nonempty ((ω^ b).val.ToType ≃o (ω^ (0 + b)).val.ToType) := by
    apply nonempty_orderIso_of_type_eq
    calc
      typeLT (ω^ b).val.ToType = (ω^ b).val := type_toType _
      _ = (ω^ (0 + b)).val := by rw [zero_add]
      _ = typeLT (ω^ (0 + b)).val.ToType := (type_toType _).symm
  let ep := OrderIso.prodCongr e₀ (OrderIso.refl (ω^ b).val.ToType)
  let eu := OrderIso.uniqueProd (ω^ b).val.ToType (1 : Ordinal.{u}).ToType
  exact ⟨ep.toEquiv.trans (eu.toEquiv.trans ez.toEquiv),
    ez.monotone.comp (eu.monotone.comp ep.monotone)⟩

private theorem pureAttain_of_split {a h r b : NatOrdinal.{u}}
    (ha : a.val = h.val + r.val)
    (hab : (a + b).val = h.val + (r + b).val)
    (ih : PureAttain r b) : PureAttain a b := by
  obtain ⟨e, he⟩ := ih
  obtain ⟨ea⟩ : Nonempty ((ω^ a).val.ToType ≃o
      ((ω^ r).val.ToType ×ₗ (ω^ h).val.ToType)) := by
    apply nonempty_orderIso_of_type_eq
    calc
      typeLT (ω^ a).val.ToType = (ω^ a).val := type_toType _
      _ = (ω^ h).val * (ω^ r).val := by simp only [val_wpow, ha, Ordinal.opow_add]
      _ = typeLT ((ω^ r).val.ToType ×ₗ (ω^ h).val.ToType) := by
        exact (Ordinal.type_lt_prod_lex.trans
          (congrArg₂ (· * ·) (type_toType _) (type_toType _))).symm
  obtain ⟨ez⟩ : Nonempty (((ω^ (r + b)).val.ToType ×ₗ (ω^ h).val.ToType) ≃o
      (ω^ (a + b)).val.ToType) := by
    apply nonempty_orderIso_of_type_eq
    calc
      typeLT ((ω^ (r + b)).val.ToType ×ₗ (ω^ h).val.ToType) =
          (ω^ h).val * (ω^ (r + b)).val :=
        Ordinal.type_lt_prod_lex.trans (congrArg₂ (· * ·) (type_toType _) (type_toType _))
      _ = (ω^ (a + b)).val := by simp only [val_wpow, hab, Ordinal.opow_add]
      _ = typeLT (ω^ (a + b)).val.ToType := (type_toType _).symm
  let ep := OrderIso.prodCongr ea (OrderIso.refl (ω^ b).val.ToType)
  refine ⟨ep.toEquiv.trans ((inflateEquiv e).trans ez.toEquiv), ?_⟩
  exact ez.monotone.comp ((monotone_inflateEquiv e he).comp ep.monotone)

private theorem pureAttain (a b : NatOrdinal.{u}) : PureAttain a b := by
  have aux : ∀ n : NatOrdinal.{u}, ∀ a b : NatOrdinal.{u}, a + b = n → PureAttain a b := by
    intro n
    induction n using NatOrdinal.lt_wf.induction with
    | h n IH =>
      intro a b hn
      have step (a b : NatOrdinal.{u}) (hn : a + b = n) (hba : b ≤ a) :
          PureAttain a b := by
        by_cases ha : a = 0
        · subst a
          exact pureAttain_zero_left b
        have hav : a.val ≠ 0 := by simpa using ha
        let c := Ordinal.log Ordinal.omega0 a.val
        let h : NatOrdinal.{u} := ω^ of c
        let r : NatOrdinal.{u} := of (a.val - Ordinal.omega0 ^ c)
        have hlo : Ordinal.omega0 ^ c ≤ a.val := Ordinal.opow_log_le_self _ hav
        have hhi : a.val < Ordinal.omega0 ^ (c + 1) := by
          simpa only [Order.succ_eq_add_one] using
            Ordinal.lt_opow_succ_log_self Ordinal.one_lt_omega0 a.val
        have hr : r < a := Ordinal.sub_omega0_opow_log_lt hav
        have hasplit : a.val = h.val + r.val := by
          simpa only [h, r, val_wpow, val_of] using
            (Ordinal.add_sub_cancel_of_le hlo).symm
        have hnatsplit : a = h + r := by
          have hh := of_omega0_opow_add (hr.trans hhi)
          change of (Ordinal.omega0 ^ c + (a.val - Ordinal.omega0 ^ c)) = h + r at hh
          rw [Ordinal.add_sub_cancel_of_le hlo, of_val] at hh
          exact hh
        have hrb : r + b < ω^ of (c + 1) :=
          add_lt_wpow (hr.trans hhi) (hba.trans_lt hhi)
        have hsum : of (h.val + (r + b).val) = h + (r + b) := by
          exact of_omega0_opow_add hrb
        have habsplit : (a + b).val = h.val + (r + b).val := by
          rw [hnatsplit, add_assoc, ← hsum, val_of]
        apply pureAttain_of_split hasplit habsplit
        exact IH (r + b) (by rw [← hn]; exact add_lt_add_of_lt_of_le hr le_rfl) r b rfl
      rcases le_total b a with hba | hab
      · exact step a b hn hba
      · exact (step b a (by simpa [add_comm] using hn) hab).symm
  exact aux (a + b) a b rfl

/-- Two omega-power well orders have a product linear extension of their natural-product type. -/
theorem exists_monotone_equiv_wpow_product (a b : NatOrdinal.{u}) :
    ∃ e : (ω^ a).val.ToType × (ω^ b).val.ToType ≃ (ω^ (a + b)).val.ToType,
      Monotone e :=
  pureAttain a b

private theorem of_type_finite_sigma_wpow {ι : Type} [Fintype ι] [LinearOrder ι]
    (f : ι → NatOrdinal.{u}) (hf : Antitone f) :
    of (typeLT (Σₗ i : ι, (ω^ (f i)).val.ToType)) = ∑ i, ω^ (f i) := by
  let e := Fintype.orderIsoFinOfCardEq ι rfl
  have ht := (sigmaLexCongrLeft e (fun i ↦ (ω^ (f i)).val.ToType)).toRelIsoLT.ordinalType_congr
  calc
    of (typeLT (Σₗ i : ι, (ω^ (f i)).val.ToType)) =
        of (typeLT (Σₗ i : Fin (Fintype.card ι), (ω^ (f (e i))).val.ToType)) :=
      congrArg of ht.symm
    _ = ∑ i : Fin (Fintype.card ι), ω^ (f (e i)) :=
      of_type_fin_sigma_wpow _ (hf.comp_monotone e.monotone)
    _ = ∑ i : ι, ω^ (f i) := e.toEquiv.sum_comp (fun i ↦ ω^ (f i))

private theorem exists_wpow_blocks_orderIso (a : NatOrdinal.{u}) :
    ∃ n : ℕ, ∃ f : Fin n → NatOrdinal.{u}, Antitone f ∧ a = ∑ i, ω^ (f i) ∧
      Nonempty (a.val.ToType ≃o (Σₗ i : Fin n, (ω^ (f i)).val.ToType)) := by
  obtain ⟨n, f, hf, ha⟩ := exists_antitone_wpow_sum a
  refine ⟨n, f, hf, ha, ?_⟩
  apply nonempty_orderIso_of_type_eq
  have ht := congrArg val (of_type_fin_sigma_wpow f hf)
  rw [← ha, val_of] at ht
  exact (type_toType _).trans ht.symm

private structure Cell (n m : ℕ) where
  fst : Fin n
  snd : Fin m

private def cellEquiv (n m : ℕ) : Cell n m ≃ Fin n × Fin m where
  toFun p := (p.fst, p.snd)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance (n m : ℕ) : Fintype (Cell n m) :=
  Fintype.ofEquiv (Fin n × Fin m) (cellEquiv n m).symm

/-- Arbitrary ordinal well orders have a product linear extension of their natural-product type. -/
theorem exists_monotone_equiv_mul (a b : NatOrdinal.{u}) :
    ∃ e : a.val.ToType × b.val.ToType ≃ (a * b).val.ToType, Monotone e := by
  classical
  obtain ⟨n, f, hf, ha, ⟨ea⟩⟩ := exists_wpow_blocks_orderIso a
  obtain ⟨m, g, hg, hb, ⟨eb⟩⟩ := exists_wpow_blocks_orderIso b
  let key : Cell n m → NatOrdinal.{u}ᵒᵈ ×ₗ (Fin n ×ₗ Fin m) :=
    fun p ↦ toLex (OrderDual.toDual (f p.fst + g p.snd), toLex (cellEquiv n m p))
  have hk : Function.Injective key := by
    intro p q hpq
    have hh := congrArg (fun x ↦ ofLex (ofLex x).2) hpq
    exact (cellEquiv n m).injective hh
  let : LinearOrder (Cell n m) := LinearOrder.lift' key hk
  have hc : Antitone (fun p : Cell n m ↦ f p.fst + g p.snd) := by
    intro p q hpq
    change key p ≤ key q at hpq
    exact Prod.Lex.monotone_fst_ofLex hpq
  have hkey {p q : Cell n m} (hp : p.fst ≤ q.fst) (hq : p.snd ≤ q.snd) : p ≤ q := by
    change key p ≤ key q
    exact Prod.Lex.toLex_le_toLex'.mpr ⟨add_le_add (hf hp) (hg hq),
      fun _ ↦ Prod.Lex.toLex_le_toLex'.mpr ⟨hp, fun _ ↦ hq⟩⟩
  choose E hE using fun (i : Fin n) (j : Fin m) ↦
    exists_monotone_equiv_wpow_product (f i) (g j)
  let em : ((Σₗ i : Fin n, (ω^ (f i)).val.ToType) ×
      (Σₗ j : Fin m, (ω^ (g j)).val.ToType)) ≃
      (Σₗ p : Cell n m, (ω^ (f p.fst + g p.snd)).val.ToType) := {
    toFun := fun x ↦ toLex ⟨⟨(ofLex x.1).1, (ofLex x.2).1⟩,
      E (ofLex x.1).1 (ofLex x.2).1 ((ofLex x.1).2, (ofLex x.2).2)⟩
    invFun := fun z ↦
      (toLex ⟨(ofLex z).1.fst, ((E (ofLex z).1.fst (ofLex z).1.snd).symm (ofLex z).2).1⟩,
       toLex ⟨(ofLex z).1.snd, ((E (ofLex z).1.fst (ofLex z).1.snd).symm (ofLex z).2).2⟩)
    left_inv := by
      rintro ⟨⟨i, x⟩, ⟨j, y⟩⟩
      change ((toLex ⟨i, ((E i j).symm (E i j (x, y))).1⟩,
          toLex ⟨j, ((E i j).symm (E i j (x, y))).2⟩) :
          (Σₗ i : Fin n, (ω^ (f i)).val.ToType) ×
          (Σₗ j : Fin m, (ω^ (g j)).val.ToType)) =
        (toLex ⟨i, x⟩, toLex ⟨j, y⟩)
      rw [Equiv.symm_apply_apply]
    right_inv := by
      rintro ⟨⟨i, j⟩, z⟩
      change (toLex ⟨(⟨i, j⟩ : Cell n m), E i j ((E i j).symm z)⟩ :
          Σₗ p : Cell n m, (ω^ (f p.fst + g p.snd)).val.ToType) =
        toLex ⟨(⟨i, j⟩ : Cell n m), z⟩
      rw [Equiv.apply_symm_apply]
  }
  have hem : Monotone em := by
    rintro ⟨⟨i, x⟩, ⟨j, y⟩⟩ ⟨⟨i', x'⟩, ⟨j', y'⟩⟩ hxy
    change Sigma.Lex ((· < ·) : Cell n m → Cell n m → Prop)
      (fun p (x y : (ω^ (f p.fst + g p.snd)).val.ToType) ↦ x ≤ y)
      ⟨⟨i, j⟩, E i j (x, y)⟩ ⟨⟨i', j'⟩, E i' j' (x', y')⟩
    change Sigma.Lex ((· < ·) : Fin n → Fin n → Prop)
        (fun i (x y : (ω^ (f i)).val.ToType) ↦ x ≤ y) ⟨i, x⟩ ⟨i', x'⟩ ∧
      Sigma.Lex ((· < ·) : Fin m → Fin m → Prop)
        (fun j (x y : (ω^ (g j)).val.ToType) ↦ x ≤ y) ⟨j, y⟩ ⟨j', y'⟩ at hxy
    rcases hxy with ⟨hx, hy⟩
    cases hx with
    | left _ _ hi =>
      have hj : j ≤ j' := by
        rcases Sigma.lex_iff.mp hy with hj | ⟨hj, _⟩
        · exact hj.le
        · exact hj.le
      apply Sigma.Lex.left
      exact lt_of_le_of_ne (hkey hi.le hj) (fun hh ↦ hi.ne (congrArg Cell.fst hh))
    | right _ _ hxx =>
      cases hy with
      | left _ _ hj =>
        apply Sigma.Lex.left
        exact lt_of_le_of_ne (hkey le_rfl hj.le) (fun hh ↦ hj.ne (congrArg Cell.snd hh))
      | right _ _ hyy => exact Sigma.Lex.right _ _ (hE _ _ ⟨hxx, hyy⟩)
  have ht : of (typeLT (Σₗ p : Cell n m,
      (ω^ (f p.fst + g p.snd)).val.ToType)) = a * b := by
    rw [of_type_finite_sigma_wpow _ hc]
    calc
      (∑ p : Cell n m, ω^ (f p.fst + g p.snd)) =
          ∑ p : Fin n × Fin m, ω^ (f p.1 + g p.2) :=
        (cellEquiv n m).sum_comp (fun p ↦ ω^ (f p.1 + g p.2))
      _ = a * b := by
        rw [ha, hb, Finset.sum_mul]
        simp only [Finset.mul_sum, ← wpow_add, Fintype.sum_prod_type]
  obtain ⟨ez⟩ : Nonempty ((Σₗ p : Cell n m,
      (ω^ (f p.fst + g p.snd)).val.ToType) ≃o (a * b).val.ToType) := by
    apply nonempty_orderIso_of_type_eq
    exact (congrArg val ht).trans (type_toType _).symm
  let ei := OrderIso.prodCongr ea eb
  exact ⟨ei.toEquiv.trans (em.trans ez.toEquiv),
    ez.monotone.comp (hem.comp ei.monotone)⟩

/-- Two well orders admit a monotone bijection from their product to their natural-product type. -/
theorem exists_monotone_equiv_product {A B : Type u}
    [LinearOrder A] [WellFoundedLT A] [LinearOrder B] [WellFoundedLT B] :
    ∃ e : A × B ≃ (of (typeLT A) * of (typeLT B)).val.ToType, Monotone e := by
  obtain ⟨ea⟩ : Nonempty (A ≃o (of (typeLT A)).val.ToType) := by
    apply nonempty_orderIso_of_type_eq
    exact ((type_toType _).trans (val_of _)).symm
  obtain ⟨eb⟩ : Nonempty (B ≃o (of (typeLT B)).val.ToType) := by
    apply nonempty_orderIso_of_type_eq
    exact ((type_toType _).trans (val_of _)).symm
  obtain ⟨e, he⟩ := exists_monotone_equiv_mul (of (typeLT A)) (of (typeLT B))
  let ep := OrderIso.prodCongr ea eb
  exact ⟨ep.toEquiv.trans e, he.comp ep.monotone⟩

end NatOrdinal
