/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.NatOrdinal.Pow
public import Mathlib.Order.Sigma
public import Mathlib.SetTheory.Ordinal.Basic

import Mathlib.Order.RelClasses
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite decreasing decompositions into omega powers

Every natural ordinal is a finite natural sum of omega powers with nonincreasing exponents.
The corresponding consecutive well-ordered blocks have that same order type. The descending
hypothesis is essential: ordinary concatenation can absorb an earlier smaller block.

These decompositions supply the finite rectangles needed to extend maximal product orders from
pure omega-power factors to arbitrary ordinal factors.
-/

universe u

public noncomputable section

open Ordinal

instance Sigma.Lex.wellFoundedLT {ι : Type*} {A : ι → Type*}
    [LT ι] [WellFoundedLT ι]
    [∀ i, LT (A i)] [∀ i, WellFoundedLT (A i)] :
    WellFoundedLT (Σₗ i, A i) := by
  refine ((WellFounded.psigma_lex (α := ι) (β := A)
    (wellFounded_lt : WellFounded ((· < ·) : ι → ι → Prop))
    (fun i ↦ (wellFounded_lt : WellFounded ((· < ·) : A i → A i → Prop)))).onFun
    (f := fun x : Σₗ i, A i ↦ (⟨(ofLex x).1, (ofLex x).2⟩ : PSigma A))).mono ?_
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  cases h with
  | left a b hij => exact PSigma.Lex.left _ _ hij
  | right a b hab => exact PSigma.Lex.right _ hab

private def finSigmaSuccIso {n : ℕ} (A : Fin (n + 1) → Type u)
    [∀ i, LinearOrder (A i)] :
    (Σₗ i, A i) ≃o (A 0 ⊕ₗ (Σₗ i : Fin n, A i.succ)) where
  toFun x := Fin.cases (fun a ↦ toLex (Sum.inl a))
    (fun i a ↦ toLex (Sum.inr (toLex ⟨i, a⟩))) (ofLex x).1 (ofLex x).2
  invFun y := Sum.elim (fun a ↦ toLex ⟨0, a⟩)
    (fun x ↦ toLex ⟨(ofLex x).1.succ, (ofLex x).2⟩) (ofLex y)
  left_inv x := by
    obtain ⟨i, a⟩ := x
    induction i using Fin.cases <;> rfl
  right_inv y := by
    induction y using Lex.rec
    rename_i y
    obtain a | ⟨i, a⟩ := y <;> rfl
  map_rel_iff' := by
    rintro ⟨i, a⟩ ⟨j, b⟩
    change Sum.Lex ((· ≤ ·) : A 0 → A 0 → Prop)
      (Sigma.Lex ((· < ·) : Fin n → Fin n → Prop) (fun i a b ↦ a ≤ b))
      (Fin.cases (motive := fun i ↦ A i → A 0 ⊕ (Σ i : Fin n, A i.succ))
        Sum.inl (fun i a ↦ Sum.inr ⟨i, a⟩) i a)
      (Fin.cases (motive := fun i ↦ A i → A 0 ⊕ (Σ i : Fin n, A i.succ))
        Sum.inl (fun i a ↦ Sum.inr ⟨i, a⟩) j b) ↔
      Sigma.Lex ((· < ·) : Fin (n + 1) → Fin (n + 1) → Prop)
        (fun i a b ↦ a ≤ b) ⟨i, a⟩ ⟨j, b⟩
    induction i using Fin.cases <;> induction j using Fin.cases
    · simp [Sigma.lex_iff]
    · simp [Sigma.lex_iff]
    · simp [Sigma.lex_iff]
    · rename_i i j
      by_cases h : i = j
      · subst j
        simp [Sigma.lex_iff]
      · simp [Sigma.lex_iff, h]

/-- The type of a finite lexicographic sum is the ordinary sum of its component types. -/
theorem Ordinal.type_fin_sigma {n : ℕ} (A : Fin n → Type u)
    [∀ i, LinearOrder (A i)] [∀ i, WellFoundedLT (A i)] :
    typeLT (Σₗ i : Fin n, A i) = (List.ofFn (fun i ↦ typeLT (A i))).sum := by
  induction n with
  | zero =>
    have : IsEmpty (Σₗ i : Fin 0, A i) := ⟨fun x ↦ Fin.elim0 x.1⟩
    rw [Ordinal.type_eq_zero_of_empty, List.ofFn_zero, List.sum_nil]
  | succ n ih =>
    rw [(finSigmaSuccIso A).toRelIsoLT.ordinalType_congr, type_lt_sum_lex,
      ih (fun i ↦ A i.succ), List.ofFn_succ, List.sum_cons]

namespace NatOrdinal

/-- A finite sum of ordinals below an omega power stays below that power. -/
theorem sum_lt_wpow {ι : Type*} (s : Finset ι) (f : ι → NatOrdinal.{u})
    {c : NatOrdinal.{u}} (h : ∀ i ∈ s, f i < ω^ c) : ∑ i ∈ s, f i < ω^ c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact add_lt_wpow (h i (Finset.mem_insert_self i s))
      (ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj)))

/-- Consecutive omega-power blocks in descending exponent order have their natural-sum type. -/
theorem of_type_fin_sigma_wpow {n : ℕ} (f : Fin n → NatOrdinal.{u})
    (hf : Antitone f) :
    of (typeLT (Σₗ i : Fin n, (ω^ (f i)).val.ToType)) = ∑ i, ω^ (f i) := by
  induction n with
  | zero =>
    have : IsEmpty (Σₗ i : Fin 0, (ω^ (f i)).val.ToType) := ⟨fun x ↦ Fin.elim0 x.1⟩
    rw [Ordinal.type_eq_zero_of_empty, of_zero, Fin.sum_univ_zero]
  | succ n ih =>
    have hi := ih (fun i ↦ f i.succ) (hf.comp_monotone Fin.strictMono_succ.monotone)
    have ht := (finSigmaSuccIso (fun i ↦ (ω^ (f i)).val.ToType)).toRelIsoLT.ordinalType_congr
    rw [ht, type_lt_sum_lex, type_toType, Fin.sum_univ_succ]
    have hb : (∑ i : Fin n, ω^ (f i.succ)) < ω^ (f 0 + 1) := by
      apply sum_lt_wpow
      intro i hi
      exact wpow_lt_wpow.mpr ((hf (Fin.zero_le i.succ)).trans_lt (lt_add_one _))
    have hb' : (∑ i : Fin n, ω^ (f i.succ)).val < Ordinal.omega0 ^ ((f 0).val + 1) := by
      simpa only [val_wpow, val_add_one] using val.strictMono hb
    have h := of_omega0_opow_add hb'
    rw [← hi] at h
    rw [← hi, val_wpow (f 0)]
    simpa only [val_of, of_val] using h


/-- Every ordinal is a finite natural sum of omega powers with nonincreasing exponents. -/
theorem exists_antitone_wpow_sum (a : NatOrdinal.{u}) :
    ∃ n : ℕ, ∃ f : Fin n → NatOrdinal.{u}, Antitone f ∧ a = ∑ i, ω^ (f i) := by
  induction a using NatOrdinal.lt_wf.induction with
  | h a ih =>
    by_cases ha : a = 0
    · subst a
      exact ⟨0, Fin.elim0, fun i ↦ Fin.elim0 i, by simp⟩
    have hav : a.val ≠ 0 := by simpa using ha
    let c : NatOrdinal.{u} := of (Ordinal.log Ordinal.omega0 a.val)
    let r : NatOrdinal.{u} := of (a.val - (ω^ c).val)
    have hr : r < a := Ordinal.sub_omega0_opow_log_lt hav
    have hlo : (ω^ c).val ≤ a.val := Ordinal.opow_log_le_self _ hav
    have hhi : a < ω^ (c + 1) := by
      apply val.lt_iff_lt.mp
      simpa only [val_wpow, val_add_one, c, val_of, Order.succ_eq_add_one] using
        Ordinal.lt_opow_succ_log_self Ordinal.one_lt_omega0 a.val
    have hsplit : a = ω^ c + r := by
      have ht : r.val < Ordinal.omega0 ^ (c.val + 1) := by
        simpa only [val_wpow, val_add_one] using val.strictMono (hr.trans hhi)
      have hh := of_omega0_opow_add ht
      change of ((ω^ c).val + (a.val - (ω^ c).val)) = ω^ c + r at hh
      rw [Ordinal.add_sub_cancel_of_le hlo, of_val] at hh
      exact hh
    obtain ⟨n, f, hf, hsum⟩ := ih r hr
    have hfc (i : Fin n) : f i ≤ c := by
      have hterm : ω^ (f i) ≤ r := by
        rw [hsum]
        exact Finset.single_le_sum (f := fun j : Fin n ↦ ω^ (f j))
          (fun j _ ↦ (bot_le : (0 : NatOrdinal.{u}) ≤ ω^ (f j))) (Finset.mem_univ i)
      exact Order.lt_add_one_iff.mp (wpow_lt_wpow.mp (hterm.trans_lt (hr.trans hhi)))
    refine ⟨n + 1, Fin.cons c f, ?_, ?_⟩
    · intro i j hij
      induction i using Fin.cases <;> induction j using Fin.cases
      · exact le_rfl
      · exact hfc _
      · exact False.elim ((not_le_of_gt (Fin.succ_pos _)) hij)
      · exact hf (Fin.succ_le_succ_iff.mp hij)
    · rw [Fin.sum_univ_succ, Fin.cons_zero]
      simpa only [Fin.cons_succ] using hsplit.trans (congrArg (ω^ c + ·) hsum)


end NatOrdinal
