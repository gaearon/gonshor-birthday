/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostPrefix
public import GonshorBirthday.NatOrdinal.OrderedSumBound
public import GonshorBirthday.NatOrdinal.FinalPower

/-!
# Uniform bounds for reduced omega-map suffixes

The minus subsequence is bounded by its number of original positions times
the largest expanded block weight. The plus subsequence is bounded by the
whole plus-only expansion. Their natural sum bounds any selected contribution.
-/

universe u

public noncomputable section

namespace Surreal

open Ordinal

/-- In any subsequence of exponent positions, the plus blocks contribute at most the
plus-only length. The other summand counts the selected minus blocks with their actual weights. -/
theorem omegaExpansionContribution_le_minus_add_wpow (x : Surreal.{u})
    {I : Type u} [LinearOrder I] [WellFoundedLT I] (e : I ↪o x.birthday.val.ToType) :
    NatOrdinal.of (typeLT (Σₗ i : I,
      (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of (e i).toOrd.1)) + 1)).val.ToType)) ≤
      NatOrdinal.of (typeLT (Σₗ i :
        {i : I | x < birthdayTruncation x (NatOrdinal.of (e i).toOrd.1)},
        (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of (e i.1).toOrd.1)) + 1)).val.ToType)) +
      ω^ plusCount x := by
  let W (i : x.birthday.val.ToType) :=
    (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of i.toOrd.1)) + 1)).val.ToType
  let M : Set I := {i | x < birthdayTruncation x (NatOrdinal.of (e i).toOrd.1)}
  let P : Set x.birthday.val.ToType :=
    {i | birthdayTruncation x (NatOrdinal.of i.toOrd.1) < x}
  have hp (i : (Mᶜ : Set I)) : birthdayTruncation x (NatOrdinal.of (e i.1).toOrd.1) < x := by
    have hi := NatOrdinal.of.strictMono (e i.1).toOrd.2
    apply lt_of_le_of_ne (le_of_not_gt i.2)
    intro he
    have hb := birthday_birthdayTruncation x hi.le
    rw [he] at hb
    exact hi.ne hb.symm
  let f : (Mᶜ : Set I) → P := fun i ↦ ⟨e i.1, hp i⟩
  have hf : StrictMono f := fun _ _ h ↦ e.strictMono h
  have hplus : NatOrdinal.of (typeLT (Σₗ i : (Mᶜ : Set I), W (e i.1))) ≤
      ω^ plusCount x := by
    have hb := Ordinal.type_sigma_le_of_embedding
      (A := fun i : (Mᶜ : Set I) ↦ W (e i.1)) (B := fun i : P ↦ W i.1)
      (OrderEmbedding.ofStrictMono f hf)
      (fun _ ↦ OrderEmbedding.ofStrictMono id strictMono_id)
    have he := omegaExpansionLength_plusPositions x
    rw [omegaExpansionLength_eq] at he
    exact (NatOrdinal.of.monotone hb).trans
      ((NatOrdinal.of.monotone le_add_self).trans_eq he)
  exact (NatOrdinal.of_type_sigma_le_add_compl (fun i : I ↦ W (e i)) M).trans
    (add_le_add le_rfl hplus)

/-- Including the initial sign, an expansion fits the natural sum of its minus and plus lengths. -/
theorem omegaExpansionLength_le_minus_add_wpow (x : Surreal.{u}) (S : Set x.birthday.val.ToType) :
    omegaExpansionLength x S ≤ NatOrdinal.of (typeLT (Σₗ j :
      {i : S | x < birthdayTruncation x (NatOrdinal.of i.1.toOrd.1)},
      (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of j.1.1.toOrd.1)) + 1)).val.ToType)) +
        ω^ plusCount x := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨j, hj⟩
  · rw [omegaExpansionLength_empty]
    exact (NatOrdinal.wpow_zero ▸ NatOrdinal.wpow_le_wpow.mpr
      (show 0 ≤ plusCount x from bot_le)).trans (le_add_of_nonneg_left bot_le)
  let W (i : S) := ω^ (plusCount (birthdayTruncation x (NatOrdinal.of i.1.toOrd.1)) + 1)
  have h := Ordinal.type_sigma_block_le (fun i : S ↦ (W i).val.ToType) ⟨j, hj⟩
  rw [Ordinal.type_toType] at h
  have hω : Ordinal.omega0 ≤ (W ⟨j, hj⟩).val := by
    simpa only [NatOrdinal.wpow_one, NatOrdinal.val_of] using NatOrdinal.val.monotone
      (NatOrdinal.wpow_le_wpow.mpr (show (1 : NatOrdinal.{u}) ≤ _ + 1 from
        le_add_of_nonneg_left bot_le))
  rw [omegaExpansionLength_eq, Ordinal.one_add_of_omega0_le (hω.trans h)]
  exact omegaExpansionContribution_le_minus_add_wpow x
    (OrderEmbedding.ofStrictMono Subtype.val (fun _ _ h ↦ h))

/-- Minus-position count and the plus-only baseline bound every selected expanded contribution. -/
theorem omegaExpansionContribution_le_of_embedding (x : Surreal.{u})
    {I : Type u} [LinearOrder I] [WellFoundedLT I] (e : I ↪o x.birthday.val.ToType) :
    NatOrdinal.of (typeLT (Σₗ i : I,
      (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of (e i).toOrd.1)) + 1)).val.ToType)) ≤
      NatOrdinal.of ((ω^ (plusCount x + 1)).val *
        typeLT {i : I | x < birthdayTruncation x (NatOrdinal.of (e i).toOrd.1)}) +
      ω^ plusCount x := by
  let W (i : x.birthday.val.ToType) :=
    (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of i.toOrd.1)) + 1)).val.ToType
  let M : Set I := {i | x < birthdayTruncation x (NatOrdinal.of (e i).toOrd.1)}
  have hminus : typeLT (Σₗ i : M, W (e i.1)) ≤
      (ω^ (plusCount x + 1)).val * typeLT M := by
    apply Ordinal.type_sigma_le_mul_of_le
    intro i
    rw [Ordinal.type_toType]
    apply NatOrdinal.val.monotone
    apply NatOrdinal.wpow_le_wpow.mpr
    exact add_le_add (plusCount_birthdayTruncation_le x
      (NatOrdinal.of.strictMono (e i.1).toOrd.2).le) le_rfl
  exact (omegaExpansionContribution_le_minus_add_wpow x e).trans
    (add_le_add (NatOrdinal.of.monotone hminus) le_rfl)

/-- Minus-position count and the plus-only baseline bound any selected original positions. -/
theorem omegaExpansionContribution_le (x : Surreal.{u})
    (S : Set x.birthday.val.ToType) :
    NatOrdinal.of (typeLT (Σₗ i : S,
      (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of i.1.toOrd.1)) + 1)).val.ToType)) ≤
      NatOrdinal.of ((ω^ (plusCount x + 1)).val *
        typeLT {i : S | x < birthdayTruncation x (NatOrdinal.of i.1.toOrd.1)}) +
      ω^ plusCount x :=
  omegaExpansionContribution_le_of_embedding x
    (OrderEmbedding.ofStrictMono Subtype.val (fun _ _ h ↦ h))

/-- A suffix of a pure reduced cost has the same order type as the whole cost. -/
theorem reducedOmegaCost_tail_eq_wpow_of_eq {C x : Surreal.{u}} {p : NatOrdinal.{u}}
    (hcost : reducedOmegaCost C x = ω^ p) (j : reducedOmegaPositions C x) :
    NatOrdinal.of (typeLT (Σₗ i : Set.Ici j,
      (ω^ (plusCount (birthdayTruncation x
        (NatOrdinal.of i.1.1.toOrd.1)) + 1)).val.ToType)) = ω^ p := by
  have hpre : reducedOmegaCost C (birthdayTruncation x (NatOrdinal.of j.1.toOrd.1)) <
      ω^ p := by
    rw [← hcost]
    apply reducedOmegaCost_birthdayTruncation_lt C x
      (NatOrdinal.of.strictMono j.1.toOrd.2)
    exact mem_reducedOmegaPositions.mp j.2
  have hv := congrArg NatOrdinal.val (reducedOmegaCost_eq_prefix_add_tail C x j)
  rw [hcost, NatOrdinal.val_of] at hv
  have hs := NatOrdinal.wpow_osub_of_lt hpre
  rw [hv, Ordinal.add_sub_cancel] at hs
  exact hs

/-- A power bound on retained suffix minuses bounds the exponent of a pure reduced cost. -/
theorem pure_reducedOmegaCost_exponent_le_of_tail {C x : Surreal.{u}}
    {p q : NatOrdinal.{u}} (hcost : reducedOmegaCost C x = ω^ p)
    (j : reducedOmegaPositions C x)
    (hminus : typeLT {i : Set.Ici j | x < birthdayTruncation x
      (NatOrdinal.of i.1.1.toOrd.1)} ≤ (ω^ q).val) :
    p ≤ NatOrdinal.of ((plusCount x).val + 1 + q.val) := by
  let e : Set.Ici j ↪o x.birthday.val.ToType :=
    OrderEmbedding.ofStrictMono (fun i ↦ i.1.1) (fun _ _ h ↦ h)
  have hb := omegaExpansionContribution_le_of_embedding x e
  change NatOrdinal.of (typeLT (Σₗ i : Set.Ici j,
    (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of i.1.1.toOrd.1)) + 1)).val.ToType)) ≤
    NatOrdinal.of ((ω^ (plusCount x + 1)).val * typeLT {i : Set.Ici j |
      x < birthdayTruncation x (NatOrdinal.of i.1.1.toOrd.1)}) + ω^ plusCount x at hb
  rw [reducedOmegaCost_tail_eq_wpow_of_eq hcost j] at hb
  have hm : NatOrdinal.of ((ω^ (plusCount x + 1)).val * typeLT {i : Set.Ici j |
      x < birthdayTruncation x (NatOrdinal.of i.1.1.toOrd.1)}) ≤
      ω^ (NatOrdinal.of ((plusCount x).val + 1 + q.val)) := by
    have h := mul_le_mul_right hminus (ω^ (plusCount x + 1)).val
    apply NatOrdinal.of.monotone
    simpa only [NatOrdinal.val_wpow, NatOrdinal.val_add_one, NatOrdinal.val_of,
      ← Ordinal.opow_add] using h
  have hP : plusCount x ≤ NatOrdinal.of ((plusCount x).val + 1 + q.val) :=
    NatOrdinal.of.monotone (le_self_add.trans le_self_add)
  by_contra hn
  have hlt := lt_of_not_ge hn
  have hsum := NatOrdinal.add_lt_wpow (NatOrdinal.wpow_lt_wpow.mpr hlt)
    (NatOrdinal.wpow_lt_wpow.mpr (hP.trans_lt hlt))
  exact (hb.trans (add_le_add hm le_rfl)).not_gt hsum

/-- Counting all original suffix minuses suffices when retained minuses are cofinal. -/
theorem pure_reducedOmegaCost_exponent_le_of_minus_suffix {C x : Surreal.{u}}
    {p q c : NatOrdinal.{u}} (hcost : reducedOmegaCost C x = ω^ p) (hc : c < x.birthday)
    (hcof : ∀ a < x.birthday, ∃ y ∈ rightPrefixes x, a < y.birthday ∧ y ≤ C)
    (hminus : typeLT {i : x.birthday.val.ToType | c ≤ NatOrdinal.of i.toOrd.1 ∧
      x < birthdayTruncation x (NatOrdinal.of i.toOrd.1)} ≤ (ω^ q).val) :
    p ≤ NatOrdinal.of ((plusCount x).val + 1 + q.val) := by
  obtain ⟨y, hy, hcy, hyC⟩ := hcof c hc
  have hyb := birthday_lt_of_mem_rightPrefixes hy
  let j : reducedOmegaPositions C x :=
    ⟨Ordinal.ToType.mk ⟨y.birthday.val, NatOrdinal.val.strictMono hyb⟩, by
      apply mem_reducedOmegaPositions.mpr
      right
      simpa only [Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val,
        (mem_rightPrefixes_iff.mp hy).1] using hyC⟩
  apply pure_reducedOmegaCost_exponent_le_of_tail hcost j
  let M := {i : Set.Ici j | x < birthdayTruncation x (NatOrdinal.of i.1.1.toOrd.1)}
  let N := {i : x.birthday.val.ToType | c ≤ NatOrdinal.of i.toOrd.1 ∧
    x < birthdayTruncation x (NatOrdinal.of i.toOrd.1)}
  have hi (i : M) : c ≤ NatOrdinal.of i.1.1.1.toOrd.1 := by
    have hb : NatOrdinal.of j.1.toOrd.1 ≤ NatOrdinal.of i.1.1.1.toOrd.1 :=
      NatOrdinal.of.monotone (Ordinal.ToType.mk.symm.monotone i.1.2)
    have hj : NatOrdinal.of j.1.toOrd.1 = y.birthday := by
      simp only [j, Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val]
    rw [hj] at hb
    exact hcy.le.trans hb
  let f : M → N := fun i ↦ ⟨i.1.1.1, hi i, i.2⟩
  have hf : StrictMono f := fun _ _ h ↦ h
  exact (RelEmbedding.ofMonotone f hf).ordinal_type_le.trans hminus

end Surreal
