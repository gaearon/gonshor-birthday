/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadCost
public import GonshorBirthday.Surreal.Birthday.NormalFormReplacement
public import GonshorBirthday.Surreal.Birthday.ReducedCostBound

import GonshorBirthday.Surreal.HahnSeries.NormalFormMul

/-!
# Reduced costs for actual normal-form product terms

A retained product boundary imposes the two shifted input retention conditions.
Positive replacement prevents support cancellation and makes every fibre with a
nondyadic input factor nondyadic. Auxiliary surreal cuts encode both the input's
own right prefixes and the shifted output right prefixes at once. The unrestricted
reduced-cost addition inequality then bounds each actual product monomial cost.
-/

universe u
public noncomputable section
namespace Surreal
open Set

/-- A supported nondyadic input factor makes its replacement product fibre nondyadic. -/
theorem birthday_coeff_mul_replacement_eq_omega0 {τ : ℝ}
    (hτpos : 0 < τ) (hτ : Transcendental ℚ τ) (x y : Surreal.{u})
    {a b : Surreal.{u}} (ha : a ∈ x.support) (hb : b ∈ y.support)
    (hinf : (x.coeff a : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0 ∨
      (y.coeff b : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0) :
    ((normalFormBirthdayReplacement τ x * normalFormBirthdayReplacement τ y).coeff (a + b) :
      Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0 := by
  have he : SurrealHahnSeries.supportAntidiagonal
      (normalFormBirthdayReplacement τ x).toHahnSeries
      (normalFormBirthdayReplacement τ y).toHahnSeries (a + b) =
      SurrealHahnSeries.supportAntidiagonal x.toHahnSeries y.toHahnSeries (a + b) := by
    apply SurrealHahnSeries.supportAntidiagonal_eq_of_support_eq
    · simp only [support_toHahnSeries, support_normalFormBirthdayReplacement hτpos]
    · simp only [support_toHahnSeries, support_normalFormBirthdayReplacement hτpos]
  rw [coeff_mul, he]
  simp only [coeff_normalFormBirthdayReplacement]
  apply birthday_sum_replacement_mul_eq_omega0 _ _ _ hτ
  · intro p hp
    obtain ⟨hp1, hp2, _⟩ := (SurrealHahnSeries.mem_supportAntidiagonal _ _ _ _).mp hp
    simpa only [support_toHahnSeries, ← support_coeff, Function.mem_support] using
      And.intro hp1 hp2
  · refine ⟨(a, b), ?_, ?_⟩
    · apply (SurrealHahnSeries.mem_supportAntidiagonal _ _ _ _).mpr
      simpa only [support_toHahnSeries] using And.intro ha (And.intro hb (Eq.refl (a + b)))
    · simpa only [birthday_real_eq_omega0_iff] using hinf

/-- A retained replacement-product boundary satisfies the shifted first-input head condition. -/
theorem head_retention_left_of_replacement_product {τ : ℝ}
    (hτpos : 0 < τ) (hτ : Transcendental ℚ τ) (x y : Surreal.{u})
    {a b v : Surreal.{u}} (hb : b ∈ y.support) (hv : a + b < v)
    (hret : ((normalFormBirthdayReplacement τ x * normalFormBirthdayReplacement τ y).normalFormTrunc
        (a + b)).support ⊆ Ici v ∧
      (((normalFormBirthdayReplacement τ x * normalFormBirthdayReplacement τ y).normalFormTrunc
        (a + b)).coeff v : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) :
    ((normalFormBirthdayReplacement τ x).normalFormTrunc a).support ⊆ Ici (v - b) ∧
      (((normalFormBirthdayReplacement τ x).normalFormTrunc a).coeff (v - b) :
        Surreal.{u}).birthday <
        NatOrdinal.of Ordinal.omega0 := by
  have hav : a < v - b := lt_sub_iff_add_lt.mpr hv
  constructor
  · intro w hw
    rw [support_trunc, mem_inter_iff, support_normalFormBirthdayReplacement hτpos] at hw
    have hp : w + b ∈
        (normalFormBirthdayReplacement τ x * normalFormBirthdayReplacement τ y).support :=
      (mem_support_mul_normalFormBirthdayReplacement hτpos x y (w + b)).mpr
        ⟨w, hw.1, b, hb, rfl⟩
    have hhead : w + b ∈
        ((normalFormBirthdayReplacement τ x * normalFormBirthdayReplacement τ y).normalFormTrunc
          (a + b)).support := by
      rw [support_trunc, mem_inter_iff]
      exact ⟨hp, by change a + b < w + b; exact add_lt_add_left hw.2 b⟩
    change v - b ≤ w
    exact sub_le_iff_le_add.mpr (show v ≤ w + b from hret.1 hhead)
  · rw [coeff_trunc_of_lt hav, birthday_coeff_normalFormBirthdayReplacement hτ]
    by_contra hn
    have hcoeff : (x.coeff (v - b) : Surreal.{u}).birthday =
        NatOrdinal.of Ordinal.omega0 :=
      le_antisymm (birthday_real_le_omega0 _) (le_of_not_gt hn)
    have hne : x.coeff (v - b) ≠ 0 := by
      intro he
      rw [he, Real.toSurreal_zero, birthday_zero] at hcoeff
      exact (show (0 : NatOrdinal.{u}) < NatOrdinal.of Ordinal.omega0 by
        exact_mod_cast Ordinal.omega0_pos).ne hcoeff
    have hprod := birthday_coeff_mul_replacement_eq_omega0 hτpos hτ x y
      (mem_support_iff.mpr hne) hb (Or.inl hcoeff)
    rw [sub_add_cancel] at hprod
    have hh := hret.2
    rw [coeff_trunc_of_lt hv, hprod] at hh
    exact hh.false

/-- A downward-closed predicate on a small set above a surreal is represented by a strict cutoff. -/
theorem exists_cutoff_of_downward_closed (z : Surreal.{u}) (P : Surreal.{u} → Prop)
    (U : Set Surreal.{u}) [Small.{u} U]
    (hP : ∀ u v : Surreal.{u}, u ≤ v → P v → P u) (hU : U ⊆ Ioi z) :
    ∃ A : Surreal.{u}, z < A ∧ ∀ u ∈ U, P u ↔ u ≤ A := by
  let V : Set Surreal.{u} := {u ∈ U | P u}
  let W : Set Surreal.{u} := {u ∈ U | ¬ P u}
  have : Small.{u} V := small_subset (show V ⊆ U from fun _ h ↦ h.1)
  have : Small.{u} W := small_subset (show W ⊆ U from fun _ h ↦ h.1)
  have hVW : ∀ u ∈ insert z V, ∀ w ∈ W, u < w := by
    intro u hu w hw
    rcases mem_insert_iff.mp hu with rfl | hu
    · exact hU hw.1
    · exact lt_of_not_ge (fun hwu ↦ hw.2 (hP w u hwu hu.2))
  let A : Surreal.{u} := !{insert z V | W}'hVW
  refine ⟨A, lt_ofSets_of_mem_left (mem_insert _ _), ?_⟩
  intro u hu
  constructor
  · intro hp
    exact (lt_ofSets_of_mem_left (H := hVW)
      (show u ∈ insert z V from mem_insert_of_mem z ⟨hu, hp⟩)).le
  · intro huA
    by_contra hn
    exact huA.not_gt (ofSets_lt_of_mem_right (show u ∈ W from ⟨hu, hn⟩))

/-- One cutoff represents native head retention on any small set of test values above the term. -/
theorem exists_head_retention_cutoff_on (H s : Surreal.{u}) (U : Set Surreal.{u})
    [Small.{u} U] (hU : U ⊆ Ioi s) :
    ∃ A : Surreal.{u}, s < A ∧ ∀ w ∈ U,
      (H.support ⊆ Ici w ∧
        (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) ↔ w ≤ A := by
  apply exists_cutoff_of_downward_closed s _ U _ hU
  intro u v huv hv
  rcases huv.lt_or_eq with huv | rfl
  · exact support_ge_and_coeff_birthday_lt_of_lt hv.1 huv
  · exact hv

/-- Each actual product monomial cost fits the natural product of its input head costs. -/
theorem headOmegaCost_mul_replacement_le {τ : ℝ}
    (hτpos : 0 < τ) (hτ : Transcendental ℚ τ) (x y : Surreal.{u})
    {a b : Surreal.{u}} (ha : a ∈ x.support) (hb : b ∈ y.support) :
    headOmegaCost
      ((normalFormBirthdayReplacement τ x * normalFormBirthdayReplacement τ y).normalFormTrunc
      (a + b)) (a + b) ≤
      headOmegaCost ((normalFormBirthdayReplacement τ x).normalFormTrunc a) a *
        headOmegaCost ((normalFormBirthdayReplacement τ y).normalFormTrunc b) b := by
  let U : Set Surreal.{u} := rightPrefixes a ∪ (fun v ↦ v - b) '' rightPrefixes (a + b)
  let V : Set Surreal.{u} := rightPrefixes b ∪ (fun v ↦ v - a) '' rightPrefixes (a + b)
  have hU : U ⊆ Ioi a := by
    intro u hu
    rcases hu with hu | ⟨v, hv, rfl⟩
    · exact (mem_rightPrefixes_iff.mp hu).2
    · exact lt_sub_iff_add_lt.mpr (mem_rightPrefixes_iff.mp hv).2
  have hV : V ⊆ Ioi b := by
    intro u hu
    rcases hu with hu | ⟨v, hv, rfl⟩
    · exact (mem_rightPrefixes_iff.mp hu).2
    · change b < v - a
      apply lt_sub_iff_add_lt.mpr
      simpa only [add_comm] using (mem_rightPrefixes_iff.mp hv).2
  obtain ⟨A, haA, hA⟩ := exists_head_retention_cutoff_on
    ((normalFormBirthdayReplacement τ x).normalFormTrunc a) a U hU
  obtain ⟨B, hbB, hB⟩ := exists_head_retention_cutoff_on
    ((normalFormBirthdayReplacement τ y).normalFormTrunc b) b V hV
  have hcostA := headOmegaCost_eq_reducedOmegaCost
    ((normalFormBirthdayReplacement τ x).normalFormTrunc a) a A (fun w hw ↦ hA w (Or.inl hw))
  have hcostB := headOmegaCost_eq_reducedOmegaCost
    ((normalFormBirthdayReplacement τ y).normalFormTrunc b) b B (fun w hw ↦ hB w (Or.inl hw))
  obtain ⟨C, _, hC, hretC⟩ := exists_head_rightPrefix_retention_cutoff
    ((normalFormBirthdayReplacement τ x * normalFormBirthdayReplacement τ y).normalFormTrunc
      (a + b))
    (a + b)
  have hCbound : C ≤ min (A + b) (a + B) := by
    rcases hC with rfl | hC
    · exact le_min (add_le_add haA.le le_rfl) (add_le_add le_rfl hbB.le)
    · have hret := (hretC C hC).mpr le_rfl
      have hleft := head_retention_left_of_replacement_product hτpos hτ x y hb
        (mem_rightPrefixes_iff.mp hC).2 hret
      have hright := head_retention_left_of_replacement_product hτpos hτ y x ha
        (a := b) (v := C) (by simpa only [add_comm] using (mem_rightPrefixes_iff.mp hC).2)
        (by simpa only [mul_comm, add_comm] using hret)
      have hleA : C - b ≤ A := (hA (C - b) (Or.inr ⟨C, hC, rfl⟩)).mp hleft
      have hleB : C - a ≤ B := (hB (C - a) (Or.inr ⟨C, hC, rfl⟩)).mp hright
      exact le_min (sub_le_iff_le_add.mp hleA)
        (by simpa only [add_comm] using sub_le_iff_le_add.mp hleB)
  rw [hcostA, hcostB,
    headOmegaCost_eq_reducedOmegaCost _ _ C hretC]
  exact (reducedOmegaCost_mono (a + b) hCbound).trans
    (reducedOmegaCost_add_le a b A B haA.le hbB.le)

end Surreal
