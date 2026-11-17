/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadCoefficientLength
public import GonshorBirthday.Surreal.Birthday.NormalFormLimit

import GonshorBirthday.NatOrdinal.OrderedSumPosition
import Mathlib.Order.Minimal

/-!
# Exact ordered-sum birthdays of arbitrary normal forms

Every position before a surreal's birthday lies between a proper normal-form
truncation's birthday and that of its completed boundary term. Choosing the first
completed term crossing that position partitions the entire intrinsic birthday.
The interval lengths are the native complete term costs. Their lexicographic sum
is order-isomorphic to the birthday, and its earlier blocks give every truncation
birthday. All support lengths, coefficient signs, and the empty support are allowed.
-/

universe u
public noncomputable section
namespace Surreal
open Set
open scoped Ordinal

/-- Every completed normal-form term is no older than the whole surreal. -/
theorem birthday_trunc_add_coeff_wpow_le (x s : Surreal.{u}) :
    (x.normalFormTrunc s + (x.coeff s : Surreal) * ω^ s).birthday ≤ x.birthday := by
  have h := birthday_birthdayTruncation_le_birthday x
    (x.normalFormTrunc s + (x.coeff s : Surreal) * ω^ s).birthday
  rwa [birthdayTruncation_trunc_add_coeff_wpow] at h

/-- Completing a normal-form term cannot decrease its head birthday. -/
theorem birthday_trunc_le_trunc_add_coeff_wpow (x s : Surreal.{u}) :
    (x.normalFormTrunc s).birthday ≤
      (x.normalFormTrunc s + (x.coeff s : Surreal) * ω^ s).birthday := by
  rw [birthday_trunc_add_coeff_mul_wpow]
  exact NatOrdinal.of.monotone le_self_add

/-- Completed normal-form term birthdays determine every bound on the whole birthday. -/
theorem birthday_le_iff_trunc_add_coeff_wpow (x : Surreal.{u}) (B : NatOrdinal.{u}) :
    x.birthday ≤ B ↔ ∀ s ∈ x.support,
      (x.normalFormTrunc s + (x.coeff s : Surreal) * ω^ s).birthday ≤ B := by
  constructor
  · exact fun h s _ ↦ (birthday_trunc_add_coeff_wpow_le x s).trans h
  · intro h
    by_cases hlim : ∀ s ∈ x.support, ∃ t ∈ x.support, t < s
    · apply (birthday_le_iff_trunc_of_no_min_support x hlim B).mpr
      exact fun s hs ↦ (birthday_trunc_le_trunc_add_coeff_wpow x s).trans (h s hs)
    · push Not at hlim
      obtain ⟨s, hs, hmin⟩ := hlim
      have he := eq_trunc_add_coeff_wpow_of_support_ge (x := x) (s := s) hmin
      exact he ▸ h s hs

/-- Every smaller birthday is exceeded by some completed normal-form term. -/
theorem exists_trunc_add_coeff_wpow_birthday_gt {x : Surreal.{u}} {a : NatOrdinal.{u}}
    (ha : a < x.birthday) : ∃ s ∈ x.support,
      a < (x.normalFormTrunc s + (x.coeff s : Surreal) * ω^ s).birthday := by
  by_contra hn
  push Not at hn
  exact ha.not_ge ((birthday_le_iff_trunc_add_coeff_wpow x a).mpr hn)

private theorem trunc_trunc_eq_of_lt {x s t : Surreal.{u}} (hst : s < t) :
    (x.normalFormTrunc s).normalFormTrunc t = x.normalFormTrunc t := by
  apply toHahnSeries_inj.mp
  rw [toHahnSeries_trunc, toHahnSeries_trunc, SurrealHahnSeries.trunc_trunc,
    max_eq_right hst.le, toHahnSeries_trunc]

/-- A completed higher term is no older than every later normal-form truncation. -/
theorem birthday_trunc_add_coeff_wpow_le_trunc {x s t : Surreal.{u}} (hts : t < s) :
    (x.normalFormTrunc s + (x.coeff s : Surreal) * ω^ s).birthday ≤
      (x.normalFormTrunc t).birthday := by
  have h := birthday_trunc_add_coeff_wpow_le (x.normalFormTrunc t) s
  rwa [trunc_trunc_eq_of_lt hts, coeff_trunc_of_lt hts] at h

/-- Every position before the birthday lies in one supported normal-form term interval. -/
theorem exists_normalForm_birthday_interval {x : Surreal.{u}} {a : NatOrdinal.{u}}
    (ha : a < x.birthday) : ∃ s ∈ x.support,
      (x.normalFormTrunc s).birthday ≤ a ∧
        a < (x.normalFormTrunc s + (x.coeff s : Surreal) * ω^ s).birthday := by
  obtain ⟨t, ht, hta⟩ := exists_trunc_add_coeff_wpow_birthday_gt ha
  obtain ⟨s, hs, hmax⟩ := exists_maximal_of_wellFoundedGT
    (fun s : x.support ↦
      a < (x.normalFormTrunc s + (x.coeff s : Surreal) * ω^ (s : Surreal)).birthday)
    ⟨⟨t, ht⟩, hta⟩
  refine ⟨s, s.2, ?_, hs⟩
  by_contra hn
  obtain ⟨t, ht, hta⟩ := exists_trunc_add_coeff_wpow_birthday_gt (lt_of_not_ge hn)
  rw [support_trunc, mem_inter_iff] at ht
  rw [trunc_trunc_eq_of_lt ht.2, coeff_trunc_of_lt ht.2] at hta
  exact ht.2.not_ge (hmax (y := ⟨t, ht.1⟩) hta ht.2.le)

/-- The exact term costs partition the intrinsic birthday in normal-form order. -/
theorem exists_orderIso_normalForm_birthday (x : Surreal.{u}) :
    ∃ f : (Σₗ i : x.toHahnSeries.length.ToType,
      (headCoefficientCost (x.normalFormTrunc (x.toHahnSeries.exp i.toOrd))
        (x.toHahnSeries.exp i.toOrd) (x.coeff (x.toHahnSeries.exp i.toOrd))).val.ToType) ≃o
          x.birthday.val.ToType,
      ∀ i t, (f (toLex ⟨i, t⟩)).toOrd.1 =
        (x.normalFormTrunc (x.toHahnSeries.exp i.toOrd)).birthday.val + t.toOrd.1 := by
  let I := x.toHahnSeries.length.ToType
  let e (i : I) : Surreal.{u} := x.toHahnSeries.exp i.toOrd
  let B (i : I) : Ordinal.{u} := (x.normalFormTrunc (e i)).birthday.val
  let c (i : I) : NatOrdinal.{u} :=
    headCoefficientCost (x.normalFormTrunc (e i)) (e i) (x.coeff (e i))
  let W := (Σₗ i : I, (c i).val.ToType)
  have hend (i : I) : B i + (c i).val =
      (x.normalFormTrunc (e i) + (x.coeff (e i) : Surreal) * ω^ (e i)).birthday.val := by
    rw [birthday_trunc_add_coeff_mul_wpow, NatOrdinal.val_of]
  have hwithin (i : I) (t : (c i).val.ToType) : B i + t.toOrd.1 < x.birthday.val := by
    apply ((Ordinal.isNormal_add_right (B i)).strictMono t.toOrd.2).trans_le
    rw [hend]
    exact NatOrdinal.val.monotone (birthday_trunc_add_coeff_wpow_le x (e i))
  have hsep {i j : I} (hij : i < j) : B i + (c i).val ≤ B j := by
    rw [hend]
    apply NatOrdinal.val.monotone
    apply birthday_trunc_add_coeff_wpow_le_trunc
    exact x.toHahnSeries.exp_strictAnti (Ordinal.ToType.mk.symm.strictMono hij)
  let f : W → x.birthday.val.ToType := fun z ↦ Ordinal.ToType.mk
    ⟨B (ofLex z).1 + (ofLex z).2.toOrd.1, hwithin (ofLex z).1 (ofLex z).2⟩
  have hf : StrictMono f := by
    rintro ⟨i, s⟩ ⟨j, t⟩ h
    change Sigma.Lex ((· < ·) : I → I → Prop)
      (fun i (a b : (c i).val.ToType) ↦ a < b) ⟨i, s⟩ ⟨j, t⟩ at h
    apply Ordinal.ToType.mk.strictMono
    change B i + s.toOrd.1 < B j + t.toOrd.1
    cases h with
    | left s t h =>
      exact ((Ordinal.isNormal_add_right (B i)).strictMono s.toOrd.2).trans_le
        ((hsep h).trans le_self_add)
    | right s t h =>
      exact (Ordinal.isNormal_add_right (B i)).strictMono (Ordinal.ToType.mk.symm.strictMono h)
  have hsurj : Function.Surjective f := by
    intro t
    have ht : NatOrdinal.of t.toOrd.1 < x.birthday :=
      NatOrdinal.val.lt_iff_lt.mp (by simpa only [NatOrdinal.val_of, Set.mem_Iio] using t.toOrd.2)
    obtain ⟨s, hs, hlo, hhi⟩ := exists_normalForm_birthday_interval ht
    let j : Iio x.toHahnSeries.length := x.toHahnSeries.exp.symm
      ⟨s, by simpa only [support_toHahnSeries] using hs⟩
    let i : I := Ordinal.ToType.mk j
    have hi : e i = s := by simp [e, i, j]
    have hlo' : B i ≤ t.toOrd.1 := by
      simpa only [B, hi, NatOrdinal.val_of] using NatOrdinal.val.monotone hlo
    have hhi' : t.toOrd.1 < B i + (c i).val := by
      rw [hend, hi]
      simpa only [NatOrdinal.val_of] using NatOrdinal.val.strictMono hhi
    let d := t.toOrd.1 - B i
    have hd : d < (c i).val := by
      apply (Ordinal.isNormal_add_right (B i)).strictMono.lt_iff_lt.mp
      dsimp only [d]
      rw [Ordinal.add_sub_cancel_of_le hlo']
      exact hhi'
    let v : (c i).val.ToType := Ordinal.ToType.mk ⟨d, hd⟩
    have hv : v.toOrd.1 = d := congrArg Subtype.val
      (OrderIso.symm_apply_apply (Ordinal.ToType.mk (o := (c i).val)) ⟨d, hd⟩)
    have hfval : (f (toLex ⟨i, v⟩)).toOrd.1 = B i + v.toOrd.1 := by
      dsimp only [f, Ordinal.ToType.toOrd]
      rw [OrderIso.symm_apply_apply]
      rfl
    refine ⟨toLex ⟨i, v⟩, ?_⟩
    apply Ordinal.ToType.mk.symm.injective
    apply Subtype.ext
    change (f (toLex ⟨i, v⟩)).toOrd.1 = t.toOrd.1
    rw [hfval, hv]
    exact Ordinal.add_sub_cancel_of_le hlo'
  refine ⟨OrderIso.ofSurjective (OrderEmbedding.ofStrictMono f hf) hsurj, ?_⟩
  intro i t
  change (f (toLex ⟨i, t⟩)).toOrd.1 = B i + t.toOrd.1
  dsimp only [f, Ordinal.ToType.toOrd]
  rw [OrderIso.symm_apply_apply]
  rfl

/-- The birthday of an arbitrary normal form is the ordered sum of its native term costs. -/
theorem birthday_eq_ordered_term_costs (x : Surreal.{u}) :
    x.birthday = NatOrdinal.of (typeLT (Σₗ i : x.toHahnSeries.length.ToType,
      (headCoefficientCost (x.normalFormTrunc (x.toHahnSeries.exp i.toOrd))
        (x.toHahnSeries.exp i.toOrd) (x.coeff (x.toHahnSeries.exp i.toOrd))).val.ToType)) := by
  obtain ⟨f, _⟩ := exists_orderIso_normalForm_birthday x
  have he := f.toRelIsoLT.ordinalType_congr
  rw [Ordinal.type_toType] at he
  exact (congrArg NatOrdinal.of he).symm

end Surreal


namespace Surreal
open Set
open scoped Ordinal

/-- A normal-form truncation has birthday equal to the ordered sum of its earlier term costs. -/
theorem birthday_trunc_eq_ordered_term_costs_before (x : Surreal.{u})
    (j : x.toHahnSeries.length.ToType) :
    (x.normalFormTrunc (x.toHahnSeries.exp j.toOrd)).birthday =
      NatOrdinal.of (typeLT (Σₗ i : Iio j,
        (headCoefficientCost (x.normalFormTrunc (x.toHahnSeries.exp i.1.toOrd))
          (x.toHahnSeries.exp i.1.toOrd)
          (x.coeff (x.toHahnSeries.exp i.1.toOrd))).val.ToType)) := by
  let c (i : x.toHahnSeries.length.ToType) :=
    headCoefficientCost (x.normalFormTrunc (x.toHahnSeries.exp i.toOrd))
      (x.toHahnSeries.exp i.toOrd) (x.coeff (x.toHahnSeries.exp i.toOrd))
  have hcoeff : x.coeff (x.toHahnSeries.exp j.toOrd) ≠ 0 := by
    apply mem_support_iff.mp
    simpa only [support_toHahnSeries] using (x.toHahnSeries.exp j.toOrd).2
  have hc : 0 < (c j).val := by
    have h : headOmegaCost (x.normalFormTrunc (x.toHahnSeries.exp j.toOrd))
        (x.toHahnSeries.exp j.toOrd) ≤ c j := by
      dsimp only [c]
      rw [headCoefficientCost_of_ne_zero _ _ hcoeff]
      exact NatOrdinal.of.monotone le_self_add
    exact NatOrdinal.val.strictMono
      ((zero_lt_one : (0 : NatOrdinal.{u}) < 1).trans_le ((one_le_headOmegaCost _ _).trans h))
  let z : (c j).val.ToType := Ordinal.ToType.mk ⟨0, hc⟩
  have hz : z.toOrd.1 = 0 := congrArg Subtype.val
    (OrderIso.symm_apply_apply (Ordinal.ToType.mk (o := (c j).val)) ⟨0, hc⟩)
  obtain ⟨f, hf⟩ := exists_orderIso_normalForm_birthday x
  have h := Ordinal.typein_apply f.toRelIsoLT.toInitialSeg (toLex ⟨j, z⟩)
  change Ordinal.typein ((· < ·) : x.birthday.val.ToType → _ → Prop)
      (f (toLex ⟨j, z⟩)) = _ at h
  rw [Ordinal.typein_toType_eq_toOrd, hf, Ordinal.typein_sigma,
    Ordinal.typein_toType_eq_toOrd, hz, add_zero, add_zero] at h
  exact congrArg NatOrdinal.of h

end Surreal
