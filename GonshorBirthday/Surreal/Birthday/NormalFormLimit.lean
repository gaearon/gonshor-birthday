/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.SupportGap

/-!
# Birthday cofinality of normal-form truncations

If a normal form has no last term, every proper canonical prefix is younger than
some proper normal-form truncation. Its birthday is therefore the supremum of
the truncation birthdays. This includes the empty support and arbitrary limit
lengths. The proof keeps the truncation witnesses in the supported-scale gap
construction and applies the same argument after negation for left prefixes.
-/

universe u
public noncomputable section
namespace Surreal
open Set

private theorem trunc_neg' (x s : Surreal.{u}) :
    (-x).normalFormTrunc s = -(x.normalFormTrunc s) := by
  apply toHahnSeries_inj.mp
  rw [toHahnSeries_trunc, toHahnSeries_neg, SurrealHahnSeries.trunc_neg,
    toHahnSeries_neg, toHahnSeries_trunc]

private theorem trunc_trunc' (x s t : Surreal.{u}) :
    (x.normalFormTrunc s).normalFormTrunc t = x.normalFormTrunc (max s t) := by
  apply toHahnSeries_inj.mp
  rw [toHahnSeries_trunc, toHahnSeries_trunc, SurrealHahnSeries.trunc_trunc,
    toHahnSeries_trunc]

private theorem birthday_trunc_add_coeff_wpow_le_trunc {x s t : Surreal.{u}} (hts : t < s) :
    (x.normalFormTrunc s + (x.coeff s : Surreal) * ω^ s).birthday ≤
      (x.normalFormTrunc t).birthday := by
  have hp := birthdayTruncation_trunc_add_coeff_wpow (x.normalFormTrunc t) s
  rw [trunc_trunc', max_eq_right hts.le, coeff_trunc_of_lt hts] at hp
  have hb := birthday_birthdayTruncation_le_birthday (x.normalFormTrunc t)
    (x.normalFormTrunc s + (x.coeff s : Surreal) * ω^ s).birthday
  rwa [hp] at hb

/-- Every right prefix of a series without a last term is younger than a proper truncation. -/
theorem exists_trunc_birthday_gt_of_mem_rightPrefixes_of_no_min_support
    {x p : Surreal.{u}} (hs : ∀ s ∈ x.support, ∃ t ∈ x.support, t < s)
    (hp : p ∈ rightPrefixes x) : ∃ t ∈ x.support, p.birthday < (x.normalFormTrunc t).birthday := by
  obtain ⟨s, hsx, hsp⟩ := exists_support_le_wlog_sub_of_birthday_lt
    (birthday_lt_of_mem_rightPrefixes hp)
  obtain ⟨v, hv, u, hu, hus⟩ := exists_rightPrefix_lt_of_no_min_set hs hsx
  obtain ⟨w, hw, q, hqt, hq, hgap⟩ :=
    exists_truncation_rightPrefix_sub_lt_real_mul_wpow_of_support hv hu
      (show (0 : ℝ) < 1 by norm_num)
  have hqpos : 0 < q - x := sub_pos.mpr (mem_rightPrefixes_iff.mp hq).2
  have hppos : 0 < p - x := sub_pos.mpr (mem_rightPrefixes_iff.mp hp).2
  have hqu : (q - x).wlog ≤ u := by
    have hle : q - x ≤ ω^ u := by simpa only [Real.toSurreal_one, one_mul] using hgap.le
    simpa only [wlog_wpow] using wlog_monotoneOn hqpos (wpow_pos u) hle
  have hsmall : q - x <ᵥ p - x := by
    rw [← wlog_lt_wlog_iff hqpos.ne' hppos.ne']
    exact hqu.trans_lt (hus.trans_le hsp)
  have hqp : q < p := sub_lt_sub_iff_right x |>.mp
    (ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg (vlt_def.mp hsmall) hppos.le)
  have hpb : p.birthday ≤ q.birthday := by
    simpa only [birthday_neg] using birthday_le_of_left_between
      (neg_mem_leftPrefixes_iff.mpr hp) (neg_le_neg hqp.le)
      (neg_le_neg (mem_rightPrefixes_iff.mp hq).2.le)
  obtain ⟨t, ht, htw⟩ := hs w hw
  exact ⟨t, ht, hpb.trans_lt ((birthday_lt_of_mem_rightPrefixes hqt).trans_le
    (birthday_trunc_add_coeff_wpow_le_trunc htw))⟩

/-- Proper normal-form truncation birthdays are cofinal when the support has no least exponent. -/
theorem exists_trunc_birthday_gt_of_birthday_lt_of_no_min_support
    {x : Surreal.{u}} (hs : ∀ s ∈ x.support, ∃ t ∈ x.support, t < s)
    {a : NatOrdinal.{u}} (ha : a < x.birthday) :
    ∃ t ∈ x.support, a < (x.normalFormTrunc t).birthday := by
  have hb := birthday_birthdayTruncation x ha.le
  have hne : birthdayTruncation x a ≠ x := by
    intro he
    exact ha.ne (hb.symm.trans (congrArg birthday he))
  obtain hl | hr := lt_or_gt_of_ne hne
  · have hsup : (-x).support = x.support := by
      rw [← support_coeff, ← support_coeff, coeff_neg, Function.support_neg]
    have hsneg : ∀ s ∈ (-x).support, ∃ t ∈ (-x).support, t < s := by
      simpa only [hsup] using hs
    have hp : -(birthdayTruncation x a) ∈ rightPrefixes (-x) :=
      neg_mem_rightPrefixes_iff.mpr (mem_leftPrefixes.mpr ⟨a, ha, rfl, hl⟩)
    obtain ⟨t, ht, htb⟩ :=
      exists_trunc_birthday_gt_of_mem_rightPrefixes_of_no_min_support hsneg hp
    refine ⟨t, hsup ▸ ht, ?_⟩
    simpa only [birthday_neg, trunc_neg', hb] using htb
  · obtain ⟨t, ht, htb⟩ :=
      exists_trunc_birthday_gt_of_mem_rightPrefixes_of_no_min_support hs
        (mem_rightPrefixes.mpr ⟨a, ha, rfl, hr⟩)
    exact ⟨t, ht, by simpa only [hb] using htb⟩

/-- Bounding proper truncations bounds a whole series without a last term. -/
theorem birthday_le_iff_trunc_of_no_min_support (x : Surreal.{u})
    (hs : ∀ s ∈ x.support, ∃ t ∈ x.support, t < s) (B : NatOrdinal.{u}) :
    x.birthday ≤ B ↔ ∀ s ∈ x.support, (x.normalFormTrunc s).birthday ≤ B := by
  constructor
  · exact fun h s _ ↦ (birthday_normalFormTrunc_le x s).trans h
  · intro h
    by_contra hn
    obtain ⟨s, hs, hsb⟩ :=
      exists_trunc_birthday_gt_of_birthday_lt_of_no_min_support hs (lt_of_not_ge hn)
    exact hsb.not_ge (h s hs)

end Surreal

namespace SurrealHahnSeries
open Set Order

/-- A zero or limit normal-form length has no least supported exponent. -/
theorem no_min_support_toSurreal_of_isSuccPrelimit (x : SurrealHahnSeries.{u})
    (hx : IsSuccPrelimit x.length) :
    ∀ s ∈ x.toSurreal.support, ∃ t ∈ x.toSurreal.support, t < s := by
  intro s hs
  rw [support_toSurreal] at hs
  obtain ⟨i, rfl⟩ := eq_exp_of_mem_support hs
  have hi : i.val + 1 < x.length := hx.succ_lt i.2
  let j : Iio x.length := ⟨i.val + 1, hi⟩
  refine ⟨x.exp j, ?_, ?_⟩
  · rw [support_toSurreal]
    exact (x.exp j).2
  · exact x.exp_strictAnti (show i < j from lt_add_one i.val)

/-- At a zero or limit support length, birthday bounds are determined by proper truncations. -/
theorem birthday_le_iff_truncIdx_of_isSuccPrelimit (x : SurrealHahnSeries.{u})
    (hx : IsSuccPrelimit x.length) (B : NatOrdinal.{u}) :
    x.toSurreal.birthday ≤ B ↔
      ∀ i < x.length, (x.truncIdx i).toSurreal.birthday ≤ B := by
  constructor
  · exact fun h i _ ↦ (birthday_truncIdx_le x i).trans h
  · intro h
    apply (Surreal.birthday_le_iff_trunc_of_no_min_support x.toSurreal
      (no_min_support_toSurreal_of_isSuccPrelimit x hx) B).mpr
    intro s hs
    rw [support_toSurreal] at hs
    obtain ⟨i, rfl⟩ := eq_exp_of_mem_support hs
    simpa only [truncIdx_of_lt i.2, toSurreal_trunc] using h i i.2

end SurrealHahnSeries
