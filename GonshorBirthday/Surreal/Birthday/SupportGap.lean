/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.HahnSeries.BirthdayGap

import GonshorBirthday.Surreal.Birthday.HeadMidpoint
import Mathlib.Order.Minimal

/-!
# Canonical right-prefix gaps at normal-form support scales

A right prefix of any supported exponent supplies arbitrarily small real multiples
of its monomial as upper bounds for actual right-prefix gaps of the entire surreal.
The proof uses the first supported exponent strictly below that prefix and the
canonical-prefix property of normal-form partial sums. All real coefficients,
coefficient signs, and support lengths are allowed.

If the support has no least exponent, right-prefix gaps consequently occur below
every supported scale. No general normal-form sign-deletion theorem is used.
-/

universe u
public noncomputable section
namespace Surreal
open Set

private theorem exists_rightPrefix_le_of_no_min_set
    {S : Set Surreal.{u}} (hS : ∀ x ∈ S, ∃ y ∈ S, y < x)
    {s : Surreal.{u}} (hs : s ∈ S) :
    ∃ x ∈ S, x < s ∧ ∃ v ∈ rightPrefixes x, v ≤ s := by
  obtain ⟨x, hx, hxs⟩ := hS s hs
  obtain ⟨x, hx, hmin⟩ := exists_minimalFor_of_wellFoundedLT
    (fun x : Surreal.{u} ↦ x ∈ S ∧ x < s) birthday ⟨x, hx, hxs⟩
  obtain ⟨y, hy, hyx⟩ := hS x hx.1
  refine ⟨y, hy, hyx.trans hx.2, ?_⟩
  by_contra hn
  have hpre : birthdayTruncation s y.birthday = y := by
    have hp := birthdayTruncation_eq_of_btwn (H := leftPrefixes_lt_rightPrefixes y)
      (fun z hz ↦ (mem_leftPrefixes_iff.mp hz).2.trans (hyx.trans hx.2))
      (fun z hz ↦ lt_of_not_ge (fun hzs ↦ hn ⟨z, hz, hzs⟩))
    simpa only [ofSets_leftPrefixes_rightPrefixes] using hp
  have hpy : y.birthday ≤ s.birthday := by
    have h := birthday_birthdayTruncation_le_birthday s y.birthday
    rwa [hpre] at h
  have hbetween : birthdayTruncation x y.birthday = y := by
    have h := birthdayTruncation_eq_of_left_between hpy
      (by simpa only [hpre] using hyx.le) hx.2.le
    simpa only [hpre] using h
  have hbyx : y.birthday < x.birthday :=
    birthday_lt_of_mem_leftPrefixes (mem_leftPrefixes_iff.mpr ⟨hbetween, hyx⟩)
  exact hbyx.not_ge (hmin ⟨hy, hyx.trans hx.2⟩ hbyx.le)

/-- A set without a least element has a member with a right prefix below any given member. -/
theorem exists_rightPrefix_lt_of_no_min_set
    {S : Set Surreal.{u}} (hS : ∀ x ∈ S, ∃ y ∈ S, y < x)
    {s : Surreal.{u}} (hs : s ∈ S) :
    ∃ x ∈ S, ∃ v ∈ rightPrefixes x, v < s := by
  obtain ⟨t, ht, hts⟩ := hS s hs
  obtain ⟨x, hx, _, v, hv, hvt⟩ := exists_rightPrefix_le_of_no_min_set hS ht
  exact ⟨x, hx, v, hv, hvt.trans_lt hts⟩

/-- A normal-form truncation together with the term at its cutoff is a canonical prefix. -/
theorem birthdayTruncation_trunc_add_coeff_wpow (x s : Surreal.{u}) :
    birthdayTruncation x (x.normalFormTrunc s + (x.coeff s : Surreal) * ω^ s).birthday =
      x.normalFormTrunc s + (x.coeff s : Surreal) * ω^ s := by
  by_cases hs : s ∈ x.support
  · let i := x.toHahnSeries.exp.symm ⟨s, by simpa only [support_toHahnSeries] using hs⟩
    have he : (x.toHahnSeries.exp i).1 = s := by simp [i]
    have hc : x.toHahnSeries.coeffIdx i = x.coeff s := by simp [i]
    have h := x.toHahnSeries.birthdayTruncation_truncIdx (i.val + 1)
    rw [SurrealHahnSeries.truncIdx_add_one i.2,
      SurrealHahnSeries.truncIdx_of_lt i.2, he, hc,
      SurrealHahnSeries.toSurreal_add, SurrealHahnSeries.toSurreal_single] at h
    simpa only [toSurreal_toHahnSeries, SurrealHahnSeries.toSurreal_trunc] using h
  · simpa only [notMem_support_iff.mp hs, Real.toSurreal_zero, zero_mul, add_zero] using
      birthdayTruncation_trunc x s

private theorem rightPrefix_of_between {v w u : Surreal.{u}}
    (hu : u ∈ rightPrefixes v) (hvw : v ≤ w) (hwu : w < u) :
    u ∈ rightPrefixes w := by
  apply mem_rightPrefixes_iff.mpr
  refine ⟨?_, hwu⟩
  have h := birthdayTruncation_eq_of_right_between
    (birthday_lt_of_mem_rightPrefixes hu).le hvw
    (by simpa only [(mem_rightPrefixes_iff.mp hu).1] using hwu.le)
  simpa only [(mem_rightPrefixes_iff.mp hu).1] using h

/-- Across an interval containing no supported exponent, truncation changes by exactly
the coefficient at its upper boundary. -/
theorem trunc_eq_trunc_add_coeff_of_no_support_between {x w u : Surreal.{u}}
    (hwu : w < u) (hgap : ∀ j ∈ x.support, j < u → j ≤ w) :
    x.normalFormTrunc w = x.normalFormTrunc u + (x.coeff u : Surreal) * ω^ u := by
  apply toHahnSeries_inj.mp
  rw [toHahnSeries_trunc, toHahnSeries_add, toHahnSeries_trunc]
  rw [← SurrealHahnSeries.toSurreal_single, SurrealHahnSeries.toHahnSeries_toSurreal]
  ext j
  by_cases hju : j = u
  · subst j
    simp [hwu]
  · by_cases hj : u < j
    · simp [SurrealHahnSeries.coeff_trunc_of_lt hj,
        SurrealHahnSeries.coeff_trunc_of_lt (hwu.trans hj),
        SurrealHahnSeries.coeff_add, SurrealHahnSeries.coeff_single, hju]
    · have hju' : j < u := lt_of_le_of_ne (le_of_not_gt hj) hju
      have hz : w < j → x.coeff j = 0 := by
        intro hwj
        by_contra hn
        exact hwj.not_ge (hgap j (mem_support_iff.mpr hn) hju')
      simp only [SurrealHahnSeries.coeff_add, Pi.add_apply,
        SurrealHahnSeries.coeff_trunc, SurrealHahnSeries.coeff_single,
        Pi.single_eq_of_ne hju, ite_eq_right hj, zero_add]
      split_ifs with hwj
      · simpa only [coeff_toHahnSeries] using hz hwj
      · rfl

/-- Supported exponent right prefixes give small gaps witnessed inside a normal-form truncation. -/
theorem exists_truncation_rightPrefix_sub_lt_real_mul_wpow_of_support
    {z v u : Surreal.{u}} (hv : v ∈ z.support) (hu : u ∈ rightPrefixes v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w ∈ z.support, ∃ p ∈ rightPrefixes (z.normalFormTrunc w + (z.coeff w : Surreal) * ω^ w),
      p ∈ rightPrefixes z ∧ p - z < (ε : Surreal) * ω^ u := by
  have hne : {w : z.support | (w : Surreal) < u}.Nonempty :=
    ⟨⟨v, hv⟩, (mem_rightPrefixes_iff.mp hu).2⟩
  obtain ⟨w, hwu, hmax⟩ := wellFounded_gt.has_min _ hne
  have hgap : ∀ j ∈ z.support, j < u → j ≤ w := by
    intro j hj hju
    exact le_of_not_gt (hmax ⟨j, hj⟩ hju)
  have huw : u ∈ rightPrefixes (w : Surreal) :=
    rightPrefix_of_between hu (hgap v hv (mem_rightPrefixes_iff.mp hu).2) hwu
  have hK : (z.normalFormTrunc u).support ⊆ Ioi u := by
    simp only [support_trunc]
    exact inter_subset_right
  have hH : (z.normalFormTrunc w).support ⊆ Ioi (w : Surreal) := by
    simp only [support_trunc]; exact inter_subset_right
  have ht : z.coeff w ≠ 0 := mem_support_iff.mp w.2
  have hlead : ((z.coeff w : Surreal) * ω^ (w : Surreal)).wlog = w := by
    rw [wlog_mul (by exact_mod_cast ht) (wpow_ne_zero _),
      wlog_realCast, wlog_wpow, zero_add]
  have hpre := birthdayTruncation_trunc_add_coeff_wpow z (w : Surreal)
  have hhead : birthdayTruncation
      (z.normalFormTrunc w + (z.coeff w : Surreal) * ω^ (w : Surreal))
        (z.normalFormTrunc w).birthday =
      z.normalFormTrunc w := by
    apply birthdayTruncation_add_of_support_lt
    rwa [hlead]
  obtain htneg | htpos := lt_or_gt_of_ne ht
  · have hRt : z.normalFormTrunc w ∈
        rightPrefixes (z.normalFormTrunc w + (z.coeff w : Surreal) * ω^ (w : Surreal)) := by
      apply mem_rightPrefixes_iff.mpr
      refine ⟨hhead, ?_⟩
      exact add_lt_of_neg_right _
        (mul_neg_of_neg_of_pos (by exact_mod_cast htneg) (wpow_pos _))
    have hR : z.normalFormTrunc w ∈ rightPrefixes z :=
      rightPrefixes_subset_of_birthdayTruncation_eq hpre hRt
    have hpos : 0 < z.normalFormTrunc w - z := sub_pos.mpr (mem_rightPrefixes_iff.mp hR).2
    have hscale : (z.normalFormTrunc w - z).wlog ≤ w := by
      have hh : z.normalFormTrunc w - z ≤ᵥ ω^ (w : Surreal) := by
        rw [← neg_sub z (z.normalFormTrunc w), neg_vle]
        exact sub_trunc_vle_wpow z w
      simpa only [wlog_wpow] using wlog_le_wlog_of_vle hpos.ne' hh
    have htarget : 0 < (ε : Surreal.{u}) * ω^ u :=
      mul_pos (Real.toSurreal_pos_iff.mpr hε) (wpow_pos _)
    have hsmall : z.normalFormTrunc w - z <ᵥ (ε : Surreal) * ω^ u := by
      rw [← wlog_lt_wlog_iff hpos.ne' htarget.ne',
        wlog_mul (Real.toSurreal_pos_iff.mpr hε).ne' (wpow_ne_zero _),
        wlog_realCast, wlog_wpow, zero_add]
      exact hscale.trans_lt hwu
    exact ⟨w, w.2, z.normalFormTrunc w, hRt, hR,
      ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg (vlt_def.mp hsmall) htarget.le⟩
  · have hL : z.normalFormTrunc w ∈ leftPrefixes z := by
      apply leftPrefixes_subset_of_birthdayTruncation_eq hpre
      apply mem_leftPrefixes_iff.mpr
      refine ⟨hhead, ?_⟩
      exact lt_add_of_pos_right _
        (mul_pos (Real.toSurreal_pos_iff.mpr htpos) (wpow_pos _))
    have hdecomp := trunc_eq_trunc_add_coeff_of_no_support_between hwu hgap
    obtain ⟨q, hqa, hqε, hqp⟩ := exists_head_real_mul_wpow_rightPrefix_lt_add
      (z.normalFormTrunc u) u hK (z.coeff u) htpos huw hε
    have hRt : z.normalFormTrunc u + (q : Surreal) * ω^ u ∈
        rightPrefixes (z.normalFormTrunc w + (z.coeff w : Surreal) * ω^ (w : Surreal)) := by
      simpa only [hdecomp, add_assoc] using hqp
    have hR : z.normalFormTrunc u + (q : Surreal) * ω^ u ∈ rightPrefixes z :=
      rightPrefixes_subset_of_birthdayTruncation_eq hpre hRt
    refine ⟨w, w.2, z.normalFormTrunc u + (q : Surreal) * ω^ u, hRt, hR, ?_⟩
    have hdiff : z.normalFormTrunc u + (q : Surreal) * ω^ u - z.normalFormTrunc w <
        (ε : Surreal) * ω^ u := by
      rw [hdecomp, add_sub_add_left_eq_sub, ← sub_mul]
      apply mul_lt_mul_of_pos_right _ (wpow_pos _)
      have hqr : q - z.coeff u < ε := by linarith only [hqε]
      rw [← Real.toSurreal_sub]
      exact Real.toSurreal_lt_iff.mpr hqr
    exact (sub_lt_sub_left (mem_leftPrefixes_iff.mp hL).2 _).trans hdiff

/-- A right prefix of a supported exponent bounds arbitrarily small actual right-prefix gaps. -/
theorem exists_rightPrefix_sub_lt_real_mul_wpow_of_support
    {z v u : Surreal.{u}} (hv : v ∈ z.support) (hu : u ∈ rightPrefixes v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ rightPrefixes z, p - z < (ε : Surreal) * ω^ u := by
  obtain ⟨_, _, p, _, hp, hgap⟩ :=
    exists_truncation_rightPrefix_sub_lt_real_mul_wpow_of_support hv hu hε
  exact ⟨p, hp, hgap⟩

/-- A support without a least exponent has right-prefix gaps below every supported scale. -/
theorem exists_rightPrefix_small_gap_of_no_min_support
    {z : Surreal.{u}} (hz : ∀ s ∈ z.support, ∃ t ∈ z.support, t < s)
    {s : Surreal.{u}} (hs : s ∈ z.support) :
    ∃ p ∈ rightPrefixes z, (p - z).wlog < s := by
  obtain ⟨v, hv, u, hu, hus⟩ := exists_rightPrefix_lt_of_no_min_set hz hs
  obtain ⟨p, hp, hgap⟩ := exists_rightPrefix_sub_lt_real_mul_wpow_of_support
    hv hu (show (0 : ℝ) < 1 by norm_num)
  have hpos : 0 < p - z := sub_pos.mpr (mem_rightPrefixes_iff.mp hp).2
  have hsmall : (p - z).wlog ≤ u := by
    have hle : p - z ≤ ω^ u := by simpa only [Real.toSurreal_one, one_mul] using hgap.le
    simpa only [wlog_wpow] using wlog_monotoneOn hpos (wpow_pos u) hle
  exact ⟨p, hp, hsmall.trans_lt hus⟩

/-- A lower bound for the support splits off the last possible normal-form term. -/
theorem eq_trunc_add_coeff_wpow_of_support_ge {x s : Surreal.{u}}
    (hs : x.support ⊆ Ici s) : x = x.normalFormTrunc s + (x.coeff s : Surreal) * ω^ s := by
  have hcut : s - 1 < s := sub_lt_self _ zero_lt_one
  have htr : x.normalFormTrunc (s - 1) = x := trunc_eq_self (fun j hj ↦ hcut.trans_le (hs hj))
  have hgap : ∀ j ∈ x.support, j < s → j ≤ s - 1 :=
    fun j hj hjs ↦ (hjs.not_ge (hs hj)).elim
  simpa only [htr] using trunc_eq_trunc_add_coeff_of_no_support_between hcut hgap

end Surreal
