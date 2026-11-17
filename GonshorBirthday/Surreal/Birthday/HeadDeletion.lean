/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module
public import GonshorBirthday.Surreal.Birthday.Head
public import GonshorBirthday.Surreal.Birthday.SupportGap

/-!
# Earlier normal-form terms and exponent right-option domination

At a canonical right prefix w of a new exponent s, a higher head has a uniform
positive gap on scale omega^w exactly when all earlier exponents are at least w
and its real coefficient at w is dyadic. The two complementary mechanisms each
make the raw omega right options redundant against translated old head options.
This is an intrinsic cut criterion; no sign-word deletion equality is assumed.
-/

universe u
public noncomputable section
namespace Surreal
open Set

/-- An earlier normal-form exponent below an exponent right prefix supplies head
right options below every positive multiple of that prefix's monomial. -/
theorem exists_head_rightPrefix_small_gap_of_support_lt
    {H s v w : Surreal.{u}} (hH : H.support ⊆ Ioi s) (hv : v ∈ H.support)
    (hvw : v < w) (hw : w ∈ rightPrefixes s) {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ rightPrefixes H, p - H < (ε : Surreal) * ω^ w := by
  have hwv : w ∈ rightPrefixes v := by
    apply mem_rightPrefixes_iff.mpr
    refine ⟨?_, hvw⟩
    have ht := birthdayTruncation_eq_of_right_between
      (birthday_lt_of_mem_rightPrefixes hw).le (hH hv).le
      (by simpa only [(mem_rightPrefixes_iff.mp hw).1] using hvw.le)
    simpa only [(mem_rightPrefixes_iff.mp hw).1] using ht
  exact exists_rightPrefix_sub_lt_real_mul_wpow_of_support hv hwv hε

/-- A lower earlier normal-form exponent makes each raw omega right option redundant
against a translated old head right option. -/
theorem exists_head_rightPrefix_add_wpow_lt_of_support_lt
    {H s v w : Surreal.{u}} (hH : H.support ⊆ Ioi s) (hv : v ∈ H.support)
    (hvw : v < w) (hw : w ∈ rightPrefixes s) {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ rightPrefixes H, p + ω^ s < H + (ε : Surreal) * ω^ w := by
  obtain ⟨p, hp, hgap⟩ := exists_head_rightPrefix_small_gap_of_support_lt hH hv hvw hw
    (half_pos hε)
  have hsmall := wpow_lt_mul_wpow (half_pos hε) (mem_rightPrefixes_iff.mp hw).2
  have hcast : ((ε / 2 : ℝ) : Surreal.{u}) = (ε : Surreal) / 2 := by
    push_cast
    norm_num
  rw [hcast] at hgap hsmall
  refine ⟨p, hp, ?_⟩
  linarith

/-- A nondyadic earlier coefficient at the boundary scale supplies head right options
below every positive multiple of that scale. -/
theorem exists_head_rightPrefix_small_gap_of_coeff_birthday_omega0
    {H w : Surreal.{u}} (hH : H.support ⊆ Ici w)
    (hc : (H.coeff w : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ rightPrefixes H, p - H < (ε : Surreal) * ω^ w := by
  have hK : (H.normalFormTrunc w).support ⊆ Ioi w := by
    simp only [support_trunc]
    exact inter_subset_right
  obtain ⟨r, hr, hrt⟩ := exists_head_real_mul_wpow_rightPrefix_lt (H.normalFormTrunc w) w hK hc
    (lt_add_of_pos_right (H.coeff w) hε)
  have hdecomp := eq_trunc_add_coeff_wpow_of_support_ge hH
  refine ⟨H.normalFormTrunc w + (r : Surreal) * ω^ w, ?_, ?_⟩
  · simpa only [← hdecomp] using hr
  have hlt : (r : Surreal.{u}) < (H.coeff w : Surreal) + (ε : Surreal) := by
    simpa only [Real.toSurreal_add] using Real.toSurreal_lt_iff.mpr hrt
  have hm := mul_lt_mul_of_pos_right hlt (wpow_pos w)
  rw [add_mul] at hm
  linarith

/-- A nondyadic coefficient at an earlier boundary scale makes each raw omega
right option redundant against a translated old head right option. -/
theorem exists_head_rightPrefix_add_wpow_lt_of_coeff_birthday_omega0
    {H s w : Surreal.{u}} (hH : H.support ⊆ Ici w) (hsw : s < w)
    (hc : (H.coeff w : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ rightPrefixes H, p + ω^ s < H + (ε : Surreal) * ω^ w := by
  obtain ⟨p, hp, hgap⟩ := exists_head_rightPrefix_small_gap_of_coeff_birthday_omega0 hH hc
    (half_pos hε)
  have hsmall := wpow_lt_mul_wpow (half_pos hε) hsw
  have hcast : ((ε / 2 : ℝ) : Surreal.{u}) = (ε : Surreal) / 2 := by
    push_cast
    norm_num
  rw [hcast] at hgap hsmall
  refine ⟨p, hp, ?_⟩
  linarith

/-- A dyadic boundary coefficient leaves a uniform positive monomial gap to all old
head right options. The statement includes a zero boundary coefficient. -/
theorem exists_uniform_head_rightPrefix_gap_of_coeff_birthday_lt_omega0
    {H w : Surreal.{u}} (hH : H.support ⊆ Ici w)
    (hc : (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ rightPrefixes H, (ε : Surreal) * ω^ w < p - H := by
  have hnext : (appendPlus (H.coeff w : Surreal.{u})).birthday <
      NatOrdinal.of Ordinal.omega0 := by
    rw [birthday_appendPlus]
    obtain ⟨n, hn⟩ := NatOrdinal.lt_omega0.mp hc
    rw [hn]
    exact_mod_cast NatOrdinal.natCast_lt_omega0 (n + 1)
  obtain ⟨q, hq⟩ := birthday_lt_omega0_iff.mp hnext
  let r : ℝ := q.toRat
  have hr : (r : Surreal.{u}) = appendPlus (H.coeff w : Surreal.{u}) := by
    simpa only [r, Real.toSurreal_ratCast] using hq
  have hlt : H.coeff w < r := by
    apply Real.toSurreal_lt_iff.mp
    rw [hr]
    exact lt_appendPlus _
  have hK : (H.normalFormTrunc w).support ⊆ Ioi w := by
    simp only [support_trunc]
    exact inter_subset_right
  have hpre := birthdayTruncation_head_real_mul_wpow_of_prefix (H.normalFormTrunc w) w hK
    (show birthdayTruncation (r : Surreal) (H.coeff w : Surreal).birthday =
      (H.coeff w : Surreal) by rw [hr]; exact birthdayTruncation_appendPlus _)
  have hdecomp := eq_trunc_add_coeff_wpow_of_support_ge hH
  rw [← hdecomp] at hpre
  refine ⟨r - H.coeff w, sub_pos.mpr hlt, ?_⟩
  intro p hp
  have hpp := (mem_rightPrefixes_iff.mp
    (rightPrefixes_subset_of_birthdayTruncation_eq hpre hp)).2
  rw [Real.toSurreal_sub, sub_mul]
  linarith

/-- At a right exponent prefix, a higher normal-form head has a uniform old-right
option gap precisely when no earlier exponent lies below the boundary and the
boundary coefficient is dyadic. -/
theorem exists_uniform_head_rightPrefix_gap_iff
    {H s w : Surreal.{u}} (hH : H.support ⊆ Ioi s) (hw : w ∈ rightPrefixes s) :
    (∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ rightPrefixes H, (ε : Surreal) * ω^ w < p - H) ↔
      H.support ⊆ Ici w ∧
        (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 := by
  constructor
  · rintro ⟨ε, hε, hgap⟩
    have hge : H.support ⊆ Ici w := by
      intro v hv
      by_contra hn
      obtain ⟨p, hp, hsmall⟩ := exists_head_rightPrefix_small_gap_of_support_lt hH hv
        (lt_of_not_ge hn) hw hε
      exact (hgap p hp).not_ge hsmall.le
    refine ⟨hge, ?_⟩
    by_contra hn
    have hc := le_antisymm (birthday_real_le_omega0 (H.coeff w)) (le_of_not_gt hn)
    obtain ⟨p, hp, hsmall⟩ := exists_head_rightPrefix_small_gap_of_coeff_birthday_omega0
      hge hc hε
    exact (hgap p hp).not_ge hsmall.le
  · rintro ⟨hge, hc⟩
    exact exists_uniform_head_rightPrefix_gap_of_coeff_birthday_lt_omega0 hge hc

end Surreal
