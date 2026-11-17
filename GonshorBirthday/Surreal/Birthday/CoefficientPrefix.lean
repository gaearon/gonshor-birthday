/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Omega
public import GonshorBirthday.Surreal.Dyadic

import GonshorBirthday.Surreal.Birthday.Dyadic
import GonshorBirthday.Surreal.Birthday.Real

/-!
# Canonical real coefficient prefixes under monomial scaling

The scalar source is a real number. Finite numeric coefficient cuts are transported
through multiplication by an arbitrary surreal monomial.
-/

universe u
public noncomputable section
namespace IGame

private theorem mk_eq_real_toDyadic (g : IGame.{u}) [Short g] [Numeric g] :
    Surreal.mk g = Real.toSurreal g.toDyadic.toRat := by
  rw [Real.toSurreal_ratCast]
  exact (Surreal.ratCast_toDyadic g).symm

private theorem toDyadic_lt_real_iff (g : IGame.{u}) [Short g] [Numeric g] (s : ℝ) :
    (g.toDyadic.toRat : ℝ) < s ↔ g < (s : IGame) := by
  rw [← Surreal.mk_lt_mk, mk_eq_real_toDyadic g, Surreal.mk_real_toIGame]
  exact Real.toSurreal_lt_iff.symm

private theorem real_lt_toDyadic_iff (s : ℝ) (g : IGame.{u}) [Short g] [Numeric g] :
    s < (g.toDyadic.toRat : ℝ) ↔ (s : IGame) < g := by
  rw [← Surreal.mk_lt_mk, mk_eq_real_toDyadic g, Surreal.mk_real_toIGame]
  exact Real.toSurreal_lt_iff.symm

/-- Real fitting coefficients preserve fitting after arbitrary monomial scaling. -/
theorem Fits.real_mul_wpow {g x : IGame.{u}} [Short g] [Numeric g] [Numeric x]
    {s : ℝ} (h : Fits (s : IGame) g) : Fits ((s : IGame) * ω^ x) (g * ω^ x) := by
  have hfitL {a : IGame.{u}} [Short a] [Numeric a] (ha : a ∈ gᴸ) : (a.toDyadic.toRat : ℝ) < s := by
    numeric
    short
    apply (toDyadic_lt_real_iff a s).mpr
    rw [← Surreal.mk_lt_mk, lt_iff_not_ge, Surreal.mk_le_mk]
    exact h.1 a ha
  have hfitR {a : IGame.{u}} [Short a] [Numeric a] (ha : a ∈ gᴿ) : s < (a.toDyadic.toRat : ℝ) := by
    numeric
    short
    apply (real_lt_toDyadic_iff s a).mpr
    rw [← Surreal.mk_lt_mk, lt_iff_not_ge, Surreal.mk_le_mk]
    exact h.2 a ha
  constructor
  · rw [forall_moves_mul]
    rintro (_ | _) a ha b hb
    · numeric
      short
      have has := hfitL ha
      have hag : (a.toDyadic.toRat : ℝ) < (g.toDyadic.toRat : ℝ) := by
        apply Real.toSurreal_lt_iff.mp
        rw [← mk_eq_real_toDyadic a, ← mk_eq_real_toDyadic g]
        exact Surreal.mk_lt_mk.mpr (Numeric.left_lt ha)
      simp only [Player.mul_left] at hb
      rw [moves_left_wpow] at hb
      rcases hb with hb | ⟨r, hr, w, hw, rfl⟩
      · obtain rfl := Set.mem_singleton_iff.mp hb
        rw [← Surreal.mk_le_mk]
        apply not_le_of_gt
        have ht := mul_lt_mul_of_pos_right (Real.toSurreal_lt_iff.mpr has)
          (Surreal.wpow_pos (Surreal.mk x))
        simpa only [mulOption, Surreal.mk_add, Surreal.mk_sub, Surreal.mk_mul,
          Surreal.mk_wpow, Surreal.mk_real_toIGame, mk_eq_real_toDyadic a,
          Surreal.mk_zero, mul_zero, add_zero, sub_zero, Real.toSurreal_ratCast] using ht
      · numeric
        have hgap : 0 < s - (a.toDyadic.toRat : ℝ) := sub_pos.mpr has
        have ht := Surreal.mul_wpow_lt_mul_wpow_of_pos
          (((g.toDyadic.toRat : ℝ) - (a.toDyadic.toRat : ℝ)) * (r.toRat : ℝ)) hgap
          (Surreal.mk_lt_mk.mpr (Numeric.left_lt hw))
        rw [← Surreal.mk_le_mk]
        apply not_le_of_gt
        simp only [mulOption, Surreal.mk_add, Surreal.mk_sub, Surreal.mk_mul,
          Surreal.mk_wpow, Surreal.mk_real_toIGame, Surreal.mk_dyadic,
          mk_eq_real_toDyadic a, mk_eq_real_toDyadic g, Real.toSurreal_ratCast]
        simp only [Real.toSurreal_mul, Real.toSurreal_sub, Real.toSurreal_ratCast] at ht
        nlinarith only [ht]
    · numeric
      short
      have hga : (g.toDyadic.toRat : ℝ) < (a.toDyadic.toRat : ℝ) := by
        apply Real.toSurreal_lt_iff.mp
        rw [← mk_eq_real_toDyadic a, ← mk_eq_real_toDyadic g]
        exact Surreal.mk_lt_mk.mpr (Numeric.lt_right ha)
      simp only [Player.mul_left] at hb
      rw [moves_right_wpow] at hb
      obtain ⟨r, hr, w, hw, rfl⟩ := hb
      numeric
      have hrreal : (0 : ℝ) < r.toRat := by exact_mod_cast (show (0 : Dyadic) < r from hr)
      have hgap : 0 < ((a.toDyadic.toRat : ℝ) - (g.toDyadic.toRat : ℝ)) * r.toRat :=
        mul_pos (sub_pos.mpr hga) hrreal
      have ht := Surreal.mul_wpow_lt_mul_wpow_of_pos
        ((a.toDyadic.toRat : ℝ) - s) hgap (Surreal.mk_lt_mk.mpr (Numeric.lt_right hw))
      rw [← Surreal.mk_le_mk]
      apply not_le_of_gt
      simp only [mulOption, Surreal.mk_add, Surreal.mk_sub, Surreal.mk_mul,
        Surreal.mk_wpow, Surreal.mk_real_toIGame, Surreal.mk_dyadic,
        mk_eq_real_toDyadic a, mk_eq_real_toDyadic g, Real.toSurreal_ratCast]
      simp only [Real.toSurreal_mul, Real.toSurreal_sub, Real.toSurreal_ratCast] at ht
      nlinarith only [ht]
  · rw [forall_moves_mul]
    rintro (_ | _) a ha b hb
    · numeric
      short
      have hag : (a.toDyadic.toRat : ℝ) < (g.toDyadic.toRat : ℝ) := by
        apply Real.toSurreal_lt_iff.mp
        rw [← mk_eq_real_toDyadic a, ← mk_eq_real_toDyadic g]
        exact Surreal.mk_lt_mk.mpr (Numeric.left_lt ha)
      simp only [Player.mul_right, Player.neg_left] at hb
      rw [moves_right_wpow] at hb
      obtain ⟨r, hr, w, hw, rfl⟩ := hb
      numeric
      have hrreal : (0 : ℝ) < r.toRat := by exact_mod_cast (show (0 : Dyadic) < r from hr)
      have hgap : 0 < ((g.toDyadic.toRat : ℝ) - (a.toDyadic.toRat : ℝ)) * r.toRat :=
        mul_pos (sub_pos.mpr hag) hrreal
      have ht := Surreal.mul_wpow_lt_mul_wpow_of_pos
        (s - (a.toDyadic.toRat : ℝ)) hgap (Surreal.mk_lt_mk.mpr (Numeric.lt_right hw))
      rw [← Surreal.mk_le_mk]
      apply not_le_of_gt
      simp only [mulOption, Surreal.mk_add, Surreal.mk_sub, Surreal.mk_mul,
        Surreal.mk_wpow, Surreal.mk_real_toIGame, Surreal.mk_dyadic,
        mk_eq_real_toDyadic a, mk_eq_real_toDyadic g, Real.toSurreal_ratCast]
      simp only [Real.toSurreal_mul, Real.toSurreal_sub, Real.toSurreal_ratCast] at ht
      nlinarith only [ht]
    · numeric
      short
      have hsa := hfitR ha
      simp only [Player.mul_right, Player.neg_right] at hb
      rw [moves_left_wpow] at hb
      rcases hb with hb | ⟨r, hr, w, hw, rfl⟩
      · obtain rfl := Set.mem_singleton_iff.mp hb
        rw [← Surreal.mk_le_mk]
        apply not_le_of_gt
        have ht := mul_lt_mul_of_pos_right (Real.toSurreal_lt_iff.mpr hsa)
          (Surreal.wpow_pos (Surreal.mk x))
        simpa only [mulOption, Surreal.mk_add, Surreal.mk_sub, Surreal.mk_mul,
          Surreal.mk_wpow, Surreal.mk_real_toIGame, mk_eq_real_toDyadic a,
          Surreal.mk_zero, mul_zero, add_zero, sub_zero, Real.toSurreal_ratCast] using ht
      · numeric
        have hgap : 0 < (a.toDyadic.toRat : ℝ) - s := sub_pos.mpr hsa
        have ht := Surreal.mul_wpow_lt_mul_wpow_of_pos
          (((a.toDyadic.toRat : ℝ) - (g.toDyadic.toRat : ℝ)) * (r.toRat : ℝ)) hgap
          (Surreal.mk_lt_mk.mpr (Numeric.left_lt hw))
        rw [← Surreal.mk_le_mk]
        apply not_le_of_gt
        simp only [mulOption, Surreal.mk_add, Surreal.mk_sub, Surreal.mk_mul,
          Surreal.mk_wpow, Surreal.mk_real_toIGame, Surreal.mk_dyadic,
          mk_eq_real_toDyadic a, mk_eq_real_toDyadic g, Real.toSurreal_ratCast]
        simp only [Real.toSurreal_mul, Real.toSurreal_sub, Real.toSurreal_ratCast] at ht
        nlinarith only [ht]


end IGame

namespace Surreal
open IGame

/-- Monomial scaling preserves every dyadic canonical prefix of a real coefficient. -/
theorem birthdayTruncation_real_mul_wpow_of_dyadic_prefix {r : ℝ} {q : Dyadic}
    (h : birthdayTruncation (r : Surreal.{u}) (q : Surreal).birthday = (q : Surreal))
    (x : Surreal.{u}) : birthdayTruncation ((r : Surreal) * ω^ x)
      ((q : Surreal) * ω^ x).birthday = (q : Surreal) * ω^ x := by
  have hb : (q : Surreal.{u}).birthday ≤ (r : Surreal).birthday := by
    have ht := birthday_birthdayTruncation_le_birthday (r : Surreal.{u}) (q : Surreal).birthday
    rwa [h] at ht
  have hf : Fits (r : IGame.{u}) (q : IGame) := by
    constructor
    · intro a ha
      numeric
      have hba : (mk a).birthday < (q : Surreal.{u}).birthday := by
        have ht := (birthday_mk_le a).trans_lt (IGame.birthday_lt_of_mem_moves ha)
        rw [IGame.birthday_dyadic] at ht
        rw [Surreal.birthday_dyadic]
        exact ht
      have haq : mk a < (q : Surreal.{u}) := by
        simpa only [mk_dyadic] using mk_lt_mk.mpr (Numeric.left_lt ha)
      have har : mk a < (r : Surreal.{u}) :=
        (lt_birthdayTruncation_iff hb hba).mp (by rwa [h])
      rw [← mk_le_mk, mk_real_toIGame]
      exact har.not_ge
    · intro a ha
      numeric
      have hba : (mk a).birthday < (q : Surreal.{u}).birthday := by
        have ht := (birthday_mk_le a).trans_lt (IGame.birthday_lt_of_mem_moves ha)
        rw [IGame.birthday_dyadic] at ht
        rw [Surreal.birthday_dyadic]
        exact ht
      have hqa : (q : Surreal.{u}) < mk a := by
        simpa only [mk_dyadic] using mk_lt_mk.mpr (Numeric.lt_right ha)
      have hra : (r : Surreal.{u}) < mk a :=
        (birthdayTruncation_lt_iff hb hba).mp (by rwa [h])
      rw [← mk_le_mk, mk_real_toIGame]
      exact hra.not_ge
  have ht := (hf.real_mul_wpow (x := x.out)).birthdayTruncation_eq
  simpa only [mk_mul, mk_real_toIGame, mk_dyadic, mk_wpow, out_eq] using ht

/-- Monomial scaling preserves every actual canonical prefix of an embedded real coefficient. -/
theorem birthdayTruncation_real_mul_wpow_of_prefix {r : ℝ} {y : Surreal.{u}}
    (h : birthdayTruncation (r : Surreal) y.birthday = y) (x : Surreal.{u}) :
    birthdayTruncation ((r : Surreal) * ω^ x) (y * ω^ x).birthday = y * ω^ x := by
  have hb : y.birthday ≤ (r : Surreal.{u}).birthday := by
    have ht := birthday_birthdayTruncation_le_birthday (r : Surreal.{u}) y.birthday
    rwa [h] at ht
  obtain hlt | he := hb.lt_or_eq
  · obtain ⟨q, hq⟩ := birthdayTruncation_real_mem_range_dyadic r hlt
    rw [h] at hq
    rw [← hq] at h ⊢
    exact birthdayTruncation_real_mul_wpow_of_dyadic_prefix h x
  · have hy : y = (r : Surreal.{u}) := by
      rw [he, birthdayTruncation_birthday] at h
      exact h.symm
    rw [hy, birthdayTruncation_birthday]

/-- Every positive real monomial coefficient extends its coefficient-one monomial. -/
theorem birthdayTruncation_real_mul_wpow (r : ℝ) (hr : 0 < r) (x : Surreal.{u}) :
    birthdayTruncation ((r : Surreal) * ω^ x) (ω^ x).birthday = ω^ x := by
  have hf : Fits (r : IGame.{u}) 1 := by
    constructor
    · intro a ha
      have he : a = 0 := by simpa only [moves_left_one, Set.mem_singleton_iff] using ha
      subst a
      have hr' : (0 : IGame.{u}) < (r : IGame) := by exact_mod_cast hr
      exact hr'.not_ge
    · intro a ha
      simp only [moves_right_one, Set.mem_empty_iff_false] at ha
  have ht := (hf.real_mul_wpow (x := x.out)).birthdayTruncation_eq
  simpa only [mk_mul, mk_real_toIGame, mk_one, mk_wpow, out_eq, one_mul] using ht

end Surreal
