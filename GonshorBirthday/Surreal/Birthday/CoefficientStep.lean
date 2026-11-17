/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Append
public import GonshorBirthday.Surreal.Dyadic
public import CombinatorialGames.Surreal.Real

import GonshorBirthday.Surreal.Birthday.Dyadic
import GonshorBirthday.Surreal.Birthday.LastMinusFamily
import GonshorBirthday.Surreal.Birthday.Real

/-!
# Bounds on a final dyadic coefficient step

If a real coefficient is the canonical minus successor of another real,
it is dyadic and the step has size at most one. The bound follows from
the native dyadic game's right move and intrinsic canonical minimality.
-/

universe u
public noncomputable section
namespace Surreal
open IGame

/-- The final minus of a dyadic surreal changes its value by at most one. -/
theorem sub_le_one_of_eq_appendMinus_dyadic (q : Dyadic) {p : Surreal.{u}}
    (hsrc : (q : Surreal.{u}) = appendMinus p) : p - (q : Surreal) ≤ 1 := by
  have hqp : (q : Surreal.{u}) < p := by
    rw [hsrc]
    exact appendMinus_lt p
  have hbp : p.birthday < (q : Surreal.{u}).birthday := by
    rw [hsrc, birthday_appendMinus]
    exact lt_add_one _
  have hnon : ∃ g : IGame.{u}, g ∈ (q : IGame)ᴿ := by
    by_contra hn
    push Not at hn
    have hf : Fits p.out (q : IGame.{u}) := by
      constructor
      · intro g hg
        numeric
        have hgq : mk g < (q : Surreal.{u}) := by
          simpa only [mk_dyadic] using mk_lt_mk.mpr (Numeric.left_lt hg)
        rw [← mk_le_mk, out_eq]
        exact (hgq.trans hqp).not_ge
      · exact fun g hg ↦ (hn g hg).elim
    have hp := hf.birthdayTruncation_eq
    rw [out_eq, mk_dyadic] at hp
    have hb := birthday_birthdayTruncation_le_birthday p (q : Surreal.{u}).birthday
    rw [hp] at hb
    exact hbp.not_ge hb
  obtain ⟨g, hg⟩ := hnon
  have : Numeric g := Numeric.of_mem_moves hg
  have hbg : (mk g).birthday < (q : Surreal.{u}).birthday := by
    have hb := (birthday_mk_le g).trans_lt (IGame.birthday_lt_of_mem_moves hg)
    rw [IGame.birthday_dyadic, Surreal.birthday_dyadic] at *
    exact hb
  have hqg : (q : Surreal.{u}) < mk g := by
    simpa only [mk_dyadic] using mk_lt_mk.mpr (Numeric.lt_right hg)
  obtain ⟨a, ha, hqa, hag⟩ := exists_birthdayTruncation_right_le hbg hqg
  have hcan : birthdayTruncation (q : Surreal.{u}) a ∈ rightPrefixes (appendMinus p) := by
    rw [← hsrc]
    exact mem_rightPrefixes.mpr ⟨a, ha, rfl, hqa⟩
  have hpg : p ≤ mk g := (le_of_mem_rightPrefixes_appendMinus hcan).trans hag
  have he : mk g = (q.upper : Surreal.{u}) := by
    simp only [Dyadic.eq_upper_of_mem_moves_right_toIGame hg, mk_dyadic]
  rw [he] at hpg
  have hqu : (q.upper : Surreal.{u}) ≤ (q : Surreal) + 1 := by
    have hd : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
    have hinv : (q.den : ℚ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hd
    have hrat : q.upper.toRat ≤ q.toRat + 1 := by
      rw [q.coe_upper]
      exact add_le_add le_rfl hinv
    exact_mod_cast hrat
  exact sub_le_iff_le_add.mpr (by simpa only [add_comm] using hpg.trans hqu)

/-- A real canonical minus successor of a real coefficient has finite birthday. -/
theorem birthday_real_lt_omega0_of_eq_appendMinus {r t : ℝ}
    (hsrc : (r : Surreal.{u}) = appendMinus (t : Surreal.{u})) :
    (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 := by
  apply (birthday_real_le_omega0 r).lt_of_ne
  intro he
  rw [hsrc, birthday_appendMinus] at he
  have hv := congrArg NatOrdinal.val he
  rw [NatOrdinal.val_add_one, NatOrdinal.val_of] at hv
  exact Ordinal.isSuccLimit_omega0.succ_ne (t : Surreal.{u}).birthday.val (by
    simpa only [Order.succ_eq_add_one] using hv)

/-- The gap from a real coefficient to its final-minus predecessor is at most one. -/
theorem real_sub_le_one_of_eq_appendMinus {r t : ℝ}
    (hsrc : (r : Surreal.{u}) = appendMinus (t : Surreal.{u})) : t - r ≤ 1 := by
  obtain ⟨q, hq⟩ := birthday_lt_omega0_iff.mp
    (birthday_real_lt_omega0_of_eq_appendMinus hsrc)
  change (q : Surreal.{u}) = (r : Surreal) at hq
  have h := sub_le_one_of_eq_appendMinus_dyadic q (hq.trans hsrc)
  rw [hq] at h
  apply Real.toSurreal_le_iff.mp
  simpa only [Real.toSurreal_sub, Real.toSurreal_one] using h

end Surreal
