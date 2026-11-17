/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadCoefficientWord
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Real coefficient tail clients with arbitrary higher heads

Both coefficient signs are included. The rational coefficient one third has infinite
birthday, so its exact omega-length tail separates this formula from a finite-word bound.
-/

universe u
open Surreal Set

private theorem birthday_third : ((1 / 3 : ℝ) : Surreal.{u}).birthday =
    NatOrdinal.of Ordinal.omega0 := by
  apply (birthday_real_eq_omega0_iff _).mpr
  rintro ⟨q, hq⟩
  change (q.toRat : ℝ) = 1 / 3 at hq
  have hq' : (q.toRat : ℝ) = Rat.cast (1 / 3 : ℚ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hq
  have he : q.toRat = (1 / 3 : ℚ) := (Rat.cast_inj (α := ℝ)).mp hq'
  have hd : q.den = 3 := by simpa using congrArg Rat.den he
  obtain ⟨n, hn⟩ := q.den_mem_powers
  change 2 ^ n = q.den at hn
  rw [hd] at hn
  cases n with
  | zero => norm_num at hn
  | succ n => rw [pow_succ] at hn; omega

/-- The headed one-third coefficient has an exact omega-length coefficient tail. -/
public theorem Tests.headed_third_tail_birthday (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) :
    (K + ((1 / 3 : ℝ) : Surreal) * ω^ s).birthday = NatOrdinal.of
      ((K + ω^ s).birthday.val + (ω^ (plusCount s)).val * Ordinal.omega0) :=
  birthday_head_real_mul_wpow_of_birthday_omega0 K s hK (by norm_num) birthday_third

example (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) :
    (K - ((1 / 3 : ℝ) : Surreal) * ω^ s).birthday = NatOrdinal.of
      ((K - ω^ s).birthday.val + (ω^ (plusCount s)).val * Ordinal.omega0) := by
  have ht := birthday_head_real_mul_wpow_of_neg K s hK (r := (-(1 / 3) : ℝ)) (by norm_num)
  have hb : (((-(1 / 3) : ℝ) : Surreal.{u})).birthday = NatOrdinal.of Ordinal.omega0 := by
    simpa only [Real.toSurreal_neg, birthday_neg] using birthday_third.{u}
  rw [hb, NatOrdinal.val_of] at ht
  have hsub : Ordinal.omega0.{u} - 1 = Ordinal.omega0 := by
    calc
      _ = (1 + Ordinal.omega0) - 1 := by simp
      _ = _ := Ordinal.add_sub_cancel 1 _
  simpa only [hsub, Real.toSurreal_neg, neg_mul, ← sub_eq_add_neg] using ht

example (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) :
    K + ((-2 : ℝ) : Surreal) * ω^ s =
      appendMinuses (K - ω^ s) (ω^ (plusCount s)).val := by
  have hp : birthdayTruncation ((-2 : ℝ) : Surreal.{u}) 1 = ((-1 : ℝ) : Surreal.{u}) := by
    have h : birthdayTruncation (2 : Surreal.{u}) (1 : Surreal).birthday = 1 := by
      simpa only [birthday_one] using birthdayTruncation_two_one.{u}
    simpa using birthdayTruncation_neg_of_eq h
  have ht := head_real_mul_wpow_birthdayTruncation_add_one_minus K s hK (-2 : ℝ)
    (a := (1 : NatOrdinal.{u})) (by simp) (by norm_num) (by rw [hp]; norm_num)
  have hb : (((-2 : ℝ) : Surreal.{u})).birthday = (1 : NatOrdinal.{u}) + 1 := by norm_num
  rw [← hb, birthdayTruncation_birthday, hp] at ht
  simpa [sub_eq_add_neg] using ht
