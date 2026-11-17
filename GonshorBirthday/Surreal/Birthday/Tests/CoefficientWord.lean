/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.CoefficientWord
import GonshorBirthday.Surreal.Birthday.Dyadic
import GonshorBirthday.Surreal.Birthday.Real
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Dyadic

/-!
# Public unrestricted real coefficient birthday clients
-/

universe u
open Surreal
namespace Tests

example {r : ℝ} (hr : r ≠ 0) (x : Surreal.{u}) :
    ((r : Surreal) * ω^ x).birthday = NatOrdinal.of
      ((ω^ x).birthday.val + (ω^ plusCount x).val * ((r : Surreal.{u}).birthday.val - 1)) :=
  birthday_real_mul_wpow_of_ne_zero hr x

/-- The mixed dyadic coefficient three halves has exactly three original signs. -/
public theorem birthday_three_halves : ((3 / 2 : ℝ) : Surreal.{u}).birthday = 3 := by
  have heRat : ((3 : Dyadic) >>> 1).toRat = (3 / 2 : ℚ) := by
    norm_num [Inclusion.IntervalDyadicReal.Dyadic.toRat_shiftRight_nat]
  have heReal : ((3 / 2 : ℝ) : Surreal.{u}) = (((3 : Dyadic) >>> 1) : Surreal) := by
    calc
      _ = Real.toSurreal (((3 : Dyadic) >>> 1).toRat : ℝ) := by
        congr 1
        rw [heRat]
        norm_num
      _ = _ := Real.toSurreal_ratCast _
  rw [heReal, birthday_dyadic]
  rfl

example (x : Surreal.{u}) :
    (((3 / 2 : ℝ) : Surreal) * ω^ x).birthday = NatOrdinal.of
      ((ω^ x).birthday.val + (ω^ plusCount x).val * 2) := by
  simpa only [Nat.cast_ofNat] using
    birthday_real_mul_wpow_of_birthday_nat (by norm_num : (0 : ℝ) < 3 / 2)
      (n := 2) birthday_three_halves x

example (x : Surreal.{u}) : ((0 : ℝ) * ω^ x).birthday = 0 := by simp

example (x : Surreal.{u}) :
    (((1 / 3 : ℝ) : Surreal) * ω^ x).birthday = NatOrdinal.of
      ((ω^ x).birthday.val + (ω^ plusCount x).val * Ordinal.omega0) := by
  have hb : ((1 / 3 : ℝ) : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0 := by
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
  exact birthday_real_mul_wpow_of_birthday_omega0 (by norm_num) hb x

example (x : Surreal.{u}) : ((3 / 2 : ℝ) : Surreal) * ω^ x =
    appendMinuses ((2 : Surreal) * ω^ x) (ω^ plusCount x).val := by
  have hf : IGame.Fits ((3 / 2 : ℝ) : IGame.{u}) (2 : IGame) := by
    constructor
    · intro a ha
      rw [IGame.moves_left_ofNat 2] at ha
      norm_num only [Nat.reduceSub, Nat.cast_one] at ha
      obtain rfl := Set.mem_singleton_iff.mp ha
      exact (show (1 : IGame.{u}) < ((3 / 2 : ℝ) : IGame) from by
        exact_mod_cast (by norm_num : (1 : ℝ) < 3 / 2)).not_ge
    · intro a ha
      simp only [IGame.moves_right_ofNat 2, Set.mem_empty_iff_false] at ha
  have hp := hf.birthdayTruncation_eq
  have h2 : Surreal.mk (2 : IGame.{u}) = (2 : Surreal.{u}) := mk_natCast 2
  rw [h2, mk_real_toIGame] at hp
  have hb : ((3 / 2 : ℝ) : Surreal.{u}).birthday = ((2 : ℝ) : Surreal).birthday + 1 := by
    rw [birthday_three_halves]
    norm_num
  have ht := real_mul_wpow_eq_appendMinuses_of_coefficient_prefix
    (r := 2) (s := 3 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by simpa using hp) hb x
  simpa using ht

end Tests
