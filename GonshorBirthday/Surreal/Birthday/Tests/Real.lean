/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import GonshorBirthday.Surreal.Birthday.Real
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Public real birthday clients

The real one third is rational and has infinite birthday, separating dyadic
coefficients from arbitrary rational coefficients.
-/

universe u
open Surreal

example : (0 : Surreal.{u}).birthday = 0 := by simp

example (r : ℝ) {a : NatOrdinal.{u}} (ha : a < (r : Surreal.{u}).birthday) :
    birthdayTruncation (r : Surreal) a ∈ Set.range ((↑) : Dyadic → Surreal.{u}) :=
  birthdayTruncation_real_mem_range_dyadic r ha

example : (((1 / 3 : ℝ) : Surreal.{u})).birthday = NatOrdinal.of Ordinal.omega0 := by
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
