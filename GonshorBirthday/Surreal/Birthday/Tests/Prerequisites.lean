/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import GonshorBirthday.Surreal.Birthday.Addition
import GonshorBirthday.Surreal.Birthday.Append
import GonshorBirthday.Surreal.Birthday.Constant
import GonshorBirthday.Surreal.Birthday.Coefficient
import GonshorBirthday.Surreal.Birthday.PlusCount
import GonshorBirthday.Surreal.Birthday.Multiplication
import GonshorBirthday.Surreal.Birthday.Omega
import GonshorBirthday.Surreal.Birthday.Dyadic

/-!
# Public clients for birthday prerequisites
-/

universe u

noncomputable section
open Surreal

example (x : Surreal.{u}) : birthdayTruncation x 0 = 0 := birthdayTruncation_zero x

example : birthdayTruncation (2 : Surreal.{u}) 1 = 1 := birthdayTruncation_two_one

example : birthdayTruncation (2 : Surreal.{u}) 1 ≠ 2 := by
  rw [birthdayTruncation_two_one]
  exact (show (1 : Surreal) < 2 from one_lt_two).ne

example (x : Surreal.{u}) {a b : NatOrdinal.{u}} (hab : a ≤ b) (hb : b ≤ x.birthday) :
    birthdayTruncation (birthdayTruncation x b) a = birthdayTruncation x a :=
  birthdayTruncation_birthdayTruncation x hab hb

example (x : Surreal.{u}) : ((-2 : Surreal) * x).birthday ≤ 2 * x.birthday := by
  simpa using birthday_intCast_mul_le (-2) x


example : plusCount (NatOrdinal.toSurreal (2 : NatOrdinal.{u})) = 2 :=
  plusCount_toSurreal _

example : (1 : Surreal.{u}) ∈ leftPrefixes 2 := one_mem_leftPrefixes_two


example (x y : Surreal.{u}) : plusCount (x + y) ≤ plusCount x + plusCount y :=
  plusCount_add_le x y



example (x : Surreal.{u}) : x.birthday ≤ (ω^ x).birthday := birthday_le_birthday_wpow x


example (a : NatOrdinal.{u}) : (ω^ a.toSurreal).birthday = ω^ a :=
  birthday_wpow_toSurreal a


example : Surreal.birthday (((1 : Dyadic) >>> 1) : Surreal.{u}) = 2 := by
  rw [Surreal.birthday_dyadic]
  rfl

example : Surreal.birthday (((-5 : Dyadic) >>> 1) : Surreal.{u}) = 4 := by
  rw [Surreal.birthday_dyadic]
  rfl


example : appendMinus (1 : Surreal.{u}) = (((1 : Dyadic) >>> 1) : Surreal.{u}) := by
  let q : Surreal.{u} := (((1 : Dyadic) >>> 1) : Surreal.{u})
  have hq : q.birthday = 2 := by
    rw [Surreal.birthday_dyadic]
    rfl
  have hL : ∀ z ∈ leftPrefixes (1 : Surreal.{u}), z < q := by
    intro z hz
    obtain ⟨a, ha, rfl, _⟩ := mem_leftPrefixes.mp hz
    have ha0 : a = 0 := NatOrdinal.lt_one_iff.mp (by simpa using ha)
    rw [ha0, birthdayTruncation_zero]
    change (0 : Surreal.{u}) < (((1 : Dyadic) >>> 1) : Surreal.{u})
    exact_mod_cast (show (0 : Dyadic) < ((1 : Dyadic) >>> 1) from by decide)
  have hR : ∀ z ∈ ({1} : Set Surreal.{u}), q < z := by
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    change ((((1 : Dyadic) >>> 1) : Dyadic) : Surreal.{u}) < 1
    exact_mod_cast (show ((1 : Dyadic) >>> 1) < 1 from by decide)
  by_contra h
  rw [appendMinus_eq_ofSets] at h
  have ht : (appendMinus (1 : Surreal.{u})).birthday < q.birthday := by
    rw [appendMinus_eq_ofSets]
    exact birthday_ofSets_lt_of_btwn hL hR h
  simp [birthday_appendMinus, hq] at ht


example : (appendPluses (1 : Surreal.{u}) Ordinal.omega0).birthday =
    NatOrdinal.of Ordinal.omega0 := by
  rw [birthday_appendPluses, birthday_one]
  simp

example : plusCount (appendPluses (0 : Surreal.{u}) Ordinal.omega0) =
    NatOrdinal.of Ordinal.omega0 := by
  rw [plusCount_appendPluses, plusCount_zero]
  simp





example (o : NatOrdinal.{u}) : appendPlus (ω^ (-o.toSurreal)) = 2 * ω^ (-o.toSurreal) := by
  have ht := appendPlus_natCast_mul_wpow_of_plusCount_eq_zero (plusCount_neg_toSurreal o) 0
  simpa only [zero_add, Nat.cast_one, one_mul, two_mul] using ht


example (x : Surreal.{u}) : (2 * ω^ x).birthday =
    NatOrdinal.of ((ω^ x).birthday.val + (plusCount (ω^ x)).val) := by
  have ht := birthday_natCast_mul_wpow_add_wpow x 0
  simpa only [zero_add, Nat.cast_one, one_mul, two_mul] using ht
