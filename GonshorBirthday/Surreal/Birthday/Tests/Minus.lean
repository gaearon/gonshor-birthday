/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import GonshorBirthday.Surreal.Birthday.Minus
import GonshorBirthday.Surreal.Birthday.Dyadic
import GonshorBirthday.Surreal.Birthday.Coefficient

/-!
# Public clients for ordinal minus blocks
-/

universe u
open Surreal

example : appendMinuses (0 : Surreal.{u}) 0 = 0 := by simp

example : plusCount (appendMinuses (1 : Surreal.{u}) Ordinal.omega0) = 1 := by
  rw [plusCount_appendMinuses]
  simpa using plusCount_toSurreal (1 : NatOrdinal.{u})

example : (appendMinuses (1 : Surreal.{u}) Ordinal.omega0).birthday =
    NatOrdinal.of Ordinal.omega0 := by
  rw [birthday_appendMinuses]
  simp

example : appendMinuses (1 : Surreal.{u}) 1 = (((1 : Dyadic) >>> 1) : Surreal.{u}) := by
  rw [appendMinuses_one]
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
