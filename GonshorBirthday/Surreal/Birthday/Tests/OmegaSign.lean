/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import GonshorBirthday.Surreal.Birthday.OmegaSign

/-!
# Public complete omega-sign reflection clients
-/

universe u
open Surreal

example (x : Surreal.{u}) {j : Ordinal.{u}} (hj : j < (ω^ x).birthday.val)
    (hj0 : j ≠ 0) (hp : birthdayTruncation (ω^ x) (NatOrdinal.of j) < ω^ x) :
    ∃ a < x.birthday, birthdayTruncation x a < x := by
  obtain hj' | ⟨a, ha, t, ht, hpos, hplus, hminus⟩ := wpow_position x hj
  · exact False.elim (hj0 hj')
  · exact ⟨a, ha, hplus.mp hp⟩

example (x : Surreal.{u}) {j : Ordinal.{u}} (hj : j < (ω^ x).birthday.val)
    (hm : ω^ x < birthdayTruncation (ω^ x) (NatOrdinal.of j)) :
    ∃ a < x.birthday, x < birthdayTruncation x a := by
  obtain rfl | ⟨a, ha, t, ht, hpos, hplus, hminus⟩ := wpow_position x hj
  · simp only [NatOrdinal.of_zero, birthdayTruncation_zero] at hm
    exact False.elim ((wpow_pos x).not_gt hm)
  · exact ⟨a, ha, hminus.mp hm⟩
