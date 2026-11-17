/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import GonshorBirthday.Surreal.Birthday.CoefficientPrefix

/-!
# Public real coefficient-prefix clients
-/

universe u
open Surreal IGame

example (r : ℝ) (hr : 0 < r) (x : Surreal.{u}) :
    birthdayTruncation ((r : Surreal) * ω^ x) (ω^ x).birthday = ω^ x :=
  birthdayTruncation_real_mul_wpow r hr x

example {r : ℝ} {q : Dyadic}
    (hq : birthdayTruncation (r : Surreal.{u}) (q : Surreal).birthday = (q : Surreal))
    (x : Surreal.{u}) : birthdayTruncation ((r : Surreal) * ω^ x)
      ((q : Surreal) * ω^ x).birthday = (q : Surreal) * ω^ x :=
  birthdayTruncation_real_mul_wpow_of_dyadic_prefix hq x

example (x : Surreal.{u}) :
    birthdayTruncation (((3 / 8 : ℝ) : Surreal) * ω^ x)
      ((2 : Surreal)⁻¹ * ω^ x).birthday = (2 : Surreal)⁻¹ * ω^ x := by
  have hf : Fits ((3 / 8 : ℝ) : IGame.{u}) ½ := by
    constructor
    · intro a ha
      obtain rfl := Set.mem_singleton_iff.mp (by simpa only [moves_left_half] using ha)
      exact (show (0 : IGame.{u}) < ((3 / 8 : ℝ) : IGame) from by
        exact_mod_cast (by norm_num : (0 : ℝ) < 3 / 8)).not_ge
    · intro a ha
      obtain rfl := Set.mem_singleton_iff.mp (by simpa only [moves_right_half] using ha)
      exact (show ((3 / 8 : ℝ) : IGame.{u}) < 1 from by
        exact_mod_cast (by norm_num : (3 / 8 : ℝ) < 1)).not_ge
  have ht := (hf.real_mul_wpow (x := x.out)).birthdayTruncation_eq
  simpa only [mk_mul, mk_real_toIGame, IGame.mk_half, mk_wpow, out_eq] using ht

example {r : ℝ} {y : Surreal.{u}}
    (h : birthdayTruncation (r : Surreal) y.birthday = y) (x : Surreal.{u}) :
    birthdayTruncation ((r : Surreal) * ω^ x) (y * ω^ x).birthday = y * ω^ x :=
  birthdayTruncation_real_mul_wpow_of_prefix h x
