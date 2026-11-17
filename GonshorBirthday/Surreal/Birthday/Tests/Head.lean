/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import GonshorBirthday.Surreal.Birthday.Head

/-!
# Higher-head coefficient-prefix clients

The nonempty head can have arbitrary exponent; the last coefficient may be negative.
The halving comparison concerns every canonical right prefix, including prefixes in the head.
-/

universe u
open Surreal Set

example (x : Surreal.{u}) {r s : ℝ}
    (hp : birthdayTruncation (r : Surreal.{u}) (s : Surreal.{u}).birthday = s) :
    birthdayTruncation ((r : Surreal) * ω^ x) ((s : Surreal) * ω^ x).birthday =
      (s : Surreal) * ω^ x := by
  simpa using birthdayTruncation_head_real_mul_wpow_of_prefix 0 x (by simp) hp

example (x : Surreal.{u}) {r : ℝ}
    (hb : (r : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0)
    {p : Surreal.{u}} (hp : p ∈ rightPrefixes (ω^ (x + 1) + (r : Surreal) * ω^ x)) :
    ∃ s : ℝ, ω^ (x + 1) + (s : Surreal) * ω^ x ∈
        rightPrefixes (ω^ (x + 1) + (r : Surreal) * ω^ x) ∧
      2 * ((ω^ (x + 1) + (s : Surreal) * ω^ x) -
        (ω^ (x + 1) + (r : Surreal) * ω^ x)) <
        p - (ω^ (x + 1) + (r : Surreal) * ω^ x) := by
  apply exists_head_real_mul_wpow_rightPrefix_half_gap (ω^ (x + 1)) x _ hb hp
  rw [support_wpow]
  intro i hi
  rw [mem_singleton_iff] at hi
  subst i
  exact lt_add_one x

example (K a b s : Surreal.{u}) (hK : K.support ⊆ Ioi s)
    (hp : birthdayTruncation a b.birthday = b) (hab : (a - b).wlog ≤ s) :
    birthdayTruncation (K + a) (K + b).birthday = K + b :=
  birthdayTruncation_head_add_of_wlog_sub_le hK hp hab
