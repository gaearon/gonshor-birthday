/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import GonshorBirthday.Surreal.Birthday.CoefficientPosition

/-!
# Public complete real coefficient-word clients

The initial monomial and the later coefficient blocks are distinguished. Both
positive and negative coefficient tails reflect their original coefficient signs.
-/

universe u
open Surreal

example {r : ℝ} (hr : 0 < r) (x : Surreal.{u}) {j : Ordinal.{u}}
    (hj : j < ((r : Surreal) * ω^ x).birthday.val) (hbase : (ω^ x).birthday.val ≤ j)
    (hp : birthdayTruncation ((r : Surreal) * ω^ x) (NatOrdinal.of j) < (r : Surreal) * ω^ x) :
    ∃ n : ℕ, ((n + 1 : ℕ) : NatOrdinal.{u}) < (r : Surreal.{u}).birthday ∧
      birthdayTruncation (r : Surreal.{u}) ((n + 1 : ℕ) : NatOrdinal) < (r : Surreal.{u}) := by
  obtain ⟨hjA, hval, hplus, hminus⟩ | ⟨n, hn, t, ht, hpos, hplus, hminus⟩ :=
    real_mul_wpow_position hr x hj
  · exact False.elim (hjA.not_ge hbase)
  · exact ⟨n, hn, hplus.mp hp⟩

example {r : ℝ} (hr : r < 0) (x : Surreal.{u}) {j : Ordinal.{u}}
    (hj : j < ((r : Surreal) * ω^ x).birthday.val) (hbase : (ω^ x).birthday.val ≤ j)
    (hp : birthdayTruncation ((r : Surreal) * ω^ x) (NatOrdinal.of j) < (r : Surreal) * ω^ x) :
    ∃ n : ℕ, ((n + 1 : ℕ) : NatOrdinal.{u}) < (r : Surreal.{u}).birthday ∧
      birthdayTruncation (r : Surreal.{u}) ((n + 1 : ℕ) : NatOrdinal) < (r : Surreal.{u}) := by
  obtain ⟨hjA, hval, hplus, hminus⟩ | ⟨n, hn, t, ht, hpos, hplus, hminus⟩ :=
    neg_real_mul_wpow_position hr x hj
  · exact False.elim (hjA.not_ge hbase)
  · exact ⟨n, hn, hplus.mp hp⟩

example (x : Surreal.{u}) {j : Ordinal.{u}} (hj : j < (ω^ x).birthday.val) :
    birthdayTruncation (((1 : ℝ) : Surreal) * ω^ x) (NatOrdinal.of j) =
      birthdayTruncation (ω^ x) (NatOrdinal.of j) := by
  have ht := real_mul_wpow_position (r := 1) (by norm_num) x
    (j := j) (by simpa only [Real.toSurreal_one, one_mul] using hj)
  rcases ht with ⟨hjA, hval, hplus, hminus⟩ | ⟨n, hn, t, ht, hpos, hplus, hminus⟩
  · exact hval
  · have h1 : (1 : NatOrdinal.{u}) ≤ ((n + 1 : ℕ) : NatOrdinal) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    simp only [Real.toSurreal_one, birthday_one] at hn
    exact False.elim (hn.not_ge h1)
