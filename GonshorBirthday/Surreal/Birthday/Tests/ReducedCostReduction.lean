/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostReduction

/-!
# Retained-minus endpoint and proper-limit clients

A last minus after an arbitrary head retains its exact cost even before a
transfinite plus tail. Under the smaller-pair induction hypothesis, a failure of
the common-margin inequality must have output birthday strictly beyond omega.
-/

public noncomputable section

namespace Tests

open Surreal Ordinal

/-- A last retained minus and a nonempty ordinal plus tail contribute in their original order. -/
theorem last_minus_before_plus_tail (C x : Surreal.{0}) (hC : x ≤ C)
    (a : Ordinal.{0}) (ha : 0 < a) :
    reducedOmegaCost C (appendPluses (appendMinus x) a) = NatOrdinal.of
      ((reducedOmegaCost C x).val + (ω^ (plusCount x + 1)).val +
        (ω^ (NatOrdinal.of ((plusCount x).val + a))).val) := by
  have hx : x ∈ rightPrefixes (appendPluses (appendMinus x) a) := by
    rw [rightPrefixes_appendPluses]
    exact mem_rightPrefixes_iff.mpr ⟨birthdayTruncation_appendMinus x, appendMinus_lt x⟩
  have hlast : ∀ z ∈ rightPrefixes (appendPluses (appendMinus x) a), z ≤ C →
      z.birthday ≤ x.birthday := by
    intro z hz _
    rw [rightPrefixes_appendPluses] at hz
    have hb := birthday_lt_of_mem_rightPrefixes hz
    rw [birthday_appendMinus] at hb
    exact Order.lt_add_one_iff.mp hb
  have hp : plusCount x < plusCount (appendPluses (appendMinus x) a) := by
    simpa only [appendPluses_zero, plusCount_appendMinus] using
      strictMono_plusCount_appendPluses (appendMinus x) ha
  have he := reducedOmegaCost_eq_of_last_retained_rightPrefix hx hC hlast
  rw [ite_eq_left hp] at he
  simpa only [plusCount_appendPluses, plusCount_appendMinus] using he

/-- A failure under the induction hypothesis requires a proper limit before the output ends. -/
theorem common_margin_failure_beyond_omega (a b d : Surreal.{0}) (hd : 0 < d)
    (ih : ∀ x y : Surreal.{0}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ t : Surreal.{0}, 0 < t → reducedOmegaCost (x + y + t) (x + y) ≤
        reducedOmegaCost (x + t) x * reducedOmegaCost (y + t) y)
    (hfail : reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b <
      reducedOmegaCost (a + b + d) (a + b)) :
    NatOrdinal.of Ordinal.omega0 < (a + b).birthday := by
  obtain ⟨c, hc, hlim, _⟩ := exists_limit_prefix_of_common_margin_failure a b d hd ih hfail
  exact (NatOrdinal.of.monotone (Ordinal.omega0_le_of_isSuccLimit hlim)).trans_lt hc

end Tests
