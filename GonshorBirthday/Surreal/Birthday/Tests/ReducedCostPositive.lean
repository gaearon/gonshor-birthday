/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostPositive

import GonshorBirthday.Surreal.Birthday.HeadMidpoint

/-!
# Positive unit endpoints with an actual late right prefix

The head is a nonzero monomial. The client constructs the late prefix, verifies
that its birthday reaches the head, and then obtains a strictly smaller gap.
-/

universe u
public noncomputable section
namespace Tests
open Surreal Set

/-- A nonempty higher head has an actual late right prefix whose gap can be halved. -/
theorem nonempty_head_half_gap (u : Surreal.{u}) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧
      ω^ (u + 1) + (q : Surreal) * ω^ u ∈
        rightPrefixes (ω^ (u + 1) + ω^ (appendMinus u)) ∧
      ∃ p ∈ rightPrefixes (ω^ (u + 1) + ω^ (appendMinus u)),
        2 * (p - (ω^ (u + 1) + ω^ (appendMinus u))) <
          (ω^ (u + 1) + (q : Surreal) * ω^ u) -
            (ω^ (u + 1) + ω^ (appendMinus u)) := by
  have hK : (ω^ (u + 1)).support ⊆ Ioi u := by
    rw [support_wpow]
    intro i hi
    rw [mem_singleton_iff] at hi
    subst i
    exact lt_add_one u
  have hu : u ∈ rightPrefixes (appendMinus u) :=
    mem_rightPrefixes_iff.mpr ⟨birthdayTruncation_appendMinus u, appendMinus_lt u⟩
  obtain ⟨q, hqpos, hqone, hqp⟩ := exists_head_real_mul_wpow_rightPrefix_lt_add
    (ω^ (u + 1)) u hK 0 (t := 1) (by norm_num) hu (ε := 1) (by norm_num)
  simp only [zero_add, Real.toSurreal_zero, zero_mul, Real.toSurreal_one, one_mul] at hqp hqone
  have hpre : birthdayTruncation (ω^ (u + 1) + (q : Surreal) * ω^ u)
      (ω^ (u + 1)).birthday = ω^ (u + 1) := by
    apply birthdayTruncation_add_of_support_lt
    rw [wlog_mul (Real.toSurreal_pos_iff.mpr hqpos).ne' (wpow_ne_zero _),
      wlog_realCast, wlog_wpow, zero_add]
    exact hK
  have hlate : (ω^ (u + 1)).birthday ≤
      (ω^ (u + 1) + (q : Surreal) * ω^ u).birthday := by
    have h := birthday_birthdayTruncation_le_birthday
      (ω^ (u + 1) + (q : Surreal) * ω^ u) (ω^ (u + 1)).birthday
    rwa [hpre] at h
  refine ⟨q, hqpos, hqone, hqp, ?_⟩
  apply exists_rightPrefix_half_gap_of_late_head_add_wpow
    (ω^ (u + 1)) (appendMinus u) _ hqp hlate
  exact fun i hi ↦ (appendMinus_lt u).trans (hK hi)

end Tests
