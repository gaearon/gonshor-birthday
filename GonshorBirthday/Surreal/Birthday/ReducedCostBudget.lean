/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostAddition
public import GonshorBirthday.Surreal.Birthday.ReducedCostPlus

import GonshorBirthday.NatOrdinal.PrefixBudget
import GonshorBirthday.Surreal.Birthday.Addition

/-!
# Completed right-prefix bounds for reduced addition costs

An output right prefix is charged together with its next minus block and the power
contributed by any later pluses. Smaller input pairs bound the prefix itself; the
retained input minus and remaining-plus budgets pay for the two additional portions.
-/

universe u

public noncomputable section

namespace Surreal

/-- An addition-option estimate pays the output prefix, next minus, and any later pluses. -/
theorem reducedOmegaCost_rightPrefix_add_budget {a b A B u v : Surreal.{u}}
    (hu : u ∈ rightPrefixes a) (huA : u ≤ A)
    (hv : v ∈ rightPrefixes (a + b)) (huv : u + b ≤ v)
    (h : reducedOmegaCost (min (A + b) (u + B)) (u + b) ≤
      reducedOmegaCost A u * reducedOmegaCost B b) :
    NatOrdinal.of ((reducedOmegaCost (min (A + b) (a + B)) v).val +
      (ω^ (plusCount v + 1)).val +
      if plusCount v < plusCount (a + b) then (ω^ plusCount (a + b)).val else 0) ≤
        reducedOmegaCost A a * reducedOmegaCost B b := by
  have hp : birthdayTruncation (u + b) v.birthday = v := by
    exact (birthdayTruncation_eq_of_right_between
      (birthday_lt_of_mem_rightPrefixes hv).le
      (add_le_add (mem_rightPrefixes_iff.mp hu).2.le le_rfl)
      (huv.trans_eq (mem_rightPrefixes_iff.mp hv).1.symm)).trans
        (mem_rightPrefixes_iff.mp hv).1
  have hα : plusCount u ≤ plusCount a := by
    simpa only [(mem_rightPrefixes_iff.mp hu).1] using
      plusCount_birthdayTruncation_le a (birthday_lt_of_mem_rightPrefixes hu).le
  have hρ : plusCount v ≤ plusCount u + plusCount b := by
    have hb : v.birthday ≤ (u + b).birthday := by
      simpa only [hp] using birthday_birthdayTruncation_le_birthday (u + b) v.birthday
    have hp' := plusCount_birthdayTruncation_le (u + b) hb
    rw [hp] at hp'
    exact hp'.trans (plusCount_add_le u b)
  have hb := NatOrdinal.oadd_wpow_budget_le_mul
    (reducedOmegaCost_rightPrefix_budget hu huA)
    (wpow_plusCount_le_reducedOmegaCost B b) hα hρ (plusCount_add_le a b)
  apply le_trans ?_ hb
  exact NatOrdinal.of.monotone (add_le_add
    (add_le_add (NatOrdinal.val.monotone (reducedOmegaCost_rightPrefix_add_le hu hv huv h))
      le_rfl) le_rfl)

/-- Smaller-input estimates bound every retained output prefix with its completed sign budget. -/
theorem reducedOmegaCost_rightPrefix_add_budget_of_smaller {a b A B v : Surreal.{u}}
    (ha : a ≤ A) (hb : b ≤ B)
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ d : Surreal.{u}, 0 < d → reducedOmegaCost (x + y + d) (x + y) ≤
        reducedOmegaCost (x + d) x * reducedOmegaCost (y + d) y)
    (hv : v ∈ rightPrefixes (a + b)) (hvC : v ≤ min (A + b) (a + B)) :
    NatOrdinal.of ((reducedOmegaCost (min (A + b) (a + B)) v).val +
      (ω^ (plusCount v + 1)).val +
      if plusCount v < plusCount (a + b) then (ω^ plusCount (a + b)).val else 0) ≤
        reducedOmegaCost A a * reducedOmegaCost B b := by
  rcases exists_rightPrefixes_add_le hv with ⟨u, hu, huv⟩ | ⟨u, hu, huv⟩
  · have huA : u ≤ A := by
      have h := huv.trans (hvC.trans (min_le_left _ _))
      simpa only [add_le_add_iff_right] using h
    have hi := (reducedOmegaCost_add_iff_common_margin u b).mp
      (ih u b (add_lt_add_of_lt_of_le (birthday_lt_of_mem_rightPrefixes hu) le_rfl))
      A B huA hb
    exact reducedOmegaCost_rightPrefix_add_budget hu huA hv huv hi
  · have huB : u ≤ B := by
      have h := huv.trans (hvC.trans (min_le_right _ _))
      simpa only [add_le_add_iff_left] using h
    have hi := (reducedOmegaCost_add_iff_common_margin u a).mp
      (ih u a (by
        simpa only [add_comm] using
          add_lt_add_of_lt_of_le (birthday_lt_of_mem_rightPrefixes hu)
            (le_refl a.birthday))) B A huB ha
    have hv' : v ∈ rightPrefixes (b + a) := by simpa only [add_comm] using hv
    have huv' : u + a ≤ v := by simpa only [add_comm] using huv
    simpa only [add_comm, min_comm, mul_comm] using
      reducedOmegaCost_rightPrefix_add_budget hu huB hv' huv' hi

end Surreal
