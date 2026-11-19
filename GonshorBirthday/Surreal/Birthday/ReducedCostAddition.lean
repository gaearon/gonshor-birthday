/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostPrefix

import GonshorBirthday.Surreal.Birthday.Addition
import Mathlib.Tactic.Abel

/-!
# Cutoff forms and right-prefix bounds for reduced addition costs

The positive common-margin estimate is equivalent to the unequal-cutoff estimate,
including zero minimum margin. Bounds for smaller input pairs also control every
retained canonical right prefix and the case when those prefixes are cofinal.
-/

universe u

public noncomputable section

namespace Surreal

/-- At the output's own value, the plus-only cost fits every pair of input costs. -/
theorem reducedOmegaCost_add_self_le (a b A B : Surreal.{u}) :
    reducedOmegaCost (a + b) (a + b) ≤ reducedOmegaCost A a * reducedOmegaCost B b := by
  rw [reducedOmegaCost_self_eq_wpow]
  calc
    ω^ plusCount (a + b) ≤ ω^ (plusCount a + plusCount b) :=
      NatOrdinal.wpow_le_wpow.mpr (plusCount_add_le a b)
    _ = ω^ plusCount a * ω^ plusCount b := NatOrdinal.wpow_add _ _
    _ ≤ _ := mul_le_mul' (wpow_plusCount_le_reducedOmegaCost A a)
      (wpow_plusCount_le_reducedOmegaCost B b)

/-- Positive common margins and arbitrary admissible cutoffs give equivalent estimates. -/
theorem reducedOmegaCost_add_iff_common_margin (a b : Surreal.{u}) :
    (∀ d : Surreal.{u}, 0 < d →
      reducedOmegaCost (a + b + d) (a + b) ≤
        reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b) ↔
    (∀ A B : Surreal.{u}, a ≤ A → b ≤ B →
      reducedOmegaCost (min (A + b) (a + B)) (a + b) ≤
        reducedOmegaCost A a * reducedOmegaCost B b) := by
  constructor
  · intro h A B ha hb
    rcases ha.lt_or_eq with ha | rfl
    · rcases hb.lt_or_eq with hb | rfl
      · let d := min (A - a) (B - b)
        have hd : 0 < d := lt_min (sub_pos.mpr ha) (sub_pos.mpr hb)
        have ha' : a + d ≤ A := by
          simpa only [add_comm] using
            (le_sub_iff_add_le.mp (min_le_left (A - a) (B - b)))
        have hb' : b + d ≤ B := by
          simpa only [add_comm] using
            (le_sub_iff_add_le.mp (min_le_right (A - a) (B - b)))
        have hC : min (A + b) (a + B) = a + b + d := by
          dsimp only [d]
          rw [add_min]
          congr 1 <;> abel
        rw [hC]
        exact (h d hd).trans (mul_le_mul' (reducedOmegaCost_mono a ha')
          (reducedOmegaCost_mono b hb'))
      · rw [min_eq_right (add_le_add ha.le le_rfl)]
        exact reducedOmegaCost_add_self_le a b A b
    · rw [min_eq_left (add_le_add le_rfl hb)]
      exact reducedOmegaCost_add_self_le a b a B
  · intro h d hd
    have he : a + d + b = a + (b + d) := by abel
    simpa only [he, min_self, add_assoc] using
      h (a + d) (b + d) (le_add_of_nonneg_right hd.le) (le_add_of_nonneg_right hd.le)

/-- An addition-option bound controls a canonical right prefix at the original output cutoff. -/
theorem reducedOmegaCost_rightPrefix_add_le {a b A B u v : Surreal.{u}}
    (hu : u ∈ rightPrefixes a) (hv : v ∈ rightPrefixes (a + b)) (huv : u + b ≤ v)
    (h : reducedOmegaCost (min (A + b) (u + B)) (u + b) ≤
      reducedOmegaCost A u * reducedOmegaCost B b) :
    reducedOmegaCost (min (A + b) (a + B)) v ≤
      reducedOmegaCost A u * reducedOmegaCost B b := by
  have hp : birthdayTruncation (u + b) v.birthday = v := by
    exact (birthdayTruncation_eq_of_right_between
      (birthday_lt_of_mem_rightPrefixes hv).le
      (add_le_add (mem_rightPrefixes_iff.mp hu).2.le le_rfl)
      (huv.trans_eq (mem_rightPrefixes_iff.mp hv).1.symm)).trans
        (mem_rightPrefixes_iff.mp hv).1
  have hb : v.birthday ≤ (u + b).birthday := by
    simpa only [hp] using birthday_birthdayTruncation_le_birthday (u + b) v.birthday
  calc
    reducedOmegaCost (min (A + b) (a + B)) v ≤
        reducedOmegaCost (min (A + b) (a + B)) (u + b) := by
      simpa only [hp] using
        reducedOmegaCost_birthdayTruncation_le (min (A + b) (a + B)) (u + b) hb
    _ ≤ reducedOmegaCost (min (A + b) (u + B)) (u + b) :=
      reducedOmegaCost_mono (u + b)
        (min_le_min le_rfl (add_le_add (mem_rightPrefixes_iff.mp hu).2.le le_rfl))
    _ ≤ _ := h

/-- Any right addition option below a retained canonical right prefix bounds its cost.
The same comparison shows that the input option is retained at its original cutoff. -/
theorem rightPrefix_cost_le_of_add_le {a b A B u w : Surreal.{u}}
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ d : Surreal.{u}, 0 < d → reducedOmegaCost (x + y + d) (x + y) ≤
        reducedOmegaCost (x + d) x * reducedOmegaCost (y + d) y)
    (hu : u ∈ rightPrefixes a) (hw : w ∈ rightPrefixes (a + b)) (huw : u + b ≤ w)
    (hwC : w ≤ min (A + b) (a + B)) :
    u ≤ A ∧ reducedOmegaCost (min (A + b) (a + B)) w ≤
      reducedOmegaCost A u * reducedOmegaCost B b := by
  have huA := (add_le_add_iff_right b).mp (huw.trans (hwC.trans (min_le_left _ _)))
  have hbB := (add_le_add_iff_left a).mp
    ((mem_rightPrefixes_iff.mp hw).2.le.trans (hwC.trans (min_le_right _ _)))
  exact ⟨huA, reducedOmegaCost_rightPrefix_add_le hu hw huw
    ((reducedOmegaCost_add_iff_common_margin u b).mp
      (ih u b (add_lt_add_of_lt_of_le (birthday_lt_of_mem_rightPrefixes hu) le_rfl)) A B huA hbB)⟩

/-- A retained output prefix is paid by an actual retained prefix in one input direction. -/
theorem exists_retained_rightPrefix_mul_bound_of_smaller {a b A B v : Surreal.{u}}
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ d : Surreal.{u}, 0 < d → reducedOmegaCost (x + y + d) (x + y) ≤
        reducedOmegaCost (x + d) x * reducedOmegaCost (y + d) y)
    (hv : v ∈ rightPrefixes (a + b)) (hvC : v ≤ min (A + b) (a + B)) :
    (∃ w ∈ rightPrefixes a, w ≤ A ∧
      reducedOmegaCost (min (A + b) (a + B)) v ≤
        reducedOmegaCost A w * reducedOmegaCost B b) ∨
    (∃ w ∈ rightPrefixes b, w ≤ B ∧
      reducedOmegaCost (min (A + b) (a + B)) v ≤
        reducedOmegaCost A a * reducedOmegaCost B w) := by
  rcases exists_rightPrefixes_add_le hv with ⟨u, hu, huv⟩ | ⟨u, hu, huv⟩
  · exact Or.inl ⟨u, hu, rightPrefix_cost_le_of_add_le ih hu hv huv hvC⟩
  · right
    refine ⟨u, hu, ?_⟩
    simpa only [add_comm, min_comm, mul_comm] using
      rightPrefix_cost_le_of_add_le (a := b) (b := a) (A := B) (B := A)
        (by simpa only [add_comm] using ih) hu (by simpa only [add_comm] using hv)
        (by simpa only [add_comm] using huv) (by simpa only [add_comm, min_comm] using hvC)

/-- Smaller-input estimates bound every retained right prefix of a sum. -/
theorem reducedOmegaCost_rightPrefix_add_le_of_smaller {a b A B v : Surreal.{u}}
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ d : Surreal.{u}, 0 < d → reducedOmegaCost (x + y + d) (x + y) ≤
        reducedOmegaCost (x + d) x * reducedOmegaCost (y + d) y)
    (hv : v ∈ rightPrefixes (a + b)) (hvC : v ≤ min (A + b) (a + B)) :
    reducedOmegaCost (min (A + b) (a + B)) v ≤
      reducedOmegaCost A a * reducedOmegaCost B b := by
  rcases exists_retained_rightPrefix_mul_bound_of_smaller ih hv hvC with
    ⟨x, hx, hxA, h⟩ | ⟨y, hy, hyB, h⟩
  · exact h.trans (mul_le_mul' (reducedOmegaCost_lt_of_mem_rightPrefixes hx hxA).le le_rfl)
  · exact h.trans (mul_le_mul' le_rfl (reducedOmegaCost_lt_of_mem_rightPrefixes hy hyB).le)

/-- Cofinal retained output minuses close the addition estimate from smaller-input estimates. -/
theorem reducedOmegaCost_add_le_of_cofinal_rightPrefixes {a b A B : Surreal.{u}}
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ d : Surreal.{u}, 0 < d → reducedOmegaCost (x + y + d) (x + y) ≤
        reducedOmegaCost (x + d) x * reducedOmegaCost (y + d) y)
    (hc : ∀ c < (a + b).birthday, ∃ v ∈ rightPrefixes (a + b),
      c < v.birthday ∧ v ≤ min (A + b) (a + B)) :
    reducedOmegaCost (min (A + b) (a + B)) (a + b) ≤
      reducedOmegaCost A a * reducedOmegaCost B b := by
  refine reducedOmegaCost_le_of_cofinal_rightPrefixes _ _ _ ?_ hc ?_
  · simpa only [one_mul] using mul_le_mul' (one_le_reducedOmegaCost A a)
      (one_le_reducedOmegaCost B b)
  · intro v hv hvC
    exact reducedOmegaCost_rightPrefix_add_le_of_smaller ih hv hvC

end Surreal
