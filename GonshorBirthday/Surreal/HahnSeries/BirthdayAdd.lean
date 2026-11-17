/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.HahnSeries.Birthday
public import GonshorBirthday.Surreal.HahnSeries.NormalFormAdd
public import GonshorBirthday.Surreal.Birthday.Addition

/-!
# Sharp plus-count addition and normal-form support

If the plus count of a sum attains the natural sum of the input plus counts,
normal-form tails below every output term cannot cancel. The argument uses the
canonical-prefix property of normal-form truncations and sharp-addition rigidity.
-/

universe u

public noncomputable section

namespace Surreal

open Set

/-- Every normal-form truncation is the corresponding canonical birthday prefix. -/
theorem birthdayTruncation_trunc (x s : Surreal.{u}) :
    birthdayTruncation x (x.normalFormTrunc s).birthday = x.normalFormTrunc s := by
  simpa only [SurrealHahnSeries.toSurreal_trunc, toSurreal_toHahnSeries] using
    SurrealHahnSeries.birthdayTruncation_trunc x.toHahnSeries s

/-- A normal-form truncation has birthday at most that of its source. -/
theorem birthday_normalFormTrunc_le (x s : Surreal.{u}) :
    (x.normalFormTrunc s).birthday ≤ x.birthday := by
  rw [← birthdayTruncation_trunc x s]
  exact birthday_birthdayTruncation_le_birthday x _

/-- Normal-form truncation is additive. -/
@[simp]
theorem trunc_add (x y s : Surreal.{u}) :
    (x + y).normalFormTrunc s = x.normalFormTrunc s + y.normalFormTrunc s := by
  apply toHahnSeries_inj.mp
  simp only [toHahnSeries_trunc, toHahnSeries_add, SurrealHahnSeries.trunc_add]

/-- Under sharp plus-count addition, a truncation fixes the sum only if it fixes both inputs. -/
theorem trunc_eq_self_of_plusCount_add_eq (x y s : Surreal.{u})
    (hs : (x + y).normalFormTrunc s = x + y)
    (hc : plusCount (x + y) = plusCount x + plusCount y) :
    x.normalFormTrunc s = x ∧ y.normalFormTrunc s = y := by
  have hsum : birthdayTruncation x (x.normalFormTrunc s).birthday +
      birthdayTruncation y (y.normalFormTrunc s).birthday = x + y := by
    rw [birthdayTruncation_trunc, birthdayTruncation_trunc, ← trunc_add, hs]
  simpa only [birthdayTruncation_trunc] using
    birthdayTruncation_eq_of_add_eq_of_plusCount_add_eq x y
      (birthday_normalFormTrunc_le x s) (birthday_normalFormTrunc_le y s) hsum hc

/-- Sharp plus-count addition prevents cancellation of all terms at or below a cutoff. -/
theorem support_subset_Ioi_of_plusCount_add_eq (x y s : Surreal.{u})
    (hs : (x + y).support ⊆ Ioi s)
    (hc : plusCount (x + y) = plusCount x + plusCount y) :
    x.support ⊆ Ioi s ∧ y.support ⊆ Ioi s := by
  obtain ⟨hx, hy⟩ := trunc_eq_self_of_plusCount_add_eq x y s (trunc_eq_self hs) hc
  exact ⟨normalFormTrunc_eq_self_iff.mp hx, normalFormTrunc_eq_self_iff.mp hy⟩

/-- With sharp plus-count addition, a lower bound for output exponents bounds both inputs. -/
theorem support_subset_Ici_of_plusCount_add_eq (x y s : Surreal.{u})
    (hs : (x + y).support ⊆ Ici s)
    (hc : plusCount (x + y) = plusCount x + plusCount y) :
    x.support ⊆ Ici s ∧ y.support ⊆ Ici s := by
  have h (j : Surreal.{u}) (hj : j < s) :
      x.support ⊆ Ioi j ∧ y.support ⊆ Ioi j :=
    support_subset_Ioi_of_plusCount_add_eq x y j
      (fun _ hk ↦ hj.trans_le (hs hk)) hc
  constructor
  · intro j hj
    by_contra hn
    have hjs : j < s := lt_of_not_ge hn
    exact (lt_irrefl j) ((h j hjs).1 hj)
  · intro j hj
    by_contra hn
    have hjs : j < s := lt_of_not_ge hn
    exact (lt_irrefl j) ((h j hjs).2 hj)

end Surreal
