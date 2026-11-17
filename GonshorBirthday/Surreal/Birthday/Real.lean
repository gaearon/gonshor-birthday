/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Dyadic
public import GonshorBirthday.Surreal.Birthday.Prefix
public import CombinatorialGames.Surreal.Real

/-!
# Exact birthday alternatives for real coefficients
-/

universe u
public noncomputable section
namespace Surreal
open Set Order

/-- A nonzero real contributes at least its first sign. -/
theorem one_le_birthday_real {r : ℝ} (hr : r ≠ 0) : 1 ≤ (r : Surreal.{u}).birthday :=
  NatOrdinal.one_le_iff_ne_zero.mpr fun h ↦
    hr (Real.toSurreal_eq_zero_iff.mp (birthday_eq_zero.mp h))

/-- Every real number is born by the first infinite birthday. -/
theorem birthday_real_le_omega0 (r : ℝ) :
    (r : Surreal.{u}).birthday ≤ NatOrdinal.of Ordinal.omega0 := by
  rw [← mk_real_toIGame]
  apply (birthday_mk_le _).trans
  rw [Real.toIGame, IGame.birthday_ofSets]
  apply max_le
  all_goals
    apply csSup_le'
    rintro _ ⟨q, ⟨q, hq, rfl⟩, rfl⟩
    exact Order.add_one_le_of_lt (IGame.Short.birthday_lt_omega0 (q : IGame.{u}))

/-- A real has finite birthday exactly when it is a dyadic real. -/
theorem birthday_real_lt_omega0_iff (r : ℝ) :
    (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 ↔
      r ∈ Set.range (fun q : Dyadic ↦ (q.toRat : ℝ)) := by
  rw [birthday_lt_omega0_iff]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    apply Real.toSurreal_inj.mp
    simpa only [Real.toSurreal_ratCast] using hq
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    have ht := congrArg (fun t : ℝ ↦ (t : Surreal.{u})) hq
    simpa only [Real.toSurreal_ratCast] using ht

/-- A nondyadic real has exactly the first infinite birthday. -/
theorem birthday_real_eq_omega0_iff (r : ℝ) :
    (r : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0 ↔
      r ∉ Set.range (fun q : Dyadic ↦ (q.toRat : ℝ)) := by
  rw [← birthday_real_lt_omega0_iff]
  constructor
  · intro h
    rw [h]
    exact lt_irrefl _
  · intro h
    exact (birthday_real_le_omega0 r).lt_or_eq.resolve_left h

/-- Every proper canonical prefix of an embedded real is an actual dyadic. -/
theorem birthdayTruncation_real_mem_range_dyadic (r : ℝ) {a : NatOrdinal.{u}}
    (ha : a < (r : Surreal.{u}).birthday) :
    birthdayTruncation (r : Surreal) a ∈ Set.range ((↑) : Dyadic → Surreal.{u}) := by
  apply birthday_lt_omega0_iff.mp
  rw [birthday_birthdayTruncation _ ha.le]
  exact ha.trans_le (birthday_real_le_omega0 r)

/-- Every canonical truncation of a real remains an embedded real. -/
theorem birthdayTruncation_real_mem_range_real (r : ℝ) (a : NatOrdinal.{u}) :
    birthdayTruncation (r : Surreal.{u}) a ∈ Set.range ((↑) : ℝ → Surreal.{u}) := by
  by_cases ha : a < (r : Surreal.{u}).birthday
  · obtain ⟨q, hq⟩ := birthdayTruncation_real_mem_range_dyadic r ha
    refine ⟨(q.toRat : ℝ), ?_⟩
    simpa only [Real.toSurreal_ratCast] using hq
  · rw [birthdayTruncation_eq_self_of_birthday_le _ (le_of_not_gt ha)]
    exact ⟨r, rfl⟩


end Surreal
