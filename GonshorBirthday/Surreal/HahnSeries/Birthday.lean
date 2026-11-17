/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.HahnSeries.NormalForm
public import GonshorBirthday.Surreal.Birthday.Prefix

/-!
# Normal-form truncations as canonical birthday prefixes

A normal-form truncation is the simplest member of a cut fitted by the whole series.
Consequently it is its intrinsic birthday-indexed canonical prefix.
-/

universe u

public noncomputable section

namespace SurrealHahnSeries

/-- Truncating a normal form gives a canonical prefix of the whole surreal. -/
theorem birthdayTruncation_truncIdx (x : SurrealHahnSeries.{u}) (i : Ordinal.{u}) :
    Surreal.birthdayTruncation x.toSurreal (x.truncIdx i).toSurreal.birthday =
      (x.truncIdx i).toSurreal := by
  have h := (fits_ofSets_truncLT_truncGT x i).birthdayTruncation_eq
  simpa only [mk_toIGame, ← toSurreal_eq'] using h

/-- Exponent truncation gives the corresponding canonical birthday prefix. -/
theorem birthdayTruncation_trunc (x : SurrealHahnSeries.{u}) (s : Surreal.{u}) :
    Surreal.birthdayTruncation x.toSurreal (x.trunc s).toSurreal.birthday =
      (x.trunc s).toSurreal := by
  obtain ⟨i, hi⟩ := trunc_mem_range_truncIdx x s
  rw [← hi]
  exact birthdayTruncation_truncIdx x i

end SurrealHahnSeries
