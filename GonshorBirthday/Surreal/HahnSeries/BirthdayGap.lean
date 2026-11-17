/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.HahnSeries.BirthdayAdd

/-!
# Lower bounds for gaps from younger surreals to normal-form heads

If every exponent of `x` is at least `s`, a surreal of strictly smaller birthday cannot differ
from `x` only on a scale below `ω^s`. A smaller-scale perturbation would have `x` as a normal-form
partial sum, hence as a canonical prefix, forcing its birthday to be at least that of `x`.

The conclusion applies to every younger surreal, including every proper canonical prefix.
No normal-form sign-expansion theorem is used.
-/

universe u

public noncomputable section

namespace Surreal

open Set

/-- A normal-form partial sum is the corresponding intrinsic canonical prefix. -/
theorem PartialSum.birthdayTruncation_eq {x : Surreal.{u}} (y : PartialSum x) :
    birthdayTruncation x y.carrier.toSurreal.birthday = y.carrier.toSurreal := by
  obtain ⟨s, hs⟩ := y.mem_range_trunc
  rw [← hs]
  exact birthdayTruncation_trunc x s

/-- Adding a term below the entire support preserves the original canonical prefix. -/
theorem birthdayTruncation_add_of_support_lt {x y : Surreal.{u}}
    (hs : x.support ⊆ Ioi y.wlog) :
    birthdayTruncation (x + y) x.birthday = x := by
  simpa only [PartialSum.carrier_ofAdd, toSurreal_toHahnSeries] using
    (PartialSum.ofAdd x y hs).birthdayTruncation_eq

/-- A younger surreal has a gap at least as large in scale as some actual support exponent. -/
theorem exists_support_le_wlog_sub_of_birthday_lt {x p : Surreal.{u}}
    (hp : p.birthday < x.birthday) : ∃ s ∈ x.support, s ≤ (p - x).wlog := by
  by_contra hn
  push Not at hn
  have hpre : birthdayTruncation p x.birthday = x := by
    have hs : x.support ⊆ Ioi (p - x).wlog := fun s hs ↦ hn s hs
    simpa only [← add_sub_assoc, add_sub_cancel_left] using
      birthdayTruncation_add_of_support_lt hs
  have hb : x.birthday ≤ p.birthday := by
    rw [← hpre]
    exact birthday_birthdayTruncation_le_birthday p _
  exact hp.not_ge hb

/-- A younger surreal differs from a normal-form head at or above its lowest allowed scale. -/
theorem le_wlog_sub_of_birthday_lt {x p s : Surreal.{u}}
    (hs : x.support ⊆ Ici s) (hp : p.birthday < x.birthday) :
    s ≤ (p - x).wlog := by
  by_contra hn
  have hg : (p - x).wlog < s := lt_of_not_ge hn
  have hpre : birthdayTruncation p x.birthday = x := by
    have hh : x.support ⊆ Ioi (p - x).wlog := fun j hj ↦ hg.trans_le (hs hj)
    simpa only [← add_sub_assoc, add_sub_cancel_left] using
      birthdayTruncation_add_of_support_lt hh
  have hb : x.birthday ≤ p.birthday := by
    rw [← hpre]
    exact birthday_birthdayTruncation_le_birthday p _
  exact hp.not_ge hb

/-- A smaller monomial is infinitesimal relative to the gap from any younger surreal. -/
theorem wpow_vlt_sub_of_birthday_lt {x p s w : Surreal.{u}}
    (hs : x.support ⊆ Ici s) (hp : p.birthday < x.birthday) (hw : w < s) :
    ω^ w <ᵥ p - x := by
  have hne : p - x ≠ 0 := by
    intro h
    have hh := congrArg birthday (sub_eq_zero.mp h)
    exact hp.ne hh
  rw [← wlog_lt_wlog_iff (wpow_ne_zero _) hne, wlog_wpow]
  exact hw.trans_le (le_wlog_sub_of_birthday_lt hs hp)

/-- Every finite multiple of a smaller monomial is less than the gap from a younger surreal. -/
theorem natCast_mul_wpow_lt_abs_sub_of_birthday_lt {x p s w : Surreal.{u}}
    (hs : x.support ⊆ Ici s) (hp : p.birthday < x.birthday) (hw : w < s) (n : ℕ) :
    n * ω^ w < |p - x| := by
  have h := (ArchimedeanClass.mk_lt_mk.mp
    (vlt_def.mp (wpow_vlt_sub_of_birthday_lt hs hp hw))) n
  simpa only [wpow_abs, nsmul_eq_mul] using h

end Surreal
