/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Birthday.Basic
public import GonshorBirthday.Surreal.HahnSeries.Transfer

import GonshorBirthday.Surreal.Birthday.HeadCostComparison
import GonshorBirthday.Surreal.Birthday.HeadOmegaLength
import CombinatorialGames.Surreal.HahnSeries.Basic
import GonshorBirthday.Surreal.Birthday.HeadCoefficientLength
import GonshorBirthday.Surreal.Birthday.HeadCostPrefix
import GonshorBirthday.Surreal.Birthday.HeadCoefficientCost
import GonshorBirthday.Surreal.Birthday.SupportGap
import GonshorBirthday.Surreal.Birthday.NormalFormLength

/-!
# Coefficient comparison by induction on supported exponents

The induction controls the birthday through the initial monomial body at every
source exponent, including exponents whose target coefficient is zero.
-/

universe u
public noncomputable section
namespace Surreal
open Set

/-- Pointwise coefficient birthday comparison forces containment of supports. -/
theorem support_subset_of_birthday_coeff_le {x y : Surreal.{u}}
    (h : ∀ s : Surreal.{u}, (y.coeff s : Surreal.{u}).birthday ≤
      (x.coeff s : Surreal.{u}).birthday) : y.support ⊆ x.support := by
  intro s hs
  apply mem_support_iff.mpr
  intro hx
  have hh : (y.coeff s : Surreal.{u}).birthday ≤ 0 := by
    simpa only [hx, Real.toSurreal_zero, birthday_zero] using h s
  have hy0 := birthday_eq_zero.mp (le_antisymm hh zero_le)
  have hy : y.coeff s = 0 := Real.toSurreal_inj.{u}.mp
    (by simpa only [Real.toSurreal_zero] using hy0)
  exact mem_support_iff.mp hs hy

private theorem trunc_trunc_eq_of_lt {x s t : Surreal.{u}} (hst : s < t) :
    (x.normalFormTrunc s).normalFormTrunc t = x.normalFormTrunc t := by
  apply toHahnSeries_inj.mp
  rw [toHahnSeries_trunc, toHahnSeries_trunc, SurrealHahnSeries.trunc_trunc,
    max_eq_right hst.le, toHahnSeries_trunc]

private theorem body_le_completed {x s : Surreal.{u}} (hs : s ∈ x.support) :
    (x.normalFormTrunc s).birthday.val + (headOmegaCost (x.normalFormTrunc s) s).val ≤
      (x.normalFormTrunc s + (x.coeff s : Surreal) * ω^ s).birthday.val := by
  rw [birthday_trunc_add_coeff_mul_wpow, NatOrdinal.val_of,
    headCoefficientCost_of_ne_zero _ _ (mem_support_iff.mp hs), NatOrdinal.val_of,
    ← add_assoc]
  exact le_self_add

private theorem completed_le_of_body_le {x y s : Surreal.{u}}
    (hx : s ∈ x.support) (hy : s ∈ y.support)
    (hc : (y.coeff s : Surreal.{u}).birthday ≤ (x.coeff s : Surreal.{u}).birthday)
    (hb : (y.normalFormTrunc s).birthday.val + (headOmegaCost (y.normalFormTrunc s) s).val ≤
      (x.normalFormTrunc s).birthday.val + (headOmegaCost (x.normalFormTrunc s) s).val) :
    (y.normalFormTrunc s + (y.coeff s : Surreal) * ω^ s).birthday ≤
      (x.normalFormTrunc s + (x.coeff s : Surreal) * ω^ s).birthday := by
  rw [birthday_trunc_add_coeff_mul_wpow, birthday_trunc_add_coeff_mul_wpow,
    headCoefficientCost_of_ne_zero _ _ (mem_support_iff.mp hy),
    headCoefficientCost_of_ne_zero _ _ (mem_support_iff.mp hx), NatOrdinal.val_of,
    NatOrdinal.val_of, ← add_assoc, ← add_assoc]
  apply NatOrdinal.of.monotone
  apply add_le_add hb
  apply mul_le_mul_right
  exact Ordinal.sub_le.mpr ((NatOrdinal.val.monotone hc).trans (Ordinal.le_add_sub _ _))

/-- Coefficient birthday decrease controls the birthday through the monomial body
at every source exponent, even when its target coefficient is zero. -/
private theorem body_birthday_le_of_coeff_birthday_le {x y : Surreal.{u}}
    (hcoeff : ∀ s, (y.coeff s : Surreal.{u}).birthday ≤ (x.coeff s : Surreal.{u}).birthday)
    (s : Surreal.{u}) (hs : s ∈ x.support) :
    (y.normalFormTrunc s).birthday.val + (headOmegaCost (y.normalFormTrunc s) s).val ≤
      (x.normalFormTrunc s).birthday.val + (headOmegaCost (x.normalFormTrunc s) s).val := by
  classical
  have hsupport := support_subset_of_birthday_coeff_le hcoeff
  have all : ∀ s : x.support,
      (y.normalFormTrunc s).birthday.val + (headOmegaCost (y.normalFormTrunc s) s).val ≤
        (x.normalFormTrunc s).birthday.val + (headOmegaCost (x.normalFormTrunc s) s).val := by
    intro s
    induction s using (wellFounded_gt (α := x.support)).induction with
    | h s ih =>
      have hhead : (y.normalFormTrunc s).birthday ≤ (x.normalFormTrunc s).birthday := by
        apply (birthday_le_iff_trunc_add_coeff_wpow _ _).mpr
        intro v hv
        rw [support_trunc] at hv
        rw [trunc_trunc_eq_of_lt hv.2, coeff_trunc_of_lt hv.2]
        exact (completed_le_of_body_le (hsupport hv.1) hv.1 (hcoeff v)
          (ih ⟨v, hsupport hv.1⟩ hv.2)).trans (birthday_trunc_add_coeff_wpow_le_trunc hv.2)
      apply headOmegaCost_add_le_add_of_restored_prefixes _ _ _ _ _
        (NatOrdinal.val.monotone hhead)
      intro w hw hret hdel
      have hsw : (s : Surreal) < w := (mem_rightPrefixes_iff.mp hw).2
      by_cases hge : (x.normalFormTrunc s).support ⊆ Ici w
      · have hn : (x.coeff w : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0 := by
          have hf : ¬ ((x.normalFormTrunc s).coeff w : Surreal.{u}).birthday <
              NatOrdinal.of Ordinal.omega0 := fun h ↦ hdel ⟨hge, h⟩
          rw [coeff_trunc_of_lt hsw] at hf
          exact le_antisymm (birthday_real_le_omega0 _) (le_of_not_gt hf)
        have hwx : w ∈ x.support := by
          apply mem_support_iff.mpr
          intro hz
          rw [hz, Real.toSurreal_zero, birthday_zero] at hn
          exact (NatOrdinal.of.strictMono Ordinal.omega0_pos).ne
            (by simpa only [NatOrdinal.of_zero] using hn)
        have hf : (y.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 := by
          simpa only [coeff_trunc_of_lt hsw] using hret.2
        have he : y.normalFormTrunc s =
            y.normalFormTrunc w + (y.coeff w : Surreal) * ω^ w := by
          have hh := eq_trunc_add_coeff_wpow_of_support_ge hret.1
          rwa [trunc_trunc_eq_of_lt hsw, coeff_trunc_of_lt hsw] at hh
        have habs : (y.normalFormTrunc s).birthday.val +
            (headOmegaCost (y.normalFormTrunc s) w).val + (ω^ (plusCount w + 1)).val =
            ((y.normalFormTrunc w).birthday.val +
              (headOmegaCost (y.normalFormTrunc w) w).val) + (ω^ (plusCount w + 1)).val := by
          by_cases hy0 : y.coeff w = 0
          · rw [he, hy0, Real.toSurreal_zero, zero_mul, add_zero]
          · rw [he]
            exact birthday_head_real_mul_wpow_add_block _ _
              (by rw [support_trunc]; exact inter_subset_right) hy0 hf
        rw [habs]
        calc
          _ ≤ ((x.normalFormTrunc w).birthday.val +
              (headOmegaCost (x.normalFormTrunc w) w).val) + (ω^ (plusCount w + 1)).val :=
            _root_.add_le_add_left (ih ⟨w, hwx⟩ hsw) _
          _ = (x.normalFormTrunc w + (x.coeff w : Surreal) * ω^ w).birthday.val := by
            rw [birthday_trunc_add_coeff_mul_wpow, NatOrdinal.val_of,
              headCoefficientCost_nondyadic_tail hn]
            simp only [NatOrdinal.val_wpow, NatOrdinal.val_add_one,
              Ordinal.opow_add, Ordinal.opow_one, add_assoc]
          _ ≤ _ := NatOrdinal.val.monotone (birthday_trunc_add_coeff_wpow_le_trunc hsw)
      · obtain ⟨v, hv, hvw⟩ := Set.not_subset.mp hge
        have hvw' : v < w := lt_of_not_ge hvw
        rw [support_trunc] at hv
        have hwv : w ∈ rightPrefixes v := by
          apply mem_rightPrefixes_iff.mpr
          refine ⟨?_, hvw'⟩
          have ht := birthdayTruncation_eq_of_right_between
            (birthday_lt_of_mem_rightPrefixes hw).le hv.2.le
            (by simpa only [(mem_rightPrefixes_iff.mp hw).1] using hvw'.le)
          simpa only [(mem_rightPrefixes_iff.mp hw).1] using ht
        have he : y.normalFormTrunc s = y.normalFormTrunc v := by
          have ht : (y.normalFormTrunc s).normalFormTrunc v = y.normalFormTrunc s :=
            trunc_eq_self (fun z hz ↦ hvw'.trans_le (hret.1 hz))
          rw [trunc_trunc_eq_of_lt hv.2] at ht
          exact ht.symm
        have hblock : (headOmegaCost (y.normalFormTrunc s) w).val +
            (ω^ (plusCount w + 1)).val ≤ (headOmegaCost (y.normalFormTrunc s) v).val :=
          headOmegaCost_add_block_le_of_mem_rightPrefixes hwv hret
        calc
          _ ≤ (y.normalFormTrunc s).birthday.val +
              (headOmegaCost (y.normalFormTrunc s) v).val := by
            rw [add_assoc]
            exact (Ordinal.isNormal_add_right _).monotone hblock
          _ = (y.normalFormTrunc v).birthday.val +
              (headOmegaCost (y.normalFormTrunc v) v).val := by rw [he]
          _ ≤ (x.normalFormTrunc v).birthday.val +
              (headOmegaCost (x.normalFormTrunc v) v).val := ih ⟨v, hv.1⟩ hv.2
          _ ≤ (x.normalFormTrunc v + (x.coeff v : Surreal) * ω^ v).birthday.val :=
            body_le_completed hv.1
          _ ≤ _ := NatOrdinal.val.monotone (birthday_trunc_add_coeff_wpow_le_trunc hv.2)
  exact all ⟨s, hs⟩

/-- Coefficient birthday decrease bounds the truncation followed by its initial
monomial, including source exponents whose target coefficient is zero. -/
theorem birthday_trunc_add_wpow_le_of_coeff_birthday_le {x y : Surreal.{u}}
    (hcoeff : ∀ s, (y.coeff s : Surreal.{u}).birthday ≤ (x.coeff s : Surreal.{u}).birthday)
    (s : Surreal.{u}) (hs : s ∈ x.support) :
    (y.normalFormTrunc s + ω^ s).birthday ≤ (x.normalFormTrunc s + ω^ s).birthday := by
  rw [birthday_head_wpow _ _ (by rw [support_trunc]; exact inter_subset_right),
    birthday_head_wpow _ _ (by rw [support_trunc]; exact inter_subset_right)]
  exact NatOrdinal.of.monotone (body_birthday_le_of_coeff_birthday_le hcoeff s hs)

/-- Arbitrary coefficient birthday decreases cannot increase the surreal birthday. -/
theorem birthday_le_of_coeff_birthday_le {x y : Surreal.{u}}
    (hcoeff : ∀ s, (y.coeff s : Surreal.{u}).birthday ≤ (x.coeff s : Surreal.{u}).birthday) :
    y.birthday ≤ x.birthday := by
  apply (birthday_le_iff_trunc_add_coeff_wpow y x.birthday).mpr
  intro s hs
  have hsx := support_subset_of_birthday_coeff_le hcoeff hs
  exact (completed_le_of_body_le hsx hs (hcoeff s)
    (body_birthday_le_of_coeff_birthday_le hcoeff s hsx)).trans
    (birthday_trunc_add_coeff_wpow_le x s)

end Surreal
