/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostClassification
public import GonshorBirthday.Surreal.Birthday.ReducedCostGap

import GonshorBirthday.Surreal.Birthday.CoefficientStep
import GonshorBirthday.Surreal.Birthday.LastMinusFamily
import GonshorBirthday.Surreal.Birthday.ReducedCostLower

/-!
# The unrestricted reduced omega-cost addition inequality

Induct on the natural sum of the input birthdays. At a prefix exhausting the product, one
input supplies arbitrarily late right prefixes below every output right option. The last
Cantor power locates the following plus block at a dyadic coefficient. Split that prefix
into two input prefixes and round on its grid. A nearby right option in the cofinal
input makes its contribution strictly smaller than the original last exponent.
-/

universe u
public noncomputable section
namespace Surreal

/-- A prefix after every original minus leaves exactly an appended plus block. -/
theorem eq_appendPluses_of_rightPrefixes_before (x : Surreal.{u}) {c : NatOrdinal.{u}}
    (hc : c < x.birthday) (hR : ∀ y ∈ rightPrefixes x, y.birthday < c) :
    x = appendPluses (birthdayTruncation x c) (x.birthday.val - c.val) := by
  have hzb := birthday_birthdayTruncation x hc.le
  have hz : birthdayTruncation x (birthdayTruncation x c).birthday = birthdayTruncation x c := by
    rw [hzb]
  apply ((appendPluses_eq_iff _ _ _).mpr ?_).symm
  constructor
  · rw [hzb, Ordinal.add_sub_cancel_of_le (NatOrdinal.val.monotone hc.le), NatOrdinal.of_val]
  · apply Set.Subset.antisymm
    · intro y hy
      apply mem_rightPrefixes_of_birthdayTruncation_eq_of_birthday_le hz hy
      · rw [hzb]
        exact (hR y hy).le
      · exact birthdayTruncation_lt (hR y hy) (mem_rightPrefixes_iff.mp hy).2
    · exact rightPrefixes_subset_of_birthdayTruncation_eq hz

/-- The next coefficient prefix needs the last Cantor exponent. One nearby upper
option gives a strict bound for this prefix at the original input cutoff. -/
private theorem not_full_prefix_of_cofinal_direction (a b d : Surreal.{u}) (hd : 0 < d)
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ t : Surreal.{u}, 0 < t → reducedOmegaCost (x + y + t) (x + y) ≤
        reducedOmegaCost (x + t) x * reducedOmegaCost (y + t) y)
    {c : NatOrdinal.{u}} (hc : c < (a + b).birthday) (hlim : Order.IsSuccLimit c.val)
    (hR : ∀ y ∈ rightPrefixes (a + b), y.birthday < c)
    (hcof : ∀ j < c, ∃ y ∈ rightPrefixes (birthdayTruncation (a + b) c),
      j < y.birthday ∧ y ≤ a + b + d)
    (hH : reducedOmegaCost (a + b + d) (birthdayTruncation (a + b) c) =
      reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b)
    (hdir : ∀ V ∈ rightPrefixes (birthdayTruncation (a + b) c),
      ∀ S < reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b,
        ∃ u ∈ rightPrefixes a, u ≤ a + d ∧ u + b ≤ V ∧
          S < reducedOmegaCost (a + d) u * reducedOmegaCost (b + d) b) : False := by
  let z := birthdayTruncation (a + b) c
  have hzb : z.birthday = c := birthday_birthdayTruncation (a + b) hc.le
  have hpre : birthdayTruncation (a + b) z.birthday = z := by rw [hzb]
  have hz := birthdayTruncation_mem_leftPrefixes_of_rightPrefixes_before (a + b) hc hR
  have hcofz : ∀ j < z.birthday, ∃ w ∈ rightPrefixes z, j < w.birthday ∧ w ≤ a + b + d := by
    simpa only [hzb] using hcof
  have hcpos : 0 < c := NatOrdinal.val.lt_iff_lt.mp (by
    simpa only [NatOrdinal.val_zero] using pos_iff_ne_zero.mpr (Ordinal.isSuccLimit_iff.mp hlim).1)
  obtain ⟨V₀, hV₀, _, _⟩ := hcof 0 hcpos
  have hproducts : ∀ S < reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b,
      ∃ u ∈ rightPrefixes a, u ≤ a + d ∧
        S < reducedOmegaCost (a + d) u * reducedOmegaCost (b + d) b := fun S hS ↦ by
    obtain ⟨u, hu, huA, _, hSu⟩ := hdir V₀ hV₀ S hS
    exact ⟨u, hu, huA, hSu⟩
  have hYpos := zero_lt_one.trans_le (one_le_reducedOmegaCost (b + d) b)
  obtain ⟨β, hY⟩ := exists_eq_wpow_of_retained_rightPrefix_products_cofinal hYpos.ne' hproducts
  have hcost := retained_rightPrefix_costs_cofinal_of_products (a + d) a hYpos hproducts
  have hcut : min (a + d + b) (a + (b + d)) = a + b + d := by
    rw [add_right_comm a d b, ← add_assoc, min_self]
  have hbelow (u : Surreal.{u}) (hu : u ∈ rightPrefixes a) (huA : u ≤ a + d) :
      ∃ w ∈ rightPrefixes z, w < u + b := by
    obtain ⟨w, hw, _, hwu⟩ := exists_retained_rightPrefix_lt_add_of_eq
      (le_add_of_nonneg_right hd.le) ih hpre (hcut ▸ hcofz) (hcut ▸ hH.ge) hu huA
    exact ⟨w, hw, hwu⟩
  obtain ⟨d', α, hd', hα, hX', hY', hflat, hV'⟩ :=
    exists_margin_at_final_powers hpre hcofz hH hcost hY hbelow
  have hβ : β ∈ NatOrdinal.cantorSupport (reducedOmegaCost (b + d) b) := by simp [hY]
  have hpB := plusCount_le_cantorSupport_reducedOmegaCost (b + d) b β hβ
  obtain ⟨L, hLmin, hLmax, hL⟩ := exists_lower_output_cutoff_of_leftPrefix hd'.le ih hz
  have hcheap : reducedOmegaCost L z < ω^ (α + β) := by
    rw [NatOrdinal.wpow_add]
    exact hL.trans_le (mul_le_mul' hX' hY')
  have hdel (w : Surreal.{u}) (hw : w ∈ rightPrefixes z) : z + d' < w := by
    apply lt_of_not_ge
    intro hwL
    exact hcheap.ne (hflat L hLmax ⟨w, hw, hwL.trans hLmin⟩)
  have hZ' := hflat _ le_rfl ⟨_, hV', le_rfl⟩
  have hcof' := retained_rightPrefixes_cofinal_of_retained hcofz hV' le_rfl
  obtain ⟨K, s, r, t, q, hK, hr, hq, hzK, hblock, hy, hcount, _⟩ :=
    exists_dyadic_prefix_of_final_power hZ' hpre hcof' hd' hdel hV'
  let y := K + (q : Surreal) * ω^ s
  change appendPluses z _ = y at hblock
  change birthdayTruncation (a + b) y.birthday = y at hy
  have hye : y ≤ a + b := by
    by_contra! h
    have hright := mem_rightPrefixes_iff.mpr ⟨hy, h⟩
    have hzy := birthday_birthdayTruncation_le_birthday y z.birthday
    have hzpre : birthdayTruncation y z.birthday = z := by
      rw [← hblock, birthdayTruncation_appendPluses]
    rw [hzpre, hzb] at hzy
    exact (hR y hright).not_ge hzy
  let c := t - (q.toRat : ℝ)
  have hW : y + (c : Surreal) * ω^ s ∈ rightPrefixes z := by
    rw [hzK]
    simpa only [y, Real.toSurreal_ratCast] using
      (right_gaps_at_coefficient_minus K s hK hr (q.toRat : ℝ)).2
  obtain ⟨u, hu, _, hsmall, _⟩ := hdir _ hW 0
    (mul_pos (zero_lt_one.trans_le (one_le_reducedOmegaCost (a + d) a)) hYpos)
  have hrq : r < (q.toRat : ℝ) := Real.toSurreal_lt_iff.mp (hq ▸ lt_appendPlus _)
  have hc : c < 1 := by
    dsimp only [c]
    linarith only [hrq, real_sub_le_one_of_eq_appendMinus hr]
  have hlt := plusCount_dyadic_sum_prefix_lt_of_right_gap q hK hy
    (retained_rightPrefixes_cofinal_of_costs_cofinal (a + d) a hcost) hα hc hu
    (by linarith only [hye, hsmall])
  exact (hcount.trans_lt (hlt.trans_le (add_le_add_right hpB α))).false

/-- The reduced cost of a sum, with cutoff a positive margin `d` above it, is at most the
natural product of the reduced costs of the summands with the same margin. -/
theorem reducedOmegaCost_add_common_margin_le (a b d : Surreal.{u}) (hd : 0 < d) :
    reducedOmegaCost (a + b + d) (a + b) ≤
      reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b := by
  have aux : ∀ μ : NatOrdinal.{u}, ∀ a b : Surreal.{u}, a.birthday + b.birthday = μ →
      ∀ d : Surreal.{u}, 0 < d → reducedOmegaCost (a + b + d) (a + b) ≤
        reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b := by
    intro μ
    induction μ using NatOrdinal.lt_wf.induction with
    | h μ ih =>
      intro a b hab d hd
      have ih' : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
          ∀ t : Surreal.{u}, 0 < t → reducedOmegaCost (x + y + t) (x + y) ≤
            reducedOmegaCost (x + t) x * reducedOmegaCost (y + t) y := by
        intro x y hxy
        exact ih _ (by simpa only [hab] using hxy) x y rfl
      by_contra hn
      have hfail := lt_of_not_ge hn
      obtain ⟨c, hc, hlim, hR, hcof, hH, _⟩ :=
        exists_limit_prefix_of_common_margin_failure a b d hd ih' hfail
      have hcut : min (a + d + b) (a + (b + d)) = a + b + d := by
        rw [add_right_comm a d b, ← add_assoc, min_self]
      let z := birthdayTruncation (a + b) c
      have hzb : z.birthday = c := birthday_birthdayTruncation (a + b) hc.le
      have hpre : birthdayTruncation (a + b) z.birthday = z := by rw [hzb]
      rcases rightPrefix_products_cofinal_at_all_gaps ih' hpre
          (by simpa only [hzb, hcut] using hcof) (hcut ▸ hH.ge) with h | h
      · exact not_full_prefix_of_cofinal_direction a b d hd ih' hc hlim hR hcof hH h
      · exact not_full_prefix_of_cofinal_direction b a d hd (by simpa only [add_comm] using ih')
          (by simpa only [add_comm] using hc) hlim (by simpa only [add_comm] using hR)
          (by simpa only [add_comm] using hcof) (by simpa only [add_comm, mul_comm] using hH)
          (by simpa only [z, add_comm, mul_comm] using h)
  exact aux _ a b rfl d hd

/-- The reduced cost of `a + b` with cutoff `min (A + b) (a + B)` is at most the natural
product of the reduced costs of `a` with cutoff `A` and of `b` with cutoff `B`. -/
theorem reducedOmegaCost_add_le (a b A B : Surreal.{u}) (ha : a ≤ A) (hb : b ≤ B) :
    reducedOmegaCost (min (A + b) (a + B)) (a + b) ≤
      reducedOmegaCost A a * reducedOmegaCost B b :=
  (reducedOmegaCost_add_iff_common_margin a b).mp
    (fun d hd ↦ reducedOmegaCost_add_common_margin_le a b d hd) A B ha hb

/-- A common boundary for an exponent sum gives the two translated input boundaries. -/
theorem reducedOmegaCost_add_at_le (a b C : Surreal.{u}) (h : a + b ≤ C) :
    reducedOmegaCost C (a + b) ≤ reducedOmegaCost (C - b) a * reducedOmegaCost (C - a) b := by
  have hb : b ≤ C - a := le_sub_iff_add_le.mpr (by rwa [add_comm])
  simpa only [sub_add_cancel, _root_.add_sub_cancel, min_self] using
    reducedOmegaCost_add_le a b (C - b) (C - a) (le_sub_iff_add_le.mpr h) hb

end Surreal
