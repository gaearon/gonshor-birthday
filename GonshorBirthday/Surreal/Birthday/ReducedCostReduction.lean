/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostEndpoint
public import GonshorBirthday.Surreal.Birthday.ReducedCostBudget

import GonshorBirthday.Surreal.Birthday.Addition

/-!
# Reduction to equality at a proper sign limit

Completed right-prefix estimates exclude a last retained minus. Their cofinal
endpoint is a limit prefix, followed by a nonempty original plus portion. Any
strict reserve in the input budget pays that portion, so a failure forces equality.
-/

universe u

public noncomputable section

namespace Surreal

open Ordinal

/-- A failure with completed-prefix bounds forces equality at a proper limit prefix. -/
theorem exists_limit_prefix_of_reducedOmegaCost_gt (C x : Surreal.{u}) (M : NatOrdinal.{u})
    (hbase : ω^ plusCount x ≤ M)
    (hsupport : ∀ p ∈ NatOrdinal.cantorSupport M, plusCount x ≤ p)
    (hbudget : ∀ y ∈ rightPrefixes x, y ≤ C →
      NatOrdinal.of ((reducedOmegaCost C y).val + (ω^ (plusCount y + 1)).val +
        if plusCount y < plusCount x then (ω^ plusCount x).val else 0) ≤ M)
    (hfail : M < reducedOmegaCost C x) :
    ∃ a : NatOrdinal.{u}, a < x.birthday ∧ Order.IsSuccLimit a.val ∧
      (∀ y ∈ rightPrefixes x, y.birthday < a) ∧
      (∀ b < a, ∃ y ∈ rightPrefixes (birthdayTruncation x a), b < y.birthday ∧ y ≤ C) ∧
      reducedOmegaCost C (birthdayTruncation x a) = M ∧
      plusCount (birthdayTruncation x a) < plusCount x ∧
      reducedOmegaCost C x = NatOrdinal.of (M.val + (ω^ plusCount x).val) := by
  have hne : ∃ y ∈ rightPrefixes x, y ≤ C := by
    by_contra hn
    have he := reducedOmegaCost_eq_wpow_of_no_retained_rightPrefixes C x
      (fun y hy hyC ↦ hn ⟨y, hy, hyC⟩)
    rw [he] at hfail
    exact hfail.not_ge hbase
  have hnext : ∀ y ∈ rightPrefixes x, y ≤ C →
      ∃ z ∈ rightPrefixes x, z ≤ C ∧ y.birthday < z.birthday := by
    intro y hy hyC
    by_contra hn
    have hlast : ∀ z ∈ rightPrefixes x, z ≤ C → z.birthday ≤ y.birthday := by
      intro z hz hzC
      exact le_of_not_gt (fun hlt ↦ hn ⟨z, hz, hzC, hlt⟩)
    have he := reducedOmegaCost_eq_of_last_retained_rightPrefix hy hyC hlast
    have hb := hbudget y hy hyC
    rw [← he] at hb
    exact hfail.not_ge hb
  let R := {i : x.birthday.val.ToType |
    x < birthdayTruncation x (NatOrdinal.of i.toOrd.1) ∧
      birthdayTruncation x (NatOrdinal.of i.toOrd.1) ≤ C}
  let a : NatOrdinal.{u} := NatOrdinal.of (⨆ i : R, i.1.toOrd.1 + 1)
  have ha : a ≤ x.birthday := by
    apply NatOrdinal.of.monotone
    exact Ordinal.iSup_le (fun i ↦ Order.add_one_le_iff.mpr i.1.toOrd.2)
  let pos (y : Surreal.{u}) (hy : y ∈ rightPrefixes x) (hyC : y ≤ C) : R :=
    ⟨Ordinal.ToType.mk ⟨y.birthday.val,
      NatOrdinal.val.strictMono (birthday_lt_of_mem_rightPrefixes hy)⟩, by
        change _ ∧ _
        simpa only [Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val,
          (mem_rightPrefixes_iff.mp hy).1] using ⟨(mem_rightPrefixes_iff.mp hy).2, hyC⟩⟩
  have hia (i : R) : NatOrdinal.of i.1.toOrd.1 < a := by
    apply NatOrdinal.of.strictMono
    exact (lt_add_one i.1.toOrd.1).trans_le (Ordinal.le_iSup _ i)
  have hret : ∀ y ∈ rightPrefixes x, y ≤ C → y.birthday < a := by
    intro y hy hyC
    simpa only [pos, Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val] using
      hia (pos y hy hyC)
  have hR : ∀ y ∈ rightPrefixes x, y.birthday < a :=
    rightPrefixes_birthday_lt_of_retained_bounded hne hret
  have hcof : ∀ b < a, ∃ y ∈ rightPrefixes x, b < y.birthday ∧ y ≤ C := by
    intro b hb
    have hb' : b.val < ⨆ i : R, i.1.toOrd.1 + 1 := by
      simpa only [a, NatOrdinal.val_of] using NatOrdinal.val.strictMono hb
    obtain ⟨i, hbi⟩ := Ordinal.lt_iSup_iff.mp hb'
    have hi : NatOrdinal.of i.1.toOrd.1 < x.birthday := NatOrdinal.of.strictMono i.1.toOrd.2
    have hRi : birthdayTruncation x (NatOrdinal.of i.1.toOrd.1) ∈ rightPrefixes x :=
      mem_rightPrefixes.mpr ⟨_, hi, rfl, i.2.1⟩
    obtain ⟨y, hy, hyC, hiy⟩ := hnext _ hRi i.2.2
    refine ⟨y, hy, ?_, hyC⟩
    have hb_le : b ≤ NatOrdinal.of i.1.toOrd.1 := by
      simpa only [NatOrdinal.of_val] using NatOrdinal.of.monotone
        (Order.lt_add_one_iff.mp hbi)
    rw [birthday_birthdayTruncation x hi.le] at hiy
    exact hb_le.trans_lt hiy
  have hpos : 0 < a := by
    obtain ⟨y, hy, hyC⟩ := hne
    exact (bot_le : (0 : NatOrdinal.{u}) ≤ y.birthday).trans_lt (hret y hy hyC)
  have hlim : Order.IsSuccLimit a.val := by
    rw [Ordinal.isSuccLimit_iff, Order.isSuccPrelimit_iff_succ_lt]
    constructor
    · simpa only [NatOrdinal.val_zero] using ne_of_gt (NatOrdinal.val.strictMono hpos)
    · intro b hb
      have hb' : NatOrdinal.of b < a := by
        simpa only [NatOrdinal.of_val] using NatOrdinal.of.strictMono hb
      obtain ⟨y, hy, hby, hyC⟩ := hcof _ hb'
      have hby' : b < y.birthday.val := by
        simpa only [NatOrdinal.val_of] using NatOrdinal.val.strictMono hby
      exact (Order.succ_le_of_lt hby').trans_lt (NatOrdinal.val.strictMono (hret y hy hyC))
  have hcofz : ∀ b < a, ∃ y ∈ rightPrefixes (birthdayTruncation x a),
      b < y.birthday ∧ y ≤ C := by
    intro b hb
    obtain ⟨y, hy, hby, hyC⟩ := hcof b hb
    refine ⟨y, ?_, hby, hyC⟩
    apply mem_rightPrefixes_iff.mpr
    constructor
    · rw [birthdayTruncation_birthdayTruncation x (hR y hy).le ha,
        (mem_rightPrefixes_iff.mp hy).1]
    · exact (birthdayTruncation_lt_iff ha (hR y hy)).mpr (mem_rightPrefixes_iff.mp hy).2
  have hprefix : ∀ y ∈ rightPrefixes x, y ≤ C → reducedOmegaCost C y ≤ M := by
    intro y hy hyC
    apply le_trans ?_ (hbudget y hy hyC)
    apply NatOrdinal.val.le_iff_le.mp
    rw [NatOrdinal.val_of]
    exact (le_self_add : (reducedOmegaCost C y).val ≤
      (reducedOmegaCost C y).val + (ω^ (plusCount y + 1)).val).trans le_self_add
  have hM : 1 ≤ M := by
    apply le_trans ?_ hbase
    calc
      (1 : NatOrdinal.{u}) = ω^ (0 : NatOrdinal.{u}) := NatOrdinal.wpow_zero.symm
      _ ≤ ω^ plusCount x := NatOrdinal.wpow_le_wpow.mpr bot_le
  have hHM : reducedOmegaCost C (birthdayTruncation x a) ≤ M := by
    apply reducedOmegaCost_le_of_cofinal_rightPrefixes C (birthdayTruncation x a) M hM
    · simpa only [birthday_birthdayTruncation x ha] using hcofz
    · intro y hy hyC
      apply hprefix y ?_ hyC
      apply rightPrefixes_subset_of_birthdayTruncation_eq ?_ hy
      rw [birthday_birthdayTruncation x ha]
  have ha' : a < x.birthday := by
    apply ha.lt_of_ne
    intro he
    rw [he, birthdayTruncation_birthday] at hHM
    exact hfail.not_ge hHM
  obtain ⟨hp, he⟩ := reducedOmegaCost_eq_prefix_add_wpow_of_rightPrefixes_before C x ha' hR
  have hEq : reducedOmegaCost C (birthdayTruncation x a) = M := by
    apply hHM.antisymm
    apply le_of_not_gt
    intro hlt
    have h := NatOrdinal.oadd_wpow_le_of_lt_of_le_cantorSupport hlt hsupport
    rw [← he] at h
    exact hfail.not_ge h
  refine ⟨a, ha', hlim, hR, hcofz, hEq, hp, ?_⟩
  rwa [hEq] at he

/-- A minimal common-margin failure has a proper limit prefix exhausting the input budget. -/
theorem exists_limit_prefix_of_common_margin_failure (a b d : Surreal.{u}) (hd : 0 < d)
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ t : Surreal.{u}, 0 < t → reducedOmegaCost (x + y + t) (x + y) ≤
        reducedOmegaCost (x + t) x * reducedOmegaCost (y + t) y)
    (hfail : reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b <
      reducedOmegaCost (a + b + d) (a + b)) :
    ∃ c : NatOrdinal.{u}, c < (a + b).birthday ∧ Order.IsSuccLimit c.val ∧
      (∀ y ∈ rightPrefixes (a + b), y.birthday < c) ∧
      (∀ e < c, ∃ y ∈ rightPrefixes (birthdayTruncation (a + b) c),
        e < y.birthday ∧ y ≤ a + b + d) ∧
      reducedOmegaCost (a + b + d) (birthdayTruncation (a + b) c) =
        reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b ∧
      plusCount (birthdayTruncation (a + b) c) < plusCount (a + b) ∧
      reducedOmegaCost (a + b + d) (a + b) = NatOrdinal.of
        ((reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b).val +
          (ω^ plusCount (a + b)).val) := by
  apply exists_limit_prefix_of_reducedOmegaCost_gt (a + b + d) (a + b) _ ?_ ?_ ?_ hfail
  · simpa only [reducedOmegaCost_self_eq_wpow] using
      reducedOmegaCost_add_self_le a b (a + d) (b + d)
  · intro p hp
    exact (plusCount_add_le a b).trans (NatOrdinal.le_cantorSupport_mul
      (plusCount_le_cantorSupport_reducedOmegaCost (a + d) a)
      (plusCount_le_cantorSupport_reducedOmegaCost (b + d) b) p hp)
  · intro y hy hyC
    have hcut : min (a + d + b) (a + (b + d)) = a + b + d := by
      rw [add_right_comm a d b, ← add_assoc, min_self]
    have h := reducedOmegaCost_rightPrefix_add_budget_of_smaller
      (le_add_of_nonneg_right hd.le) (le_add_of_nonneg_right hd.le) ih hy
      (by rwa [hcut])
    simpa only [hcut] using h

end Surreal
