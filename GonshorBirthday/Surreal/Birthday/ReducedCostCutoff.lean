/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostCofinality

import GonshorBirthday.NatOrdinal.OrderedSum
import GonshorBirthday.NatOrdinal.FinalPower
import Mathlib.SetTheory.Ordinal.Principal

/-!
# Reduced-cost tails under lowered cutoffs

A retained right prefix fixes every later retention decision. Cofinal retained
minuses also force each proper original plus rank strictly below every final
Cantor exponent of the full reduced cost.
-/

universe u

public noncomputable section

namespace Surreal

open Ordinal

/-- Among canonical right prefixes, a smaller value occurs strictly later. -/
theorem birthday_lt_of_rightPrefixes_lt {x y z : Surreal.{u}}
    (hy : y ∈ rightPrefixes x) (hz : z ∈ rightPrefixes x) (hzy : z < y) :
    y.birthday < z.birthday := by
  apply lt_of_not_ge
  intro h
  exact hzy.not_ge (rightPrefix_le_cutoff_of_birthday_le hz le_rfl hy h)

/-- A later canonical right prefix has at least the reduced cost of an earlier one. -/
theorem reducedOmegaCost_le_of_rightPrefixes_lt (D : Surreal.{u}) {x y z : Surreal.{u}}
    (hy : y ∈ rightPrefixes x) (hz : z ∈ rightPrefixes x) (hzy : z < y) :
    reducedOmegaCost D y ≤ reducedOmegaCost D z := by
  have hby := birthday_lt_of_rightPrefixes_lt hy hz hzy
  have ht : birthdayTruncation z y.birthday = y := by
    rw [← (mem_rightPrefixes_iff.mp hz).1,
      birthdayTruncation_birthdayTruncation x hby.le (birthday_lt_of_mem_rightPrefixes hz).le,
      (mem_rightPrefixes_iff.mp hy).1]
  simpa only [ht] using reducedOmegaCost_birthdayTruncation_le D z hby.le

/-- Once one right prefix survives a new cutoff, cofinal minus positions survive it. -/
theorem retained_rightPrefixes_cofinal_of_retained {C D x y : Surreal.{u}}
    (hcof : ∀ a < x.birthday, ∃ z ∈ rightPrefixes x, a < z.birthday ∧ z ≤ D)
    (hy : y ∈ rightPrefixes x) (hyC : y ≤ C) :
    ∀ a < x.birthday, ∃ z ∈ rightPrefixes x, a < z.birthday ∧ z ≤ C := by
  intro a ha
  obtain ⟨z, hz, haz, _, hzy⟩ := exists_retained_rightPrefix_lt_of_cofinal hcof hy ha
  exact ⟨z, hz, haz, hzy.le.trans hyC⟩

/-- Cofinal retained minuses put each proper prefix plus count below every final cost exponent. -/
theorem plusCount_prefix_lt_cantorSupport_of_retained_cofinal {C x : Surreal.{u}}
    (hcof : ∀ a < x.birthday, ∃ y ∈ rightPrefixes x, a < y.birthday ∧ y ≤ C)
    {a p : NatOrdinal.{u}} (ha : a < x.birthday)
    (hp : p ∈ NatOrdinal.cantorSupport (reducedOmegaCost C x)) :
    plusCount (birthdayTruncation x a) < p := by
  obtain ⟨y, hy, hay, hyC⟩ := hcof a ha
  let j : reducedOmegaPositions C x :=
    ⟨Ordinal.ToType.mk ⟨y.birthday.val,
      NatOrdinal.val.strictMono (birthday_lt_of_mem_rightPrefixes hy)⟩, by
      apply mem_reducedOmegaPositions.mpr
      right
      simpa only [Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val,
        (mem_rightPrefixes_iff.mp hy).1] using hyC⟩
  let q (i : reducedOmegaPositions C x) :=
    plusCount (birthdayTruncation x (NatOrdinal.of i.1.toOrd.1)) + 1
  have hbound : plusCount (birthdayTruncation x a) + 1 ≤ p := by
    rw [reducedOmegaCost_eq_positions, omegaExpansionLength_eq] at hp
    apply NatOrdinal.le_cantorSupport_of_type_sigma_wpow_tail q j
      (plusCount (birthdayTruncation x a) + 1) 1 ?_ p hp
    intro i hji
    have hyi : y.birthday ≤ NatOrdinal.of i.1.toOrd.1 := by
      have hi := NatOrdinal.of.monotone (Ordinal.ToType.mk.symm.monotone hji)
      simpa only [j, Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val] using hi
    have hai := hay.le.trans hyi
    have hix : NatOrdinal.of i.1.toOrd.1 ≤ x.birthday :=
      (NatOrdinal.of.strictMono i.1.toOrd.2).le
    have ha' : a ≤ (birthdayTruncation x (NatOrdinal.of i.1.toOrd.1)).birthday := by
      rw [birthday_birthdayTruncation x hix]
      exact hai
    have hpc := plusCount_birthdayTruncation_le
      (birthdayTruncation x (NatOrdinal.of i.1.toOrd.1)) ha'
    rw [birthdayTruncation_birthdayTruncation x hai hix] at hpc
    exact add_le_add hpc le_rfl
  exact (lt_add_one _).trans_le hbound

/-- Above a shared retained right prefix, lowering the cutoff leaves the entire tail unchanged. -/
theorem reducedOmegaCost_eq_prefix_add_old_tail {C D x y : Surreal.{u}}
    (hCD : C ≤ D) (hy : y ∈ rightPrefixes x) (hyC : y ≤ C) :
    reducedOmegaCost C x = NatOrdinal.of ((reducedOmegaCost C y).val +
      ((reducedOmegaCost D x).val - (reducedOmegaCost D y).val)) := by
  let r : x.birthday.val.ToType := Ordinal.ToType.mk
    ⟨y.birthday.val, NatOrdinal.val.strictMono (birthday_lt_of_mem_rightPrefixes hy)⟩
  have hr : NatOrdinal.of r.toOrd.1 = y.birthday := by
    simp only [r, Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val]
  have hCr : r ∈ reducedOmegaPositions C x := by
    apply mem_reducedOmegaPositions.mpr
    rw [hr, (mem_rightPrefixes_iff.mp hy).1]
    exact Or.inr hyC
  have hDr : r ∈ reducedOmegaPositions D x := by
    apply mem_reducedOmegaPositions.mpr
    rw [hr, (mem_rightPrefixes_iff.mp hy).1]
    exact Or.inr (hyC.trans hCD)
  let jC : reducedOmegaPositions C x := ⟨r, hCr⟩
  let jD : reducedOmegaPositions D x := ⟨r, hDr⟩
  let f : Set.Ici jC → Set.Ici jD := fun i ↦
    ⟨⟨i.1.1, by
      apply mem_reducedOmegaPositions.mpr
      exact (mem_reducedOmegaPositions.mp i.1.2).imp_right (fun h ↦ h.trans hCD)⟩, i.2⟩
  have hf : StrictMono f := fun _ _ h ↦ h
  have honto : Function.Surjective f := by
    intro i
    have hri : y.birthday ≤ NatOrdinal.of i.1.1.toOrd.1 := by
      have h := NatOrdinal.of.monotone (Ordinal.ToType.mk.symm.monotone i.2)
      simpa only [jD, r, Ordinal.ToType.toOrd, OrderIso.symm_apply_apply,
        NatOrdinal.of_val] using h
    have hiC : i.1.1 ∈ reducedOmegaPositions C x := by
      apply mem_reducedOmegaPositions.mpr
      right
      apply birthdayTruncation_le_cutoff_of_rightPrefix_le (C := C) hri
        (NatOrdinal.of.strictMono i.1.1.toOrd.2).le
      · rw [(mem_rightPrefixes_iff.mp hy).1]
        exact (mem_rightPrefixes_iff.mp hy).2
      · rwa [(mem_rightPrefixes_iff.mp hy).1]
    exact ⟨⟨⟨i.1.1, hiC⟩, i.2⟩, rfl⟩
  let e : Set.Ici jC ≃o Set.Ici jD :=
    OrderIso.ofSurjective (OrderEmbedding.ofStrictMono f hf) honto
  let W (i : Set.Ici jC) :=
    (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of i.1.1.toOrd.1)) + 1)).val.ToType
  let V (i : Set.Ici jD) :=
    (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of i.1.1.toOrd.1)) + 1)).val.ToType
  have he : typeLT (Σₗ i, W i) = typeLT (Σₗ i, V i) := by
    apply Ordinal.type_sigma_congr W V e
    intro i
    rfl
  have hC := reducedOmegaCost_eq_prefix_add_tail C x jC
  have hD := reducedOmegaCost_eq_prefix_add_tail D x jD
  change reducedOmegaCost C x = NatOrdinal.of
    ((reducedOmegaCost C (birthdayTruncation x (NatOrdinal.of r.toOrd.1))).val +
      typeLT (Σₗ i, W i)) at hC
  change reducedOmegaCost D x = NatOrdinal.of
    ((reducedOmegaCost D (birthdayTruncation x (NatOrdinal.of r.toOrd.1))).val +
      typeLT (Σₗ i, V i)) at hD
  rw [hr, (mem_rightPrefixes_iff.mp hy).1, he] at hC
  rw [hr, (mem_rightPrefixes_iff.mp hy).1] at hD
  rw [hD, NatOrdinal.val_of, Ordinal.add_sub_cancel]
  exact hC

/-- A nonempty retained-minus family has a first original position. -/
theorem exists_first_retained_rightPrefix {C x : Surreal.{u}}
    (hne : ∃ y ∈ rightPrefixes x, y ≤ C) :
    ∃ y ∈ rightPrefixes x, y ≤ C ∧
      ∀ z ∈ rightPrefixes x, z ≤ C → y.birthday ≤ z.birthday := by
  let S : Set NatOrdinal.{u} := {a | ∃ y ∈ rightPrefixes x, y ≤ C ∧ y.birthday = a}
  have hS : S.Nonempty := by
    obtain ⟨y, hy, hyC⟩ := hne
    exact ⟨y.birthday, y, hy, hyC, rfl⟩
  obtain ⟨a, ha, hmin⟩ := NatOrdinal.lt_wf.has_min S hS
  obtain ⟨y, hy, hyC, hya⟩ := ha
  refine ⟨y, hy, hyC, ?_⟩
  intro z hz hzC
  rw [hya]
  exact le_of_not_gt (hmin z.birthday ⟨z, hz, hzC, rfl⟩)

/-- Deleting all minuses before a final power leaves exactly that power if one minus remains. -/
theorem reducedOmegaCost_eq_wpow_of_cutoff_final {C D x : Surreal.{u}}
    {X₀ p : NatOrdinal.{u}} (hCD : C ≤ D)
    (hfinal : reducedOmegaCost D x = NatOrdinal.of (X₀.val + (ω^ p).val))
    (hhead : ∀ y ∈ rightPrefixes x, y ≤ C → X₀ ≤ reducedOmegaCost D y)
    (hrank : ∀ y ∈ rightPrefixes x, y ≤ C → plusCount y < p)
    (hne : ∃ y ∈ rightPrefixes x, y ≤ C) : reducedOmegaCost C x = ω^ p := by
  obtain ⟨y, hy, hyC, hfirst⟩ := exists_first_retained_rightPrefix hne
  have hbase : reducedOmegaCost C y = ω^ plusCount y := by
    apply reducedOmegaCost_eq_wpow_of_no_retained_rightPrefixes
    intro z hz hzC
    have hz' := rightPrefixes_subset_of_birthdayTruncation_eq (mem_rightPrefixes_iff.mp hy).1 hz
    exact (birthday_lt_of_mem_rightPrefixes hz).not_ge (hfirst z hz' hzC)
  have hlt : reducedOmegaCost D y < NatOrdinal.of (X₀.val + (ω^ p).val) := by
    rw [← hfinal]
    exact reducedOmegaCost_lt_of_mem_rightPrefixes hy (hyC.trans hCD)
  have htail := NatOrdinal.final_wpow_osub (hhead y hy hyC) hlt
  have he := reducedOmegaCost_eq_prefix_add_old_tail hCD hy hyC
  rw [hbase, hfinal, NatOrdinal.val_of] at he
  have ht : (X₀.val + (ω^ p).val) - (reducedOmegaCost D y).val = (ω^ p).val :=
    congrArg NatOrdinal.val htail
  rw [ht, NatOrdinal.val_wpow, NatOrdinal.val_wpow] at he
  have hsmall : (ω^ plusCount y).val < Ordinal.omega0 ^ p.val := by
    simpa only [NatOrdinal.val_wpow] using
      NatOrdinal.val.strictMono (NatOrdinal.wpow_lt_wpow.mpr (hrank y hy hyC))
  rw [NatOrdinal.val_wpow] at hsmall
  rw [Ordinal.add_omega0_opow hsmall, NatOrdinal.of_omega0_opow, NatOrdinal.of_val] at he
  exact he

/-- If all newly retained minuses start in the old final power, the lowered cost is at most it. -/
theorem reducedOmegaCost_le_wpow_of_cutoff_final {C D x : Surreal.{u}}
    {X₀ p : NatOrdinal.{u}} (hCD : C ≤ D)
    (hfinal : reducedOmegaCost D x = NatOrdinal.of (X₀.val + (ω^ p).val))
    (hhead : ∀ y ∈ rightPrefixes x, y ≤ C → X₀ ≤ reducedOmegaCost D y)
    (hrank : ∀ y ∈ rightPrefixes x, y ≤ C → plusCount y < p)
    (hbase : plusCount x ≤ p) : reducedOmegaCost C x ≤ ω^ p := by
  by_cases hne : ∃ y ∈ rightPrefixes x, y ≤ C
  · exact (reducedOmegaCost_eq_wpow_of_cutoff_final hCD hfinal hhead hrank hne).le
  · rw [reducedOmegaCost_eq_wpow_of_no_retained_rightPrefixes C x
      (fun y hy hyC ↦ hne ⟨y, hy, hyC⟩)]
    exact NatOrdinal.wpow_le_wpow.mpr hbase

end Surreal
