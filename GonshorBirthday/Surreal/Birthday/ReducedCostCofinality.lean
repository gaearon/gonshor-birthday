/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostReduction

import GonshorBirthday.Surreal.Birthday.Addition

/-!
# Directional cofinality of retained prefix costs

At equality, one input's retained-prefix product costs are cofinal in the
whole product budget. Its retained minus positions are consequently cofinal
in its entire word. No single retained addition option bounds all retained
output right prefixes from below.
-/

universe u

public noncomputable section

namespace Surreal

/-- Cofinal retained right prefixes eventually lie below any specified right prefix. -/
theorem exists_retained_rightPrefix_lt_of_cofinal {C x v : Surreal.{u}}
    (hcof : ∀ a < x.birthday, ∃ y ∈ rightPrefixes x, a < y.birthday ∧ y ≤ C)
    (hv : v ∈ rightPrefixes x) {a : NatOrdinal.{u}} (ha : a < x.birthday) :
    ∃ y ∈ rightPrefixes x, a < y.birthday ∧ y ≤ C ∧ y < v := by
  obtain ⟨y, hy, hby, hyC⟩ := hcof (max a v.birthday)
    (max_lt ha (birthday_lt_of_mem_rightPrefixes hv))
  have hva : v.birthday < y.birthday := (le_max_right a v.birthday).trans_lt hby
  have hyv := birthdayTruncation_lt hva (mem_rightPrefixes_iff.mp hv).2
  rw [(mem_rightPrefixes_iff.mp hy).1] at hyv
  exact ⟨y, hy, (le_max_left a v.birthday).trans_lt hby, hyC, hyv⟩

/-- A retained output prefix is paid by an actual retained prefix in one input direction. -/
theorem exists_retained_rightPrefix_mul_bound_of_smaller {a b A B v : Surreal.{u}}
    (ha : a ≤ A) (hb : b ≤ B)
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
  rcases exists_rightPrefixes_add_le hv with ⟨w, hw, hwv⟩ | ⟨w, hw, hwv⟩
  · have hwA : w ≤ A := by
      have h := hwv.trans (hvC.trans (min_le_left _ _))
      simpa only [add_le_add_iff_right] using h
    have hi := (reducedOmegaCost_add_iff_common_margin w b).mp
      (ih w b (add_lt_add_of_lt_of_le (birthday_lt_of_mem_rightPrefixes hw) le_rfl))
      A B hwA hb
    exact Or.inl ⟨w, hw, hwA, reducedOmegaCost_rightPrefix_add_le hw hv hwv hi⟩
  · have hwB : w ≤ B := by
      have h := hwv.trans (hvC.trans (min_le_right _ _))
      simpa only [add_le_add_iff_left] using h
    have hi := (reducedOmegaCost_add_iff_common_margin w a).mp
      (ih w a (by
        simpa only [add_comm] using
          add_lt_add_of_lt_of_le (birthday_lt_of_mem_rightPrefixes hw)
            (le_refl a.birthday))) B A hwB ha
    have hv' : v ∈ rightPrefixes (b + a) := by simpa only [add_comm] using hv
    have hwv' : w + a ≤ v := by simpa only [add_comm] using hwv
    refine Or.inr ⟨w, hw, hwB, ?_⟩
    simpa only [add_comm, min_comm, mul_comm] using
      reducedOmegaCost_rightPrefix_add_le hw hv' hwv' hi

/-- Cofinal retained-prefix costs force their original minus positions to be cofinal too. -/
theorem retained_rightPrefixes_cofinal_of_costs_cofinal (C x : Surreal.{u})
    (hcost : ∀ S < reducedOmegaCost C x, ∃ y ∈ rightPrefixes x,
      y ≤ C ∧ S < reducedOmegaCost C y) :
    ∀ a < x.birthday, ∃ y ∈ rightPrefixes x, a < y.birthday ∧ y ≤ C := by
  obtain ⟨y, hy, hyC, _⟩ := hcost 0
    (zero_lt_one.trans_le (one_le_reducedOmegaCost C x))
  intro a ha
  by_contra hn
  have hbound : ∀ z ∈ rightPrefixes x, z ≤ C → z.birthday ≤ a := by
    intro z hz hzC
    exact le_of_not_gt (fun h ↦ hn ⟨z, hz, h, hzC⟩)
  have hr : birthdayTruncation x a < x ∨ birthdayTruncation x a ≤ C := by
    by_cases hl : birthdayTruncation x a < x
    · exact Or.inl hl
    have hne : birthdayTruncation x a ≠ x := by
      intro he
      have he' := birthday_birthdayTruncation x ha.le
      rw [he] at he'
      exact ha.ne he'.symm
    have hz : birthdayTruncation x a ∈ rightPrefixes x :=
      mem_rightPrefixes.mpr ⟨a, ha, rfl, lt_of_le_of_ne (le_of_not_gt hl) hne.symm⟩
    apply Or.inr
    apply rightPrefix_le_cutoff_of_birthday_le hy hyC hz
    rw [birthday_birthdayTruncation x ha.le]
    exact hbound y hy hyC
  obtain ⟨z, hz, hzC, hcostz⟩ := hcost _ (reducedOmegaCost_birthdayTruncation_lt C x ha hr)
  have hza : z.birthday ≤ a := hbound z hz hzC
  have ht : birthdayTruncation (birthdayTruncation x a) z.birthday = z := by
    rw [birthdayTruncation_birthdayTruncation x hza ha.le, (mem_rightPrefixes_iff.mp hz).1]
  have hba : z.birthday ≤ (birthdayTruncation x a).birthday := by
    rw [birthday_birthdayTruncation x ha.le]
    exact hza
  have hb := reducedOmegaCost_birthdayTruncation_le C (birthdayTruncation x a) hba
  rw [ht] at hb
  exact hcostz.not_ge hb

/-- Cofinal retained minus positions make their prefix costs cofinal in the whole cost. -/
theorem retained_rightPrefix_costs_cofinal_of_positions {C x : Surreal.{u}}
    (hx : 0 < x.birthday)
    (hcof : ∀ a < x.birthday, ∃ y ∈ rightPrefixes x, a < y.birthday ∧ y ≤ C) :
    ∀ S < reducedOmegaCost C x, ∃ y ∈ rightPrefixes x,
      y ≤ C ∧ S < reducedOmegaCost C y := by
  intro S hS
  by_contra hn
  have hbound : ∀ y ∈ rightPrefixes x, y ≤ C → reducedOmegaCost C y ≤ S := by
    intro y hy hyC
    exact le_of_not_gt (fun h ↦ hn ⟨y, hy, hyC, h⟩)
  have hone : 1 ≤ S := by
    obtain ⟨y, hy, _, hyC⟩ := hcof 0 hx
    exact (one_le_reducedOmegaCost C y).trans (hbound y hy hyC)
  exact hS.not_ge (reducedOmegaCost_le_of_cofinal_rightPrefixes C x S hone hcof hbound)

/-- Cofinal retained-prefix costs give a nonzero limit cost. -/
theorem isSuccLimit_reducedOmegaCost_of_costs_cofinal (C x : Surreal.{u})
    (hcost : ∀ S < reducedOmegaCost C x, ∃ y ∈ rightPrefixes x,
      y ≤ C ∧ S < reducedOmegaCost C y) :
    Order.IsSuccLimit (reducedOmegaCost C x).val := by
  rcases reducedOmegaCost_eq_one_or_isSuccLimit C x with he | hl
  · obtain ⟨y, hy, hyC, _⟩ := hcost 0
      (zero_lt_one.trans_le (one_le_reducedOmegaCost C x))
    have h := (one_le_reducedOmegaCost C y).trans_lt
      (reducedOmegaCost_lt_of_mem_rightPrefixes hy hyC)
    rw [he] at h
    exact False.elim (lt_irrefl _ h)
  · exact hl

/-- Cofinality of the products implies cofinality of the first factor's retained-prefix costs. -/
theorem retained_rightPrefix_costs_cofinal_of_products (C x : Surreal.{u})
    {Y : NatOrdinal.{u}} (hY : 0 < Y)
    (hprod : ∀ S < reducedOmegaCost C x * Y, ∃ y ∈ rightPrefixes x,
      y ≤ C ∧ S < reducedOmegaCost C y * Y) :
    ∀ S < reducedOmegaCost C x, ∃ y ∈ rightPrefixes x,
      y ≤ C ∧ S < reducedOmegaCost C y := by
  intro S hS
  obtain ⟨y, hy, hyC, hp⟩ := hprod (S * Y) (mul_lt_mul_of_pos_right hS hY)
  refine ⟨y, hy, hyC, lt_of_not_ge ?_⟩
  intro hyS
  exact hp.not_ge (mul_le_mul' hyS le_rfl)

/-- Equality at an output limit forces retained-prefix product cofinality in one input. -/
theorem retained_rightPrefix_products_cofinal_or_of_eq {a b A B z : Surreal.{u}}
    (ha : a ≤ A) (hb : b ≤ B)
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ d : Surreal.{u}, 0 < d → reducedOmegaCost (x + y + d) (x + y) ≤
        reducedOmegaCost (x + d) x * reducedOmegaCost (y + d) y)
    (hz : birthdayTruncation (a + b) z.birthday = z) (hzpos : 0 < z.birthday)
    (hcof : ∀ c < z.birthday, ∃ v ∈ rightPrefixes z,
      c < v.birthday ∧ v ≤ min (A + b) (a + B))
    (hH : reducedOmegaCost A a * reducedOmegaCost B b ≤
      reducedOmegaCost (min (A + b) (a + B)) z) :
    (∀ S < reducedOmegaCost A a * reducedOmegaCost B b,
      ∃ w ∈ rightPrefixes a, w ≤ A ∧ S < reducedOmegaCost A w * reducedOmegaCost B b) ∨
    (∀ S < reducedOmegaCost A a * reducedOmegaCost B b,
      ∃ w ∈ rightPrefixes b, w ≤ B ∧ S < reducedOmegaCost A a * reducedOmegaCost B w) := by
  classical
  by_contra hn
  rcases not_or.mp hn with ⟨hnA, hnB⟩
  push Not at hnA hnB
  obtain ⟨S, hS, hSA⟩ := hnA
  obtain ⟨T, hT, hTB⟩ := hnB
  have hbound : ∀ v ∈ rightPrefixes z, v ≤ min (A + b) (a + B) →
      reducedOmegaCost (min (A + b) (a + B)) v ≤ max S T := by
    intro v hv hvC
    have hv' := rightPrefixes_subset_of_birthdayTruncation_eq hz hv
    rcases exists_retained_rightPrefix_mul_bound_of_smaller ha hb ih hv' hvC with
      ⟨w, hw, hwA, hcost⟩ | ⟨w, hw, hwB, hcost⟩
    · exact hcost.trans ((hSA w hw hwA).trans (le_max_left S T))
    · exact hcost.trans ((hTB w hw hwB).trans (le_max_right S T))
  have hone : 1 ≤ max S T := by
    obtain ⟨v, hv, _, hvC⟩ := hcof 0 hzpos
    exact (one_le_reducedOmegaCost _ v).trans (hbound v hv hvC)
  have hcost := reducedOmegaCost_le_of_cofinal_rightPrefixes
    (min (A + b) (a + B)) z (max S T) hone hcof hbound
  exact (max_lt hS hT).not_ge (hH.trans hcost)

/-- At equality, a retained addition option has a retained output right prefix strictly below it. -/
theorem exists_retained_rightPrefix_lt_add_of_eq {a b A B z w : Surreal.{u}}
    (hb : b ≤ B)
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ d : Surreal.{u}, 0 < d → reducedOmegaCost (x + y + d) (x + y) ≤
        reducedOmegaCost (x + d) x * reducedOmegaCost (y + d) y)
    (hz : birthdayTruncation (a + b) z.birthday = z)
    (hcof : ∀ c < z.birthday, ∃ v ∈ rightPrefixes z,
      c < v.birthday ∧ v ≤ min (A + b) (a + B))
    (hH : reducedOmegaCost A a * reducedOmegaCost B b ≤
      reducedOmegaCost (min (A + b) (a + B)) z)
    (hw : w ∈ rightPrefixes a) (hwA : w ≤ A) :
    ∃ v ∈ rightPrefixes z, v ≤ min (A + b) (a + B) ∧ v < w + b := by
  by_contra hn
  have hi := (reducedOmegaCost_add_iff_common_margin w b).mp
    (ih w b (add_lt_add_of_lt_of_le (birthday_lt_of_mem_rightPrefixes hw) le_rfl))
    A B hwA hb
  have hone : 1 ≤ reducedOmegaCost A w * reducedOmegaCost B b := by
    simpa only [one_mul] using mul_le_mul' (one_le_reducedOmegaCost A w)
      (one_le_reducedOmegaCost B b)
  have hcost : reducedOmegaCost (min (A + b) (a + B)) z ≤
      reducedOmegaCost A w * reducedOmegaCost B b := by
    apply reducedOmegaCost_le_of_cofinal_rightPrefixes _ z _ hone hcof
    intro v hv hvC
    have hwv : w + b ≤ v := le_of_not_gt (fun h ↦ hn ⟨v, hv, hvC, h⟩)
    exact reducedOmegaCost_rightPrefix_add_le hw
      (rightPrefixes_subset_of_birthdayTruncation_eq hz hv) hwv hi
  have hstrict := mul_lt_mul_of_pos_right (reducedOmegaCost_lt_of_mem_rightPrefixes hw hwA)
    (zero_lt_one.trans_le (one_le_reducedOmegaCost B b))
  exact hstrict.not_ge (hH.trans hcost)

/-- The fixed-witness exclusion holds arbitrarily late and strictly below the old cutoff. -/
theorem exists_later_retained_rightPrefix_lt_add_of_eq {a b A B z w : Surreal.{u}}
    (hb : b ≤ B)
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ d : Surreal.{u}, 0 < d → reducedOmegaCost (x + y + d) (x + y) ≤
        reducedOmegaCost (x + d) x * reducedOmegaCost (y + d) y)
    (hz : birthdayTruncation (a + b) z.birthday = z)
    (hcof : ∀ c < z.birthday, ∃ v ∈ rightPrefixes z,
      c < v.birthday ∧ v ≤ min (A + b) (a + B))
    (hH : reducedOmegaCost A a * reducedOmegaCost B b ≤
      reducedOmegaCost (min (A + b) (a + B)) z)
    (hw : w ∈ rightPrefixes a) (hwA : w ≤ A)
    {c : NatOrdinal.{u}} (hc : c < z.birthday) :
    ∃ v ∈ rightPrefixes z, c < v.birthday ∧
      v < min (A + b) (a + B) ∧ v < w + b := by
  obtain ⟨v, hv, hvC, hvw⟩ :=
    exists_retained_rightPrefix_lt_add_of_eq hb ih hz hcof hH hw hwA
  obtain ⟨v', hv', hcv', _, hv'v⟩ := exists_retained_rightPrefix_lt_of_cofinal hcof hv hc
  exact ⟨v', hv', hcv', hv'v.trans_le hvC, hv'v.trans hvw⟩

end Surreal
