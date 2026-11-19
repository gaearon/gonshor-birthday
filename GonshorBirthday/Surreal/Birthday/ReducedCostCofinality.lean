/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostReduction

import GonshorBirthday.Surreal.Birthday.Addition
import GonshorBirthday.NatOrdinal.FinalPower

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

/-- Cofinal retained-prefix product costs force the other nonzero factor to be a pure power. -/
theorem exists_eq_wpow_of_retained_rightPrefix_products_cofinal {C x : Surreal.{u}}
    {Y : NatOrdinal.{u}} (hY : Y ≠ 0)
    (hprod : ∀ S < reducedOmegaCost C x * Y, ∃ y ∈ rightPrefixes x,
      y ≤ C ∧ S < reducedOmegaCost C y * Y) : ∃ p, Y = ω^ p := by
  have hx : reducedOmegaCost C x ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le (one_le_reducedOmegaCost C x))
  apply NatOrdinal.exists_eq_wpow_of_products_cofinal hx hY
  intro S hS
  obtain ⟨y, hy, hyC, hSy⟩ := hprod S hS
  exact ⟨reducedOmegaCost C y, reducedOmegaCost_lt_of_mem_rightPrefixes hy hyC, hSy.le⟩

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

/-- If a prefix uses the entire product, one input supplies arbitrarily expensive right
prefixes below every prescribed right option of the output. The same input works for all
these options, and all costs use the original cutoffs. -/
theorem rightPrefix_products_cofinal_at_all_gaps {a b A B z : Surreal.{u}}
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ d : Surreal.{u}, 0 < d → reducedOmegaCost (x + y + d) (x + y) ≤
        reducedOmegaCost (x + d) x * reducedOmegaCost (y + d) y)
    (hz : birthdayTruncation (a + b) z.birthday = z)
    (hcof : ∀ j < z.birthday, ∃ v ∈ rightPrefixes z,
      j < v.birthday ∧ v ≤ min (A + b) (a + B))
    (hH : reducedOmegaCost A a * reducedOmegaCost B b ≤
      reducedOmegaCost (min (A + b) (a + B)) z) :
    (∀ V ∈ rightPrefixes z, ∀ S < reducedOmegaCost A a * reducedOmegaCost B b,
      ∃ u ∈ rightPrefixes a, u ≤ A ∧ u + b ≤ V ∧
        S < reducedOmegaCost A u * reducedOmegaCost B b) ∨
    (∀ U ∈ rightPrefixes z, ∀ T < reducedOmegaCost A a * reducedOmegaCost B b,
      ∃ v ∈ rightPrefixes b, v ≤ B ∧ a + v ≤ U ∧
        T < reducedOmegaCost A a * reducedOmegaCost B v) := by
  have below {a b A B : Surreal.{u}}
      (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
        ∀ d : Surreal.{u}, 0 < d → reducedOmegaCost (x + y + d) (x + y) ≤
          reducedOmegaCost (x + d) x * reducedOmegaCost (y + d) y)
      (hp : birthdayTruncation (a + b) z.birthday = z)
      (hpos : ∀ j < z.birthday, ∃ w ∈ rightPrefixes z, j < w.birthday ∧ w ≤ min (A + b) (a + B))
      (hmax : reducedOmegaCost A a * reducedOmegaCost B b ≤
        reducedOmegaCost (min (A + b) (a + B)) z)
      (hdir : ∀ w ∈ rightPrefixes (a + b), ∃ u ∈ rightPrefixes a, u + b ≤ w)
      (V : Surreal.{u}) (hV : V ∈ rightPrefixes z) (S : NatOrdinal.{u})
      (hS : S < reducedOmegaCost A a * reducedOmegaCost B b) :
      ∃ u ∈ rightPrefixes a, u ≤ A ∧ u + b ≤ V ∧
        S < reducedOmegaCost A u * reducedOmegaCost B b := by
    obtain ⟨w, hw, hwC, hcost⟩ := retained_rightPrefix_costs_cofinal_of_positions
      (bot_le.trans_lt (birthday_lt_of_mem_rightPrefixes hV)) hpos S (hS.trans_le hmax)
    have hmin : min w V ∈ rightPrefixes z :=
      (min_choice w V).elim (fun e ↦ e.symm ▸ hw) (fun e ↦ e.symm ▸ hV)
    obtain ⟨u, hu, h⟩ := hdir _ (rightPrefixes_subset_of_birthdayTruncation_eq hp hmin)
    obtain ⟨huA, hb⟩ := rightPrefix_cost_le_of_add_le ih hu
      (rightPrefixes_subset_of_birthdayTruncation_eq hp hw) (h.trans (min_le_left _ _)) hwC
    exact ⟨u, hu, huA, h.trans (min_le_right _ _), hcost.trans_le hb⟩
  rcases rightPrefixes_add_coinitial a b with h | h
  · exact Or.inl (below ih hz hcof hH h)
  · right
    simpa only [add_comm, mul_comm] using below (a := b) (b := a) (A := B) (B := A)
      (by simpa only [add_comm] using ih) (by simpa only [add_comm] using hz)
      (by simpa only [add_comm, min_comm] using hcof)
      (by simpa only [add_comm, min_comm, mul_comm] using hH)
      (by simpa only [add_comm] using h)

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

end Surreal
