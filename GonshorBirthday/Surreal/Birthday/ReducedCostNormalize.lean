/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostPure
public import GonshorBirthday.Surreal.Birthday.ReducedCostCutoff

import GonshorBirthday.NatOrdinal.FinalPower
import GonshorBirthday.Surreal.Birthday.Addition
import Mathlib.Tactic.Abel

/-!
# Normalization by an actual smaller common margin

Moving the output cutoff to a later canonical right prefix removes the lower
Cantor terms of both input budgets while preserving a hypothetical failure.
-/

universe u

public noncomputable section

namespace Surreal

/-- A cofinal input direction and pure opposite factor can be normalized at a smaller margin. -/
theorem exists_smaller_margin_pure_costs_of_cofinal_direction
    (a b d : Surreal.{u}) (hd : 0 < d)
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ t : Surreal.{u}, 0 < t → reducedOmegaCost (x + y + t) (x + y) ≤
        reducedOmegaCost (x + t) x * reducedOmegaCost (y + t) y)
    {c β : NatOrdinal.{u}} (hc : c < (a + b).birthday) (hlim : Order.IsSuccLimit c.val)
    (hR : ∀ y ∈ rightPrefixes (a + b), y.birthday < c)
    (hcof : ∀ e < c, ∃ v ∈ rightPrefixes (birthdayTruncation (a + b) c),
      e < v.birthday ∧ v ≤ a + b + d)
    (hH : reducedOmegaCost (a + b + d) (birthdayTruncation (a + b) c) =
      reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b)
    (hXcof : ∀ S < reducedOmegaCost (a + d) a, ∃ w ∈ rightPrefixes a,
      w ≤ a + d ∧ S < reducedOmegaCost (a + d) w)
    (hY : reducedOmegaCost (b + d) b = ω^ β) :
    ∃ d' : Surreal.{u}, ∃ α : NatOrdinal.{u}, 0 < d' ∧ d' < d ∧ 0 < α ∧
      reducedOmegaCost (a + d') a = ω^ α ∧
      reducedOmegaCost (b + d') b = ω^ β ∧
      reducedOmegaCost (a + b + d') (birthdayTruncation (a + b) c) = ω^ (α + β) ∧
      reducedOmegaCost (a + d') a * reducedOmegaCost (b + d') b <
        reducedOmegaCost (a + b + d') (a + b) := by
  let z := birthdayTruncation (a + b) c
  have hzb : z.birthday = c := birthday_birthdayTruncation (a + b) hc.le
  have hz : birthdayTruncation (a + b) z.birthday = z := by rw [hzb]
  have hzpos : 0 < z.birthday := by
    rw [hzb]
    exact NatOrdinal.val.lt_iff_lt.mp (by
      simpa only [NatOrdinal.val_zero] using
        (pos_iff_ne_zero.mpr (Ordinal.isSuccLimit_iff.mp hlim).1))
  have hcofz : ∀ e < z.birthday, ∃ v ∈ rightPrefixes z,
      e < v.birthday ∧ v ≤ a + b + d := by simpa only [hzb] using hcof
  have hXlim := isSuccLimit_reducedOmegaCost_of_costs_cofinal (a + d) a hXcof
  obtain ⟨X₀, α, hα, hX, hXadd, hαleast⟩ :=
    NatOrdinal.exists_final_wpow_of_isSuccLimit hXlim
  have hXsum : reducedOmegaCost (a + d) a = X₀ + ω^ α := hX.trans hXadd
  let H₀ := X₀ * ω^ β
  have hHsum : reducedOmegaCost (a + b + d) z = H₀ + ω^ (α + β) := by
    rw [hH, hY, hXsum, add_mul, ← NatOrdinal.wpow_add]
  have hX₀support : ∀ e ∈ NatOrdinal.cantorSupport X₀, α ≤ e := by
    intro e he
    apply hαleast.2
    change e ∈ NatOrdinal.cantorSupport (reducedOmegaCost (a + d) a)
    rw [hXsum, NatOrdinal.cantorSupport_add]
    exact Finset.mem_union.mpr (Or.inl he)
  have hH₀support : ∀ e ∈ NatOrdinal.cantorSupport H₀, α + β ≤ e := by
    apply NatOrdinal.le_cantorSupport_mul hX₀support
    intro e he
    rw [NatOrdinal.cantorSupport_wpow, Finset.mem_singleton] at he
    exact he.ge
  have hHfinal : reducedOmegaCost (a + b + d) z =
      NatOrdinal.of (H₀.val + (ω^ (α + β)).val) :=
    hHsum.trans (NatOrdinal.of_oadd_wpow_of_le_cantorSupport hH₀support).symm
  have hpA : plusCount a ≤ α :=
    plusCount_le_cantorSupport_reducedOmegaCost (a + d) a α hαleast.1
  have hpB : plusCount b ≤ β := by
    have h := plusCount_le_cantorSupport_reducedOmegaCost (b + d) b
    rw [hY] at h
    exact h β (by simp only [NatOrdinal.cantorSupport_wpow, Finset.mem_singleton])
  have hpz : plusCount z < α + β := by
    have hlt := (reducedOmegaCost_eq_prefix_add_wpow_of_rightPrefixes_before
      (a + b + d) (a + b) hc hR).1
    exact hlt.trans_le ((plusCount_add_le a b).trans (add_le_add hpA hpB))
  have hXcofpos := retained_rightPrefixes_cofinal_of_costs_cofinal (a + d) a hXcof
  have hX₀lt : X₀ < reducedOmegaCost (a + d) a := by
    rw [hXsum]
    exact lt_add_of_pos_right X₀ (NatOrdinal.wpow_pos α)
  obtain ⟨u₀, hu₀, hu₀A, hXu₀⟩ := hXcof X₀ hX₀lt
  have hH₀lt : H₀ < reducedOmegaCost (a + b + d) z := by
    rw [hHsum]
    exact lt_add_of_pos_right H₀ (NatOrdinal.wpow_pos (α + β))
  obtain ⟨v₀, hv₀, hv₀C, hHv₀⟩ :=
    retained_rightPrefix_costs_cofinal_of_positions hzpos hcofz H₀ hH₀lt
  have hcut : min (a + d + b) (a + (b + d)) = a + b + d := by
    rw [add_right_comm a d b, ← add_assoc, min_self]
  obtain ⟨v₁, hv₁, hv₀v₁, hv₁C, hv₁u₀⟩ :=
    exists_later_retained_rightPrefix_lt_add_of_eq
      (le_add_of_nonneg_right hd.le) ih hz
      (by simpa only [hcut] using hcofz)
      (by simpa only [hcut] using hH.ge) hu₀ hu₀A
      (birthday_lt_of_mem_rightPrefixes hv₀)
  rw [hcut] at hv₁C
  have hv₁v₀ : v₁ < v₀ := by
    have h := birthdayTruncation_lt hv₀v₁ (mem_rightPrefixes_iff.mp hv₀).2
    rwa [(mem_rightPrefixes_iff.mp hv₁).1] at h
  have hv₁e := (mem_rightPrefixes_iff.mp
    (rightPrefixes_subset_of_birthdayTruncation_eq hz hv₁)).2
  let d' := v₁ - (a + b)
  have hd' : 0 < d' := sub_pos.mpr hv₁e
  have hd'd : d' < d := by
    exact (sub_lt_iff_lt_add).mpr (by simpa only [add_comm] using hv₁C)
  have hnewC : a + b + d' = v₁ := by dsimp only [d']; abel
  have hnewA : a + d' < u₀ := by
    apply (add_lt_add_iff_right b).mp
    have he : a + d' + b = v₁ := by dsimp only [d']; abel
    rwa [he]
  have hCmono : v₁ ≤ a + b + d := hv₁C.le
  have hAmono : a + d' ≤ a + d := add_le_add le_rfl hd'd.le
  have hBmono : b + d' ≤ b + d := add_le_add le_rfl hd'd.le
  have hZnew : reducedOmegaCost v₁ z = ω^ (α + β) := by
    apply reducedOmegaCost_eq_wpow_of_cutoff_final hCmono hHfinal
    · intro y hy hyv₁
      exact hHv₀.le.trans (reducedOmegaCost_le_of_rightPrefixes_lt (a + b + d)
        hv₀ hy (hyv₁.trans_lt hv₁v₀))
    · intro y hy _
      have hb := (birthday_lt_of_mem_rightPrefixes hy).le
      have hp := plusCount_birthdayTruncation_le z hb
      rw [(mem_rightPrefixes_iff.mp hy).1] at hp
      exact hp.trans_lt hpz
    · exact ⟨v₁, hv₁, le_rfl⟩
  have hAnew : reducedOmegaCost (a + d') a ≤ ω^ α := by
    apply reducedOmegaCost_le_wpow_of_cutoff_final hAmono hX
    · intro y hy hyC
      exact hXu₀.le.trans (reducedOmegaCost_le_of_rightPrefixes_lt (a + d)
        hu₀ hy (hyC.trans_lt hnewA))
    · intro y hy _
      have h := plusCount_prefix_lt_cantorSupport_of_retained_cofinal hXcofpos
        (birthday_lt_of_mem_rightPrefixes hy) hαleast.1
      simpa only [(mem_rightPrefixes_iff.mp hy).1] using h
    · exact hpA
  have hBnew : reducedOmegaCost (b + d') b ≤ ω^ β := by
    rw [← hY]
    exact reducedOmegaCost_mono b hBmono
  have hcofnew := retained_rightPrefixes_cofinal_of_retained hcofz hv₁
    (show v₁ ≤ v₁ from le_rfl)
  have hcut' : min (a + d' + b) (a + (b + d')) = v₁ := by
    rw [add_right_comm a d' b, ← add_assoc, min_self, hnewC]
  have hlower : ω^ (α + β) ≤ reducedOmegaCost (a + d') a * reducedOmegaCost (b + d') b := by
    rw [← hZnew]
    refine reducedOmegaCost_le_of_cofinal_rightPrefixes _ z _ ?_ hcofnew ?_
    · simpa only [one_mul] using mul_le_mul' (one_le_reducedOmegaCost _ _)
        (one_le_reducedOmegaCost _ _)
    · intro v hv hvC
      have h := reducedOmegaCost_rightPrefix_add_le_of_smaller
        (le_add_of_nonneg_right hd'.le) (le_add_of_nonneg_right hd'.le) ih
        (rightPrefixes_subset_of_birthdayTruncation_eq hz hv)
        (by rwa [hcut'])
      simpa only [hcut'] using h
  have hprod : reducedOmegaCost (a + d') a * reducedOmegaCost (b + d') b = ω^ (α + β) := by
    apply le_antisymm ?_ hlower
    rw [NatOrdinal.wpow_add]
    exact mul_le_mul' hAnew hBnew
  have hAeq : reducedOmegaCost (a + d') a = ω^ α := by
    apply hAnew.antisymm
    apply le_of_not_gt
    intro hlt
    have h := (mul_le_mul' le_rfl hBnew).trans_lt
      (mul_lt_mul_of_pos_right hlt (NatOrdinal.wpow_pos β))
    rw [hprod, ← NatOrdinal.wpow_add] at h
    exact lt_irrefl _ h
  have hBeq : reducedOmegaCost (b + d') b = ω^ β := by
    apply hBnew.antisymm
    apply le_of_not_gt
    intro hlt
    have h : reducedOmegaCost (a + d') a * reducedOmegaCost (b + d') b < ω^ α * ω^ β := by
      rw [hAeq]
      exact mul_lt_mul_of_pos_left hlt (NatOrdinal.wpow_pos α)
    rw [hprod, ← NatOrdinal.wpow_add] at h
    exact lt_irrefl _ h
  refine ⟨d', α, hd', hd'd, hα, hAeq, hBeq, ?_, ?_⟩
  · rwa [hnewC]
  · have he := (reducedOmegaCost_eq_prefix_add_wpow_of_rightPrefixes_before
      v₁ (a + b) hc hR).2
    rw [hnewC, he, hprod, hZnew]
    exact NatOrdinal.of.strictMono (lt_add_of_pos_right _ (NatOrdinal.wpow_pos _))

/-- Every minimal common-margin failure persists at a smaller margin with both input costs pure. -/
theorem exists_smaller_margin_pure_costs_of_common_margin_failure
    (a b d : Surreal.{u}) (hd : 0 < d)
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ t : Surreal.{u}, 0 < t → reducedOmegaCost (x + y + t) (x + y) ≤
        reducedOmegaCost (x + t) x * reducedOmegaCost (y + t) y)
    (hfail : reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b <
      reducedOmegaCost (a + b + d) (a + b)) :
    ∃ d' : Surreal.{u}, ∃ α β : NatOrdinal.{u},
      0 < d' ∧ d' < d ∧ (0 < α ∨ 0 < β) ∧
      reducedOmegaCost (a + d') a = ω^ α ∧
      reducedOmegaCost (b + d') b = ω^ β ∧
      reducedOmegaCost (a + d') a * reducedOmegaCost (b + d') b <
        reducedOmegaCost (a + b + d') (a + b) := by
  obtain ⟨c, hc, hlim, hR, hcof, hH, _⟩ :=
    exists_limit_prefix_of_common_margin_failure a b d hd ih hfail
  rcases pure_factor_or_of_common_margin_failure a b d hd ih hfail with
    ⟨β, hY, _, hXcof⟩ | ⟨α, hX, _, hYcof⟩
  · obtain ⟨d', α, hd', hd'd, hα, hA, hB, _, hfail'⟩ :=
      exists_smaller_margin_pure_costs_of_cofinal_direction a b d hd ih
        hc hlim hR hcof hH hXcof hY
    exact ⟨d', α, β, hd', hd'd, Or.inl hα, hA, hB, hfail'⟩
  · have ih' : ∀ x y : Surreal.{u}, x.birthday + y.birthday < b.birthday + a.birthday →
        ∀ t : Surreal.{u}, 0 < t → reducedOmegaCost (x + y + t) (x + y) ≤
          reducedOmegaCost (x + t) x * reducedOmegaCost (y + t) y := by
      simpa only [add_comm] using ih
    obtain ⟨d', β, hd', hd'd, hβ, hB, hA, _, hfail'⟩ :=
      exists_smaller_margin_pure_costs_of_cofinal_direction b a d hd ih'
        (by simpa only [add_comm] using hc) hlim
        (by simpa only [add_comm] using hR)
        (by simpa only [add_comm] using hcof)
        (by simpa only [add_comm, mul_comm] using hH) hYcof hX
    refine ⟨d', α, β, hd', hd'd, Or.inr hβ, hA, hB, ?_⟩
    simpa only [add_comm, mul_comm] using hfail'

end Surreal
