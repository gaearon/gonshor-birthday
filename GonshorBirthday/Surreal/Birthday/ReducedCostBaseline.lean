/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostCutoff
public import GonshorBirthday.Surreal.Birthday.Minus

/-!
# Cofinal signs at the reduced-cost baseline

When retained minuses are cofinal and the reduced cost equals its plus-only
baseline, plus positions must be cofinal too. In particular, such a word has
no nonempty final constant-sign block. A cofinal family of deleted right
prefixes also forces every right prefix to be deleted.
-/

universe u

public noncomputable section

namespace Surreal

/-- With cofinal retained minuses, a last Cantor exponent equal to the plus count
forces pluses to occur cofinally as well. -/
theorem leftPrefixes_cofinal_of_plusCount_mem_support {C x : Surreal.{u}}
    (hsupport : plusCount x ∈ NatOrdinal.cantorSupport (reducedOmegaCost C x))
    (hcof : ∀ a < x.birthday, ∃ y ∈ rightPrefixes x, a < y.birthday ∧ y ≤ C) :
    ∀ a < x.birthday, ∃ y ∈ leftPrefixes x, a < y.birthday := by
  intro a ha
  obtain ⟨v, hv, hav, _⟩ := hcof a ha
  have hp : plusCount v < plusCount x := by
    have h := plusCount_prefix_lt_cantorSupport_of_retained_cofinal hcof
      (birthday_lt_of_mem_rightPrefixes hv) hsupport
    simpa only [(mem_rightPrefixes_iff.mp hv).1] using h
  obtain ⟨y, hy, hvy⟩ := exists_leftPrefixes_plusCount_ge hp
  have hby : v.birthday < y.birthday := by
    apply lt_of_not_ge
    intro hyv
    have ht : birthdayTruncation v y.birthday = y := by
      rw [← (mem_rightPrefixes_iff.mp hv).1,
        birthdayTruncation_birthdayTruncation x hyv (birthday_lt_of_mem_rightPrefixes hv).le,
        (mem_leftPrefixes_iff.mp hy).1]
    have hyv' : y ∈ leftPrefixes v := mem_leftPrefixes_iff.mpr
      ⟨ht, (mem_leftPrefixes_iff.mp hy).2.trans (mem_rightPrefixes_iff.mp hv).2⟩
    exact (plusCount_lt_of_mem_leftPrefixes hyv').not_ge hvy
  exact ⟨y, hy, hav.trans hby⟩

/-- A baseline cost with cofinal retained minuses has cofinal plus positions as well. -/
theorem leftPrefixes_cofinal_of_baseline_cost {C x : Surreal.{u}}
    (hbase : reducedOmegaCost C x = ω^ plusCount x)
    (hcof : ∀ a < x.birthday, ∃ y ∈ rightPrefixes x, a < y.birthday ∧ y ≤ C) :
    ∀ a < x.birthday, ∃ y ∈ leftPrefixes x, a < y.birthday := by
  apply leftPrefixes_cofinal_of_plusCount_mem_support _ hcof
  rw [hbase, NatOrdinal.cantorSupport_wpow, Finset.mem_singleton]

/-- A word with cofinal plus positions cannot end in a nonempty minus block. -/
theorem ne_appendMinuses_of_leftPrefixes_cofinal {x : Surreal.{u}}
    (hcof : ∀ a < x.birthday, ∃ y ∈ leftPrefixes x, a < y.birthday)
    (z : Surreal.{u}) {ρ : Ordinal.{u}} (hρ : 0 < ρ) : x ≠ appendMinuses z ρ := by
  intro he
  subst x
  have hz : z.birthday < (appendMinuses z ρ).birthday := by
    rw [birthday_appendMinuses]
    exact NatOrdinal.of.strictMono (lt_add_of_pos_right z.birthday.val hρ)
  obtain ⟨y, hy, hzy⟩ := hcof z.birthday hz
  rw [leftPrefixes_appendMinuses] at hy
  exact hzy.not_gt (birthday_lt_of_mem_leftPrefixes hy)

/-- A word with cofinal right-prefix positions cannot end in a nonempty plus block. -/
theorem ne_appendPluses_of_rightPrefixes_cofinal {x : Surreal.{u}}
    (hcof : ∀ a < x.birthday, ∃ y ∈ rightPrefixes x, a < y.birthday)
    (z : Surreal.{u}) {ρ : Ordinal.{u}} (hρ : 0 < ρ) : x ≠ appendPluses z ρ := by
  intro he
  subst x
  have hz : z.birthday < (appendPluses z ρ).birthday := by
    rw [birthday_appendPluses]
    exact NatOrdinal.of.strictMono (lt_add_of_pos_right z.birthday.val hρ)
  obtain ⟨y, hy, hzy⟩ := hcof z.birthday hz
  rw [rightPrefixes_appendPluses] at hy
  exact hzy.not_gt (birthday_lt_of_mem_rightPrefixes hy)

/-- A baseline input with cofinal retained minuses has neither kind of final constant block. -/
theorem no_final_constant_block_of_baseline_cost {C x : Surreal.{u}}
    (hbase : reducedOmegaCost C x = ω^ plusCount x)
    (hcof : ∀ a < x.birthday, ∃ y ∈ rightPrefixes x, a < y.birthday ∧ y ≤ C)
    (z : Surreal.{u}) {ρ : Ordinal.{u}} (hρ : 0 < ρ) :
    x ≠ appendPluses z ρ ∧ x ≠ appendMinuses z ρ := by
  constructor
  · apply ne_appendPluses_of_rightPrefixes_cofinal ?_ z hρ
    intro a ha
    obtain ⟨y, hy, hay, _⟩ := hcof a ha
    exact ⟨y, hy, hay⟩
  · exact ne_appendMinuses_of_leftPrefixes_cofinal
      (leftPrefixes_cofinal_of_baseline_cost hbase hcof) z hρ

/-- Deletion of a cofinal family of right prefixes forces deletion of every right prefix. -/
theorem rightPrefixes_gt_cutoff_of_cofinal_subset {C x : Surreal.{u}}
    (S : Set Surreal.{u}) (hS : S ⊆ rightPrefixes x)
    (hcof : ∀ a < x.birthday, ∃ y ∈ S, a < y.birthday)
    (hdel : ∀ y ∈ S, C < y) : ∀ z ∈ rightPrefixes x, C < z := by
  intro z hz
  obtain ⟨y, hy, hzy⟩ := hcof z.birthday (birthday_lt_of_mem_rightPrefixes hz)
  have hyz := birthdayTruncation_lt hzy (mem_rightPrefixes_iff.mp hz).2
  rw [(mem_rightPrefixes_iff.mp (hS hy)).1] at hyz
  exact (hdel y hy).trans hyz

end Surreal
