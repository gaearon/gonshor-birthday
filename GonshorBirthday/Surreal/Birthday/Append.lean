/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.PlusCount

/-!
# Appending a canonical sign

The two canonical successors are defined by cuts of actual surreal numbers.
-/

universe u

public noncomputable section

namespace Surreal
open Set Order

/-- Append one plus sign to the canonical sign expansion. -/
def appendPlus (x : Surreal.{u}) : Surreal.{u} :=
  !{{x} | rightPrefixes x}'(by
    intro z hz y hy
    obtain rfl := mem_singleton_iff.mp hz
    exact (mem_rightPrefixes.mp hy).choose_spec.2.2)

/-- Append one minus sign to the canonical sign expansion. -/
def appendMinus (x : Surreal.{u}) : Surreal.{u} :=
  !{leftPrefixes x | {x}}'(by
    intro z hz y hy
    obtain rfl := mem_singleton_iff.mp hy
    exact (mem_leftPrefixes.mp hz).choose_spec.2.2)

/-- The plus successor is the simplest number above its source and below its right prefixes. -/
theorem appendPlus_eq_ofSets (x : Surreal.{u}) : appendPlus x =
    !{{x} | rightPrefixes x}'(by
      intro z hz y hy
      obtain rfl := mem_singleton_iff.mp hz
      exact (mem_rightPrefixes.mp hy).choose_spec.2.2) := by
  unfold appendPlus
  rfl

/-- The minus successor is the simplest number below its source and above its left prefixes. -/
theorem appendMinus_eq_ofSets (x : Surreal.{u}) : appendMinus x =
    !{leftPrefixes x | {x}}'(by
      intro z hz y hy
      obtain rfl := mem_singleton_iff.mp hy
      exact (mem_leftPrefixes.mp hz).choose_spec.2.2) := by
  unfold appendMinus
  rfl

/-- The plus successor is strictly larger than its source. -/
theorem lt_appendPlus (x : Surreal.{u}) : x < appendPlus x := by
  unfold appendPlus
  exact lt_ofSets_of_mem_left (mem_singleton x)

/-- The minus successor is strictly smaller than its source. -/
theorem appendMinus_lt (x : Surreal.{u}) : appendMinus x < x := by
  unfold appendMinus
  exact ofSets_lt_of_mem_right (mem_singleton x)

/-- The plus successor remains below every canonical right prefix. -/
theorem appendPlus_lt_of_mem_rightPrefixes {x z : Surreal.{u}} (hz : z ∈ rightPrefixes x) :
    appendPlus x < z := by
  unfold appendPlus
  exact ofSets_lt_of_mem_right hz

/-- The minus successor remains above every canonical left prefix. -/
theorem lt_appendMinus_of_mem_leftPrefixes {x z : Surreal.{u}} (hz : z ∈ leftPrefixes x) :
    z < appendMinus x := by
  unfold appendMinus
  exact lt_ofSets_of_mem_left hz

/-- Removing the final sign of the plus successor recovers its source. -/
theorem birthdayTruncation_appendPlus (x : Surreal.{u}) :
    birthdayTruncation (appendPlus x) x.birthday = x := by
  have ht := birthdayTruncation_eq_of_btwn
    (H := leftPrefixes_lt_rightPrefixes x)
    (fun z hz ↦ ((mem_leftPrefixes.mp hz).choose_spec.2.2).trans (lt_appendPlus x))
    (fun _ hz ↦ appendPlus_lt_of_mem_rightPrefixes hz)
  simpa only [ofSets_leftPrefixes_rightPrefixes] using ht

/-- Removing the final sign of the minus successor recovers its source. -/
theorem birthdayTruncation_appendMinus (x : Surreal.{u}) :
    birthdayTruncation (appendMinus x) x.birthday = x := by
  have ht := birthdayTruncation_eq_of_btwn
    (H := leftPrefixes_lt_rightPrefixes x)
    (fun _ hz ↦ lt_appendMinus_of_mem_leftPrefixes hz)
    (fun z hz ↦ (appendMinus_lt x).trans ((mem_rightPrefixes.mp hz).choose_spec.2.2))
  simpa only [ofSets_leftPrefixes_rightPrefixes] using ht

/-- Appending one plus sign increases birthday by one. -/
theorem birthday_appendPlus (x : Surreal.{u}) : (appendPlus x).birthday = x.birthday + 1 := by
  apply le_antisymm
  · unfold appendPlus
    apply birthday_ofSets_le.trans
    apply max_le
    · simp
    · apply csSup_le'
      rintro _ ⟨z, hz, rfl⟩
      exact (add_one_le_iff.mpr (birthday_lt_of_mem_rightPrefixes hz)).trans
        (le_add_of_nonneg_right zero_le)
  · apply add_one_le_iff.mpr
    by_contra h
    have he := birthdayTruncation_eq_self_of_birthday_le (appendPlus x) (le_of_not_gt h)
    rw [birthdayTruncation_appendPlus] at he
    exact (lt_appendPlus x).ne he

/-- Appending one minus sign increases birthday by one. -/
theorem birthday_appendMinus (x : Surreal.{u}) : (appendMinus x).birthday = x.birthday + 1 := by
  apply le_antisymm
  · unfold appendMinus
    apply birthday_ofSets_le.trans
    apply max_le
    · apply csSup_le'
      rintro _ ⟨z, hz, rfl⟩
      exact (add_one_le_iff.mpr (birthday_lt_of_mem_leftPrefixes hz)).trans
        (le_add_of_nonneg_right zero_le)
    · simp
  · apply add_one_le_iff.mpr
    by_contra h
    have he := birthdayTruncation_eq_self_of_birthday_le (appendMinus x) (le_of_not_gt h)
    rw [birthdayTruncation_appendMinus] at he
    exact (appendMinus_lt x).ne he.symm

/-- Earlier prefixes of a plus successor are precisely the corresponding source prefixes. -/
theorem birthdayTruncation_appendPlus_of_le (x : Surreal.{u}) {a : NatOrdinal.{u}}
    (ha : a ≤ x.birthday) : birthdayTruncation (appendPlus x) a = birthdayTruncation x a := by
  have hb : x.birthday ≤ (appendPlus x).birthday := by
    rw [birthday_appendPlus]
    exact le_add_of_nonneg_right zero_le
  have ht := birthdayTruncation_birthdayTruncation (appendPlus x) ha hb
  rw [birthdayTruncation_appendPlus] at ht
  exact ht.symm

/-- Earlier prefixes of a minus successor are precisely the corresponding source prefixes. -/
theorem birthdayTruncation_appendMinus_of_le (x : Surreal.{u}) {a : NatOrdinal.{u}}
    (ha : a ≤ x.birthday) : birthdayTruncation (appendMinus x) a = birthdayTruncation x a := by
  have hb : x.birthday ≤ (appendMinus x).birthday := by
    rw [birthday_appendMinus]
    exact le_add_of_nonneg_right zero_le
  have ht := birthdayTruncation_birthdayTruncation (appendMinus x) ha hb
  rw [birthdayTruncation_appendMinus] at ht
  exact ht.symm

/-- Appending a plus sign increases the plus count by one. -/
theorem plusCount_appendPlus (x : Surreal.{u}) : plusCount (appendPlus x) = plusCount x + 1 := by
  apply le_antisymm
  · apply (plusCount_le_iff_forall_birthdayTruncation _ _).mpr
    intro a ha _
    rw [birthday_appendPlus] at ha
    have ha' : a ≤ x.birthday := lt_add_one_iff.mp ha
    rw [birthdayTruncation_appendPlus_of_le x ha']
    exact lt_add_one_iff.mpr (plusCount_birthdayTruncation_le x ha')
  · have hb : x.birthday < (appendPlus x).birthday := by
      rw [birthday_appendPlus]
      exact lt_add_one_iff.mpr le_rfl
    have hl : birthdayTruncation (appendPlus x) x.birthday < appendPlus x := by
      rw [birthdayTruncation_appendPlus]
      exact lt_appendPlus x
    have hc := plusCount_birthdayTruncation_lt (appendPlus x) hb hl
    rw [birthdayTruncation_appendPlus] at hc
    exact add_one_le_iff.mpr hc

/-- Appending a minus sign preserves the plus count. -/
theorem plusCount_appendMinus (x : Surreal.{u}) : plusCount (appendMinus x) = plusCount x := by
  apply le_antisymm
  · apply (plusCount_le_iff_forall_birthdayTruncation _ _).mpr
    intro a ha hl
    rw [birthday_appendMinus] at ha
    have ha' : a ≤ x.birthday := lt_add_one_iff.mp ha
    rw [birthdayTruncation_appendMinus_of_le x ha'] at hl ⊢
    rcases ha'.lt_or_eq with ha' | ha'
    · exact plusCount_birthdayTruncation_lt x ha' (hl.trans (appendMinus_lt x))
    · rw [ha', birthdayTruncation_birthday] at hl
      exact False.elim ((appendMinus_lt x).not_gt hl)
  · have hb : x.birthday ≤ (appendMinus x).birthday := by
      rw [birthday_appendMinus]
      exact le_add_of_nonneg_right zero_le
    have hc := plusCount_birthdayTruncation_le (appendMinus x) hb
    rwa [birthdayTruncation_appendMinus] at hc

/-- A plus-oriented extension by one birthday is the canonical plus successor. -/
theorem eq_appendPlus_of_birthdayTruncation_eq {x y : Surreal.{u}}
    (hp : birthdayTruncation y x.birthday = x) (hb : y.birthday = x.birthday + 1)
    (hxy : x < y) : y = appendPlus x := by
  have hR := rightPrefixes_subset_of_birthdayTruncation_eq hp
  have ht : birthdayTruncation y (appendPlus x).birthday = appendPlus x := by
    rw [appendPlus_eq_ofSets]
    apply birthdayTruncation_eq_of_btwn
    · intro z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact hxy
    · intro z hz
      exact (mem_rightPrefixes_iff.mp (hR hz)).2
  rw [birthday_appendPlus, ← hb, birthdayTruncation_birthday] at ht
  exact ht

/-- A minus-oriented extension by one birthday is the canonical minus successor. -/
theorem eq_appendMinus_of_birthdayTruncation_eq {x y : Surreal.{u}}
    (hp : birthdayTruncation y x.birthday = x) (hb : y.birthday = x.birthday + 1)
    (hyx : y < x) : y = appendMinus x := by
  have hL := leftPrefixes_subset_of_birthdayTruncation_eq hp
  have ht : birthdayTruncation y (appendMinus x).birthday = appendMinus x := by
    rw [appendMinus_eq_ofSets]
    apply birthdayTruncation_eq_of_btwn
    · intro z hz
      exact (mem_leftPrefixes_iff.mp (hL hz)).2
    · intro z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact hyx
  rw [birthday_appendMinus, ← hb, birthdayTruncation_birthday] at ht
  exact ht

/-- An adjacent canonical prefix appends a plus sign when the source lies to its right. -/
theorem birthdayTruncation_add_one_eq_appendPlus (x : Surreal.{u}) {a : NatOrdinal.{u}}
    (ha : a + 1 ≤ x.birthday) (hl : birthdayTruncation x a < x) :
    birthdayTruncation x (a + 1) = appendPlus (birthdayTruncation x a) := by
  have hab : a ≤ x.birthday := (le_add_of_nonneg_right (by simp)).trans ha
  have hb : (birthdayTruncation x a).birthday = a := birthday_birthdayTruncation x hab
  apply eq_appendPlus_of_birthdayTruncation_eq
  · rw [hb, birthdayTruncation_birthdayTruncation x (by simp) ha]
  · rw [birthday_birthdayTruncation x ha, hb]
  · apply (lt_birthdayTruncation_iff ha (by rw [hb]; simp)).mpr hl

/-- An adjacent canonical prefix appends a minus sign when the source lies to its left. -/
theorem birthdayTruncation_add_one_eq_appendMinus (x : Surreal.{u}) {a : NatOrdinal.{u}}
    (ha : a + 1 ≤ x.birthday) (hr : x < birthdayTruncation x a) :
    birthdayTruncation x (a + 1) = appendMinus (birthdayTruncation x a) := by
  have hab : a ≤ x.birthday := (le_add_of_nonneg_right (by simp)).trans ha
  have hb : (birthdayTruncation x a).birthday = a := birthday_birthdayTruncation x hab
  apply eq_appendMinus_of_birthdayTruncation_eq
  · rw [hb, birthdayTruncation_birthdayTruncation x (by simp) ha]
  · rw [birthday_birthdayTruncation x ha, hb]
  · apply (birthdayTruncation_lt_iff ha (by rw [hb]; simp)).mpr hr


end Surreal
