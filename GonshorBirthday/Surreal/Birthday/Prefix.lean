/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Birthday.Basic

/-!
# Birthday truncations of surreal numbers

Truncation is defined intrinsically by the cut of younger numbers on either side.
-/

universe u

public noncomputable section

namespace Surreal
open Set Order

instance small_setOfPred_birthday_lt_and_lt (x : Surreal.{u}) (a : NatOrdinal.{u}) :
    Small.{u} {z : Surreal | z.birthday < a ∧ z < x} :=
  small_subset (s := {z : Surreal | z.birthday < a}) (fun _ hz ↦ hz.1)

instance small_setOfPred_birthday_lt_and_gt (x : Surreal.{u}) (a : NatOrdinal.{u}) :
    Small.{u} {z : Surreal | z.birthday < a ∧ x < z} :=
  small_subset (s := {z : Surreal | z.birthday < a}) (fun _ hz ↦ hz.1)

/-- The initial segment of length `a` of the sign sequence of `x`, or `x` itself if `a` is at
least its birthday. It is defined as the simplest surreal lying on the same side as `x` of every
number born before day `a`. -/
def birthdayTruncation (x : Surreal.{u}) (a : NatOrdinal.{u}) : Surreal.{u} :=
  !{{z | z.birthday < a ∧ z < x} | {z | z.birthday < a ∧ x < z}}'
    (fun _ hz _ hw ↦ hz.2.trans hw.2)

/-- A birthday truncation is the cut of younger numbers on either side of its source. -/
theorem birthdayTruncation_eq_ofSets (x : Surreal.{u}) (a : NatOrdinal.{u}) :
    birthdayTruncation x a =
      !{{z | z.birthday < a ∧ z < x} | {z | z.birthday < a ∧ x < z}}'
        (fun _ hz _ hw ↦ hz.2.trans hw.2) := by
  unfold birthdayTruncation
  rfl

/-- Every younger number below `x` is below its birthday truncation. -/
theorem lt_birthdayTruncation {x z : Surreal.{u}} {a : NatOrdinal.{u}}
    (hz : z.birthday < a) (hzx : z < x) : z < birthdayTruncation x a := by
  unfold birthdayTruncation
  exact lt_ofSets_of_mem_left ⟨hz, hzx⟩

/-- Every younger number above `x` is above its birthday truncation. -/
theorem birthdayTruncation_lt {x z : Surreal.{u}} {a : NatOrdinal.{u}}
    (hz : z.birthday < a) (hxz : x < z) : birthdayTruncation x a < z := by
  unfold birthdayTruncation
  exact ofSets_lt_of_mem_right ⟨hz, hxz⟩

/-- Truncation at a fixed birthday is order preserving. -/
theorem monotone_birthdayTruncation (a : NatOrdinal.{u}) :
    Monotone (fun x : Surreal.{u} ↦ birthdayTruncation x a) := by
  intro x y hxy
  unfold birthdayTruncation
  apply ofSets_le_ofSets_iff.mpr
  constructor
  · intro z hz
    exact lt_birthdayTruncation hz.1 (hz.2.trans_le hxy)
  · intro z hz
    exact birthdayTruncation_lt hz.1 (hxy.trans_lt hz.2)

/-- Numbers between two numbers with a common truncation have that truncation. -/
theorem birthdayTruncation_eq_of_between {x y z : Surreal.{u}} {a : NatOrdinal.{u}}
    (hxy : x ≤ y) (hyz : y ≤ z)
    (h : birthdayTruncation x a = birthdayTruncation z a) :
    birthdayTruncation y a = birthdayTruncation x a := by
  apply le_antisymm
  · exact (monotone_birthdayTruncation a hyz).trans_eq h.symm
  · exact monotone_birthdayTruncation a hxy

/-- A birthday truncation is no older than its index. -/
theorem birthday_birthdayTruncation_le (x : Surreal.{u}) (a : NatOrdinal.{u}) :
    (birthdayTruncation x a).birthday ≤ a := by
  unfold birthdayTruncation
  apply birthday_ofSets_le.trans
  apply max_le
  all_goals
    apply csSup_le'
    rintro _ ⟨z, hz, rfl⟩
    exact Order.add_one_le_iff.mpr hz.1

/-- A birthday truncation is no older than its source. -/
theorem birthday_birthdayTruncation_le_birthday (x : Surreal.{u}) (a : NatOrdinal.{u}) :
    (birthdayTruncation x a).birthday ≤ x.birthday := by
  unfold birthdayTruncation
  exact birthday_ofSets_le_of_btwn (fun _ hz ↦ hz.2) (fun _ hz ↦ hz.2)

/-- Every index up to the birthday occurs as the exact birthday of a truncation. -/
theorem birthday_birthdayTruncation (x : Surreal.{u}) {a : NatOrdinal.{u}}
    (ha : a ≤ x.birthday) : (birthdayTruncation x a).birthday = a := by
  apply (birthday_birthdayTruncation_le x a).antisymm
  by_contra h
  have hb : (birthdayTruncation x a).birthday < a := lt_of_not_ge h
  rcases lt_trichotomy (birthdayTruncation x a) x with hx | hx | hx
  · exact (lt_birthdayTruncation hb hx).false
  · exact (ha.trans_eq (congrArg birthday hx).symm).not_gt hb
  · exact (birthdayTruncation_lt hb hx).false

/-- Truncating at or above the birthday recovers the original number. -/
theorem birthdayTruncation_eq_self_of_birthday_le (x : Surreal.{u}) {a : NatOrdinal.{u}}
    (ha : x.birthday ≤ a) : birthdayTruncation x a = x := by
  by_contra h
  have hb : (birthdayTruncation x a).birthday < x.birthday := by
    unfold birthdayTruncation at h ⊢
    exact birthday_ofSets_lt_of_btwn (fun _ hz ↦ hz.2) (fun _ hz ↦ hz.2) h
  have hba := hb.trans_le ha
  rcases lt_trichotomy (birthdayTruncation x a) x with hx | hx | hx
  · exact (lt_birthdayTruncation hba hx).false
  · exact h hx
  · exact (birthdayTruncation_lt hba hx).false

/-- Truncating at the birthday recovers the original number. -/
@[simp]
theorem birthdayTruncation_birthday (x : Surreal.{u}) :
    birthdayTruncation x x.birthday = x :=
  birthdayTruncation_eq_self_of_birthday_le x le_rfl

/-- The birthday of every truncation is the minimum of the index and source birthday. -/
theorem birthday_birthdayTruncation_eq_min (x : Surreal.{u}) (a : NatOrdinal.{u}) :
    (birthdayTruncation x a).birthday = min a x.birthday := by
  rcases le_total a x.birthday with ha | ha
  · rw [birthday_birthdayTruncation x ha, min_eq_left ha]
  · rw [birthdayTruncation_eq_self_of_birthday_le x ha, min_eq_right ha]

/-- A younger number has the same comparison with a truncation and with its source. -/
theorem lt_birthdayTruncation_iff {x z : Surreal.{u}} {a : NatOrdinal.{u}}
    (ha : a ≤ x.birthday) (hz : z.birthday < a) :
    z < birthdayTruncation x a ↔ z < x := by
  refine ⟨fun h ↦ ?_, lt_birthdayTruncation hz⟩
  rcases lt_trichotomy z x with hx | hx | hx
  · exact hx
  · exact False.elim ((hz.trans_le ha).ne (congrArg birthday hx))
  · exact False.elim ((birthdayTruncation_lt hz hx).not_gt h)

/-- A younger number has the same comparison with a truncation and with its source. -/
theorem birthdayTruncation_lt_iff {x z : Surreal.{u}} {a : NatOrdinal.{u}}
    (ha : a ≤ x.birthday) (hz : z.birthday < a) :
    birthdayTruncation x a < z ↔ x < z := by
  refine ⟨fun h ↦ ?_, birthdayTruncation_lt hz⟩
  rcases lt_trichotomy x z with hx | hx | hx
  · exact hx
  · exact False.elim ((hz.trans_le ha).ne (congrArg birthday hx.symm))
  · exact False.elim ((lt_birthdayTruncation hz hx).not_gt h)

/-- Truncating a truncation at an earlier birthday gives the earlier truncation. -/
theorem birthdayTruncation_birthdayTruncation (x : Surreal.{u})
    {a b : NatOrdinal.{u}} (hab : a ≤ b) (hb : b ≤ x.birthday) :
    birthdayTruncation (birthdayTruncation x b) a = birthdayTruncation x a := by
  have hL : {z : Surreal | z.birthday < a ∧ z < birthdayTruncation x b} =
      {z : Surreal | z.birthday < a ∧ z < x} := by
    ext z
    exact and_congr_right (fun hz ↦ lt_birthdayTruncation_iff hb (hz.trans_le hab))
  have hR : {z : Surreal | z.birthday < a ∧ birthdayTruncation x b < z} =
      {z : Surreal | z.birthday < a ∧ x < z} := by
    ext z
    exact and_congr_right (fun hz ↦ birthdayTruncation_lt_iff hb (hz.trans_le hab))
  change !{{z | z.birthday < a ∧ z < birthdayTruncation x b} |
    {z | z.birthday < a ∧ birthdayTruncation x b < z}}'
      (fun _ hz _ hw ↦ hz.2.trans hw.2) =
    !{{z | z.birthday < a ∧ z < x} | {z | z.birthday < a ∧ x < z}}'
      (fun _ hz _ hw ↦ hz.2.trans hw.2)
  congr 1
  rw [hL, hR]

/-- Truncating a prefix preserves its comparison with every earlier prefix. -/
theorem birthdayTruncation_lt_birthdayTruncation_iff (x : Surreal.{u})
    {a b : NatOrdinal.{u}} (hab : a < b) (hb : b ≤ x.birthday) :
    birthdayTruncation x a < birthdayTruncation x b ↔ birthdayTruncation x a < x :=
  lt_birthdayTruncation_iff hb
    ((birthday_birthdayTruncation_le x a).trans_lt hab)

/-- Truncating an ordinal gives the ordinal at the truncation index. -/
theorem birthdayTruncation_toSurreal {a b : NatOrdinal.{u}} (hab : a ≤ b) :
    birthdayTruncation b.toSurreal a = a.toSurreal := by
  have hL : ∀ z : Surreal.{u}, z.birthday < a ∧ z < b.toSurreal → z < a.toSurreal := by
    intro z hz
    exact z.le_toSurreal_birthday.trans_lt (NatOrdinal.toSurreal.lt_iff_lt.mpr hz.1)
  have hR : ∀ z : Surreal.{u}, z.birthday < a ∧ b.toSurreal < z → a.toSurreal < z := by
    intro z hz
    exact (NatOrdinal.toSurreal.monotone hab).trans_lt hz.2
  have he := birthday_birthdayTruncation b.toSurreal (by simpa using hab)
  by_contra h
  have ht : (birthdayTruncation b.toSurreal a).birthday < a.toSurreal.birthday := by
    change (!{{z | z.birthday < a ∧ z < b.toSurreal} |
      {z | z.birthday < a ∧ b.toSurreal < z}}'
        (fun _ hz _ hw ↦ hz.2.trans hw.2)).birthday < _
    exact birthday_ofSets_lt_of_btwn hL hR h
  simp [he] at ht

/-- A younger number to the left of a cut is bounded by one of its left options. -/
theorem exists_mem_left_ge_of_birthday_lt {s t : Set Surreal.{u}}
    [Small.{u} s] [Small.{u} t] {H : ∀ x ∈ s, ∀ y ∈ t, x < y}
    {z : Surreal.{u}} (hz : z < !{s | t}'H) (hb : z.birthday < (!{s | t}'H).birthday) :
    ∃ y ∈ s, z ≤ y := by
  by_contra h
  have hL : ∀ y ∈ s, y < z := by
    intro y hy
    exact lt_of_not_ge (fun hzy ↦ h ⟨y, hy, hzy⟩)
  have hR : ∀ y ∈ t, z < y := fun y hy ↦ hz.trans (ofSets_lt_of_mem_right hy)
  exact hb.not_ge (birthday_ofSets_le_of_btwn hL hR)

/-- A younger number to the right of a cut bounds one of its right options. -/
theorem exists_mem_right_le_of_birthday_lt {s t : Set Surreal.{u}}
    [Small.{u} s] [Small.{u} t] {H : ∀ x ∈ s, ∀ y ∈ t, x < y}
    {z : Surreal.{u}} (hz : (!{s | t}'H) < z) (hb : z.birthday < (!{s | t}'H).birthday) :
    ∃ y ∈ t, y ≤ z := by
  by_contra h
  have hL : ∀ y ∈ s, y < z := fun y hy ↦ (lt_ofSets_of_mem_left hy).trans hz
  have hR : ∀ y ∈ t, z < y := by
    intro y hy
    exact lt_of_not_ge (fun hyz ↦ h ⟨y, hy, hyz⟩)
  exact hb.not_ge (birthday_ofSets_le_of_btwn hL hR)

/-- The simplest member of a cut is a canonical prefix of every number fitting that cut. -/
theorem birthdayTruncation_eq_of_btwn {s t : Set Surreal.{u}}
    [Small.{u} s] [Small.{u} t] {H : ∀ x ∈ s, ∀ y ∈ t, x < y} {x : Surreal.{u}}
    (hL : ∀ z ∈ s, z < x) (hR : ∀ z ∈ t, x < z) :
    birthdayTruncation x (!{s | t}'H).birthday = !{s | t}'H := by
  let u : Surreal.{u} := !{s | t}'H
  have ha : u.birthday ≤ x.birthday := birthday_ofSets_le_of_btwn hL hR
  have huL : ∀ z : Surreal.{u}, z.birthday < u.birthday ∧ z < x → z < u := by
    intro z hz
    by_contra h
    have huz : u ≤ z := le_of_not_gt h
    have hsz : ∀ w ∈ s, w < z := fun w hw ↦ (lt_ofSets_of_mem_left hw).trans_le huz
    have hzt : ∀ w ∈ t, z < w := fun w hw ↦ hz.2.trans (hR w hw)
    exact hz.1.not_ge (birthday_ofSets_le_of_btwn hsz hzt)
  have huR : ∀ z : Surreal.{u}, z.birthday < u.birthday ∧ x < z → u < z := by
    intro z hz
    by_contra h
    have hzu : z ≤ u := le_of_not_gt h
    have hsz : ∀ w ∈ s, w < z := fun w hw ↦ (hL w hw).trans hz.2
    have hzt : ∀ w ∈ t, z < w := fun w hw ↦ hzu.trans_lt (ofSets_lt_of_mem_right hw)
    exact hz.1.not_ge (birthday_ofSets_le_of_btwn hsz hzt)
  have he : (birthdayTruncation x u.birthday).birthday = u.birthday :=
    birthday_birthdayTruncation x ha
  by_contra h
  have ht : (birthdayTruncation x u.birthday).birthday < u.birthday := by
    unfold birthdayTruncation
    exact birthday_ofSets_lt_of_btwn huL huR h
  exact ht.ne he

open IGame in
/-- A numeric game is a canonical prefix of every numeric game fitting its cut. -/
theorem _root_.IGame.Fits.birthdayTruncation_eq {x y : IGame.{u}}
    [IGame.Numeric x] [IGame.Numeric y] (h : IGame.Fits x y) :
    birthdayTruncation (mk x) (mk y).birthday = mk y := by
  have hn : IGame.Numeric !{yᴸ | yᴿ} := by simpa only [IGame.ofSets_moves'] using
    (inferInstance : IGame.Numeric y)
  have he := mk_ofSets (s := yᴸ) (t := yᴿ) (H := hn)
  simp only [IGame.ofSets_moves'] at he
  have hL : ∀ z ∈ Set.range (fun z : yᴸ ↦
      @mk z.1 (IGame.Numeric.of_mem_moves z.2)), z < mk x := by
    rintro _ ⟨⟨z, hz⟩, rfl⟩
    numeric
    rw [lt_iff_not_ge, mk_le_mk]
    exact h.1 z hz
  have hR : ∀ z ∈ Set.range (fun z : yᴿ ↦
      @mk z.1 (IGame.Numeric.of_mem_moves z.2)), mk x < z := by
    rintro _ ⟨⟨z, hz⟩, rfl⟩
    numeric
    rw [lt_iff_not_ge, mk_le_mk]
    exact h.2 z hz
  have ht := birthdayTruncation_eq_of_btwn (H := fun z hz w hw ↦
    (hL z hz).trans (hR w hw)) hL hR
  simpa only [← he] using ht

/-- A number between a left prefix and its source has the same prefix. -/
theorem birthdayTruncation_eq_of_left_between {x y : Surreal.{u}} {a : NatOrdinal.{u}}
    (ha : a ≤ x.birthday) (hL : birthdayTruncation x a ≤ y) (hR : y ≤ x) :
    birthdayTruncation y a = birthdayTruncation x a := by
  have hi : birthdayTruncation (birthdayTruncation x a) a = birthdayTruncation x a :=
    birthdayTruncation_birthdayTruncation x le_rfl ha
  exact (birthdayTruncation_eq_of_between hL hR hi).trans hi

/-- A number between a source and its right prefix has the same prefix. -/
theorem birthdayTruncation_eq_of_right_between {x y : Surreal.{u}} {a : NatOrdinal.{u}}
    (ha : a ≤ x.birthday) (hL : x ≤ y) (hR : y ≤ birthdayTruncation x a) :
    birthdayTruncation y a = birthdayTruncation x a := by
  have hi : birthdayTruncation (birthdayTruncation x a) a = birthdayTruncation x a :=
    birthdayTruncation_birthdayTruncation x le_rfl ha
  exact birthdayTruncation_eq_of_between hL hR hi.symm

/-- Every younger number to the left is bounded by a canonical left prefix. -/
theorem exists_birthdayTruncation_left_ge {x y : Surreal.{u}}
    (hy : y.birthday < x.birthday) (hyx : y < x) :
    ∃ a < x.birthday, y ≤ birthdayTruncation x a ∧ birthdayTruncation x a < x := by
  have aux : ∀ b : NatOrdinal.{u}, ∀ y : Surreal.{u}, y.birthday = b →
      b < x.birthday → y < x →
      ∃ a < x.birthday, y ≤ birthdayTruncation x a ∧ birthdayTruncation x a < x := by
    intro b
    induction b using NatOrdinal.lt_wf.induction with
    | h b ih =>
      intro y hyb hb hyx
      have hu : (birthdayTruncation x b).birthday = b := birthday_birthdayTruncation x hb.le
      rcases lt_trichotomy (birthdayTruncation x b) x with hx | hx | hx
      · refine ⟨b, hb, ?_, hx⟩
        by_contra h
        have hyt : birthdayTruncation y b = birthdayTruncation x b :=
          birthdayTruncation_eq_of_left_between hb.le (le_of_not_ge h) hyx.le
        have hyr : birthdayTruncation y b = y := by
          rw [← hyb]
          exact birthdayTruncation_birthday y
        exact h (hyr.symm.trans hyt).le
      · exact False.elim (hb.ne (hu.symm.trans (congrArg birthday hx)))
      · have hyu : y < birthdayTruncation x b := hyx.trans hx
        let z : Surreal.{u} := !{{y} | {birthdayTruncation x b}}'
          (by simpa using hyu)
        have hzy : y < z := lt_ofSets_of_mem_left (mem_singleton y)
        have hzu : z < birthdayTruncation x b :=
          ofSets_lt_of_mem_right (mem_singleton _)
        have hzb : z.birthday < b :=
          birthday_ofSets_singleton_lt_of_birthday_eq hyb hu hyu
        have hzx : z < x := (lt_birthdayTruncation_iff hb.le hzb).mp hzu
        obtain ⟨a, ha, hza, hax⟩ := ih z.birthday hzb z rfl (hzb.trans hb) hzx
        exact ⟨a, ha, hzy.le.trans hza, hax⟩
  exact aux y.birthday y rfl hy hyx

/-- Every younger number to the right bounds a canonical right prefix. -/
theorem exists_birthdayTruncation_right_le {x y : Surreal.{u}}
    (hy : y.birthday < x.birthday) (hxy : x < y) :
    ∃ a < x.birthday, x < birthdayTruncation x a ∧ birthdayTruncation x a ≤ y := by
  have aux : ∀ b : NatOrdinal.{u}, ∀ y : Surreal.{u}, y.birthday = b →
      b < x.birthday → x < y →
      ∃ a < x.birthday, x < birthdayTruncation x a ∧ birthdayTruncation x a ≤ y := by
    intro b
    induction b using NatOrdinal.lt_wf.induction with
    | h b ih =>
      intro y hyb hb hxy
      have hu : (birthdayTruncation x b).birthday = b := birthday_birthdayTruncation x hb.le
      rcases lt_trichotomy (birthdayTruncation x b) x with hx | hx | hx
      · have huy : birthdayTruncation x b < y := hx.trans hxy
        let z : Surreal.{u} := !{{birthdayTruncation x b} | {y}}'
          (by simpa using huy)
        have huz : birthdayTruncation x b < z := lt_ofSets_of_mem_left (mem_singleton _)
        have hzy : z < y := ofSets_lt_of_mem_right (mem_singleton _)
        have hzb : z.birthday < b :=
          birthday_ofSets_singleton_lt_of_birthday_eq hu hyb huy
        have hxz : x < z := (birthdayTruncation_lt_iff hb.le hzb).mp huz
        obtain ⟨a, ha, hxa, haz⟩ := ih z.birthday hzb z rfl (hzb.trans hb) hxz
        exact ⟨a, ha, hxa, haz.trans hzy.le⟩
      · exact False.elim (hb.ne (hu.symm.trans (congrArg birthday hx)))
      · refine ⟨b, hb, hx, ?_⟩
        by_contra h
        have hyt : birthdayTruncation y b = birthdayTruncation x b :=
          birthdayTruncation_eq_of_right_between hb.le hxy.le (le_of_not_ge h)
        have hyr : birthdayTruncation y b = y := by
          rw [← hyb]
          exact birthdayTruncation_birthday y
        exact h (hyr.symm.trans hyt).ge
  exact aux y.birthday y rfl hy hxy

/-- Truncation at birthday zero is zero. -/
@[simp]
theorem birthdayTruncation_zero (x : Surreal.{u}) : birthdayTruncation x 0 = 0 := by
  apply birthday_eq_zero.mp
  exact le_antisymm (birthday_birthdayTruncation_le x 0) zero_le

/-- The birthday-one truncation of two is one. -/
theorem birthdayTruncation_two_one : birthdayTruncation (2 : Surreal.{u}) 1 = 1 := by
  have hb : (birthdayTruncation (2 : Surreal.{u}) 1).birthday = 1 :=
    birthday_birthdayTruncation _ (by simp)
  have hp : 0 < birthdayTruncation (2 : Surreal.{u}) 1 :=
    lt_birthdayTruncation (by simp) (by simp)
  rcases birthday_eq_one.mp hb with h | h
  · exact h
  · rw [h] at hp
    exact False.elim ((neg_nonpos.mpr zero_le_one).not_gt hp)

end Surreal
