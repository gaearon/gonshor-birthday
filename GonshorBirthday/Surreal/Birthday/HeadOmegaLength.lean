/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module
public import GonshorBirthday.Surreal.Birthday.HeadCost
import GonshorBirthday.Surreal.Birthday.HeadCostPrefix
import GonshorBirthday.Surreal.Birthday.HeadBoundary
import GonshorBirthday.Surreal.Birthday.HeadOmegaLimit
import GonshorBirthday.Surreal.Birthday.HeadAllDeleted

/-!
# Exact initial headed monomial length

For every normal-form head supported strictly above an arbitrary surreal exponent,
adding its positive monomial concatenates exactly the native retained original
exponent-position cost. Both history-dependent minus-deletion mechanisms are
included through the support and finite boundary-coefficient criterion. The proof
uses actual full-deletion words, the exact first retained transition, undeleted
successor blocks and cofinal headed prefix continuity.
-/

universe u
public noncomputable section
namespace Surreal
open Set

private theorem block_val (x : Surreal.{u}) :
    (ω^ (plusCount x + 1)).val = (ω^ (plusCount x)).val * Ordinal.omega0 := by
  rw [NatOrdinal.val_wpow, NatOrdinal.val_add_one, Ordinal.opow_add, Ordinal.opow_one]
  rfl

private theorem block_absorb (x : Surreal.{u}) :
    (ω^ (plusCount x)).val + (ω^ (plusCount x)).val * Ordinal.omega0 =
      (ω^ (plusCount x)).val * Ordinal.omega0 := by
  calc
    _ = (ω^ (plusCount x)).val * (1 + Ordinal.omega0) := by rw [mul_add, mul_one]
    _ = _ := by rw [Ordinal.one_add_omega0]

private theorem birthday_head_wpow_of_no_retained
    {H x : Surreal.{u}} (hH : H.support ⊆ Ioi x)
    (hdel : ∀ w ∈ rightPrefixes x, ¬ (H.support ⊆ Ici w ∧
      (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)) :
    (H + ω^ x).birthday = NatOrdinal.of (H.birthday.val + (headOmegaCost H x).val) := by
  rw [headOmegaCost_eq_wpow_of_no_retained_rightPrefix H x hdel,
    ← appendPluses_head_add_wpow_of_no_retained_rightPrefix hH hdel, birthday_appendPluses]

private theorem birthday_head_wpow_first_retained
    {H w : Surreal.{u}} (hH : H.support ⊆ Ici w)
    (hf : (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    (hfirst : ∀ v ∈ rightPrefixes w, ¬ (H.support ⊆ Ici v ∧
      (H.coeff v : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)) :
    (H + ω^ appendMinus w).birthday =
      NatOrdinal.of (H.birthday.val + (headOmegaCost H (appendMinus w)).val) := by
  have hcost : headOmegaCost H (appendMinus w) =
      NatOrdinal.of ((ω^ (plusCount w)).val * Ordinal.omega0) := by
    rw [headOmegaCost_appendMinus_of_retained ⟨hH, hf⟩,
      headOmegaCost_eq_wpow_of_no_retained_rightPrefix H w hfirst, block_val, block_absorb]
  rw [← head_first_retained_appendMinus_word hH hf hfirst, birthday_appendMinuses,
    birthday_appendPluses, NatOrdinal.val_of, hcost, NatOrdinal.val_of,
    add_assoc, block_absorb]

private theorem birthday_head_wpow_plus_step
    {H w : Surreal.{u}} (hH : H.support ⊆ Ioi (appendPlus w))
    (ih : (H + ω^ w).birthday = NatOrdinal.of (H.birthday.val + (headOmegaCost H w).val)) :
    (H + ω^ appendPlus w).birthday =
      NatOrdinal.of (H.birthday.val + (headOmegaCost H (appendPlus w)).val) := by
  rw [← appendPluses_head_wpow_appendPlus hH, birthday_appendPluses, ih, NatOrdinal.val_of,
    headOmegaCost_appendPlus, NatOrdinal.val_of, block_val, add_assoc]

private theorem birthday_head_wpow_minus_step
    {H w : Surreal.{u}} (hH : H.support ⊆ Ioi w)
    (ih : (H + ω^ w).birthday = NatOrdinal.of (H.birthday.val + (headOmegaCost H w).val)) :
    (H + ω^ appendMinus w).birthday =
      NatOrdinal.of (H.birthday.val + (headOmegaCost H (appendMinus w)).val) := by
  have hret : H.support ⊆ Ici w ∧
      (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 := by
    refine ⟨fun v hv ↦ mem_Ici.mpr (mem_Ioi.mp (hH hv)).le, ?_⟩
    have hw0 : H.coeff w = 0 := notMem_support_iff.mp (fun hw ↦ (mem_Ioi.mp (hH hw)).false)
    rw [hw0, Real.toSurreal_zero, birthday_zero]
    exact_mod_cast Ordinal.omega0_pos
  rw [← appendMinuses_head_wpow_appendMinus hH, birthday_appendMinuses, ih, NatOrdinal.val_of,
    headOmegaCost_appendMinus_of_retained hret, NatOrdinal.val_of, block_val, add_assoc]

private theorem birthday_head_wpow_successor
    {H s : Surreal.{u}} {a : NatOrdinal.{u}} (hs : s.birthday = a + 1)
    (hH : H.support ⊆ Ioi s)
    (ih : ∀ v : Surreal.{u}, v.birthday = a → H.support ⊆ Ioi v →
      (H + ω^ v).birthday = NatOrdinal.of (H.birthday.val + (headOmegaCost H v).val)) :
    (H + ω^ s).birthday = NatOrdinal.of (H.birthday.val + (headOmegaCost H s).val) := by
  let v := birthdayTruncation s a
  have hav : a < s.birthday := by rw [hs]; exact lt_add_one a
  have hv : v.birthday = a := birthday_birthdayTruncation s hav.le
  have hne : v ≠ s := by
    intro he
    exact hav.ne (hv.symm.trans (congrArg birthday he))
  by_cases hl : v < s
  · have he : s = appendPlus v := by
      have hh := birthdayTruncation_add_one_eq_appendPlus s (by rw [hs]) hl
      simpa only [← hs, birthdayTruncation_birthday] using hh
    have hvH : H.support ⊆ Ioi v := fun j hj ↦
      mem_Ioi.mpr (hl.trans (mem_Ioi.mp (hH hj)))
    rw [he] at hH ⊢
    exact birthday_head_wpow_plus_step hH (ih v hv hvH)
  · have hr : s < v := lt_of_le_of_ne (le_of_not_gt hl) hne.symm
    have he : s = appendMinus v := by
      have hh := birthdayTruncation_add_one_eq_appendMinus s (by rw [hs]) hr
      simpa only [← hs, birthdayTruncation_birthday] using hh
    by_cases hret : H.support ⊆ Ici v ∧
        (H.coeff v : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0
    · by_cases hfirst : ∀ w ∈ rightPrefixes v, ¬ (H.support ⊆ Ici w ∧
          (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
      · rw [he]
        exact birthday_head_wpow_first_retained hret.1 hret.2 hfirst
      · push Not at hfirst
        obtain ⟨w, hw, hwret⟩ := hfirst
        have hvH : H.support ⊆ Ioi v := fun j hj ↦
          mem_Ioi.mpr ((mem_rightPrefixes_iff.mp hw).2.trans_le (mem_Ici.mp (hwret.1 hj)))
        rw [he]
        exact birthday_head_wpow_minus_step hvH (ih v hv hvH)
    · apply birthday_head_wpow_of_no_retained hH
      intro w hw hwret
      rw [he, rightPrefixes_appendMinus] at hw
      rcases mem_insert_iff.mp hw with rfl | hw
      · exact hret hwret
      · exact hret (support_ge_and_coeff_birthday_lt_of_lt hwret.1
          (mem_rightPrefixes_iff.mp hw).2)

private theorem birthday_head_wpow_limit
    {H s : Surreal.{u}} (hH : H.support ⊆ Ioi s)
    (hlim : Order.IsSuccLimit s.birthday.val)
    (ih : ∀ b < s.birthday, H.support ⊆ Ioi (birthdayTruncation s b) →
      (H + ω^ birthdayTruncation s b).birthday =
        NatOrdinal.of (H.birthday.val + (headOmegaCost H (birthdayTruncation s b)).val)) :
    (H + ω^ s).birthday = NatOrdinal.of (H.birthday.val + (headOmegaCost H s).val) := by
  classical
  by_cases hdel : ∀ w ∈ rightPrefixes s, ¬ (H.support ⊆ Ici w ∧
      (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
  · exact birthday_head_wpow_of_no_retained hH hdel
  push Not at hdel
  obtain ⟨w, hw, hwret⟩ := hdel
  obtain ⟨d, hwd, hds⟩ := hlim.lt_iff_nonempty_Ioo.mp
    (NatOrdinal.val.strictMono (birthday_lt_of_mem_rightPrefixes hw))
  let b₀ := NatOrdinal.of d
  have hb₀ : b₀ < s.birthday := by
    apply NatOrdinal.val.lt_iff_lt.mp
    simpa only [b₀, NatOrdinal.val_of] using hds
  have hwb₀ : w.birthday < b₀ := by
    apply NatOrdinal.val.lt_iff_lt.mp
    simpa only [b₀, NatOrdinal.val_of] using hwd
  have htail : ∀ b : NatOrdinal.{u}, b₀ ≤ b → b ≤ s.birthday →
      H.support ⊆ Ioi (birthdayTruncation s b) := by
    intro b hb0 _ v hv
    have hbw : birthdayTruncation s b < w :=
      birthdayTruncation_lt (hwb₀.trans_le hb0) (mem_rightPrefixes_iff.mp hw).2
    exact mem_Ioi.mpr (hbw.trans_le (mem_Ici.mp (hwret.1 hv)))
  have hactual (M : NatOrdinal.{u}) : (H + ω^ s).birthday ≤ M ↔
      ∀ b : NatOrdinal.{u}, b₀ ≤ b → b < s.birthday →
        (H + ω^ birthdayTruncation s b).birthday ≤ M := by
    have hh := birthday_head_wpow_birthdayTruncation_limit le_rfl hb₀ hlim htail M
    simpa only [birthdayTruncation_birthday] using hh
  have hupper : (H + ω^ s).birthday ≤
      NatOrdinal.of (H.birthday.val + (headOmegaCost H s).val) := by
    apply (hactual _).mpr
    intro b hb0 hbs
    rw [ih b hbs (htail b hb0 hbs.le)]
    apply NatOrdinal.of.monotone
    exact (Ordinal.isNormal_add_right _).monotone
      (NatOrdinal.val.monotone (headOmegaCost_birthdayTruncation_le H s hbs.le))
  have hpre : birthdayTruncation (H + ω^ s) H.birthday = H := by
    apply birthdayTruncation_add_of_support_lt
    simpa only [wlog_wpow] using hH
  have hHZ : H.birthday.val ≤ (H + ω^ s).birthday.val := by
    have hb := birthday_birthdayTruncation_le_birthday (H + ω^ s) H.birthday
    rw [hpre] at hb
    exact NatOrdinal.val.monotone hb
  have hcost : headOmegaCost H s ≤
      NatOrdinal.of ((H + ω^ s).birthday.val - H.birthday.val) := by
    apply (headOmegaCost_le_iff_of_isSuccLimit H s hlim _).mpr
    intro b hbs
    let c := max b b₀
    have hcs : c < s.birthday := max_lt hbs hb₀
    have hcH := htail c (le_max_right _ _) hcs.le
    have hp := birthdayTruncation_head_wpow_of_prefix hH hcH
      (show birthdayTruncation s (birthdayTruncation s c).birthday =
        birthdayTruncation s c by rw [birthday_birthdayTruncation s hcs.le])
    have hbc := birthday_birthdayTruncation_le_birthday (H + ω^ s)
      (H + ω^ birthdayTruncation s c).birthday
    rw [hp, ih c hcs hcH] at hbc
    have hcap : headOmegaCost H (birthdayTruncation s c) ≤
        NatOrdinal.of ((H + ω^ s).birthday.val - H.birthday.val) := by
      apply NatOrdinal.val.le_iff_le.mp
      rw [NatOrdinal.val_of]
      apply (Ordinal.le_sub_of_le hHZ).mpr
      simpa only [NatOrdinal.val_of] using NatOrdinal.val.monotone hbc
    have hcb : b ≤ (birthdayTruncation s c).birthday := by
      rw [birthday_birthdayTruncation s hcs.le]
      exact le_max_left _ _
    have hmono := headOmegaCost_birthdayTruncation_le H (birthdayTruncation s c) hcb
    rw [birthdayTruncation_birthdayTruncation s (le_max_left b b₀) hcs.le] at hmono
    exact hmono.trans hcap
  apply le_antisymm hupper
  apply NatOrdinal.val.le_iff_le.mp
  rw [NatOrdinal.val_of]
  apply (Ordinal.le_sub_of_le hHZ).mp
  simpa only [NatOrdinal.val_of] using NatOrdinal.val.monotone hcost

/-- The exact initial monomial birthday after an arbitrary higher normal-form head
is its native retained original-position cost concatenated to the head birthday. -/
theorem birthday_head_wpow (H s : Surreal.{u}) (hH : H.support ⊆ Ioi s) :
    (H + ω^ s).birthday = NatOrdinal.of (H.birthday.val + (headOmegaCost H s).val) := by
  classical
  have aux : ∀ a : Ordinal.{u}, ∀ s : Surreal.{u}, s.birthday = NatOrdinal.of a →
      ∀ H : Surreal.{u}, H.support ⊆ Ioi s →
        (H + ω^ s).birthday = NatOrdinal.of (H.birthday.val + (headOmegaCost H s).val) := by
    intro a
    induction a using Ordinal.limitRecOn with
    | zero =>
      intro s hs H hH
      have hs0 : s = 0 := birthday_eq_zero.mp (by simpa only [NatOrdinal.of_zero] using hs)
      subst s
      apply birthday_head_wpow_of_no_retained hH
      intro w hw
      simp only [rightPrefixes_zero, mem_empty_iff_false] at hw
    | add_one a ih =>
      intro s hs H hH
      have hs' : s.birthday = NatOrdinal.of a + 1 := by rwa [NatOrdinal.of_add_one] at hs
      apply birthday_head_wpow_successor hs' hH
      intro v hv hvH
      exact ih v hv H hvH
    | limit a hlim ih =>
      intro s hs H hH
      apply birthday_head_wpow_limit hH (by simpa only [hs, NatOrdinal.val_of] using hlim)
      intro b hb hHb
      have hba : b.val < a := by
        simpa only [hs, NatOrdinal.val_of] using NatOrdinal.val.strictMono hb
      exact ih b.val hba (birthdayTruncation s b)
        (by rw [birthday_birthdayTruncation s hb.le, NatOrdinal.of_val]) H hHb
  exact aux s.birthday.val s (NatOrdinal.of_val s.birthday).symm H hH

end Surreal
