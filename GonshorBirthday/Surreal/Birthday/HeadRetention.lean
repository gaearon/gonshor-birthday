/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module
public import GonshorBirthday.Surreal.Birthday.HeadDeletion
public import GonshorBirthday.Surreal.Birthday.ReducedCost
public import GonshorBirthday.Surreal.Birthday.HeadMidpoint
public import GonshorBirthday.Surreal.Birthday.CoefficientRun

/-!
# Native head retention cutoffs and boundary blocks

The support and finite-boundary-coefficient condition selects exactly one actual
surreal cutoff on original exponent positions. At a nonzero dyadic boundary, the
first coefficient block is an actual canonical right prefix of the new term, with
its full ordinal length inside the source birthday.
-/

universe u
public noncomputable section
namespace Surreal
open Set

/-- Below a retained boundary scale every smaller scale has a zero boundary coefficient. -/
theorem support_ge_and_coeff_birthday_lt_of_lt
    {H w z : Surreal.{u}} (hH : H.support ⊆ Ici w) (hzw : z < w) :
    H.support ⊆ Ici z ∧
      (H.coeff z : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 := by
  refine ⟨fun v hv ↦ (hzw.le.trans (hH hv)), ?_⟩
  have hz : H.coeff z = 0 := notMem_support_iff.mp (fun hz ↦ hzw.not_ge (hH hz))
  rw [hz, Real.toSurreal_zero, birthday_zero]
  exact_mod_cast Ordinal.omega0_pos

/-- The native head retention condition is exactly a single actual surreal cutoff
on the original exponent right prefixes. -/
theorem exists_head_rightPrefix_retention_cutoff (H s : Surreal.{u}) :
    ∃ C : Surreal, s ≤ C ∧ (C = s ∨ C ∈ rightPrefixes s) ∧
      ∀ w ∈ rightPrefixes s,
      (H.support ⊆ Ici w ∧
        (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) ↔ w ≤ C := by
  classical
  let P : Surreal → Prop := fun w ↦ w ∈ rightPrefixes s ∧ H.support ⊆ Ici w ∧
    (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0
  by_cases hP : ∃ w, P w
  · obtain ⟨C, hC, hmin⟩ := (InvImage.wf birthday wellFounded_lt).has_min {w | P w} hP
    refine ⟨C, (mem_rightPrefixes_iff.mp hC.1).2.le, Or.inr hC.1, ?_⟩
    intro w hw
    constructor
    · intro hret
      have hb : C.birthday ≤ w.birthday := le_of_not_gt (hmin w ⟨hw, hret⟩)
      have h := birthdayTruncation_le_cutoff_of_rightPrefix_le hb
        (birthday_lt_of_mem_rightPrefixes hw).le
        (show s < birthdayTruncation s C.birthday by
          rw [(mem_rightPrefixes_iff.mp hC.1).1]
          exact (mem_rightPrefixes_iff.mp hC.1).2)
        (show birthdayTruncation s C.birthday ≤ C by
          rw [(mem_rightPrefixes_iff.mp hC.1).1])
      simpa only [(mem_rightPrefixes_iff.mp hw).1] using h
    · intro hwC
      rcases hwC.lt_or_eq with hwC | rfl
      · exact support_ge_and_coeff_birthday_lt_of_lt hC.2.1 hwC
      · exact hC.2
  · refine ⟨s, le_rfl, Or.inl rfl, ?_⟩
    intro w hw
    constructor
    · intro hret
      exact (hP ⟨w, hw, hret⟩).elim
    · intro hws
      exact ((mem_rightPrefixes_iff.mp hw).2.not_ge hws).elim

/-- The original exponent positions selected by the native head condition are exactly
one of the checked reduced omega position sets. -/
theorem exists_reducedOmegaPositions_eq_head_condition (H s : Surreal.{u}) :
    ∃ C : Surreal, s ≤ C ∧ (C = s ∨ C ∈ rightPrefixes s) ∧
      reducedOmegaPositions C s =
        {i | birthdayTruncation s (NatOrdinal.of i.toOrd.1) < s ∨
          (H.support ⊆ Ici (birthdayTruncation s (NatOrdinal.of i.toOrd.1)) ∧
            (H.coeff (birthdayTruncation s (NatOrdinal.of i.toOrd.1)) : Surreal.{u}).birthday <
              NatOrdinal.of Ordinal.omega0)} := by
  obtain ⟨C, hCs, hC, hret⟩ := exists_head_rightPrefix_retention_cutoff H s
  refine ⟨C, hCs, hC, ?_⟩
  ext i
  rw [mem_reducedOmegaPositions]
  change (_ ∨ _) ↔ (_ ∨ _)
  by_cases hl : birthdayTruncation s (NatOrdinal.of i.toOrd.1) < s
  · simp only [hl, true_or]
  · have hb : NatOrdinal.of i.toOrd.1 < s.birthday := by
      apply NatOrdinal.val.lt_iff_lt.mp
      simpa only [NatOrdinal.val_of, mem_Iio] using i.toOrd.2
    have hne : birthdayTruncation s (NatOrdinal.of i.toOrd.1) ≠ s := by
      intro he
      have hh := birthday_birthdayTruncation_le s (NatOrdinal.of i.toOrd.1)
      rw [he] at hh
      exact hb.not_ge hh
    have hr : birthdayTruncation s (NatOrdinal.of i.toOrd.1) ∈ rightPrefixes s :=
      mem_rightPrefixes.mpr ⟨_, hb, rfl, lt_of_le_of_ne (le_of_not_gt hl) hne.symm⟩
    simpa only [hl, false_or] using (hret _ hr).symm

/-- The first coefficient-plus block at a dyadic retained boundary is an actual
canonical right prefix of the new headed monomial. -/
theorem head_coeff_appendPlus_mem_rightPrefixes_add_wpow
    {H s w : Surreal.{u}} (hH : H.support ⊆ Ici w) (hw : w ∈ rightPrefixes s)
    {r : ℝ} (hr : (r : Surreal.{u}) = appendPlus (H.coeff w : Surreal.{u})) :
    H.normalFormTrunc w + (r : Surreal) * ω^ w ∈ rightPrefixes (H + ω^ s) := by
  have hK : (H.normalFormTrunc w).support ⊆ Ioi w := by
    simp only [support_trunc]
    exact inter_subset_right
  have har : H.coeff w < r := by
    apply Real.toSurreal_lt_iff.mp
    rw [hr]
    exact lt_appendPlus _
  obtain ⟨q, haq, hqr, hq⟩ :=
    exists_head_real_mul_wpow_rightPrefix_lt_add (H.normalFormTrunc w) w hK
    (H.coeff w) zero_lt_one hw (sub_pos.mpr har)
  have hqr' : q < r := by linarith
  have hqrS : (q : Surreal.{u}) < (r : Surreal) := Real.toSurreal_lt_iff.mpr hqr'
  have haS : (H.coeff w : Surreal.{u}) < (q : Surreal) := Real.toSurreal_lt_iff.mpr haq
  have hp : birthdayTruncation (q : Surreal.{u}) (r : Surreal).birthday = (r : Surreal) := by
    rw [hr, appendPlus_eq_ofSets]
    apply birthdayTruncation_eq_of_btwn
    · intro z hz
      simpa only [mem_singleton_iff.mp hz] using haS
    · intro z hz
      exact (hqrS.trans_eq hr).trans (appendPlus_lt_of_mem_rightPrefixes hz)
  have hnext := birthdayTruncation_head_real_mul_wpow_of_prefix (H.normalFormTrunc w) w hK hp
  have hdecomp := eq_trunc_add_coeff_wpow_of_support_ge hH
  have hq' : H.normalFormTrunc w + (q : Surreal) * ω^ w ∈ rightPrefixes (H + ω^ s) := by
    simpa only [Real.toSurreal_one, one_mul, ← add_assoc, ← hdecomp] using hq
  apply mem_rightPrefixes_iff.mpr
  refine ⟨birthdayTruncation_eq_trans (mem_rightPrefixes_iff.mp hq').1 hnext, ?_⟩
  exact (mem_rightPrefixes_iff.mp hq').2.trans
    (add_lt_add_right (mul_lt_mul_of_pos_right hqrS (wpow_pos w)) _)

/-- A nonzero dyadic boundary coefficient allocates a full original omega-power block
inside the actual new headed monomial birthday. -/
theorem exists_head_rightPrefix_birthday_add_wpow_plusCount
    {H s w : Surreal.{u}} (hH : H.support ⊆ Ici w) (hw : w ∈ rightPrefixes s)
    (hc : H.coeff w ≠ 0)
    (hf : (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) :
    ∃ p ∈ rightPrefixes (H + ω^ s),
      p.birthday = NatOrdinal.of (H.birthday.val + (ω^ (plusCount w)).val) := by
  have hK : (H.normalFormTrunc w).support ⊆ Ioi w := by
    simp only [support_trunc]
    exact inter_subset_right
  obtain ⟨q, hq0, hq, hblock⟩ := exists_dyadic_head_coefficient_plus_block
    (H.normalFormTrunc w) w hK hc hf
  have hsrc : ((q.toRat : ℝ) : Surreal.{u}) = appendPlus (H.coeff w : Surreal.{u}) := by
    simpa only [Real.toSurreal_ratCast] using hq
  have hp := head_coeff_appendPlus_mem_rightPrefixes_add_wpow hH hw hsrc
  have hdecomp := eq_trunc_add_coeff_wpow_of_support_ge hH
  refine ⟨H.normalFormTrunc w + (q : Surreal) * ω^ w, ?_, ?_⟩
  · simpa only [Real.toSurreal_ratCast] using hp
  rw [← hdecomp] at hblock
  rw [← hblock, birthday_appendPluses]

end Surreal
