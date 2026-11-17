/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module
public import GonshorBirthday.Surreal.Birthday.HeadRetainedBlock
public import GonshorBirthday.Surreal.Birthday.HeadAllDeleted

/-!
# The first retained right block

The exact full-deletion word at the first retained exponent supplies its initial
block even when the head coefficient there is zero. Actual coefficient-minus
stages then allocate its entire omega-length block in the source birthday.
-/

universe u
public noncomputable section
namespace Surreal
open Set

/-- The first retained exponent right prefix allocates every finite original block,
including when its boundary coefficient is zero. -/
theorem exists_head_rightPrefix_birthday_add_wpow_mul_nat_of_first_retained
    {H s w : Surreal.{u}} (hH : H.support ⊆ Ici w) (hw : w ∈ rightPrefixes s)
    (hf : (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    (hfirst : ∀ v ∈ rightPrefixes w, ¬ (H.support ⊆ Ici v ∧
      (H.coeff v : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)) (n : ℕ) :
    ∃ p ∈ rightPrefixes (H + ω^ s),
      p.birthday = NatOrdinal.of (H.birthday.val + (ω^ (plusCount w)).val * (n + 1)) := by
  by_cases hc : H.coeff w = 0
  · have hstrict : H.support ⊆ Ioi w := by
      intro v hv
      apply mem_Ioi.mpr
      apply lt_of_le_of_ne (mem_Ici.mp (hH hv))
      intro he
      exact mem_support_iff.mp hv (he ▸ hc)
    have hblock := appendPluses_head_add_wpow_of_no_retained_rightPrefix hstrict hfirst
    have htrunc : H.normalFormTrunc w = H := by
      have hh := eq_trunc_add_coeff_wpow_of_support_ge hH
      simpa only [hc, Real.toSurreal_zero, zero_mul, add_zero] using hh.symm
    have hr : ((1 : ℝ) : Surreal.{u}) = appendPlus (H.coeff w : Surreal.{u}) := by
      rw [hc, Real.toSurreal_zero, Real.toSurreal_one]
      apply eq_appendPlus_of_birthdayTruncation_eq
      · simp only [birthday_zero, birthdayTruncation_zero]
      · simp only [birthday_one, birthday_zero, zero_add]
      · exact zero_lt_one
    apply exists_head_rightPrefix_birthday_add_wpow_mul_nat_of_initial_block hH hw hf hr
    simpa only [htrunc, Real.toSurreal_one, one_mul] using hblock
  · exact exists_head_rightPrefix_birthday_add_wpow_mul_nat hH hw hc hf n

/-- The whole first retained minus block lies inside the actual source birthday,
including a zero boundary coefficient. -/
theorem birthday_add_wpow_mul_omega0_le_of_first_retained
    {H s w : Surreal.{u}} (hH : H.support ⊆ Ici w) (hw : w ∈ rightPrefixes s)
    (hf : (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    (hfirst : ∀ v ∈ rightPrefixes w, ¬ (H.support ⊆ Ici v ∧
      (H.coeff v : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)) :
    H.birthday.val + (ω^ (plusCount w)).val * Ordinal.omega0 ≤ (H + ω^ s).birthday.val := by
  have hfinite : ∀ n : ℕ, H.birthday.val + (ω^ (plusCount w)).val * (n + 1) <
      (H + ω^ s).birthday.val := by
    intro n
    obtain ⟨p, hp, hb⟩ :=
      exists_head_rightPrefix_birthday_add_wpow_mul_nat_of_first_retained hH hw hf hfirst n
    have hh := birthday_lt_of_mem_rightPrefixes hp
    rw [hb] at hh
    exact NatOrdinal.val.lt_iff_lt.mpr hh
  have hHZ : H.birthday.val ≤ (H + ω^ s).birthday.val :=
    (le_self_add).trans (hfinite 0).le
  apply (Ordinal.le_sub_of_le hHZ).mp
  apply (Ordinal.mul_le_iff_of_isSuccLimit Ordinal.isSuccLimit_omega0).mpr
  intro a ha
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp ha
  apply (Ordinal.le_sub_of_le hHZ).mpr
  apply le_trans ?_ (hfinite n).le
  gcongr
  exact_mod_cast Nat.le_succ n

/-- At the exact native cutoff, every earlier right prefix was deleted. -/
theorem no_retained_rightPrefixes_of_head_cutoff {H s C : Surreal.{u}}
    (hC : C ∈ rightPrefixes s)
    (hcut : ∀ w ∈ rightPrefixes s, (H.support ⊆ Ici w ∧
      (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) ↔ w ≤ C) :
    ∀ v ∈ rightPrefixes C, ¬ (H.support ⊆ Ici v ∧
      (H.coeff v : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) := by
  intro v hv hret
  have hvs := rightPrefixes_subset_of_birthdayTruncation_eq (mem_rightPrefixes_iff.mp hC).1 hv
  exact (mem_rightPrefixes_iff.mp hv).2.not_ge ((hcut v hvs).mp hret)

end Surreal
