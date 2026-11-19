/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Head

import GonshorBirthday.Surreal.Birthday.SupportGap

/-!
# Right gaps in normal forms without a last term

If the support has no least exponent, every right-prefix gap admits another less than half
its size.
-/

universe u

public noncomputable section

namespace Surreal

/-- Gaps smaller in scale than every supported monomial give arbitrarily halved right gaps. -/
theorem exists_rightPrefix_half_gap_of_support_gaps {z : Surreal.{u}}
    (hsmall : ∀ s ∈ z.support, ∃ v ∈ rightPrefixes z, (v - z).wlog < s)
    {w : Surreal.{u}} (hw : w ∈ rightPrefixes z) :
    ∃ v ∈ rightPrefixes z, 2 * (v - z) < w - z := by
  obtain ⟨s, hs, hsw⟩ := exists_support_le_wlog_sub_of_birthday_lt
    (birthday_lt_of_mem_rightPrefixes hw)
  obtain ⟨v, hv, hvs⟩ := hsmall s hs
  have hvpos : 0 < v - z := sub_pos.mpr (mem_rightPrefixes_iff.mp hv).2
  have hwpos : 0 < w - z := sub_pos.mpr (mem_rightPrefixes_iff.mp hw).2
  have hvl : v - z <ᵥ w - z := by
    rw [← wlog_lt_wlog_iff hvpos.ne' hwpos.ne']
    exact hvs.trans_le hsw
  have hh := (ArchimedeanClass.mk_lt_mk.mp (vlt_def.mp hvl)) 2
  refine ⟨v, hv, ?_⟩
  simpa only [nsmul_eq_mul, Nat.cast_ofNat, abs_of_pos hvpos, abs_of_pos hwpos] using hh

/-- A support without a least exponent admits a strict half-gap at every right prefix. -/
theorem exists_rightPrefix_half_gap_of_no_min_support {z : Surreal.{u}}
    (hs : ∀ s ∈ z.support, ∃ t ∈ z.support, t < s)
    {w : Surreal.{u}} (hw : w ∈ rightPrefixes z) :
    ∃ p ∈ rightPrefixes z, 2 * (p - z) < w - z :=
  exists_rightPrefix_half_gap_of_support_gaps
    (fun _ ht ↦ exists_rightPrefix_small_gap_of_no_min_support hs ht) hw

end Surreal
