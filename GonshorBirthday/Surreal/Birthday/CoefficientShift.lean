/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.CoefficientPrefix
public import GonshorBirthday.Surreal.Birthday.Coefficient

/-!
# Translated coefficient-prefix monomial families

Lower-scale canonical prefixes may be inserted after a fitting positive real
coefficient head in the direction of the target coefficient.
-/

universe u
public noncomputable section
namespace Surreal
open Set IGame

/-- Every monomial left prefix is below every positive real coefficient monomial. -/
theorem lt_real_mul_wpow_of_mem_leftPrefixes {r : ℝ} (hr : 0 < r)
    {x a : Surreal.{u}} (ha : a ∈ leftPrefixes (ω^ x)) : a < (r : Surreal) * ω^ x := by
  obtain rfl | ⟨v, hv, n, han⟩ := exists_natCast_mul_wpow_ge_of_mem_leftPrefixes ha
  · exact mul_pos (Real.toSurreal_pos_iff.mpr hr) (wpow_pos x)
  apply han.trans_lt
  have ht := mul_wpow_lt_mul_wpow_of_pos (n : ℝ) hr (mem_leftPrefixes_iff.mp hv).2
  simpa only [Real.toSurreal_natCast] using ht

/-- A lower-scale plus family at a positive coefficient prefix still prefixes the target. -/
theorem birthdayTruncation_real_mul_wpow_add_leftPrefix {r s : ℝ}
    (hr : 0 < r) (hrs : r < s)
    (hp : birthdayTruncation (s : Surreal.{u}) (r : Surreal).birthday = (r : Surreal))
    {x a : Surreal.{u}} (ha : a ∈ leftPrefixes (ω^ x)) :
    birthdayTruncation ((s : Surreal) * ω^ x) ((r : Surreal) * ω^ x + a).birthday =
      (r : Surreal) * ω^ x + a := by
  have hpre := birthdayTruncation_real_mul_wpow_of_prefix hp x
  have hsmall := lt_real_mul_wpow_of_mem_leftPrefixes (sub_pos.mpr hrs) ha
  rw [Real.toSurreal_sub, sub_mul] at hsmall
  have hgap : (r : Surreal) * ω^ x + a < (s : Surreal) * ω^ x := by
    linarith only [hsmall]
  have ha0 := nonneg_of_mem_leftPrefixes (wpow_pos x) ha
  have hr0 : 0 ≤ (r : Surreal.{u}) * ω^ x :=
    mul_nonneg (Real.toSurreal_nonneg_iff.mpr hr.le) (wpow_nonneg x)
  have hL : ∀ z ∈ (· + a) '' leftPrefixes ((r : Surreal) * ω^ x) ∪
      ((r : Surreal) * ω^ x + ·) '' leftPrefixes a, z < (s : Surreal) * ω^ x := by
    rintro z (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact (add_lt_add_left (mem_leftPrefixes_iff.mp hp).2 a).trans hgap
    · exact (add_lt_add_right (mem_leftPrefixes_iff.mp hp).2 _).trans hgap
  have hR : ∀ z ∈ (· + a) '' rightPrefixes ((r : Surreal) * ω^ x) ∪
      ((r : Surreal) * ω^ x + ·) '' rightPrefixes a, (s : Surreal) * ω^ x < z := by
    rintro z (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · have ht := rightPrefixes_subset_of_birthdayTruncation_eq hpre hp
      exact (mem_rightPrefixes_iff.mp ht).2.trans_le (le_add_of_nonneg_right ha0)
    · have hpA := rightPrefixes_subset_of_birthdayTruncation_eq
        (mem_leftPrefixes_iff.mp ha).1 hp
      have hpS := rightPrefixes_subset_of_birthdayTruncation_eq
        (birthdayTruncation_real_mul_wpow s (hr.trans hrs) x) hpA
      exact (mem_rightPrefixes_iff.mp hpS).2.trans_le (le_add_of_nonneg_left hr0)
  have ht := birthdayTruncation_eq_of_btwn
    (H := fun z hz w hw ↦ (hL z hz).trans (hR w hw)) hL hR
  rw [← add_eq_ofSets_leftPrefixes ((r : Surreal) * ω^ x) a] at ht
  exact ht

/-- A lower-scale minus family at a positive coefficient prefix still prefixes the target. -/
theorem birthdayTruncation_real_mul_wpow_sub_leftPrefix {r s : ℝ}
    (hs : 0 < s) (hsr : s < r)
    (hp : birthdayTruncation (s : Surreal.{u}) (r : Surreal).birthday = (r : Surreal))
    {x a : Surreal.{u}} (ha : a ∈ leftPrefixes (ω^ x)) :
    birthdayTruncation ((s : Surreal) * ω^ x) ((r : Surreal) * ω^ x - a).birthday =
      (r : Surreal) * ω^ x - a := by
  have hpre := birthdayTruncation_real_mul_wpow_of_prefix hp x
  have hsmall := lt_real_mul_wpow_of_mem_leftPrefixes (sub_pos.mpr hsr) ha
  rw [Real.toSurreal_sub, sub_mul] at hsmall
  have hgap : (s : Surreal) * ω^ x < (r : Surreal) * ω^ x - a := by
    linarith only [hsmall]
  have ha0 := nonneg_of_mem_leftPrefixes (wpow_pos x) ha
  have hs0 : 0 < (s : Surreal.{u}) * ω^ x :=
    mul_pos (Real.toSurreal_pos_iff.mpr hs) (wpow_pos x)
  have hL : ∀ z ∈ (· + -a) '' leftPrefixes ((r : Surreal) * ω^ x) ∪
      ((r : Surreal) * ω^ x + ·) '' leftPrefixes (-a), z < (s : Surreal) * ω^ x := by
    rintro z (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · have ht := leftPrefixes_subset_of_birthdayTruncation_eq hpre hp
      exact (add_le_of_nonpos_right (neg_nonpos.mpr ha0)).trans_lt
        (mem_leftPrefixes_iff.mp ht).2
    · rw [leftPrefixes_neg] at hp
      obtain ⟨p, hp, rfl⟩ := hp
      have hpA := rightPrefixes_subset_of_birthdayTruncation_eq
        (mem_leftPrefixes_iff.mp ha).1 hp
      have hpR := rightPrefixes_subset_of_birthdayTruncation_eq
        (birthdayTruncation_real_mul_wpow r (hs.trans hsr) x) hpA
      have ht := sub_neg.mpr (mem_rightPrefixes_iff.mp hpR).2
      simpa only [sub_eq_add_neg] using ht.trans hs0
  have hR : ∀ z ∈ (· + -a) '' rightPrefixes ((r : Surreal) * ω^ x) ∪
      ((r : Surreal) * ω^ x + ·) '' rightPrefixes (-a), (s : Surreal) * ω^ x < z := by
    rintro z (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · have ht := sub_lt_sub_right (mem_rightPrefixes_iff.mp hp).2 a
      simpa only [sub_eq_add_neg] using hgap.trans ht
    · rw [rightPrefixes_neg] at hp
      obtain ⟨p, hp, rfl⟩ := hp
      have ht := sub_lt_sub_left (mem_leftPrefixes_iff.mp hp).2 ((r : Surreal) * ω^ x)
      simpa only [sub_eq_add_neg] using hgap.trans ht
  have ht := birthdayTruncation_eq_of_btwn
    (H := fun z hz w hw ↦ (hL z hz).trans (hR w hw)) hL hR
  rw [← add_eq_ofSets_leftPrefixes ((r : Surreal) * ω^ x) (-a)] at ht
  simpa only [sub_eq_add_neg] using ht

/-- Every stage of a lower-scale plus family preserves the coefficient head's right prefixes. -/
theorem rightPrefixes_real_mul_wpow_add_leftPrefix {r s : ℝ}
    (hr : 0 < r) (hrs : r < s)
    (hp : birthdayTruncation (s : Surreal.{u}) (r : Surreal).birthday = (r : Surreal))
    {x a : Surreal.{u}} (ha : a ∈ leftPrefixes (ω^ x)) :
    rightPrefixes ((r : Surreal) * ω^ x + a) = rightPrefixes ((r : Surreal) * ω^ x) := by
  have hpre := birthdayTruncation_real_mul_wpow_of_prefix hp x
  have hstage := birthdayTruncation_real_mul_wpow_add_leftPrefix hr hrs hp ha
  have hsmall := lt_real_mul_wpow_of_mem_leftPrefixes (sub_pos.mpr hrs) ha
  rw [Real.toSurreal_sub, sub_mul] at hsmall
  have hgap : (r : Surreal) * ω^ x + a < (s : Surreal) * ω^ x := by
    linarith only [hsmall]
  have ha0 := nonneg_of_mem_leftPrefixes (wpow_pos x) ha
  have hr0 : 0 ≤ (r : Surreal.{u}) * ω^ x :=
    mul_nonneg (Real.toSurreal_nonneg_iff.mpr hr.le) (wpow_nonneg x)
  have hb : ((r : Surreal) * ω^ x).birthday ≤ ((s : Surreal) * ω^ x).birthday := by
    have ht := birthday_birthdayTruncation_le_birthday
      ((s : Surreal) * ω^ x) ((r : Surreal) * ω^ x).birthday
    rwa [hpre] at ht
  have hhead : birthdayTruncation ((r : Surreal) * ω^ x + a)
      ((r : Surreal) * ω^ x).birthday = (r : Surreal) * ω^ x := by
    have ht := birthdayTruncation_eq_of_left_between hb
      (by rw [hpre]; exact le_add_of_nonneg_right ha0) hgap.le
    exact ht.trans hpre
  apply Set.Subset.antisymm
  · intro z hz
    have liftRight : ∀ w ∈ rightPrefixes ((r : Surreal) * ω^ x), w ≤ z →
        z ∈ rightPrefixes ((r : Surreal) * ω^ x) := by
      intro w hw hwz
      have hws := rightPrefixes_subset_of_birthdayTruncation_eq hpre hw
      have hsumw := hgap.trans (mem_rightPrefixes_iff.mp hws).2
      have hzpre := (mem_rightPrefixes_iff.mp hz).1
      have ht := birthdayTruncation_eq_of_right_between
        (birthday_lt_of_mem_rightPrefixes hz).le hsumw.le (by rwa [hzpre])
      rw [hzpre] at ht
      exact mem_rightPrefixes_iff.mpr
        ⟨birthdayTruncation_eq_trans (mem_rightPrefixes_iff.mp hw).1 ht,
          (mem_rightPrefixes_iff.mp hw).2.trans_le hwz⟩
    rcases exists_rightPrefixes_add_le hz with ⟨w, hw, hwz⟩ | ⟨w, hw, hwz⟩
    · exact liftRight w hw ((le_add_of_nonneg_right ha0).trans hwz)
    · have hwA := rightPrefixes_subset_of_birthdayTruncation_eq
        (mem_leftPrefixes_iff.mp ha).1 hw
      have hwH := rightPrefixes_subset_of_birthdayTruncation_eq
        (birthdayTruncation_real_mul_wpow r hr x) hwA
      exact liftRight w hwH ((le_add_of_nonneg_left hr0).trans hwz)
  · exact rightPrefixes_subset_of_birthdayTruncation_eq hhead

/-- Every stage of a lower-scale minus family preserves the coefficient head's left prefixes. -/
theorem leftPrefixes_real_mul_wpow_sub_leftPrefix {r s : ℝ}
    (hs : 0 < s) (hsr : s < r)
    (hp : birthdayTruncation (s : Surreal.{u}) (r : Surreal).birthday = (r : Surreal))
    {x a : Surreal.{u}} (ha : a ∈ leftPrefixes (ω^ x)) :
    leftPrefixes ((r : Surreal) * ω^ x - a) = leftPrefixes ((r : Surreal) * ω^ x) := by
  have hpre := birthdayTruncation_real_mul_wpow_of_prefix hp x
  have hsmall := lt_real_mul_wpow_of_mem_leftPrefixes (sub_pos.mpr hsr) ha
  rw [Real.toSurreal_sub, sub_mul] at hsmall
  have hgap : (s : Surreal) * ω^ x < (r : Surreal) * ω^ x - a := by
    linarith only [hsmall]
  have ha0 := nonneg_of_mem_leftPrefixes (wpow_pos x) ha
  have hs0 : 0 < (s : Surreal.{u}) * ω^ x :=
    mul_pos (Real.toSurreal_pos_iff.mpr hs) (wpow_pos x)
  have hb : ((r : Surreal) * ω^ x).birthday ≤ ((s : Surreal) * ω^ x).birthday := by
    have ht := birthday_birthdayTruncation_le_birthday
      ((s : Surreal) * ω^ x) ((r : Surreal) * ω^ x).birthday
    rwa [hpre] at ht
  have hhead : birthdayTruncation ((r : Surreal) * ω^ x - a)
      ((r : Surreal) * ω^ x).birthday = (r : Surreal) * ω^ x := by
    have ht := birthdayTruncation_eq_of_right_between hb hgap.le
      (by rw [hpre]; exact sub_le_self _ ha0)
    exact ht.trans hpre
  apply Set.Subset.antisymm
  · intro z hz
    have liftLeft : ∀ w ∈ leftPrefixes ((r : Surreal) * ω^ x), z ≤ w →
        z ∈ leftPrefixes ((r : Surreal) * ω^ x) := by
      intro w hw hzw
      have hws := leftPrefixes_subset_of_birthdayTruncation_eq hpre hw
      have hwsum := (mem_leftPrefixes_iff.mp hws).2.trans hgap
      have hzpre := (mem_leftPrefixes_iff.mp hz).1
      have ht := birthdayTruncation_eq_of_left_between
        (birthday_lt_of_mem_leftPrefixes hz).le (by rwa [hzpre]) hwsum.le
      rw [hzpre] at ht
      exact mem_leftPrefixes_iff.mpr
        ⟨birthdayTruncation_eq_trans (mem_leftPrefixes_iff.mp hw).1 ht,
          hzw.trans_lt (mem_leftPrefixes_iff.mp hw).2⟩
    have hz' : z ∈ leftPrefixes ((r : Surreal) * ω^ x + -a) := by
      simpa only [sub_eq_add_neg] using hz
    rcases exists_leftPrefixes_add_ge hz' with ⟨w, hw, hzw⟩ | ⟨w, hw, hzw⟩
    · exact liftLeft w hw (hzw.trans (add_le_of_nonpos_right (neg_nonpos.mpr ha0)))
    · rw [leftPrefixes_neg] at hw
      obtain ⟨w, hw, rfl⟩ := hw
      have hwA := rightPrefixes_subset_of_birthdayTruncation_eq
        (mem_leftPrefixes_iff.mp ha).1 hw
      have hwH := rightPrefixes_subset_of_birthdayTruncation_eq
        (birthdayTruncation_real_mul_wpow r (hs.trans hsr) x) hwA
      have hwneg : (r : Surreal) * ω^ x + -w < 0 := by
        simpa only [sub_eq_add_neg] using sub_neg.mpr (mem_rightPrefixes_iff.mp hwH).2
      have hz0 : z ≤ 0 := hzw.trans hwneg.le
      exact liftLeft 0 (zero_mem_leftPrefixes
        (mul_pos (Real.toSurreal_pos_iff.mpr (hs.trans hsr)) (wpow_pos x))) hz0
  · exact leftPrefixes_subset_of_birthdayTruncation_eq hhead


private theorem support_real_mul_wpow_subset (r : ℝ) (x : Surreal.{u}) :
    ((r : Surreal) * ω^ x).support ⊆ Ici x := by
  rw [← SurrealHahnSeries.toSurreal_single x r, SurrealHahnSeries.support_toSurreal]
  intro z hz
  have hez : z = x := Set.mem_singleton_iff.mp (SurrealHahnSeries.support_single_subset hz)
  rw [hez]
  change x ≤ x
  exact le_rfl

/-- Every translated plus stage has exact birthday given by the original lower-scale plus rank. -/
theorem birthday_real_mul_wpow_add_leftPrefix {r s : ℝ}
    (hr : 0 < r) (hrs : r < s)
    (hp : birthdayTruncation (s : Surreal.{u}) (r : Surreal).birthday = (r : Surreal))
    {x a : Surreal.{u}} (ha : a ∈ leftPrefixes (ω^ x)) :
    ((r : Surreal) * ω^ x + a).birthday =
      NatOrdinal.of (((r : Surreal) * ω^ x).birthday.val + (plusCount a).val) := by
  apply birthday_add_left_prefix_eq_of_stage_rightPrefixes (t := (s : Surreal) * ω^ x)
      (wpow_pos x) _ _ _ _ ha
  · intro y hy
    exact rightPrefixes_real_mul_wpow_add_leftPrefix hr hrs hp hy
  · intro y hy
    exact birthdayTruncation_real_mul_wpow_add_leftPrefix hr hrs hp hy
  · intro y hy
    have ht := lt_real_mul_wpow_of_mem_leftPrefixes (sub_pos.mpr hrs) hy
    rw [Real.toSurreal_sub, sub_mul] at ht
    linarith only [ht]
  · intro y hy p hpy
    exact (add_lt_of_mem_leftPrefixes_wpow_of_support
      (support_real_mul_wpow_subset r x) hy hpy).le

/-- Every reflected minus stage has exact birthday given by the original lower-scale plus rank. -/
theorem birthday_real_mul_wpow_sub_leftPrefix {r s : ℝ}
    (hs : 0 < s) (hsr : s < r)
    (hp : birthdayTruncation (s : Surreal.{u}) (r : Surreal).birthday = (r : Surreal))
    {x a : Surreal.{u}} (ha : a ∈ leftPrefixes (ω^ x)) :
    ((r : Surreal) * ω^ x - a).birthday =
      NatOrdinal.of (((r : Surreal) * ω^ x).birthday.val + (plusCount a).val) := by
  let H : Surreal.{u} := -((r : Surreal) * ω^ x)
  let t : Surreal.{u} := -((s : Surreal) * ω^ x)
  have hR : ∀ y ∈ leftPrefixes (ω^ x), rightPrefixes (H + y) = rightPrefixes H := by
    intro y hy
    have he : H + y = -((r : Surreal) * ω^ x - y) := by dsimp only [H]; ring
    rw [he, rightPrefixes_neg, leftPrefixes_real_mul_wpow_sub_leftPrefix hs hsr hp hy]
    exact (rightPrefixes_neg ((r : Surreal) * ω^ x)).symm
  have hP : ∀ y ∈ leftPrefixes (ω^ x), birthdayTruncation t (H + y).birthday = H + y := by
    intro y hy
    have ht := birthdayTruncation_neg_of_eq
      (birthdayTruncation_real_mul_wpow_sub_leftPrefix hs hsr hp hy)
    have he : -((r : Surreal) * ω^ x - y) = H + y := by dsimp only [H]; ring
    rw [← birthday_neg ((r : Surreal) * ω^ x - y), he] at ht
    exact ht
  have hB : ∀ y ∈ leftPrefixes (ω^ x), H + y ≤ t := by
    intro y hy
    have ht := lt_real_mul_wpow_of_mem_leftPrefixes (sub_pos.mpr hsr) hy
    rw [Real.toSurreal_sub, sub_mul] at ht
    dsimp only [H, t]
    linarith only [ht]
  have hSupport : H.support ⊆ Ici x := by
    have he : H = ((-r : ℝ) : Surreal) * ω^ x := by simp [H]
    rw [he]
    exact support_real_mul_wpow_subset (-r) x
  have hG : ∀ y ∈ leftPrefixes (ω^ x), ∀ p ∈ leftPrefixes H, p + y ≤ H :=
    fun _ hy _ hp ↦ (add_lt_of_mem_leftPrefixes_wpow_of_support hSupport hy hp).le
  have ht := birthday_add_left_prefix_eq_of_stage_rightPrefixes (wpow_pos x) hR hP hB hG ha
  have he : H + a = -((r : Surreal) * ω^ x - a) := by dsimp only [H]; ring
  rw [he, birthday_neg] at ht
  simpa only [H, birthday_neg] using ht


end Surreal
