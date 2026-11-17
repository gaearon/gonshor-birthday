/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module
public import GonshorBirthday.Surreal.Birthday.HeadRetention
public import GonshorBirthday.Surreal.Birthday.HeadCoefficientWord

/-!
# Actual original right blocks at retained boundaries

For a nonzero dyadic boundary coefficient, every finite coefficient-minus stage
is an actual right prefix of the new lower monomial after its head. Their exact
birthdays allocate the whole ordinary omega-power block times omega inside the
actual source birthday. No upper budget is substituted for this input capacity.
-/

universe u
public noncomputable section
namespace Surreal
open Set

/-- Every canonical left prefix of a plus successor is at most its predecessor. -/
theorem le_of_mem_leftPrefixes_appendPlus {x p : Surreal.{u}}
    (hp : p ∈ leftPrefixes (appendPlus x)) : p ≤ x := by
  have hbp := birthday_lt_of_mem_leftPrefixes hp
  have hpx := (mem_leftPrefixes_iff.mp hp).2
  rw [appendPlus_eq_ofSets] at hbp hpx
  obtain ⟨q, hq, hpq⟩ := exists_mem_left_ge_of_birthday_lt hpx hbp
  obtain rfl := Set.mem_singleton_iff.mp hq
  exact hpq

/-- A real boundary neighbour whose entire original left cut stays below the old
coefficient gives an actual new headed right prefix. -/
theorem head_real_mul_wpow_mem_rightPrefixes_of_leftPrefixes_le
    {H s w : Surreal.{u}} (hH : H.support ⊆ Ici w) (hw : w ∈ rightPrefixes s)
    {r : ℝ} (har : H.coeff w < r)
    (hL : ∀ z ∈ leftPrefixes (r : Surreal.{u}), z ≤ (H.coeff w : Surreal.{u})) :
    H.normalFormTrunc w + (r : Surreal.{u}) * ω^ w ∈ rightPrefixes (H + ω^ s) := by
  have hK : (H.normalFormTrunc w).support ⊆ Ioi w := by
    simp only [support_trunc]
    exact inter_subset_right
  obtain ⟨q, haq, hqr, hq⟩ :=
    exists_head_real_mul_wpow_rightPrefix_lt_add (H.normalFormTrunc w) w hK
    (H.coeff w) zero_lt_one hw (sub_pos.mpr har)
  have hqrS : (q : Surreal.{u}) < (r : Surreal.{u}) :=
    Real.toSurreal_lt_iff.mpr (by linarith)
  have haS : (H.coeff w : Surreal.{u}) < (q : Surreal.{u}) :=
    Real.toSurreal_lt_iff.mpr haq
  have hp : birthdayTruncation (q : Surreal.{u}) (r : Surreal.{u}).birthday =
      (r : Surreal.{u}) := by
    have ht := birthdayTruncation_eq_of_btwn
      (s := leftPrefixes (r : Surreal.{u})) (t := rightPrefixes (r : Surreal.{u}))
      (H := leftPrefixes_lt_rightPrefixes (r : Surreal.{u}))
      (x := (q : Surreal.{u}))
    apply (by simpa only [ofSets_leftPrefixes_rightPrefixes] using ht)
    · intro z hz
      exact (hL z hz).trans_lt haS
    · intro z hz
      exact hqrS.trans (mem_rightPrefixes_iff.mp hz).2
  have hnext := birthdayTruncation_head_real_mul_wpow_of_prefix (H.normalFormTrunc w) w hK hp
  have hdecomp := eq_trunc_add_coeff_wpow_of_support_ge hH
  have hq' : H.normalFormTrunc w + (q : Surreal.{u}) * ω^ w ∈ rightPrefixes (H + ω^ s) := by
    simpa only [Real.toSurreal_one, one_mul, ← add_assoc, ← hdecomp] using hq
  apply mem_rightPrefixes_iff.mpr
  refine ⟨birthdayTruncation_eq_trans (mem_rightPrefixes_iff.mp hq').1 hnext, ?_⟩
  exact (mem_rightPrefixes_iff.mp hq').2.trans
    (add_lt_add_right (mul_lt_mul_of_pos_right hqrS (wpow_pos w)) _)

private theorem exists_head_coeff_minus_stages
    {H w : Surreal.{u}}
    (hf : (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    {r : ℝ} (hr : (r : Surreal.{u}) = appendPlus (H.coeff w : Surreal.{u}))
    (hblock : appendPluses H (ω^ (plusCount w)).val =
      H.normalFormTrunc w + (r : Surreal) * ω^ w) (n : ℕ) :
    ∃ r : ℝ, (r : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0 ∧ r ≠ 0 ∧
      (H.coeff w : Surreal.{u}) ∈ leftPrefixes (r : Surreal.{u}) ∧
      (∀ z ∈ leftPrefixes (r : Surreal.{u}), z ≤ (H.coeff w : Surreal.{u})) ∧
      (H.normalFormTrunc w + (r : Surreal.{u}) * ω^ w).birthday =
        NatOrdinal.of (H.birthday.val + (ω^ (plusCount w)).val * (n + 1)) := by
  have hK : (H.normalFormTrunc w).support ⊆ Ioi w := by
    simp only [support_trunc]
    exact inter_subset_right
  induction n with
  | zero =>
    refine ⟨r, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hr, birthday_appendPlus]
      obtain ⟨m, hm⟩ := NatOrdinal.lt_omega0.mp hf
      rw [hm]
      exact_mod_cast NatOrdinal.natCast_lt_omega0 (m + 1)
    · intro he
      have hh : (r : Surreal.{u}) = 0 := by rw [he, Real.toSurreal_zero]
      rw [hr] at hh
      have hb := congrArg birthday hh
      simp only [birthday_appendPlus, birthday_zero, NatOrdinal.add_eq_zero_iff,
        one_ne_zero, and_false] at hb
    · rw [hr]
      exact mem_leftPrefixes_iff.mpr ⟨birthdayTruncation_appendPlus _, lt_appendPlus _⟩
    · intro z hz
      rw [hr] at hz
      exact le_of_mem_leftPrefixes_appendPlus hz
    · rw [← hblock, birthday_appendPluses]
      simp only [Nat.cast_zero, zero_add, mul_one]
  | succ n ih =>
    obtain ⟨r, hrf, hr0, har, hL, hb⟩ := ih
    have hnextf : (appendMinus (r : Surreal.{u})).birthday <
        NatOrdinal.of Ordinal.omega0 := by
      rw [birthday_appendMinus]
      obtain ⟨m, hm⟩ := NatOrdinal.lt_omega0.mp hrf
      rw [hm]
      exact_mod_cast NatOrdinal.natCast_lt_omega0 (m + 1)
    obtain ⟨q, hq⟩ := birthday_lt_omega0_iff.mp hnextf
    let t : ℝ := q.toRat
    have ht : (t : Surreal.{u}) = appendMinus (r : Surreal.{u}) := by
      simpa only [t, Real.toSurreal_ratCast] using hq
    have hleft : leftPrefixes (t : Surreal.{u}) = leftPrefixes (r : Surreal.{u}) := by
      rw [ht, ← appendMinuses_one, leftPrefixes_appendMinuses]
    refine ⟨t, by simpa only [ht] using hnextf, ?_, ?_, ?_, ?_⟩
    · intro he
      have hh : (t : Surreal.{u}) = 0 := by rw [he, Real.toSurreal_zero]
      rw [ht] at hh
      have heq := congrArg birthday hh
      simp only [birthday_appendMinus, birthday_zero, NatOrdinal.add_eq_zero_iff,
        one_ne_zero, and_false] at heq
    · rwa [hleft]
    · simpa only [hleft] using hL
    · have hblock := appendMinuses_head_real_mul_wpow_of_appendMinus
        (H.normalFormTrunc w) w hK hr0 ht
      rw [← hblock, birthday_appendMinuses, hb, NatOrdinal.val_of]
      congr 1
      simp only [Nat.cast_succ, mul_add,
        mul_one, add_assoc]

/-- An exact first boundary plus block extends to every finite original minus stage. -/
theorem exists_head_rightPrefix_birthday_add_wpow_mul_nat_of_initial_block
    {H s w : Surreal.{u}} (hH : H.support ⊆ Ici w) (hw : w ∈ rightPrefixes s)
    (hf : (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    {r : ℝ} (hr : (r : Surreal.{u}) = appendPlus (H.coeff w : Surreal.{u}))
    (hblock : appendPluses H (ω^ (plusCount w)).val =
      H.normalFormTrunc w + (r : Surreal) * ω^ w) (n : ℕ) :
    ∃ p ∈ rightPrefixes (H + ω^ s),
      p.birthday = NatOrdinal.of (H.birthday.val + (ω^ (plusCount w)).val * (n + 1)) := by
  obtain ⟨r, _, _, har, hL, hb⟩ := exists_head_coeff_minus_stages hf hr hblock n
  have hlt : H.coeff w < r :=
    Real.toSurreal_lt_iff.mp (mem_leftPrefixes_iff.mp har).2
  exact ⟨_, head_real_mul_wpow_mem_rightPrefixes_of_leftPrefixes_le hH hw hlt hL, hb⟩

/-- Every finite boundary block is an actual canonical right prefix, with the
coefficient's original minus stages preserving their exact ordinal lengths. -/
theorem exists_head_rightPrefix_birthday_add_wpow_mul_nat
    {H s w : Surreal.{u}} (hH : H.support ⊆ Ici w) (hw : w ∈ rightPrefixes s)
    (hc : H.coeff w ≠ 0)
    (hf : (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) (n : ℕ) :
    ∃ p ∈ rightPrefixes (H + ω^ s),
      p.birthday = NatOrdinal.of (H.birthday.val + (ω^ (plusCount w)).val * (n + 1)) := by
  have hK : (H.normalFormTrunc w).support ⊆ Ioi w := by
    simp only [support_trunc]
    exact inter_subset_right
  obtain ⟨q, _, hq, hblock⟩ := exists_dyadic_head_coefficient_plus_block
    (H.normalFormTrunc w) w hK hc hf
  have hr : ((q.toRat : ℝ) : Surreal.{u}) = appendPlus (H.coeff w : Surreal.{u}) := by
    simpa only [Real.toSurreal_ratCast] using hq
  have hdecomp := eq_trunc_add_coeff_wpow_of_support_ge hH
  rw [← hdecomp] at hblock
  apply exists_head_rightPrefix_birthday_add_wpow_mul_nat_of_initial_block hH hw hf hr
  simpa only [Real.toSurreal_ratCast] using hblock

/-- The entire retained boundary minus block fits inside the actual source birthday. -/
theorem birthday_add_wpow_mul_omega0_le_of_retained_boundary
    {H s w : Surreal.{u}} (hH : H.support ⊆ Ici w) (hw : w ∈ rightPrefixes s)
    (hc : H.coeff w ≠ 0)
    (hf : (H.coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) :
    H.birthday.val + (ω^ (plusCount w)).val * Ordinal.omega0 ≤ (H + ω^ s).birthday.val := by
  have hfinite : ∀ n : ℕ, H.birthday.val + (ω^ (plusCount w)).val * (n + 1) <
      (H + ω^ s).birthday.val := by
    intro n
    obtain ⟨p, hp, hb⟩ := exists_head_rightPrefix_birthday_add_wpow_mul_nat hH hw hc hf n
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

end Surreal
