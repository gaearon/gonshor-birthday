/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadPerturbation
public import GonshorBirthday.Surreal.Birthday.Perturbation

import GonshorBirthday.Surreal.Birthday.ReciprocalCoefficient
import GonshorBirthday.Surreal.Birthday.LastMinusFamily

/-!
# Shifted dyadic coefficient boundary families

Uniform canonical coefficient neighbours permit translating reciprocal monomial
prefixes through a dyadic coefficient at the same exponent. A higher head is arbitrary.
At an exponent's final minus, these actual right prefixes form a coinitial family
whose gaps can be strictly halved, including the zero and negative coefficient boundaries.
-/

universe u
public noncomputable section
namespace Surreal
open Set

/-- Uniform real coefficient neighbours permit translating a fitting monomial prefix. -/
theorem birthdayTruncation_real_mul_wpow_add_of_neighbors
    {a l r c : ℝ} {w b : Surreal.{u}}
    (hl : birthdayTruncation (l : Surreal.{u}) (a : Surreal).birthday = a)
    (hr : birthdayTruncation (r : Surreal.{u}) (a : Surreal).birthday = a)
    (hcl : c < a - l) (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hbr : b < ((r - a : ℝ) : Surreal) * ω^ w)
    (hp : birthdayTruncation b ((c : Surreal) * ω^ w).birthday = (c : Surreal) * ω^ w) :
    birthdayTruncation ((a : Surreal) * ω^ w + b)
      ((a : Surreal) * ω^ w + (c : Surreal) * ω^ w).birthday =
        (a : Surreal) * ω^ w + (c : Surreal) * ω^ w := by
  apply birthdayTruncation_add_of_prefix_of_head_gaps hp
  · intro p hpa
    have hpp := leftPrefixes_subset_of_birthdayTruncation_eq
      (birthdayTruncation_real_mul_wpow_of_prefix hl w) hpa
    have hpc : (c : Surreal.{u}) * ω^ w < ((a - l : ℝ) : Surreal) * ω^ w :=
      mul_lt_mul_of_pos_right (Real.toSurreal_lt_iff.mpr hcl) (wpow_pos w)
    have hpl' := (mem_leftPrefixes_iff.mp hpp).2
    rw [Real.toSurreal_sub, sub_mul] at hpc
    linarith only [hpc, hpl', hb]
  · intro p hpa
    have hpp := rightPrefixes_subset_of_birthdayTruncation_eq
      (birthdayTruncation_real_mul_wpow_of_prefix hr w) hpa
    have hpr := (mem_rightPrefixes_iff.mp hpp).2
    have hcz := mul_nonneg (Real.toSurreal_nonneg_iff.mpr hc) (wpow_nonneg w)
    rw [Real.toSurreal_sub, sub_mul] at hbr
    linarith only [hpr, hcz, hbr]

/-- A higher head preserves prefix translation between uniform coefficient neighbours. -/
theorem birthdayTruncation_head_real_mul_wpow_add_of_neighbors
    (K w : Surreal.{u}) (hK : K.support ⊆ Ioi w) {a l r c : ℝ} {b : Surreal.{u}}
    (hl : birthdayTruncation (l : Surreal.{u}) (a : Surreal).birthday = a)
    (hr : birthdayTruncation (r : Surreal.{u}) (a : Surreal).birthday = a)
    (hcl : c < a - l) (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hbr : b < ((r - a : ℝ) : Surreal) * ω^ w)
    (hp : birthdayTruncation b ((c : Surreal) * ω^ w).birthday = (c : Surreal) * ω^ w) :
    birthdayTruncation (K + ((a : Surreal) * ω^ w + b))
      (K + ((a : Surreal) * ω^ w + (c : Surreal) * ω^ w)).birthday =
        K + ((a : Surreal) * ω^ w + (c : Surreal) * ω^ w) := by
  apply birthdayTruncation_head_add_of_abs_sub_le_real_mul_wpow hK
    (birthdayTruncation_real_mul_wpow_add_of_neighbors hl hr hcl hc hb hbr hp) (r - a + c)
  have hcz := mul_nonneg (Real.toSurreal_nonneg_iff.mpr hc) (wpow_nonneg w)
  rw [Real.toSurreal_add, Real.toSurreal_sub, add_mul, sub_mul]
  rw [Real.toSurreal_sub, sub_mul] at hbr
  apply abs_le.mpr
  constructor <;> linarith only [hb, hcz, hbr]

private theorem realCast_inv_two_pow (n : ℕ) :
    Real.toSurreal ((2 : ℝ)⁻¹ ^ n) = (2 : Surreal.{u})⁻¹ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Real.toSurreal_mul, ih, Real.toSurreal_inv]
    norm_num only [Real.toSurreal_ofNat]
    rw [pow_succ]

/-- Positive real lower terms admit shifted reciprocal prefixes at a dyadic boundary. -/
theorem exists_head_shifted_reciprocal_wpow_rightPrefixes_of_pos
    (K w : Surreal.{u}) (hK : K.support ⊆ Ioi w) {a : ℝ}
    (ha : (a : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    {t : ℝ} (ht : 0 < t) {s : Surreal.{u}} (hw : w ∈ rightPrefixes s) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K + ((a : Surreal) * ω^ w + (2 : Surreal)⁻¹ ^ n * ω^ w) ∈
        rightPrefixes (K + ((a : Surreal) * ω^ w + (t : Surreal) * ω^ s)) := by
  obtain ⟨l, hl⟩ := exists_real_appendMinus_of_birthday_lt_omega0 ha
  obtain ⟨r, hr⟩ := exists_real_appendPlus_of_birthday_lt_omega0 ha
  have hla : l < a := Real.toSurreal_lt_iff.mp (by rw [hl]; exact appendMinus_lt _)
  have har : a < r := Real.toSurreal_lt_iff.mp (by rw [hr]; exact lt_appendPlus _)
  have hlp : birthdayTruncation (l : Surreal.{u}) (a : Surreal).birthday = a := by
    rw [hl]
    exact birthdayTruncation_appendMinus _
  have hrp : birthdayTruncation (r : Surreal.{u}) (a : Surreal).birthday = a := by
    rw [hr]
    exact birthdayTruncation_appendPlus _
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hla)
    (show (2 : ℝ)⁻¹ < 1 by norm_num)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hcn : (2 : ℝ)⁻¹ ^ n < a - l := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [pow_add]
    apply (mul_le_of_le_one_right (by positivity)
      (pow_le_one₀ (by positivity) (by norm_num))).trans_lt hN
  have hb : (t : Surreal) * ω^ s < ((r - a : ℝ) : Surreal.{u}) * ω^ w := by
    have ht := mul_wpow_lt_mul_wpow_of_pos t (sub_pos.mpr har)
      (mem_rightPrefixes_iff.mp hw).2
    simpa using ht
  have hcp := rightPrefixes_subset_of_birthdayTruncation_eq
    (birthdayTruncation_real_mul_wpow t ht s)
    (inv_two_pow_mul_wpow_mem_rightPrefixes hw n)
  have hpt : birthdayTruncation ((t : Surreal) * ω^ s)
      (((((2 : ℝ)⁻¹ ^ n) : ℝ) : Surreal.{u}) * ω^ w).birthday =
        (((((2 : ℝ)⁻¹ ^ n) : ℝ) : Surreal.{u}) * ω^ w) := by
    rw [realCast_inv_two_pow]
    exact (mem_rightPrefixes_iff.mp hcp).1
  have hpre := birthdayTruncation_head_real_mul_wpow_add_of_neighbors K w hK
    hlp hrp hcn (by positivity)
      (mul_nonneg (Real.toSurreal_pos_iff.mpr ht).le (wpow_nonneg s)) hb hpt
  rw [realCast_inv_two_pow] at hpre
  exact mem_rightPrefixes_iff.mpr ⟨hpre,
    add_lt_add_right (add_lt_add_right (mem_rightPrefixes_iff.mp hcp).2 _) K⟩

/-- Late shifted reciprocal monomials are canonical right prefixes at a dyadic boundary. -/
theorem exists_head_shifted_reciprocal_wpow_rightPrefixes
    (K w : Surreal.{u}) (hK : K.support ⊆ Ioi w) {a : ℝ}
    (ha : (a : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    {s : Surreal.{u}} (hw : w ∈ rightPrefixes s) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K + ((a : Surreal) * ω^ w + (2 : Surreal)⁻¹ ^ n * ω^ w) ∈
        rightPrefixes (K + ((a : Surreal) * ω^ w + ω^ s)) := by
  have ht := exists_head_shifted_reciprocal_wpow_rightPrefixes_of_pos K w hK ha
    (t := (1 : ℝ)) (by norm_num) hw
  simpa only [Real.toSurreal_one, one_mul] using ht

private theorem inv_two_pow_antitone {m n : ℕ} (hmn : m ≤ n) :
    (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add]
  exact mul_le_of_le_one_right (by positivity)
    (pow_le_one₀ (by positivity) (by norm_num))

/-- A lower bound for all right exponents gives coinitial reciprocal monomials. -/
theorem exists_inv_two_pow_mul_wpow_le_of_le_rightPrefixes
    (w s : Surreal.{u}) (hmin : ∀ v ∈ rightPrefixes s, w ≤ v) (N : ℕ)
    {p : Surreal.{u}} (hp : p ∈ rightPrefixes (ω^ s)) :
    ∃ n : ℕ, N ≤ n ∧ (2 : Surreal)⁻¹ ^ n * ω^ w ≤ p := by
  obtain ⟨v, hv, m, hmp⟩ := exists_inv_two_pow_mul_wpow_le_of_mem_rightPrefixes hp
  have hwv := hmin v hv
  obtain hwv | rfl := hwv.lt_or_eq
  · refine ⟨N, le_rfl, ?_⟩
    have ht := mul_wpow_lt_mul_wpow_of_pos ((2 : ℝ)⁻¹ ^ N)
      (show 0 < (2 : ℝ)⁻¹ ^ m by positivity) hwv
    rw [realCast_inv_two_pow, realCast_inv_two_pow] at ht
    exact ht.le.trans hmp
  · refine ⟨max N m, le_max_left _ _, ?_⟩
    have hc := Real.toSurreal_le_iff.mpr (inv_two_pow_antitone (le_max_right N m))
    rw [realCast_inv_two_pow, realCast_inv_two_pow] at hc
    exact (mul_le_mul_of_nonneg_right hc (wpow_nonneg w)).trans hmp

/-- Every reciprocal tail is coinitial above an omega-map at an exponent minus successor. -/
theorem exists_inv_two_pow_mul_wpow_le_of_appendMinus (w : Surreal.{u}) (N : ℕ)
    {p : Surreal.{u}} (hp : p ∈ rightPrefixes (ω^ (appendMinus w))) :
    ∃ n : ℕ, N ≤ n ∧ (2 : Surreal)⁻¹ ^ n * ω^ w ≤ p := by
  exact exists_inv_two_pow_mul_wpow_le_of_le_rightPrefixes w (appendMinus w)
    (fun _ hv ↦ le_of_mem_rightPrefixes_appendMinus hv) N hp

/-- A least right exponent gives a shifted dyadic boundary gap-halving family. -/
theorem exists_head_shifted_reciprocal_wpow_halving_family_of_min_rightPrefix
    (K w : Surreal.{u}) (hK : K.support ⊆ Ioi w) {a : ℝ}
    (ha : (a : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0)
    {s : Surreal.{u}} (hw : w ∈ rightPrefixes s)
    (hmin : ∀ v ∈ rightPrefixes s, w ≤ v) :
    let X := K + ((a : Surreal) * ω^ w + ω^ s)
    let P := fun n : ℕ ↦ K + ((a : Surreal) * ω^ w + (2 : Surreal)⁻¹ ^ n * ω^ w)
    ∃ N : ℕ, (∀ n : ℕ, N ≤ n → P n ∈ rightPrefixes X) ∧
      (∀ p ∈ rightPrefixes X, ∃ n : ℕ, N ≤ n ∧ P n ≤ p) ∧
      (∀ n : ℕ, N ≤ n → 2 * (P (n + 1) - X) < P n - X) := by
  dsimp only
  obtain ⟨N, hN⟩ := exists_head_shifted_reciprocal_wpow_rightPrefixes K w hK ha hw
  refine ⟨N, hN, ?_, ?_⟩
  · intro p hp
    rw [← add_assoc] at hp
    rcases exists_rightPrefixes_add_le hp with ⟨q, hq, hqp⟩ | ⟨q, hq, hqp⟩
    · obtain ⟨r, hr⟩ := exists_real_appendPlus_of_birthday_lt_omega0 ha
      have har : a < r := Real.toSurreal_lt_iff.mp (by rw [hr]; exact lt_appendPlus _)
      have hrp : birthdayTruncation (r : Surreal.{u}) (a : Surreal).birthday = a := by
        rw [hr]
        exact birthdayTruncation_appendPlus _
      have hpre := birthdayTruncation_head_real_mul_wpow_of_prefix K w hK hrp
      have hqr := rightPrefixes_subset_of_birthdayTruncation_eq hpre hq
      have hlt := (mem_rightPrefixes_iff.mp hqr).2
      obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr har)
        (show (2 : ℝ)⁻¹ < 1 by norm_num)
      refine ⟨max N M, le_max_left _ _, ?_⟩
      have hc := (inv_two_pow_antitone (le_max_right N M)).trans_lt hM
      have hcm := mul_lt_mul_of_pos_right (Real.toSurreal_lt_iff.mpr hc) (wpow_pos w)
      rw [realCast_inv_two_pow, Real.toSurreal_sub, sub_mul] at hcm
      have hb := wpow_pos s
      linarith only [hcm, hlt, hb, hqp]
    · obtain ⟨n, hn, hnq⟩ := exists_inv_two_pow_mul_wpow_le_of_le_rightPrefixes w s hmin N hq
      refine ⟨n, hn, ?_⟩
      simpa only [add_assoc] using
        (add_le_add_right hnq (K + (a : Surreal) * ω^ w)).trans hqp
  · intro n _
    have he : 2 * ((2 : Surreal.{u})⁻¹ ^ (n + 1) * ω^ w) =
        (2 : Surreal)⁻¹ ^ n * ω^ w := by
      rw [pow_succ]
      field_simp
    have hb := wpow_pos s
    linarith only [he, hb]

/-- A dyadic coefficient boundary admits a coinitial canonical right gap-halving family. -/
theorem exists_head_shifted_reciprocal_wpow_halving_family
    (K w : Surreal.{u}) (hK : K.support ⊆ Ioi w) {a : ℝ}
    (ha : (a : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) :
    let X := K + ((a : Surreal) * ω^ w + ω^ (appendMinus w))
    let P := fun n : ℕ ↦ K + ((a : Surreal) * ω^ w + (2 : Surreal)⁻¹ ^ n * ω^ w)
    ∃ N : ℕ, (∀ n : ℕ, N ≤ n → P n ∈ rightPrefixes X) ∧
      (∀ p ∈ rightPrefixes X, ∃ n : ℕ, N ≤ n ∧ P n ≤ p) ∧
      (∀ n : ℕ, N ≤ n → 2 * (P (n + 1) - X) < P n - X) := by
  exact exists_head_shifted_reciprocal_wpow_halving_family_of_min_rightPrefix K w hK ha
    (mem_rightPrefixes_iff.mpr ⟨birthdayTruncation_appendMinus w, appendMinus_lt w⟩)
    (fun _ hv ↦ le_of_mem_rightPrefixes_appendMinus hv)

/-- Every real coefficient boundary admits arbitrarily small positive coefficient prefixes. -/
theorem exists_head_real_mul_wpow_rightPrefix_lt_add
    (K w : Surreal.{u}) (hK : K.support ⊆ Ioi w) (a : ℝ) {t : ℝ} (ht : 0 < t)
    {s : Surreal.{u}} (hw : w ∈ rightPrefixes s) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℝ, a < q ∧ q < a + ε ∧ K + (q : Surreal) * ω^ w ∈
      rightPrefixes (K + ((a : Surreal) * ω^ w + (t : Surreal) * ω^ s)) := by
  by_cases ha : (a : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0
  · obtain ⟨N, hN⟩ := exists_head_shifted_reciprocal_wpow_rightPrefixes_of_pos K w hK ha ht hw
    obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hε (show (2 : ℝ)⁻¹ < 1 by norm_num)
    let n := max N M
    have hcn : (2 : ℝ)⁻¹ ^ n < ε :=
      (inv_two_pow_antitone (le_max_right N M)).trans_lt hM
    refine ⟨a + (2 : ℝ)⁻¹ ^ n,
      lt_add_of_pos_right a (by positivity), by linarith only [hcn], ?_⟩
    rw [Real.toSurreal_add, add_mul, realCast_inv_two_pow]
    exact hN n (le_max_left _ _)
  · have hb : (a : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0 :=
      le_antisymm (birthday_real_le_omega0 a) (le_of_not_gt ha)
    obtain ⟨q, hqa, hqε⟩ := exists_real_rightPrefix_lt hb
      (show a < a + ε by linarith only [hε])
    have hqp : K + (q : Surreal) * ω^ w ∈ rightPrefixes (K + (a : Surreal) * ω^ w) := by
      apply mem_rightPrefixes_iff.mpr
      exact ⟨birthdayTruncation_head_real_mul_wpow_of_prefix K w hK
        (mem_rightPrefixes_iff.mp hqa).1,
        add_lt_add_right (mul_lt_mul_of_pos_right (mem_rightPrefixes_iff.mp hqa).2
          (wpow_pos w)) K⟩
    have hsupp : (K + (a : Surreal) * ω^ w).support ⊆ Ioi ((t : Surreal) * ω^ s).wlog := by
      rw [wlog_mul (Real.toSurreal_pos_iff.mpr ht).ne' (wpow_ne_zero _),
        wlog_realCast, wlog_wpow, zero_add]
      intro i hi
      exact (mem_rightPrefixes_iff.mp hw).2.trans_le
        (support_head_real_mul_wpow_subset K w hK a hi)
    have hpre := birthdayTruncation_add_of_support_lt hsupp
    have hq := rightPrefixes_subset_of_birthdayTruncation_eq hpre hqp
    refine ⟨q, Real.toSurreal_lt_iff.mp (mem_rightPrefixes_iff.mp hqa).2, hqε, ?_⟩
    simpa only [add_assoc] using hq

end Surreal
