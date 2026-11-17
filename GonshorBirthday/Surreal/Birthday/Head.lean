/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.CoefficientPrefix
public import GonshorBirthday.Surreal.Birthday.Real
public import GonshorBirthday.Surreal.HahnSeries.BirthdayGap

/-!
# Canonical gaps below an arbitrary higher normal-form head
-/

universe u
public noncomputable section
namespace Surreal
open Set IGame

/-- A younger number differs from a strictly higher head at a strictly higher exponent. -/
theorem lt_wlog_sub_of_birthday_lt {x p s : Surreal.{u}}
    (hs : x.support ⊆ Ioi s) (hp : p.birthday < x.birthday) : s < (p - x).wlog := by
  by_contra hn
  have hg : (p - x).wlog ≤ s := le_of_not_gt hn
  have hpre : birthdayTruncation p x.birthday = x := by
    have hh : x.support ⊆ Ioi (p - x).wlog := fun j hj ↦ hg.trans_lt (hs hj)
    simpa only [← add_sub_assoc, add_sub_cancel_left] using
      birthdayTruncation_add_of_support_lt hh
  have hb : x.birthday ≤ p.birthday := by
    rw [← hpre]
    exact birthday_birthdayTruncation_le_birthday p _
  exact hp.not_ge hb

/-- Every finite real monomial multiple lies inside every younger gap of a higher head. -/
theorem real_mul_wpow_lt_abs_sub_of_birthday_lt {x p s : Surreal.{u}}
    (hs : x.support ⊆ Ioi s) (hp : p.birthday < x.birthday) (r : ℝ) :
    (r : Surreal) * ω^ s < |p - x| := by
  have hne : p - x ≠ 0 := by
    intro he
    exact hp.ne (congrArg birthday (sub_eq_zero.mp he))
  have hv : ω^ s <ᵥ p - x := by
    rw [← wlog_lt_wlog_iff (wpow_ne_zero _) hne, wlog_wpow]
    exact lt_wlog_sub_of_birthday_lt hs hp
  obtain ⟨n, hn⟩ := exists_nat_gt r
  have hcoeff : (r : Surreal.{u}) ≤ (n : Surreal) := by exact_mod_cast hn.le
  have hg := (ArchimedeanClass.mk_lt_mk.mp (vlt_def.mp hv)) n
  have hg' : (n : Surreal) * ω^ s < |p - x| := by
    simpa only [wpow_abs, nsmul_eq_mul] using hg
  exact (mul_le_mul_of_nonneg_right hcoeff (wpow_nonneg s)).trans_lt hg'

/-- Translation preserves a canonical prefix when every head-option gap stays open. -/
theorem birthdayTruncation_add_of_prefix_of_head_gaps {K a b : Surreal.{u}}
    (hp : birthdayTruncation a b.birthday = b)
    (hL : ∀ p ∈ leftPrefixes K, p + b < K + a)
    (hR : ∀ p ∈ rightPrefixes K, K + a < p + b) :
    birthdayTruncation (K + a) (K + b).birthday = K + b := by
  have heK := ofSets_eq_mk (s := leftPrefixes K) (t := rightPrefixes K)
    (H := leftPrefixes_lt_rightPrefixes K)
  have heB := ofSets_eq_mk (s := leftPrefixes b) (t := rightPrefixes b)
    (H := leftPrefixes_lt_rightPrefixes b)
  generalize_proofs at heK heB
  rw [ofSets_leftPrefixes_rightPrefixes] at heK heB
  let k : IGame.{u} := !{out '' leftPrefixes K | out '' rightPrefixes K}
  let f : IGame.{u} := !{out '' leftPrefixes b | out '' rightPrefixes b}
  have : Numeric k := by assumption
  have : Numeric f := by assumption
  change K = mk k at heK
  change b = mk f at heB
  have htail : Fits a.out f := by
    constructor
    · intro p hpf
      rw [moves_left_ofSets] at hpf
      obtain ⟨p, hpf, rfl⟩ := hpf
      have hpa := leftPrefixes_subset_of_birthdayTruncation_eq hp hpf
      rw [← mk_le_mk, out_eq, out_eq]
      exact (mem_leftPrefixes_iff.mp hpa).2.not_ge
    · intro p hpf
      rw [moves_right_ofSets] at hpf
      obtain ⟨p, hpf, rfl⟩ := hpf
      have hpa := rightPrefixes_subset_of_birthdayTruncation_eq hp hpf
      rw [← mk_le_mk, out_eq, out_eq]
      exact (mem_rightPrefixes_iff.mp hpa).2.not_ge
  have hf : Fits (k + a.out) (k + f) := by
    constructor
    · intro z hz
      rw [moves_add] at hz
      rcases hz with ⟨p, hpk, rfl⟩ | ⟨p, hpf, rfl⟩
      · rw [moves_left_ofSets] at hpk
        obtain ⟨p, hpk, rfl⟩ := hpk
        rw [← mk_le_mk, mk_add, mk_add, out_eq, out_eq, ← heK, ← heB]
        exact (hL p hpk).not_ge
      · numeric
        have hpa : p < a.out := by
          rw [← mk_lt_mk, lt_iff_not_ge, mk_le_mk]
          exact htail.1 p hpf
        exact (add_lt_add_right hpa k).not_ge
    · intro z hz
      rw [moves_add] at hz
      rcases hz with ⟨p, hpk, rfl⟩ | ⟨p, hpf, rfl⟩
      · rw [moves_right_ofSets] at hpk
        obtain ⟨p, hpk, rfl⟩ := hpk
        rw [← mk_le_mk, mk_add, mk_add, out_eq, out_eq, ← heK, ← heB]
        exact (hR p hpk).not_ge
      · numeric
        have hap : a.out < p := by
          rw [← mk_lt_mk, lt_iff_not_ge, mk_le_mk]
          exact htail.2 p hpf
        exact (add_lt_add_right hap k).not_ge
  have ht := hf.birthdayTruncation_eq
  simpa only [mk_add, out_eq, ← heK, ← heB] using ht

/-- Arbitrary higher normal-form heads preserve real coefficient canonical prefixes. -/
theorem birthdayTruncation_head_real_mul_wpow_of_prefix (K : Surreal.{u}) (u : Surreal.{u})
    (hK : K.support ⊆ Ioi u) {r s : ℝ}
    (hp : birthdayTruncation (r : Surreal.{u}) (s : Surreal).birthday = (s : Surreal)) :
    birthdayTruncation (K + (r : Surreal) * ω^ u) (K + (s : Surreal) * ω^ u).birthday =
      K + (s : Surreal) * ω^ u := by
  apply birthdayTruncation_add_of_prefix_of_head_gaps
    (birthdayTruncation_real_mul_wpow_of_prefix hp u)
  · intro p hpk
    have hgap := real_mul_wpow_lt_abs_sub_of_birthday_lt hK
      (birthday_lt_of_mem_leftPrefixes hpk) (s - r)
    rw [abs_of_neg (sub_neg.mpr (mem_leftPrefixes_iff.mp hpk).2), neg_sub,
      Real.toSurreal_sub] at hgap
    nlinarith only [hgap]
  · intro p hpk
    have hgap := real_mul_wpow_lt_abs_sub_of_birthday_lt hK
      (birthday_lt_of_mem_rightPrefixes hpk) (r - s)
    rw [abs_of_pos (sub_pos.mpr (mem_rightPrefixes_iff.mp hpk).2),
      Real.toSurreal_sub] at hgap
    nlinarith only [hgap]

/-- Fitting finite coefficient cuts remain canonical prefixes after an arbitrary higher head. -/
theorem birthdayTruncation_head_real_mul_wpow_of_fits (K : Surreal.{u}) (u : Surreal.{u})
    (hK : K.support ⊆ Ioi u) {r : ℝ} {g : IGame.{u}} [Short g] [Numeric g]
    (h : Fits (r : IGame) g) :
    birthdayTruncation (K + (r : Surreal) * ω^ u) (K + mk g * ω^ u).birthday =
      K + mk g * ω^ u := by
  have hg : mk g = Real.toSurreal g.toDyadic.toRat := by
    rw [Real.toSurreal_ratCast]
    exact (ratCast_toDyadic g).symm
  have hp := h.birthdayTruncation_eq
  rw [mk_real_toIGame, hg] at hp
  rw [hg]
  exact birthdayTruncation_head_real_mul_wpow_of_prefix K u hK hp

/-- A perturbation below the head's support lies inside every younger head gap. -/
theorem abs_lt_abs_sub_of_wlog_le_of_birthday_lt {K p d s : Surreal.{u}}
    (hK : K.support ⊆ Ioi s) (hp : p.birthday < K.birthday) (hd : d.wlog ≤ s) :
    |d| < |p - K| := by
  have hgap : p - K ≠ 0 := by
    intro he
    exact hp.ne (congrArg birthday (sub_eq_zero.mp he))
  by_cases hzero : d = 0
  · simpa only [hzero, abs_zero] using abs_pos.mpr hgap
  · have hv : d <ᵥ p - K := by
      rw [← wlog_lt_wlog_iff hzero hgap]
      exact hd.trans_lt (lt_wlog_sub_of_birthday_lt hK hp)
    have h := (ArchimedeanClass.mk_lt_mk.mp (vlt_def.mp hv)) 1
    simpa only [one_nsmul] using h

/-- Canonical prefix transport past a higher head for a scale-bounded change. -/
theorem birthdayTruncation_head_add_of_wlog_sub_le {K a b s : Surreal.{u}}
    (hK : K.support ⊆ Ioi s) (hp : birthdayTruncation a b.birthday = b)
    (hab : (a - b).wlog ≤ s) :
    birthdayTruncation (K + a) (K + b).birthday = K + b := by
  apply birthdayTruncation_add_of_prefix_of_head_gaps hp
  · intro p hpk
    have hg := abs_lt_abs_sub_of_wlog_le_of_birthday_lt hK
      (birthday_lt_of_mem_leftPrefixes hpk) hab
    rw [abs_of_neg (sub_neg.mpr (mem_leftPrefixes_iff.mp hpk).2), neg_sub] at hg
    have hb := neg_abs_le (a - b)
    linarith only [hb, hg]
  · intro p hpk
    have hg := abs_lt_abs_sub_of_wlog_le_of_birthday_lt hK
      (birthday_lt_of_mem_rightPrefixes hpk) hab
    rw [abs_of_pos (sub_pos.mpr (mem_rightPrefixes_iff.mp hpk).2)] at hg
    have hb := (le_abs_self (a - b)).trans_lt hg
    linarith only [hb]

/-- Canonical right prefixes of a nondyadic real are coinitial above that real. -/
theorem exists_real_rightPrefix_lt {r t : ℝ}
    (hb : (r : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0) (hrt : r < t) :
    ∃ s : ℝ, (s : Surreal.{u}) ∈ rightPrefixes (r : Surreal.{u}) ∧ s < t := by
  obtain ⟨q, hrq, hqt⟩ := exists_dyadic_btwn hrt
  have hqb : (q : Surreal.{u}).birthday < (r : Surreal.{u}).birthday := by
    rw [hb]
    exact birthday_dyadic_lt_omega0 q
  have hrqs : (r : Surreal.{u}) < (q : Surreal.{u}) := by
    rw [← Real.toSurreal_ratCast]
    exact Real.toSurreal_lt_iff.mpr hrq
  obtain ⟨a, ha, hra, haq⟩ := exists_birthdayTruncation_right_le hqb hrqs
  obtain ⟨s, hs⟩ := birthdayTruncation_real_mem_range_real r a
  refine ⟨s, ?_, ?_⟩
  · rw [hs]
    exact mem_rightPrefixes.mpr ⟨a, ha, rfl, hra⟩
  · have hsq : s ≤ (q.toRat : ℝ) := by
      apply Real.toSurreal_le_iff.mp
      rw [Real.toSurreal_ratCast, hs]
      exact haq
    exact hsq.trans_lt hqt

/-- A higher normal-form head preserves the coinitial real-coefficient right prefixes. -/
theorem exists_head_real_mul_wpow_rightPrefix_lt (K u : Surreal.{u})
    (hK : K.support ⊆ Ioi u) {r t : ℝ}
    (hb : (r : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0) (hrt : r < t) :
    ∃ s : ℝ, K + (s : Surreal) * ω^ u ∈ rightPrefixes (K + (r : Surreal) * ω^ u) ∧
      s < t := by
  obtain ⟨s, hs, hst⟩ := exists_real_rightPrefix_lt hb hrt
  refine ⟨s, mem_rightPrefixes_iff.mpr ⟨?_, ?_⟩, hst⟩
  · exact birthdayTruncation_head_real_mul_wpow_of_prefix K u hK
      (mem_rightPrefixes_iff.mp hs).1
  · exact add_lt_add_right (mul_lt_mul_of_pos_right (mem_rightPrefixes_iff.mp hs).2
      (wpow_pos u)) K

/-- A headed monomial has no normal-form exponents below its last exponent. -/
theorem support_head_real_mul_wpow_subset (K u : Surreal.{u})
    (hK : K.support ⊆ Ioi u) (r : ℝ) :
    (K + (r : Surreal) * ω^ u).support ⊆ Ici u := by
  intro i hi
  rcases support_add_subset hi with hi | hi
  · exact Set.mem_Ici.mpr (Set.mem_Ioi.mp (hK hi)).le
  · have hm : ((r : Surreal.{u}) * ω^ u).toHahnSeries =
        SurrealHahnSeries.single u r :=
      toHahnSeries_eq (SurrealHahnSeries.toSurreal_single u r)
    have hi' : i ∈ (SurrealHahnSeries.single u r).support := by
      rw [← hm, support_toHahnSeries]
      exact hi
    have he := SurrealHahnSeries.support_single_subset hi'
    exact le_of_eq (Set.mem_singleton_iff.mp he).symm

/-- Every younger positive gap above a headed monomial dominates a positive real multiple. -/
theorem exists_real_mul_wpow_lt_rightPrefix_gap (K u : Surreal.{u})
    (hK : K.support ⊆ Ioi u) (r : ℝ) {p : Surreal.{u}}
    (hp : p ∈ rightPrefixes (K + (r : Surreal) * ω^ u)) :
    ∃ δ : ℝ, 0 < δ ∧ (δ : Surreal) * ω^ u < p - (K + (r : Surreal) * ω^ u) := by
  let x := K + (r : Surreal) * ω^ u
  have hpx : x < p := (mem_rightPrefixes_iff.mp hp).2
  have hne : p - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hpx)
  have hv : ω^ u ≤ᵥ p - x := by
    rw [← wlog_le_wlog_iff (wpow_ne_zero _) hne, wlog_wpow]
    exact le_wlog_sub_of_birthday_lt (support_head_real_mul_wpow_subset K u hK r)
      (birthday_lt_of_mem_rightPrefixes hp)
  obtain ⟨n, hn⟩ := ArchimedeanClass.mk_le_mk.mp (vle_def.mp hv)
  have hn' : ω^ u ≤ (n : Surreal) * (p - x) := by
    simpa only [wpow_abs, abs_of_pos (sub_pos.mpr hpx), nsmul_eq_mul] using hn
  have hd : 0 < (n : ℝ) + 1 := by positivity
  refine ⟨((n : ℝ) + 1)⁻¹, inv_pos.mpr hd, ?_⟩
  have hds : 0 < ((n : Surreal) + 1) := by positivity
  have hh : ω^ u < ((n : Surreal) + 1) * (p - x) := by
    nlinarith only [hn', sub_pos.mpr hpx]
  rw [Real.toSurreal_inv, Real.toSurreal_add, Real.toSurreal_natCast,
    Real.toSurreal_one]
  calc
    ((n : Surreal) + 1)⁻¹ * ω^ u = ω^ u / ((n : Surreal) + 1) := by ring
    _ < p - x := (div_lt_iff₀ hds).mpr (by simpa only [mul_comm] using hh)

/-- A nondyadic last coefficient supplies a coinitial gap-halving canonical right family. -/
theorem exists_head_real_mul_wpow_rightPrefix_half_gap (K u : Surreal.{u})
    (hK : K.support ⊆ Ioi u) {r : ℝ}
    (hb : (r : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0) {p : Surreal.{u}}
    (hp : p ∈ rightPrefixes (K + (r : Surreal) * ω^ u)) :
    ∃ s : ℝ, K + (s : Surreal) * ω^ u ∈ rightPrefixes (K + (r : Surreal) * ω^ u) ∧
      2 * ((K + (s : Surreal) * ω^ u) - (K + (r : Surreal) * ω^ u)) <
        p - (K + (r : Surreal) * ω^ u) := by
  obtain ⟨δ, hd, hgap⟩ := exists_real_mul_wpow_lt_rightPrefix_gap K u hK r hp
  obtain ⟨s, hs, hst⟩ := exists_head_real_mul_wpow_rightPrefix_lt K u hK hb
    (show r < r + δ / 2 by linarith)
  refine ⟨s, hs, ?_⟩
  have hst' : (s : Surreal.{u}) < (r : Surreal) + (δ : Surreal) / 2 := by
    have hh := Real.toSurreal_lt_iff.mpr hst
    simpa using hh
  have hscaled := mul_lt_mul_of_pos_right hst' (wpow_pos u)
  nlinarith only [hgap, hscaled]

end Surreal
