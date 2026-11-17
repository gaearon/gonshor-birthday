/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Real
public import GonshorBirthday.Surreal.Birthday.Dyadic
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.Algebra.Algebra.Rat

import GonshorBirthday.Surreal.Birthday.RealMultiplication
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Analysis.Real.Cardinality

/-!
# Positive coefficient replacements

A dyadic coefficient is replaced by its finite birthday; every nondyadic coefficient
is replaced by one common positive transcendental real. This preserves individual
birthdays and dyadicness. In each finite product fibre, the birthday of the original
coefficient sum is at most the birthday of its replacement sum, including when
original summands cancel.

Nonnegative polynomial coefficients prevent cancellation at the transcendental
value. This supplies a scalar comparison independent of normal-form sign deletion.
-/

universe u v
public noncomputable section
open Polynomial

namespace Surreal

/-- There is a positive real transcendental over the rationals. -/
theorem exists_pos_transcendental_real : ∃ τ : ℝ, 0 < τ ∧ Transcendental ℚ τ := by
  classical
  by_contra! h
  have hc : (Set.Ioo (0 : ℝ) 1).Countable := (Algebraic.countable ℚ ℝ).mono
    (fun x hx ↦ by simpa only [Transcendental, not_not, Set.mem_ofPred_eq] using h x hx.1)
  have hf := Cardinal.Real.Ioo_countable_iff.mp hc
  norm_num at hf

open Classical in
private def birthdayReplacementPolynomial (r : ℝ) : ℚ[X] :=
  if h : r ∈ Set.range (fun q : Dyadic ↦ (q.toRat : ℝ)) then
    C (h.choose.birthday : ℚ) else X

/-- Replace each dyadic by its finite birthday and every nondyadic coefficient by `τ`. -/
def birthdayReplacement (τ r : ℝ) : ℝ :=
  aeval τ (birthdayReplacementPolynomial r)

private theorem birthdayReplacementPolynomial_dyadic (q : Dyadic) :
    birthdayReplacementPolynomial (q.toRat : ℝ) = C (q.birthday : ℚ) := by
  have h : (q.toRat : ℝ) ∈ Set.range (fun q : Dyadic ↦ (q.toRat : ℝ)) := ⟨q, rfl⟩
  rw [birthdayReplacementPolynomial, dite_eq_left h]
  have he : h.choose = q := Dyadic.ext ((Rat.cast_inj (α := ℝ)).mp h.choose_spec)
  rw [he]

private theorem birthdayReplacementPolynomial_nondyadic (r : ℝ)
    (hr : r ∉ Set.range (fun q : Dyadic ↦ (q.toRat : ℝ))) :
    birthdayReplacementPolynomial r = X := by
  rw [birthdayReplacementPolynomial, dite_eq_right hr]

/-- A dyadic coefficient is replaced by its finite birthday. -/
theorem birthdayReplacement_dyadic (τ : ℝ) (q : Dyadic) :
    birthdayReplacement τ (q.toRat : ℝ) = (q.birthday : ℝ) := by
  rw [birthdayReplacement, birthdayReplacementPolynomial_dyadic]
  simp

/-- A nondyadic coefficient is replaced by the common value `τ`. -/
theorem birthdayReplacement_nondyadic (τ r : ℝ)
    (hr : r ∉ Set.range (fun q : Dyadic ↦ (q.toRat : ℝ))) :
    birthdayReplacement τ r = τ := by
  rw [birthdayReplacement, birthdayReplacementPolynomial_nondyadic r hr, aeval_X]

/-- A transcendental real has birthday omega. -/
theorem birthday_real_eq_omega0_of_transcendental {τ : ℝ} (hτ : Transcendental ℚ τ) :
    (τ : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0 := by
  apply (birthday_real_eq_omega0_iff τ).mpr
  rintro ⟨q, rfl⟩
  exact hτ (isAlgebraic_algebraMap q.toRat)

/-- Transcendental replacements preserve every real coefficient birthday. -/
theorem birthday_birthdayReplacement (τ r : ℝ) (hτ : Transcendental ℚ τ) :
    ((birthdayReplacement τ r : ℝ) : Surreal.{u}).birthday = (r : Surreal).birthday := by
  by_cases hr : r ∈ Set.range (fun q : Dyadic ↦ (q.toRat : ℝ))
  · obtain ⟨q, rfl⟩ := hr
    rw [birthdayReplacement_dyadic, Real.toSurreal_natCast, birthday_natCast,
      Real.toSurreal_ratCast, birthday_dyadic]
  · rw [birthdayReplacement_nondyadic τ r hr,
      birthday_real_eq_omega0_of_transcendental hτ, (birthday_real_eq_omega0_iff r).mpr hr]

/-- Every nonzero coefficient has positive replacement when `τ` is positive. -/
theorem birthdayReplacement_pos {τ r : ℝ} (hτ : 0 < τ) (hr : r ≠ 0) :
    0 < birthdayReplacement τ r := by
  by_cases hd : r ∈ Set.range (fun q : Dyadic ↦ (q.toRat : ℝ))
  · obtain ⟨q, rfl⟩ := hd
    rw [birthdayReplacement_dyadic, Nat.cast_pos]
    have hq : q.birthday ≠ 0 := by
      intro he
      have hs : (q : Surreal.{0}) = 0 := birthday_eq_zero.mp (by simp [birthday_dyadic, he])
      apply hr
      exact Real.toSurreal_eq_zero_iff.mp (by simpa only [Real.toSurreal_ratCast] using hs)
    exact Nat.pos_of_ne_zero hq
  · rw [birthdayReplacement_nondyadic τ r hd]
    exact hτ

/-- The replacement of zero is zero. -/
@[simp]
theorem birthdayReplacement_zero (τ : ℝ) : birthdayReplacement τ 0 = 0 := by
  simpa [show Dyadic.birthday 0 = 0 from rfl] using birthdayReplacement_dyadic τ 0

/-- A positive replacement preserves exactly the zero coefficients. -/
theorem birthdayReplacement_eq_zero_iff {τ : ℝ} (hτ : 0 < τ) (r : ℝ) :
    birthdayReplacement τ r = 0 ↔ r = 0 := by
  constructor
  · intro he
    by_contra hr
    exact (birthdayReplacement_pos hτ hr).ne' he
  · rintro rfl
    exact birthdayReplacement_zero τ

/-- A transcendental replacement preserves dyadicness. -/
theorem birthdayReplacement_dyadic_iff (τ r : ℝ) (hτ : Transcendental ℚ τ) :
    birthdayReplacement τ r ∈ Set.range (fun q : Dyadic ↦ (q.toRat : ℝ)) ↔
      r ∈ Set.range (fun q : Dyadic ↦ (q.toRat : ℝ)) := by
  rw [← birthday_real_lt_omega0_iff.{0}, ← birthday_real_lt_omega0_iff.{0},
    birthday_birthdayReplacement τ r hτ]

private theorem coeff_birthdayReplacementPolynomial_nonneg (r : ℝ) (n : ℕ) :
    0 ≤ (birthdayReplacementPolynomial r).coeff n := by
  by_cases hr : r ∈ Set.range (fun q : Dyadic ↦ (q.toRat : ℝ))
  · obtain ⟨q, rfl⟩ := hr
    rw [birthdayReplacementPolynomial_dyadic, coeff_C]
    split_ifs <;> positivity
  · rw [birthdayReplacementPolynomial_nondyadic r hr, coeff_X]
    split_ifs <;> positivity

private theorem coeff_birthdayReplacementPolynomial_mul_nonneg (r s : ℝ) (n : ℕ) :
    0 ≤ (birthdayReplacementPolynomial r * birthdayReplacementPolynomial s).coeff n := by
  rw [coeff_mul]
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg
    (coeff_birthdayReplacementPolynomial_nonneg r i.1)
    (coeff_birthdayReplacementPolynomial_nonneg s i.2)

private theorem exists_pos_coeff_birthdayReplacementPolynomial_mul (r s : ℝ)
    (hr : r ∉ Set.range (fun q : Dyadic ↦ (q.toRat : ℝ))) (hs : s ≠ 0) :
    ∃ n : ℕ, 0 < n ∧
      0 < (birthdayReplacementPolynomial r * birthdayReplacementPolynomial s).coeff n := by
  rw [birthdayReplacementPolynomial_nondyadic r hr]
  by_cases hd : s ∈ Set.range (fun q : Dyadic ↦ (q.toRat : ℝ))
  · obtain ⟨q, rfl⟩ := hd
    have hp := birthdayReplacement_pos (τ := 1) zero_lt_one hs
    rw [birthdayReplacement_dyadic, Nat.cast_pos] at hp
    refine ⟨1, zero_lt_one, ?_⟩
    simpa [birthdayReplacementPolynomial_dyadic] using (Nat.cast_pos (α := ℚ)).mpr hp
  · refine ⟨2, by decide, ?_⟩
    simp [birthdayReplacementPolynomial_nondyadic s hd, ← pow_two]

private theorem birthday_aeval_eq_omega0_of_pos_coeff {τ : ℝ} (hτ : Transcendental ℚ τ)
    (p : ℚ[X]) (n : ℕ) (hn : 0 < n) (hp : p.coeff n ≠ 0) :
    ((aeval τ p : ℝ) : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0 := by
  apply (birthday_real_eq_omega0_iff _).mpr
  rintro ⟨q, hq⟩
  have he : p = C q.toRat := (transcendental_iff_injective.mp hτ)
    (by simpa using hq.symm)
  have hc := congrArg (fun f : ℚ[X] ↦ f.coeff n) he
  rw [coeff_C, ite_eq_right hn.ne'] at hc
  exact hp hc

/-- A finite nonzero product fibre with a nondyadic factor has replacement birthday omega. -/
theorem birthday_sum_replacement_mul_eq_omega0 {ι : Type v} (I : Finset ι)
    (r s : ι → ℝ) {τ : ℝ} (hτ : Transcendental ℚ τ)
    (hne : ∀ i ∈ I, r i ≠ 0 ∧ s i ≠ 0)
    (hinf : ∃ i ∈ I,
      r i ∉ Set.range (fun q : Dyadic ↦ (q.toRat : ℝ)) ∨
      s i ∉ Set.range (fun q : Dyadic ↦ (q.toRat : ℝ))) :
    (((∑ i ∈ I, birthdayReplacement τ (r i) * birthdayReplacement τ (s i) : ℝ)) :
      Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0 := by
  let p : ι → ℚ[X] := fun i ↦
    birthdayReplacementPolynomial (r i) * birthdayReplacementPolynomial (s i)
  obtain ⟨i, hi, hinf⟩ := hinf
  have hpos : ∃ n : ℕ, 0 < n ∧ 0 < (p i).coeff n := by
    rcases hinf with hr | hs
    · exact exists_pos_coeff_birthdayReplacementPolynomial_mul (r i) (s i) hr (hne i hi).2
    · simpa only [p, mul_comm] using
        exists_pos_coeff_birthdayReplacementPolynomial_mul (s i) (r i) hs (hne i hi).1
  obtain ⟨n, hn, hp⟩ := hpos
  have hcoeff : 0 < (∑ i ∈ I, p i).coeff n := by
    rw [finsetSum_coeff]
    exact hp.trans_le (Finset.single_le_sum
      (fun j _ ↦ coeff_birthdayReplacementPolynomial_mul_nonneg (r j) (s j) n) hi)
  have hb := birthday_aeval_eq_omega0_of_pos_coeff hτ (∑ i ∈ I, p i) n hn hcoeff.ne'
  simpa only [map_sum, map_mul, p, birthdayReplacement] using hb

private theorem exists_nat_sum_replacement_mul_of_dyadic {ι : Type v} (I : Finset ι)
    (r s : ι → ℝ) (τ : ℝ)
    (hd : ∀ i ∈ I,
      r i ∈ Set.range (fun q : Dyadic ↦ (q.toRat : ℝ)) ∧
      s i ∈ Set.range (fun q : Dyadic ↦ (q.toRat : ℝ))) :
    ∃ n : ℕ, (∑ i ∈ I, birthdayReplacement τ (r i) * birthdayReplacement τ (s i)) =
      (n : ℝ) ∧ (((∑ i ∈ I, r i * s i : ℝ)) : Surreal.{u}).birthday ≤ (n : NatOrdinal) := by
  classical
  revert hd
  induction I using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨0, by simp, by simp⟩
  | @insert i I hi ih =>
    intro hd
    obtain ⟨n, he, hb⟩ := ih (fun j hj ↦ hd j (Finset.mem_insert_of_mem hj))
    obtain ⟨q, hq⟩ := (hd i (Finset.mem_insert_self i I)).1
    obtain ⟨t, ht⟩ := (hd i (Finset.mem_insert_self i I)).2
    refine ⟨q.birthday * t.birthday + n, ?_, ?_⟩
    · rw [Finset.sum_insert hi, ← hq, ← ht,
        birthdayReplacement_dyadic, birthdayReplacement_dyadic, he]
      push_cast
      rfl
    · have hbr : (r i : Surreal.{u}).birthday = (q.birthday : NatOrdinal) := by
        rw [← hq, Real.toSurreal_ratCast, birthday_dyadic]
      have hbs : (s i : Surreal.{u}).birthday = (t.birthday : NatOrdinal) := by
        rw [← ht, Real.toSurreal_ratCast, birthday_dyadic]
      have hmul := birthday_real_mul_le (r i) (s i)
      rw [← Real.toSurreal_mul, hbr, hbs, ← Nat.cast_mul] at hmul
      rw [Finset.sum_insert hi, Real.toSurreal_add, Nat.cast_add]
      exact (birthday_add_le _ _).trans (add_le_add hmul hb)

/-- Replacement dominates the birthday of a finite sum of nonzero coefficient products. -/
theorem birthday_sum_mul_le_replacement {ι : Type v} (I : Finset ι)
    (r s : ι → ℝ) {τ : ℝ} (hτ : Transcendental ℚ τ)
    (hne : ∀ i ∈ I, r i ≠ 0 ∧ s i ≠ 0) :
    (((∑ i ∈ I, r i * s i : ℝ)) : Surreal.{u}).birthday ≤
      (((∑ i ∈ I, birthdayReplacement τ (r i) * birthdayReplacement τ (s i) : ℝ)) :
        Surreal.{u}).birthday := by
  classical
  by_cases hd : ∀ i ∈ I,
      r i ∈ Set.range (fun q : Dyadic ↦ (q.toRat : ℝ)) ∧
      s i ∈ Set.range (fun q : Dyadic ↦ (q.toRat : ℝ))
  · obtain ⟨n, he, hb⟩ := exists_nat_sum_replacement_mul_of_dyadic I r s τ hd
    rw [he, Real.toSurreal_natCast, birthday_natCast]
    exact hb
  · have hinf : ∃ i ∈ I,
        r i ∉ Set.range (fun q : Dyadic ↦ (q.toRat : ℝ)) ∨
        s i ∉ Set.range (fun q : Dyadic ↦ (q.toRat : ℝ)) := by
      simpa only [not_forall, not_and_or, exists_prop] using hd
    rw [birthday_sum_replacement_mul_eq_omega0 I r s hτ hne hinf]
    exact birthday_real_le_omega0 _

end Surreal
