/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.CoefficientReplacement

/-!
# Positive coefficient replacement clients

The replacement sends a negative half to two, preserves zero, and sends one third
to the common transcendental. The finite-fibre comparison includes opposite-sign
summands whose original sum is zero.
-/

universe u
public noncomputable section
namespace Tests
open Surreal

/-- The finite replacement uses birthday, rather than absolute value. -/
theorem replacement_negative_half (τ : ℝ) : birthdayReplacement τ (-1 / 2) = 2 := by
  have h := birthdayReplacement_dyadic τ ((-1 : Dyadic) >>> 1)
  have hb : Dyadic.birthday ((-1 : Dyadic) >>> 1) = 2 := rfl
  have hv : (((-1 : Dyadic) >>> 1).toRat : ℝ) = -1 / 2 := by
    rw [show ((-1 : Dyadic) >>> 1).toRat = (-1 / 2 : ℚ) by
      change mkRat (-1) 2 = -1 / 2
      rw [Rat.mkRat_eq_div]
      norm_num]
    norm_num
  simpa only [hb, hv, Nat.cast_ofNat] using h

example (τ : ℝ) : birthdayReplacement τ 0 = 0 := birthdayReplacement_zero τ

private theorem third_nondyadic :
    (1 / 3 : ℝ) ∉ Set.range (fun q : Dyadic ↦ (q.toRat : ℝ)) := by
  rintro ⟨q, hq⟩
  have hq' : (q.toRat : ℝ) = Rat.cast (1 / 3 : ℚ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hq
  have he : q.toRat = (1 / 3 : ℚ) := (Rat.cast_inj (α := ℝ)).mp hq'
  have hd : q.den = 3 := by simpa using congrArg Rat.den he
  obtain ⟨n, hn⟩ := q.den_mem_powers
  change 2 ^ n = q.den at hn
  rw [hd] at hn
  cases n with
  | zero => norm_num at hn
  | succ n => rw [pow_succ] at hn; omega

example (τ : ℝ) : birthdayReplacement τ (1 / 3) = τ :=
  birthdayReplacement_nondyadic τ _ third_nondyadic

/-- Opposite original coefficients cancel, but the replacement fibre has birthday omega. -/
theorem replacement_cancelled_fibre (τ : ℝ) (hτ : Transcendental ℚ τ) :
    (((birthdayReplacement τ (-1 / 3) * birthdayReplacement τ 3 +
      birthdayReplacement τ (1 / 3) * birthdayReplacement τ 3 : ℝ)) :
        Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0 := by
  have h := birthday_sum_replacement_mul_eq_omega0 (Finset.univ : Finset Bool)
    (fun b ↦ if b then (1 / 3 : ℝ) else -1 / 3) (fun _ ↦ (3 : ℝ)) hτ
    (by intro b _; cases b <;> norm_num)
    (by exact ⟨true, Finset.mem_univ _, Or.inl third_nondyadic⟩)
  simpa [add_comm] using h

example : ((-1 / 3 : ℝ) * 3 + (1 / 3 : ℝ) * 3) = 0 := by norm_num

example (τ : ℝ) (hτ : Transcendental ℚ τ) :
    ((∑ i ∈ (∅ : Finset Bool), (if i then (2 : ℝ) else 3) * 1 : ℝ) :
      Surreal.{u}).birthday ≤
      ((∑ i ∈ (∅ : Finset Bool),
        birthdayReplacement τ (if i then (2 : ℝ) else 3) * birthdayReplacement τ 1 : ℝ) :
          Surreal.{u}).birthday :=
  birthday_sum_mul_le_replacement ∅ _ _ hτ (by simp)

end Tests
