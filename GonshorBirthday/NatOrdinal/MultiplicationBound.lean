/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.NatOrdinal.Pow

/-!
# Uniform bounds below a final ordinal power

Natural multiplication need not preserve suprema. If the first factor ends in a power of omega,
products with its proper initial segments admit a uniform bound unless the second factor is a
single power of omega. The bounds use finite coefficient estimates, without any continuity premise.

The final theorem assumes explicitly that the displayed ordinary sum also equals the natural sum,
as happens when it splits off the last copy of the last Cantor-normal-form term.
-/

universe u

public noncomputable section

namespace NatOrdinal

variable {x y a d : NatOrdinal.{u}}

/-- A strict power bound on one factor and a degree bound on the other bound the product. -/
theorem mul_lt_wpow_add (hx : x < ω^ a) (hy : y < ω^ (d + 1)) :
    x * y < ω^ (a + d) := by
  obtain rfl | ha := eq_or_ne a 0
  · have hx0 : x = 0 := by simpa using hx
    simp [hx0]
  obtain ⟨c, hca, n, hxn⟩ := (lt_wpow_iff ha).mp hx
  obtain ⟨m, hym⟩ := lt_wpow_add_one_iff.mp hy
  calc
    x * y ≤ (ω^ c * n) * (ω^ d * m) := mul_le_mul' hxn.le hym.le
    _ = ω^ (c + d) * (n * m : ℕ) := by rw [wpow_add, Nat.cast_mul]; ac_rfl
    _ < ω^ (a + d) := wpow_mul_natCast_lt (add_lt_add_of_lt_of_le hca le_rfl) (n * m)

/-- All products below an ordinary final power have one uniform natural-sum bound. -/
theorem mul_lt_add_wpow_of_lt_oadd_wpow (x₀ : NatOrdinal.{u})
    (hx : x < of (x₀.val + (ω^ a).val)) (hy : y < ω^ (d + 1)) :
    x * y < x₀ * y + ω^ (a + d) := by
  obtain ⟨c, hc, hxc⟩ := (Ordinal.lt_add_iff (wpow_ne_zero a)).mp hx
  have hxn : x ≤ x₀ + of c :=
    (of.monotone hxc).trans (oadd_le_add x₀ (of c))
  calc
    x * y ≤ (x₀ + of c) * y := mul_le_mul' hxn le_rfl
    _ = x₀ * y + of c * y := add_mul ..
    _ < x₀ * y + ω^ (a + d) :=
      add_lt_add_of_le_of_lt le_rfl (mul_lt_wpow_add hc hy)

/-- A nontrivial lower Cantor term or leading coefficient leaves room above the uniform bound. -/
theorem add_wpow_lt_mul_of_wpow_lt (x₀ : NatOrdinal.{u}) (hy : ω^ d < y) :
    x₀ * y + ω^ (a + d) < (x₀ + ω^ a) * y := by
  rw [add_mul, wpow_add]
  exact add_lt_add_of_le_of_lt le_rfl (mul_lt_mul_of_pos_left hy (wpow_pos a))

/-- Cofinality of multiplication through an ordinary final power forces the other factor pure. -/
theorem eq_wpow_of_mul_cofinal (x₀ : NatOrdinal.{u})
    (hadd : of (x₀.val + (ω^ a).val) = x₀ + ω^ a)
    (hyl : ω^ d ≤ y) (hyu : y < ω^ (d + 1))
    (hc : ∀ b < (x₀ + ω^ a) * y,
      ∃ z < x₀ + ω^ a, b ≤ z * y) : y = ω^ d := by
  by_contra h
  have hy : ω^ d < y := lt_of_le_of_ne hyl (Ne.symm h)
  obtain ⟨z, hz, hb⟩ := hc (x₀ * y + ω^ (a + d))
    (add_wpow_lt_mul_of_wpow_lt x₀ hy)
  rw [← hadd] at hz
  exact (mul_lt_add_wpow_of_lt_oadd_wpow x₀ hz hyu).not_ge hb

/-- A nonzero factor whose products are cofinal through a final power is a pure omega power. -/
theorem exists_eq_wpow_of_mul_cofinal (x₀ : NatOrdinal.{u})
    (hadd : of (x₀.val + (ω^ a).val) = x₀ + ω^ a) (hy : y ≠ 0)
    (hc : ∀ b < (x₀ + ω^ a) * y,
      ∃ z < x₀ + ω^ a, b ≤ z * y) : ∃ d, y = ω^ d := by
  have hyv : y.val ≠ 0 := by simpa using hy
  refine ⟨of (Ordinal.log Ordinal.omega0 y.val), eq_wpow_of_mul_cofinal x₀ hadd ?_ ?_ hc⟩
  · simpa only [of_omega0_opow, of_val] using
      of.monotone (Ordinal.opow_log_le_self Ordinal.omega0 hyv)
  · simpa only [Order.succ_eq_add_one, of_omega0_opow, of_add_one, of_val] using
      of.strictMono (Ordinal.lt_opow_succ_log_self Ordinal.one_lt_omega0 y.val)

end NatOrdinal
