/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.NatOrdinal.CantorSupport

import Mathlib.Tactic.NormNum

/-!
# Clients for the least Cantor exponent and final-block estimates

The two-term ordinal `omega^2 + omega` has least exponent one, not its leading exponent two.
Its natural square has least exponent two. The prefix estimate reaches equality on a prefix
ending with a finite remainder, while a proper prefix of `omega^omega` leaves a full suffix.
-/

public noncomputable section

namespace Tests

open Ordinal NatOrdinal
open scoped Pointwise

/-- The lower Cantor term is retained in the support. -/
theorem two_term_cantorSupport :
    cantorSupport (ω^ (2 : NatOrdinal.{0}) + ω^ (1 : NatOrdinal.{0})) = {2, 1} := by
  simp

/-- Zero has no least Cantor exponent. -/
theorem zero_has_no_least_cantorExponent (p : NatOrdinal.{0}) :
    ¬ IsLeast (cantorSupport 0 : Set NatOrdinal.{0}) p := by
  simp [IsLeast]

/-- The trailing exponent of a two-term natural square is two. -/
theorem two_term_square_least :
    IsLeast
      (cantorSupport ((ω^ (2 : NatOrdinal.{0}) + ω^ (1 : NatOrdinal.{0})) *
        (ω^ (2 : NatOrdinal.{0}) + ω^ (1 : NatOrdinal.{0}))) : Set NatOrdinal.{0}) 2 := by
  have h : IsLeast (cantorSupport (ω^ (2 : NatOrdinal.{0}) + ω^ (1 : NatOrdinal.{0})) :
      Set NatOrdinal.{0}) 1 := by
    constructor
    · simp
    · intro e he
      simp only [two_term_cantorSupport, Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl
      · exact one_le_two
      · exact le_rfl
  simpa only [one_add_one_eq_two] using isLeast_cantorSupport_mul h h

/-- Every proper prefix admits one more block of the least Cantor exponent. -/
theorem proper_prefix_room {h : NatOrdinal.{0}}
    (hh : h < ω^ (2 : NatOrdinal.{0}) + ω^ (1 : NatOrdinal.{0})) :
    of (h.val + (ω^ (1 : NatOrdinal.{0})).val) ≤
      ω^ (2 : NatOrdinal.{0}) + ω^ (1 : NatOrdinal.{0}) := by
  apply oadd_wpow_le_of_lt_of_le_cantorSupport hh
  intro e he
  rw [two_term_cantorSupport] at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact one_le_two
  · exact le_rfl

/-- A finite remainder uses exactly one remaining omega block. -/
theorem final_omega_block_exact :
    of ((ω^ (2 : NatOrdinal.{0}) + 7).val + (ω^ (1 : NatOrdinal.{0})).val) =
      ω^ (2 : NatOrdinal.{0}) + ω^ (1 : NatOrdinal.{0}) := by
  have h : ((7 : ℕ) : Ordinal.{0}) < Ordinal.omega0 := Ordinal.natCast_lt_omega0 7
  change of ((ω^ (2 : NatOrdinal.{0}) + (7 : ℕ)).val +
    (ω^ (1 : NatOrdinal.{0})).val) = _
  rw [val_add_natCast, val_wpow, val_wpow, val_one, Ordinal.opow_one, add_assoc,
    Ordinal.add_omega0 h]
  simpa only [wpow_one, val_wpow, val_of] using
    (of_oadd_wpow_of_le_cantorSupport (x := ω^ (2 : NatOrdinal.{0})) (p := 1)
      (by simp))

/-- Removing an initial omega-squared interval from omega-to-omega leaves its full type. -/
theorem pure_limit_suffix :
    of ((ω^ (of Ordinal.omega0 : NatOrdinal.{0})).val -
      (ω^ (2 : NatOrdinal.{0})).val) = ω^ (of Ordinal.omega0 : NatOrdinal.{0}) := by
  apply wpow_osub_of_lt
  apply wpow_lt_wpow.mpr
  exact of.strictMono (Ordinal.natCast_lt_omega0 2)

/-- A finite last term prevents ordinary divisibility, despite the large leading term. -/
theorem finite_remainder_not_divisible :
    ¬ (ω^ (1 : NatOrdinal.{0})).val ∣ (ω^ (2 : NatOrdinal.{0}) + 1).val := by
  intro h
  have h0 := le_cantorSupport_of_wpow_dvd_val h 0 (by simp)
  exact (not_le.mpr (zero_lt_one : (0 : NatOrdinal.{0}) < 1)) h0

/-- The infinite power tail absorbs small remainders from any earlier prefix. -/
theorem power_tail_after_arbitrary_prefix (c : Ordinal.{0}) :
    ∀ e ∈ cantorSupport (of (c + typeLT (Σₗ n : ℕ,
      (ω^ (n : NatOrdinal.{0})).val.ToType))), (2 : NatOrdinal.{0}) ≤ e := by
  apply le_cantorSupport_of_type_sigma_wpow_tail
    (fun n : ℕ ↦ (n : NatOrdinal.{0})) 2 2 c
  intro n hn
  exact Nat.cast_le.mpr hn

/-- Ordinary left divisibility is strictly different from natural divisibility at a limit. -/
theorem ordinary_not_natural_divisor :
    (of Ordinal.omega0 : NatOrdinal.{0}).val ∣ (ω^ (of Ordinal.omega0 : NatOrdinal.{0})).val ∧
      ¬ (of Ordinal.omega0 : NatOrdinal.{0}) ∣ ω^ (of Ordinal.omega0 : NatOrdinal.{0}) := by
  constructor
  · simpa only [val_of, val_wpow, Ordinal.opow_one] using
      (Ordinal.opow_dvd_opow Ordinal.omega0 (le_of_lt Ordinal.one_lt_omega0))
  · rintro ⟨y, hy⟩
    have hm : of Ordinal.omega0 ∈ cantorSupport ((of Ordinal.omega0 : NatOrdinal.{0}) * y) := by
      rw [← hy]
      simp
    rw [cantorSupport_mul] at hm
    obtain ⟨a, ha, b, _, hab⟩ := Finset.mem_add.mp hm
    simp only [cantorSupport_omega, Finset.mem_singleton] at ha
    subst a
    have he : b.val + 1 = (Ordinal.omega0 : Ordinal.{0}) := by
      simpa only [add_comm (1 : NatOrdinal.{0}), val_add_one, val_of] using congrArg val hab
    exact Ordinal.isSuccLimit_omega0.succ_ne b.val (by
      simpa only [Order.succ_eq_add_one] using he)

end Tests
