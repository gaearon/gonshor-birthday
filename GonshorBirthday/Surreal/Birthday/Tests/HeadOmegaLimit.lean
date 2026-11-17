/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadOmegaLimit

/-!
# A genuine ordinal-omega exponent limit with an arbitrary higher head
-/

universe u
public section
open Surreal Set
namespace Tests

/-- The natural exponent stages determine the actual headed omega-exponent limit. -/
theorem headed_ordinal_omega_limit (H : Surreal.{u})
    (hH : H.support ⊆ Ioi (NatOrdinal.of Ordinal.omega0).toSurreal) (M : NatOrdinal.{u}) :
    (H + ω^ (NatOrdinal.of Ordinal.omega0).toSurreal).birthday ≤ M ↔
      ∀ n : ℕ, (H + ω^ (n : Surreal)).birthday ≤ M := by
  let s : Surreal.{u} := (NatOrdinal.of Ordinal.omega0).toSurreal
  have hns (n : ℕ) : (n : Surreal.{u}) < s := by
    have hh := NatOrdinal.toSurreal.strictMono (NatOrdinal.natCast_lt_omega0 n)
    simpa only [NatOrdinal.toSurreal_natCast] using hh
  have htH : ∀ n : ℕ, H.support ⊆ Ioi (n : Surreal.{u}) := by
    intro n v hv
    exact mem_Ioi.mpr ((hns n).trans (mem_Ioi.mp (hH hv)))
  have ht : ∀ n : ℕ, birthdayTruncation s (n : Surreal).birthday = (n : Surreal) := by
    intro n
    rw [birthday_natCast]
    have hh := birthdayTruncation_toSurreal (NatOrdinal.natCast_lt_omega0 n).le
    simpa only [NatOrdinal.toSurreal_natCast] using hh
  have hcof : ∀ a < s.birthday, ∃ n : ℕ, a < (n : Surreal.{u}).birthday := by
    intro a ha
    have hs : s.birthday = NatOrdinal.of Ordinal.omega0 := birthday_toSurreal _
    rw [hs] at ha
    obtain ⟨n, hn⟩ := NatOrdinal.lt_omega0.mp ha
    refine ⟨n + 1, ?_⟩
    rw [birthday_natCast, hn]
    exact_mod_cast Nat.lt_succ_self n
  exact birthday_head_wpow_le_iff_of_cofinal_prefixes (fun n : ℕ ↦ (n : Surreal))
    hH htH ht hcof M

end Tests
