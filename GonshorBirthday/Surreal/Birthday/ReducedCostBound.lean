/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostClassification
public import GonshorBirthday.Surreal.Birthday.ReducedCostInput
public import GonshorBirthday.Surreal.Birthday.CoefficientRun

/-!
# The unrestricted reduced omega-cost addition inequality

The common-margin estimate is proved by induction on the natural sum of the input
birthdays. A hypothetical failure persists at a smaller margin with both input costs
pure. Its limit prefix ends in a coefficient minus, and the output extends it by
one full plus block. This gives a dyadic last coefficient; sharp plus-count addition
forces dyadic input coefficients. The input with cofinal retention is then a negative
unit monomial after a higher head, contradicting the paired canonical prefix gaps.

All surreals and positive surreal margins are allowed. The equivalent unequal-cutoff
estimate includes equality with either input. No normal-form sign-deletion theorem is
assumed. These local estimates are not the full multiplication birthday inequality.
-/

universe u
public noncomputable section
namespace Surreal

/-- A prefix after every original minus leaves exactly an appended plus block. -/
theorem eq_appendPluses_of_rightPrefixes_before (x : Surreal.{u}) {c : NatOrdinal.{u}}
    (hc : c < x.birthday) (hR : ∀ y ∈ rightPrefixes x, y.birthday < c) :
    x = appendPluses (birthdayTruncation x c) (x.birthday.val - c.val) := by
  have hzb := birthday_birthdayTruncation x hc.le
  have hz : birthdayTruncation x (birthdayTruncation x c).birthday = birthdayTruncation x c := by
    rw [hzb]
  apply ((appendPluses_eq_iff _ _ _).mpr ?_).symm
  constructor
  · rw [hzb, Ordinal.add_sub_cancel_of_le (NatOrdinal.val.monotone hc.le), NatOrdinal.of_val]
  · apply Set.Subset.antisymm
    · intro y hy
      apply mem_rightPrefixes_of_birthdayTruncation_eq_of_birthday_le hz hy
      · rw [hzb]
        exact (hR y hy).le
      · exact birthdayTruncation_lt (hR y hy) (mem_rightPrefixes_iff.mp hy).2
    · exact rightPrefixes_subset_of_birthdayTruncation_eq hz

/-- A minimal common-margin failure cannot have both input costs pure omega powers. -/
theorem not_pure_common_margin_failure (a b d : Surreal.{u}) (hd : 0 < d)
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ t : Surreal.{u}, 0 < t → reducedOmegaCost (x + y + t) (x + y) ≤
        reducedOmegaCost (x + t) x * reducedOmegaCost (y + t) y)
    {α β : NatOrdinal.{u}}
    (hA : reducedOmegaCost (a + d) a = ω^ α)
    (hB : reducedOmegaCost (b + d) b = ω^ β)
    (hfail : reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b <
      reducedOmegaCost (a + b + d) (a + b)) : False := by
  obtain ⟨c, hc, hlim, hR, hcof, hH, _, hdel, _⟩ :=
    exists_deleted_limit_prefix_of_pure_common_margin_failure a b d hd ih hA hB hfail
  let z := birthdayTruncation (a + b) c
  let ρ := (a + b).birthday.val - c.val
  have hzb : z.birthday = c := birthday_birthdayTruncation (a + b) hc.le
  have hzpos : 0 < z.birthday := by
    rw [hzb]
    exact NatOrdinal.val.lt_iff_lt.mp (by
      simpa only [NatOrdinal.val_zero] using
        (pos_iff_ne_zero.mpr (Ordinal.isSuccLimit_iff.mp hlim).1))
  have hρpos : 0 < ρ := Ordinal.lt_sub.mpr (by
    simpa only [add_zero] using NatOrdinal.val.strictMono hc)
  have he : a + b = appendPluses z ρ := eq_appendPluses_of_rightPrefixes_before _ hc hR
  have hcofz : ∀ j < z.birthday,
      ∃ w ∈ rightPrefixes z, j < w.birthday ∧ w ≤ a + b + d := by
    simpa only [hzb] using hcof
  obtain ⟨K, s, r, t, hK, hr, hf, hsrc, hz, hρ, hpc, hα, hβ, hbaseA, hbaseB⟩ :=
    exists_full_block_last_term_of_pure_gap_window a b d z hzpos hρpos
      hA hB hH he hcofz hdel
  obtain ⟨q, _, _, hblock⟩ := exists_dyadic_head_coefficient_plus_block K s hK hr hf
  have heshape : a + b = K + ((q.toRat : ℝ) : Surreal) * ω^ s := by
    rw [Real.toSurreal_ratCast, ← hblock, ← hρ, ← hz, ← he]
  have hsharp : plusCount (a + b) = plusCount a + plusCount b := by
    simpa only [hα, hβ] using hpc
  have hdeleted : ∀ w ∈ rightPrefixes (K + (r : Surreal) * ω^ s),
      K + (r : Surreal) * ω^ s + d < w := by
    simpa only [← hz] using hdel
  rcases pure_factor_or_of_common_margin_failure a b d hd ih hfail with
    ⟨_, _, _, hcostA⟩ | ⟨_, _, _, hcostB⟩
  · have hca := retained_rightPrefixes_cofinal_of_costs_cofinal (a + d) a hcostA
    obtain ⟨w, hw, hwC, _⟩ := hcostA 0
      (zero_lt_one.trans_le (one_le_reducedOmegaCost _ _))
    exact not_retained_baseline_of_last_minus_output a b d K s q hK hsrc heshape hsharp
      hbaseA hca ⟨w, hw, hwC⟩ hdeleted
  · have hcb := retained_rightPrefixes_cofinal_of_costs_cofinal (b + d) b hcostB
    obtain ⟨w, hw, hwC, _⟩ := hcostB 0
      (zero_lt_one.trans_le (one_le_reducedOmegaCost _ _))
    exact not_retained_baseline_of_last_minus_output b a d K s q hK hsrc
      (by simpa only [add_comm] using heshape) (by simpa only [add_comm] using hsharp)
      hbaseB hcb ⟨w, hw, hwC⟩ hdeleted

/-- The reduced cost of a sum, with cutoff a positive margin `d` above it, is at most the
natural product of the reduced costs of the summands with the same margin. -/
theorem reducedOmegaCost_add_common_margin_le (a b d : Surreal.{u}) (hd : 0 < d) :
    reducedOmegaCost (a + b + d) (a + b) ≤
      reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b := by
  have aux : ∀ μ : NatOrdinal.{u}, ∀ a b : Surreal.{u}, a.birthday + b.birthday = μ →
      ∀ d : Surreal.{u}, 0 < d → reducedOmegaCost (a + b + d) (a + b) ≤
        reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b := by
    intro μ
    induction μ using NatOrdinal.lt_wf.induction with
    | h μ ih =>
      intro a b hab d hd
      have ih' : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
          ∀ t : Surreal.{u}, 0 < t → reducedOmegaCost (x + y + t) (x + y) ≤
            reducedOmegaCost (x + t) x * reducedOmegaCost (y + t) y := by
        intro x y hxy
        exact ih _ (by simpa only [hab] using hxy) x y rfl
      by_contra hn
      obtain ⟨d', α, β, hd', _, _, hA, hB, hfail⟩ :=
        exists_smaller_margin_pure_costs_of_common_margin_failure a b d hd ih'
          (lt_of_not_ge hn)
      exact not_pure_common_margin_failure a b d' hd' ih' hA hB hfail
  exact aux _ a b rfl d hd

/-- The reduced cost of `a + b` with cutoff `min (A + b) (a + B)` is at most the natural
product of the reduced costs of `a` with cutoff `A` and of `b` with cutoff `B`. -/
theorem reducedOmegaCost_add_le (a b A B : Surreal.{u}) (ha : a ≤ A) (hb : b ≤ B) :
    reducedOmegaCost (min (A + b) (a + B)) (a + b) ≤
      reducedOmegaCost A a * reducedOmegaCost B b :=
  (reducedOmegaCost_add_iff_common_margin a b).mp
    (fun d hd ↦ reducedOmegaCost_add_common_margin_le a b d hd) A B ha hb

end Surreal
