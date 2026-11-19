/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostCofinality

import GonshorBirthday.NatOrdinal.OrderedSum
import GonshorBirthday.NatOrdinal.FinalPower
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Reduced-cost tails under lowered cutoffs

A retained right prefix fixes every later retention decision. Cofinal retained
minuses also force each proper original plus rank strictly below every final
Cantor exponent of the full reduced cost.
-/

universe u

public noncomputable section

namespace Surreal

open Ordinal

/-- A later canonical right prefix has at least the reduced cost of an earlier one. -/
theorem reducedOmegaCost_le_of_rightPrefixes_lt (D : Surreal.{u}) {x y z : Surreal.{u}}
    (hy : y ∈ rightPrefixes x) (hz : z ∈ rightPrefixes x) (hzy : z < y) :
    reducedOmegaCost D y ≤ reducedOmegaCost D z := by
  have hby := birthday_lt_of_rightPrefixes_lt hy hz hzy
  have ht : birthdayTruncation z y.birthday = y := by
    rw [← (mem_rightPrefixes_iff.mp hz).1,
      birthdayTruncation_birthdayTruncation x hby.le (birthday_lt_of_mem_rightPrefixes hz).le,
      (mem_rightPrefixes_iff.mp hy).1]
  simpa only [ht] using reducedOmegaCost_birthdayTruncation_le D z hby.le

/-- Once one right prefix survives a new cutoff, cofinal minus positions survive it. -/
theorem retained_rightPrefixes_cofinal_of_retained {C D x y : Surreal.{u}}
    (hcof : ∀ a < x.birthday, ∃ z ∈ rightPrefixes x, a < z.birthday ∧ z ≤ D)
    (hy : y ∈ rightPrefixes x) (hyC : y ≤ C) :
    ∀ a < x.birthday, ∃ z ∈ rightPrefixes x, a < z.birthday ∧ z ≤ C := by
  intro a ha
  obtain ⟨z, hz, haz, _, hzy⟩ := exists_retained_rightPrefix_lt_of_cofinal hcof hy ha
  exact ⟨z, hz, haz, hzy.le.trans hyC⟩

/-- Cofinal retained minuses put each proper prefix plus count below every final cost exponent. -/
theorem plusCount_prefix_lt_cantorSupport_of_retained_cofinal {C x : Surreal.{u}}
    (hcof : ∀ a < x.birthday, ∃ y ∈ rightPrefixes x, a < y.birthday ∧ y ≤ C)
    {a p : NatOrdinal.{u}} (ha : a < x.birthday)
    (hp : p ∈ NatOrdinal.cantorSupport (reducedOmegaCost C x)) :
    plusCount (birthdayTruncation x a) < p := by
  obtain ⟨y, hy, hay, hyC⟩ := hcof a ha
  let j : reducedOmegaPositions C x :=
    ⟨Ordinal.ToType.mk ⟨y.birthday.val,
      NatOrdinal.val.strictMono (birthday_lt_of_mem_rightPrefixes hy)⟩, by
      apply mem_reducedOmegaPositions.mpr
      right
      simpa only [Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val,
        (mem_rightPrefixes_iff.mp hy).1] using hyC⟩
  let q (i : reducedOmegaPositions C x) :=
    plusCount (birthdayTruncation x (NatOrdinal.of i.1.toOrd.1)) + 1
  have hbound : plusCount (birthdayTruncation x a) + 1 ≤ p := by
    rw [reducedOmegaCost_eq_positions, omegaExpansionLength_eq] at hp
    apply NatOrdinal.le_cantorSupport_of_type_sigma_wpow_tail q j
      (plusCount (birthdayTruncation x a) + 1) 1 ?_ p hp
    intro i hji
    have hyi : y.birthday ≤ NatOrdinal.of i.1.toOrd.1 := by
      have hi := NatOrdinal.of.monotone (Ordinal.ToType.mk.symm.monotone hji)
      simpa only [j, Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val] using hi
    have hai := hay.le.trans hyi
    have hix : NatOrdinal.of i.1.toOrd.1 ≤ x.birthday :=
      (NatOrdinal.of.strictMono i.1.toOrd.2).le
    have ha' : a ≤ (birthdayTruncation x (NatOrdinal.of i.1.toOrd.1)).birthday := by
      rw [birthday_birthdayTruncation x hix]
      exact hai
    have hpc := plusCount_birthdayTruncation_le
      (birthdayTruncation x (NatOrdinal.of i.1.toOrd.1)) ha'
    rw [birthdayTruncation_birthdayTruncation x hai hix] at hpc
    exact add_le_add hpc le_rfl
  exact (lt_add_one _).trans_le hbound

/-- Above a shared retained right prefix, lowering the cutoff leaves the entire tail unchanged. -/
theorem reducedOmegaCost_eq_prefix_add_old_tail {C D x y : Surreal.{u}}
    (hCD : C ≤ D) (hy : y ∈ rightPrefixes x) (hyC : y ≤ C) :
    reducedOmegaCost C x = NatOrdinal.of ((reducedOmegaCost C y).val +
      ((reducedOmegaCost D x).val - (reducedOmegaCost D y).val)) := by
  let r : x.birthday.val.ToType := Ordinal.ToType.mk
    ⟨y.birthday.val, NatOrdinal.val.strictMono (birthday_lt_of_mem_rightPrefixes hy)⟩
  have hr : NatOrdinal.of r.toOrd.1 = y.birthday := by
    simp only [r, Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val]
  have hCr : r ∈ reducedOmegaPositions C x := by
    apply mem_reducedOmegaPositions.mpr
    rw [hr, (mem_rightPrefixes_iff.mp hy).1]
    exact Or.inr hyC
  have hDr : r ∈ reducedOmegaPositions D x := by
    apply mem_reducedOmegaPositions.mpr
    rw [hr, (mem_rightPrefixes_iff.mp hy).1]
    exact Or.inr (hyC.trans hCD)
  let jC : reducedOmegaPositions C x := ⟨r, hCr⟩
  let jD : reducedOmegaPositions D x := ⟨r, hDr⟩
  let f : Set.Ici jC → Set.Ici jD := fun i ↦
    ⟨⟨i.1.1, by
      apply mem_reducedOmegaPositions.mpr
      exact (mem_reducedOmegaPositions.mp i.1.2).imp_right (fun h ↦ h.trans hCD)⟩, i.2⟩
  have hf : StrictMono f := fun _ _ h ↦ h
  have honto : Function.Surjective f := by
    intro i
    have hri : y.birthday ≤ NatOrdinal.of i.1.1.toOrd.1 := by
      have h := NatOrdinal.of.monotone (Ordinal.ToType.mk.symm.monotone i.2)
      simpa only [jD, r, Ordinal.ToType.toOrd, OrderIso.symm_apply_apply,
        NatOrdinal.of_val] using h
    have hiC : i.1.1 ∈ reducedOmegaPositions C x := by
      apply mem_reducedOmegaPositions.mpr
      right
      apply birthdayTruncation_le_cutoff_of_rightPrefix_le (C := C) hri
        (NatOrdinal.of.strictMono i.1.1.toOrd.2).le
      · rw [(mem_rightPrefixes_iff.mp hy).1]
        exact (mem_rightPrefixes_iff.mp hy).2
      · rwa [(mem_rightPrefixes_iff.mp hy).1]
    exact ⟨⟨⟨i.1.1, hiC⟩, i.2⟩, rfl⟩
  let e : Set.Ici jC ≃o Set.Ici jD :=
    OrderIso.ofSurjective (OrderEmbedding.ofStrictMono f hf) honto
  let W (i : Set.Ici jC) :=
    (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of i.1.1.toOrd.1)) + 1)).val.ToType
  let V (i : Set.Ici jD) :=
    (ω^ (plusCount (birthdayTruncation x (NatOrdinal.of i.1.1.toOrd.1)) + 1)).val.ToType
  have he : typeLT (Σₗ i, W i) = typeLT (Σₗ i, V i) := by
    apply Ordinal.type_sigma_congr W V e
    intro i
    rfl
  have hC := reducedOmegaCost_eq_prefix_add_tail C x jC
  have hD := reducedOmegaCost_eq_prefix_add_tail D x jD
  change reducedOmegaCost C x = NatOrdinal.of
    ((reducedOmegaCost C (birthdayTruncation x (NatOrdinal.of r.toOrd.1))).val +
      typeLT (Σₗ i, W i)) at hC
  change reducedOmegaCost D x = NatOrdinal.of
    ((reducedOmegaCost D (birthdayTruncation x (NatOrdinal.of r.toOrd.1))).val +
      typeLT (Σₗ i, V i)) at hD
  rw [hr, (mem_rightPrefixes_iff.mp hy).1, he] at hC
  rw [hr, (mem_rightPrefixes_iff.mp hy).1] at hD
  rw [hD, NatOrdinal.val_of, Ordinal.add_sub_cancel]
  exact hC

/-- Cut at a right prefix lying in the final Cantor power. Before that prefix only its
pluses remain, and they are absorbed by the surviving tail of the power. -/
theorem reducedOmegaCost_at_rightPrefix_eq_final_power {C x w : Surreal.{u}}
    {H p : NatOrdinal.{u}} (hw : w ∈ rightPrefixes x) (hwC : w ≤ C)
    (hfinal : reducedOmegaCost C x = NatOrdinal.of (H.val + (ω^ p).val))
    (hhead : H ≤ reducedOmegaCost C w) (hp : plusCount w < p) :
    reducedOmegaCost w x = ω^ p := by
  have hlt := reducedOmegaCost_lt_of_mem_rightPrefixes (C := C) hw hwC
  rw [hfinal] at hlt
  have htail := congrArg NatOrdinal.val (NatOrdinal.final_wpow_osub hhead hlt)
  have he := reducedOmegaCost_eq_prefix_add_old_tail hwC hw le_rfl
  rw [reducedOmegaCost_self_eq_wpow, hfinal, NatOrdinal.val_of] at he
  simp only [NatOrdinal.val_of] at htail
  rw [htail] at he
  have hsmall : Ordinal.omega0 ^ (plusCount w).val < Ordinal.omega0 ^ p.val :=
    by simpa only [NatOrdinal.val_wpow] using
         NatOrdinal.val.strictMono (NatOrdinal.wpow_lt_wpow.mpr hp)
  simpa only [NatOrdinal.val_wpow, Ordinal.add_omega0_opow hsmall, NatOrdinal.of_omega0_opow,
    NatOrdinal.of_val] using he

/-- If retained minuses have cofinal costs, every sufficiently low cutoff that still
retains a minus gives exactly the last Cantor power of the original cost. -/
theorem eventually_last_power_at_right_cut {C x : Surreal.{u}} {p : NatOrdinal.{u}}
    (hp : IsLeast (NatOrdinal.cantorSupport (reducedOmegaCost C x) : Set NatOrdinal.{u}) p)
    (hcost : ∀ S < reducedOmegaCost C x, ∃ u ∈ rightPrefixes x, u ≤ C ∧ S < reducedOmegaCost C u) :
    ∃ u ∈ rightPrefixes x, u ≤ C ∧ ∀ D ≤ u, (∃ v ∈ rightPrefixes x, v ≤ D) →
      reducedOmegaCost D x = ω^ p := by
  obtain ⟨H, q, hfinal, hadd, hq⟩ := NatOrdinal.exists_final_wpow
    (zero_lt_one.trans_le (one_le_reducedOmegaCost C x)).ne'
  obtain rfl := hp.unique hq
  have hH : H < reducedOmegaCost C x := by
    rw [hfinal, hadd]
    exact lt_add_of_pos_right H (NatOrdinal.wpow_pos _)
  obtain ⟨u, hu, huC, hHu⟩ := hcost H hH
  have atOption (v : Surreal.{u}) (hv : v ∈ rightPrefixes x) (hvu : v ≤ u) :
      reducedOmegaCost v x = ω^ p := by
    apply reducedOmegaCost_at_rightPrefix_eq_final_power hv (hvu.trans huC) hfinal
    · rcases hvu.lt_or_eq with hvu | rfl
      · exact hHu.le.trans (reducedOmegaCost_le_of_rightPrefixes_lt C hu hv hvu)
      · exact hHu.le
    · simpa only [(mem_rightPrefixes_iff.mp hv).1] using
        plusCount_prefix_lt_cantorSupport_of_retained_cofinal
          (retained_rightPrefixes_cofinal_of_costs_cofinal C x hcost)
          (birthday_lt_of_mem_rightPrefixes hv) hq.1
  refine ⟨u, hu, huC, fun D hDu ⟨v, hv, hvD⟩ ↦ ?_⟩
  exact ((reducedOmegaCost_mono x hDu).trans_eq (atOption u hu le_rfl)).antisymm
    ((atOption v hv (hvD.trans hDu)).ge.trans (reducedOmegaCost_mono x hvD))

/-- At a sufficiently late right option of the output, the output has its last Cantor
power and each input costs at most its own last power. -/
theorem exists_margin_at_final_powers {a b d z : Surreal.{u}} {β : NatOrdinal.{u}}
    (hp : birthdayTruncation (a + b) z.birthday = z)
    (hcof : ∀ j < z.birthday, ∃ w ∈ rightPrefixes z, j < w.birthday ∧ w ≤ a + b + d)
    (hH : reducedOmegaCost (a + b + d) z =
      reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b)
    (hcost : ∀ S < reducedOmegaCost (a + d) a, ∃ u ∈ rightPrefixes a,
      u ≤ a + d ∧ S < reducedOmegaCost (a + d) u)
    (hY : reducedOmegaCost (b + d) b = ω^ β)
    (hbelow : ∀ u ∈ rightPrefixes a, u ≤ a + d → ∃ w ∈ rightPrefixes z, w < u + b) :
    ∃ d' : Surreal.{u}, ∃ α : NatOrdinal.{u}, 0 < d' ∧
      α ∈ NatOrdinal.cantorSupport (reducedOmegaCost (a + d) a) ∧
      reducedOmegaCost (a + d') a ≤ ω^ α ∧ reducedOmegaCost (b + d') b ≤ ω^ β ∧
      (∀ L ≤ a + b + d', (∃ w ∈ rightPrefixes z, w ≤ L) → reducedOmegaCost L z = ω^ (α + β)) ∧
      a + b + d' ∈ rightPrefixes z := by
  obtain ⟨_, α, _, _, hα⟩ := NatOrdinal.exists_final_wpow
    (zero_lt_one.trans_le (one_le_reducedOmegaCost (a + d) a)).ne'
  have hβ : IsLeast (NatOrdinal.cantorSupport (reducedOmegaCost (b + d) b) : Set _) β := by
    simp [hY, isLeast_singleton]
  have hγ : IsLeast (NatOrdinal.cantorSupport (reducedOmegaCost (a + b + d) z) : Set _)
      (α + β) := by
    rw [hH]
    exact NatOrdinal.isLeast_cantorSupport_mul hα hβ
  obtain ⟨u, hu, huA, hU⟩ := eventually_last_power_at_right_cut hα hcost
  obtain ⟨w, hw, hwu⟩ := hbelow u hu huA
  obtain ⟨v₀, hv₀, hvC, hV⟩ := eventually_last_power_at_right_cut hγ
    (retained_rightPrefix_costs_cofinal_of_positions
      (bot_le.trans_lt (birthday_lt_of_mem_rightPrefixes hw)) hcof)
  let v := min w v₀
  have hv : v ∈ rightPrefixes z := by
    change min w v₀ ∈ rightPrefixes z
    exact (min_choice w v₀).elim (fun e ↦ e.symm ▸ hw) (fun e ↦ e.symm ▸ hv₀)
  let d' := v - (a + b)
  have he : a + b + d' = v := by dsimp only [d']; abel
  have hd' : 0 < d' := sub_pos.mpr
    (mem_rightPrefixes_iff.mp (rightPrefixes_subset_of_birthdayTruncation_eq hp hv)).2
  have hA : a + d' ≤ u := by
    linarith only [he, (show v ≤ w from min_le_left _ _).trans_lt hwu]
  have hB : b + d' ≤ b + d := by
    linarith only [he, (show v ≤ v₀ from min_le_right _ _).trans hvC]
  exact ⟨d', α, hd', hα.1, (reducedOmegaCost_mono a hA).trans_eq (hU u le_rfl ⟨u, hu, le_rfl⟩),
    (reducedOmegaCost_mono b hB).trans_eq hY,
    fun L hL ↦ hV L ((hL.trans_eq he).trans (min_le_right _ _)),
    he ▸ hv⟩

end Surreal
