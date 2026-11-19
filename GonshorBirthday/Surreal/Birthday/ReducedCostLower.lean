/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostCutoff

import GonshorBirthday.Surreal.Birthday.Addition
import Mathlib.Tactic.Linarith

/-!
# Lowering the output cutoff

At a pure output cost above its plus-only rank, any retained minus preserves
the whole cost. A left-prefix induction estimate at a lower output cutoff is
strictly cheaper. Consequently every output-prefix minus is deleted at the
prefix's own value plus the original common margin.
-/

universe u

public noncomputable section

namespace Surreal

/-- A pure reduced cost above the plus rank persists at every lower cutoff retaining a minus. -/
theorem reducedOmegaCost_eq_wpow_of_le_of_retained {C D x : Surreal.{u}}
    {p : NatOrdinal.{u}} (hCD : C ≤ D) (hD : reducedOmegaCost D x = ω^ p)
    (hp : plusCount x < p) (hne : ∃ y ∈ rightPrefixes x, y ≤ C) :
    reducedOmegaCost C x = ω^ p := by
  obtain ⟨w, hw, hwC⟩ := hne
  have hr := plusCount_birthdayTruncation_le x (birthday_lt_of_mem_rightPrefixes hw).le
  rw [(mem_rightPrefixes_iff.mp hw).1] at hr
  have hwCost := reducedOmegaCost_at_rightPrefix_eq_final_power (H := 0) hw (hwC.trans hCD)
    (by simpa only [NatOrdinal.val_zero, zero_add, NatOrdinal.of_val] using hD)
    bot_le (hr.trans_lt hp)
  exact ((reducedOmegaCost_mono x hCD).trans_eq hD).antisymm
    (hwCost.ge.trans (reducedOmegaCost_mono x hwC))

/-- A proper prefix after all original minuses is a canonical left prefix. -/
theorem birthdayTruncation_mem_leftPrefixes_of_rightPrefixes_before (x : Surreal.{u})
    {c : NatOrdinal.{u}} (hc : c < x.birthday)
    (hR : ∀ y ∈ rightPrefixes x, y.birthday < c) :
    birthdayTruncation x c ∈ leftPrefixes x := by
  apply mem_leftPrefixes.mpr
  refine ⟨c, hc, rfl, ?_⟩
  apply lt_of_not_ge
  intro hx
  have hne : birthdayTruncation x c ≠ x := by
    intro he
    have hb := birthday_birthdayTruncation x hc.le
    rw [he] at hb
    exact hc.ne hb.symm
  have hy : birthdayTruncation x c ∈ rightPrefixes x :=
    mem_rightPrefixes.mpr ⟨c, hc, rfl, lt_of_le_of_ne hx hne.symm⟩
  have h := hR _ hy
  rw [birthday_birthdayTruncation x hc.le] at h
  exact lt_irrefl c h

/-- A left addition option gives a strict cost bound at its induced shifted cutoff. -/
theorem reducedOmegaCost_leftPrefix_add_lt {a b d u z : Surreal.{u}}
    (hu : u ∈ leftPrefixes a) (hz : z ∈ leftPrefixes (a + b)) (hzu : z ≤ u + b)
    (hpair : reducedOmegaCost (min (a + d + b) (u + (b + d))) (u + b) ≤
      reducedOmegaCost (a + d) u * reducedOmegaCost (b + d) b) :
    reducedOmegaCost (u + b + d) z <
      reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b := by
  have hua := (mem_leftPrefixes_iff.mp hu).2
  have hp : birthdayTruncation (u + b) z.birthday = z := by
    exact (birthdayTruncation_eq_of_left_between
      (birthday_lt_of_mem_leftPrefixes hz).le
      (by rwa [(mem_leftPrefixes_iff.mp hz).1])
      (add_le_add hua.le le_rfl)).trans (mem_leftPrefixes_iff.mp hz).1
  have hb : z.birthday ≤ (u + b).birthday := by
    simpa only [hp] using birthday_birthdayTruncation_le_birthday (u + b) z.birthday
  have hmin : min (a + d + b) (u + (b + d)) = u + b + d := by
    rw [← add_assoc u b d, min_eq_right]
    linarith
  have hpre : reducedOmegaCost (u + b + d) z ≤ reducedOmegaCost (u + b + d) (u + b) := by
    simpa only [hp] using reducedOmegaCost_birthdayTruncation_le (u + b + d) (u + b) hb
  rw [hmin] at hpair
  exact (hpre.trans hpair).trans_lt
    (mul_lt_mul_of_pos_right (reducedOmegaCost_lt_of_mem_leftPrefixes (a + d) hu)
      (zero_lt_one.trans_le (one_le_reducedOmegaCost (b + d) b)))

/-- Smaller-input induction gives a strict left-prefix bound at the original input cutoffs. -/
theorem exists_lower_output_cutoff_of_leftPrefix {a b d z : Surreal.{u}} (hd : 0 ≤ d)
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ t : Surreal.{u}, 0 < t → reducedOmegaCost (x + y + t) (x + y) ≤
        reducedOmegaCost (x + t) x * reducedOmegaCost (y + t) y)
    (hz : z ∈ leftPrefixes (a + b)) :
    ∃ K : Surreal.{u}, z + d ≤ K ∧ K ≤ a + b + d ∧
      reducedOmegaCost K z < reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b := by
  rcases exists_leftPrefixes_add_ge hz with ⟨u, hu, hzu⟩ | ⟨u, hu, hzu⟩
  · have hua := (mem_leftPrefixes_iff.mp hu).2
    have huA : u ≤ a + d := hua.le.trans (le_add_of_nonneg_right hd)
    have hi := (reducedOmegaCost_add_iff_common_margin u b).mp
      (ih u b (add_lt_add_of_lt_of_le (birthday_lt_of_mem_leftPrefixes hu) le_rfl))
      (a + d) (b + d) huA (le_add_of_nonneg_right hd)
    exact ⟨u + b + d, add_le_add hzu le_rfl,
      add_le_add (add_le_add hua.le le_rfl) le_rfl,
      reducedOmegaCost_leftPrefix_add_lt hu hz hzu hi⟩
  · have hub := (mem_leftPrefixes_iff.mp hu).2
    have huB : u ≤ b + d := hub.le.trans (le_add_of_nonneg_right hd)
    have hi := (reducedOmegaCost_add_iff_common_margin u a).mp
      (ih u a (by simpa only [add_comm] using
        add_lt_add_of_lt_of_le (birthday_lt_of_mem_leftPrefixes hu) (le_refl a.birthday)))
      (b + d) (a + d) huB (le_add_of_nonneg_right hd)
    have hz' : z ∈ leftPrefixes (b + a) := by simpa only [add_comm] using hz
    have hzu' : z ≤ u + a := by simpa only [add_comm] using hzu
    refine ⟨u + a + d, add_le_add hzu' le_rfl, ?_, ?_⟩
    · simpa only [add_comm] using add_le_add (add_le_add hub.le (le_refl a)) (le_refl d)
    · simpa only [mul_comm] using reducedOmegaCost_leftPrefix_add_lt hu hz' hzu' hi

/-- Every right prefix is deleted at the lowered output cutoff in a pure equality case. -/
theorem rightPrefixes_gt_shifted_cutoff_of_pure_eq {a b d z : Surreal.{u}}
    {p : NatOrdinal.{u}} (hd : 0 ≤ d)
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ t : Surreal.{u}, 0 < t → reducedOmegaCost (x + y + t) (x + y) ≤
        reducedOmegaCost (x + t) x * reducedOmegaCost (y + t) y)
    (hz : z ∈ leftPrefixes (a + b)) (hp : plusCount z < p)
    (hH : reducedOmegaCost (a + b + d) z = ω^ p)
    (hM : reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b = ω^ p) :
    ∀ w ∈ rightPrefixes z, z + d < w := by
  obtain ⟨K, hKlow, hKhigh, hKcost⟩ := exists_lower_output_cutoff_of_leftPrefix hd ih hz
  intro w hw
  apply lt_of_not_ge
  intro hwC
  have he := reducedOmegaCost_eq_wpow_of_le_of_retained hKhigh hH hp
    ⟨w, hw, hwC.trans hKlow⟩
  rw [he, hM] at hKcost
  exact lt_irrefl _ hKcost

/-- A retained output right-prefix gap lies between the two deleted-gap thresholds and their sum. -/
theorem exists_rightPrefix_gap_window {e z d : Surreal.{u}}
    (hz : birthdayTruncation e z.birthday = z)
    (hdel : ∀ w ∈ rightPrefixes z, z + d < w)
    (hne : ∃ w ∈ rightPrefixes z, w ≤ e + d) :
    ∃ w ∈ rightPrefixes z, max d (e - z) < w - z ∧
      w - z ≤ d + (e - z) ∧ d + (e - z) ≤ 2 * max d (e - z) := by
  obtain ⟨w, hw, hwC⟩ := hne
  have hdw := hdel w hw
  have hew := (mem_rightPrefixes_iff.mp
    (rightPrefixes_subset_of_birthdayTruncation_eq hz hw)).2
  refine ⟨w, hw, max_lt (by linarith) (by linarith), by linarith, ?_⟩
  have h₁ := le_max_left d (e - z)
  have h₂ := le_max_right d (e - z)
  linarith

/-- A retained gap window excludes any coinitial right-prefix family admitting repeated halving. -/
theorem not_coinitial_halving_rightPrefixes_of_gap_window {e z d : Surreal.{u}}
    (hz : birthdayTruncation e z.birthday = z)
    (hdel : ∀ w ∈ rightPrefixes z, z + d < w)
    (hne : ∃ w ∈ rightPrefixes z, w ≤ e + d)
    (S : Set Surreal.{u}) (hS : S ⊆ rightPrefixes z)
    (hcoinitial : ∀ w ∈ rightPrefixes z, ∃ v ∈ S, v ≤ w) :
    ¬ (∀ v ∈ S, ∃ u ∈ S, 2 * (u - z) < v - z) := by
  intro hhalf
  obtain ⟨w, hw, _, hgap, hsum⟩ := exists_rightPrefix_gap_window hz hdel hne
  obtain ⟨v, hv, hvw⟩ := hcoinitial w hw
  obtain ⟨u, hu, huv⟩ := hhalf v hv
  have hdu := hdel u (hS hu)
  have heu := (mem_rightPrefixes_iff.mp
    (rightPrefixes_subset_of_birthdayTruncation_eq hz (hS hu))).2
  have hmax : max d (e - z) < u - z := max_lt (by linarith) (by linarith)
  linarith

/-- A minimal pure-cost failure has a proper limit prefix with every lowered minus deleted. -/
theorem exists_deleted_limit_prefix_of_pure_common_margin_failure
    (a b d : Surreal.{u}) (hd : 0 < d)
    (ih : ∀ x y : Surreal.{u}, x.birthday + y.birthday < a.birthday + b.birthday →
      ∀ t : Surreal.{u}, 0 < t → reducedOmegaCost (x + y + t) (x + y) ≤
        reducedOmegaCost (x + t) x * reducedOmegaCost (y + t) y)
    {α β : NatOrdinal.{u}}
    (hA : reducedOmegaCost (a + d) a = ω^ α)
    (hB : reducedOmegaCost (b + d) b = ω^ β)
    (hfail : reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b <
      reducedOmegaCost (a + b + d) (a + b)) :
    ∃ c : NatOrdinal.{u}, c < (a + b).birthday ∧ Order.IsSuccLimit c.val ∧
      (∀ y ∈ rightPrefixes (a + b), y.birthday < c) ∧
      (∀ e < c, ∃ y ∈ rightPrefixes (birthdayTruncation (a + b) c),
        e < y.birthday ∧ y ≤ a + b + d) ∧
      reducedOmegaCost (a + b + d) (birthdayTruncation (a + b) c) = ω^ (α + β) ∧
      plusCount (birthdayTruncation (a + b) c) < α + β ∧
      (∀ w ∈ rightPrefixes (birthdayTruncation (a + b) c),
        birthdayTruncation (a + b) c + d < w) ∧
      ∃ w ∈ rightPrefixes (birthdayTruncation (a + b) c),
        max d (a + b - birthdayTruncation (a + b) c) <
          w - birthdayTruncation (a + b) c ∧
        w - birthdayTruncation (a + b) c ≤ d + (a + b - birthdayTruncation (a + b) c) := by
  obtain ⟨c, hc, hlim, hR, hcof, hH, hp, _⟩ :=
    exists_limit_prefix_of_common_margin_failure a b d hd ih hfail
  have hM : reducedOmegaCost (a + d) a * reducedOmegaCost (b + d) b = ω^ (α + β) := by
    rw [hA, hB, NatOrdinal.wpow_add]
  rw [hM] at hH
  have hpA : plusCount a ≤ α := by
    have h := plusCount_le_cantorSupport_reducedOmegaCost (a + d) a
    rw [hA] at h
    exact h α (by simp only [NatOrdinal.cantorSupport_wpow, Finset.mem_singleton])
  have hpB : plusCount b ≤ β := by
    have h := plusCount_le_cantorSupport_reducedOmegaCost (b + d) b
    rw [hB] at h
    exact h β (by simp only [NatOrdinal.cantorSupport_wpow, Finset.mem_singleton])
  have hp' : plusCount (birthdayTruncation (a + b) c) < α + β :=
    hp.trans_le ((plusCount_add_le a b).trans (add_le_add hpA hpB))
  have hz := birthdayTruncation_mem_leftPrefixes_of_rightPrefixes_before (a + b) hc hR
  have hdel := rightPrefixes_gt_shifted_cutoff_of_pure_eq hd.le ih hz hp' hH hM
  refine ⟨c, hc, hlim, hR, hcof, hH, hp', hdel, ?_⟩
  have hcpos : 0 < c := NatOrdinal.val.lt_iff_lt.mp (by
    simpa only [NatOrdinal.val_zero] using
      (pos_iff_ne_zero.mpr (Ordinal.isSuccLimit_iff.mp hlim).1))
  obtain ⟨w, hw, _, hwC⟩ := hcof 0 hcpos
  have hzprefix : birthdayTruncation (a + b)
      (birthdayTruncation (a + b) c).birthday = birthdayTruncation (a + b) c := by
    rw [birthday_birthdayTruncation (a + b) hc.le]
  obtain ⟨v, hv, hlow, hhigh, _⟩ :=
    exists_rightPrefix_gap_window hzprefix hdel ⟨w, hw, hwC⟩
  exact ⟨v, hv, hlow, hhigh⟩

end Surreal
