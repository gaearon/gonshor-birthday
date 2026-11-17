/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.OmegaBlock
public import GonshorBirthday.Surreal.Birthday.ExpansionLength

/-!
# The exact intrinsic omega-map birthday

The length uses the original canonical plus ranks and ordinary concatenation of
all exponent sign blocks.
-/

universe u
public noncomputable section
namespace Surreal
open Set Order

/-- The omega-map birthday equals the complete canonical sign-block expansion length. -/
theorem birthday_wpow_eq_omegaExpansionLength (x : Surreal.{u}) :
    (ω^ x).birthday = omegaExpansionLength x Set.univ := by
  have aux : ∀ a : Ordinal.{u}, NatOrdinal.of a ≤ x.birthday →
      (ω^ birthdayTruncation x (NatOrdinal.of a)).birthday =
        omegaExpansionLength (birthdayTruncation x (NatOrdinal.of a)) Set.univ := by
    intro a
    induction a using Ordinal.limitRecOn with
    | zero =>
      intro ha
      have hT : birthdayTruncation x (NatOrdinal.of 0) = 0 := by simp
      have hE := congrArg (fun y : Surreal.{u} ↦ omegaExpansionLength y Set.univ) hT
      rw [hE, omegaExpansionLength_univ_zero, hT]
      simp
    | add_one a ih =>
      intro ha
      have ha' : NatOrdinal.of a + 1 ≤ x.birthday := by
        simpa only [NatOrdinal.of_add_one] using ha
      have hp : NatOrdinal.of a ≤ x.birthday := (le_add_of_nonneg_right (by simp)).trans ha'
      apply NatOrdinal.val.injective
      rw [NatOrdinal.of_add_one, birthday_wpow_birthdayTruncation_add_one x ha',
        NatOrdinal.val_of, ih hp, omegaExpansionLength_univ_birthdayTruncation_add_one x ha']
      simp only [NatOrdinal.val_wpow, NatOrdinal.val_add_one, Ordinal.opow_add,
        Ordinal.opow_one]
    | limit a hl ih =>
      intro ha
      have hy : (birthdayTruncation x (NatOrdinal.of a)).birthday = NatOrdinal.of a :=
        birthday_birthdayTruncation x ha
      have hly : IsSuccLimit (birthdayTruncation x (NatOrdinal.of a)).birthday.val := by
        simpa only [hy, NatOrdinal.val_of] using hl
      have hiff : ∀ M : NatOrdinal.{u},
          (ω^ birthdayTruncation x (NatOrdinal.of a)).birthday ≤ M ↔
            omegaExpansionLength (birthdayTruncation x (NatOrdinal.of a)) Set.univ ≤ M := by
        intro M
        rw [birthday_wpow_le_iff_of_isSuccLimit _ hly,
          omegaExpansionLength_univ_birthdayTruncation_limit x ha
            (by simpa only [NatOrdinal.val_of] using hl), hy]
        apply forall_congr'
        intro b
        apply forall_congr'
        intro hb
        rw [birthdayTruncation_birthdayTruncation x hb.le ha]
        have hi := ih b.val (by simpa only [NatOrdinal.val_of] using
          NatOrdinal.val.strictMono hb) (hb.le.trans ha)
        simpa only [NatOrdinal.of_val] using (congrArg (fun z ↦ z ≤ M) hi).to_iff
      exact le_antisymm ((hiff _).mpr le_rfl) ((hiff _).mp le_rfl)
  have ht := aux x.birthday.val (by simp)
  have hT : birthdayTruncation x (NatOrdinal.of x.birthday.val) = x := by simp
  calc
    (ω^ x).birthday = (ω^ birthdayTruncation x (NatOrdinal.of x.birthday.val)).birthday :=
      congrArg (fun y : Surreal.{u} ↦ (ω^ y).birthday) hT.symm
    _ = _ := ht
    _ = omegaExpansionLength x Set.univ :=
      congrArg (fun y : Surreal.{u} ↦ omegaExpansionLength y Set.univ) hT

/-- Every stage within an expanded plus block is the corresponding actual omega prefix. -/
theorem birthdayTruncation_wpow_plus_block (x : Surreal.{u}) {a : NatOrdinal.{u}}
    (ha : a + 1 ≤ x.birthday) (hl : birthdayTruncation x a < x) {t : Ordinal.{u}}
    (ht : t ≤ (ω^ plusCount (birthdayTruncation x a)).val * Ordinal.omega0) :
    birthdayTruncation (ω^ x)
      (NatOrdinal.of ((omegaExpansionLength (birthdayTruncation x a) Set.univ).val + t)) =
        appendPluses (ω^ birthdayTruncation x a) t := by
  have hpre := birthdayTruncation_wpow_birthdayTruncation x (a + 1)
  rw [birthdayTruncation_add_one_eq_appendPlus x ha hl, wpow_appendPlus] at hpre
  have hstage : birthdayTruncation
      (appendPluses (ω^ birthdayTruncation x a)
        ((ω^ plusCount (birthdayTruncation x a)).val * Ordinal.omega0))
      (appendPluses (ω^ birthdayTruncation x a) t).birthday =
        appendPluses (ω^ birthdayTruncation x a) t := by
    rw [birthday_appendPluses]
    exact birthdayTruncation_appendPluses_add _ ht
  have h := birthdayTruncation_eq_trans hpre hstage
  rwa [birthday_appendPluses, birthday_wpow_eq_omegaExpansionLength] at h

/-- Every stage within an expanded minus block is the corresponding actual omega prefix. -/
theorem birthdayTruncation_wpow_minus_block (x : Surreal.{u}) {a : NatOrdinal.{u}}
    (ha : a + 1 ≤ x.birthday) (hr : x < birthdayTruncation x a) {t : Ordinal.{u}}
    (ht : t ≤ (ω^ plusCount (birthdayTruncation x a)).val * Ordinal.omega0) :
    birthdayTruncation (ω^ x)
      (NatOrdinal.of ((omegaExpansionLength (birthdayTruncation x a) Set.univ).val + t)) =
        appendMinuses (ω^ birthdayTruncation x a) t := by
  have hpre := birthdayTruncation_wpow_birthdayTruncation x (a + 1)
  rw [birthdayTruncation_add_one_eq_appendMinus x ha hr, wpow_appendMinus] at hpre
  have hstage : birthdayTruncation
      (appendMinuses (ω^ birthdayTruncation x a)
        ((ω^ plusCount (birthdayTruncation x a)).val * Ordinal.omega0))
      (appendMinuses (ω^ birthdayTruncation x a) t).birthday =
        appendMinuses (ω^ birthdayTruncation x a) t := by
    rw [birthday_appendMinuses]
    exact birthdayTruncation_appendMinuses_add _ ht
  have h := birthdayTruncation_eq_trans hpre hstage
  rwa [birthday_appendMinuses, birthday_wpow_eq_omegaExpansionLength] at h


/-- Every interior position of a plus exponent block carries a plus sign in the omega-map. -/
theorem birthdayTruncation_wpow_plus_block_lt (x : Surreal.{u}) {a : NatOrdinal.{u}}
    (ha : a + 1 ≤ x.birthday) (hl : birthdayTruncation x a < x) {t : Ordinal.{u}}
    (ht : t < (ω^ plusCount (birthdayTruncation x a)).val * Ordinal.omega0) :
    birthdayTruncation (ω^ x)
      (NatOrdinal.of ((omegaExpansionLength (birthdayTruncation x a) Set.univ).val + t)) <
        ω^ x := by
  have hpre := birthdayTruncation_wpow_birthdayTruncation x (a + 1)
  rw [birthdayTruncation_add_one_eq_appendPlus x ha hl, wpow_appendPlus] at hpre
  have hstage : appendPluses (ω^ birthdayTruncation x a) t ∈ leftPrefixes
      (appendPluses (ω^ birthdayTruncation x a)
        ((ω^ plusCount (birthdayTruncation x a)).val * Ordinal.omega0)) := by
    apply mem_leftPrefixes_iff.mpr
    exact ⟨birthdayTruncation_appendPluses_of_lt _ ht, strictMono_appendPluses _ ht⟩
  have hsource := leftPrefixes_subset_of_birthdayTruncation_eq hpre hstage
  rw [birthdayTruncation_wpow_plus_block x ha hl ht.le]
  exact (mem_leftPrefixes_iff.mp hsource).2

/-- Every interior position of a minus exponent block carries a minus sign in the omega-map. -/
theorem lt_birthdayTruncation_wpow_minus_block (x : Surreal.{u}) {a : NatOrdinal.{u}}
    (ha : a + 1 ≤ x.birthday) (hr : x < birthdayTruncation x a) {t : Ordinal.{u}}
    (ht : t < (ω^ plusCount (birthdayTruncation x a)).val * Ordinal.omega0) :
    ω^ x < birthdayTruncation (ω^ x)
      (NatOrdinal.of ((omegaExpansionLength (birthdayTruncation x a) Set.univ).val + t)) := by
  have hpre := birthdayTruncation_wpow_birthdayTruncation x (a + 1)
  rw [birthdayTruncation_add_one_eq_appendMinus x ha hr, wpow_appendMinus] at hpre
  have hstage : appendMinuses (ω^ birthdayTruncation x a) t ∈ rightPrefixes
      (appendMinuses (ω^ birthdayTruncation x a)
        ((ω^ plusCount (birthdayTruncation x a)).val * Ordinal.omega0)) := by
    apply mem_rightPrefixes_iff.mpr
    exact ⟨birthdayTruncation_appendMinuses_of_lt _ ht, strictAnti_appendMinuses _ ht⟩
  have hsource := rightPrefixes_subset_of_birthdayTruncation_eq hpre hstage
  rw [birthdayTruncation_wpow_minus_block x ha hr ht.le]
  exact (mem_rightPrefixes_iff.mp hsource).2


end Surreal
