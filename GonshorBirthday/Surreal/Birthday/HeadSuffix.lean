/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadRun

/-!
# Original minus positions after a negative unit monomial

After a higher normal-form head K, each canonical right prefix p of K-omega^s
with birthday at least birthday K gives the original left prefix K-p of omega^s.
This produces an order embedding of the original suffix minus positions into the
plus positions of omega^s, bounding their order type by omega^(plusCount s).
No deletion formula or cofinality hypothesis is used.
-/

universe u
public noncomputable section
namespace Surreal
open Set Ordinal

/-- Subtracting a late right prefix from the head gives a left prefix of the monomial. -/
theorem sub_mem_leftPrefixes_wpow_of_head_rightPrefix
    {K s p : Surreal.{u}} (hK : K.support ⊆ Ioi s)
    (hp : p ∈ rightPrefixes (K - ω^ s)) (hb : K.birthday ≤ p.birthday) :
    K - p ∈ leftPrefixes (ω^ s) := by
  have hpk : p ≤ K := by
    have hm := monotone_birthdayTruncation p.birthday
      (show K - ω^ s ≤ K by simp [wpow_nonneg])
    change birthdayTruncation (K - ω^ s) p.birthday ≤ birthdayTruncation K p.birthday at hm
    rw [(mem_rightPrefixes_iff.mp hp).1, birthdayTruncation_eq_self_of_birthday_le K hb] at hm
    exact hm
  have hnK : (-K).support ⊆ Ioi s := by simpa only [support_neg] using hK
  have hbound : |(K - ω^ s) - p| ≤ ((1 : ℝ) : Surreal) * ω^ s := by
    rw [Real.toSurreal_one, one_mul,
      abs_of_neg (sub_neg.mpr (mem_rightPrefixes_iff.mp hp).2)]
    linarith only [hpk]
  have hcan := birthdayTruncation_head_add_of_abs_sub_le_real_mul_wpow hnK
    (mem_rightPrefixes_iff.mp hp).1 (1 : ℝ) hbound
  have hsource : -K + (K - ω^ s) = -ω^ s := by ring
  have hcand : -K + p = -(K - p) := by ring
  rw [hsource, hcand] at hcan
  have hpre : birthdayTruncation (ω^ s) (K - p).birthday = K - p := by
    simpa only [neg_neg, birthday_neg] using birthdayTruncation_neg_of_eq hcan
  refine mem_leftPrefixes_iff.mpr ⟨hpre, ?_⟩
  have hs := (mem_rightPrefixes_iff.mp hp).2
  linarith only [hs]

/-- The original minus positions after a higher head have order type at most
the monomial plus count. -/
theorem minus_suffix_type_head_sub_wpow (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) :
    typeLT {i : (K - ω^ s).birthday.val.ToType | K.birthday ≤ NatOrdinal.of i.toOrd.1 ∧
      K - ω^ s < birthdayTruncation (K - ω^ s) (NatOrdinal.of i.toOrd.1)} ≤
        (ω^ (plusCount s)).val := by
  let Z := K - ω^ s
  let D := {i : Z.birthday.val.ToType | K.birthday ≤ NatOrdinal.of i.toOrd.1 ∧
    Z < birthdayTruncation Z (NatOrdinal.of i.toOrd.1)}
  let E := {i : (ω^ s).birthday.val.ToType |
    birthdayTruncation (ω^ s) (NatOrdinal.of i.toOrd.1) < ω^ s}
  have hidx (i : D) : NatOrdinal.of i.1.toOrd.1 < Z.birthday :=
    NatOrdinal.of.lt_iff_lt.mpr i.1.toOrd.2
  have hpos (i : D) : birthdayTruncation Z (NatOrdinal.of i.1.toOrd.1) ∈ rightPrefixes Z :=
    mem_rightPrefixes.mpr ⟨_, hidx i, rfl, i.2.2⟩
  have hbpos (i : D) : (birthdayTruncation Z (NatOrdinal.of i.1.toOrd.1)).birthday =
      NatOrdinal.of i.1.toOrd.1 := birthday_birthdayTruncation Z (hidx i).le
  have hA (i : D) : K - birthdayTruncation Z (NatOrdinal.of i.1.toOrd.1) ∈
      leftPrefixes (ω^ s) := by
    apply sub_mem_leftPrefixes_wpow_of_head_rightPrefix hK (hpos i)
    rw [hbpos]
    exact i.2.1
  let f : D → E := fun i ↦
    ⟨Ordinal.ToType.mk ⟨(K - birthdayTruncation Z (NatOrdinal.of i.1.toOrd.1)).birthday.val,
      NatOrdinal.val.strictMono (birthday_lt_of_mem_leftPrefixes (hA i))⟩, by
        change birthdayTruncation (ω^ s) (NatOrdinal.of ((Ordinal.ToType.mk _).toOrd.1)) < ω^ s
        simpa only [Ordinal.ToType.toOrd, OrderIso.symm_apply_apply, NatOrdinal.of_val,
          (mem_leftPrefixes_iff.mp (hA i)).1] using (mem_leftPrefixes_iff.mp (hA i)).2⟩
  have hf : StrictMono f := by
    intro i j hij
    have hij0 : i.1 < j.1 := hij
    have hij' := Ordinal.ToType.mk.symm.strictMono hij0
    have hbi : (birthdayTruncation Z (NatOrdinal.of i.1.toOrd.1)).birthday <
        NatOrdinal.of j.1.toOrd.1 := by
      rw [hbpos]
      exact NatOrdinal.of.strictMono hij'
    have hpji := birthdayTruncation_lt hbi i.2.2
    have hai := sub_lt_sub_left hpji K
    have hle := birthday_le_of_left_between (hA i) hai.le (mem_leftPrefixes_iff.mp (hA j)).2.le
    have hne : (K - birthdayTruncation Z (NatOrdinal.of i.1.toOrd.1)).birthday ≠
        (K - birthdayTruncation Z (NatOrdinal.of j.1.toOrd.1)).birthday := by
      intro he
      have hpre := (mem_leftPrefixes_iff.mp (hA i)).1
      rw [he, (mem_leftPrefixes_iff.mp (hA j)).1] at hpre
      exact hai.ne hpre.symm
    have hlt := NatOrdinal.val.strictMono (lt_of_le_of_ne hle hne)
    change Ordinal.ToType.mk _ < Ordinal.ToType.mk _
    exact Ordinal.ToType.mk.strictMono hlt
  have htype := (RelEmbedding.ofMonotone f hf).ordinal_type_le
  have hpc : typeLT E = (ω^ (plusCount s)).val := by
    rw [← plusCount_wpow s, plusCount_eq]
    simp only [NatOrdinal.val_of]
    rfl
  exact htype.trans_eq hpc

/-- A negative unit last monomial has an original minus suffix bounded by its pure-power quantum. -/
theorem exists_minus_suffix_le_head_sub_wpow (K s : Surreal.{u}) (hK : K.support ⊆ Ioi s) :
    ∃ c < (K - ω^ s).birthday,
      typeLT {i : (K - ω^ s).birthday.val.ToType | c ≤ NatOrdinal.of i.toOrd.1 ∧
        K - ω^ s < birthdayTruncation (K - ω^ s) (NatOrdinal.of i.toOrd.1)} ≤
          (ω^ (plusCount s)).val :=
  ⟨K.birthday, birthday_lt_of_mem_rightPrefixes (head_mem_rightPrefixes_sub_wpow K s hK),
    minus_suffix_type_head_sub_wpow K s hK⟩

end Surreal
