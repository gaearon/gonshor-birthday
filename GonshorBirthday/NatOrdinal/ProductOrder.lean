/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.NatOrdinal.MultiplicationBound
public import GonshorBirthday.NatOrdinal.Shuffle

/-!
# The natural-product bound for ordered rectangles

A well-ordered linear extension of a coordinatewise product has order type at most the natural
product. This is the upper-bound part of Carruth, *Arithmetic of ordinals with applications to the
theory of ordered Abelian groups* (1942), Theorem 2.I, pp. 264–265.

The coordinate version also allows subsets of a rectangle. Induction splits a non-pure factor at
its leading omega power. For two pure factors, each proper output prefix lies in two strictly
smaller rectangles. The two-colour shuffle bound finishes that case. No continuity of natural
multiplication is used. Existence of a linear extension attaining the bound is a separate result.
-/

universe u

public noncomputable section

namespace NatOrdinal

open Set Ordinal

private theorem eq_zero_or_eq_wpow_or_split (a : NatOrdinal.{u}) :
    a = 0 ∨ (∃ c, a = ω^ c) ∨
      ∃ a₀ a₁ : NatOrdinal.{u}, a₀ < a ∧ a₁ < a ∧ a = a₀ + a₁ ∧
        a.val = a₀.val + a₁.val := by
  by_cases ha : a = 0
  · exact Or.inl ha
  by_cases hp : ∃ c, a = ω^ c
  · exact Or.inr (Or.inl hp)
  have hav : a.val ≠ 0 := by simpa using ha
  let c := Ordinal.log Ordinal.omega0 a.val
  have hlo : Ordinal.omega0 ^ c ≤ a.val := Ordinal.opow_log_le_self _ hav
  have hhi : a.val < Ordinal.omega0 ^ (c + 1) := by
    simpa only [Order.succ_eq_add_one] using
      Ordinal.lt_opow_succ_log_self Ordinal.one_lt_omega0 a.val
  have hr : a.val - Ordinal.omega0 ^ c < a.val :=
    Ordinal.sub_omega0_opow_log_lt hav
  have hsum := Ordinal.add_sub_cancel_of_le hlo
  refine Or.inr (Or.inr ⟨ω^ of c, of (a.val - Ordinal.omega0 ^ c), ?_, hr, ?_, ?_⟩)
  · apply lt_of_le_of_ne (of.monotone hlo)
    intro he
    exact hp ⟨of c, he.symm⟩
  · have h := of_omega0_opow_add (hr.trans hhi)
    rw [hsum, of_val] at h
    exact h
  · simpa only [val_wpow, val_of] using hsum.symm

private def GridBound (a b : NatOrdinal.{u}) : Prop :=
  ∀ (γ : Type u) [LinearOrder γ] [WellFoundedLT γ]
    (p q : γ → NatOrdinal.{u}),
    (∀ x, p x < a) → (∀ x, q x < b) →
    (∀ x y, p x ≤ p y → q x ≤ q y → x ≤ y) →
    of (typeLT γ) ≤ a * b

private theorem GridBound.symm {a b : NatOrdinal.{u}} (h : GridBound a b) : GridBound b a := by
  intro γ _ _ p q hp hq hm
  simpa only [mul_comm] using h γ q p hq hp (fun x y hq hp ↦ hm x y hp hq)

private theorem gridBound_zero_left (b : NatOrdinal.{u}) : GridBound 0 b := by
  intro γ _ _ p q hp hq hm
  let : IsEmpty γ := ⟨fun x ↦ (not_lt_of_ge (bot_le : (0 : NatOrdinal.{u}) ≤ p x)) (hp x)⟩
  simp [Ordinal.type_eq_zero_of_empty]

private theorem gridBound_of_split {a a₀ a₁ b : NatOrdinal.{u}}
    (hn : a = a₀ + a₁) (ho : a.val = a₀.val + a₁.val)
    (h₀ : GridBound a₀ b) (h₁ : GridBound a₁ b) : GridBound a b := by
  intro γ _ _ p q hp hq hm
  let s : Set γ := {x | p x < a₀}
  have hs : of (typeLT s) ≤ a₀ * b :=
    h₀ s (fun x : s ↦ p x) (fun x : s ↦ q x) (fun x ↦ x.2) (fun x ↦ hq x)
      (fun x y hx hy ↦ hm x y hx hy)
  have hleft (x : (sᶜ : Set γ)) : a₀.val ≤ (p x).val :=
    val.monotone (le_of_not_gt x.2)
  have hrem (x : (sᶜ : Set γ)) : of ((p x).val - a₀.val) < a₁ := by
    rw [← of_val a₁]
    apply of.strictMono
    apply (Ordinal.sub_lt_of_le (hleft x)).mpr
    rw [← ho]
    exact val.strictMono (hp x)
  have hcmp (x y : (sᶜ : Set γ))
      (h : of ((p x).val - a₀.val) ≤ of ((p y).val - a₀.val)) : p x ≤ p y := by
    apply val.le_iff_le.mp
    calc
      (p x).val = a₀.val + ((p x).val - a₀.val) :=
        (Ordinal.add_sub_cancel_of_le (hleft x)).symm
      _ ≤ a₀.val + ((p y).val - a₀.val) := add_le_add le_rfl (val.monotone h)
      _ = (p y).val := Ordinal.add_sub_cancel_of_le (hleft y)
  have ht : of (typeLT (sᶜ : Set γ)) ≤ a₁ * b :=
    h₁ (sᶜ : Set γ) (fun x : (sᶜ : Set γ) ↦ of ((p x).val - a₀.val)) (fun x ↦ q x)
      hrem (fun x ↦ hq x) (fun x y hx hy ↦ hm x y (hcmp x y hx) hy)
  calc
    of (typeLT γ) ≤ of (typeLT s) + of (typeLT (sᶜ : Set γ)) :=
      of_type_le_add_of_type_compl s
    _ ≤ a₀ * b + a₁ * b := add_le_add hs ht
    _ = a * b := by rw [← add_mul, ← hn]

private theorem gridBound_wpow {a b : NatOrdinal.{u}}
    (IH : ∀ a' b', a' ≤ ω^ a → b' ≤ ω^ b → (a' < ω^ a ∨ b' < ω^ b) →
      GridBound a' b') : GridBound (ω^ a) (ω^ b) := by
  intro γ _ _ p q hp hq hm
  have hprefix (z : γ) : of (typeLT (Iio z)) < ω^ a * ω^ b := by
    let s : Set (Iio z) := {x | p x < p z}
    have hs : of (typeLT s) ≤ p z * ω^ b :=
      IH (p z) (ω^ b) (hp z).le le_rfl (Or.inl (hp z)) s
        (fun x : s ↦ p x.1) (fun x : s ↦ q x.1) (fun x ↦ x.2) (fun x ↦ hq x.1)
        (fun x y hx hy ↦ hm x.1 y.1 hx hy)
    have hq' (x : (sᶜ : Set (Iio z))) : q x.1 < q z := by
      by_contra hn
      exact (not_le_of_gt x.1.2) (hm z x.1 (le_of_not_gt x.2) (le_of_not_gt hn))
    have ht : of (typeLT (sᶜ : Set (Iio z))) ≤ ω^ a * q z :=
      IH (ω^ a) (q z) le_rfl (hq z).le (Or.inr (hq z)) (sᶜ : Set (Iio z))
        (fun x : (sᶜ : Set (Iio z)) ↦ p x.1) (fun x ↦ q x.1)
        (fun x ↦ hp x.1) hq' (fun x y hx hy ↦ hm x.1 y.1 hx hy)
    have hpb : p z * ω^ b < ω^ (a + b) :=
      mul_lt_wpow_add (hp z) (wpow_lt_wpow.mpr (lt_add_one b))
    have haq : ω^ a * q z < ω^ (a + b) := by
      simpa only [mul_comm, add_comm] using
        mul_lt_wpow_add (hq z) (wpow_lt_wpow.mpr (lt_add_one a))
    calc
      of (typeLT (Iio z)) ≤ of (typeLT s) + of (typeLT (sᶜ : Set (Iio z))) :=
        of_type_le_add_of_type_compl s
      _ ≤ p z * ω^ b + ω^ a * q z := add_le_add hs ht
      _ < ω^ (a + b) := add_lt_wpow hpb haq
      _ = ω^ a * ω^ b := wpow_add a b
  by_contra h
  have hlt : (ω^ a * ω^ b).val < typeLT γ := by
    simpa only [val_of] using val.strictMono (lt_of_not_ge h)
  obtain ⟨z, hz⟩ := Ordinal.typein_surj (α := γ) (· < ·) hlt
  have h := hprefix z
  rw [type_Iio_lt, hz, of_val] at h
  exact (lt_irrefl _) h

private theorem gridBound (a b : NatOrdinal.{u}) : GridBound a b := by
  have aux : ∀ n : NatOrdinal.{u}, ∀ a b : NatOrdinal.{u}, a + b = n → GridBound a b := by
    intro n
    induction n using NatOrdinal.lt_wf.induction with
    | h n IH =>
      intro a b hn
      have ih (a' b' : NatOrdinal.{u}) (ha : a' ≤ a) (hb : b' ≤ b)
          (hstrict : a' < a ∨ b' < b) : GridBound a' b' := by
        apply IH (a' + b') ?_ a' b' rfl
        rw [← hn]
        rcases hstrict with ha' | hb'
        · exact add_lt_add_of_lt_of_le ha' hb
        · exact add_lt_add_of_le_of_lt ha hb'
      rcases eq_zero_or_eq_wpow_or_split a with rfl | ⟨c, rfl⟩ | ⟨a₀, a₁, ha₀, ha₁, hna, hoa⟩
      · exact gridBound_zero_left b
      · rcases eq_zero_or_eq_wpow_or_split b with rfl | ⟨d, rfl⟩ | ⟨b₀, b₁, hb₀, hb₁, hnb, hob⟩
        · exact (gridBound_zero_left (ω^ c)).symm
        · exact gridBound_wpow ih
        · apply GridBound.symm
          exact gridBound_of_split hnb hob
            (ih (ω^ c) b₀ le_rfl hb₀.le (Or.inr hb₀)).symm
            (ih (ω^ c) b₁ le_rfl hb₁.le (Or.inr hb₁)).symm
      · exact gridBound_of_split hna hoa
          (ih a₀ b ha₀.le le_rfl (Or.inl ha₀))
          (ih a₁ b ha₁.le le_rfl (Or.inl ha₁))
  exact aux (a + b) a b rfl

/-- A well order compatible with coordinatewise comparison has type at most the natural product.
This is a form of Carruth's theorem on the maximal order type of a product. -/
theorem of_type_le_mul_of_coordinates {γ : Type u} [LinearOrder γ] [WellFoundedLT γ]
    (a b : NatOrdinal.{u}) (p q : γ → NatOrdinal.{u})
    (hp : ∀ x, p x < a) (hq : ∀ x, q x < b)
    (hm : ∀ x y, p x ≤ p y → q x ≤ q y → x ≤ y) :
    of (typeLT γ) ≤ a * b :=
  gridBound a b γ p q hp hq hm

/-- A well-ordered linear extension of a product is bounded by the natural product of its types. -/
theorem of_type_le_mul_of_monotone_equiv {α β γ : Type u}
    [LinearOrder α] [WellFoundedLT α] [LinearOrder β] [WellFoundedLT β]
    [LinearOrder γ] [WellFoundedLT γ] (e : γ ≃ α × β) (hm : Monotone e.symm) :
    of (typeLT γ) ≤ of (typeLT α) * of (typeLT β) := by
  apply of_type_le_mul_of_coordinates (of (typeLT α)) (of (typeLT β))
    (fun x ↦ of (typein (α := α) (· < ·) (e x).1)) (fun x ↦ of (typein (α := β) (· < ·) (e x).2))
  · exact fun x ↦ of.strictMono (typein_lt_type _ _)
  · exact fun x ↦ of.strictMono (typein_lt_type _ _)
  · intro x y hp hq
    have hp' : (e x).1 ≤ (e y).1 :=
      le_of_not_gt ((typein_le_typein (α := α) (· < ·)).mp (of.le_iff_le.mp hp))
    have hq' : (e x).2 ≤ (e y).2 :=
      le_of_not_gt ((typein_le_typein (α := β) (· < ·)).mp (of.le_iff_le.mp hq))
    simpa only [Equiv.symm_apply_apply] using hm ⟨hp', hq'⟩

end NatOrdinal
