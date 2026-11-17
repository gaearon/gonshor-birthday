/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.NatOrdinal.AddMonoidAlgebra
public import GonshorBirthday.NatOrdinal.FiniteBlocks
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

import GonshorBirthday.NatOrdinal.OrderedSum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Data.Finsupp.Order
import Mathlib.SetTheory.Ordinal.Principal

/-!
# Cantor supports and lower exponent bounds

The finite set of Cantor exponents is computed through the existing isomorphism between natural
ordinals and the additive monoid algebra with natural coefficients. Its support is a union under
natural addition and a sumset under natural multiplication. In particular, the least exponent of
a nonzero product is the natural sum of the least exponents of its factors.

A lower bound for all Cantor exponents also controls ordinary concatenation: appending finitely
many copies of that power agrees with natural addition, and every proper prefix leaves room for
one such copy. The divisibility used in this argument is ordinary ordinal left divisibility.
-/

universe u

public noncomputable section

namespace NatOrdinal

open Ordinal
open scoped Pointwise

/-- The finite set of exponents with nonzero coefficients in Cantor normal form. -/
def cantorSupport (x : NatOrdinal.{u}) : Finset NatOrdinal.{u} :=
  (toAddMonoidAlgebra x).coeff.support

theorem mem_cantorSupport {x e : NatOrdinal.{u}} :
    e ∈ cantorSupport x ↔ (toAddMonoidAlgebra x).coeff e ≠ 0 := by
  exact Finsupp.mem_support_iff

@[simp]
theorem cantorSupport_zero : cantorSupport (0 : NatOrdinal.{u}) = ∅ := by
  simp [cantorSupport]

@[simp]
theorem cantorSupport_wpow (e : NatOrdinal.{u}) : cantorSupport (ω^ e) = {e} := by
  simp [cantorSupport]

@[simp]
theorem cantorSupport_one : cantorSupport (1 : NatOrdinal.{u}) = {0} := by
  simpa only [wpow_zero] using cantorSupport_wpow (0 : NatOrdinal.{u})

@[simp]
theorem cantorSupport_omega : cantorSupport (of Ordinal.omega0 : NatOrdinal.{u}) = {1} := by
  simpa only [wpow_one] using cantorSupport_wpow (1 : NatOrdinal.{u})

@[simp]
theorem cantorSupport_add (x y : NatOrdinal.{u}) :
    cantorSupport (x + y) = cantorSupport x ∪ cantorSupport y := by
  classical
  simp [cantorSupport, Finsupp.support_add_eq_union]

theorem cantorSupport_mul_subset (x y : NatOrdinal.{u}) :
    cantorSupport (x * y) ⊆ cantorSupport x + cantorSupport y := by
  classical
  simpa only [cantorSupport, toAddMonoidAlgebra_mul] using
    AddMonoidAlgebra.support_coeff_mul_subset (toAddMonoidAlgebra x) (toAddMonoidAlgebra y)

theorem add_mem_cantorSupport_mul {x y a b : NatOrdinal.{u}}
    (ha : a ∈ cantorSupport x) (hb : b ∈ cantorSupport y) :
    a + b ∈ cantorSupport (x * y) := by
  classical
  rw [mem_cantorSupport, toAddMonoidAlgebra_mul, AddMonoidAlgebra.coeff_mul]
  apply Nat.ne_of_gt
  apply lt_of_lt_of_le (Nat.mul_pos (Nat.pos_of_ne_zero (mem_cantorSupport.mp ha))
    (Nat.pos_of_ne_zero (mem_cantorSupport.mp hb)))
  change _ ≤ ∑ i ∈ (toAddMonoidAlgebra x).coeff.support,
    ∑ j ∈ (toAddMonoidAlgebra y).coeff.support,
      if i + j = a + b then _ else 0
  apply le_trans ?_ (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) ha)
  simpa only [ite_true] using
    (Finset.single_le_sum (s := (toAddMonoidAlgebra y).coeff.support)
      (f := fun j ↦ if a + j = a + b then
        (toAddMonoidAlgebra x).coeff a * (toAddMonoidAlgebra y).coeff j else 0)
      (fun _ _ ↦ Nat.zero_le _) hb)

@[simp]
theorem cantorSupport_mul (x y : NatOrdinal.{u}) :
    cantorSupport (x * y) = cantorSupport x + cantorSupport y := by
  classical
  refine Finset.Subset.antisymm (cantorSupport_mul_subset x y) ?_
  intro e he
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp he
  exact add_mem_cantorSupport_mul ha hb

/-- Lower bounds for Cantor exponents add naturally under natural multiplication. -/
theorem le_cantorSupport_mul {x y p q : NatOrdinal.{u}}
    (hp : ∀ a ∈ cantorSupport x, p ≤ a) (hq : ∀ b ∈ cantorSupport y, q ≤ b) :
    ∀ e ∈ cantorSupport (x * y), p + q ≤ e := by
  classical
  intro e he
  rw [cantorSupport_mul] at he
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp he
  exact add_le_add (hp a ha) (hq b hb)

/-- The least Cantor exponent of a nonzero product is the natural sum of the input minima. -/
theorem isLeast_cantorSupport_mul {x y p q : NatOrdinal.{u}}
    (hp : IsLeast (cantorSupport x : Set NatOrdinal.{u}) p)
    (hq : IsLeast (cantorSupport y : Set NatOrdinal.{u}) q) :
    IsLeast (cantorSupport (x * y) : Set NatOrdinal.{u}) (p + q) := by
  exact ⟨add_mem_cantorSupport_mul hp.1 hq.1,
    le_cantorSupport_mul (fun _ ha ↦ hp.2 ha) (fun _ hb ↦ hq.2 hb)⟩

theorem cantorSupport_sum {ι : Type*} (s : Finset ι) (f : ι → NatOrdinal.{u}) :
    cantorSupport (∑ i ∈ s, f i) = s.biUnion (fun i ↦ cantorSupport (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, ih]

theorem mem_cantorSupport_sum_wpow {n : ℕ} (f : Fin n → NatOrdinal.{u}) (i : Fin n) :
    f i ∈ cantorSupport (∑ j, ω^ (f j)) := by
  classical
  simp only [cantorSupport_sum, cantorSupport_wpow, Finset.mem_biUnion,
    Finset.mem_univ, Finset.mem_singleton, true_and]
  exact ⟨i, rfl⟩

private theorem of_oadd_wpow_sum {n : ℕ} (f : Fin n → NatOrdinal.{u})
    (hf : Antitone f) (p : NatOrdinal.{u}) (hp : ∀ i, p ≤ f i) :
    of ((∑ i, ω^ (f i)).val + (ω^ p).val) = (∑ i, ω^ (f i)) + ω^ p := by
  induction n with
  | zero => simp
  | succ n ih =>
    let t : NatOrdinal.{u} := ∑ i : Fin n, ω^ (f i.succ)
    have ht : t < ω^ (f 0 + 1) := by
      apply sum_lt_wpow
      intro i hi
      exact wpow_lt_wpow.mpr ((hf (Fin.zero_le i.succ)).trans_lt (lt_add_one _))
    have htp : t + ω^ p < ω^ (f 0 + 1) :=
      add_lt_wpow ht (wpow_lt_wpow.mpr ((hp 0).trans_lt (lt_add_one _)))
    have hsplit : of ((ω^ (f 0)).val + t.val) = ω^ (f 0) + t :=
      of_omega0_opow_add (by simpa only [val_wpow, val_add_one] using val.strictMono ht)
    have hi : of (t.val + (ω^ p).val) = t + ω^ p :=
      ih (fun i ↦ f i.succ) (hf.comp_monotone Fin.strictMono_succ.monotone)
        (fun i ↦ hp i.succ)
    have hi' : t.val + (ω^ p).val = (t + ω^ p).val := by
      exact congrArg val hi
    rw [Fin.sum_univ_succ]
    change of ((ω^ (f 0) + t).val + (ω^ p).val) = ω^ (f 0) + t + ω^ p
    rw [← hsplit, val_of, add_assoc, hi', hsplit, add_assoc]
    exact of_omega0_opow_add
      (by simpa only [val_wpow, val_add_one] using val.strictMono htp)

/-- Appending a power no larger than any Cantor exponent agrees with natural addition. -/
theorem of_oadd_wpow_of_le_cantorSupport {x p : NatOrdinal.{u}}
    (hp : ∀ e ∈ cantorSupport x, p ≤ e) :
    of (x.val + (ω^ p).val) = x + ω^ p := by
  obtain ⟨n, f, hf, rfl⟩ := exists_antitone_wpow_sum x
  exact of_oadd_wpow_sum f hf p (fun i ↦ hp _ (mem_cantorSupport_sum_wpow f i))

private theorem wpow_dvd_val_sum {n : ℕ} (f : Fin n → NatOrdinal.{u})
    (hf : Antitone f) (p : NatOrdinal.{u}) (hp : ∀ i, p ≤ f i) :
    (ω^ p).val ∣ (∑ i, ω^ (f i)).val := by
  induction n with
  | zero => simp
  | succ n ih =>
    let t : NatOrdinal.{u} := ∑ i : Fin n, ω^ (f i.succ)
    have ht : t < ω^ (f 0 + 1) := by
      apply sum_lt_wpow
      intro i hi
      exact wpow_lt_wpow.mpr ((hf (Fin.zero_le i.succ)).trans_lt (lt_add_one _))
    have hsplit : of ((ω^ (f 0)).val + t.val) = ω^ (f 0) + t :=
      of_omega0_opow_add (by simpa only [val_wpow, val_add_one] using val.strictMono ht)
    rw [Fin.sum_univ_succ]
    change (ω^ p).val ∣ (ω^ (f 0) + t).val
    rw [← hsplit, val_of]
    have hd : (ω^ p).val ∣ (ω^ (f 0)).val := by
      simp only [val_wpow]
      exact Ordinal.opow_dvd_opow _ (val.monotone (hp 0))
    exact (Ordinal.dvd_add_iff hd).mpr
      (ih (fun i ↦ f i.succ) (hf.comp_monotone Fin.strictMono_succ.monotone)
        (fun i ↦ hp i.succ))

/-- A lower bound for all Cantor exponents supplies ordinary left divisibility by that power. -/
theorem wpow_dvd_val_of_le_cantorSupport {x p : NatOrdinal.{u}}
    (hp : ∀ e ∈ cantorSupport x, p ≤ e) : (ω^ p).val ∣ x.val := by
  obtain ⟨n, f, hf, rfl⟩ := exists_antitone_wpow_sum x
  exact wpow_dvd_val_sum f hf p (fun i ↦ hp _ (mem_cantorSupport_sum_wpow f i))

/-- A proper prefix leaves room for one power no larger than the last Cantor exponent. -/
theorem oadd_wpow_le_of_lt_of_le_cantorSupport {x y p : NatOrdinal.{u}}
    (hxy : x < y) (hp : ∀ e ∈ cantorSupport y, p ≤ e) :
    of (x.val + (ω^ p).val) ≤ y := by
  obtain ⟨q, hq⟩ := wpow_dvd_val_of_le_cantorSupport hp
  apply of.monotone
  change x.val + (ω^ p).val ≤ y.val
  have hv := val.strictMono hxy
  rw [hq] at hv ⊢
  obtain ⟨a, ha, b, hb, hx⟩ := Ordinal.lt_mul_iff.mp hv
  rw [hx, add_assoc, val_wpow, Ordinal.add_omega0_opow hb, ← mul_add_one]
  exact mul_le_mul_right (Order.add_one_le_iff.mpr ha) _

/-- A finite coefficient introduces no new Cantor exponent into a pure omega power. -/
theorem cantorSupport_wpow_mul_natCast_subset (p : NatOrdinal.{u}) (n : ℕ) :
    cantorSupport (ω^ p * n) ⊆ {p} := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add_one, mul_add, mul_one, cantorSupport_add, cantorSupport_wpow]
    exact Finset.union_subset ih (by rfl)

/-- Any finite number of low final-power copies may be added naturally or ordinarily. -/
theorem of_oadd_wpow_mul_natCast_of_le_cantorSupport {x p : NatOrdinal.{u}}
    (hp : ∀ e ∈ cantorSupport x, p ≤ e) (n : ℕ) :
    of (x.val + (ω^ p).val * (n : Ordinal)) = x + ω^ p * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi : x.val + (ω^ p).val * (n : Ordinal) = (x + ω^ p * n).val :=
      congrArg val ih
    rw [Nat.cast_add_one, mul_add_one, ← add_assoc, hi, Nat.cast_add_one,
      mul_add, mul_one, ← add_assoc]
    apply of_oadd_wpow_of_le_cantorSupport
    intro e he
    rw [cantorSupport_add] at he
    rcases Finset.mem_union.mp he with he | he
    · exact hp e he
    · exact (Finset.mem_singleton.mp (cantorSupport_wpow_mul_natCast_subset p n he)).ge

/-- A final interval of an omega power has the full type, even after a nonzero prefix. -/
theorem wpow_osub_of_lt {x p : NatOrdinal.{u}} (hx : x < ω^ p) :
    of ((ω^ p).val - x.val) = ω^ p := by
  exact congrArg of (Ordinal.sub_eq_of_add_eq
    (Ordinal.add_omega0_opow (val.strictMono hx)))

private theorem le_of_wpow_dvd_val_sum {n : ℕ} (f : Fin n → NatOrdinal.{u})
    (hf : Antitone f) (p : NatOrdinal.{u})
    (hd : (ω^ p).val ∣ (∑ i, ω^ (f i)).val) : ∀ i, p ≤ f i := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    let t : NatOrdinal.{u} := ∑ i : Fin n, ω^ (f i.succ)
    have ht : t < ω^ (f 0 + 1) := by
      apply sum_lt_wpow
      intro i hi
      exact wpow_lt_wpow.mpr ((hf (Fin.zero_le i.succ)).trans_lt (lt_add_one _))
    have hsplit : of ((ω^ (f 0)).val + t.val) = ω^ (f 0) + t :=
      of_omega0_opow_add (by simpa only [val_wpow, val_add_one] using val.strictMono ht)
    have hspos : 0 < ∑ i, ω^ (f i) := by
      rw [Fin.sum_univ_succ]
      exact (wpow_pos (f 0)).trans_le (le_add_of_nonneg_right bot_le)
    have hp0 : p ≤ f 0 := by
      by_contra hp
      have hp' : f 0 < p := lt_of_not_ge hp
      have hs : (∑ i, ω^ (f i)) < ω^ p := by
        apply sum_lt_wpow
        intro i hi
        exact wpow_lt_wpow.mpr ((hf (Fin.zero_le i)).trans_lt hp')
      have hxne : (∑ i, ω^ (f i)).val ≠ 0 := (val.strictMono hspos).ne'
      exact hs.not_ge (of.monotone (Ordinal.le_of_dvd hxne hd))
    rw [Fin.sum_univ_succ] at hd
    change (ω^ p).val ∣ (ω^ (f 0) + t).val at hd
    rw [← hsplit, val_of] at hd
    have hd0 : (ω^ p).val ∣ (ω^ (f 0)).val := by
      simp only [val_wpow]
      exact Ordinal.opow_dvd_opow _ (val.monotone hp0)
    have hdt := (Ordinal.dvd_add_iff hd0).mp hd
    have hi := ih (fun i ↦ f i.succ) (hf.comp_monotone Fin.strictMono_succ.monotone) hdt
    intro i
    induction i using Fin.cases
    · exact hp0
    · exact hi _

/-- Ordinary left divisibility by an omega power bounds every Cantor exponent below. -/
theorem le_cantorSupport_of_wpow_dvd_val {x p : NatOrdinal.{u}}
    (hd : (ω^ p).val ∣ x.val) : ∀ e ∈ cantorSupport x, p ≤ e := by
  classical
  obtain ⟨n, f, hf, rfl⟩ := exists_antitone_wpow_sum x
  have hi := le_of_wpow_dvd_val_sum f hf p hd
  intro e he
  simp only [cantorSupport_sum, cantorSupport_wpow, Finset.mem_biUnion,
    Finset.mem_univ, Finset.mem_singleton, true_and] at he
  obtain ⟨i, rfl⟩ := he
  exact hi i

/-- A lower bound for Cantor exponents is exactly ordinary left divisibility by that power. -/
theorem wpow_dvd_val_iff_le_cantorSupport {x p : NatOrdinal.{u}} :
    (ω^ p).val ∣ x.val ↔ ∀ e ∈ cantorSupport x, p ≤ e :=
  ⟨le_cantorSupport_of_wpow_dvd_val, wpow_dvd_val_of_le_cantorSupport⟩

/-- A final interval of sufficiently large power blocks bounds every final Cantor exponent. -/
theorem le_cantorSupport_of_type_sigma_wpow_tail {I : Type u}
    [LinearOrder I] [WellFoundedLT I] (p : I → NatOrdinal.{u}) (j : I)
    (a : NatOrdinal.{u}) (c : Ordinal.{u}) (ha : ∀ i, j ≤ i → a ≤ p i) :
    ∀ e ∈ cantorSupport (of (c + typeLT (Σₗ i, (ω^ (p i)).val.ToType))), a ≤ e := by
  apply le_cantorSupport_of_wpow_dvd_val
  change (ω^ a).val ∣ c + typeLT (Σₗ i, (ω^ (p i)).val.ToType)
  rw [val_wpow]
  apply Ordinal.omega0_opow_dvd_add_type_sigma_of_tail
    (fun i ↦ (ω^ (p i)).val) j a.val c
  · simpa only [val_wpow] using
      (Ordinal.opow_ne_zero (p j).val Ordinal.omega0_ne_zero)
  · intro i hi
    rw [val_wpow]
    exact Ordinal.opow_dvd_opow _ (val.monotone (ha i hi))

end NatOrdinal
