/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.FieldTheory.Minpoly.IsConjRoot

/-!
# Conjugate root classes

In this file, we define the `ConjRootClass` of a field extension `L / K` as the quotient of `L` by
the relation `IsConjRoot K`.
-/

variable (K L S : Type*) [Field K] [Field L] [Field S]
variable [Algebra K L] [Algebra K S] [Algebra L S] [IsScalarTower K L S]

/-- `ConjRootClass K L` is the quotient of `L` by the relation `IsConjRoot K`. -/
def ConjRootClass := Quotient (α := L) (IsConjRoot.setoid K L)

namespace ConjRootClass

variable {L}

/-- The canonical quotient map from a field `K` into the `ConjRootClass` of the field extension
`L / K`. -/
def mk (x : L) : ConjRootClass K L :=
  ⟦x⟧

@[simp]
theorem mk_def {x : L} : ⟦x⟧ = mk K x := rfl

instance : Zero (ConjRootClass K L) :=
  ⟨mk K 0⟩

@[elab_as_elim, cases_eliminator, induction_eliminator]
lemma ind {motive : ConjRootClass K L → Prop} (h : ∀ x : L, motive (mk K x))
    (c : ConjRootClass K L) : motive c :=
  Quotient.ind h c

variable {K}

@[simp]
theorem mk_eq_mk {x y : L} : mk K x = mk K y ↔ IsConjRoot K x y := Quotient.eq

@[simp]
theorem mk_zero : mk K (0 : L) = 0 :=
  rfl

@[simp]
theorem mk_eq_zero_iff (x : L) : mk K x = 0 ↔ x = 0 := by
  rw [eq_comm (b := 0), ← mk_zero, mk_eq_mk, isConjRoot_zero_iff_eq_zero]

instance [Normal K L] [DecidableEq L] [Fintype Gal(L/K)] : DecidableEq (ConjRootClass K L) :=
  Quotient.decidableEq (d := IsConjRoot.decidable)

/-- `c.carrier` is the set of conjugates represented by `c`. -/
def carrier (c : ConjRootClass K L) : Set L :=
  mk K ⁻¹' {c}

@[simp]
theorem mem_carrier {x : L} {c : ConjRootClass K L} : x ∈ c.carrier ↔ mk K x = c :=
  Iff.rfl

@[simp]
theorem carrier_zero : (0 : ConjRootClass K L).carrier = {0} := by
  ext; rw [mem_carrier, mk_eq_zero_iff, Set.mem_singleton_iff]

theorem carrier_inj : Function.Injective (carrier (K := K) (L := L)) := by
  intro x y H
  induction x with | h x => ?_
  induction y with | h y => ?_
  simp_rw [Set.ext_iff, mem_carrier] at H
  rw [← H]

instance : Neg (ConjRootClass K L) where
  neg := Quotient.map (fun x ↦ -x) (fun _ _ ↦ IsConjRoot.neg)

theorem mk_neg (x : L) : - mk K x = mk K (-x) :=
  rfl

instance : InvolutiveNeg (ConjRootClass K L) where
  neg_neg c := by induction c; rw [mk_neg, mk_neg, neg_neg]

@[simp]
theorem carrier_neg (c : ConjRootClass K L) : carrier (- c) = - carrier c := by
  ext
  simp [mem_carrier, ← mk_neg, neg_eq_iff_eq_neg]

theorem exists_mem_carrier_add_eq_zero (x y : ConjRootClass K L) :
    (∃ᵉ (a ∈ x.carrier) (b ∈ y.carrier), a + b = 0) ↔ x = -y := by
  simp_rw [mem_carrier]
  constructor
  · rintro ⟨a, rfl, b, rfl, h⟩
    rw [mk_neg, mk_eq_mk, add_eq_zero_iff_eq_neg.mp h]
  · rintro rfl
    induction y with
    | h y => exact ⟨-y, mk_neg y, y, rfl, neg_add_cancel _⟩

instance [Normal K L] [DecidableEq L] [Fintype Gal(L/K)] (c : ConjRootClass K L) :
    DecidablePred (· ∈ c.carrier) := fun x ↦
  decidable_of_iff (mk K x = c) (by simp)

instance [Normal K L] [DecidableEq L] [Fintype Gal(L/K)] (c : ConjRootClass K L) :
    Fintype c.carrier :=
  Quotient.recOnSubsingleton c fun x =>
    .ofFinset
      ((Finset.univ (α := Gal(L/K))).image (· x))
      (fun _ ↦ by simp [← isConjRoot_iff_exists_algEquiv, ← mk_eq_mk])

open Polynomial

/-- `c.minpoly` is the minimal polynomial of the conjugates. -/
protected noncomputable def minpoly : ConjRootClass K L → K[X] :=
  Quotient.lift (minpoly K) fun _ _ ↦ id

@[simp]
theorem minpoly_mk (x : L) : (mk K x).minpoly = minpoly K x :=
  rfl

@[simp]
theorem minpoly_inj {c d : ConjRootClass K L} : c.minpoly = d.minpoly ↔ c = d := by
  induction c
  induction d
  simp [isConjRoot_def]

theorem minpoly_injective : Function.Injective (ConjRootClass.minpoly (K := K) (L := L)) :=
  fun _ _ ↦ minpoly_inj.mp

theorem splits_minpoly [n : Normal K L] (c : ConjRootClass K L) :
    Splits (algebraMap K L) c.minpoly := by
  induction c
  rw [minpoly_mk]
  exact n.splits _

section IsAlgebraic

variable [Algebra.IsAlgebraic K L]

theorem monic_minpoly (c : ConjRootClass K L) : c.minpoly.Monic := by
  induction c
  rw [minpoly_mk]
  exact minpoly.monic (Algebra.IsIntegral.isIntegral _)

theorem minpoly_ne_zero (c : ConjRootClass K L) : c.minpoly ≠ 0 :=
  c.monic_minpoly.ne_zero

theorem irreducible_minpoly (c : ConjRootClass K L) : Irreducible c.minpoly := by
  induction c
  rw [minpoly_mk]
  exact minpoly.irreducible (Algebra.IsIntegral.isIntegral _)

theorem aeval_minpoly_iff (x : L) (c : ConjRootClass K L) :
    aeval x c.minpoly = 0 ↔ mk K x = c := by
  induction c
  simpa [← isConjRoot_iff_aeval_eq_zero (Algebra.IsIntegral.isIntegral _)] using comm

theorem rootSet_minpoly_eq_carrier (c : ConjRootClass K L) :
    c.minpoly.rootSet L = c.carrier := by
  ext x
  rw [mem_carrier, mem_rootSet, aeval_minpoly_iff x c]
  simp [c.minpoly_ne_zero]

end IsAlgebraic

section IsSeparable

variable [Algebra.IsSeparable K L]

theorem separable_minpoly (c : ConjRootClass K L) : Separable c.minpoly := by
  induction c
  exact Algebra.IsSeparable.isSeparable K _

theorem nodup_aroots_minpoly (c : ConjRootClass K L) : (c.minpoly.aroots L).Nodup :=
  nodup_roots c.separable_minpoly.map

theorem aroots_minpoly_eq_carrier_val (c : ConjRootClass K L) [Fintype c.carrier] :
    c.minpoly.aroots L = c.carrier.toFinset.1 := by
  classical
  simp_rw [← rootSet_minpoly_eq_carrier, rootSet_def, Finset.toFinset_coe, Multiset.toFinset_val,
    c.nodup_aroots_minpoly.dedup]

theorem carrier_eq_mk_aroots_minpoly (c : ConjRootClass K L) [Fintype c.carrier] :
    c.carrier.toFinset = ⟨c.minpoly.aroots L, c.nodup_aroots_minpoly⟩ := by
  simp only [aroots_minpoly_eq_carrier_val]

theorem minpoly.map_eq_prod [Normal K L] (c : ConjRootClass K L) [Fintype c.carrier] :
    c.minpoly.map (algebraMap K L) = ∏ x ∈ c.carrier.toFinset, (X - C x) := by
  classical
  simp_rw [← rootSet_minpoly_eq_carrier, Finset.prod_eq_multiset_prod, rootSet_def,
    Finset.toFinset_coe, Multiset.toFinset_val]
  rw [Multiset.dedup_eq_self.mpr (nodup_roots c.separable_minpoly.map),
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq (c.monic_minpoly.map _)]
  rw [← splits_iff_card_roots, splits_id_iff_splits]
  exact c.splits_minpoly

end IsSeparable

end ConjRootClass
