/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.LinearAlgebra.LinearDisjoint
import Mathlib.LinearAlgebra.TensorProduct.Subalgebra
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Algebra.Subalgebra.MulOpposite
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!

# Linearly disjoint subalgebras

This file contains basics about linearly disjoint subalgebras.

## Main definitions

- `Subalgebra.LinearDisjoint`: two subalgebras are linearly disjoint, if they are
  linearly disjoint as submodules (`Submodule.LinearDisjoint`).

- `Subalgebra.LinearDisjoint.mulMap`: if two subalgebras `A` and `B` of `S / R` are
  linearly disjoint, then there is `A ⊗[R] B ≃ₐ[R] A ⊔ B` induced by multiplication in `S`.

## Main results

### Equivalent characterization of linearly disjointness

- `Subalgebra.LinearDisjoint.linearIndependent_left_of_flat`:
  if `A` and `B` are linearly disjoint, if `B` is a flat `R`-module, then for any family of
  `R`-linearly independent elements of `A`, they are also `B`-linearly independent.

- `Subalgebra.LinearDisjoint.of_basis_left_op`:
  conversely, if a basis of `A` is also `B`-linearly independent, then `A` and `B` are
  linearly disjoint.

- `Subalgebra.LinearDisjoint.linearIndependent_right_of_flat`:
  if `A` and `B` are linearly disjoint, if `A` is a flat `R`-module, then for any family of
  `R`-linearly independent elements of `B`, they are also `A`-linearly independent.

- `Subalgebra.LinearDisjoint.of_basis_right`:
  conversely, if a basis of `B` is also `A`-linearly independent,
  then `A` and `B` are linearly disjoint.

- `Subalgebra.LinearDisjoint.linearIndependent_mul_of_flat`:
  if `A` and `B` are linearly disjoint, if one of `A` and `B` is flat, then for any family of
  `R`-linearly independent elements `{ a_i }` of `A`, and any family of
  `R`-linearly independent elements `{ b_j }` of `B`, the family `{ a_i * b_j }` in `S` is
  also `R`-linearly independent.

- `Subalgebra.LinearDisjoint.of_basis_mul`:
  conversely, if `{ a_i }` is an `R`-basis of `A`, if `{ b_j }` is an `R`-basis of `B`,
  such that the family `{ a_i * b_j }` in `S` is `R`-linearly independent,
  then `A` and `B` are linearly disjoint.

### Other main results

- `Subalgebra.LinearDisjoint.symm_of_commute`, `Subalgebra.linearDisjoint_symm_of_commute`:
  linearly disjoint is symmetric under some commutative conditions.

- `Subalgebra.LinearDisjoint.bot_left`, `Subalgebra.LinearDisjoint.bot_right`:
  the image of `R` in `S` is linearly disjoint with any other subalgebras.

- `Subalgebra.LinearDisjoint.sup_free_of_free`: the compositum of two linearly disjoint
  subalgebras is a free module, if two subalgebras are also free modules.

- `Subalgebra.LinearDisjoint.inf_eq_bot_of_commute`, `Subalgebra.LinearDisjoint.inf_eq_bot`:
  if `A` and `B` are linearly disjoint, under suitable technical conditions, they are disjoint.

The results with name containing "of_commute" also have corresponding specialized versions
assuming `S` is commutative.

## Tags

linearly disjoint, linearly independent, tensor product

-/

open scoped Classical TensorProduct

noncomputable section

universe u v w

namespace Subalgebra

variable {R : Type u} {S : Type v}

section Semiring

variable [CommSemiring R] [Semiring S] [Algebra R S]

variable (A B : Subalgebra R S)

/-- If `A` and `B` are subalgebras of `S / R`,
then `A` and `B` are linearly disjoint, if they are linearly disjoint as submodules of `S`. -/
protected abbrev LinearDisjoint : Prop := (toSubmodule A).LinearDisjoint (toSubmodule B)

theorem linearDisjoint_iff : A.LinearDisjoint B ↔ (toSubmodule A).LinearDisjoint (toSubmodule B) :=
  Iff.rfl

variable {A B}

@[nontriviality]
theorem LinearDisjoint.of_subsingleton [Subsingleton R] : A.LinearDisjoint B :=
  Submodule.LinearDisjoint.of_subsingleton

/-- Linearly disjoint is symmetric if elements in the module commute. -/
theorem LinearDisjoint.symm_of_commute (H : A.LinearDisjoint B)
    (hc : ∀ (a : A) (b : B), Commute a.1 b.1) : B.LinearDisjoint A :=
  Submodule.LinearDisjoint.symm_of_commute H hc

/-- Linearly disjoint is symmetric if elements in the module commute. -/
theorem linearDisjoint_symm_of_commute
    (hc : ∀ (a : A) (b : B), Commute a.1 b.1) : A.LinearDisjoint B ↔ B.LinearDisjoint A :=
  ⟨fun H ↦ H.symm_of_commute hc, fun H ↦ H.symm_of_commute fun _ _ ↦ (hc _ _).symm⟩

namespace LinearDisjoint

variable (A B)

/-- The image of `R` in `S` is linearly disjoint with any other subalgebras. -/
theorem bot_left : (⊥ : Subalgebra R S).LinearDisjoint B :=
  Submodule.LinearDisjoint.one_left _

/-- The image of `R` in `S` is linearly disjoint with any other subalgebras. -/
theorem bot_right : A.LinearDisjoint ⊥ :=
  Submodule.LinearDisjoint.one_right _

end LinearDisjoint

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring S] [Algebra R S]

variable {A B : Subalgebra R S}

/-- Linearly disjoint is symmetric in a commutative ring. -/
theorem LinearDisjoint.symm (H : A.LinearDisjoint B) : B.LinearDisjoint A :=
  H.symm_of_commute fun _ _ ↦ mul_comm _ _

/-- Linearly disjoint is symmetric in a commutative ring. -/
theorem linearDisjoint_symm : A.LinearDisjoint B ↔ B.LinearDisjoint A :=
  ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

namespace LinearDisjoint

variable (H : A.LinearDisjoint B)
include H

/-- If `A` and `B` are subalgebras in a commutative algebra `S` over `R`, and if they are
linearly disjoint, then there is the natural isomorphism
`A ⊗[R] B ≃ₐ[R] A ⊔ B` induced by multiplication in `S`. -/
protected def mulMap :=
  (AlgEquiv.ofInjective (A.mulMap B) H.injective).trans (equivOfEq _ _ (mulMap_range A B))

@[simp]
theorem val_mulMap_tmul (a : A) (b : B) : (H.mulMap (a ⊗ₜ[R] b) : S) = a.1 * b.1 := rfl

/-- If `A` and `B` are subalgebras in a commutative algebra `S` over `R`, and if they are
linearly disjoint, and if they are free `R`-modules, then `A ⊔ B` is also a free `R`-module. -/
theorem sup_free_of_free [Module.Free R A] [Module.Free R B] : Module.Free R ↥(A ⊔ B) :=
  Module.Free.of_equiv H.mulMap.toLinearEquiv

end LinearDisjoint

end CommSemiring

section Ring

namespace LinearDisjoint

variable [CommRing R] [Ring S] [Algebra R S]

variable (A B : Subalgebra R S)

lemma mulLeftMap_ker_eq_bot_iff_linearIndependent_op {ι : Type*} (a : ι → A) :
    LinearMap.ker (Submodule.mulLeftMap (M := toSubmodule A) (toSubmodule B) a) = ⊥ ↔
    LinearIndependent B.op (MulOpposite.op ∘ A.val ∘ a) := by
  -- need this instance otherwise `LinearMap.ker_eq_bot` does not work
  letI : AddCommGroup (ι →₀ toSubmodule B) := Finsupp.instAddCommGroup
  letI : AddCommGroup (ι →₀ B.op) := Finsupp.instAddCommGroup
  simp_rw [LinearIndependent, LinearMap.ker_eq_bot]
  let i : (ι →₀ B) →ₗ[R] S := Submodule.mulLeftMap (M := toSubmodule A) (toSubmodule B) a
  let j : (ι →₀ B) →ₗ[R] S := (MulOpposite.opLinearEquiv _).symm.toLinearMap ∘ₗ
    (Finsupp.linearCombination B.op (MulOpposite.op ∘ A.val ∘ a)).restrictScalars R ∘ₗ
    (Finsupp.mapRange.linearEquiv (linearEquivOp B)).toLinearMap
  suffices i = j by
    change Function.Injective i ↔ _
    simp_rw [this, j, LinearMap.coe_comp,
      LinearEquiv.coe_coe, EquivLike.comp_injective, EquivLike.injective_comp]
    rfl
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, coe_val,
    Finsupp.mapRange.linearEquiv_toLinearMap, LinearEquiv.coe_coe,
    MulOpposite.coe_opLinearEquiv_symm, LinearMap.coe_restrictScalars,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Finsupp.linearCombination_single,
    MulOpposite.unop_smul, MulOpposite.unop_op, i, j]
  exact Submodule.mulLeftMap_apply_single _ _ _

variable {A B} in
/-- If `A` and `B` are linearly disjoint, if `B` is a flat `R`-module, then for any family of
`R`-linearly independent elements of `A`, they are also `B`-linearly independent
in the opposite ring. -/
theorem linearIndependent_left_op_of_flat (H : A.LinearDisjoint B) [Module.Flat R B]
    {ι : Type*} {a : ι → A} (ha : LinearIndependent R a) :
    LinearIndependent B.op (MulOpposite.op ∘ A.val ∘ a) := by
  have h := Submodule.LinearDisjoint.linearIndependent_left_of_flat H ha
  rwa [mulLeftMap_ker_eq_bot_iff_linearIndependent_op] at h

/-- If a basis of `A` is also `B`-linearly independent in the opposite ring,
then `A` and `B` are linearly disjoint. -/
theorem of_basis_left_op {ι : Type*} (a : Basis ι R A)
    (H : LinearIndependent B.op (MulOpposite.op ∘ A.val ∘ a)) :
    A.LinearDisjoint B := by
  rw [← mulLeftMap_ker_eq_bot_iff_linearIndependent_op] at H
  exact Submodule.LinearDisjoint.of_basis_left _ _ a H

lemma mulRightMap_ker_eq_bot_iff_linearIndependent {ι : Type*} (b : ι → B) :
    LinearMap.ker (Submodule.mulRightMap (toSubmodule A) (N := toSubmodule B) b) = ⊥ ↔
    LinearIndependent A (B.val ∘ b) := by
  -- need this instance otherwise `LinearMap.ker_eq_bot` does not work
  letI : AddCommGroup (ι →₀ toSubmodule A) := Finsupp.instAddCommGroup
  simp_rw [LinearIndependent, LinearMap.ker_eq_bot]
  let i : (ι →₀ A) →ₗ[R] S := Submodule.mulRightMap (toSubmodule A) (N := toSubmodule B) b
  let j : (ι →₀ A) →ₗ[R] S := (Finsupp.linearCombination A (B.val ∘ b)).restrictScalars R
  suffices i = j by change Function.Injective i ↔ Function.Injective j; rw [this]
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, coe_val,
    LinearMap.coe_restrictScalars, Finsupp.linearCombination_single, i, j]
  exact Submodule.mulRightMap_apply_single _ _ _

variable {A B} in
/-- If `A` and `B` are linearly disjoint, if `A` is a flat `R`-module, then for any family of
`R`-linearly independent elements of `B`, they are also `A`-linearly independent. -/
theorem linearIndependent_right_of_flat (H : A.LinearDisjoint B) [Module.Flat R A]
    {ι : Type*} {b : ι → B} (hb : LinearIndependent R b) :
    LinearIndependent A (B.val ∘ b) := by
  have h := Submodule.LinearDisjoint.linearIndependent_right_of_flat H hb
  rwa [mulRightMap_ker_eq_bot_iff_linearIndependent] at h

/-- If a basis of `B` is also `A`-linearly independent, then `A` and `B` are linearly disjoint. -/
theorem of_basis_right {ι : Type*} (b : Basis ι R B)
    (H : LinearIndependent A (B.val ∘ b)) : A.LinearDisjoint B := by
  rw [← mulRightMap_ker_eq_bot_iff_linearIndependent] at H
  exact Submodule.LinearDisjoint.of_basis_right _ _ b H

variable {A B} in
/-- If `A` and `B` are linearly disjoint and their elements commute, if `B` is a flat `R`-module,
then for any family of `R`-linearly independent elements of `A`,
they are also `B`-linearly independent. -/
theorem linearIndependent_left_of_flat_of_commute (H : A.LinearDisjoint B) [Module.Flat R B]
    {ι : Type*} {a : ι → A} (ha : LinearIndependent R a)
    (hc : ∀ (a : A) (b : B), Commute a.1 b.1) : LinearIndependent B (A.val ∘ a) :=
  (H.symm_of_commute hc).linearIndependent_right_of_flat ha

/-- If a basis of `A` is also `B`-linearly independent, if elements in `A` and `B` commute,
then `A` and `B` are linearly disjoint. -/
theorem of_basis_left_of_commute {ι : Type*} (a : Basis ι R A)
    (H : LinearIndependent B (A.val ∘ a)) (hc : ∀ (a : A) (b : B), Commute a.1 b.1) :
    A.LinearDisjoint B :=
  (of_basis_right B A a H).symm_of_commute fun _ _ ↦ (hc _ _).symm

variable {A B} in
/-- If `A` and `B` are linearly disjoint, if `A` is flat, then for any family of
`R`-linearly independent elements `{ a_i }` of `A`, and any family of
`R`-linearly independent elements `{ b_j }` of `B`, the family `{ a_i * b_j }` in `S` is
also `R`-linearly independent. -/
theorem linearIndependent_mul_of_flat_left (H : A.LinearDisjoint B) [Module.Flat R A]
    {κ ι : Type*} {a : κ → A} {b : ι → B} (ha : LinearIndependent R a)
    (hb : LinearIndependent R b) : LinearIndependent R fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1 :=
  Submodule.LinearDisjoint.linearIndependent_mul_of_flat_left H ha hb

variable {A B} in
/-- If `A` and `B` are linearly disjoint, if `B` is flat, then for any family of
`R`-linearly independent elements `{ a_i }` of `A`, and any family of
`R`-linearly independent elements `{ b_j }` of `B`, the family `{ a_i * b_j }` in `S` is
also `R`-linearly independent. -/
theorem linearIndependent_mul_of_flat_right (H : A.LinearDisjoint B) [Module.Flat R B]
    {κ ι : Type*} {a : κ → A} {b : ι → B} (ha : LinearIndependent R a)
    (hb : LinearIndependent R b) : LinearIndependent R fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1 :=
  Submodule.LinearDisjoint.linearIndependent_mul_of_flat_right H ha hb

variable {A B} in
/-- If `A` and `B` are linearly disjoint, if one of `A` and `B` is flat, then for any family of
`R`-linearly independent elements `{ a_i }` of `A`, and any family of
`R`-linearly independent elements `{ b_j }` of `B`, the family `{ a_i * b_j }` in `S` is
also `R`-linearly independent. -/
theorem linearIndependent_mul_of_flat (H : A.LinearDisjoint B)
    (hf : Module.Flat R A ∨ Module.Flat R B)
    {κ ι : Type*} {a : κ → A} {b : ι → B} (ha : LinearIndependent R a)
    (hb : LinearIndependent R b) : LinearIndependent R fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1 :=
  Submodule.LinearDisjoint.linearIndependent_mul_of_flat H hf ha hb

/-- If `{ a_i }` is an `R`-basis of `A`, if `{ b_j }` is an `R`-basis of `B`,
such that the family `{ a_i * b_j }` in `S` is `R`-linearly independent,
then `A` and `B` are linearly disjoint. -/
theorem of_basis_mul {κ ι : Type*} (a : Basis κ R A) (b : Basis ι R B)
    (H : LinearIndependent R fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1) : A.LinearDisjoint B :=
  Submodule.LinearDisjoint.of_basis_mul _ _ a b H

variable {A B}

section

variable (H : A.LinearDisjoint B)
include H

theorem of_le_left_of_flat {A' : Subalgebra R S}
    (h : A' ≤ A) [Module.Flat R B] : A'.LinearDisjoint B :=
  Submodule.LinearDisjoint.of_le_left_of_flat H h

theorem of_le_right_of_flat {B' : Subalgebra R S}
    (h : B' ≤ B) [Module.Flat R A] : A.LinearDisjoint B' :=
  Submodule.LinearDisjoint.of_le_right_of_flat H h

theorem of_le_of_flat_right {A' B' : Subalgebra R S}
    (ha : A' ≤ A) (hb : B' ≤ B) [Module.Flat R B] [Module.Flat R A'] :
    A'.LinearDisjoint B' := (H.of_le_left_of_flat ha).of_le_right_of_flat hb

theorem of_le_of_flat_left {A' B' : Subalgebra R S}
    (ha : A' ≤ A) (hb : B' ≤ B) [Module.Flat R A] [Module.Flat R B'] :
    A'.LinearDisjoint B' := (H.of_le_right_of_flat hb).of_le_left_of_flat ha

end

end LinearDisjoint

end Ring

section CommRing

namespace LinearDisjoint

variable [CommRing R] [CommRing S] [Algebra R S]

variable (A B : Subalgebra R S)

variable {A B} in
/-- In a commutative ring, if `A` and `B` are linearly disjoint, if `B` is a flat `R`-module,
then for any family of `R`-linearly independent elements of `A`,
they are also `B`-linearly independent. -/
theorem linearIndependent_left_of_flat (H : A.LinearDisjoint B) [Module.Flat R B]
    {ι : Type*} {a : ι → A} (ha : LinearIndependent R a) : LinearIndependent B (A.val ∘ a) :=
  H.linearIndependent_left_of_flat_of_commute ha fun _ _ ↦ mul_comm _ _

/-- In a commutative ring, if a basis of `A` is also `B`-linearly independent,
then `A` and `B` are linearly disjoint. -/
theorem of_basis_left {ι : Type*} (a : Basis ι R A)
    (H : LinearIndependent B (A.val ∘ a)) : A.LinearDisjoint B :=
  of_basis_left_of_commute A B a H fun _ _ ↦ mul_comm _ _

/-- If `A/R` is integral, such that `A'` and `B` are linearly disjoint for all subalgebras `A'`
of `A` which are finitely generated `R`-modules, then `A` and `B` are linearly disjoint. -/
theorem of_linearDisjoint_finite_left [Algebra.IsIntegral R A]
    (H : ∀ A' : Subalgebra R S, A' ≤ A → [Module.Finite R A'] → A'.LinearDisjoint B) :
    A.LinearDisjoint B := by
  rw [linearDisjoint_iff, Submodule.linearDisjoint_iff]
  intro x y hxy
  obtain ⟨M', hM, hf, h⟩ :=
    TensorProduct.exists_finite_submodule_left_of_finite' {x, y} (Set.toFinite _)
  obtain ⟨s, hs⟩ := Module.Finite.iff_fg.1 hf
  have hs' : (s : Set S) ⊆ A := by rwa [← hs, Submodule.span_le] at hM
  let A' := Algebra.adjoin R (s : Set S)
  have hf' : Submodule.FG (toSubmodule A') := fg_adjoin_of_finite s.finite_toSet fun x hx ↦
    (isIntegral_algHom_iff A.val Subtype.val_injective).2
      (Algebra.IsIntegral.isIntegral (R := R) (A := A) ⟨x, hs' hx⟩)
  replace hf' : Module.Finite R A' := Module.Finite.iff_fg.2 hf'
  have hA : toSubmodule A' ≤ toSubmodule A := Algebra.adjoin_le_iff.2 hs'
  replace h : {x, y} ⊆ (LinearMap.range (LinearMap.rTensor (toSubmodule B)
      (Submodule.inclusion hA)) : Set _) := fun _ hx ↦ by
    have : Submodule.inclusion hM = Submodule.inclusion hA ∘ₗ Submodule.inclusion
      (show M' ≤ toSubmodule A' by
        rw [← hs, Submodule.span_le]; exact Algebra.adjoin_le_iff.1 (le_refl _)) := rfl
    rw [this, LinearMap.rTensor_comp] at h
    exact LinearMap.range_comp_le_range _ _ (h hx)
  obtain ⟨x', hx'⟩ := h (show x ∈ {x, y} by simp)
  obtain ⟨y', hy'⟩ := h (show y ∈ {x, y} by simp)
  rw [← hx', ← hy']; congr
  exact (H A' hA).injective (by simp [← Submodule.mulMap_comp_rTensor _ hA, hx', hy', hxy])

/-- If `B/R` is integral, such that `A` and `B'` are linearly disjoint for all subalgebras `B'`
of `B` which are finitely generated `R`-modules, then `A` and `B` are linearly disjoint. -/
theorem of_linearDisjoint_finite_right [Algebra.IsIntegral R B]
    (H : ∀ B' : Subalgebra R S, B' ≤ B → [Module.Finite R B'] → A.LinearDisjoint B') :
    A.LinearDisjoint B :=
  (of_linearDisjoint_finite_left B A fun B' hB' _ ↦ (H B' hB').symm).symm

variable {A B}

/-- If `A/R` and `B/R` are integral, such that any finite subalgebras in `A` and `B` are
linearly disjoint, then `A` and `B` are linearly disjoint. -/
theorem of_linearDisjoint_finite
    [Algebra.IsIntegral R A] [Algebra.IsIntegral R B]
    (H : ∀ (A' B' : Subalgebra R S), A' ≤ A → B' ≤ B →
      [Module.Finite R A'] → [Module.Finite R B'] → A'.LinearDisjoint B') :
    A.LinearDisjoint B :=
  of_linearDisjoint_finite_left A B fun _ hA' _ ↦
    of_linearDisjoint_finite_right _ B fun _ hB' _ ↦ H _ _ hA' hB'

end LinearDisjoint

end CommRing

section FieldAndRing

namespace LinearDisjoint

variable [Field R] [Ring S] [Algebra R S]

variable {A B : Subalgebra R S}

theorem inf_eq_bot_of_commute (H : A.LinearDisjoint B)
    (hc : ∀ (a b : ↥(A ⊓ B)), Commute a.1 b.1) : A ⊓ B = ⊥ :=
  eq_bot_of_rank_le_one (Submodule.LinearDisjoint.rank_inf_le_one_of_commute_of_flat_left H hc)

theorem eq_bot_of_commute_of_self (H : A.LinearDisjoint A)
    (hc : ∀ (a b : A), Commute a.1 b.1) : A = ⊥ := by
  rw [← inf_of_le_left (le_refl A)] at hc ⊢
  exact H.inf_eq_bot_of_commute hc

end LinearDisjoint

end FieldAndRing

section FieldAndCommRing

namespace LinearDisjoint

variable [Field R] [CommRing S] [Algebra R S]

variable {A B : Subalgebra R S}

theorem inf_eq_bot (H : A.LinearDisjoint B) : A ⊓ B = ⊥ :=
  H.inf_eq_bot_of_commute fun _ _ ↦ mul_comm _ _

theorem eq_bot_of_self (H : A.LinearDisjoint A) : A = ⊥ :=
  H.eq_bot_of_commute_of_self fun _ _ ↦ mul_comm _ _

end LinearDisjoint

end FieldAndCommRing

end Subalgebra
