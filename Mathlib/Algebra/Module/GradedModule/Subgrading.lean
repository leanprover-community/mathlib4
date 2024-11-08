/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
import Mathlib.Algebra.Module.GradedModule.Basic

/-!
# Homogeneous Submodule of Graded Module is a Graded Module

-/

open SetLike DirectSum

variable {ιA ιM σA σM A M : Type*}

variable [Semiring A] [AddCommMonoid M] [Module A M]

variable {𝒜 : ιA → σA} {ℳ : ιM → σM}
variable [DecidableEq ιA] [AddMonoid ιA] [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]
variable [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
variable [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]

namespace HomogeneousSubmodule

variable [(i : ιM) → (x : ℳ i) → Decidable (x ≠ 0)]

variable (p : HomogeneousSubmodule 𝒜 ℳ)

/--
If `A` is a graded ring and `M` a graded module over `A`. Let `p` a homogeneous submodule of `M`,
then `p` is a graded module over `A` as well whose degree `i` part is `Mᵢ ∩ p`.
-/
def subgrading (i : ιM) : AddSubmonoid p where
  carrier := { x | (x : M) ∈ ℳ i }
  add_mem' := AddMemClass.add_mem
  zero_mem' := ZeroMemClass.zero_mem _

/--
`p ≃ ⨁ᵢ p ∩ Mᵢ` is defined by `x ↦ i ↦ xᵢ`. This is well-defined because `p` is homogeneous.
-/
def subgradingDecompose
    (a : p) : ⨁ i, p.subgrading i :=
  ∑ i in (decompose ℳ a).support,
    .of _ (i : ιM) ⟨⟨decompose ℳ a i, p.2 i a.2⟩, SetLike.coe_mem _⟩

lemma subgradingDecompose_zero : p.subgradingDecompose 0 = 0 := by
  simp [subgradingDecompose]

lemma subgradingDecompose_apply (a : p) (j : ιM) :
    (p.subgradingDecompose a j : M) = decompose ℳ a j := by
  delta subgradingDecompose
  erw [DFinsupp.finset_sum_apply, AddSubmonoidClass.coe_finset_sum,
        AddSubmonoidClass.coe_finset_sum]
  simp_rw [DirectSum.coe_of_apply]
  calc _
    _ = (∑ i ∈ (decompose ℳ (a : M)).support,
          if i = j then decompose ℳ (a : M) i else 0 : M) :=
        Finset.sum_congr rfl fun _ _ ↦ by split_ifs <;> rfl
  aesop

lemma subgradingDecompose_add (a b : p) :
    p.subgradingDecompose (a + b) =
    p.subgradingDecompose a + p.subgradingDecompose b := by
  refine DFinsupp.ext fun i ↦ ?_
  ext
  simp only [subgradingDecompose_apply, Subsemiring.coe_add, Subring.coe_toSubsemiring,
    DirectSum.decompose_add, add_apply, AddMemClass.coe_add, AddSubmonoid.coe_add]

lemma subgradingDecompose_leftInverse :
    Function.LeftInverse
      (DirectSum.coeAddMonoidHom p.subgrading) p.subgradingDecompose :=
  fun a ↦ Subtype.ext <| show p.subtype _ = _ by
  classical
  simp only [subgradingDecompose, map_sum, coeAddMonoidHom_of, Submodule.coe_subtype]
  conv_rhs => rw [← sum_support_decompose ℳ a.1]

lemma subgradingDecompose_rightInverse :
    Function.RightInverse (DirectSum.coeAddMonoidHom p.subgrading) p.subgradingDecompose := by
  intro a
  refine DFinsupp.ext fun i ↦ ?_
  ext
  rw [subgradingDecompose_apply]
  induction' a using DirectSum.induction_on with j x x y hx hy
  · simp only [map_zero, ZeroMemClass.coe_zero, DirectSum.decompose_zero, zero_apply]
  · simp only [coeAddMonoidHom_of]
    erw [DirectSum.decompose_coe (ℳ := ℳ) (i := j) ⟨x.1.1, x.2⟩]
    by_cases h : i = j
    · subst h; simp only [of_eq_same]
    · rw [of_eq_of_ne, of_eq_of_ne] <;> aesop
  · simp [map_add, DirectSum.add_apply, hx, hy]

instance subgrading.decomposition : Decomposition p.subgrading where
  decompose' := p.subgradingDecompose
  left_inv := p.subgradingDecompose_leftInverse
  right_inv := p.subgradingDecompose_rightInverse

instance subgrading.gradedSMul : GradedSMul 𝒜 p.subgrading where
  smul_mem _ _ _ _ ha hm := (inferInstance : SetLike.GradedSMul 𝒜 ℳ).smul_mem ha hm

end HomogeneousSubmodule
