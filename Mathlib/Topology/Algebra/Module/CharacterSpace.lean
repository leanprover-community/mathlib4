/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis

! This file was ported from Lean 3 source module topology.algebra.module.character_space
! leanprover-community/mathlib commit a148d797a1094ab554ad4183a4ad6f130358ef64
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Algebra.Algebra.Spectrum
import Mathlib.Topology.ContinuousFunction.Algebra

/-!
# Character space of a topological algebra

The character space of a topological algebra is the subset of elements of the weak dual that
are also algebra homomorphisms. This space is used in the Gelfand transform, which gives an
isomorphism between a commutative C⋆-algebra and continuous functions on the character space
of the algebra. This, in turn, is used to construct the continuous functional calculus on
C⋆-algebras.


## Implementation notes

We define `character_space 𝕜 A` as a subset of the weak dual, which automatically puts the
correct topology on the space. We then define `to_alg_hom` which provides the algebra homomorphism
corresponding to any element. We also provide `to_clm` which provides the element as a
continuous linear map. (Even though `weak_dual 𝕜 A` is a type copy of `A →L[𝕜] 𝕜`, this is
often more convenient.)

## Tags

character space, Gelfand transform, functional calculus

-/


namespace WeakDual

/-- The character space of a topological algebra is the subset of elements of the weak dual that
are also algebra homomorphisms. -/
def characterSpace (𝕜 : Type _) (A : Type _) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
    [ContinuousConstSMul 𝕜 𝕜] [NonUnitalNonAssocSemiring A] [TopologicalSpace A] [Module 𝕜 A] :=
  {φ : WeakDual 𝕜 A | φ ≠ 0 ∧ ∀ x y : A, φ (x * y) = φ x * φ y}
#align weak_dual.character_space WeakDual.characterSpace

variable {𝕜 : Type _} {A : Type _}

namespace CharacterSpace

section NonUnitalNonAssocSemiring

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]
  [NonUnitalNonAssocSemiring A] [TopologicalSpace A] [Module 𝕜 A]

@[simp, norm_cast, protected]
theorem coe_coe (φ : characterSpace 𝕜 A) : ⇑(φ : WeakDual 𝕜 A) = φ :=
  rfl
#align weak_dual.character_space.coe_coe WeakDual.characterSpace.coe_coe

/-- Elements of the character space are continuous linear maps. -/
instance : ContinuousLinearMapClass (characterSpace 𝕜 A) 𝕜 A 𝕜 where
  coe φ := (φ : A → 𝕜)
  coe_injective' φ ψ h := by ext; exact congr_fun h x
  map_smulₛₗ φ := (φ : WeakDual 𝕜 A).map_smul
  map_add φ := (φ : WeakDual 𝕜 A).map_add
  map_continuous φ := (φ : WeakDual 𝕜 A).cont

@[ext]
theorem ext {φ ψ : characterSpace 𝕜 A} (h : ∀ x, φ x = ψ x) : φ = ψ :=
  FunLike.ext _ _ h
#align weak_dual.character_space.ext WeakDual.characterSpace.ext

/-- An element of the character space, as a continuous linear map. -/
def toClm (φ : characterSpace 𝕜 A) : A →L[𝕜] 𝕜 :=
  (φ : WeakDual 𝕜 A)
#align weak_dual.character_space.to_clm WeakDual.characterSpace.toClm

@[simp]
theorem coe_toClm (φ : characterSpace 𝕜 A) : ⇑(toClm φ) = φ :=
  rfl
#align weak_dual.character_space.coe_to_clm WeakDual.characterSpace.coe_toClm

/-- Elements of the character space are non-unital algebra homomorphisms. -/
instance : NonUnitalAlgHomClass (characterSpace 𝕜 A) 𝕜 A 𝕜 :=
  {
    characterSpace.continuousLinearMapClass with
    map_smul := fun φ => map_smul φ
    map_zero := fun φ => map_zero φ
    map_mul := fun φ => φ.Prop.2 }

/-- An element of the character space, as an non-unital algebra homomorphism. -/
def toNonUnitalAlgHom (φ : characterSpace 𝕜 A) : A →ₙₐ[𝕜] 𝕜 where
  toFun := (φ : A → 𝕜)
  map_mul' := map_mul φ
  map_smul' := map_smul φ
  map_zero' := map_zero φ
  map_add' := map_add φ
#align weak_dual.character_space.to_non_unital_alg_hom WeakDual.characterSpace.toNonUnitalAlgHom

@[simp]
theorem coe_toNonUnitalAlgHom (φ : characterSpace 𝕜 A) : ⇑(toNonUnitalAlgHom φ) = φ :=
  rfl
#align weak_dual.character_space.coe_to_non_unital_alg_hom WeakDual.characterSpace.coe_toNonUnitalAlgHom

instance [Subsingleton A] : IsEmpty (characterSpace 𝕜 A) :=
  ⟨fun φ =>
    φ.Prop.1 <| ContinuousLinearMap.ext fun x => by simp only [Subsingleton.elim x 0, map_zero]⟩

variable (𝕜 A)

theorem union_zero :
    characterSpace 𝕜 A ∪ {0} = {φ : WeakDual 𝕜 A | ∀ x y : A, φ (x * y) = φ x * φ y} :=
  le_antisymm
    (by rintro φ (hφ | h₀); · exact hφ.2; · exact fun x y => by simp [Set.eq_of_mem_singleton h₀])
    fun φ hφ => Or.elim (em <| φ = 0) (fun h₀ => Or.inr h₀) fun h₀ => Or.inl ⟨h₀, hφ⟩
#align weak_dual.character_space.union_zero WeakDual.characterSpace.union_zero

/-- The `character_space 𝕜 A` along with `0` is always a closed set in `weak_dual 𝕜 A`. -/
theorem union_zero_isClosed [T2Space 𝕜] [ContinuousMul 𝕜] : IsClosed (characterSpace 𝕜 A ∪ {0}) :=
  by
  simp only [union_zero, Set.setOf_forall]
  exact
    isClosed_iInter fun x =>
      isClosed_iInter fun y =>
        isClosed_eq (eval_continuous _) <| (eval_continuous _).mul (eval_continuous _)
#align weak_dual.character_space.union_zero_is_closed WeakDual.characterSpace.union_zero_isClosed

end NonUnitalNonAssocSemiring

section Unital

variable [CommRing 𝕜] [NoZeroDivisors 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [TopologicalSpace A] [Semiring A] [Algebra 𝕜 A]

/-- In a unital algebra, elements of the character space are algebra homomorphisms. -/
instance : AlgHomClass (characterSpace 𝕜 A) 𝕜 A 𝕜 :=
  have map_one' : ∀ φ : characterSpace 𝕜 A, φ 1 = 1 := fun φ => by
    have h₁ : φ 1 * (1 - φ 1) = 0 := by rw [mul_sub, sub_eq_zero, mul_one, ← map_mul φ, one_mul]
    rcases mul_eq_zero.mp h₁ with (h₂ | h₂)
    · have : ∀ a, φ (a * 1) = 0 := fun a => by simp only [map_mul φ, h₂, MulZeroClass.mul_zero]
      exact False.elim (φ.prop.1 <| ContinuousLinearMap.ext <| by simpa only [mul_one] using this)
    · exact (sub_eq_zero.mp h₂).symm
  {
    characterSpace.nonUnitalAlgHomClass with
    map_one := map_one'
    commutes := fun φ r => by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.id.map_eq_id, RingHom.id_apply]
      change ((φ : WeakDual 𝕜 A) : A →L[𝕜] 𝕜) (r • 1) = r
      rw [map_smul, Algebra.id.smul_eq_mul, character_space.coe_coe, map_one' φ, mul_one] }

/-- An element of the character space of a unital algebra, as an algebra homomorphism. -/
@[simps]
def toAlgHom (φ : characterSpace 𝕜 A) : A →ₐ[𝕜] 𝕜 :=
  { toNonUnitalAlgHom φ with
    map_one' := map_one φ
    commutes' := AlgHomClass.commutes φ }
#align weak_dual.character_space.to_alg_hom WeakDual.characterSpace.toAlgHom

theorem eq_set_map_one_map_mul [Nontrivial 𝕜] :
    characterSpace 𝕜 A = {φ : WeakDual 𝕜 A | φ 1 = 1 ∧ ∀ x y : A, φ (x * y) = φ x * φ y} := by
  ext x
  refine' ⟨fun h => ⟨map_one (⟨x, h⟩ : character_space 𝕜 A), h.2⟩, fun h => ⟨_, h.2⟩⟩
  rintro rfl
  simpa using h.1
#align weak_dual.character_space.eq_set_map_one_map_mul WeakDual.characterSpace.eq_set_map_one_map_mul

/-- under suitable mild assumptions on `𝕜`, the character space is a closed set in
`weak_dual 𝕜 A`. -/
protected theorem isClosed [Nontrivial 𝕜] [T2Space 𝕜] [ContinuousMul 𝕜] :
    IsClosed (characterSpace 𝕜 A) := by
  rw [eq_set_map_one_map_mul, Set.setOf_and]
  refine' IsClosed.inter (isClosed_eq (eval_continuous _) continuous_const) _
  simpa only [(union_zero 𝕜 A).symm] using union_zero_is_closed _ _
#align weak_dual.character_space.is_closed WeakDual.characterSpace.isClosed

end Unital

section Ring

variable [CommRing 𝕜] [NoZeroDivisors 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [TopologicalSpace A] [Ring A] [Algebra 𝕜 A]

theorem apply_mem_spectrum [Nontrivial 𝕜] (φ : characterSpace 𝕜 A) (a : A) : φ a ∈ spectrum 𝕜 a :=
  AlgHom.apply_mem_spectrum φ a
#align weak_dual.character_space.apply_mem_spectrum WeakDual.characterSpace.apply_mem_spectrum

theorem ext_ker {φ ψ : characterSpace 𝕜 A} (h : RingHom.ker φ = RingHom.ker ψ) : φ = ψ := by
  ext
  have : x - algebraMap 𝕜 A (ψ x) ∈ RingHom.ker φ := by
    simpa only [h, RingHom.mem_ker, map_sub, AlgHomClass.commutes] using sub_self (ψ x)
  · rwa [RingHom.mem_ker, map_sub, AlgHomClass.commutes, sub_eq_zero] at this 
#align weak_dual.character_space.ext_ker WeakDual.characterSpace.ext_ker

end Ring

end CharacterSpace

section Kernel

variable [Field 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]

variable [Ring A] [TopologicalSpace A] [Algebra 𝕜 A]

/-- The `ring_hom.ker` of `φ : character_space 𝕜 A` is maximal. -/
instance ker_isMaximal (φ : characterSpace 𝕜 A) : (RingHom.ker φ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective φ fun z =>
    ⟨algebraMap 𝕜 A z, by simp only [AlgHomClass.commutes, Algebra.id.map_eq_id, RingHom.id_apply]⟩
#align weak_dual.ker_is_maximal WeakDual.ker_isMaximal

end Kernel

section GelfandTransform

open ContinuousMap

variable (𝕜 A) [CommRing 𝕜] [NoZeroDivisors 𝕜] [TopologicalSpace 𝕜] [TopologicalRing 𝕜]
  [TopologicalSpace A] [Semiring A] [Algebra 𝕜 A]

/-- The **Gelfand transform** is an algebra homomorphism (over `𝕜`) from a topological `𝕜`-algebra
`A` into the `𝕜`-algebra of continuous `𝕜`-valued functions on the `character_space 𝕜 A`.
The character space itself consists of all algebra homomorphisms from `A` to `𝕜`.  -/
@[simps]
def gelfandTransform : A →ₐ[𝕜] C(characterSpace 𝕜 A, 𝕜) where
  toFun a :=
    { toFun := fun φ => φ a
      continuous_toFun := (eval_continuous a).comp continuous_induced_dom }
  map_one' := by ext; simp only [coe_mk, coe_one, Pi.one_apply, map_one a]
  map_mul' a b := by ext; simp only [map_mul, coe_mk, coe_mul, Pi.mul_apply]
  map_zero' := by ext; simp only [map_zero, coe_mk, coe_mul, coe_zero, Pi.zero_apply]
  map_add' a b := by ext; simp only [map_add, coe_mk, coe_add, Pi.add_apply]
  commutes' k := by ext;
    simp only [AlgHomClass.commutes, Algebra.id.map_eq_id, RingHom.id_apply, coe_mk,
      algebraMap_apply, Algebra.id.smul_eq_mul, mul_one]
#align weak_dual.gelfand_transform WeakDual.gelfandTransform

end GelfandTransform

end WeakDual

