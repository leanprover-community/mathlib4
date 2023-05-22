/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang

! This file was ported from Lean 3 source module algebra.module.graded_module
! leanprover-community/mathlib commit 59cdeb0da2480abbc235b7e611ccd9a7e5603d7c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.GradedAlgebra.Basic
import Mathbin.Algebra.GradedMulAction
import Mathbin.Algebra.DirectSum.Decomposition
import Mathbin.Algebra.Module.BigOperators

/-!
# Graded Module

Given an `R`-algebra `A` graded by `𝓐`, a graded `A`-module `M` is expressed as
`direct_sum.decomposition 𝓜` and `set_like.has_graded_smul 𝓐 𝓜`.
Then `⨁ i, 𝓜 i` is an `A`-module and is isomorphic to `M`.

## Tags

graded module
-/


section

open DirectSum

variable {ι : Type _} (A : ι → Type _) (M : ι → Type _)

namespace DirectSum

open GradedMonoid

/-- A graded version of `distrib_mul_action`. -/
class GdistribMulAction [AddMonoid ι] [GMonoid A] [∀ i, AddMonoid (M i)] extends
  GMulAction A M where
  smul_add {i j} (a : A i) (b c : M j) : smul a (b + c) = smul a b + smul a c
  smul_zero {i j} (a : A i) : smul a (0 : M j) = 0
#align direct_sum.gdistrib_mul_action DirectSum.GdistribMulAction

/-- A graded version of `module`. -/
class Gmodule [AddMonoid ι] [∀ i, AddMonoid (A i)] [∀ i, AddMonoid (M i)] [GMonoid A] extends
  GdistribMulAction A M where
  add_smul {i j} (a a' : A i) (b : M j) : smul (a + a') b = smul a b + smul a' b
  zero_smul {i j} (b : M j) : smul (0 : A i) b = 0
#align direct_sum.gmodule DirectSum.Gmodule

/-- A graded version of `semiring.to_module`. -/
instance GSemiring.toGmodule [DecidableEq ι] [AddMonoid ι] [∀ i : ι, AddCommMonoid (A i)]
    [GSemiring A] : Gmodule A A :=
  { GMonoid.toGMulAction A with
    smul_add := fun _ _ => GSemiring.mul_add
    smul_zero := fun i j => GSemiring.mul_zero
    add_smul := fun i j => GSemiring.add_mul
    zero_smul := fun i j => GSemiring.zero_mul }
#align direct_sum.gsemiring.to_gmodule DirectSum.GSemiring.toGmodule

variable [AddMonoid ι] [∀ i : ι, AddCommMonoid (A i)] [∀ i, AddCommMonoid (M i)]

/-- The piecewise multiplication from the `has_mul` instance, as a bundled homomorphism. -/
@[simps]
def gsmulHom [GMonoid A] [Gmodule A M] {i j} : A i →+ M j →+ M (i + j)
    where
  toFun a :=
    { toFun := fun b => GSmul.smul a b
      map_zero' := GdistribMulAction.smul_zero _
      map_add' := GdistribMulAction.smul_add _ }
  map_zero' := AddMonoidHom.ext fun a => Gmodule.zero_smul a
  map_add' a₁ a₂ := AddMonoidHom.ext fun b => Gmodule.add_smul _ _ _
#align direct_sum.gsmul_hom DirectSum.gsmulHom

namespace Gmodule

/-- For graded monoid `A` and a graded module `M` over `A`. `gmodule.smul_add_monoid_hom` is the
`⨁ᵢ Aᵢ`-scalar multiplication on `⨁ᵢ Mᵢ` induced by `gsmul_hom`. -/
def smulAddMonoidHom [DecidableEq ι] [GMonoid A] [Gmodule A M] :
    (⨁ i, A i) →+ (⨁ i, M i) →+ ⨁ i, M i :=
  toAddMonoid fun i =>
    AddMonoidHom.flip <|
      toAddMonoid fun j => AddMonoidHom.flip <| (of M _).compHom.comp <| gsmulHom A M
#align direct_sum.gmodule.smul_add_monoid_hom DirectSum.Gmodule.smulAddMonoidHom

section

open GradedMonoid DirectSum Gmodule

instance [DecidableEq ι] [GMonoid A] [Gmodule A M] : SMul (⨁ i, A i) (⨁ i, M i)
    where smul x y := smulAddMonoidHom A M x y

@[simp]
theorem smul_def [DecidableEq ι] [GMonoid A] [Gmodule A M] (x : ⨁ i, A i) (y : ⨁ i, M i) :
    x • y = smulAddMonoidHom _ _ x y :=
  rfl
#align direct_sum.gmodule.smul_def DirectSum.Gmodule.smul_def

@[simp]
theorem smulAddMonoidHom_apply_of_of [DecidableEq ι] [GMonoid A] [Gmodule A M] {i j} (x : A i)
    (y : M j) :
    smulAddMonoidHom A M (DirectSum.of A i x) (of M j y) = of M (i + j) (GSmul.smul x y) := by
  simp [smul_add_monoid_hom]
#align direct_sum.gmodule.smul_add_monoid_hom_apply_of_of DirectSum.Gmodule.smulAddMonoidHom_apply_of_of

@[simp]
theorem of_smul_of [DecidableEq ι] [GMonoid A] [Gmodule A M] {i j} (x : A i) (y : M j) :
    DirectSum.of A i x • of M j y = of M (i + j) (GSmul.smul x y) :=
  smulAddMonoidHom_apply_of_of _ _ _ _
#align direct_sum.gmodule.of_smul_of DirectSum.Gmodule.of_smul_of

open AddMonoidHom

-- Almost identical to the proof of `direct_sum.one_mul`
private theorem one_smul [DecidableEq ι] [GMonoid A] [Gmodule A M] (x : ⨁ i, M i) :
    (1 : ⨁ i, A i) • x = x :=
  by
  suffices smulAddMonoidHom A M 1 = AddMonoidHom.id (⨁ i, M i) from AddMonoidHom.congr_fun this x
  apply DirectSum.addHom_ext; intro i xi
  unfold One.one
  rw [smul_add_monoid_hom_apply_of_of]
  exact DirectSum.of_eq_of_gradedMonoid_eq (one_smul (GradedMonoid A) <| GradedMonoid.mk i xi)
#align direct_sum.gmodule.one_smul direct_sum.gmodule.one_smul

-- Almost identical to the proof of `direct_sum.mul_assoc`
private theorem mul_smul [DecidableEq ι] [GSemiring A] [Gmodule A M] (a b : ⨁ i, A i)
    (c : ⨁ i, M i) : (a * b) • c = a • b • c :=
  by
  suffices
    (-- `λ a b c, (a * b) • c` as a bundled hom
              smulAddMonoidHom
              A M).compHom.comp
        (DirectSum.mulHom A) =
      (AddMonoidHom.compHom AddMonoidHom.flipHom <|
          (smulAddMonoidHom A M).flip.compHom.comp <| smulAddMonoidHom A M).flip
    from-- `λ a b c, a • (b • c)` as a bundled hom
      AddMonoidHom.congr_fun
      (AddMonoidHom.congr_fun (AddMonoidHom.congr_fun this a) b) c
  ext (ai ax bi bx ci cx) : 6
  dsimp only [coe_comp, Function.comp_apply, comp_hom_apply_apply, flip_apply, flip_hom_apply]
  rw [smul_add_monoid_hom_apply_of_of, smul_add_monoid_hom_apply_of_of, DirectSum.mulHom_of_of,
    smul_add_monoid_hom_apply_of_of]
  exact
    DirectSum.of_eq_of_gradedMonoid_eq
      (mul_smul (GradedMonoid.mk ai ax) (GradedMonoid.mk bi bx) (GradedMonoid.mk ci cx))
#align direct_sum.gmodule.mul_smul direct_sum.gmodule.mul_smul

/-- The `module` derived from `gmodule A M`. -/
instance module [DecidableEq ι] [GSemiring A] [Gmodule A M] : Module (⨁ i, A i) (⨁ i, M i)
    where
  smul := (· • ·)
  one_smul := one_smul _ _
  mul_smul := mul_smul _ _
  smul_add r := (smulAddMonoidHom A M r).map_add
  smul_zero r := (smulAddMonoidHom A M r).map_zero
  add_smul r s x := by simp only [smul_def, map_add, AddMonoidHom.add_apply]
  zero_smul x := by simp only [smul_def, map_zero, AddMonoidHom.zero_apply]
#align direct_sum.gmodule.module DirectSum.Gmodule.module

end

end Gmodule

end DirectSum

end

open DirectSum BigOperators

variable {ι R A M σ σ' : Type _}

variable [AddMonoid ι] [CommSemiring R] [Semiring A] [Algebra R A]

variable (𝓐 : ι → σ') [SetLike σ' A]

variable (𝓜 : ι → σ)

namespace SetLike

include σ' A σ M

instance gmulAction [AddMonoid M] [DistribMulAction A M] [SetLike σ M] [SetLike.GradedMonoid 𝓐]
    [SetLike.GradedSmul 𝓐 𝓜] : GradedMonoid.GMulAction (fun i => 𝓐 i) fun i => 𝓜 i :=
  {
    SetLike.toGSmul 𝓐
      𝓜 with
    one_smul := fun ⟨i, m⟩ => Sigma.subtype_ext (zero_add _) (one_smul _ _)
    mul_smul := fun ⟨i, a⟩ ⟨j, a'⟩ ⟨k, b⟩ => Sigma.subtype_ext (add_assoc _ _ _) (mul_smul _ _ _) }
#align set_like.gmul_action SetLike.gmulAction

instance gdistribMulAction [AddMonoid M] [DistribMulAction A M] [SetLike σ M]
    [AddSubmonoidClass σ M] [SetLike.GradedMonoid 𝓐] [SetLike.GradedSmul 𝓐 𝓜] :
    DirectSum.GdistribMulAction (fun i => 𝓐 i) fun i => 𝓜 i :=
  {
    SetLike.gmulAction 𝓐
      𝓜 with
    smul_add := fun i j a b c => Subtype.ext <| smul_add _ _ _
    smul_zero := fun i j a => Subtype.ext <| smul_zero _ }
#align set_like.gdistrib_mul_action SetLike.gdistribMulAction

variable [AddCommMonoid M] [Module A M] [SetLike σ M] [AddSubmonoidClass σ' A]
  [AddSubmonoidClass σ M] [SetLike.GradedMonoid 𝓐] [SetLike.GradedSmul 𝓐 𝓜]

/-- `[set_like.graded_monoid 𝓐] [set_like.has_graded_smul 𝓐 𝓜]` is the internal version of graded
  module, the internal version can be translated into the external version `gmodule`. -/
instance gmodule : DirectSum.Gmodule (fun i => 𝓐 i) fun i => 𝓜 i :=
  {
    SetLike.gdistribMulAction 𝓐
      𝓜 with
    smul := fun i j x y => ⟨(x : A) • (y : M), SetLike.GradedSmul.smul_mem x.2 y.2⟩
    add_smul := fun i j a a' b => Subtype.ext <| add_smul _ _ _
    zero_smul := fun i j b => Subtype.ext <| zero_smul _ _ }
#align set_like.gmodule SetLike.gmodule

end SetLike

namespace GradedModule

include σ' A σ M

variable [AddCommMonoid M] [Module A M] [SetLike σ M] [AddSubmonoidClass σ' A]
  [AddSubmonoidClass σ M] [SetLike.GradedMonoid 𝓐] [SetLike.GradedSmul 𝓐 𝓜]

/-- The smul multiplication of `A` on `⨁ i, 𝓜 i` from `(⨁ i, 𝓐 i) →+ (⨁ i, 𝓜 i) →+ ⨁ i, 𝓜 i`
turns `⨁ i, 𝓜 i` into an `A`-module
-/
def isModule [DecidableEq ι] [GradedRing 𝓐] : Module A (⨁ i, 𝓜 i) :=
  { Module.compHom _ (DirectSum.decomposeRingEquiv 𝓐 : A ≃+* ⨁ i, 𝓐 i).toRingHom with
    smul := fun a b => DirectSum.decompose 𝓐 a • b }
#align graded_module.is_module GradedModule.isModule

attribute [local instance] GradedModule.isModule

/-- `⨁ i, 𝓜 i` and `M` are isomorphic as `A`-modules.
"The internal version" and "the external version" are isomorphism as `A`-modules.
-/
def linearEquiv [DecidableEq ι] [GradedRing 𝓐] [DirectSum.Decomposition 𝓜] : M ≃ₗ[A] ⨁ i, 𝓜 i :=
  {
    DirectSum.decomposeAddEquiv
      𝓜 with
    toFun := DirectSum.decomposeAddEquiv 𝓜
    map_smul' := fun x y => by
      classical
        rw [← DirectSum.sum_support_decompose 𝓐 x, map_sum, Finset.sum_smul, map_sum,
          Finset.sum_smul, Finset.sum_congr rfl fun i hi => _]
        rw [RingHom.id_apply, ← DirectSum.sum_support_decompose 𝓜 y, map_sum, Finset.smul_sum,
          map_sum, Finset.smul_sum, Finset.sum_congr rfl fun j hj => _]
        simp only [(· • ·), DirectSum.decomposeAddEquiv_apply, DirectSum.decompose_coe,
          DirectSum.Gmodule.smulAddMonoidHom_apply_of_of]
        convert DirectSum.decompose_coe 𝓜 _
        rfl }
#align graded_module.linear_equiv GradedModule.linearEquiv

end GradedModule

