/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Algebra.GradedMulAction
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Module.BigOperators

/-!
# Graded Module

Given an `R`-algebra `A` graded by `𝓐`, a graded `A`-module `M` is expressed as
`DirectSum.Decomposition 𝓜` and `SetLike.GradedSMul 𝓐 𝓜`.
Then `⨁ i, 𝓜 i` is an `A`-module and is isomorphic to `M`.

## Tags

graded module
-/

@[expose] public section


section

open DirectSum

variable {ιA ιB : Type*} (A : ιA → Type*) (M : ιB → Type*)

namespace DirectSum

open GradedMonoid

/-- A graded version of `DistribMulAction`. -/
class GdistribMulAction [AddMonoid ιA] [VAdd ιA ιB] [GMonoid A] [∀ i, AddMonoid (M i)]
    extends GMulAction A M where
  smul_add {i j} (a : A i) (b c : M j) : smul a (b + c) = smul a b + smul a c
  smul_zero {i j} (a : A i) : smul a (0 : M j) = 0

/-- A graded version of `Module`. -/
class Gmodule [AddMonoid ιA] [VAdd ιA ιB] [∀ i, AddMonoid (A i)] [∀ i, AddMonoid (M i)] [GMonoid A]
    extends GdistribMulAction A M where
  add_smul {i j} (a a' : A i) (b : M j) : smul (a + a') b = smul a b + smul a' b
  zero_smul {i j} (b : M j) : smul (0 : A i) b = 0

/-- A graded version of `Semiring.toModule`. -/
instance GSemiring.toGmodule [AddMonoid ιA] [∀ i : ιA, AddCommMonoid (A i)]
    [h : GSemiring A] : Gmodule A A :=
  { GMonoid.toGMulAction A with
    smul_add := fun _ _ _ => h.mul_add _ _ _
    smul_zero := fun _ => h.mul_zero _
    add_smul := fun _ _ => h.add_mul _ _
    zero_smul := fun _ => h.zero_mul _ }

variable [AddMonoid ιA] [VAdd ιA ιB] [∀ i : ιA, AddCommMonoid (A i)] [∀ i, AddCommMonoid (M i)]

/-- The piecewise multiplication from the `Mul` instance, as a bundled homomorphism. -/
@[simps]
def gsmulHom [GMonoid A] [Gmodule A M] {i j} : A i →+ M j →+ M (i +ᵥ j) where
  toFun a :=
    { toFun := fun b => GSMul.smul a b
      map_zero' := GdistribMulAction.smul_zero _
      map_add' := GdistribMulAction.smul_add _ }
  map_zero' := AddMonoidHom.ext fun a => Gmodule.zero_smul a
  map_add' _a₁ _a₂ := AddMonoidHom.ext fun _b => Gmodule.add_smul _ _ _

namespace Gmodule

/-- For graded monoid `A` and a graded module `M` over `A`. `Gmodule.smulAddMonoidHom` is the
`⨁ᵢ Aᵢ`-scalar multiplication on `⨁ᵢ Mᵢ` induced by `gsmul_hom`. -/
def smulAddMonoidHom [DecidableEq ιA] [DecidableEq ιB] [GMonoid A] [Gmodule A M] :
    (⨁ i, A i) →+ (⨁ i, M i) →+ ⨁ i, M i :=
  toAddMonoid fun _i =>
    AddMonoidHom.flip <|
      toAddMonoid fun _j => AddMonoidHom.flip <| (of M _).compHom.comp <| gsmulHom A M

section

open GradedMonoid DirectSum Gmodule

instance [DecidableEq ιA] [DecidableEq ιB] [GMonoid A] [Gmodule A M] :
    SMul (⨁ i, A i) (⨁ i, M i) where
  smul x y := smulAddMonoidHom A M x y

@[simp]
theorem smul_def [DecidableEq ιA] [DecidableEq ιB] [GMonoid A] [Gmodule A M]
    (x : ⨁ i, A i) (y : ⨁ i, M i) :
    x • y = smulAddMonoidHom _ _ x y := rfl

@[simp]
theorem smulAddMonoidHom_apply_of_of [DecidableEq ιA] [DecidableEq ιB] [GMonoid A] [Gmodule A M]
    {i j} (x : A i) (y : M j) :
    smulAddMonoidHom A M (DirectSum.of A i x) (of M j y) = of M (i +ᵥ j) (GSMul.smul x y) := by
  simp [smulAddMonoidHom]

theorem of_smul_of [DecidableEq ιA] [DecidableEq ιB] [GMonoid A] [Gmodule A M]
    {i j} (x : A i) (y : M j) :
    DirectSum.of A i x • of M j y = of M (i +ᵥ j) (GSMul.smul x y) := by simp

open AddMonoidHom

-- Almost identical to the proof of `direct_sum.one_mul`
set_option backward.privateInPublic true in
private theorem one_smul' [DecidableEq ιA] [DecidableEq ιB] [GMonoid A] [Gmodule A M]
    (x : ⨁ i, M i) :
    (1 : ⨁ i, A i) • x = x := by
  suffices smulAddMonoidHom A M 1 = AddMonoidHom.id (⨁ i, M i) from DFunLike.congr_fun this x
  apply DirectSum.addHom_ext; intro i xi
  rw [show (1 : DirectSum ιA fun i => A i) = (of A 0) GOne.one by rfl]
  rw [smulAddMonoidHom_apply_of_of]
  exact DirectSum.of_eq_of_gradedMonoid_eq (one_smul (GradedMonoid A) <| GradedMonoid.mk i xi)

-- Almost identical to the proof of `direct_sum.mul_assoc`
set_option backward.privateInPublic true in
private theorem mul_smul' [DecidableEq ιA] [DecidableEq ιB] [GSemiring A] [Gmodule A M]
    (a b : ⨁ i, A i)
    (c : ⨁ i, M i) : (a * b) • c = a • b • c := by
  suffices
    (-- `fun a b c ↦ (a * b) • c` as a bundled hom
              smulAddMonoidHom
              A M).compHom.comp
        (DirectSum.mulHom A) =
      (AddMonoidHom.compHom AddMonoidHom.flipHom <|
          (smulAddMonoidHom A M).flip.compHom.comp <| smulAddMonoidHom A M).flip
    from -- `fun a b c ↦ a • (b • c)` as a bundled hom
      DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun this a) b) c
  ext ai ax bi bx ci cx : 6
  dsimp only [coe_comp, Function.comp_apply, compHom_apply_apply, flip_apply, flipHom_apply]
  rw [smulAddMonoidHom_apply_of_of, smulAddMonoidHom_apply_of_of, DirectSum.mulHom_of_of,
    smulAddMonoidHom_apply_of_of]
  exact
    DirectSum.of_eq_of_gradedMonoid_eq
      (mul_smul (GradedMonoid.mk ai ax) (GradedMonoid.mk bi bx) (GradedMonoid.mk ci cx))

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The `Module` derived from `gmodule A M`. -/
instance module [DecidableEq ιA] [DecidableEq ιB] [GSemiring A] [Gmodule A M] :
    Module (⨁ i, A i) (⨁ i, M i) where
  one_smul := one_smul' _ _
  mul_smul := mul_smul' _ _
  smul_add r := (smulAddMonoidHom A M r).map_add
  smul_zero r := (smulAddMonoidHom A M r).map_zero
  add_smul r s x := by simp only [smul_def, map_add, AddMonoidHom.add_apply]
  zero_smul x := by simp only [smul_def, map_zero, AddMonoidHom.zero_apply]

end

end Gmodule

end DirectSum

end

open DirectSum

variable {ιA ιM R A M σ σ' : Type*}
variable [AddMonoid ιA] [AddAction ιA ιM] [CommSemiring R] [Semiring A] [Algebra R A]
variable (𝓐 : ιA → σ') [SetLike σ' A]
variable (𝓜 : ιM → σ)

namespace SetLike

instance gmulAction [AddMonoid M] [DistribMulAction A M] [SetLike σ M] [SetLike.GradedMonoid 𝓐]
    [SetLike.GradedSMul 𝓐 𝓜] : GradedMonoid.GMulAction (fun i => 𝓐 i) fun i => 𝓜 i :=
  { SetLike.toGSMul 𝓐 𝓜 with
    one_smul := fun ⟨_i, _m⟩ => Sigma.subtype_ext (zero_vadd _ _) (one_smul _ _)
    mul_smul := fun ⟨_i, _a⟩ ⟨_j, _a'⟩ ⟨_k, _b⟩ =>
      Sigma.subtype_ext (add_vadd _ _ _) (mul_smul _ _ _) }

instance gdistribMulAction [AddMonoid M] [DistribMulAction A M] [SetLike σ M]
    [AddSubmonoidClass σ M] [SetLike.GradedMonoid 𝓐] [SetLike.GradedSMul 𝓐 𝓜] :
    DirectSum.GdistribMulAction (fun i => 𝓐 i) fun i => 𝓜 i :=
  { SetLike.gmulAction 𝓐 𝓜 with
    smul_add := fun _a _b _c => Subtype.ext <| smul_add _ _ _
    smul_zero := fun _a => Subtype.ext <| smul_zero _ }

variable [AddCommMonoid M] [Module A M] [SetLike σ M] [AddSubmonoidClass σ' A]
  [AddSubmonoidClass σ M] [SetLike.GradedMonoid 𝓐] [SetLike.GradedSMul 𝓐 𝓜]

/-- `[SetLike.GradedMonoid 𝓐] [SetLike.GradedSMul 𝓐 𝓜]` is the internal version of graded
  module, the internal version can be translated into the external version `gmodule`. -/
instance gmodule : DirectSum.Gmodule (fun i => 𝓐 i) fun i => 𝓜 i :=
  { SetLike.gdistribMulAction 𝓐 𝓜 with
    smul := fun x y => ⟨(x : A) • (y : M), SetLike.GradedSMul.smul_mem x.2 y.2⟩
    add_smul := fun _a _a' _b => Subtype.ext <| add_smul _ _ _
    zero_smul := fun _b => Subtype.ext <| zero_smul _ _ }

end SetLike

namespace GradedModule

variable [AddCommMonoid M] [Module A M] [SetLike σ M] [AddSubmonoidClass σ' A]
  [AddSubmonoidClass σ M] [SetLike.GradedMonoid 𝓐] [SetLike.GradedSMul 𝓐 𝓜]

/-- The smul multiplication of `A` on `⨁ i, 𝓜 i` from `(⨁ i, 𝓐 i) →+ (⨁ i, 𝓜 i) →+ ⨁ i, 𝓜 i`
turns `⨁ i, 𝓜 i` into an `A`-module
-/
@[implicit_reducible]
def isModule [DecidableEq ιA] [DecidableEq ιM] [GradedRing 𝓐] : Module A (⨁ i, 𝓜 i) :=
  { Module.compHom _ (DirectSum.decomposeRingEquiv 𝓐 : A ≃+* ⨁ i, 𝓐 i).toRingHom with
    smul := fun a b => DirectSum.decompose 𝓐 a • b }

/-- `⨁ i, 𝓜 i` and `M` are isomorphic as `A`-modules.
"The internal version" and "the external version" are isomorphism as `A`-modules.
-/
def linearEquiv [DecidableEq ιA] [DecidableEq ιM] [GradedRing 𝓐] [DirectSum.Decomposition 𝓜] :
    @LinearEquiv A A _ _ (RingHom.id A) (RingHom.id A) _ _ M (⨁ i, 𝓜 i) _
    _ _ (by letI := isModule 𝓐 𝓜; infer_instance) := by
  letI h := isModule 𝓐 𝓜
  refine ⟨⟨(DirectSum.decomposeAddEquiv 𝓜).toAddHom, ?_⟩,
    (DirectSum.decomposeAddEquiv 𝓜).symm.toFun, (DirectSum.decomposeAddEquiv 𝓜).left_inv,
    (DirectSum.decomposeAddEquiv 𝓜).right_inv⟩
  intro x y
  classical
  rw [AddHom.toFun_eq_coe, ← DirectSum.sum_support_decompose 𝓐 x, map_sum, Finset.sum_smul,
    AddEquiv.coe_toAddHom, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl (fun i _hi => ?_)
  rw [RingHom.id_apply, ← DirectSum.sum_support_decompose 𝓜 y, map_sum, Finset.smul_sum, map_sum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _hj => ?_)
  rw [show (decompose 𝓐 x i : A) • (decomposeAddEquiv 𝓜 ↑(decompose 𝓜 y j) : (⨁ i, 𝓜 i)) =
    DirectSum.Gmodule.smulAddMonoidHom _ _ (decompose 𝓐 ↑(decompose 𝓐 x i))
    (decomposeAddEquiv 𝓜 ↑(decompose 𝓜 y j)) from DirectSum.Gmodule.smul_def _ _ _ _]
  simp only [decomposeAddEquiv_apply, decompose_coe, Gmodule.smulAddMonoidHom_apply_of_of]
  convert DirectSum.decompose_coe 𝓜 _
  rfl

/--
The projection map of an internally graded module.
-/
@[simps]
def proj [DecidableEq ιM] [Decomposition 𝓜] (i : ιM) : M →+ M where
  toFun m := decompose 𝓜 m i
  map_zero' := by simp
  map_add' := by simp

end GradedModule
