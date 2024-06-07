/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.RingTheory.Derivation.Basic

#align_import geometry.manifold.derivation_bundle from "leanprover-community/mathlib"@"86c29aefdba50b3f33e86e52e3b2f51a0d8f0282"

/-!

# Derivation bundle

In this file we define the derivations at a point of a manifold on the algebra of smooth fuctions.
Moreover, we define the differential of a function in terms of derivations.

The content of this file is not meant to be regarded as an alternative definition to the current
tangent bundle but rather as a purely algebraic theory that provides a purely algebraic definition
of the Lie algebra for a Lie group.

-/


variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (M : Type*)
  [TopologicalSpace M] [ChartedSpace H M] (n : ℕ∞)

open scoped Manifold

-- the following two instances prevent poorly understood type class inference timeout problems
instance smoothFunctionsAlgebra : Algebra 𝕜 C^∞⟮I, M; 𝕜⟯ := by infer_instance
#align smooth_functions_algebra smoothFunctionsAlgebra

instance smooth_functions_tower : IsScalarTower 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯ := by infer_instance
#align smooth_functions_tower smooth_functions_tower

/-- Type synonym, introduced to put a different `SMul` action on `C^n⟮I, M; 𝕜⟯`
which is defined as `f • r = f(x) * r`. -/
@[nolint unusedArguments]
def PointedSmoothMap (_ : M) :=
  C^n⟮I, M; 𝕜⟯
#align pointed_smooth_map PointedSmoothMap

@[inherit_doc]
scoped[Derivation] notation "C^" n "⟮" I ", " M "; " 𝕜 "⟯⟨" x "⟩" => PointedSmoothMap 𝕜 I M n x

variable {𝕜 M}

namespace PointedSmoothMap

open scoped Derivation

instance instFunLike {x : M} : FunLike C^∞⟮I, M; 𝕜⟯⟨x⟩ M 𝕜 :=
  ContMDiffMap.instFunLike
#align pointed_smooth_map.fun_like PointedSmoothMap.instFunLike

instance {x : M} : CommRing C^∞⟮I, M; 𝕜⟯⟨x⟩ :=
  SmoothMap.commRing

instance {x : M} : Algebra 𝕜 C^∞⟮I, M; 𝕜⟯⟨x⟩ :=
  SmoothMap.algebra

instance {x : M} : Inhabited C^∞⟮I, M; 𝕜⟯⟨x⟩ :=
  ⟨0⟩

instance {x : M} : Algebra C^∞⟮I, M; 𝕜⟯⟨x⟩ C^∞⟮I, M; 𝕜⟯ :=
  Algebra.id C^∞⟮I, M; 𝕜⟯

instance {x : M} : IsScalarTower 𝕜 C^∞⟮I, M; 𝕜⟯⟨x⟩ C^∞⟮I, M; 𝕜⟯ :=
  IsScalarTower.right

variable {I}

/-- `SmoothMap.evalRingHom` gives rise to an algebra structure of `C^∞⟮I, M; 𝕜⟯` on `𝕜`. -/
instance evalAlgebra {x : M} : Algebra C^∞⟮I, M; 𝕜⟯⟨x⟩ 𝕜 :=
  (SmoothMap.evalRingHom x : C^∞⟮I, M; 𝕜⟯⟨x⟩ →+* 𝕜).toAlgebra
#align pointed_smooth_map.eval_algebra PointedSmoothMap.evalAlgebra

/-- With the `evalAlgebra` algebra structure evaluation is actually an algebra morphism. -/
def eval (x : M) : C^∞⟮I, M; 𝕜⟯ →ₐ[C^∞⟮I, M; 𝕜⟯⟨x⟩] 𝕜 :=
  Algebra.ofId C^∞⟮I, M; 𝕜⟯⟨x⟩ 𝕜
#align pointed_smooth_map.eval PointedSmoothMap.eval

theorem smul_def (x : M) (f : C^∞⟮I, M; 𝕜⟯⟨x⟩) (k : 𝕜) : f • k = f x * k :=
  rfl
#align pointed_smooth_map.smul_def PointedSmoothMap.smul_def

instance (x : M) : IsScalarTower 𝕜 C^∞⟮I, M; 𝕜⟯⟨x⟩ 𝕜 where
  smul_assoc k f h := by
    rw [smul_def, smul_def, SmoothMap.coe_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]

end PointedSmoothMap

open scoped Derivation

/-- The derivations at a point of a manifold. Some regard this as a possible definition of the
tangent space -/
abbrev PointDerivation (x : M) :=
  Derivation 𝕜 C^∞⟮I, M; 𝕜⟯⟨x⟩ 𝕜
#align point_derivation PointDerivation

section

open scoped Derivation

variable (X Y : Derivation 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯) (f g : C^∞⟮I, M; 𝕜⟯) (r : 𝕜)

/-- Evaluation at a point gives rise to a `C^∞⟮I, M; 𝕜⟯`-linear map between `C^∞⟮I, M; 𝕜⟯` and `𝕜`.
 -/
def SmoothFunction.evalAt (x : M) : C^∞⟮I, M; 𝕜⟯ →ₗ[C^∞⟮I, M; 𝕜⟯⟨x⟩] 𝕜 :=
  (PointedSmoothMap.eval x).toLinearMap
#align smooth_function.eval_at SmoothFunction.evalAt

namespace Derivation

variable {I}

/-- The evaluation at a point as a linear map. -/
def evalAt (x : M) : Derivation 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯ →ₗ[𝕜] PointDerivation I x :=
  (SmoothFunction.evalAt I x).compDer
#align derivation.eval_at Derivation.evalAt

theorem evalAt_apply (x : M) : evalAt x X f = (X f) x :=
  rfl
#align derivation.eval_at_apply Derivation.evalAt_apply

end Derivation

variable {I} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*}
  [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M']
  [ChartedSpace H' M']

/-- The heterogeneous differential as a linear map. Instead of taking a function as an argument this
differential takes `h : f x = y`. It is particularly handy to deal with situations where the points
on where it has to be evaluated are equal but not definitionally equal. -/
def hfdifferential {f : C^∞⟮I, M; I', M'⟯} {x : M} {y : M'} (h : f x = y) :
    PointDerivation I x →ₗ[𝕜] PointDerivation I' y where
  toFun v :=
    Derivation.mk'
      { toFun := fun g => v (g.comp f)
        map_add' := fun g g' => by dsimp; rw [SmoothMap.add_comp, Derivation.map_add]
        map_smul' := fun k g => by
          dsimp; rw [SmoothMap.smul_comp, Derivation.map_smul, smul_eq_mul] }
      fun g g' => by
        dsimp
        rw [SmoothMap.mul_comp, Derivation.leibniz,
          PointedSmoothMap.smul_def, ContMDiffMap.comp_apply,
          PointedSmoothMap.smul_def, ContMDiffMap.comp_apply, h]
        norm_cast
  map_smul' k v := rfl
  map_add' v w := rfl
#align hfdifferential hfdifferential

/-- The homogeneous differential as a linear map. -/
def fdifferential (f : C^∞⟮I, M; I', M'⟯) (x : M) :
    PointDerivation I x →ₗ[𝕜] PointDerivation I' (f x) :=
  hfdifferential (rfl : f x = f x)
#align fdifferential fdifferential

-- Standard notation for the differential. The abbreviation is `MId`.
scoped[Manifold] notation "𝒅" => fdifferential

-- Standard notation for the differential. The abbreviation is `MId`.
scoped[Manifold] notation "𝒅ₕ" => hfdifferential

@[simp]
theorem apply_fdifferential (f : C^∞⟮I, M; I', M'⟯) {x : M} (v : PointDerivation I x)
    (g : C^∞⟮I', M'; 𝕜⟯) : 𝒅 f x v g = v (g.comp f) :=
  rfl
#align apply_fdifferential apply_fdifferential

@[simp]
theorem apply_hfdifferential {f : C^∞⟮I, M; I', M'⟯} {x : M} {y : M'} (h : f x = y)
    (v : PointDerivation I x) (g : C^∞⟮I', M'; 𝕜⟯) : 𝒅ₕ h v g = 𝒅 f x v g :=
  rfl
#align apply_hfdifferential apply_hfdifferential

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*}
  [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*} [TopologicalSpace M'']
  [ChartedSpace H'' M'']

@[simp]
theorem fdifferential_comp (g : C^∞⟮I', M'; I'', M''⟯) (f : C^∞⟮I, M; I', M'⟯) (x : M) :
    𝒅 (g.comp f) x = (𝒅 g (f x)).comp (𝒅 f x) :=
  rfl
#align fdifferential_comp fdifferential_comp

end
