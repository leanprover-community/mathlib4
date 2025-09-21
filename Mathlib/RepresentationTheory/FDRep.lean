/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Category.FGModuleCat.Limits
import Mathlib.Algebra.Category.FGModuleCat.Colimits
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Rep

/-!
# `FDRep k G` is the category of finite dimensional `k`-linear representations of `G`.

If `V : FDRep k G`, there is a coercion that allows you to treat `V` as a type,
and this type comes equipped with `Module k V` and `FiniteDimensional k V` instances.
Also `V.ρ` gives the homomorphism `G →* (V →ₗ[k] V)`.

Conversely, given a homomorphism `ρ : G →* (V →ₗ[k] V)`,
you can construct the bundled representation as `Rep.of ρ`.

We prove Schur's Lemma: the dimension of the `Hom`-space between two irreducible representation is
`0` if they are not isomorphic, and `1` if they are.
This is the content of `finrank_hom_simple_simple`

We verify that `FDRep k G` is a `k`-linear monoidal category, and rigid when `G` is a group.

`FDRep k G` has all finite limits.

## Implementation notes

We define `FDRep R G` for any ring `R` and monoid `G`,
as the category of finitely generated `R`-linear representations of `G`.

The main case of interest is when `R = k` is a field and `G` is a group,
and this is reflected in the documentation.

## TODO
* `FdRep k G ≌ FullSubcategory (FiniteDimensional k)`
* `FdRep k G` has all finite colimits.
* `FdRep k G` is abelian.
* `FdRep k G ≌ FGModuleCat (MonoidAlgebra k G)`.

-/

suppress_compilation

universe u

open CategoryTheory

open CategoryTheory.Limits


/-- The category of finitely generated `R`-linear representations of a monoid `G`.

Note that `R` can be any ring,
but the main case of interest is when `R = k` is a field and `G` is a group. -/
abbrev FDRep (R G : Type u) [Ring R] [Monoid G] :=
  Action (FGModuleCat.{u} R) G

namespace FDRep

variable {R k G : Type u} [CommRing R] [Field k] [Monoid G]

-- The `LargeCategory, ConcreteCategory, Preadditive, HasFiniteLimits` instances should be
-- constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380
instance : LargeCategory (FDRep R G) := inferInstance
instance : ConcreteCategory (FDRep R G) (Action.HomSubtype _ _) := inferInstance
instance : Preadditive (FDRep R G) := inferInstance
instance : HasFiniteLimits (FDRep k G) := inferInstance

instance : Linear R (FDRep R G) := by infer_instance

instance : CoeSort (FDRep R G) (Type u) :=
  ⟨fun V => V.V⟩

instance (V : FDRep R G) : AddCommGroup V := by
  change AddCommGroup ((forget₂ (FDRep R G) (FGModuleCat R)).obj V).obj; infer_instance

instance (V : FDRep R G) : Module R V := by
  change Module R ((forget₂ (FDRep R G) (FGModuleCat R)).obj V).obj; infer_instance

instance (V : FDRep R G) : Module.Finite R V := by
  change Module.Finite R ((forget₂ (FDRep R G) (FGModuleCat R)).obj V); infer_instance

instance (V : FDRep k G) : FiniteDimensional k V := by
  infer_instance

/-- All hom spaces are finite dimensional. -/
instance (V W : FDRep k G) : FiniteDimensional k (V ⟶ W) :=
  FiniteDimensional.of_injective ((forget₂ (FDRep k G) (FGModuleCat k)).mapLinearMap k)
    (Functor.map_injective (forget₂ (FDRep k G) (FGModuleCat k)))

/-- The monoid homomorphism corresponding to the action of `G` onto `V : FDRep R G`. -/
def ρ (V : FDRep R G) : G →* V →ₗ[R] V :=
  (ModuleCat.endRingEquiv _).toMonoidHom.comp (Action.ρ V)

@[simp]
lemma endRingEquiv_symm_comp_ρ (V : FDRep R G) :
    (MonoidHomClass.toMonoidHom (ModuleCat.endRingEquiv V.V.obj).symm).comp (ρ V) =
      (Action.ρ V) :=
  rfl

@[simp]
lemma endRingEquiv_comp_ρ (V : FDRep R G) :
    (MonoidHomClass.toMonoidHom (ModuleCat.endRingEquiv V.V.obj)).comp (Action.ρ V) = ρ V := rfl

@[simp]
lemma hom_action_ρ (V : FDRep R G) (g : G) : (Action.ρ V g).hom = ρ V g := rfl

/-- The underlying `LinearEquiv` of an isomorphism of representations. -/
def isoToLinearEquiv {V W : FDRep R G} (i : V ≅ W) : V ≃ₗ[R] W :=
  FGModuleCat.isoToLinearEquiv ((Action.forget (FGModuleCat R) G).mapIso i)

theorem Iso.conj_ρ {V W : FDRep R G} (i : V ≅ W) (g : G) :
    W.ρ g = (FDRep.isoToLinearEquiv i).conj (V.ρ g) := by
  rw [FDRep.isoToLinearEquiv, ← hom_action_ρ V, ← FGModuleCat.Iso.conj_hom_eq_conj, Iso.conj_apply,
      ← ModuleCat.hom_ofHom (W.ρ g), ← ModuleCat.hom_ext_iff,
      Iso.eq_inv_comp ((Action.forget (FGModuleCat R) G).mapIso i)]
  exact (i.hom.comm g).symm

/-- Lift an unbundled representation to `FDRep`. -/
@[simps ρ]
abbrev of {V : Type u} [AddCommGroup V] [Module R V] [Module.Finite R V]
    (ρ : Representation R G V) : FDRep R G :=
  ⟨FGModuleCat.of R V, (ModuleCat.endRingEquiv _).symm.toMonoidHom.comp ρ⟩

/-- This lemma is about `FDRep.ρ`, instead of `Action.ρ` for `of_ρ`. -/
@[simp]
theorem of_ρ' {V : Type u} [AddCommGroup V] [Module R V] [Module.Finite R V] (ρ : G →* V →ₗ[R] V) :
    (of ρ).ρ = ρ := rfl

@[deprecated Representation.inv_self_apply (since := "2025-05-09")]
theorem ρ_inv_self_apply {G : Type u} [Group G] {A : FDRep R G} (g : G) (x : A) :
    A.ρ g⁻¹ (A.ρ g x) = x :=
  show (A.ρ g⁻¹ * A.ρ g) x = x by rw [← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

@[deprecated Representation.self_inv_apply (since := "2025-05-09")]
theorem ρ_self_inv_apply {G : Type u} [Group G] {A : FDRep R G} (g : G) (x : A) :
    A.ρ g (A.ρ g⁻¹ x) = x :=
  show (A.ρ g * A.ρ g⁻¹) x = x by rw [← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

instance : HasForget₂ (FDRep R G) (Rep R G) where
  forget₂ := (forget₂ (FGModuleCat R) (ModuleCat R)).mapAction G

theorem forget₂_ρ (V : FDRep R G) : ((forget₂ (FDRep R G) (Rep R G)).obj V).ρ = V.ρ := by
  ext g v; rfl

instance [IsNoetherianRing R] : PreservesFiniteLimits (forget₂ (FDRep R G) (Rep R G)) :=
  inferInstanceAs <| PreservesFiniteLimits <| (forget₂ (FGModuleCat R) (ModuleCat R)).mapAction G

instance : PreservesFiniteColimits (forget₂ (FDRep R G) (Rep R G)) :=
  inferInstanceAs <| PreservesFiniteColimits <| (forget₂ (FGModuleCat R) (ModuleCat R)).mapAction G

-- Verify that the monoidal structure is available.
example : MonoidalCategory (FDRep R G) := by infer_instance

example : MonoidalPreadditive (FDRep R G) := by infer_instance

example : MonoidalLinear R (FDRep R G) := by infer_instance

open Module

-- We need to provide this instance explicitly as otherwise `finrank_hom_simple_simple` gives a
-- deterministic timeout.
instance : HasKernels (FDRep k G) := by infer_instance

open scoped Classical in
/-- Schur's Lemma: the dimension of the `Hom`-space between two irreducible representation is `0` if
they are not isomorphic, and `1` if they are. -/
theorem finrank_hom_simple_simple [IsAlgClosed k] (V W : FDRep k G) [Simple V] [Simple W] :
    finrank k (V ⟶ W) = if Nonempty (V ≅ W) then 1 else 0 :=
  CategoryTheory.finrank_hom_simple_simple k V W

/-- The forgetful functor to `Rep k G` preserves hom-sets and their vector space structure. -/
def forget₂HomLinearEquiv (X Y : FDRep R G) :
    ((forget₂ (FDRep R G) (Rep R G)).obj X ⟶
      (forget₂ (FDRep R G) (Rep R G)).obj Y) ≃ₗ[R] X ⟶ Y where
  toFun f := ⟨f.hom, f.comm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨(forget₂ (FGModuleCat R) (ModuleCat R)).map f.hom, f.comm⟩

instance : (forget₂ (FDRep R G) (Rep R G)).Full := by
  dsimp [forget₂, HasForget₂.forget₂]
  infer_instance

instance : (forget₂ (FDRep R G) (Rep R G)).Faithful := by
  dsimp [forget₂, HasForget₂.forget₂]
  infer_instance

-- Appealing to the fact that simple objects are not zero objects would be more complicated here,
-- so instead, we use that `0 = 𝟙` holds for rank 0 spaces, since they are subsingletons,
-- but not for simple objects.
theorem finrank_pos_of_simple (V : FDRep R G) [Simple V] [StrongRankCondition R]
    [NoZeroSMulDivisors R V] : 0 < finrank R V := by
  by_contra! h
  rw[nonpos_iff_eq_zero, Module.finrank_zero_iff] at h
  apply id_nonzero V
  ext a
  simpa using Subsingleton.allEq _ _

end FDRep
namespace FDRep

variable {k G : Type u} [Field k] [Group G]

-- Verify that the right rigid structure is available when the monoid is a group.
noncomputable instance : RightRigidCategory (FDRep k G) := by
  change RightRigidCategory (Action (FGModuleCat k) G); infer_instance

example : RigidCategory (FDRep k G) := by infer_instance

end FDRep

namespace FDRep

-- The variables in this section are slightly weird, living half in `Representation` and half in
-- `FDRep`. When we have a better API for general monoidal closed and rigid categories and these
-- structures on `FDRep`, we should remove the dependency of statements about `FDRep` on
-- `Representation.linHom` and `Representation.dual`. The isomorphism `dualTensorIsoLinHom`
-- below should then just be obtained from general results about rigid categories.
open Representation

variable {k G V : Type u} [Field k] [Group G]
variable [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V]
variable (ρV : Representation k G V) (W : FDRep k G)

open scoped MonoidalCategory

/-- Auxiliary definition for `FDRep.dualTensorIsoLinHom`. -/
noncomputable def dualTensorIsoLinHomAux :
    (FDRep.of ρV.dual ⊗ W).V ≅ (FDRep.of (linHom ρV W.ρ)).V :=
  LinearEquiv.toFGModuleCatIso (dualTensorHomEquiv k V W)

/-- When `V` and `W` are finite dimensional representations of a group `G`, the isomorphism
`dualTensorHomEquiv k V W` of vector spaces induces an isomorphism of representations. -/
noncomputable def dualTensorIsoLinHom : FDRep.of ρV.dual ⊗ W ≅ FDRep.of (linHom ρV W.ρ) := by
  refine Action.mkIso (dualTensorIsoLinHomAux ρV W) (fun g => ?_)
  ext : 1
  exact dualTensorHom_comm ρV W.ρ g

@[simp]
theorem dualTensorIsoLinHom_hom_hom :
    (dualTensorIsoLinHom ρV W).hom.hom = ModuleCat.ofHom (dualTensorHom k V W) :=
  rfl

end FDRep
