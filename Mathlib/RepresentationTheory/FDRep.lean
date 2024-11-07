/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Category.FGModuleCat.Limits
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


/-- The category of finite dimensional `k`-linear representations of a monoid `G`. -/
abbrev FDRep (k G : Type u) [Field k] [Monoid G] :=
  Action (FGModuleCat.{u} k) (MonCat.of G)

@[deprecated (since := "2024-07-05")]
alias FdRep := FDRep

namespace FDRep

variable {k G : Type u} [Field k] [Monoid G]

-- Porting note: `@[derive]` didn't work for `FDRep`. Add the 4 instances here.
instance : LargeCategory (FDRep k G) := inferInstance
instance : ConcreteCategory (FDRep k G) := inferInstance
instance : Preadditive (FDRep k G) := inferInstance
instance : HasFiniteLimits (FDRep k G) := inferInstance

instance : Linear k (FDRep k G) := by infer_instance

instance : CoeSort (FDRep k G) (Type u) :=
  ConcreteCategory.hasCoeToSort _

instance (V : FDRep k G) : AddCommGroup V := by
  change AddCommGroup ((forget₂ (FDRep k G) (FGModuleCat k)).obj V).obj; infer_instance

instance (V : FDRep k G) : Module k V := by
  change Module k ((forget₂ (FDRep k G) (FGModuleCat k)).obj V).obj; infer_instance

instance (V : FDRep k G) : FiniteDimensional k V := by
  change FiniteDimensional k ((forget₂ (FDRep k G) (FGModuleCat k)).obj V); infer_instance

/-- All hom spaces are finite dimensional. -/
instance (V W : FDRep k G) : FiniteDimensional k (V ⟶ W) :=
  FiniteDimensional.of_injective ((forget₂ (FDRep k G) (FGModuleCat k)).mapLinearMap k)
    (Functor.map_injective (forget₂ (FDRep k G) (FGModuleCat k)))

/-- The monoid homomorphism corresponding to the action of `G` onto `V : FDRep k G`. -/
def ρ (V : FDRep k G) : G →* V →ₗ[k] V :=
  Action.ρ V

/-- The underlying `LinearEquiv` of an isomorphism of representations. -/
def isoToLinearEquiv {V W : FDRep k G} (i : V ≅ W) : V ≃ₗ[k] W :=
  FGModuleCat.isoToLinearEquiv ((Action.forget (FGModuleCat k) (MonCat.of G)).mapIso i)

theorem Iso.conj_ρ {V W : FDRep k G} (i : V ≅ W) (g : G) :
    W.ρ g = (FDRep.isoToLinearEquiv i).conj (V.ρ g) := by
  -- Porting note: Changed `rw` to `erw`
  erw [FDRep.isoToLinearEquiv, ← FGModuleCat.Iso.conj_eq_conj, Iso.conj_apply]
  rw [Iso.eq_inv_comp ((Action.forget (FGModuleCat k) (MonCat.of G)).mapIso i)]
  exact (i.hom.comm g).symm

/-- Lift an unbundled representation to `FDRep`. -/
@[simps ρ]
def of {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) : FDRep k G :=
  ⟨FGModuleCat.of k V, ρ⟩

instance : HasForget₂ (FDRep k G) (Rep k G) where
  forget₂ := (forget₂ (FGModuleCat k) (ModuleCat k)).mapAction (MonCat.of G)

theorem forget₂_ρ (V : FDRep k G) : ((forget₂ (FDRep k G) (Rep k G)).obj V).ρ = V.ρ := by
  ext g v; rfl

-- Verify that the monoidal structure is available.
example : MonoidalCategory (FDRep k G) := by infer_instance

example : MonoidalPreadditive (FDRep k G) := by infer_instance

example : MonoidalLinear k (FDRep k G) := by infer_instance

open Module

open scoped Classical

-- We need to provide this instance explicitly as otherwise `finrank_hom_simple_simple` gives a
-- deterministic timeout.
instance : HasKernels (FDRep k G) := by infer_instance

/-- Schur's Lemma: the dimension of the `Hom`-space between two irreducible representation is `0` if
they are not isomorphic, and `1` if they are. -/
theorem finrank_hom_simple_simple [IsAlgClosed k] (V W : FDRep k G) [Simple V] [Simple W] :
    finrank k (V ⟶ W) = if Nonempty (V ≅ W) then 1 else 0 :=
  CategoryTheory.finrank_hom_simple_simple k V W

/-- The forgetful functor to `Rep k G` preserves hom-sets and their vector space structure. -/
def forget₂HomLinearEquiv (X Y : FDRep k G) :
    ((forget₂ (FDRep k G) (Rep k G)).obj X ⟶
      (forget₂ (FDRep k G) (Rep k G)).obj Y) ≃ₗ[k] X ⟶ Y where
  toFun f := ⟨f.hom, f.comm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨(forget₂ (FGModuleCat k) (ModuleCat k)).map f.hom, f.comm⟩
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

end FDRep

namespace FDRep

variable {k G : Type u} [Field k] [Group G]

-- Verify that the right rigid structure is available when the monoid is a group.
noncomputable instance : RightRigidCategory (FDRep k G) := by
  change RightRigidCategory (Action (FGModuleCat k) (Grp.of G)); infer_instance

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
  -- Porting note: had to make all types explicit arguments
  @LinearEquiv.toFGModuleCatIso k _ (FDRep.of ρV.dual ⊗ W).V (V →ₗ[k] W)
    _ _ _ _ _ _ (dualTensorHomEquiv k V W)

/-- When `V` and `W` are finite dimensional representations of a group `G`, the isomorphism
`dualTensorHomEquiv k V W` of vector spaces induces an isomorphism of representations. -/
noncomputable def dualTensorIsoLinHom : FDRep.of ρV.dual ⊗ W ≅ FDRep.of (linHom ρV W.ρ) := by
  refine Action.mkIso (dualTensorIsoLinHomAux ρV W) ?_
  convert dualTensorHom_comm ρV W.ρ

@[simp]
theorem dualTensorIsoLinHom_hom_hom : (dualTensorIsoLinHom ρV W).hom.hom = dualTensorHom k V W :=
  rfl

end FDRep
