/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.RepresentationTheory.Rep
import Mathlib.Algebra.Category.FGModuleCat.Limits
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.RepresentationTheory.Basic

#align_import representation_theory.fdRep from "leanprover-community/mathlib"@"19a70dceb9dff0994b92d2dd049de7d84d28112b"

/-!
# `FdRep k G` is the category of finite dimensional `k`-linear representations of `G`.

If `V : FdRep k G`, there is a coercion that allows you to treat `V` as a type,
and this type comes equipped with `Module k V` and `FiniteDimensional k V` instances.
Also `V.ρ` gives the homomorphism `G →* (V →ₗ[k] V)`.

Conversely, given a homomorphism `ρ : G →* (V →ₗ[k] V)`,
you can construct the bundled representation as `Rep.of ρ`.

We verify that `FdRep k G` is a `k`-linear monoidal category, and rigid when `G` is a group.

`FdRep k G` has all finite limits.

## TODO
* `FdRep k G ≌ FullSubcategory (FiniteDimensional k)`
* Upgrade the right rigid structure to a rigid structure
  (this just needs to be done for `FGModuleCat`).
* `FdRep k G` has all finite colimits.
* `FdRep k G` is abelian.
* `FdRep k G ≌ FGModuleCat (MonoidAlgebra k G)`.

-/


universe u

open CategoryTheory

open CategoryTheory.Limits

set_option linter.uppercaseLean3 false -- `fdRep`

/-- The category of finite dimensional `k`-linear representations of a monoid `G`. -/
abbrev FdRep (k G : Type u) [Field k] [Monoid G] :=
  Action (FGModuleCat.{u} k) (MonCat.of G)
#align fdRep FdRep

namespace FdRep

variable {k G : Type u} [Field k] [Monoid G]

-- Porting note: `@[derive]` didn't work for `FdRep`. Add the 4 instances here.
instance : LargeCategory (FdRep k G) := inferInstance
instance : ConcreteCategory (FdRep k G) := inferInstance
instance : Preadditive (FdRep k G) := inferInstance
instance : HasFiniteLimits (FdRep k G) := inferInstance

instance : Linear k (FdRep k G) := by infer_instance
                                      -- 🎉 no goals

instance : CoeSort (FdRep k G) (Type u) :=
  ConcreteCategory.hasCoeToSort _

instance (V : FdRep k G) : AddCommGroup V := by
  change AddCommGroup ((forget₂ (FdRep k G) (FGModuleCat k)).obj V).obj; infer_instance
  -- ⊢ AddCommGroup ↑((forget₂ (FdRep k G) (FGModuleCat k)).obj V).obj
                                                                         -- 🎉 no goals

instance (V : FdRep k G) : Module k V := by
  change Module k ((forget₂ (FdRep k G) (FGModuleCat k)).obj V).obj; infer_instance
  -- ⊢ Module k ↑((forget₂ (FdRep k G) (FGModuleCat k)).obj V).obj
                                                                     -- 🎉 no goals

instance (V : FdRep k G) : FiniteDimensional k V := by
  change FiniteDimensional k ((forget₂ (FdRep k G) (FGModuleCat k)).obj V); infer_instance
  -- ⊢ FiniteDimensional k ↑((forget₂ (FdRep k G) (FGModuleCat k)).obj V)
                                                                            -- 🎉 no goals

/-- All hom spaces are finite dimensional. -/
instance (V W : FdRep k G) : FiniteDimensional k (V ⟶ W) :=
  FiniteDimensional.of_injective ((forget₂ (FdRep k G) (FGModuleCat k)).mapLinearMap k)
    (Functor.map_injective (forget₂ (FdRep k G) (FGModuleCat k)))

/-- The monoid homomorphism corresponding to the action of `G` onto `V : FdRep k G`. -/
def ρ (V : FdRep k G) : G →* V →ₗ[k] V :=
  Action.ρ V
#align fdRep.ρ FdRep.ρ

/-- The underlying `LinearEquiv` of an isomorphism of representations. -/
def isoToLinearEquiv {V W : FdRep k G} (i : V ≅ W) : V ≃ₗ[k] W :=
  FGModuleCat.isoToLinearEquiv ((Action.forget (FGModuleCat k) (MonCat.of G)).mapIso i)
#align fdRep.iso_to_linear_equiv FdRep.isoToLinearEquiv

theorem Iso.conj_ρ {V W : FdRep k G} (i : V ≅ W) (g : G) :
    W.ρ g = (FdRep.isoToLinearEquiv i).conj (V.ρ g) := by
  -- Porting note: Changed `rw` to `erw`
  erw [FdRep.isoToLinearEquiv, ← FGModuleCat.Iso.conj_eq_conj, Iso.conj_apply]
  -- ⊢ ↑(ρ W) g = ((Action.forget (FGModuleCat k) (MonCat.of G)).mapIso i).inv ≫ ↑( …
  rw [Iso.eq_inv_comp ((Action.forget (FGModuleCat k) (MonCat.of G)).mapIso i)]
  -- ⊢ ((Action.forget (FGModuleCat k) (MonCat.of G)).mapIso i).hom ≫ ↑(ρ W) g = ↑( …
  exact (i.hom.comm g).symm
  -- 🎉 no goals
#align fdRep.iso.conj_ρ FdRep.Iso.conj_ρ

/-- Lift an unbundled representation to `FdRep`. -/
@[simps ρ]
def of {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) : FdRep k G :=
  ⟨FGModuleCat.of k V, ρ⟩
#align fdRep.of FdRep.of

instance : HasForget₂ (FdRep k G) (Rep k G)
    where forget₂ := (forget₂ (FGModuleCat k) (ModuleCat k)).mapAction (MonCat.of G)

theorem forget₂_ρ (V : FdRep k G) : ((forget₂ (FdRep k G) (Rep k G)).obj V).ρ = V.ρ := by
  ext g v; rfl
  -- ⊢ ↑(↑(Rep.ρ ((forget₂ (FdRep k G) (Rep k G)).obj V)) g) v = ↑(↑(ρ V) g) v
           -- 🎉 no goals
#align fdRep.forget₂_ρ FdRep.forget₂_ρ

-- Verify that the monoidal structure is available.
example : MonoidalCategory (FdRep k G) := by infer_instance
                                             -- 🎉 no goals

example : MonoidalPreadditive (FdRep k G) := by infer_instance
                                                -- 🎉 no goals

example : MonoidalLinear k (FdRep k G) := by infer_instance
                                             -- 🎉 no goals

open FiniteDimensional

open scoped Classical

-- We need to provide this instance explicitely as otherwise `finrank_hom_simple_simple` gives a
-- deterministic timeout.
instance : HasKernels (FdRep k G) := by infer_instance
                                        -- 🎉 no goals

-- Verify that Schur's lemma applies out of the box.
theorem finrank_hom_simple_simple [IsAlgClosed k] (V W : FdRep k G) [Simple V] [Simple W] :
    finrank k (V ⟶ W) = if Nonempty (V ≅ W) then 1 else 0 :=
  CategoryTheory.finrank_hom_simple_simple k V W
#align fdRep.finrank_hom_simple_simple FdRep.finrank_hom_simple_simple

/-- The forgetful functor to `Rep k G` preserves hom-sets and their vector space structure. -/
def forget₂HomLinearEquiv (X Y : FdRep k G) :
    ((forget₂ (FdRep k G) (Rep k G)).obj X ⟶ (forget₂ (FdRep k G) (Rep k G)).obj Y) ≃ₗ[k] X ⟶ Y
    where
  toFun f := ⟨f.hom, f.comm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨(forget₂ (FGModuleCat k) (ModuleCat k)).map f.hom, f.comm⟩
  left_inv _ := by ext; rfl
                   -- ⊢ ↑((fun f => Action.Hom.mk ((forget₂ (FGModuleCat k) (ModuleCat k)).map f.hom …
                        -- 🎉 no goals
  right_inv _ := by ext; rfl
                    -- ⊢ ↑(AddHom.toFun { toAddHom := { toFun := fun f => Action.Hom.mk f.hom, map_ad …
                         -- 🎉 no goals
#align fdRep.forget₂_hom_linear_equiv FdRep.forget₂HomLinearEquiv

end FdRep

namespace FdRep

variable {k G : Type u} [Field k] [Group G]

-- Verify that the right rigid structure is available when the monoid is a group.
noncomputable instance : RightRigidCategory (FdRep k G) := by
  change RightRigidCategory (Action (FGModuleCat k) (GroupCat.of G)); infer_instance
  -- ⊢ RightRigidCategory (Action (FGModuleCat k) ((forget₂ GroupCat MonCat).obj (G …
                                                                      -- 🎉 no goals

end FdRep

namespace FdRep

-- The variables in this section are slightly weird, living half in `Representation` and half in
-- `FdRep`. When we have a better API for general monoidal closed and rigid categories and these
-- structures on `FdRep`, we should remove the dependancy of statements about `FdRep` on
-- `Representation.linHom` and `Representation.dual`. The isomorphism `dualTensorIsoLinHom`
-- below should then just be obtained from general results about rigid categories.
open Representation

variable {k G V : Type u} [Field k] [Group G]
variable [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V]
variable (ρV : Representation k G V) (W : FdRep k G)

open scoped MonoidalCategory

/-- Auxiliary definition for `FdRep.dualTensorIsoLinHom`. -/
noncomputable def dualTensorIsoLinHomAux :
    (FdRep.of ρV.dual ⊗ W).V ≅ (FdRep.of (linHom ρV W.ρ)).V :=
  -- Porting note: had to make all types explicit arguments
  @LinearEquiv.toFGModuleCatIso k _ (FdRep.of ρV.dual ⊗ W).V (V →ₗ[k] W)
    _ _ _ _ _ _ (dualTensorHomEquiv k V W)
#align fdRep.dual_tensor_iso_lin_hom_aux FdRep.dualTensorIsoLinHomAux

/-- When `V` and `W` are finite dimensional representations of a group `G`, the isomorphism
`dualTensorHomEquiv k V W` of vector spaces induces an isomorphism of representations. -/
noncomputable def dualTensorIsoLinHom : FdRep.of ρV.dual ⊗ W ≅ FdRep.of (linHom ρV W.ρ) := by
  refine Action.mkIso (dualTensorIsoLinHomAux ρV W) ?_
  -- ⊢ ∀ (g : ↑(MonCat.of G)), ↑(of (dual ρV) ⊗ W).ρ g ≫ (dualTensorIsoLinHomAux ρV …
  convert dualTensorHom_comm ρV W.ρ
  -- 🎉 no goals
#align fdRep.dual_tensor_iso_lin_hom FdRep.dualTensorIsoLinHom

@[simp]
theorem dualTensorIsoLinHom_hom_hom : (dualTensorIsoLinHom ρV W).hom.hom = dualTensorHom k V W :=
  rfl
#align fdRep.dual_tensor_iso_lin_hom_hom_hom FdRep.dualTensorIsoLinHom_hom_hom

end FdRep
