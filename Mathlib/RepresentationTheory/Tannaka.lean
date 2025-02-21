/-
Copyright (c) 2025 Yacine Benmeuraiem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yacine Benmeuraiem
-/
import Mathlib.RepresentationTheory.FDRep

/-!
# Tannaka duality for finite groups

In this file we prove Tannaka duality for finite groups.

The theorem can be formulated as follows: for any field `k`, a finite group `G` can be recovered
from `FDRep k G`, the monoidal category of finite dimensional `k`-linear representations of `G`,
and the monoidal forgetful functor `F : FDRep k G ⥤ FGModuleCat k`.

## Notation

- `F`   : the monoidal forgetful functor `FDRep k G ⥤ FGModuleCat k`
- `T`   : the morphism `G →* Aut (F k G)` shown to be an isomorphism
- `τᵣ`  : the right regular representation on `G → k`
- `α`   : the map sending a monoidal natural isomorphism `η : Aut (F k G)` to its `τᵣ` component

## Reference

<https://math.leidenuniv.nl/scripties/1bachCommelin.pdf>
-/

noncomputable section

open CategoryTheory ModuleCat Pi

universe u

namespace TannakaDuality

variable {k G : Type u} [Field k] [Group G]

section definitions

instance : (forget₂ (FDRep k G) (FGModuleCat k)).Monoidal := by
  change (Action.forget _ _).Monoidal; infer_instance

variable (k G) in
/-- The monoidal forgetful functor from `FDRep k G` to `FGModuleCat k` -/
def F := LaxMonoidalFunctor.of (forget₂ (FDRep k G) (FGModuleCat k))

/-- Definition of `T g : Aut (F k G)` by its components -/
def T_app (g : G) (X : FDRep k G) : X.V ≅ X.V where
  hom := ofHom (X.ρ g)
  inv := ofHom (X.ρ g⁻¹)
  hom_inv_id := by
    ext x
    change (X.ρ g⁻¹ * X.ρ g) x = x
    simp [← map_mul]
  inv_hom_id := by
    ext x
    change (X.ρ g * X.ρ g⁻¹) x = x
    simp [← map_mul]

/-- The function defining `T` -/
def T_fun (g : G) : Aut (F k G) :=
  LaxMonoidalFunctor.isoOfComponents (T_app g) (fun f ↦ (f.comm g).symm) rfl (by intros; rfl)

@[simp]
lemma T_apply (g : G) (X : FDRep k G) : ((T_fun g).hom.hom.app X).hom = X.ρ g := rfl

variable (k G) in
/-- The group homomorphism `G →* Aut (F k G)` shown to be bijective -/
def T : G →* Aut (F k G) where
  toFun := T_fun
  map_one' := by ext; simp; rfl
  map_mul' _ _ := by ext; simp; rfl

/-- The representation on `G → k` induced by multiplication on the right in `G` -/
@[simps]
def τᵣ : Representation k G (G → k) where
  toFun s := {
    toFun f t := f (t * s)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
  }
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp [mul_assoc]

variable [Fintype G]

variable (k G) in
/-- The right regular representation `τᵣ` on `G → k` as a `FDRep k G` -/
def fdRepτᵣ : FDRep k G := FDRep.of τᵣ

/-- Map sending `η : Aut (F k G)` to its component at `fdRepτᵣ k G` as a linear map -/
def α (η : Aut (F k G)) : (G → k) →ₗ[k] (G → k) := (η.hom.hom.app (fdRepτᵣ k G)).hom

end definitions

variable [Fintype G]

lemma T_injective [DecidableEq G] : Function.Injective (T k G) := by
  rw [injective_iff_map_eq_one]
  intro s h
  apply_fun α at h
  apply_fun (· (single 1 1) 1) at h
  change (single 1 1 : G → k) (1 * s) = (single 1 1 : G → k) 1 at h
  simp_all [single_apply]

end TannakaDuality
