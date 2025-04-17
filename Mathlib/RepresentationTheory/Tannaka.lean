/-
Copyright (c) 2025 Yacine Benmeuraiem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yacine Benmeuraiem
-/
import Mathlib.RepresentationTheory.FDRep

/-!
# Tannaka duality for finite groups

In this file we prove Tannaka duality for finite groups.

The theorem can be formulated as follows: for any integral domain `k`, a finite group `G` can be
recovered from `FDRep k G`, the monoidal category of finite dimensional `k`-linear representations
of `G`, and the monoidal forgetful functor `forget : FDRep k G ⥤ FGModuleCat k`.

More specifically, the main result is the isomorphism `equiv : G ≃* Aut (forget k G)`.

## Reference

<https://math.leidenuniv.nl/scripties/1bachCommelin.pdf>
-/

noncomputable section

open CategoryTheory MonoidalCategory ModuleCat Finset Pi

universe u

namespace TannakaDuality

namespace FiniteGroup

variable {k G : Type u} [CommRing k] [Group G]

section definitions

instance : (forget₂ (FDRep k G) (FGModuleCat k)).Monoidal := by
  change (Action.forget _ _).Monoidal; infer_instance

variable (k G) in
/-- The monoidal forgetful functor from `FDRep k G` to `FGModuleCat k`. -/
def forget := LaxMonoidalFunctor.of (forget₂ (FDRep k G) (FGModuleCat k))

@[simp] lemma forget_obj (X : FDRep k G) : (forget k G).obj X = X.V := rfl

@[simp] lemma forget_map (X Y : FDRep k G) (f : X ⟶ Y) : (forget k G).map f = f.hom := rfl

/-- Definition of `equivHom g : Aut (forget k G)` by its components. -/
@[simps]
def equivApp (g : G) (X : FDRep k G) : X.V ≅ X.V where
  hom := ofHom (X.ρ g)
  inv := ofHom (X.ρ g⁻¹)
  hom_inv_id := by
    ext x
    simp
  inv_hom_id := by
    ext x
    simp

variable (k G) in
/-- The group homomorphism `G →* Aut (forget k G)` shown to be an isomorphism. -/
@[simps]
def equivHom : G →* Aut (forget k G) where
  toFun g :=
    LaxMonoidalFunctor.isoOfComponents (equivApp g) (fun f ↦ (f.comm g).symm) rfl (by intros; rfl)
  map_one' := by ext; simp; rfl
  map_mul' _ _ := by ext; simp; rfl

/-- The representation on `G → k` induced by multiplication on the right in `G`. -/
def rightRegular : Representation k G (G → k) where
  toFun s :=
  { toFun f t := f (t * s)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp [mul_assoc]

@[simp]
lemma rightRegular_apply (s t : G) (f : G → k) : rightRegular s f t = f (t * s) := rfl

/-- The representation on `G → k` induced by multiplication on the left in `G`. -/
def leftRegular : Representation k G (G → k) where
  toFun s :=
  { toFun f t := f (s⁻¹ * t)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp [mul_assoc]

@[simp]
lemma leftRegular_apply (s t : G) (f : G → k) : leftRegular s f t = f (s⁻¹ * t) := rfl

variable [Fintype G]

/-- The right regular representation `rightRegular` on `G → k` as a `FDRep k G`. -/
@[simp]
def rightFDRep : FDRep k G := FDRep.of rightRegular

end definitions

variable [Fintype G]

lemma equivHom_inj [Nontrivial k] [DecidableEq G] : Function.Injective (equivHom k G) := by
  intro s t h
  apply_fun (fun x ↦ (x.hom.hom.app rightFDRep).hom (single t 1) 1) at h
  simp_all [single_apply]

/-- The `FDRep k G` morphism induced by multiplication on `G → k`. -/
def mulRepHom : rightFDRep (k := k) (G := G) ⊗ rightFDRep ⟶ rightFDRep where
  hom := ofHom (LinearMap.mul' k (G → k))
  comm := by
    intro
    ext u
    refine TensorProduct.induction_on u rfl (fun _ _ ↦ rfl) (fun _ _ hx hy ↦ ?_)
    simp only [map_add, hx, hy]

/-- The `rightFDRep` component of `η : Aut (forget k G)` preserves multiplication -/
lemma map_mul_toRightFDRepComp (η : Aut (forget k G)) (f g : G → k) :
    let α : (G → k) →ₗ[k] (G → k) := (η.hom.hom.app rightFDRep).hom
    α (f * g) = (α f) * (α g) := by
  have nat := η.hom.hom.naturality mulRepHom
  have tensor (X Y) : η.hom.hom.app (X ⊗ Y) = (η.hom.hom.app X ⊗ η.hom.hom.app Y) :=
    η.hom.isMonoidal.tensor X Y
  rw [tensor] at nat
  apply_fun (Hom.hom · (f ⊗ₜ[k] g)) at nat
  exact nat

/-- The `rightFDRep` component of `η : Aut (forget k G)` gives rise to
an algebra morphism `(G → k) →ₐ[k] (G → k)`. -/
def algHomOfRightFDRepComp (η : Aut (forget k G)) : (G → k) →ₐ[k] (G → k) := by
  let α : (G → k) →ₗ[k] (G → k) := (η.hom.hom.app rightFDRep).hom
  let α_inv : (G → k) →ₗ[k] (G → k) := (η.inv.hom.app rightFDRep).hom
  refine AlgHom.ofLinearMap α ?_ (map_mul_toRightFDRepComp η)
  suffices α (α_inv 1) = (1 : G → k) by
    have h := this
    rwa [← one_mul (α_inv 1), map_mul_toRightFDRepComp, h, mul_one] at this
  have := η.inv_hom_id
  apply_fun (fun x ↦ (x.hom.app rightFDRep).hom (1 : G → k)) at this
  exact this

end FiniteGroup

end TannakaDuality

end
