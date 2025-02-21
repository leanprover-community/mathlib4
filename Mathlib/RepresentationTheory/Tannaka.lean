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

open CategoryTheory MonoidalCategory ModuleCat Finset Pi

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

/-- The representation on `G → k` induced by multiplication on the left in `G` -/
@[simps]
def τₗ : Representation k G (G → k) where
  toFun s := {
    toFun f t := f (s⁻¹ * t)
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

/-- An algebra morphism `φ : (G → k) →ₐ[k] k` is an evaluation map. -/
lemma eval_of_alghom {G : Type u} [DecidableEq G] [Fintype G] (φ : (G → k) →ₐ[k] k) :
    ∃ (s : G), φ = evalAlgHom _ _ s := by
  have h1 := map_one φ
  rw [← univ_sum_single (1 : G → k), map_sum] at h1
  obtain ⟨s, hs⟩ : ∃ (s : G), φ (single s 1) ≠ 0 := by
    by_contra
    simp_all
  have h2 : ∀ t ≠ s, φ (single t 1) = 0 := by
    intros
    apply eq_zero_of_ne_zero_of_mul_right_eq_zero hs
    rw [← map_mul]
    convert map_zero φ
    ext u
    by_cases u = s <;> simp_all
  have h3 : φ (single s 1) = 1 := by
    rwa [Fintype.sum_eq_single s] at h1
    exact h2
  use s
  apply AlgHom.toLinearMap_injective
  apply Basis.ext (basisFun k G)
  intro t
  by_cases t = s <;> simp_all

/-- The `FDRep k G` morphism induced by multiplication on `G → k`. -/
def μ : fdRepτᵣ k G ⊗ fdRepτᵣ k G ⟶ fdRepτᵣ k G where
  hom := ofHom (LinearMap.mul' k (G → k))
  comm := by
    intro
    ext (u : TensorProduct k (G → k) (G → k))
    refine TensorProduct.induction_on u rfl (fun _ _ ↦ rfl) ?_
    intro _ _ hx hy
    simp only [map_add, hx, hy]

/-- For `η : Aut (F k G)`, `α η` is compatible with multiplication -/
lemma map_mul_α (η : Aut (F k G)) : ∀ (x y : G → k), (α η) (x * y) = ((α η) x) * ((α η) y) := by
  intro f g
  have nat := η.hom.hom.naturality μ
  have tensor := η.hom.isMonoidal.tensor
  have F_μ {X Y} : Functor.LaxMonoidal.μ (F k G).toFunctor X Y = 𝟙 _ := rfl
  simp only [F_μ, Category.id_comp, Category.comp_id] at tensor
  rw [tensor] at nat
  apply_fun Hom.hom at nat
  apply_fun (· (f ⊗ₜ[k] g)) at nat
  exact nat

/-- For `η : Aut (F k G)`, `α η` gives rise to an algebra morphism `(G → k) →ₐ[k] (G → k)` -/
def algHomOfα (η : Aut (F k G)) : (G → k) →ₐ[k] (G → k) := by
  refine AlgHom.ofLinearMap (α η) ?_ (map_mul_α η)
  let α_inv : (G → k) → (G → k) := (η.inv.hom.app (fdRepτᵣ k G)).hom
  have := η.inv_hom_id
  apply_fun NatTrans.app ∘ LaxMonoidalFunctor.Hom.hom at this
  replace := congrFun this (fdRepτᵣ k G)
  apply_fun (Hom.hom · (1 : G → k)) at this
  change (α η) (α_inv 1) = (1 : G → k) at this
  have h := this
  rwa [← one_mul (α_inv 1), map_mul_α, h, mul_one] at this

end TannakaDuality
