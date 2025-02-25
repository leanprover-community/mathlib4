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

/-- Definition of `equivHom g : Aut (forget k G)` by its components. -/
@[simps]
def equivApp (g : G) (X : FDRep k G) : X.V ≅ X.V where
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

variable (k G) in
/-- The group homomorphism `G →* Aut (forget k G)` shown to be an isomorphism. -/
def equivHom : G →* Aut (forget k G) where
  toFun g :=
    LaxMonoidalFunctor.isoOfComponents (equivApp g) (fun f ↦ (f.comm g).symm) rfl (by intros; rfl)
  map_one' := by ext; simp; rfl
  map_mul' _ _ := by ext; simp; rfl

/-- The representation on `G → k` induced by multiplication on the right in `G`. -/
@[simps]
def rightRegular : Representation k G (G → k) where
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

/-- The representation on `G → k` induced by multiplication on the left in `G`. -/
@[simps]
def leftRegular : Representation k G (G → k) where
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
/-- The right regular representation `rightRegular` on `G → k` as a `FDRep k G`. -/
def rightFDRep : FDRep k G := FDRep.of rightRegular

/-- Map sending `η : Aut (forget k G)` to its component at `rightFDRep k G` as a linear map. -/
def toRightFDRepComp (η : Aut (forget k G)) : (G → k) →ₗ[k] (G → k) :=
  (η.hom.hom.app (rightFDRep k G)).hom

end definitions

variable [Fintype G]

lemma equivHom_inj [Nontrivial k] [DecidableEq G] : Function.Injective (equivHom k G) := by
  rw [injective_iff_map_eq_one]
  intro s h
  apply_fun (fun x ↦ (toRightFDRepComp x) (single 1 1) 1) at h
  change (single 1 1 : G → k) (1 * s) = (single 1 1 : G → k) 1 at h
  simp_all [single_apply]

/-- An algebra morphism `φ : (G → k) →ₐ[k] k` is an evaluation map. -/
lemma eval_of_alghom [IsDomain k] {G : Type u} [DecidableEq G] [Fintype G] (φ : (G → k) →ₐ[k] k) :
    ∃ (s : G), φ = evalAlgHom _ _ s := by
  have h1 := map_one φ
  simp only [← univ_sum_single (1 : G → k), one_apply, map_sum] at h1
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
    rwa [Fintype.sum_eq_single s h2] at h1
  use s
  refine AlgHom.toLinearMap_injective (Basis.ext (basisFun k G) (fun t ↦ ?_))
  by_cases t = s <;> simp_all

/-- The `FDRep k G` morphism induced by multiplication on `G → k`. -/
def mulRepHom : rightFDRep k G ⊗ rightFDRep k G ⟶ rightFDRep k G where
  hom := ofHom (LinearMap.mul' k (G → k))
  comm := by
    intro
    ext (u : TensorProduct k (G → k) (G → k))
    refine TensorProduct.induction_on u rfl (fun _ _ ↦ rfl) (fun _ _ hx hy ↦ ?_)
    simp only [map_add, hx, hy]

/-- For `η : Aut (forget k G)`, `toRightFDRepComp η` preserves multiplication -/
lemma map_mul_toRightFDRepComp (η : Aut (forget k G)) (f g : G → k) :
    (toRightFDRepComp η) (f * g) = ((toRightFDRepComp η) f) * ((toRightFDRepComp η) g) := by
  have nat := η.hom.hom.naturality mulRepHom
  have tensor (X Y) : η.hom.hom.app (X ⊗ Y) = (η.hom.hom.app X ⊗ η.hom.hom.app Y) :=
    η.hom.isMonoidal.tensor X Y
  rw [tensor] at nat
  apply_fun (Hom.hom · (f ⊗ₜ[k] g)) at nat
  exact nat

/-- For `η : Aut (forget k G)`, `toRightFDRepComp η` gives rise to
an algebra morphism `(G → k) →ₐ[k] (G → k)`. -/
def algHomOfRightFDRepComp (η : Aut (forget k G)) : (G → k) →ₐ[k] (G → k) := by
  refine AlgHom.ofLinearMap (toRightFDRepComp η) ?_ (map_mul_toRightFDRepComp η)
  let α_inv : (G → k) → (G → k) := (η.inv.hom.app (rightFDRep k G)).hom
  have := η.inv_hom_id
  apply_fun (fun x ↦ (x.hom.app (rightFDRep k G)).hom (1 : G → k)) at this
  change (toRightFDRepComp η) (α_inv 1) = (1 : G → k) at this
  have h := this
  rwa [← one_mul (α_inv 1), map_mul_toRightFDRepComp, h, mul_one] at this

variable [DecidableEq G]

/-- `leftRegular` as a morphism `rightFDRep k G ⟶ rightFDRep k G` in `FDRep k G`. -/
def leftRegularFDRepHom (s : G) : rightFDRep k G ⟶ rightFDRep k G where
  hom := ofHom (leftRegular s)
  comm := by
    intro (t : G)
    ext (f : G → k)
    funext u
    change (leftRegular s) ((rightRegular t) f) u = (rightRegular t) ((leftRegular s) f) u
    simp [mul_assoc]

lemma toRightFDRepComp_in_rightRegular [IsDomain k] (η : Aut (forget k G)) :
    ∃ (s : G), toRightFDRepComp η = rightRegular s := by
  obtain ⟨s, hs⟩ := eval_of_alghom ((evalAlgHom _ _ 1).comp (algHomOfRightFDRepComp η))
  use s
  apply Basis.ext (basisFun k G)
  intro u
  ext t
  have nat := η.hom.hom.naturality (leftRegularFDRepHom t⁻¹)
  apply_fun Hom.hom at nat
  calc
    _ = leftRegular t⁻¹ (toRightFDRepComp η (single u 1)) 1 := by simp
    _ = toRightFDRepComp η (leftRegular t⁻¹ (single u 1)) 1 :=
      congrFun (congrFun (congrArg DFunLike.coe nat) (single u 1)).symm 1
    _ = evalAlgHom _ _ s (leftRegular t⁻¹ (single u 1)) :=
      congrFun (congrArg DFunLike.coe hs) ((leftRegular t⁻¹) (single u 1))
    _ = _ := by
      by_cases u = t * s <;> simp_all [single_apply]

/-- Auxiliary map for the proof of `toRightFDRepComp_inj`. -/
@[simps]
def auxLinearMap {X : FDRep k G} (v : X) : (G → k) →ₗ[k] X where
  toFun f := ∑ s : G, (f s) • (X.ρ s⁻¹ v)
  map_add' _ _ := by
    simp only [add_apply, add_smul]
    exact sum_add_distrib
  map_smul' _ _ := by
    simp only [smul_apply, smul_eq_mul, RingHom.id_apply, smul_sum, smul_smul]

lemma auxLinearMap_single_id {X : FDRep k G} (v : X) : (auxLinearMap v) (single 1 1) = v := by
  rw [auxLinearMap_apply]
  calc
    _ = ∑ s ∈ {1}ᶜ, single 1 1 s • (X.ρ s⁻¹) v + single 1 1 1 • (X.ρ 1⁻¹) v :=
      Fintype.sum_eq_sum_compl_add 1 _
    _ = (single 1 1 : G → k) 1 • (X.ρ 1⁻¹) v := by
      apply add_left_eq_self.mpr
      apply sum_eq_zero
      simp_all
    _ = _ := by
      simp

/-- Auxiliary representation morphism for the proof of `toRightFDRepComp_inj`. -/
@[simps]
def auxFDRepHom (X : FDRep k G) (v : X) : (rightFDRep k G) ⟶ X where
  hom := ofHom (auxLinearMap v)
  comm := by
    intro (t : G)
    ext (f : G → k)
    change (auxLinearMap v) (rightRegular t f) = X.ρ t (auxLinearMap v f)
    simp only [auxLinearMap_apply, map_sum]
    set φ_term := fun (X : FDRep k G) (f : G → k) v s ↦ (f s) • (X.ρ s⁻¹ v)
    have := sum_map univ (mulRightEmbedding t⁻¹) (φ_term X (rightRegular t f) v)
    simp only [φ_term, univ_map_embedding] at this
    rw [this]
    apply sum_congr rfl
    simp

lemma toRightFDRepComp_inj : Function.Injective <| @toRightFDRepComp k G _ _ _ := by
  intro η₁ η₂ h
  ext X v
  have h1 := η₁.hom.hom.naturality (auxFDRepHom X v)
  have h2 := η₂.hom.hom.naturality (auxFDRepHom X v)
  rw [hom_ext h, ← h2] at h1
  apply_fun (Hom.hom · (single 1 1)) at h1
  change Hom.hom _ ((auxLinearMap v) _) = Hom.hom _ ((auxLinearMap v) _) at h1
  rw [auxLinearMap_single_id] at h1
  exact h1

lemma equivHom_surj [IsDomain k] : Function.Surjective (equivHom k G) := by
  intro η
  obtain ⟨s, h⟩ := toRightFDRepComp_in_rightRegular η
  use s
  apply toRightFDRepComp_inj
  exact h.symm

theorem tannaka_duality [IsDomain k] : Function.Bijective (equivHom k G) :=
  ⟨equivHom_inj, equivHom_surj⟩

variable (k G) in
/-- Tannaka duality for finite groups:

A group `G` is isomorphic to `Aut (forget k G)`, where `k` is any integral domain,
and `forget k G` is the monoidal forgetful functor `FDRep k G ⥤ FGModuleCat k G`. -/
def equiv [IsDomain k] : G ≃* Aut (forget k G) :=
  MulEquiv.ofBijective (equivHom k G) tannaka_duality

end FiniteGroup

end TannakaDuality
