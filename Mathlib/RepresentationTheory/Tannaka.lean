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

The main result is the isomorphism `equiv : G ≃* Aut (forget k G)`.

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

/-- The right regular representation `rightRegular` on `G → k` as a `FDRep k G`. -/
@[simp]
def rightFDRep [Finite G] : FDRep k G := FDRep.of rightRegular

end definitions

variable [Finite G]

lemma equivHom_injective [Nontrivial k] : Function.Injective (equivHom k G) := by
  intro s t h
  classical
  apply_fun (fun x ↦ (x.hom.hom.app rightFDRep).hom (single t 1) 1) at h
  simp_all [single_apply]

@[deprecated (since := "2025-04-27")]
alias equivHom_inj := equivHom_injective

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
  have tensor (X Y) : η.hom.hom.app (X ⊗ Y) = (η.hom.hom.app X ⊗ₘ η.hom.hom.app Y) :=
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

/-- For `v : X` and `G` a finite group, the `G`-equivariant linear map from the right
regular representation `rightFDRep` to `X` sending `single 1 1` to `v`. -/
@[simps]
def sumSMulInv [Fintype G] {X : FDRep k G} (v : X) : (G → k) →ₗ[k] X where
  toFun f := ∑ s : G, (f s) • (X.ρ s⁻¹ v)
  map_add' _ _ := by simp [add_smul, sum_add_distrib]
  map_smul' _ _ := by simp [smul_sum, smul_smul]

omit [Finite G] in
@[simp]
lemma sumSMulInv_single_id [Fintype G] [DecidableEq G] {X : FDRep k G} (v : X) :
    ∑ s : G, (single 1 1 : G → k) s • (X.ρ s⁻¹) v = v := by
  rw [Fintype.sum_eq_single 1]
  · simp
  · simp_all

/-- For `v : X` and `G` a finite group, the representation morphism from the right
regular representation `rightFDRep` to `X` sending `single 1 1` to `v`. -/
@[simps]
def ofRightFDRep [Fintype G] (X : FDRep k G) (v : X) : rightFDRep ⟶ X where
  hom := ofHom (sumSMulInv v)
  comm t := by
    ext f
    let φ_term (X : FDRep k G) (f : G → k) v s := (f s) • (X.ρ s⁻¹ v)
    have := sum_map univ (mulRightEmbedding t⁻¹) (φ_term X (rightRegular t f) v)
    simpa [φ_term] using this

lemma toRightFDRepComp_injective {η₁ η₂ : Aut (forget k G)}
    (h : η₁.hom.hom.app rightFDRep = η₂.hom.hom.app rightFDRep) : η₁ = η₂ := by
  have := Fintype.ofFinite G
  classical
  ext X v
  have h1 := η₁.hom.hom.naturality (ofRightFDRep X v)
  have h2 := η₂.hom.hom.naturality (ofRightFDRep X v)
  rw [h, ← h2] at h1
  simpa using congr(($h1).hom (single 1 1))

/-- `leftRegular` as a morphism `rightFDRep k G ⟶ rightFDRep k G` in `FDRep k G`. -/
def leftRegularFDRepHom (s : G) : End (rightFDRep : FDRep k G) where
  hom := ofHom (leftRegular s)
  comm _ := by
    ext f
    funext _
    apply congrArg f
    exact mul_assoc ..

lemma toRightFDRepComp_in_rightRegular [IsDomain k] (η : Aut (forget k G)) :
    ∃ (s : G), (η.hom.hom.app rightFDRep).hom = rightRegular s := by
  classical
  obtain ⟨s, hs⟩ := ((evalAlgHom _ _ 1).comp (algHomOfRightFDRepComp η)).eq_piEvalAlgHom
  refine ⟨s, Basis.ext (basisFun k G) (fun u ↦ ?_)⟩
  simp only [rightFDRep, forget_obj]
  ext t
  have nat := η.hom.hom.naturality (leftRegularFDRepHom t⁻¹)
  calc
    _ = leftRegular t⁻¹ ((η.hom.hom.app rightFDRep).hom (single u 1)) 1 := by simp
    _ = (η.hom.hom.app rightFDRep).hom (leftRegular t⁻¹ (single u 1)) 1 :=
      congrFun congr(($nat.symm).hom (single u 1)) 1
    _ = evalAlgHom _ _ s (leftRegular t⁻¹ (single u 1)) :=
      congr($hs (leftRegular t⁻¹ (single u 1)))
    _ = _ := by by_cases u = t * s <;> simp_all [single_apply]

lemma equivHom_surjective [IsDomain k] : Function.Surjective (equivHom k G) := by
  intro η
  obtain ⟨s, h⟩ := toRightFDRepComp_in_rightRegular η
  exact ⟨s, toRightFDRepComp_injective (hom_ext h.symm)⟩

variable (k G) in
/-- Tannaka duality for finite groups:

A finite group `G` is isomorphic to `Aut (forget k G)`, where `k` is any integral domain,
and `forget k G` is the monoidal forgetful functor `FDRep k G ⥤ FGModuleCat k G`. -/
def equiv [IsDomain k] : G ≃* Aut (forget k G) :=
  MulEquiv.ofBijective (equivHom k G) ⟨equivHom_injective, equivHom_surjective⟩

end FiniteGroup

end TannakaDuality

end
