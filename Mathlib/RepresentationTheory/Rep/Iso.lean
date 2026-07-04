/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Equivalence between `Rep k G` and `ModuleCat k[G]`

In this file we show that the category of `k`-linear representations of a monoid `G` is
equivalent to the category of modules over the monoid algebra `k[G]`.
-/

@[expose] public section

universe w w' u u' v v'

namespace Rep

open CategoryTheory
open scoped MonoidAlgebra

suppress_compilation

section Group

variable (k G H : Type u) [Group G] [Monoid H] [MulAction G H] [CommRing k] (n : ℕ)

open MonoidalCategory Finsupp Representation.IntertwiningMap

/-- An isomorphism of `k`-linear representations of `G` from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` (on
which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) sending `(g₀, ..., gₙ)` to
`g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. The inverse sends `g₀ ⊗ (g₁, ..., gₙ)` to
`(g₀, g₀g₁, ..., g₀g₁...gₙ)`. -/
abbrev diagonalSuccIsoTensorTrivial :
    diagonal k G (n + 1) ≅ leftRegular k G ⊗ trivial k G k[Fin n → G] :=
  linearizationOfMulActionIso k G (Fin (n + 1) → G) ≪≫ (linearization k G).mapIso
    (Action.diagonalSuccIsoTensorTrivial G n) ≪≫
    (Functor.Monoidal.μIso (linearization k G) _ _).symm ≪≫
    tensorIso (linearizationOfMulActionIso k G G) (linearizationTrivialIso k G (Fin n → G))

/-- Representation isomorphism `k[Gⁿ⁺¹] ≅ (Gⁿ →₀ k[G])`, where the right-hand representation is
defined pointwise by the left regular representation on `k[G]`. The map sends
`single (g₀, ..., gₙ) a ↦ single (g₀⁻¹g₁, ..., gₙ₋₁⁻¹gₙ) (single g₀ a)`. -/
abbrev diagonalSuccIsoFree : diagonal k G (n + 1) ≅ free k G (Fin n → G) :=
  diagonalSuccIsoTensorTrivial k G n ≪≫ leftRegularTensorTrivialIsoFree k G (Fin n → G)

variable (A : Rep k G)

/-- Given a `k`-linear `G`-representation `A`, the set of representation morphisms
`Hom(k[Gⁿ⁺¹], A)` is `k`-linearly isomorphic to the set of functions `Gⁿ → A`. -/
abbrev diagonalHomEquiv :
    (Rep.diagonal k G (n + 1) ⟶ A) ≃ₗ[k] (Fin n → G) → A :=
  Linear.homCongr k (diagonalSuccIsoFree k G n) (Iso.refl _) ≪≫ₗ
    freeLiftLEquiv k G (Fin n → G) A

end Group

/-!
### The categorical equivalence `Rep k G ≌ Module.{u} k[G]`.
-/


variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

open MonoidAlgebra

/-- Auxiliary lemma for `toModuleMonoidAlgebra`. -/
theorem to_Module_monoidAlgebra_map_aux {k G : Type*} [CommRing k] [Monoid G] (V W : Type*)
    [AddCommGroup V] [AddCommGroup W] [Module k V] [Module k W] (ρ : G →* V →ₗ[k] V)
    (σ : G →* W →ₗ[k] W) (f : V →ₗ[k] W) (w : ∀ g : G, f.comp (ρ g) = (σ g).comp f)
    (r : k[G]) (x : V) :
    f (MonoidAlgebra.lift k (V →ₗ[k] V) G ρ r x) =
      MonoidAlgebra.lift k (W →ₗ[k] W) G σ r (f x) := by
  apply MonoidAlgebra.induction_on r
  · intro g
    simp only [one_smul, MonoidAlgebra.lift_single, MonoidAlgebra.of_apply]
    exact LinearMap.congr_fun (w g) x
  · intro g h gw hw; simp only [map_add, LinearMap.add_apply, hw, gw]
  · intro r g w
    simp only [map_smul, w, LinearMap.smul_apply]

/-- Auxiliary definition for `toModuleMonoidAlgebra`. -/
def toModuleMonoidAlgebraMap {V W : Rep.{w} k G} (f : V ⟶ W) :
    ModuleCat.of k[G] V.ρ.asModule ⟶ ModuleCat.of k[G] W.ρ.asModule :=
  ModuleCat.ofHom
    { f.hom.toLinearMap with
      map_smul' := fun r x => to_Module_monoidAlgebra_map_aux V.V W.V V.ρ W.ρ
        f.hom.toLinearMap f.hom.2 r x }

/-- Functorially convert a representation of `G` into a module over `k[G]`. -/
def toModuleMonoidAlgebra : Rep.{w} k G ⥤ ModuleCat k[G] where
  obj V := ModuleCat.of _ V.ρ.asModule
  map f := toModuleMonoidAlgebraMap f

set_option backward.isDefEq.respectTransparency false in
/-- Functorially convert a module over `k[G]` into a representation of `G`. -/
def ofModuleMonoidAlgebra : ModuleCat k[G] ⥤ Rep.{w} k G where
  obj M := Rep.of (Representation.ofModule M)
  map f := ofHom {
    __ := f.hom
    map_smul' r x := f.hom.map_smul (algebraMap k _ r) x
    isIntertwining' g := by ext; apply f.hom.map_smul
  }

theorem ofModuleMonoidAlgebra_obj_coe (M : ModuleCat.{w} k[G]) :
    ofModuleMonoidAlgebra.obj M = RestrictScalars k k[G] M :=
  rfl

theorem ofModuleMonoidAlgebra_obj_ρ (M : ModuleCat.{w} k[G]) :
    (ofModuleMonoidAlgebra.obj M).ρ = Representation.ofModule M :=
  rfl

/-- Auxiliary definition for `equivalenceModuleMonoidAlgebra`. -/
def counitIsoAddEquiv {M : ModuleCat.{w} k[G]} :
    (ofModuleMonoidAlgebra ⋙ toModuleMonoidAlgebra).obj M ≃+ M := by
  dsimp [ofModuleMonoidAlgebra, toModuleMonoidAlgebra]
  exact (Representation.ofModule M).asModuleEquiv.toAddEquiv.trans
    (RestrictScalars.addEquiv k k[G] _)

set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `equivalenceModuleMonoidAlgebra`. -/
def unitIsoAddEquiv {V : Rep.{w} k G} : V ≃+ (toModuleMonoidAlgebra ⋙
    ofModuleMonoidAlgebra).obj V := by
  dsimp [ofModuleMonoidAlgebra, toModuleMonoidAlgebra]
  exact V.ρ.asModuleEquiv.symm.toAddEquiv.trans (RestrictScalars.addEquiv _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `equivalenceModuleMonoidAlgebra`. -/
def counitIso (M : ModuleCat.{w} k[G]) :
    (ofModuleMonoidAlgebra ⋙ toModuleMonoidAlgebra).obj M ≅ M :=
  LinearEquiv.toModuleIso
    { counitIsoAddEquiv with
      map_smul' := fun r x => by
        simp [counitIsoAddEquiv] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem unit_iso_comm (V : Rep.{w} k G) (g : G) (x : V) :
    unitIsoAddEquiv ((V.ρ g).toFun x) = ((ofModuleMonoidAlgebra.obj
      (toModuleMonoidAlgebra.obj V)).ρ g).toFun (unitIsoAddEquiv x) := by
  simp [unitIsoAddEquiv, ofModuleMonoidAlgebra, toModuleMonoidAlgebra]

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `equivalenceModuleMonoidAlgebra`. -/
def unitIso (V : Rep.{w} k G) : V ≅ (toModuleMonoidAlgebra ⋙ ofModuleMonoidAlgebra).obj V :=
  mkIso <| .mk
  { unitIsoAddEquiv (k := k) (G := G) with
    map_smul' r x := show (RestrictScalars.addEquiv _ _ _).symm
      (V.ρ.asModuleEquiv.symm (r • x)) = _ by
      simp only [Representation.asModuleEquiv_symm_map_smul]
      rfl } fun g ↦ by ext; exact unit_iso_comm ..

/-- The categorical equivalence `Rep k G ≌ ModuleCat k[G]`. -/
def equivalenceModuleMonoidAlgebra : Rep.{w} k G ≌ ModuleCat k[G] where
  functor := toModuleMonoidAlgebra
  inverse := ofModuleMonoidAlgebra
  unitIso := NatIso.ofComponents (fun V => unitIso V) (by cat_disch)
  counitIso := NatIso.ofComponents (fun M => counitIso M) (by cat_disch)

instance : (toModuleMonoidAlgebra.{w} (k := k) (G := G)).IsEquivalence :=
  (equivalenceModuleMonoidAlgebra (k := k) (G := G)).isEquivalence_functor

instance : (ofModuleMonoidAlgebra (k := k) (G := G)).IsEquivalence :=
  (equivalenceModuleMonoidAlgebra (k := k) (G := G)).isEquivalence_inverse

instance : Abelian (Rep.{w} k G) := abelianOfEquivalence toModuleMonoidAlgebra

-- TODO Verify that the equivalence with `ModuleCat k[G]` is a monoidal functor.

variable {k G : Type u} [CommRing k] [Monoid G] in
instance : CategoryTheory.EnoughProjectives (Rep.{max w u} k G) :=
  equivalenceModuleMonoidAlgebra.enoughProjectives_iff.2 ModuleCat.enoughProjectives.{max w u}

instance free_projective {α : Type (max w u)} :
    Projective (free k G α) :=
  equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective _ <|
    @ModuleCat.projective_of_free _ _
      (ModuleCat.of k[G] (Representation.free k G α).asModule)
      _ (Representation.freeAsModuleBasis k G α)

section

variable {G : Type u} [Group G] {n : ℕ}

instance diagonal_succ_projective :
    Projective (diagonal k G (n + 1)) := by
  classical
  exact Projective.of_iso (diagonalSuccIsoFree k G n).symm inferInstance

instance leftRegular_projective :
    Projective (leftRegular k G) :=
  Projective.of_iso (diagonalOneIsoLeftRegular k G) inferInstance

instance trivial_projective_of_subsingleton [Subsingleton G] :
    Projective (trivial k G k) :=
  Projective.of_iso (ofMulActionSubsingletonIsoTrivial _ _ (Fin 1 → G)) diagonal_succ_projective

end

end Rep
