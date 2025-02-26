/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.RepresentationTheory.GroupCohomology.Basic
import Mathlib.RepresentationTheory.GroupCohomology.LowDegree

/-!
# Functoriality of group cohomology

Given a commutative ring `k`, a group homomorphism `f : G →* H`, a `k`-linear `H`-representation
`A`, a `k`-linear `G`-representation `B`, and a representation morphism `Res(f)(A) ⟶ B`, we get
a cochain map `inhomogeneousCochains A ⟶ inhomogeneousCochains B` and hence maps on
cohomology `Hⁿ(H, A) ⟶ Hⁿ(G, B)`.
We also provide extra API for these maps in degrees 0, 1, 2.

## Main definitions

* `groupCohomology.cochainsMap f φ` is the map `inhomogeneousCochains A ⟶ inhomogeneousCochains B`
induced by a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`.
* `groupCohomology.map f φ n` is the map `Hⁿ(H, A) ⟶ Hⁿ(G, B)` induced by a group
homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`.
-/

universe v u

namespace groupCohomology
open Rep CategoryTheory Representation

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
  {A : Rep k H} {B : Rep k G} (f : G →* H) (φ : (Action.res _ f).obj A ⟶ B) (n : ℕ)

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the chain map sending `x : Hⁿ → A` to `(g : Gⁿ) ↦ φ (x (f ∘ g))`. -/
@[simps! (config := .lemmasOnly) f f_hom]
noncomputable def cochainsMap :
    inhomogeneousCochains A ⟶ inhomogeneousCochains B where
  f i := ModuleCat.ofHom <|
    φ.hom.hom.compLeft (Fin i → G) ∘ₗ LinearMap.funLeft k A (fun x : Fin i → G => (f ∘ x))
  comm' i j (hij : _ = _) := by
    subst hij
    ext
    funext
    simpa [inhomogeneousCochains.d_apply, Fin.comp_contractNth] using (hom_comm_apply φ _ _).symm

@[simp]
lemma cochainsMap_id :
    cochainsMap (MonoidHom.id _) (𝟙 A) = 𝟙 (inhomogeneousCochains A) := by
  rfl

@[simp]
lemma cochainsMap_id_f_eq_compLeft {A B : Rep k G} (f : A ⟶ B) (i : ℕ) :
    (cochainsMap (MonoidHom.id G) f).f i = ModuleCat.ofHom (f.hom.hom.compLeft _) := by
  ext
  rfl

lemma cochainsMap_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) :
    cochainsMap (f.comp g) ((Action.res _ g).map φ ≫ ψ) =
      cochainsMap f φ ≫ cochainsMap g ψ := by
  rfl

lemma cochainsMap_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    cochainsMap (MonoidHom.id G) (φ ≫ ψ) =
      cochainsMap (MonoidHom.id G) φ ≫ cochainsMap (MonoidHom.id G) ψ := by
  rfl

@[simp]
lemma cochainsMap_zero : cochainsMap (A := A) (B := B) f 0 = 0 := by rfl

lemma cochainsMap_f_map_mono (hf : Function.Surjective f) [Mono φ] (i : ℕ) :
    Mono ((cochainsMap f φ).f i) := by
  simpa [ModuleCat.mono_iff_injective] using
    ((Rep.mono_iff_injective φ).1 inferInstance).comp_left.comp <|
    LinearMap.funLeft_injective_of_surjective k A _ hf.comp_left

instance cochainsMap_id_f_map_mono {A B : Rep k G} (φ : A ⟶ B) [Mono φ] (i : ℕ) :
    Mono ((cochainsMap (MonoidHom.id G) φ).f i) :=
  cochainsMap_f_map_mono (MonoidHom.id G) φ (fun x => ⟨x, rfl⟩) i

lemma cochainsMap_f_map_epi (hf : Function.Injective f) [Epi φ] (i : ℕ) :
    Epi ((cochainsMap f φ).f i) := by
  simpa [ModuleCat.epi_iff_surjective] using
    ((Rep.epi_iff_surjective φ).1 inferInstance).comp_left.comp <|
    LinearMap.funLeft_surjective_of_injective k A _ hf.comp_left

instance cochainsMap_id_f_map_epi {A B : Rep k G} (φ : A ⟶ B) [Epi φ] (i : ℕ) :
    Epi ((cochainsMap (MonoidHom.id G) φ).f i) :=
  cochainsMap_f_map_epi (MonoidHom.id G) φ (fun _ _ h => h) i

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map `Zⁿ(H, A) ⟶ Zⁿ(G, B)` sending `x : Hⁿ → A` to
`(g : Gⁿ) ↦ φ (x (f ∘ g))`. -/
noncomputable abbrev cocyclesMap (n : ℕ) :
    groupCohomology.cocycles A n ⟶ groupCohomology.cocycles B n :=
  HomologicalComplex.cyclesMap (cochainsMap f φ) n

theorem cocyclesMap_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℕ) :
    cocyclesMap (MonoidHom.id G) (φ ≫ ψ) n =
      cocyclesMap (MonoidHom.id G) φ n ≫ cocyclesMap (MonoidHom.id G) ψ n := by
  simp [cocyclesMap, cochainsMap_id_comp, HomologicalComplex.cyclesMap_comp]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map `Hⁿ(H, A) ⟶ Hⁿ(G, B)` sending `x : Hⁿ → A` to
`(g : Gⁿ) ↦ φ (x (f ∘ g))`. -/
noncomputable abbrev map (n : ℕ) :
    groupCohomology A n ⟶ groupCohomology B n :=
  HomologicalComplex.homologyMap (cochainsMap f φ) n

theorem map_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℕ) :
    map (MonoidHom.id G) (φ ≫ ψ) n =
      map (MonoidHom.id G) φ n ≫ map (MonoidHom.id G) ψ n := by
  rw [map, cochainsMap_id_comp, HomologicalComplex.homologyMap_comp]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map sending `x : H → A` to `(g : G) ↦ φ (x (f g))`. -/
abbrev fOne : (H → A) →ₗ[k] (G → B) := φ.hom.hom.compLeft G ∘ₗ LinearMap.funLeft k A f

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map sending `x : H × H → A` to `(g₁, g₂ : G × G) ↦ φ (x (f g₁, f g₂))`. -/
abbrev fTwo : (H × H → A) →ₗ[k] (G × G → B) :=
  φ.hom.hom.compLeft (G × G) ∘ₗ LinearMap.funLeft k A (Prod.map f f)

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map sending `x : H × H × H → A` to
`(g₁, g₂, g₃ : G × G × G) ↦ φ (x (f g₁, f g₂, f g₃))`. -/
abbrev fThree : (H × H × H → A) →ₗ[k] (G × G × G → B) :=
  φ.hom.hom.compLeft (G × G × G) ∘ₗ LinearMap.funLeft k A (Prod.map f (Prod.map f f))

@[reassoc]
lemma cochainsMap_f_0_comp_zeroCochainsLequiv :
    (cochainsMap f φ).f 0 ≫ (zeroCochainsLequiv B).toModuleIso.hom =
      (zeroCochainsLequiv A).toModuleIso.hom ≫ φ.hom := by
  ext x
  simp only [cochainsMap_f, Unique.eq_default (f ∘ _)]
  rfl

@[reassoc]
lemma cochainsMap_f_1_comp_oneCochainsLequiv :
    (cochainsMap f φ).f 1 ≫ (oneCochainsLequiv B).toModuleIso.hom =
      (oneCochainsLequiv A).toModuleIso.hom ≫ ModuleCat.ofHom (fOne f φ) := by
  ext x
  simp only [cochainsMap_f, Unique.eq_default (f ∘ _)]
  rfl

@[reassoc]
lemma cochainsMap_f_2_comp_twoCochainsLequiv :
    (cochainsMap f φ).f 2 ≫ (twoCochainsLequiv B).toModuleIso.hom =
      (twoCochainsLequiv A).toModuleIso.hom ≫ ModuleCat.ofHom (fTwo f φ) := by
  ext x g
  show φ.hom (x _) = φ.hom (x _)
  rcongr x
  fin_cases x <;> rfl

@[reassoc]
lemma cochainsMap_f_3_comp_threeCochainsLequiv :
    (cochainsMap f φ).f 3 ≫ (threeCochainsLequiv B).toModuleIso.hom =
      (threeCochainsLequiv A).toModuleIso.hom ≫ ModuleCat.ofHom (fThree f φ) := by
  ext x g
  show φ.hom (x _) = φ.hom (x _)
  rcongr x
  fin_cases x <;> rfl

end groupCohomology
