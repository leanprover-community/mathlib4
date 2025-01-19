/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Functoriality of group cohomology

Given a commutative ring `k`, a group homomorphism `f : G →* H`, a `k`-linear `H`-representation
`A`, a `k`-linear `G`-representation `B`, and a representation morphism `Res(f)(A) ⟶ B`, we get
a cochain map `inhomogeneousCochains A ⟶ inhomogeneousCochains B` and hence maps on
cohomology `Hⁿ(H, A) ⟶ Hⁿ(G, B)`. We use this to show a short exact sequence of representations
induces a short exact sequence of complexes of inhomogeneous cochains, allowing us to specialize
API for long exact sequences to group cohomology.

We also provide extra API for these functoriality maps in degrees 0, 1, 2.

## Main definitions

* `groupCohomology.cochainsMap f φ` is the map
`inhomogeneousCochains A ⟶ inhomogeneousCochains B`
induced by a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`.
* `groupCohomology.map f φ n` is the map `Hⁿ(H, A) ⟶ Hⁿ(G, B)` induced by a group
homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`.
-/

universe v u
variable (n : ℕ)

open CategoryTheory

lemma Fin.comp_contractNth {G H : Type*} [MulOneClass G] [MulOneClass H] (f : G →* H)
    (j : Fin (n + 1)) (g : Fin (n + 1) → G) :
    f ∘ Fin.contractNth j (· * ·) g = Fin.contractNth j (· * ·) (f ∘ g) := by
  ext x
  rcases lt_trichotomy (x : ℕ) j with (h|h|h)
  · simp only [Function.comp_apply, Fin.contractNth_apply_of_lt, h]
  · simp only [Function.comp_apply, Fin.contractNth_apply_of_eq, h, f.map_mul]
  · simp only [Function.comp_apply, Fin.contractNth_apply_of_gt, h]

namespace LinearMap

lemma ker_compLeft
    {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (I : Type*) :
    LinearMap.ker (f.compLeft I) = Submodule.pi (Set.univ : Set I) (fun _ => LinearMap.ker f) :=
  Submodule.ext fun _ => ⟨fun (hx : _ = _) i _ => congr_fun hx i,
    fun hx => funext fun i => hx i trivial⟩

lemma range_compLeft
    {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (I : Type*) :
    LinearMap.range (f.compLeft I) = Submodule.pi (Set.univ : Set I) (fun _ => LinearMap.range f) :=
  Submodule.ext fun _ => ⟨fun ⟨y, hy⟩ i _ => ⟨y i, congr_fun hy i⟩, fun hx => by
    choose y hy using hx
    exact ⟨fun i => y i trivial, funext fun i => hy i trivial⟩⟩

end LinearMap
namespace ModuleCat

variable (R : Type u) [Ring R]

end ModuleCat

namespace groupCohomology
open Rep

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
  {A : Rep k H} {B : Rep k G} (f : G →* H) (φ : (Action.res _ f).obj A ⟶ B) (n : ℕ)

open Representation

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the chain map sending `x : (Fin n → H) → A)` to `(g : Fin n → G) ↦ φ (x (f ∘ g))`. -/
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
lemma cochainsMap_id_eq_compLeft {A B : Rep k G} (f : A ⟶ B) (i : ℕ) :
    (cochainsMap (MonoidHom.id G) f).f i = ModuleCat.ofHom (f.hom.hom.compLeft _) := by
  ext
  rfl

@[simp]
lemma cochainsMap_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) :
    cochainsMap (f.comp g) ((Action.res _ g).map φ ≫ ψ) =
      cochainsMap f φ ≫ cochainsMap g ψ := by
  rfl

@[simp]
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
this is the induced map `Zⁿ(H, A) ⟶ Zⁿ(G, B)` sending `x : (Fin n → H) → A)` to
`(g : Fin n → G) ↦ φ (x (f ∘ g))`. -/
noncomputable abbrev cocyclesMap (n : ℕ) :
    groupCohomology.cocycles A n ⟶ groupCohomology.cocycles B n :=
  HomologicalComplex.cyclesMap (cochainsMap f φ) n

@[simp]
theorem cocyclesMap_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℕ) :
    cocyclesMap (MonoidHom.id G) (φ ≫ ψ) n =
      cocyclesMap (MonoidHom.id G) φ n ≫ cocyclesMap (MonoidHom.id G) ψ n := by
  simp [cocyclesMap, cochainsMap_id_comp, HomologicalComplex.cyclesMap_comp]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map `Hⁿ(H, A) ⟶ Hⁿ(G, B)` sending `x : (Fin n → H) → A)` to
`(g : Fin n → G) ↦ φ (x (f ∘ g))`. -/
noncomputable abbrev map (n : ℕ) :
    groupCohomology A n ⟶ groupCohomology B n :=
  HomologicalComplex.homologyMap (cochainsMap f φ) n

@[simp]
theorem map_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℕ) :
    map (MonoidHom.id G) (φ ≫ ψ) n =
      map (MonoidHom.id G) φ n ≫ map (MonoidHom.id G) ψ n := by
  rw [map, cochainsMap_id_comp, HomologicalComplex.homologyMap_comp]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map sending `x : H → A` to `(g : G) ↦ φ (x (f g))`. -/
abbrev fOne := φ.hom.hom.compLeft G ∘ₗ LinearMap.funLeft k A f

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map sending `x : H × H → A` to `(g₁, g₂ : G × G) ↦ φ (x (f g₁, f g₂))`. -/
abbrev fTwo := φ.hom.hom.compLeft (G × G) ∘ₗ LinearMap.funLeft k A (Prod.map f f)

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map sending `x : H × H × H → A` to
`(g₁, g₂, g₃ : G × G × G) ↦ φ (x (f g₁, f g₂, f g₃))`. -/
abbrev fThree := φ.hom.hom.compLeft (G × G × G) ∘ₗ LinearMap.funLeft k A (Prod.map f (Prod.map f f))

@[reassoc (attr := simp)]
lemma cochainsMap_f_0_comp_zeroCochainsLEquiv :
    (cochainsMap f φ).f 0 ≫ (zeroCochainsLEquiv B).toModuleIso.hom =
      (zeroCochainsLEquiv A).toModuleIso.hom ≫ φ.hom := by
  ext x
  simp only [cochainsMap_f, Unique.eq_default (f ∘ _)]
  rfl

@[reassoc (attr := simp)]
lemma cochainsMap_f_1_comp_oneCochainsLEquiv :
    (cochainsMap f φ).f 1 ≫ (oneCochainsLEquiv B).toModuleIso.hom =
      (oneCochainsLEquiv A).toModuleIso.hom ≫ ModuleCat.ofHom (fOne f φ) := by
  ext x
  simp only [cochainsMap_f, Unique.eq_default (f ∘ _)]
  rfl

@[reassoc (attr := simp)]
lemma cochainsMap_f_2_comp_twoCochainsLEquiv :
    (cochainsMap f φ).f 2 ≫ (twoCochainsLEquiv B).toModuleIso.hom =
      (twoCochainsLEquiv A).toModuleIso.hom ≫ ModuleCat.ofHom (fTwo f φ) := by
  ext x g
  show φ.hom (x _) = φ.hom (x _)
  rcongr x
  fin_cases x <;> rfl

@[reassoc (attr := simp)]
lemma cochainsMap_f_3_comp_threeCochainsLEquiv :
    (cochainsMap f φ).f 3 ≫ (threeCochainsLEquiv B).toModuleIso.hom =
      (threeCochainsLEquiv A).toModuleIso.hom ≫ ModuleCat.ofHom (fThree f φ) := by
  ext x g
  show φ.hom (x _) = φ.hom (x _)
  rcongr x
  fin_cases x <;> rfl

open ShortComplex

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is induced map `Aᴴ ⟶ Bᴳ`. -/
def H0Map : ModuleCat.of k (H0 A) ⟶ ModuleCat.of k (H0 B) :=
  ModuleCat.ofHom <| LinearMap.codRestrict _ (φ.hom.hom ∘ₗ A.ρ.invariants.subtype)
    fun ⟨c, hc⟩ g => by simpa [hc (f g)] using (hom_comm_apply φ g c).symm

@[simp]
theorem H0Map_id : H0Map (MonoidHom.id _) (𝟙 A) = 𝟙 _ := by
  rfl

@[simp]
theorem H0Map_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) :
    H0Map (f.comp g) ((Action.res _ g).map φ ≫ ψ) = H0Map f φ ≫ H0Map g ψ :=
  rfl

@[simp]
theorem H0Map_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    H0Map (MonoidHom.id G) (φ ≫ ψ) = H0Map (MonoidHom.id G) φ ≫ H0Map (MonoidHom.id G) ψ := rfl

theorem H0Map_id_eq_invariantsFunctor_map {A B : Rep k G} (f : A ⟶ B) :
    H0Map (MonoidHom.id G) f = (invariantsFunctor k G).map f := by
  rfl

instance mono_H0Map_of_mono {A B : Rep k G} (f : A ⟶ B) [Mono f] :
    Mono (H0Map (MonoidHom.id G) f) :=
  inferInstanceAs (Mono <| (invariantsFunctor k G).map f)

@[reassoc (attr := simp)]
theorem cocyclesMap_comp_isoZeroCocycles_hom :
    cocyclesMap f φ 0 ≫ (isoZeroCocycles B).hom = (isoZeroCocycles A).hom ≫ H0Map f φ := by
  rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq,
    ← cancel_mono (HomologicalComplex.iCycles _ _)]
  simp only [CochainComplex.of_x, cocyclesMap, Category.assoc, HomologicalComplex.cyclesMap_i,
    isoZeroCocycles_inv_comp_iCocycles_assoc, ModuleCat.of_coe, LinearEquiv.toModuleIso_inv_hom,
    isoZeroCocycles_inv_comp_iCocycles]
  rfl

@[reassoc (attr := simp)]
theorem map_comp_isoH0_hom :
    map f φ 0 ≫ (isoH0 B).hom = (isoH0 A).hom ≫ H0Map f φ := by
  simp [← cancel_epi (groupCohomologyπ _ _)]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map from the short complex `A --dZero--> Fun(H, A) --dOne--> Fun(H × H, A)`
to `B --dZero--> Fun(G, B) --dOne--> Fun(G × G, B)`. -/
@[simps]
def mapShortComplexH1 :
    shortComplexH1 A ⟶ shortComplexH1 B where
  τ₁ := φ.hom
  τ₂ := ModuleCat.ofHom (fOne f φ)
  τ₃ := ModuleCat.ofHom (fTwo f φ)
  comm₁₂ := by
    ext x
    funext g
    simpa [shortComplexH1, dZero, fOne] using (hom_comm_apply φ g x).symm
  comm₂₃ := by
    ext x
    funext g
    simpa [shortComplexH1, dOne, fOne, fTwo] using (hom_comm_apply φ _ _).symm

@[simp]
theorem mapShortComplexH1_zero :
    mapShortComplexH1 (A := A) (B := B) f 0 = 0 := by
  rfl

@[simp]
theorem mapShortComplexH1_id :
    mapShortComplexH1 (MonoidHom.id _) (𝟙 A) = 𝟙 _ := by
  rfl

@[simp]
theorem mapShortComplexH1_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) :
    mapShortComplexH1 (f.comp g) ((Action.res _ g).map φ ≫ ψ) =
      mapShortComplexH1 f φ ≫ mapShortComplexH1 g ψ := rfl

@[simp]
theorem mapShortComplexH1_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapShortComplexH1 (MonoidHom.id G) (φ ≫ ψ) =
      mapShortComplexH1 (MonoidHom.id G) φ ≫ mapShortComplexH1 (MonoidHom.id G) ψ := rfl

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is induced map `Z¹(H, A) ⟶ Z¹(G, B)`. -/
noncomputable abbrev mapOneCocycles :
    ModuleCat.of k (oneCocycles A) ⟶ ModuleCat.of k (oneCocycles B) :=
  ShortComplex.cyclesMap' (mapShortComplexH1 f φ) (shortComplexH1 A).moduleCatLeftHomologyData
    (shortComplexH1 B).moduleCatLeftHomologyData

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is induced map `H¹(H, A) ⟶ H¹(G, B)`. -/
noncomputable abbrev H1Map : ModuleCat.of k (H1 A) ⟶ ModuleCat.of k (H1 B) :=
  ShortComplex.leftHomologyMap' (mapShortComplexH1 f φ)
    (shortComplexH1 A).moduleCatLeftHomologyData (shortComplexH1 B).moduleCatLeftHomologyData

@[simp]
theorem H1Map_id : H1Map (MonoidHom.id _) (𝟙 A) = 𝟙 _ := by
  simp only [H1Map, shortComplexH1, mapShortComplexH1_id, leftHomologyMap'_id]
  rfl

@[simp]
theorem H1Map_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) :
    H1Map (f.comp g) ((Action.res _ g).map φ ≫ ψ) = H1Map f φ ≫ H1Map g ψ := by
  simpa [H1Map, shortComplexH1, mapShortComplexH1_comp] using leftHomologyMap'_comp _ _ _ _ _

@[simp]
theorem H1Map_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    H1Map (MonoidHom.id G) (φ ≫ ψ) = H1Map (MonoidHom.id G) φ ≫ H1Map (MonoidHom.id G) ψ :=
  H1Map_comp (MonoidHom.id G) (MonoidHom.id G) _ _

@[simp]
lemma mapOneCocycles_comp_subtype :
    mapOneCocycles f φ ≫ ModuleCat.ofHom (oneCocycles B).subtype =
      ModuleCat.ofHom (oneCocycles A).subtype ≫ ModuleCat.ofHom (fOne f φ) :=
  ShortComplex.cyclesMap'_i (mapShortComplexH1 f φ) (moduleCatLeftHomologyData _)
    (moduleCatLeftHomologyData _)

@[simp]
lemma H1π_comp_H1Map :
    H1π A ≫ H1Map f φ = mapOneCocycles f φ ≫ H1π B :=
  leftHomologyπ_naturality' (mapShortComplexH1 f φ) _ _

@[reassoc (attr := simp)]
lemma cocyclesMap_comp_isoOneCocycles_hom :
    cocyclesMap f φ 1 ≫ (isoOneCocycles B).hom =
      (isoOneCocycles A).hom ≫ mapOneCocycles f φ := by
  simp_rw [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 B)).i, mapOneCocycles,
      Category.assoc, cyclesMap'_i, isoOneCocycles, ← Category.assoc]
  simp [cochainsMap_f_1_comp_oneCochainsLEquiv f φ, mapShortComplexH1]

@[reassoc (attr := simp)]
lemma map_comp_isoH1_hom :
    map f φ 1 ≫ (isoH1 B).hom = (isoH1 A).hom ≫ H1Map f φ := by
  simp [← cancel_epi (groupCohomologyπ _ _), H1Map, Category.assoc]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map from the short complex
`Fun(H, A) --dOne--> Fun(H × H, A) --dTwo--> Fun(H × H × H, A)` to
`Fun(G, B) --dOne--> Fun(G × G, B) --dTwo--> Fun(G × G × G, B)`. -/
@[simps]
def mapShortComplexH2 :
    shortComplexH2 A ⟶ shortComplexH2 B where
  τ₁ := ModuleCat.ofHom (fOne f φ)
  τ₂ := ModuleCat.ofHom (fTwo f φ)
  τ₃ := ModuleCat.ofHom (fThree f φ)
  comm₁₂ := by
    ext x
    funext g
    simpa [shortComplexH2, dOne, fOne, fTwo] using (hom_comm_apply φ _ _).symm
  comm₂₃ := by
    ext x
    funext g
    simpa [shortComplexH2, dTwo, fTwo, fThree] using (hom_comm_apply φ _ _).symm

@[simp]
theorem mapShortComplexH2_zero :
    mapShortComplexH2 (A := A) (B := B) f 0 = 0 := rfl

@[simp]
theorem mapShortComplexH2_id :
    mapShortComplexH2 (MonoidHom.id _) (𝟙 A) = 𝟙 _ := by
  rfl

@[simp]
theorem mapShortComplexH2_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) :
    mapShortComplexH2 (f.comp g) ((Action.res _ g).map φ ≫ ψ) =
      mapShortComplexH2 f φ ≫ mapShortComplexH2 g ψ := rfl

@[simp]
theorem mapShortComplexH2_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapShortComplexH2 (MonoidHom.id G) (φ ≫ ψ) =
      mapShortComplexH2 (MonoidHom.id G) φ ≫ mapShortComplexH2 (MonoidHom.id G) ψ := rfl

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is induced map `Z²(H, A) ⟶ Z²(G, B)`. -/
noncomputable abbrev mapTwoCocycles :
    ModuleCat.of k (twoCocycles A) ⟶ ModuleCat.of k (twoCocycles B) :=
  ShortComplex.cyclesMap' (mapShortComplexH2 f φ) (shortComplexH2 A).moduleCatLeftHomologyData
    (shortComplexH2 B).moduleCatLeftHomologyData

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is induced map `H²(H, A) ⟶ H²(G, B)`. -/
noncomputable abbrev H2Map : ModuleCat.of k (H2 A) ⟶ ModuleCat.of k (H2 B) :=
  ShortComplex.leftHomologyMap' (mapShortComplexH2 f φ)
    (shortComplexH2 A).moduleCatLeftHomologyData
    (shortComplexH2 B).moduleCatLeftHomologyData

@[simp]
theorem H2Map_id : H2Map (MonoidHom.id _) (𝟙 A) = 𝟙 _ := by
  simp only [H2Map, shortComplexH2, mapShortComplexH2_id, leftHomologyMap'_id]
  rfl

@[simp]
theorem H2Map_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) :
    H2Map (f.comp g) ((Action.res _ g).map φ ≫ ψ) = H2Map f φ ≫ H2Map g ψ := by
  simpa [H2Map, shortComplexH2, mapShortComplexH2_comp] using leftHomologyMap'_comp _ _ _ _ _

@[simp]
theorem H2Map_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    H2Map (MonoidHom.id G) (φ ≫ ψ) = H2Map (MonoidHom.id G) φ ≫ H2Map (MonoidHom.id G) ψ :=
  H2Map_comp (MonoidHom.id G) (MonoidHom.id G) _ _

@[simp]
lemma mapTwoCocycles_comp_subtype :
    mapTwoCocycles f φ ≫ ModuleCat.ofHom (twoCocycles B).subtype =
      ModuleCat.ofHom (twoCocycles A).subtype ≫ ModuleCat.ofHom (fTwo f φ) :=
  ShortComplex.cyclesMap'_i (mapShortComplexH2 f φ) (moduleCatLeftHomologyData _)
    (moduleCatLeftHomologyData _)

@[simp]
lemma H2π_comp_H2Map :
    H2π A ≫ H2Map f φ = mapTwoCocycles f φ ≫ H2π B :=
  leftHomologyπ_naturality' (mapShortComplexH2 f φ) _ _

@[reassoc (attr := simp)]
lemma cocyclesMap_comp_isoTwoCocycles_hom :
    cocyclesMap f φ 2 ≫ (isoTwoCocycles B).hom = (isoTwoCocycles A).hom ≫ mapTwoCocycles f φ := by
  simp_rw [← cancel_mono (moduleCatLeftHomologyData (shortComplexH2 B)).i, mapTwoCocycles,
      Category.assoc, cyclesMap'_i, isoTwoCocycles, ← Category.assoc]
  simp [cochainsMap_f_2_comp_twoCochainsLEquiv f φ, mapShortComplexH2]

@[reassoc (attr := simp)]
lemma map_comp_isoH2_hom :
    map f φ 2 ≫ (isoH2 B).hom = (isoH2 A).hom ≫ H2Map f φ := by
  simp [← cancel_epi (groupCohomologyπ _ _), H2Map, Category.assoc]

variable (k G) in
/-- The functor sending a representation to its complex of inhomogeneous cochains. -/
@[simps]
noncomputable def cochainsFunctor : Rep k G ⥤ CochainComplex (ModuleCat k) ℕ where
  obj A := inhomogeneousCochains A
  map f := cochainsMap (MonoidHom.id _) f
  map_id _ := cochainsMap_id
  map_comp φ ψ := cochainsMap_comp (MonoidHom.id G) (MonoidHom.id G) φ ψ

instance : (cochainsFunctor k G).PreservesZeroMorphisms where
instance : (cochainsFunctor k G).Additive where

variable (k G) in
/-- The functor sending a `G`-representation `A` to `Hⁿ(G, A)`. -/
@[simps]
noncomputable def functor (n : ℕ) : Rep k G ⥤ ModuleCat k where
  obj A := groupCohomology A n
  map φ := map (MonoidHom.id _) φ n
  map_id _ := HomologicalComplex.homologyMap_id _ _
  map_comp _ _ := by
    simp only [← HomologicalComplex.homologyMap_comp]
    rfl

instance (n : ℕ) : (functor k G n).PreservesZeroMorphisms where
  map_zero _ _ := by simp [map]

variable {X : ShortComplex (Rep k G)} (hX : ShortExact X)

include hX

lemma cochainsMap_shortExact :
    ShortExact (X.map (cochainsFunctor k G)) :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => {
    exact := by
      rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
      have : LinearMap.range X.f.hom.hom = LinearMap.ker X.g.hom.hom :=
        (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
      show LinearMap.range (LinearMap.compLeft X.f.hom.hom (Fin i → G)) =
        LinearMap.ker (LinearMap.compLeft X.g.hom.hom (Fin i → G))
      rw [LinearMap.range_compLeft, LinearMap.ker_compLeft, this]
    mono_f := letI := hX.2; cochainsMap_id_f_map_mono X.f i
    epi_g := letI := hX.3; cochainsMap_id_f_map_epi X.g i }

/-- The short complex `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁) ⟶ Hʲ(G, X₂)` associated to an exact
sequence of representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev mapShortComplex₁ {i j : ℕ} (hij : i + 1 = j) :=
  ShortComplex.mk _ _ ((cochainsMap_shortExact hX).δ_comp i j hij)

variable (X) in
/-- The short complex `Hⁱ(G, X₁) ⟶ Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃)` associated to a short complex of
representations `X₁ ⟶ X₂ ⟶ X₃`. -/
noncomputable abbrev mapShortComplex₂ (i : ℕ) :=
  ShortComplex.mk (map (MonoidHom.id G) X.f i)
    (map (MonoidHom.id G) X.g i) <| by
      simp [← map_id_comp, X.zero, map]

/-- The short complex `Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)`. -/
noncomputable abbrev mapShortComplex₃ {i j : ℕ} (hij : i + 1 = j) :=
  ShortComplex.mk _ _ ((cochainsMap_shortExact hX).comp_δ i j hij)

/-- Exactness of `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁) ⟶ Hʲ(G, X₂)`. -/
lemma mapShortComplex₁_exact {i j : ℕ} (hij : i + 1 = j) :
    (mapShortComplex₁ hX hij).Exact :=
  (cochainsMap_shortExact hX).homology_exact₁ i j hij

/-- Exactness of `Hⁱ(G, X₁) ⟶ Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃)`. -/
lemma mapShortComplex₂_exact (i : ℕ) :
    (mapShortComplex₂ X i).Exact :=
  (cochainsMap_shortExact hX).homology_exact₂ i

/--  Exactness of `Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)`. -/
lemma mapShortComplex₃_exact {i j : ℕ} (hij : i + 1 = j) :
    (mapShortComplex₃ hX hij).Exact :=
  (cochainsMap_shortExact hX).homology_exact₃ i j hij

theorem δ_apply_aux {i j l : ℕ} (y : (Fin i → G) → X.X₂)
    (x : (Fin j → G) → X.X₁) (hx : X.f.hom ∘ x = (inhomogeneousCochains X.X₂).d i j y) :
    (inhomogeneousCochains X.X₁).d j l x = 0 :=
  ShortExact.δ_apply_aux (cochainsMap_shortExact hX) i j y x
    (by simpa [cochainsMap_id_eq_compLeft] using hx) l

theorem δ_apply (i j l : ℕ) (hij : i + 1 = j) (hjl : (ComplexShape.up ℕ).next j = l)
    (z : (Fin i → G) → X.X₃) (hz : (inhomogeneousCochains X.X₃).d i j z = 0)
    (y : (Fin i → G) → X.X₂) (hy : (cochainsMap (MonoidHom.id G) X.g).f i y = z)
    (x : (Fin j → G) → X.X₁) (hx : X.f.hom ∘ x = (inhomogeneousCochains X.X₂).d i j y) :
    (cochainsMap_shortExact hX).δ i j hij (groupCohomologyπ X.X₃ i <|
      (moduleCatCyclesIso _).inv ⟨z, show ((inhomogeneousCochains X.X₃).dFrom i).hom z = 0 by
        simp_all [(inhomogeneousCochains X.X₃).dFrom_eq hij]⟩) = groupCohomologyπ X.X₁ j
      ((moduleCatCyclesIso _).inv ⟨x, δ_apply_aux hX y x hx⟩) := by
  convert ShortExact.δ_apply (cochainsMap_shortExact hX) i j hij z
    hz y hy x (by simpa [cochainsMap_id_eq_compLeft] using hx) l hjl
  <;> rw [moduleCatCyclesIso_inv_apply]
  <;> rfl

/-- The degree 0 connecting homomorphism `X₃ᴳ ⟶ H¹(G, X₁)` associated to an exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations. Uses a simpler expression for `H⁰` and `H¹` than
general `δ`. -/
noncomputable def δ₀ :
    ModuleCat.of k (H0 X.X₃) ⟶ ModuleCat.of k (H1 X.X₁) :=
  (isoH0 X.X₃).inv ≫ (cochainsMap_shortExact hX).δ 0 1 rfl ≫ (isoH1 X.X₁).hom

theorem δ₀_apply_aux (y : X.X₂) (x : G → X.X₁) (hx : X.f.hom ∘ x = dZero X.X₂ y) :
    dOne X.X₁ x = 0 := by
  have hδ := δ_apply_aux hX (l := 2) ((zeroCochainsLEquiv X.X₂).symm y)
    ((oneCochainsLEquiv X.X₁).symm x)
  have hy := congr($((CommSq.horiz_inv ⟨(shortComplexH1Iso X.X₂).hom.comm₁₂⟩).w) y)
  have h := congr($((Iso.eq_inv_comp _).2 (shortComplexH1Iso X.X₁).hom.comm₂₃) x)
  have h0 := congr($((CommSq.vert_inv
    ⟨(cochainsMap_f_1_comp_oneCochainsLEquiv (MonoidHom.id G) X.f)⟩).w) x)
  simp_all [LinearMap.compLeft, shortComplexH1, MonoidHom.coe_id, ← hx]

theorem δ₀_apply (z : X.X₃) (hz : z ∈ X.X₃.ρ.invariants) (y : X.X₂) (hy : X.g.hom y = z)
    (x : G → X.X₁) (hx : X.f.hom ∘ x = dZero X.X₂ y) :
    δ₀ hX ⟨z, hz⟩ = H1π X.X₁ ⟨x, δ₀_apply_aux hX y x hx⟩ := by
  have h0z : ((inhomogeneousCochains X.X₃).d 0 1) ((zeroCochainsLEquiv X.X₃).symm z) = 0 := by
    have := congr($((CommSq.horiz_inv ⟨dZero_comp_eq X.X₃⟩).w) z)
    simp_all [← dZero_ker_eq_invariants]
  have hxy : X.f.hom ∘ (oneCochainsLEquiv X.X₁).symm x = (inhomogeneousCochains X.X₂).d 0 1
      ((zeroCochainsLEquiv X.X₂).symm y) := by
    have := congr($((CommSq.horiz_inv ⟨dZero_comp_eq X.X₂⟩).w) y)
    ext i
    simp_all [← hx, oneCochainsLEquiv]
  have δ_0_1 := congr((isoH1 X.X₁).hom
    $(δ_apply hX 0 1 2 rfl (by simp) ((zeroCochainsLEquiv X.X₃).symm z) h0z
    ((zeroCochainsLEquiv X.X₂).symm y) (hy ▸ rfl) ((oneCochainsLEquiv X.X₁).symm x) hxy))
  convert δ_0_1
  · simp only [δ₀, isoH0, Iso.trans_inv, ModuleCat.hom_comp, LinearMap.coe_comp,
      Function.comp_apply]
    rw [moduleCatCyclesIso_inv_apply, isoZeroCocycles_inv_apply_eq_cyclesMk]
    rfl
  · simp only [Iso.trans_inv, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      congr($(((Iso.inv_comp_eq _).2 (groupCohomologyπ_comp_isoH1_hom X.X₁)).symm) ⟨x, _⟩)]
    rw [isoOneCocycles_inv_apply_eq_cyclesMk, moduleCatCyclesIso_inv_apply]
    rfl

open Limits

theorem epi_δ₀_of_isZero (h1 : IsZero (ModuleCat.of k <| H1 X.X₂)) :
    Epi (δ₀ hX) := by
  letI : Epi ((cochainsMap_shortExact hX).δ 0 1 rfl) := (cochainsMap_shortExact hX).epi_δ _ _ rfl
    (h1.of_iso (isoH1 X.X₂))
  exact epi_comp _ _

/-- The degree 1 connecting homomorphism `H¹(G, X₃) ⟶ H²(G, X₁)` associated to an exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations. Uses a simpler expression for `H¹` and `H²` than
general `δ`. -/
noncomputable def δ₁ :
    ModuleCat.of k (H1 X.X₃) ⟶ ModuleCat.of k (H2 X.X₁) :=
  (isoH1 X.X₃).inv ≫ (cochainsMap_shortExact hX).δ 1 2 rfl ≫ (isoH2 X.X₁).hom

theorem δ₁_apply_aux (y : G → X.X₂) (x : G × G → X.X₁) (hx : X.f.hom ∘ x = dOne X.X₂ y) :
    dTwo X.X₁ x = 0 := by
  have hδ := δ_apply_aux hX (l := 3) ((oneCochainsLEquiv X.X₂).symm y)
    ((twoCochainsLEquiv X.X₁).symm x)
  have hy := congr($((CommSq.horiz_inv ⟨(shortComplexH2Iso X.X₂).hom.comm₁₂⟩).w) y)
  have h := congr($((Iso.eq_inv_comp _).2 (shortComplexH2Iso X.X₁).hom.comm₂₃) x)
  have h2 := congr($((CommSq.vert_inv
    ⟨(cochainsMap_f_2_comp_twoCochainsLEquiv (MonoidHom.id G) X.f)⟩).w) x)
  simp_all [LinearMap.compLeft, shortComplexH2, MonoidHom.coe_id, ← hx]

theorem δ₁_apply (z : G → X.X₃) (hz : z ∈ oneCocycles X.X₃) (y : G → X.X₂) (hy : X.g.hom ∘ y = z)
    (x : G × G → X.X₁) (hx : X.f.hom ∘ x = dOne X.X₂ y) :
    δ₁ hX (H1π X.X₃ ⟨z, hz⟩) = H2π X.X₁ ⟨x, δ₁_apply_aux hX y x hx⟩ := by
  have h1z : ((inhomogeneousCochains X.X₃).d 1 2) ((oneCochainsLEquiv X.X₃).symm z) = 0 := by
    have := congr($((CommSq.horiz_inv ⟨dOne_comp_eq X.X₃⟩).w) z)
    simp_all [oneCocycles]
  have hxy : X.f.hom ∘ (twoCochainsLEquiv X.X₁).symm x =
      (inhomogeneousCochains X.X₂).d 1 2 ((oneCochainsLEquiv X.X₂).symm y) := by
    have := congr($((CommSq.horiz_inv ⟨dOne_comp_eq X.X₂⟩).w) y)
    ext i
    simp_all [← hx, twoCochainsLEquiv]
  have δ_1_2 := congr((isoH2 X.X₁).hom
    $(δ_apply hX 1 2 3 rfl (by simp) ((oneCochainsLEquiv X.X₃).symm z) h1z
    ((oneCochainsLEquiv X.X₂).symm y) (hy ▸ rfl) ((twoCochainsLEquiv X.X₁).symm x) hxy))
  convert δ_1_2
  · show (H1π X.X₃ ≫ δ₁ hX) ⟨z, hz⟩ = _
    rw [moduleCatCyclesIso_inv_apply]
    simp [δ₁, ← Category.assoc, (CommSq.vert_inv ⟨groupCohomologyπ_comp_isoH1_hom X.X₃⟩).w,
        isoOneCocycles_inv_apply_eq_cyclesMk X.X₃ ⟨z, hz⟩, HomologicalComplex.cyclesMk,
        groupCohomology]
  · rw [moduleCatCyclesIso_inv_apply]
    simp [(Iso.eq_inv_comp _).2 (groupCohomologyπ_comp_isoH2_hom X.X₁).symm,
      -groupCohomologyπ_comp_isoH2_hom, isoTwoCocycles_inv_apply_eq_cyclesMk X.X₁ ⟨x, _⟩,
      HomologicalComplex.cyclesMk]

theorem epi_δ₁_of_isZero (h2 : IsZero (ModuleCat.of k <| H2 X.X₂)) :
    Epi (δ₁ hX) := by
  letI : Epi ((cochainsMap_shortExact hX).δ 1 2 rfl) := (cochainsMap_shortExact hX).epi_δ _ _ rfl
    (h2.of_iso (isoH2 X.X₂))
  exact epi_comp _ _

variable (X) in
/-- The short complex `X₁ᴳ ⟶ X₂ᴳ ⟶ X₃ᴳ` associated to a short complex of representations. -/
noncomputable abbrev H0ShortComplex₂ :=
  ShortComplex.mk (H0Map (MonoidHom.id G) X.f) (H0Map (MonoidHom.id G) X.g) <| by
    ext x; exact congr(Action.Hom.hom $(X.zero) x.1)

variable (X) in
/-- When `i = 0`, the general short complex `Hⁱ(G, X₁) ⟶ Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃)` associated to a
short complex of representations agrees with our simpler expression of `X₁ᴳ ⟶ X₂ᴳ ⟶ X₃ᴳ.` -/
noncomputable def isoH0ShortComplex₂ :
    mapShortComplex₂ X 0 ≅ H0ShortComplex₂ X :=
  isoMk (isoH0 _) (isoH0 _) (isoH0 _) (map_comp_isoH0_hom (MonoidHom.id G) _).symm
    (map_comp_isoH0_hom (MonoidHom.id G) _).symm

theorem H0ShortComplex₂_exact :
    (H0ShortComplex₂ X).Exact :=
  exact_of_iso (isoH0ShortComplex₂ X) (mapShortComplex₂_exact hX _)

/-- The short complex `X₂ᴳ ⟶ X₃ᴳ ⟶ H¹(G, X₁)` associated to a short exact sequence of
representations. -/
noncomputable abbrev H0ShortComplex₃ (H : ShortExact X) :=
  ShortComplex.mk (H0Map (MonoidHom.id G) X.g) (δ₀ H) <| by
    rw [δ₀, ← Category.assoc, (CommSq.vert_inv ⟨map_comp_isoH0_hom
       (MonoidHom.id G) X.g⟩).w]
    simpa using (cochainsMap_shortExact H).comp_δ_assoc 0 1 rfl _

/-- When `i = 0`, the general short complex `Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃) ⟶ Hⁱ⁺¹(G, X₁)` associated to a
short exact sequence of representations agrees with our simpler expression for
`X₂ᴳ ⟶ X₃ᴳ ⟶ H¹(G, X₁).` -/
noncomputable def isoH0ShortComplex₃ (H : ShortExact X) :
    mapShortComplex₃ H (j := 1) rfl ≅ H0ShortComplex₃ H :=
  isoMk (isoH0 _) (isoH0 _) (isoH1 _)
    (map_comp_isoH0_hom (MonoidHom.id G) _).symm (by simp [δ₀])

theorem H0ShortComplex₃_exact :
    (H0ShortComplex₃ hX).Exact :=
  exact_of_iso (isoH0ShortComplex₃ hX) (mapShortComplex₃_exact hX _)

/-- The short complex  `X₃ᴳ ⟶ H¹(G, X₁) ⟶ H¹(G, X₂)` associated to a short exact sequence of
representations. -/
noncomputable abbrev H1ShortComplex₁ :=
  ShortComplex.mk (δ₀ hX) (H1Map (MonoidHom.id G) X.f) <| by
    simpa [δ₀, ← map_comp_isoH1_hom]
      using (cochainsMap_shortExact hX).δ_comp_assoc 0 1 rfl _

/-- When `i = 0`, the general short complex `Hⁱ(G, X₃) ⟶ Hⁱ⁺¹(G, X₁) ⟶ Hⁱ⁺¹(G, X₂)` associated to
a short exact sequence of representations agrees with our simpler expression for
`X₃ᴳ ⟶ H¹(G, X₁) ⟶ H¹(G, X₂).` -/
noncomputable def isoH1ShortComplex₁ :
    mapShortComplex₁ hX (i := 0) rfl ≅ H1ShortComplex₁ hX :=
  isoMk (isoH0 _) (isoH1 _) (isoH1 _) (by simp [δ₀])
    (map_comp_isoH1_hom (MonoidHom.id G) _).symm

theorem H1ShortComplex₁_exact :
    (H1ShortComplex₁ hX).Exact :=
  exact_of_iso (isoH1ShortComplex₁ hX) (mapShortComplex₁_exact _ _)

variable (X) in
/-- The short complex  `H¹(G, X₁) ⟶ H¹(G, X₂) ⟶ H¹(G, X₃)` associated to a short complex of
representations. -/
noncomputable abbrev H1ShortComplex₂ :=
  ShortComplex.mk (H1Map (MonoidHom.id G) X.f) (H1Map (MonoidHom.id G) X.g) <| by
    rw [← H1Map_id_comp, X.zero]; exact leftHomologyMap'_zero _ _

variable (X) in
/-- When `i = 1`, the general short complex `Hⁱ(G, X₁) ⟶ Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃)` associated to
a short complex of representations agrees with our simpler expression for
`H¹(G, X₁) ⟶ H¹(G, X₂) ⟶ H¹(G, X₃).` -/
noncomputable def isoH1ShortComplex₂ :
    mapShortComplex₂ X 1 ≅ H1ShortComplex₂ X :=
  isoMk (isoH1 _) (isoH1 _) (isoH1 _) (map_comp_isoH1_hom (MonoidHom.id G) _).symm
    (map_comp_isoH1_hom (MonoidHom.id G) _).symm

theorem H1ShortComplex₂_exact :
    (H1ShortComplex₂ X).Exact :=
  exact_of_iso (isoH1ShortComplex₂ X) (mapShortComplex₂_exact hX _)

/-- The short complex  `H¹(G, X₂) ⟶ H¹(G, X₃) ⟶ H²(G, X₁)` associated to a short exact sequence of
representations. -/
noncomputable abbrev H1ShortComplex₃ :=
  ShortComplex.mk (H1Map (MonoidHom.id G) X.g) (δ₁ hX) <| by
    rw [δ₁, ← Category.assoc, (CommSq.vert_inv ⟨map_comp_isoH1_hom
      (MonoidHom.id G) X.g⟩).w]
    simpa using (cochainsMap_shortExact hX).comp_δ_assoc 1 2 rfl _

/-- When `i = 1`, the general short complex `Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃) ⟶ Hⁱ⁺¹(G, X₁)` associated to
a short exact sequence of representations agrees with our simpler expression for
`H¹(G, X₂) ⟶ H¹(G, X₃) ⟶ H²(G, X₁).` -/
noncomputable def isoH1ShortComplex₃ :
    mapShortComplex₃ hX (i := 1) rfl ≅ H1ShortComplex₃ hX :=
  isoMk (isoH1 _) (isoH1 _) (isoH2 _)
    (map_comp_isoH1_hom (MonoidHom.id G) _).symm (by simp [δ₁])

theorem H1ShortComplex₃_exact :
    (H1ShortComplex₃ hX).Exact :=
  exact_of_iso (isoH1ShortComplex₃ hX) (mapShortComplex₃_exact _ _)

/-- The short complex  `H¹(G, X₃) ⟶ H²(G, X₁) ⟶ H²(G, X₂)` associated to a short exact
sequence of representations. -/
noncomputable abbrev H2ShortComplex₁ :=
  ShortComplex.mk (δ₁ hX) (H2Map (MonoidHom.id G) X.f) <| by
    simpa [δ₁, ← map_comp_isoH2_hom]
      using (cochainsMap_shortExact hX).δ_comp_assoc 1 2 rfl _

/-- When `i = 1`, the general short complex `Hⁱ(G, X₃) ⟶ Hⁱ⁺¹(G, X₁) ⟶ Hⁱ⁺¹(G, X₂)` associated to
a short exact sequence of representations agrees with our simpler expression for
`H¹(G, X₃) ⟶ H²(G, X₁) ⟶ H²(G, X₂).` -/
noncomputable def isoH2ShortComplex₁ :
    mapShortComplex₁ hX (i := 1) rfl ≅ H2ShortComplex₁ hX :=
  isoMk (isoH1 _) (isoH2 _) (isoH2 _) (by simp [δ₁])
    (map_comp_isoH2_hom (MonoidHom.id G) _).symm

theorem H2ShortComplex₁_exact :
    (H2ShortComplex₁ hX).Exact :=
  exact_of_iso (isoH2ShortComplex₁ hX) (mapShortComplex₁_exact _ _)

end groupCohomology
