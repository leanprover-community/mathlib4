/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.RepresentationTheory.GroupCohomology.Basic
import Mathlib.RepresentationTheory.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.GroupCohomology.ToMove

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
@[simps! -isSimp f f_hom]
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

@[reassoc]
lemma cochainsMap_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) :
    cochainsMap (f.comp g) ((Action.res _ g).map φ ≫ ψ) =
      cochainsMap f φ ≫ cochainsMap g ψ := by
  rfl

@[reassoc]
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

@[reassoc]
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

@[reassoc]
theorem map_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℕ) :
    map (MonoidHom.id G) (φ ≫ ψ) n =
      map (MonoidHom.id G) φ n ≫ map (MonoidHom.id G) ψ n := by
  rw [map, cochainsMap_id_comp, HomologicalComplex.homologyMap_comp]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map sending `x : H → A` to `(g : G) ↦ φ (x (f g))`. -/
noncomputable abbrev fOne : (H → A) →ₗ[k] (G → B) := φ.hom.hom.compLeft G ∘ₗ LinearMap.funLeft k A f

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map sending `x : H × H → A` to `(g₁, g₂ : G × G) ↦ φ (x (f g₁, f g₂))`. -/
noncomputable abbrev fTwo : (H × H → A) →ₗ[k] (G × G → B) :=
  φ.hom.hom.compLeft (G × G) ∘ₗ LinearMap.funLeft k A (Prod.map f f)

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map sending `x : H × H × H → A` to
`(g₁, g₂, g₃ : G × G × G) ↦ φ (x (f g₁, f g₂, f g₃))`. -/
noncomputable abbrev fThree : (H × H × H → A) →ₗ[k] (G × G × G → B) :=
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

open ShortComplex

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is induced map `Aᴴ ⟶ Bᴳ`. -/
noncomputable abbrev H0Map : H0 A ⟶ H0 B :=
  ModuleCat.ofHom <| LinearMap.codRestrict _ (φ.hom.hom ∘ₗ A.ρ.invariants.subtype)
    fun ⟨c, hc⟩ g => by simpa [hc (f g)] using (hom_comm_apply φ g c).symm

@[simp]
theorem H0Map_id : H0Map (MonoidHom.id _) (𝟙 A) = 𝟙 _ := by
  rfl

@[reassoc]
theorem H0Map_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) :
    H0Map (f.comp g) ((Action.res _ g).map φ ≫ ψ) = H0Map f φ ≫ H0Map g ψ :=
  rfl

@[reassoc]
theorem H0Map_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    H0Map (MonoidHom.id G) (φ ≫ ψ) = H0Map (MonoidHom.id G) φ ≫ H0Map (MonoidHom.id G) ψ := rfl

theorem H0Map_id_eq_invariantsFunctor_map {A B : Rep k G} (f : A ⟶ B) :
    H0Map (MonoidHom.id G) f = (invariantsFunctor k G).map f := by
  rfl

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma H0Map_comp_f :
    H0Map f φ ≫ (shortComplexH0 B).f = (shortComplexH0 A).f ≫ φ.hom := by
  ext
  simp [shortComplexH0]

instance mono_H0Map_of_mono {A B : Rep k G} (f : A ⟶ B) [Mono f] :
    Mono (H0Map (MonoidHom.id G) f) :=
  (ModuleCat.mono_iff_injective _).2 fun _ _ hxy => Subtype.ext <|
    (mono_iff_injective f).1 ‹_› (Subtype.ext_iff.1 hxy)

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem cocyclesMap_comp_isoZeroCocycles_hom :
    cocyclesMap f φ 0 ≫ (isoZeroCocycles B).hom = (isoZeroCocycles A).hom ≫ H0Map f φ := by
  have := cochainsMap_f_0_comp_zeroCochainsLequiv f φ
  simp_all [← cancel_mono (shortComplexH0 B).f]

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem map_comp_isoH0_hom :
    map f φ 0 ≫ (isoH0 B).hom = (isoH0 A).hom ≫ H0Map f φ := by
  simp [← cancel_epi (groupCohomologyπ _ _)]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map from the short complex `A --dZero--> Fun(H, A) --dOne--> Fun(H × H, A)`
to `B --dZero--> Fun(G, B) --dOne--> Fun(G × G, B)`. -/
@[simps]
noncomputable def mapShortComplexH1 :
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

@[reassoc]
theorem mapShortComplexH1_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) :
    mapShortComplexH1 (f.comp g) ((Action.res _ g).map φ ≫ ψ) =
      mapShortComplexH1 f φ ≫ mapShortComplexH1 g ψ := rfl

@[reassoc]
theorem mapShortComplexH1_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapShortComplexH1 (MonoidHom.id G) (φ ≫ ψ) =
      mapShortComplexH1 (MonoidHom.id G) φ ≫ mapShortComplexH1 (MonoidHom.id G) ψ := rfl

variable (k G) in
@[simps]
noncomputable def shortComplexH1Functor : Rep k G ⥤ ShortComplex (ModuleCat k) where
  obj := shortComplexH1
  map := mapShortComplexH1 (MonoidHom.id G)

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is induced map `Z¹(H, A) ⟶ Z¹(G, B)`. -/
noncomputable abbrev mapOneCocycles :
    ModuleCat.of k (oneCocycles A) ⟶ ModuleCat.of k (oneCocycles B) :=
  ShortComplex.cyclesMap' (mapShortComplexH1 f φ) (shortComplexH1 A).moduleCatLeftHomologyData
    (shortComplexH1 B).moduleCatLeftHomologyData

@[reassoc, elementwise]
lemma mapOneCocycles_comp_i :
    mapOneCocycles f φ ≫ (shortComplexH1 B).moduleCatLeftHomologyData.i =
      (shortComplexH1 A).moduleCatLeftHomologyData.i ≫ ModuleCat.ofHom (fOne f φ) := by
  simp

@[deprecated (since := "2025-05-09")]
alias mapOneCocycles_comp_subtype := mapOneCocycles_comp_i

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma cocyclesMap_comp_isoOneCocycles_hom :
    cocyclesMap f φ 1 ≫ (isoOneCocycles B).hom = (isoOneCocycles A).hom ≫ mapOneCocycles f φ := by
  simp [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 B)).i, mapShortComplexH1,
    cochainsMap_f_1_comp_oneCochainsLequiv f, ← LinearEquiv.toModuleIso_hom]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is induced map `H¹(H, A) ⟶ H¹(G, B)`. -/
noncomputable abbrev H1Map : H1 A ⟶ H1 B :=
  ShortComplex.leftHomologyMap' (mapShortComplexH1 f φ)
    (shortComplexH1 A).moduleCatLeftHomologyData (shortComplexH1 B).moduleCatLeftHomologyData

@[simp]
theorem H1Map_id : H1Map (MonoidHom.id _) (𝟙 A) = 𝟙 _ := by
  simp only [H1Map, shortComplexH1, mapShortComplexH1_id, leftHomologyMap'_id]
  rfl

@[reassoc]
theorem H1Map_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) :
    H1Map (f.comp g) ((Action.res _ g).map φ ≫ ψ) = H1Map f φ ≫ H1Map g ψ := by
  simpa [H1Map, shortComplexH1, mapShortComplexH1_comp] using leftHomologyMap'_comp ..

@[reassoc]
theorem H1Map_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    H1Map (MonoidHom.id G) (φ ≫ ψ) = H1Map (MonoidHom.id G) φ ≫ H1Map (MonoidHom.id G) ψ :=
  H1Map_comp (MonoidHom.id G) (MonoidHom.id G) _ _

@[reassoc, elementwise]
lemma H1π_comp_H1Map :
    H1π A ≫ H1Map f φ = mapOneCocycles f φ ≫ H1π B := by
  simp

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma map_comp_isoH1_hom :
    map f φ 1 ≫ (isoH1 B).hom = (isoH1 A).hom ≫ H1Map f φ := by
  simp [← cancel_epi (groupCohomologyπ _ _), H1Map, Category.assoc]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map from the short complex
`Fun(H, A) --dOne--> Fun(H × H, A) --dTwo--> Fun(H × H × H, A)` to
`Fun(G, B) --dOne--> Fun(G × G, B) --dTwo--> Fun(G × G × G, B)`. -/
@[simps]
noncomputable def mapShortComplexH2 :
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

@[reassoc]
theorem mapShortComplexH2_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) :
    mapShortComplexH2 (f.comp g) ((Action.res _ g).map φ ≫ ψ) =
      mapShortComplexH2 f φ ≫ mapShortComplexH2 g ψ := rfl

@[reassoc]
theorem mapShortComplexH2_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapShortComplexH2 (MonoidHom.id G) (φ ≫ ψ) =
      mapShortComplexH2 (MonoidHom.id G) φ ≫ mapShortComplexH2 (MonoidHom.id G) ψ := rfl

variable (k G) in
@[simps]
noncomputable def shortComplexH2Functor : Rep k G ⥤ ShortComplex (ModuleCat k) where
  obj := shortComplexH2
  map := mapShortComplexH2 (MonoidHom.id G)

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is induced map `Z²(H, A) ⟶ Z²(G, B)`. -/
noncomputable abbrev mapTwoCocycles :
    ModuleCat.of k (twoCocycles A) ⟶ ModuleCat.of k (twoCocycles B) :=
  ShortComplex.cyclesMap' (mapShortComplexH2 f φ) (shortComplexH2 A).moduleCatLeftHomologyData
    (shortComplexH2 B).moduleCatLeftHomologyData

@[reassoc, elementwise]
lemma mapTwoCocycles_comp_i :
    mapTwoCocycles f φ ≫ (shortComplexH2 B).moduleCatLeftHomologyData.i =
      (shortComplexH2 A).moduleCatLeftHomologyData.i ≫ ModuleCat.ofHom (fTwo f φ) := by
  simp

@[deprecated (since := "2025-05-09")]
alias mapTwoCocycles_comp_subtype := mapTwoCocycles_comp_i

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma cocyclesMap_comp_isoTwoCocycles_hom :
    cocyclesMap f φ 2 ≫ (isoTwoCocycles B).hom = (isoTwoCocycles A).hom ≫ mapTwoCocycles f φ := by
  simp [← cancel_mono (moduleCatLeftHomologyData (shortComplexH2 B)).i, mapShortComplexH2,
    cochainsMap_f_2_comp_twoCochainsLequiv f, ← LinearEquiv.toModuleIso_hom]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is induced map `H²(H, A) ⟶ H²(G, B)`. -/
noncomputable abbrev H2Map : H2 A ⟶ H2 B :=
  ShortComplex.leftHomologyMap' (mapShortComplexH2 f φ)
    (shortComplexH2 A).moduleCatLeftHomologyData (shortComplexH2 B).moduleCatLeftHomologyData

@[simp]
theorem H2Map_id : H2Map (MonoidHom.id _) (𝟙 A) = 𝟙 _ := by
  simp only [H2Map, shortComplexH2, mapShortComplexH2_id, leftHomologyMap'_id]
  rfl

@[reassoc]
theorem H2Map_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) :
    H2Map (f.comp g) ((Action.res _ g).map φ ≫ ψ) = H2Map f φ ≫ H2Map g ψ := by
  simpa [H2Map, shortComplexH2, mapShortComplexH2_comp] using leftHomologyMap'_comp ..

@[reassoc]
theorem H2Map_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    H2Map (MonoidHom.id G) (φ ≫ ψ) = H2Map (MonoidHom.id G) φ ≫ H2Map (MonoidHom.id G) ψ :=
  H2Map_comp (MonoidHom.id G) (MonoidHom.id G) _ _

@[reassoc, elementwise]
lemma H2π_comp_H2Map :
    H2π A ≫ H2Map f φ = mapTwoCocycles f φ ≫ H2π B := by
  simp

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma map_comp_isoH2_hom :
    map f φ 2 ≫ (isoH2 B).hom = (isoH2 A).hom ≫ H2Map f φ := by
  simp [← cancel_epi (groupCohomologyπ _ _), H2Map, Category.assoc]

variable (k G)

/-- The functor sending a representation to its complex of inhomogeneous cochains. -/
@[simps obj map]
noncomputable def cochainsFunctor : Rep k G ⥤ CochainComplex (ModuleCat k) ℕ where
  obj A := inhomogeneousCochains A
  map f := cochainsMap (MonoidHom.id _) f
  map_id _ := cochainsMap_id
  map_comp φ ψ := cochainsMap_comp (MonoidHom.id G) (MonoidHom.id G) φ ψ

instance : (cochainsFunctor k G).PreservesZeroMorphisms where
instance : (cochainsFunctor k G).Additive where

/-- The functor sending a `G`-representation `A` to `Zⁿ(G, A)`. -/
noncomputable abbrev cocyclesFunctor (n : ℕ) : Rep k G ⥤ ModuleCat k :=
  cochainsFunctor k G ⋙ HomologicalComplex.cyclesFunctor _ _ n

instance (n : ℕ) : (cocyclesFunctor k G n).PreservesZeroMorphisms where
instance (n : ℕ) : (cocyclesFunctor k G n).Additive := inferInstance

/-- The functor sending a `G`-representation `A` to `Cⁿ(G, A)/Bⁿ(G, A)`. -/
noncomputable abbrev opcocyclesFunctor (n : ℕ) : Rep k G ⥤ ModuleCat k :=
  cochainsFunctor k G ⋙ HomologicalComplex.opcyclesFunctor _ _ n

instance (n : ℕ) : (opcocyclesFunctor k G n).PreservesZeroMorphisms where
instance (n : ℕ) : (opcocyclesFunctor k G n).Additive := inferInstance

/-- The functor sending a `G`-representation `A` to `Hⁿ(G, A)`. -/
noncomputable abbrev functor (n : ℕ) : Rep k G ⥤ ModuleCat k :=
  cochainsFunctor k G ⋙ HomologicalComplex.homologyFunctor _ _ n

instance (n : ℕ) : (functor k G n).PreservesZeroMorphisms where
instance (n : ℕ) : (functor k G n).Additive := inferInstance

section LowDegree

/-- The functor sending a `G`-representation `A` to `Z¹(G, A)`, using a convenient expression
for `Z¹`. -/
noncomputable abbrev oneCocyclesFunctor : Rep k G ⥤ ModuleCat k :=
  shortComplexH1Functor k G ⋙ ShortComplex.cyclesFunctor' (fun X => X.moduleCatLeftHomologyData)

instance : (oneCocyclesFunctor k G).PreservesZeroMorphisms where
instance : (oneCocyclesFunctor k G).Additive where

/-- The functor sending a `G`-representation `A` to `C¹(G, A)/B¹(G, A)`, using a convenient
expression for `C¹/B¹`. . -/
noncomputable abbrev oneOpcocyclesFunctor : Rep k G ⥤ ModuleCat k :=
  shortComplexH1Functor k G ⋙ ShortComplex.opcyclesFunctor'
    (fun X => X.moduleCatRightHomologyData)

instance : (oneOpcocyclesFunctor k G).PreservesZeroMorphisms where
  map_zero _ _ := ModuleCat.hom_ext <| Submodule.linearMap_qext _ <| rfl

instance : (oneOpcocyclesFunctor k G).Additive where
  map_add := ModuleCat.hom_ext <| Submodule.linearMap_qext _ <| rfl

/-- The functor sending a `G`-representation `A` to `H¹(G, A)`, using a convenient expression
for `H¹`. . -/
noncomputable abbrev H1Functor : Rep k G ⥤ ModuleCat k :=
  shortComplexH1Functor k G ⋙ ShortComplex.leftHomologyFunctor'
    (fun X => X.moduleCatLeftHomologyData)

instance : (H1Functor k G).PreservesZeroMorphisms where
  map_zero _ _ := (cancel_epi (H1π _)).1 rfl

instance : (H1Functor k G).Additive where
  map_add := (cancel_epi (H1π _)).1 rfl

/-- The functor sending a `G`-representation `A` to `Z²(G, A)`, using a convenient expression
for `Z²`. -/
noncomputable abbrev twoCocyclesFunctor : Rep k G ⥤ ModuleCat k :=
  shortComplexH2Functor k G ⋙ ShortComplex.cyclesFunctor'
    (fun X => X.moduleCatLeftHomologyData)

instance : (twoCocyclesFunctor k G).PreservesZeroMorphisms where
instance : (twoCocyclesFunctor k G).Additive where

/-- The functor sending a `G`-representation `A` to `C²(G, A)/B²(G, A)`, using a convenient
expression for `C²/B²`. -/
noncomputable abbrev twoOpcocyclesFunctor : Rep k G ⥤ ModuleCat k :=
  shortComplexH2Functor k G ⋙ ShortComplex.opcyclesFunctor'
    (fun X => X.moduleCatRightHomologyData)

instance : (twoOpcocyclesFunctor k G).PreservesZeroMorphisms where
  map_zero _ _ := ModuleCat.hom_ext <| Submodule.linearMap_qext _ <| rfl

instance : (twoOpcocyclesFunctor k G).Additive where
  map_add := ModuleCat.hom_ext <| Submodule.linearMap_qext _ <| rfl

/-- The functor sending a `G`-representation `A` to `H²(G, A)`, using a convenient expression
for `H²`. -/
noncomputable abbrev H2Functor : Rep k G ⥤ ModuleCat k :=
  shortComplexH2Functor k G ⋙ ShortComplex.leftHomologyFunctor'
    (fun X => X.moduleCatLeftHomologyData)

instance : (H2Functor k G).PreservesZeroMorphisms where
  map_zero _ _ := (cancel_epi (H2π _)).1 rfl

instance : (H2Functor k G).Additive where
  map_add := (cancel_epi (H2π _)).1 rfl

end LowDegree
section NatIsos

/-- The functor sending a `G`-representation `A` to `H⁰(G, A) := Aᴳ` is naturally isomorphic to the
general group cohomology functor at 0. -/
@[simps! hom_app inv_app]
noncomputable def isoInvariantsFunctor :
    functor k G 0 ≅ invariantsFunctor k G :=
  NatIso.ofComponents isoH0 fun f => by simp

/-- The functor sending a `G`-representation `A` to its 0th opcycles is naturally isomorphic to the
forgetful functor `Rep k G ⥤ ModuleCat k`. -/
@[simps! hom_app inv_app]
noncomputable def zeroOpcocyclesFunctorIso :
    opcocyclesFunctor k G 0 ≅ Action.forget (ModuleCat k) G :=
  NatIso.ofComponents (fun A => zeroOpcocyclesIso A) fun {X Y} f => by
    have := cochainsMap_f_0_comp_zeroCochainsLequiv (MonoidHom.id G) f
    simp_all [← cancel_epi (HomologicalComplex.pOpcycles _ _)]

@[reassoc, elementwise]
theorem pOpcycles_comp_zeroOpcocyclesFunctorIso_hom_app :
    (inhomogeneousCochains B).pOpcycles 0 ≫ (zeroOpcocyclesFunctorIso k G).hom.app B =
      ModuleCat.ofHom (zeroCochainsLequiv B).toLinearMap := by
  simp

/-- The functor sending a `G`-representation `A` to `Z¹(G, A)` is naturally isomorphic to the
general cocycles functor at 1. -/
@[simps! hom_app inv_app]
noncomputable def isoOneCocyclesFunctor :
    cocyclesFunctor k G 1 ≅ oneCocyclesFunctor k G :=
  NatIso.ofComponents isoOneCocycles fun f => by simp

/-- The functor sending a `G`-representation `A` to `C¹(G, A)/B¹(G, A)` is naturally isomorphic to
the general opcocycles functor at 1. -/
@[simps! hom_app inv_app]
noncomputable def isoOneOpcocyclesFunctor :
    opcocyclesFunctor k G 1 ≅ oneOpcocyclesFunctor k G :=
  NatIso.ofComponents
    (fun A => (inhomogeneousCochains A).opcyclesIsoSc' _ _ _ (by simp) (by simp) ≪≫ opcyclesMapIso
      (shortComplexH1Iso A) ≪≫ (shortComplexH1 A).moduleCatOpcyclesIso) fun f => by
        simpa [← cancel_epi (pOpcycles _), HomologicalComplex.opcyclesIsoSc',
          HomologicalComplex.opcyclesMap]
          using cochainsMap_f_1_comp_oneCochainsLequiv_assoc (MonoidHom.id G) f _

@[reassoc, elementwise]
theorem pOpcycles_comp_isoOneOpcocyclesFunctor_hom_app :
    (inhomogeneousCochains B).pOpcycles 1 ≫ (isoOneOpcocyclesFunctor k G).hom.app B =
      ModuleCat.ofHom (oneCochainsLequiv _).toLinearMap ≫
      (shortComplexH1 B).moduleCatRightHomologyData.p := by
  simp

/-- The functor sending a `G`-representation `A` to `H¹(G, A)` is naturally isomorphic to the
general group cohomology functor at 1. -/
@[simps! hom_app inv_app]
noncomputable def isoH1Functor :
    functor k G 1 ≅ H1Functor k G :=
  NatIso.ofComponents isoH1 fun f => by simp

/-- The functor sending a `G`-representation `A` to `Z²(G, A)` is naturally isomorphic to the
general cocycles functor at 2. -/
@[simps! hom_app inv_app]
noncomputable def isoTwoCocyclesFunctor :
    cocyclesFunctor k G 2 ≅ twoCocyclesFunctor k G :=
  NatIso.ofComponents isoTwoCocycles fun f => by simp

/-- The functor sending a `G`-representation `A` to `C²(G, A)/B²(G, A)` is naturally isomorphic to
the general opcocycles functor at 2. -/
@[simps! hom_app inv_app]
noncomputable def isoTwoOpcocyclesFunctor :
    opcocyclesFunctor k G 2 ≅ twoOpcocyclesFunctor k G :=
  NatIso.ofComponents
    (fun A => (inhomogeneousCochains A).opcyclesIsoSc' _ _ _ (by simp) (by simp) ≪≫ opcyclesMapIso
      (shortComplexH2Iso A) ≪≫ (shortComplexH2 A).moduleCatOpcyclesIso) fun f => by
        simpa [← cancel_epi (pOpcycles _), HomologicalComplex.opcyclesIsoSc',
          HomologicalComplex.opcyclesMap]
          using cochainsMap_f_2_comp_twoCochainsLequiv_assoc (MonoidHom.id G) f _

@[reassoc, elementwise]
theorem pOpcycles_comp_isoTwoOpcocyclesFunctor_hom_app :
    (inhomogeneousCochains B).pOpcycles 2 ≫ (isoTwoOpcocyclesFunctor k G).hom.app B =
      ModuleCat.ofHom (twoCochainsLequiv _).toLinearMap ≫
      (shortComplexH2 B).moduleCatRightHomologyData.p := by
  simp

/-- The functor sending a `G`-representation `A` to `H²(G, A)` is naturally isomorphic to the
general group cohomology functor at 2. -/
@[simps! hom_app inv_app]
noncomputable def isoH2Functor :
    functor k G 2 ≅ H2Functor k G :=
  NatIso.ofComponents isoH2 fun f => by simp

end NatIsos
end Functors
end groupCohomology
