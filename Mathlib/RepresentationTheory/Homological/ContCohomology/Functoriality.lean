/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Richard Hill
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
# Functoriality of continuous cohomology

Given topological groups `G` and `H`, a continuous group homomorphism `φ : H →ₜ* G`, a topological
representation `X` of `G`, a topological representation `Y` of `H`, and a morphism of topological
`H`-representations `f : res φ X ⟶ Y`, we construct a cochain map
`homogeneousCochains X ⟶ homogeneousCochains Y` and hence maps on continuous cohomology
`Hⁿ(G, X) ⟶ Hⁿ(H, Y)`.

## Main definitions

* `ContinuousCohomology.cochainsMap₂ φ f` : the cochain map
  `homogeneousCochains X ⟶ homogeneousCochains Y` induced by `φ : H →ₜ* G` and
  `f : res φ X ⟶ Y`, sending an invariant function `σ : C(G, C(G, ⋯))` to `f ∘ σ ∘ φ`.
* `ContinuousCohomology.map₂ φ f n` : the induced map `Hⁿ(G, X) ⟶ Hⁿ(H, Y)` on continuous
  cohomology.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Functor

namespace ContinuousCohomology

open TopRep ContRepresentation

variable {k : Type u} {G H K : Type v} [Ring k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  {X X' X'' : TopRep k G} {Y : TopRep k H} {Z : TopRep k K}

abbrev resolutionMap (f : X ⟶ X') :
    (i : ℕ) → (resolutionX X i) ⟶ (resolutionX X' i)
  | 0 => f
  | i + 1 => ((coind₁Functor k G).map (resolutionMap f i))

@[simp]
lemma resolutionMap_zero (f : X ⟶ X') : resolutionMap f 0 = f := rfl

lemma resolutionMap_succ (f : X ⟶ X') (n : ℕ) :
    resolutionMap f (n + 1) = (coind₁Functor k G).map (resolutionMap f n) := rfl

/-- The maps `resolutionMap f` commute with the differentials of the resolutions. -/
lemma resolutionMap_comp_d (f : X ⟶ X') (i : ℕ) :
    resolutionMap f i ≫ d X' i = (d X i) ≫ resolutionMap f (i + 1) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [d_succ, d_succ, resolutionMap_succ f (i + 1), Preadditive.comp_sub,
      Preadditive.sub_comp]
    congr 1
    rw [resolutionMap_succ f i, ← Functor.map_comp, ← Functor.map_comp, ih]

lemma resolutionMap_id (i : ℕ) : resolutionMap (𝟙 X) i = 𝟙 (resolutionX X i) := by
  induction i with
  | zero => rw [resolutionMap_zero]
  | succ _ ih => rw [resolutionMap_succ, ih, map_id]

lemma resolutionMap_comp (f : X ⟶ X') (f' : X' ⟶ X'') (i : ℕ) :
    resolutionMap (f ≫ f') i = (resolutionMap f i) ≫ resolutionMap f' i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [resolutionMap_succ, resolutionMap_succ, resolutionMap_succ, ih,
      map_comp]

variable (k G)
@[simps] abbrev resolution'Functor : TopRep k G ⥤ CochainComplex (TopRep k G) ℕ where
  obj           := resolution'
  map {X Y} f   := {
    f n   := resolutionMap f (n + 1)
    comm' := by simp +contextual [resolution'd_eq, resolutionMap_comp_d f _]
  }
  map_id _      := HomologicalComplex.hom_ext _ _ <| fun _ ↦ resolutionMap_id _
  map_comp _ _  := HomologicalComplex.hom_ext _ _ <| fun _ ↦ resolutionMap_comp _ _ _

abbrev homogeneousCochainsFunctor : TopRep k G ⥤ CochainComplex (TopModuleCat k) ℕ :=
    resolution'Functor k G ⋙ (invariantsFunctor k G).mapHomologicalComplex (.up ℕ)

lemma homogeneousCochainsFunctor_obj :
    (homogeneousCochainsFunctor k G).obj = homogeneousCochains := rfl

noncomputable abbrev Functor (n : ℕ) : TopRep k G ⥤ TopModuleCat k :=
    homogeneousCochainsFunctor k G ⋙ HomologicalComplex.homologyFunctor _ _ n

notation "Hₜ" => continuousCohomology

lemma Functor_obj (n : ℕ) : (Functor k G n).obj = Hₜ n := rfl

variable {k G}
variable (X) in
/-- The morphisms between the levels of the standard resolutions of `X` and `Y` induced by a
continuous group homomorphism `φ : H →ₜ* G` and a morphism `f : res φ X ⟶ Y`, given by
`F ↦ f ∘ F ∘ φ`. -/
abbrev _root_.TopRep.resolutionXRes (φ : H →ₜ* G) :
    (i : ℕ) → (res φ (resolutionX X i)) ⟶ (resolutionX (res φ.toMonoidHom X) i)
  | 0 => 𝟙 _
  | i + 1 => ofHom (coind₁ResMap φ (resolutionXRes φ i).hom)

@[simp]
lemma resolutionXRes_zero (φ : H →ₜ* G) : X.resolutionXRes φ 0 = 𝟙 _ := rfl

lemma resolutionXRes_one (φ : H →ₜ* G) : X.resolutionXRes φ 1 = ofHom (coind₁ResMap φ .id) := rfl

lemma resolutionXRes_succ (φ : H →ₜ* G) (i : ℕ) :
    resolutionXRes X φ (i + 1) = ofHom (coind₁ResMap φ (resolutionXRes _ φ i).hom) := rfl

@[simp]
lemma resolutionXRes_id (X : TopRep k G) (i : ℕ) :
    resolutionXRes X (ContinuousMonoidHom.id G) i = 𝟙 (resolutionX X i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionXRes_succ, ih]
    ext; rfl


lemma resolutionXRes_comp (φ : H →ₜ* G) (ψ : K →ₜ* H) (i : ℕ) :
    resolutionXRes X (φ.comp ψ) i =
      (resFunctor ψ.toMonoidHom).map (resolutionXRes X φ i) ≫ resolutionXRes _ ψ i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionXRes_succ, resolutionXRes_succ, resolutionXRes_succ, ih]
    ext; rfl

/-- The maps `resolutionMap₂ φ f` commute with the differentials of the resolutions. -/
lemma resolutionXRes_comp_d (φ : H →ₜ* G) (i : ℕ) :
    resolutionXRes X φ i ≫ d _ i =
      (resFunctor (φ : H →* G)).map (d X i) ≫ resolutionXRes X φ (i + 1) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    ext : 1
    replace ih := congr($(ih).hom)
    simp only [TopRep.hom_comp, TopRep.hom_ofHom, hom_d_succ,
      ContIntertwiningMap.restrict_sub, ContIntertwiningMap.sub_comp,
      ContIntertwiningMap.comp_sub, coind₁Map_comp_coind₁ResMap,
      coind₁ResMap_comp_coind₁Map_restrict] at ih ⊢
    rw [ih, ← coind₁ResMap_comp_coind₁ι_restrict]

/-- The maps `resolutionXRes X φ` are natural in `X`. -/
lemma resolutionXRes_naturality (φ : H →ₜ* G) (f : X ⟶ X') (i : ℕ) :
    (resFunctor (φ : H →* G)).map (resolutionMap f i) ≫ resolutionXRes X' φ i =
      resolutionXRes X φ i ≫ resolutionMap ((resFunctor φ.toMonoidHom).map f) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionXRes_succ, resolutionXRes_succ, resolutionMap_succ, resolutionMap_succ]
    ext F x
    exact congr($(ih).hom (F (φ x)))

abbrev resolution'Res (φ : H →ₜ* G) :
    ((resFunctor φ.toMonoidHom).mapHomologicalComplex (.up ℕ)).obj (resolution' X)
    ⟶ resolution' (res φ.toMonoidHom X) where
  f n := resolutionXRes X φ (n + 1)
  comm' := by
    intro _ _ rfl
    simp only [mapHomologicalComplex_obj_d, ContinuousMonoidHom.coe_toMonoidHom,
      CochainComplex.of_d, resolution'd_eq]
    exact resolutionXRes_comp_d φ _

def resolution'ResNatTrans (φ : H →ₜ* G) :
    resolution'Functor k G ⋙ (resFunctor ↑φ).mapHomologicalComplex (.up ℕ)
    ⟶ (resFunctor φ) ⋙ resolution'Functor k H where
  app X := resolution'Res φ
  naturality X Y f := by
    ext n : 1
    exact resolutionXRes_naturality φ f (n + 1)

def _root_.TopRep.homogeneousCochainsXRes (φ : H →ₜ* G) (X : TopRep k G) (n : ℕ) :
    X.homogeneousCochains.X n ⟶ (X.res φ.toMonoidHom).homogeneousCochains.X n :=
  (X.resolutionX _).invariantsRes φ.toMonoidHom ≫ ((invariantsFunctor (k := k) (G := H)).map
  (resolutionXRes X φ _))

lemma _root_.TopRep.homogeneousCochainsXRes_zero (φ : H →ₜ* G) (X : TopRep k G) :
    X.homogeneousCochainsXRes φ 0 =
    X.coind₁.invariantsRes φ ≫ (invariantsFunctor k H).map (ofHom (coind₁ResMap φ .id)) := rfl

lemma _root_.TopRep.homogeneousCochainsXRes_succ (φ : H →ₜ* G) (X : TopRep k G) (n : ℕ) :
    X.homogeneousCochainsXRes φ (n + 1) =
    (X.resolution'X n).coind₁.invariantsRes φ ≫ (invariantsFunctor k H).map
    (ofHom (coind₁ResMap φ (X.resolutionXRes φ (n + 1)).hom)) := rfl

variable (k) in
def homogeneousCochainsResNatTrans (φ : H →ₜ* G) : homogeneousCochainsFunctor k G
    ⟶ (resFunctor φ.toMonoidHom) ⋙ homogeneousCochainsFunctor k H :=
  (𝟙 (resolution'Functor k G)
    ◫ ((invariantsResNatTrans φ.toMonoidHom (k := k)).mapHomologicalComplex _
    ≫ (mapHomologicalComplexCompIso (.refl _) _).inv))
  ≫ (associator _ _ _).inv
  ≫ (resolution'ResNatTrans φ ◫ (𝟙 _))
  ≫ (associator _ _ _).hom

lemma homogeneousCochainsResNatTrans_app_f (φ : H →ₜ* G) (X : TopRep k G) (n : ℕ) :
    ((homogeneousCochainsResNatTrans k φ).app X).f n = homogeneousCochainsXRes φ X n := rfl

variable (k) in
noncomputable abbrev resNatTrans (φ : H →ₜ* G) (n : ℕ) :
    (Functor k G n) ⟶ (resFunctor φ.toMonoidHom ⋙ Functor k H n) :=
  homogeneousCochainsResNatTrans k φ ◫ 𝟙 _

lemma resNatTrans_app (φ : H →ₜ* G) (n : ℕ) (X : TopRep k G) :
    (resNatTrans k φ n).app X =
      HomologicalComplex.homologyMap ((homogeneousCochainsResNatTrans k φ).app X) n := by
  simp only [resNatTrans, NatTrans.hcomp_id_app, HomologicalComplex.homologyFunctor_map]



set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex

/-- The morphisms between the levels of the standard resolutions of `X` and `Y` induced by a
continuous group homomorphism `φ : H →ₜ* G` and a morphism `f : res φ X ⟶ Y`, given by
`F ↦ f ∘ F ∘ φ`. -/
def resolutionMap₂ (φ : H →ₜ* G) (f : res φ X ⟶ Y) :
    (i : ℕ) → res φ (resolutionX X i) ⟶ resolutionX Y i
  | 0 => f
  | i + 1 => ofHom (coind₁ResMap φ (resolutionMap₂ φ f i).hom)

@[simp]
lemma resolutionMap₂_zero (φ : H →ₜ* G) (f : res φ X ⟶ Y) :
    resolutionMap₂ φ f 0 = f := rfl

lemma resolutionMap₂_succ (φ : H →ₜ* G) (f : res φ X ⟶ Y) (i : ℕ) :
    resolutionMap₂ φ f (i + 1) = ofHom (coind₁ResMap φ (resolutionMap₂ φ f i).hom) := rfl

@[simp]
lemma resolutionMap₂_id (X : TopRep k G) (i : ℕ) :
    resolutionMap₂ (ContinuousMonoidHom.id G) (𝟙 X) i = 𝟙 (resolutionX X i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionMap₂_succ, ih]
    ext F x
    rfl

lemma resolutionMap₂_comp (φ : H →ₜ* G) (ψ : K →ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z)
    (i : ℕ) :
    resolutionMap₂ (φ.comp ψ) (X := X) ((resFunctor (ψ : K →* H)).map f ≫ g) i =
      (resFunctor (ψ : K →* H)).map (resolutionMap₂ φ f i) ≫ resolutionMap₂ ψ g i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionMap₂_succ, resolutionMap₂_succ, resolutionMap₂_succ, ih]
    ext F x
    rfl


/-- The maps `resolutionMap₂ φ f` commute with the differentials of the resolutions. -/
lemma resolutionMap₂_comp_d (φ : H →ₜ* G) (f : res φ X ⟶ Y) (i : ℕ) :
    resolutionMap₂ φ f i ≫ d Y i =
      (resFunctor (φ : H →* G)).map (d X i) ≫ resolutionMap₂ φ f (i + 1) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    ext : 1
    replace ih := congr($(ih).hom)
    simp only [TopRep.hom_comp, resolutionMap₂_succ, TopRep.hom_ofHom, hom_d_succ,
      ContIntertwiningMap.restrict_sub, ContIntertwiningMap.sub_comp,
      ContIntertwiningMap.comp_sub, coind₁Map_comp_coind₁ResMap,
      coind₁ResMap_comp_coind₁Map_restrict] at ih ⊢
    rw [ih, ← coind₁ResMap_comp_coind₁ι_restrict]

/-- The cochain map `homogeneousCochains X ⟶ homogeneousCochains Y` induced by a continuous
group homomorphism `φ : H →ₜ* G` and a morphism of topological `H`-representations
`f : res φ X ⟶ Y`, sending an invariant function `σ : C(G, C(G, ⋯))` to `f ∘ σ ∘ φ`. -/
@[simps! -isSimp f f_hom]
def cochainsMap₂ (φ : H →ₜ* G) (f : res φ X ⟶ Y) :
    homogeneousCochains X ⟶ homogeneousCochains Y where
  f i := invariantsResMap φ (resolutionMap₂ φ f (i + 1))
  comm' i j (hij : _ = _) := by
    subst hij
    rw [homogeneousCochains.d_eq, homogeneousCochains.d_eq, ← invariantsResMap_comp,
      resolutionMap₂_comp_d, invariantsResMap_map_comp]

@[simp]
lemma cochainsMap₂_id (X : TopRep k G) :
    cochainsMap₂ (ContinuousMonoidHom.id G) (𝟙 X) = 𝟙 (homogeneousCochains X) := by
  ext i : 1
  rw [cochainsMap₂_f, resolutionMap₂_id]
  ext v
  rfl

@[reassoc]
lemma cochainsMap₂_comp (φ : H →ₜ* G) (ψ : K →ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z) :
    cochainsMap₂ (φ.comp ψ) (X := X) ((resFunctor (ψ : K →* H)).map f ≫ g) =
      cochainsMap₂ φ f ≫ cochainsMap₂ ψ g := by
  ext i v x
  exact congr($(resolutionMap₂_comp φ ψ f g (i + 1)).hom v.1 x)

/-- The map `Zⁿ(G, X) ⟶ Zⁿ(H, Y)` on cocycles induced by a continuous group homomorphism
`φ : H →ₜ* G` and a morphism of topological `H`-representations `f : res φ X ⟶ Y`. -/
noncomputable abbrev cocyclesMap₂ (φ : H →ₜ* G) (f : res φ X ⟶ Y) (n : ℕ) :
    cocycles X n ⟶ cocycles Y n :=
  HomologicalComplex.cyclesMap (cochainsMap₂ φ f) n

@[simp]
lemma cocyclesMap₂_id (X : TopRep k G) (n : ℕ) :
    cocyclesMap₂ (ContinuousMonoidHom.id G) (𝟙 X) n = 𝟙 _ := by
  simp [cocyclesMap₂]

@[reassoc]
lemma cocyclesMap₂_comp (φ : H →ₜ* G) (ψ : K →ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z)
    (n : ℕ) :
    cocyclesMap₂ (φ.comp ψ) (X := X) ((resFunctor (ψ : K →* H)).map f ≫ g) n =
      cocyclesMap₂ φ f n ≫ cocyclesMap₂ ψ g n := by
  simp [cocyclesMap₂, ← HomologicalComplex.cyclesMap_comp, ← cochainsMap₂_comp]

/-- The map `Hⁿ(G, X) ⟶ Hⁿ(H, Y)` on continuous cohomology induced by a continuous group
homomorphism `φ : H →ₜ* G` and a morphism of topological `H`-representations
`f : res φ X ⟶ Y`. -/
noncomputable abbrev map₂ (φ : H →ₜ* G) (f : res φ X ⟶ Y) (n : ℕ) :
    continuousCohomology n X ⟶ continuousCohomology n Y :=
  HomologicalComplex.homologyMap (cochainsMap₂ φ f) n

@[reassoc]
theorem π_map₂ (φ : H →ₜ* G) (f : res φ X ⟶ Y) (n : ℕ) :
    π X n ≫ map₂ φ f n = cocyclesMap₂ φ f n ≫ π Y n := by
  simp [map₂, cocyclesMap₂]

@[simp]
lemma map₂_id (X : TopRep k G) (n : ℕ) :
    map₂ (ContinuousMonoidHom.id G) (𝟙 X) n = 𝟙 _ := by
  simp [map₂]

@[reassoc]
lemma map₂_comp (φ : H →ₜ* G) (ψ : K →ₜ* H) (f : res φ X ⟶ Y) (g : res ψ Y ⟶ Z) (n : ℕ) :
    map₂ (φ.comp ψ) (X := X) ((resFunctor (ψ : K →* H)).map f ≫ g) n =
      map₂ φ f n ≫ map₂ ψ g n := by
  simp [map₂, ← HomologicalComplex.homologyMap_comp, ← cochainsMap₂_comp]

/-!
### Relation to the functorial constructions

The maps `resolutionMap₂`, `cochainsMap₂` and `map₂` combine restriction along `φ : H →ₜ* G` with
functoriality in the coefficient representation. The following lemmas express them in terms of
the two constructions they combine: `resolutionXRes`, `homogeneousCochainsResNatTrans` and
`resNatTrans` (pure restriction), and `resolutionMap` and the functors
`homogeneousCochainsFunctor` and `Functor` (pure coefficient maps).
-/

/-- `resolutionMap₂ φ f` is the restriction map `resolutionXRes X φ` followed by the functorial
map `resolutionMap f`. -/
@[reassoc]
lemma resolutionMap₂_eq (φ : H →ₜ* G) (f : res φ X ⟶ Y) (i : ℕ) :
    resolutionMap₂ φ f i = resolutionXRes X φ i ≫ resolutionMap f i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionMap₂_succ, resolutionXRes_succ, resolutionMap_succ, ih]
    ext F x
    rfl

/-- `resolutionXRes` is the special case of `resolutionMap₂` where the coefficient map is the
identity. -/
lemma resolutionMap₂_id_right (φ : H →ₜ* G) (i : ℕ) :
    resolutionMap₂ φ (𝟙 (res φ.toMonoidHom X)) i = resolutionXRes X φ i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [resolutionMap₂_succ, resolutionXRes_succ, ih]

/-- `resolutionMap` is the special case of `resolutionMap₂` along the identity of `G`. -/
lemma resolutionMap₂_id_left (f : X ⟶ X') (i : ℕ) :
    resolutionMap₂ (ContinuousMonoidHom.id G) f i = resolutionMap f i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionMap₂_succ, resolutionMap_succ, ih]
    ext F x
    rfl

/-- `cochainsMap₂ φ f` is the component of the restriction natural transformation on homogeneous
cochains followed by the functorial map on homogeneous cochains. -/
@[reassoc]
lemma cochainsMap₂_eq (φ : H →ₜ* G) (f : res φ X ⟶ Y) :
    cochainsMap₂ φ f = (homogeneousCochainsResNatTrans k φ).app X ≫
      (homogeneousCochainsFunctor k H).map f := by
  ext i v x
  exact congr($(resolutionMap₂_eq φ f (i + 1)).hom v.1 x)

/-- The levelwise form of `cochainsMap₂_eq`: the restriction part expressed via
`homogeneousCochainsXRes` and the coefficient part via `resolutionMap`. -/
@[reassoc]
lemma cochainsMap₂_f_eq (φ : H →ₜ* G) (f : res φ X ⟶ Y) (n : ℕ) :
    (cochainsMap₂ φ f).f n = homogeneousCochainsXRes φ X n ≫
      (invariantsFunctor k H).map (resolutionMap f (n + 1)) := by
  rw [cochainsMap₂_eq]
  rfl

/-- The component of the restriction natural transformation on homogeneous cochains is the
special case of `cochainsMap₂` where the coefficient map is the identity. -/
lemma cochainsMap₂_id_right (φ : H →ₜ* G) :
    cochainsMap₂ φ (𝟙 (res φ.toMonoidHom X)) = (homogeneousCochainsResNatTrans k φ).app X := by
  ext i v x
  exact congr($(resolutionMap₂_id_right φ (i + 1)).hom v.1 x)

/-- The functorial map on homogeneous cochains is the special case of `cochainsMap₂` along the
identity of `G`. -/
lemma cochainsMap₂_id_left (f : X ⟶ X') :
    cochainsMap₂ (ContinuousMonoidHom.id G) f = (homogeneousCochainsFunctor k G).map f := by
  ext i v x
  exact congr($(resolutionMap₂_id_left f (i + 1)).hom v.1 x)

/-- `map₂ φ f n` is the component of the restriction natural transformation `resNatTrans`
followed by the functorial map on continuous cohomology. -/
@[reassoc]
lemma map₂_eq (φ : H →ₜ* G) (f : res φ X ⟶ Y) (n : ℕ) :
    map₂ φ f n = (resNatTrans k φ n).app X ≫ (Functor k H n).map f := by
  rw [resNatTrans_app]
  exact (congrArg (HomologicalComplex.homologyMap · n) (cochainsMap₂_eq φ f)).trans
    (HomologicalComplex.homologyMap_comp _ _ _)

/-- The component of `resNatTrans` is the special case of `map₂` where the coefficient map is
the identity. -/
lemma map₂_id_right (φ : H →ₜ* G) (n : ℕ) :
    map₂ φ (𝟙 (res φ.toMonoidHom X)) n = (resNatTrans k φ n).app X := by
  rw [resNatTrans_app]
  exact congrArg (HomologicalComplex.homologyMap · n) (cochainsMap₂_id_right φ)

/-- The functorial map on continuous cohomology is the special case of `map₂` along the
identity of `G`. -/
lemma map₂_id_left (f : X ⟶ X') (n : ℕ) :
    map₂ (ContinuousMonoidHom.id G) f n = (Functor k G n).map f := by
  simp only [map₂, cochainsMap₂_id_left]
  rfl

end ContinuousCohomology
