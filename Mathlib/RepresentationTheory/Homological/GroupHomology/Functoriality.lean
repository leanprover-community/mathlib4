/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree

/-!
# Functoriality of group homology

Given a commutative ring `k`, a group homomorphism `f : G →* H`, a `k`-linear `G`-representation
`A`, a `k`-linear `H`-representation `B`, and a representation morphism `A ⟶ Res(f)(B)`, we get
a chain map `inhomogeneousChains A ⟶ inhomogeneousChains B` and hence maps on homology
`Hₙ(G, A) ⟶ Hₙ(H, B)`.

We also provide extra API for these maps in degrees 0, 1, 2.

## Main definitions

* `groupHomology.chainsMap f φ` is the map `inhomogeneousChains A ⟶ inhomogeneousChains B`
  induced by a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`.
* `groupHomology.map f φ n` is the map `Hₙ(G, A) ⟶ Hₙ(H, B)` induced by a group homomorphism
  `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`.

-/

universe v u

namespace groupHomology

open CategoryTheory Rep Finsupp Representation

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
  {A : Rep k G} {B : Rep k H} (f : G →* H) (φ : A ⟶ (Action.res _ f).obj B) (n : ℕ)

theorem congr {f₁ f₂ : G →* H} (h : f₁ = f₂) {φ : A ⟶ (Action.res _ f₁).obj B} {T : Type*}
    (F : (f : G →* H) → (φ : A ⟶ (Action.res _ f).obj B) → T) :
    F f₁ φ = F f₂ (h ▸ φ) := by
  subst h
  rfl

variable [DecidableEq G] [DecidableEq H]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the chain map sending `∑ aᵢ·gᵢ : Gⁿ →₀ A` to `∑ φ(aᵢ)·(f ∘ gᵢ) : Hⁿ →₀ B`. -/
@[simps! (config := .lemmasOnly) f f_hom]
noncomputable def chainsMap :
    inhomogeneousChains A ⟶ inhomogeneousChains B where
  f i := ModuleCat.ofHom <| mapRange.linearMap φ.hom.hom ∘ₗ lmapDomain A k (f ∘ ·)
  comm' i j (hij : _ = _) := by
    subst hij
    refine ModuleCat.hom_ext <| lhom_ext fun _ _ => ?_
    simpa [Fin.comp_contractNth, map_add] using congr(single _ $((hom_comm_apply φ (_)⁻¹ _).symm))

@[reassoc (attr := simp)]
lemma lsingle_comp_chainsMap_f (n : ℕ) (x : Fin n → G) :
    ModuleCat.ofHom (lsingle x) ≫ (chainsMap f φ).f n =
      φ.hom ≫ ModuleCat.ofHom (lsingle (f ∘ x)) := by
  ext
  simp [chainsMap_f]

lemma chainsMap_f_single (n : ℕ) (x : Fin n → G) (a : A) :
    (chainsMap f φ).f n (single x a) = single (f ∘ x) (φ.hom a) := by
  simp [chainsMap_f]

@[simp]
lemma chainsMap_id :
    chainsMap (MonoidHom.id G) (𝟙 A) = 𝟙 (inhomogeneousChains A) :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext <| lhom_ext' fun _ =>
    ModuleCat.hom_ext_iff.1 <| lsingle_comp_chainsMap_f (k := k) (MonoidHom.id G) ..

@[simp]
lemma chainsMap_id_f_eq_mapRange {A B : Rep k G} (i : ℕ) (φ : A ⟶ B) :
    (chainsMap (MonoidHom.id G) φ).f i = ModuleCat.ofHom (mapRange.linearMap φ.hom.hom) := by
  refine ModuleCat.hom_ext <| lhom_ext fun _ _ => ?_
  simp [chainsMap_f, MonoidHom.coe_id]

lemma chainsMap_comp {G H K : Type u} [Group G] [Group H] [Group K]
    [DecidableEq G] [DecidableEq H] [DecidableEq K] {A : Rep k G} {B : Rep k H} {C : Rep k K}
    (f : G →* H) (g : H →* K) (φ : A ⟶ (Action.res _ f).obj B) (ψ : B ⟶ (Action.res _ g).obj C) :
    chainsMap (g.comp f) (φ ≫ (Action.res _ f).map ψ) = chainsMap f φ ≫ chainsMap g ψ := by
  ext : 1
  refine ModuleCat.hom_ext <| lhom_ext fun _ _ => ?_
  simp [chainsMap_f, Function.comp_assoc]

lemma chainsMap_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    chainsMap (MonoidHom.id G) (φ ≫ ψ) =
      chainsMap (MonoidHom.id G) φ ≫ chainsMap (MonoidHom.id G) ψ :=
  chainsMap_comp (MonoidHom.id G) (MonoidHom.id G) _ _

@[simp]
lemma chainsMap_zero : chainsMap f (0 : A ⟶ (Action.res _ f).obj B) = 0 :=
  HomologicalComplex.hom_ext _ _ <| fun _ => ModuleCat.hom_ext <| lhom_ext' <|
    fun _ => LinearMap.ext fun _ => by simp [chainsMap_f, LinearMap.zero_apply (M₂ := B)]

lemma chainsMap_f_map_mono (hf : Function.Injective f) [Mono φ] (i : ℕ) :
    Mono ((chainsMap f φ).f i) := by
  simpa [ModuleCat.mono_iff_injective] using
    (mapRange_injective φ.hom (map_zero _) <| (Rep.mono_iff_injective φ).1
    inferInstance).comp (mapDomain_injective hf.comp_left)

instance chainsMap_id_f_map_mono {A B : Rep k G} (φ : A ⟶ B) [Mono φ] (i : ℕ) :
    Mono ((chainsMap (MonoidHom.id G) φ).f i) :=
  chainsMap_f_map_mono (MonoidHom.id G) φ (fun _ _ h => h) _

lemma chainsMap_f_map_epi (hf : Function.Surjective f) [Epi φ] (i : ℕ) :
    Epi ((chainsMap f φ).f i) := by
  simpa [ModuleCat.epi_iff_surjective] using
    (mapRange_surjective φ.hom (map_zero _) ((Rep.epi_iff_surjective φ).1 inferInstance)).comp
    (mapDomain_surjective hf.comp_left)

instance chainsMap_id_f_map_epi {A B : Rep k G} (φ : A ⟶ B) [Epi φ] (i : ℕ) :
    Epi ((chainsMap (MonoidHom.id G) φ).f i) :=
  chainsMap_f_map_epi _ _ (fun x => ⟨x, rfl⟩) _

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map `Zₙ(G, A) ⟶ Zₙ(H, B)` sending `∑ aᵢ·gᵢ : Gⁿ →₀ A` to
`∑ φ(aᵢ)·(f ∘ gᵢ) : Hⁿ →₀ B`. -/
noncomputable abbrev cyclesMap (n : ℕ) :
    groupHomology.cycles A n ⟶ groupHomology.cycles B n :=
  HomologicalComplex.cyclesMap (chainsMap f φ) n

theorem cyclesMap_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℕ) :
    cyclesMap (MonoidHom.id G) (φ ≫ ψ) n =
      cyclesMap (MonoidHom.id G) φ n ≫ cyclesMap (MonoidHom.id G) ψ n := by
  simp [cyclesMap, chainsMap_id_comp, HomologicalComplex.cyclesMap_comp]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map `Hₙ(G, A) ⟶ Hₙ(H, B)` sending `∑ aᵢ·gᵢ : Gⁿ →₀ A` to
`∑ φ(aᵢ)·(f ∘ gᵢ) : Hⁿ →₀ B`. -/
noncomputable abbrev map (n : ℕ) :
    groupHomology A n ⟶ groupHomology B n :=
  HomologicalComplex.homologyMap (chainsMap f φ) n

theorem map_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℕ) :
    map (MonoidHom.id G) (φ ≫ ψ) n =
      map (MonoidHom.id G) φ n ≫ map (MonoidHom.id G) ψ n := by
  rw [map, chainsMap_id_comp, HomologicalComplex.homologyMap_comp]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map sending `∑ aᵢ·gᵢ : G →₀ A` to `∑ φ(aᵢ)·f(gᵢ) : H →₀ B` -/
noncomputable abbrev fOne : (G →₀ A) →ₗ[k] H →₀ B :=
  mapRange.linearMap φ.hom.hom ∘ₗ lmapDomain A k f

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map sending `∑ aᵢ·(gᵢ₁, gᵢ₂) : G × G →₀ A` to
`∑ φ(aᵢ)·(f(gᵢ₁), f(gᵢ₂)) : H × H →₀ B`.  -/
noncomputable abbrev fTwo : (G × G →₀ A) →ₗ[k] H × H →₀ B :=
  mapRange.linearMap φ.hom.hom ∘ₗ lmapDomain A k (Prod.map f f)

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map sending `∑ aᵢ·(gᵢ₁, gᵢ₂, gᵢ₃) : G × G × G →₀ A` to
`∑ φ(aᵢ)·(f(gᵢ₁), f(gᵢ₂), f(gᵢ₃)) : H × H × H →₀ B`.  -/
noncomputable abbrev fThree : (G × G × G →₀ A) →ₗ[k] H × H × H →₀ B :=
  mapRange.linearMap φ.hom.hom ∘ₗ lmapDomain A k (Prod.map f (Prod.map f f))

@[reassoc]
lemma chainsMap_f_0_comp_zeroChainsLequiv :
    (chainsMap f φ).f 0 ≫ (zeroChainsLequiv B).toModuleIso.hom =
      (zeroChainsLequiv A).toModuleIso.hom ≫ φ.hom := by
  refine ModuleCat.hom_ext <| lhom_ext' fun x => ModuleCat.homEquiv.symm.bijective.1 ?_
  ext y
  simp [ModuleCat.homEquiv, zeroChainsLequiv, Unique.eq_default]

@[reassoc]
lemma chainsMap_f_1_comp_oneChainsLequiv :
    (chainsMap f φ).f 1 ≫ (oneChainsLequiv B).toModuleIso.hom =
      (oneChainsLequiv A).toModuleIso.hom ≫ ModuleCat.ofHom (fOne f φ) := by
  refine ModuleCat.hom_ext <| lhom_ext' fun x => ModuleCat.homEquiv.symm.bijective.1 ?_
  ext y
  simp [ModuleCat.homEquiv, oneChainsLequiv, fOne]

@[reassoc]
lemma chainsMap_f_2_comp_twoChainsLequiv :
    (chainsMap f φ).f 2 ≫ (twoChainsLequiv B).toModuleIso.hom =
      (twoChainsLequiv A).toModuleIso.hom ≫ ModuleCat.ofHom (fTwo f φ) := by
  refine ModuleCat.hom_ext <| lhom_ext' fun x => ModuleCat.homEquiv.symm.bijective.1 ?_
  ext y
  simp [ModuleCat.homEquiv, twoChainsLequiv, fTwo]

@[reassoc]
lemma chainsMap_f_3_comp_threeChainsLequiv :
    (chainsMap f φ).f 3 ≫ (threeChainsLequiv B).toModuleIso.hom =
      (threeChainsLequiv A).toModuleIso.hom ≫ ModuleCat.ofHom (fThree f φ) := by
  refine ModuleCat.hom_ext <| lhom_ext' fun x => ModuleCat.homEquiv.symm.bijective.1 ?_
  ext y
  simp [ModuleCat.homEquiv, threeChainsLequiv, fThree, ← Fin.comp_tail]

open ShortComplex

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map `A_G ⟶ B_H`. -/
noncomputable def H0Map : H0 A ⟶ H0 B :=
  ModuleCat.ofHom <| Submodule.mapQ _ _ φ.hom.hom <| Submodule.span_le.2 <| fun _ ⟨⟨g, y⟩, hy⟩ =>
    mem_augmentationSubmodule_of_eq (f g) (φ.hom y) _ <| by
      simpa [← hy] using (hom_comm_apply φ _ _).symm

omit [DecidableEq G] in
@[simp]
theorem H0Map_id : H0Map (MonoidHom.id G) (𝟙 A) = 𝟙 _ :=
  ModuleCat.hom_ext <| Submodule.linearMap_qext _ rfl

theorem H0Map_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G →* H) (g : H →* K)
    (φ : A ⟶ (Action.res _ f).obj B) (ψ : B ⟶ (Action.res _ g).obj C) :
    H0Map (g.comp f) (φ ≫ (Action.res _ f).map ψ) = H0Map f φ ≫ H0Map g ψ :=
  ModuleCat.hom_ext <| Submodule.linearMap_qext _ rfl

omit [DecidableEq G] in
theorem H0Map_eq_coinvariantsFunctor_map {A B : Rep k G} (f : A ⟶ B) :
    H0Map (MonoidHom.id G) f = (coinvariantsFunctor k G).map f := by
  rfl

instance epi_H0Map_of_epi {A B : Rep k G} (f : A ⟶ B) [Epi f] :
    Epi (H0Map (MonoidHom.id G) f) :=
  (inferInstanceAs (Epi <| (coinvariantsFunctor k G).map f))

omit [DecidableEq G] [DecidableEq H] in
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem H0π_comp_H0Map :
    H0π A ≫ H0Map f φ = φ.hom ≫ H0π B := rfl

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem map_comp_isoH0_hom :
    map f φ 0 ≫ (isoH0 B).hom = (isoH0 A).hom ≫ H0Map f φ := by
  simp [isoZeroCycles, ← cancel_epi (groupHomologyπ _ _),
    chainsMap_f_0_comp_zeroChainsLequiv_assoc f φ, ← LinearEquiv.toModuleIso_hom]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map from the short complex `(G × G →₀ A) --dOne--> (G →₀ A) --dZero--> A`
to `(H × H →₀ B) --dOne--> (H →₀ B) --dZero--> B`. -/
@[simps]
noncomputable def mapShortComplexH1 :
    shortComplexH1 A ⟶ shortComplexH1 B where
  τ₁ := ModuleCat.ofHom (fTwo f φ)
  τ₂ := ModuleCat.ofHom (fOne f φ)
  τ₃ := φ.hom
  comm₁₂ := ModuleCat.hom_ext <| lhom_ext fun a b => by
    simpa [dOne, map_add, map_sub, shortComplexH1, fTwo, fOne, ← map_inv]
      using congr(Finsupp.single (f a.2) $((hom_comm_apply φ _ _).symm))
  comm₂₃ := ModuleCat.hom_ext <| lhom_ext fun a b => by
    simpa [map_add, map_sub, shortComplexH1, fOne, ← map_inv]
      using (hom_comm_apply φ _ _).symm

@[simp]
theorem mapShortComplexH1_zero :
    mapShortComplexH1 (A := A) (B := B) f 0 = 0 := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ rfl
  all_goals
  { refine ModuleCat.hom_ext <| lhom_ext fun _ _ => ?_
    show mapRange.linearMap 0 (mapDomain _ (single _ _)) = 0
    simp [LinearMap.zero_apply (M₂ := B)] }

@[simp]
theorem mapShortComplexH1_id : mapShortComplexH1 (MonoidHom.id G) (𝟙 A) = 𝟙 _ := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ rfl
  all_goals
  { refine ModuleCat.hom_ext <| Finsupp.lhom_ext fun _ _ => ?_
    show Finsupp.mapRange.linearMap LinearMap.id _ = Finsupp.single _ _
    simp [MonoidHom.coe_id] }

theorem mapShortComplexH1_comp {G H K : Type u} [Group G] [Group H] [Group K]
    [DecidableEq G] [DecidableEq H] [DecidableEq K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G →* H) (g : H →* K)
    (φ : A ⟶ (Action.res _ f).obj B) (ψ : B ⟶ (Action.res _ g).obj C) :
    mapShortComplexH1 (g.comp f) (φ ≫ (Action.res _ f).map ψ) =
      (mapShortComplexH1 f φ) ≫ (mapShortComplexH1 g ψ) := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ rfl
  all_goals
  { refine ModuleCat.hom_ext <| lhom_ext fun _ _ => ?_
    simp [shortComplexH1, Prod.map, fTwo, fOne] }

theorem mapShortComplexH1_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapShortComplexH1 (MonoidHom.id G) (φ ≫ ψ) =
      mapShortComplexH1 (MonoidHom.id G) φ ≫ mapShortComplexH1 (MonoidHom.id G) ψ :=
  mapShortComplexH1_comp (MonoidHom.id G) (MonoidHom.id G) _ _

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map `Z₁(G, A) ⟶ Z₁(H, B)`. -/
noncomputable abbrev mapOneCycles :
    ModuleCat.of k (oneCycles A) ⟶ ModuleCat.of k (oneCycles B) :=
  ShortComplex.cyclesMap' (mapShortComplexH1 f φ) (shortComplexH1 A).moduleCatLeftHomologyData
    (shortComplexH1 B).moduleCatLeftHomologyData

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma mapOneCycles_comp_subtype :
    mapOneCycles f φ ≫ ModuleCat.ofHom (oneCycles B).subtype =
      ModuleCat.ofHom (fOne f φ ∘ₗ (oneCycles A).subtype) :=
  ShortComplex.cyclesMap'_i (mapShortComplexH1 f φ) (moduleCatLeftHomologyData _)
    (moduleCatLeftHomologyData _)

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma cyclesMap_comp_isoOneCycles_hom :
    cyclesMap f φ 1 ≫ (isoOneCycles B).hom =
      (isoOneCycles A).hom ≫ mapOneCycles f φ := by
  simp_rw [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 B)).i, mapOneCycles,
    Category.assoc, cyclesMap'_i, isoOneCycles, ← Category.assoc]
  simp [chainsMap_f_1_comp_oneChainsLequiv f φ, mapShortComplexH1, ← LinearEquiv.toModuleIso_hom]

variable (A) in
instance mapOneCycles_quotientGroupMk'_epi (S : Subgroup G) [S.Normal]
    [DecidableEq (G ⧸ S)] [IsTrivial (A.ρ.comp S.subtype)] :
    Epi (mapOneCycles (QuotientGroup.mk' S) (resOfQuotientIso A S).inv) := by
  rw [ModuleCat.epi_iff_surjective]
  rintro ⟨x, hx⟩
  choose! s hs using QuotientGroup.mk_surjective (s := S)
  have hs₁ : QuotientGroup.mk ∘ s = id := funext hs
  refine ⟨⟨mapDomain s x, ?_⟩, Subtype.ext <| by
    rw [mapOneCycles_comp_subtype_apply]; simp [← mapDomain_comp, hs₁]⟩
  simpa [mem_oneCycles_iff, ← (mem_oneCycles_iff _).1 hx, sum_mapDomain_index_inj (f := s)
      (fun x y h => by rw [← hs x, ← hs y, h])]
    using Finsupp.sum_congr fun a b => QuotientGroup.induction_on a fun a => by
      simp [← QuotientGroup.mk_inv, ρ_eq_of_coe_eq A.ρ S (s a)⁻¹ a⁻¹ (by simp [hs])]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map `H₁(G, A) ⟶ H₁(H, B)`. -/
noncomputable abbrev H1Map : H1 A ⟶ H1 B :=
  ShortComplex.leftHomologyMap' (mapShortComplexH1 f φ)
    (shortComplexH1 A).moduleCatLeftHomologyData (shortComplexH1 B).moduleCatLeftHomologyData

@[simp]
theorem H1Map_id : H1Map (MonoidHom.id G) (𝟙 A) = 𝟙 _ := by
  simp only [H1Map, shortComplexH1, mapShortComplexH1_id, leftHomologyMap'_id]
  rfl

theorem H1Map_comp {G H K : Type u} [Group G] [Group H] [Group K]
    [DecidableEq G] [DecidableEq H] [DecidableEq K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G →* H) (g : H →* K)
    (φ : A ⟶ (Action.res _ f).obj B) (ψ : B ⟶ (Action.res _ g).obj C) :
    H1Map (g.comp f) (φ ≫ (Action.res _ f).map ψ) = H1Map f φ ≫ H1Map g ψ := by
  simpa [H1Map, shortComplexH1, mapShortComplexH1_comp] using leftHomologyMap'_comp _ _ _ _ _

theorem H1Map_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    H1Map (MonoidHom.id G) (φ ≫ ψ) = H1Map (MonoidHom.id G) φ ≫ H1Map (MonoidHom.id G) ψ :=
  H1Map_comp (MonoidHom.id G) (MonoidHom.id G) _ _

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma H1π_comp_H1Map :
    H1π A ≫ H1Map f φ = mapOneCycles f φ ≫ H1π B :=
  leftHomologyπ_naturality' (mapShortComplexH1 f φ) _ _

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma map_comp_isoH1_hom :
    map f φ 1 ≫ (isoH1 B).hom = (isoH1 A).hom ≫ H1Map f φ := by
  simp [← cancel_epi (groupHomologyπ _ _), H1Map, Category.assoc, (leftHomologyπ_naturality'
    (mapShortComplexH1 f φ) (moduleCatLeftHomologyData _) (moduleCatLeftHomologyData _)).symm]

@[simp]
lemma H1Map_one (φ : A ⟶ (Action.res _ (1 : G →* H)).obj B) :
    H1Map (1 : G →* H) φ = 0 := by
  simp only [← cancel_epi (H1π A), H1π_comp_H1Map, Limits.comp_zero]
  ext x
  rw [ModuleCat.hom_comp]
  refine (H1π_eq_zero_iff _).2 ?_
  simpa [← mapDomain_mapRange] using
    Submodule.finsupp_sum_mem _ _ _ _ fun _ _ => single_one_mem_oneBoundaries _

section CoresCoinf

variable (A) (S : Subgroup G) [S.Normal] [DecidableEq (G ⧸ S)]

section OfTrivial

variable [IsTrivial (A.ρ.comp S.subtype)]

/-- Given a `G`-representation `A` on which a normal subgroup `S ≤ G` acts trivially, this is the
short complex `H₁(S, A) ⟶ H₁(G, A) ⟶ H₁(G ⧸ S, A)`. -/
@[simps X₁ X₂ X₃ f g]
noncomputable def H1CoresCoinfOfTrivial :
    ShortComplex (ModuleCat k) where
  X₁ := H1 ((Action.res _ S.subtype).obj A)
  X₂ := H1 A
  X₃ := H1 (ofQuotient A S)
  f := H1Map S.subtype (𝟙 _)
  g := H1Map (QuotientGroup.mk' S) <| (resOfQuotientIso A S).inv
  zero := by
    rw [← H1Map_comp, congr (QuotientGroup.mk'_comp_subtype S) H1Map, H1Map_one]

instance H1Map_quotientGroupMk'_epi :
    Epi (H1Map (QuotientGroup.mk' S) (resOfQuotientIso A S).inv) := by
  convert epi_of_epi (H1π A) _
  rw [H1π_comp_H1Map]
  exact @epi_comp _ _ _ _ _ _ (mapOneCycles_quotientGroupMk'_epi A S) (H1π _) inferInstance

/-- Given a `G`-representation `A` on which a normal subgroup `S ≤ G` acts trivially, the
induced map `H₁(G, A) ⟶ H₁(G ⧸ S, A)` is an epimorphism. -/
instance H1CoresCoinfOfTrivial_g_epi :
    Epi (H1CoresCoinfOfTrivial A S).g :=
  inferInstanceAs <| Epi (H1Map _ _)

/-- Given a `G`-representation `A` on which a normal subgroup `S ≤ G` acts trivially, the short
complex `H₁(S, A) ⟶ H₁(G, A) ⟶ H₁(G ⧸ S, A)` is exact. -/
theorem H1CoresCoinfOfTrivial_exact :
    (H1CoresCoinfOfTrivial A S).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
  intro x hx
/- Denote `C(i) : C(S, A) ⟶ C(G, A), C(π) : C(G, A) ⟶ C(G ⧸ S, A)` and let `x : Z₁(G, A)` map to
0 in `H₁(G ⧸ S, A)`. -/
  induction' x using H1_induction_on with x
  rcases x with ⟨x, hxc⟩
  simp_all only [H1CoresCoinfOfTrivial_X₂, H1CoresCoinfOfTrivial_X₃, H1CoresCoinfOfTrivial_g,
    LinearMap.mem_ker, H1π_comp_H1Map_apply (QuotientGroup.mk' S)]
/- Choose `y := ∑ y(σ, τ)·(σ, τ) ∈ C₂(G ⧸ S, A)` such that `C₁(π)(x) = d(y)`. -/
  rcases (H1π_eq_zero_iff _).1 hx with ⟨y, hy⟩
/- Let `s : G ⧸ S → G` be a section of the quotient map. -/
  choose! s hs using QuotientGroup.mk'_surjective S
  have hs₁ : QuotientGroup.mk (s := S) ∘ s = id := funext hs
/- Let `z := ∑ y(σ, τ)·(s(σ), s(τ))`. -/
  let z : G × G →₀ A := lmapDomain _ k (Prod.map s s) y
/- We have that `C₂(π)(z) = y`. -/
  have hz : lmapDomain _ k (QuotientGroup.mk' S) (dOne A z) = dOne (A.ofQuotient S) y := by
    have := congr($((mapShortComplexH1 (QuotientGroup.mk' S)
      (resOfQuotientIso A S).inv).comm₁₂.symm) z)
    simp_all [shortComplexH1, z, ← mapDomain_comp, Prod.map_comp_map]
  let v := x - dOne _ z
/- We have `C₁(s ∘ π)(v) = ∑ v(g)·s(π(g)) = 0`, since `C₁(π)(v) = dC₁(π)(z) - C₁(π)(dz) = 0` by
previous assumptions. -/
  have hv : mapDomain (s ∘ QuotientGroup.mk) v = 0 := by
    rw [mapDomain_comp]
    simp_all [v, mapDomain, sum_sub_index]
  let e : G → G × G := fun (g : G) => (s (g : G ⧸ S), (s (g : G ⧸ S))⁻¹ * g)
  have he : e.Injective := fun x y hxy => by
    obtain ⟨(h₁ : s _ = s _), (h₂ : _ * _ = _ * _)⟩ := Prod.ext_iff.1 hxy
    exact (mul_right_inj _).1 (h₁ ▸ h₂)
/- Let `ve := ∑ v(g)·(s(π(g)), s(π(g))⁻¹g)`. -/
  let ve : G × G →₀ A := mapDomain e v
  have hS : (v + dOne _ ve).support.toSet ⊆ S := by
  /- We have `d(ve) = ∑ ρ(s(π(g))⁻¹)(v(g))·s(π(g))⁻¹g - ∑ v(g)·g + ∑ v(g)·s(π(g))`.
    The second sum is `v`, so cancels: -/
    simp only [dOne, coe_lsum, he, ve, sum_mapDomain_index_inj, mul_inv_cancel_left,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
      lsingle_apply, sum_add, sum_sub, sum_single, ← add_assoc, add_sub_cancel, e]
    intro w hw
    · obtain (hl | hr) := Finset.mem_union.1 (support_add hw)
    /- The first sum clearly has support in `S`: -/
      · obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.1 (support_sum hl)
        apply support_single_subset at ht
        simp_all [← QuotientGroup.eq, hs]
    /- The third sum is 0, by `hv`. -/
      · simp_all [mapDomain]
  /- Now `v + d(ve)` has support in `S` and agrees with `x` in `H₁(G, A)`: -/
  use H1π _ ⟨comapDomain Subtype.val (v + dOne _ ve) <|
    Set.injOn_of_injective Subtype.val_injective, ?_⟩
  · simp only [H1CoresCoinfOfTrivial_X₁, H1CoresCoinfOfTrivial_f, Action.res_obj_V,
      ModuleCat.hom_ofHom, Submodule.mkQ_apply, H1π_comp_H1Map_apply]
    refine (H1π_eq_iff _ _).2 ?_
  /- Indeed, `v + d(ve) - x = d(ve - z) ∈ B₁(G, A)`, since `v := x - dz`. -/
    use ve - z
    have := mapOneCycles_comp_subtype_apply (B := A) S.subtype (𝟙 _)
    have := mapDomain_comapDomain (α := S) Subtype.val Subtype.val_injective
      (v + dOne A ve) (fun x hx => ⟨⟨x, hS hx⟩, rfl⟩)
    simp_all [-mapOneCycles_comp_subtype_apply, v, add_sub_assoc, sub_add_sub_cancel']
  /- And `v + d(ve) := x - dz + d(ve)` is a 1-cycle because `x` is. -/
  · have : v + dOne _ ve ∈ oneCycles A := Submodule.add_mem _
      (Submodule.sub_mem _ hxc <| dOne_apply_mem_oneCycles _) (dOne_apply_mem_oneCycles _)
    rw [mem_oneCycles_iff] at this ⊢
    rwa [← sum_comapDomain, ← sum_comapDomain (g := fun _ a => a)] at this <;>
    exact ⟨Set.mapsTo_preimage _ _, Set.injOn_of_injective Subtype.val_injective,
      fun x hx => ⟨⟨x, hS hx⟩, hx, rfl⟩⟩

end OfTrivial

end CoresCoinf

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map from the short complex
`(G × G × G →₀ A) --dTwo--> (G × G →₀ A) --dOne--> (G →₀ A)` to
`(H × H × H →₀ B) --dTwo--> (H × H →₀ B) --dOne--> (H →₀ B)`. -/
@[simps]
noncomputable def mapShortComplexH2 :
    shortComplexH2 A ⟶ shortComplexH2 B where
  τ₁ := ModuleCat.ofHom (fThree f φ)
  τ₂ := ModuleCat.ofHom (fTwo f φ)
  τ₃ := ModuleCat.ofHom (fOne f φ)
  comm₁₂ := ModuleCat.hom_ext <| lhom_ext fun a b => by
    simpa [dTwo, shortComplexH2, map_add, map_sub, fThree, fTwo, ← map_inv]
      using congr(Finsupp.single _ $((hom_comm_apply φ _ _).symm))
  comm₂₃ := ModuleCat.hom_ext <| lhom_ext fun a b => by
    simpa [dOne, shortComplexH2, map_add, map_sub, fTwo, fOne, ← map_inv]
      using congr(Finsupp.single _ $((hom_comm_apply φ _ _).symm))

@[simp]
theorem mapShortComplexH2_zero :
    mapShortComplexH2 (A := A) (B := B) f 0 = 0 := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  all_goals
  { refine ModuleCat.hom_ext <| Finsupp.lhom_ext fun _ _ => ?_
    show Finsupp.mapRange.linearMap 0 (Finsupp.mapDomain _ (Finsupp.single _ _)) = 0
    simp [LinearMap.zero_apply (M₂ := B)] }

@[simp]
theorem mapShortComplexH2_id : mapShortComplexH2 (MonoidHom.id _) (𝟙 A) = 𝟙 _ := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  all_goals
  { refine ModuleCat.hom_ext <| Finsupp.lhom_ext fun _ _ => ?_
    show Finsupp.mapRange.linearMap LinearMap.id _ = Finsupp.single _ _
    simp [MonoidHom.coe_id] }

theorem mapShortComplexH2_comp {G H K : Type u} [Group G] [Group H] [Group K]
    [DecidableEq G] [DecidableEq H] [DecidableEq K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G →* H) (g : H →* K)
    (φ : A ⟶ (Action.res _ f).obj B) (ψ : B ⟶ (Action.res _ g).obj C) :
    mapShortComplexH2 (g.comp f) (φ ≫ (Action.res _ f).map ψ) =
      (mapShortComplexH2 f φ) ≫ (mapShortComplexH2 g ψ) := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  all_goals
  { refine ModuleCat.hom_ext <| Finsupp.lhom_ext fun _ _ => ?_
    simp [shortComplexH2, Prod.map, fThree, fTwo, fOne] }

theorem mapShortComplexH2_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapShortComplexH2 (MonoidHom.id G) (φ ≫ ψ) =
      mapShortComplexH2 (MonoidHom.id G) φ ≫ mapShortComplexH2 (MonoidHom.id G) ψ :=
  mapShortComplexH2_comp (MonoidHom.id G) (MonoidHom.id G) _ _

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map `Z₂(G, A) ⟶ Z₂(H, B)`. -/
noncomputable abbrev mapTwoCycles :
    ModuleCat.of k (twoCycles A) ⟶ ModuleCat.of k (twoCycles B) :=
  ShortComplex.cyclesMap' (mapShortComplexH2 f φ) (shortComplexH2 A).moduleCatLeftHomologyData
    (shortComplexH2 B).moduleCatLeftHomologyData

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma mapTwoCycles_comp_subtype :
    mapTwoCycles f φ ≫ ModuleCat.ofHom (twoCycles B).subtype =
      ModuleCat.ofHom (fTwo f φ ∘ₗ (twoCycles A).subtype) :=
  ShortComplex.cyclesMap'_i (mapShortComplexH2 f φ) (moduleCatLeftHomologyData _)
    (moduleCatLeftHomologyData _)

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma cyclesMap_comp_isoTwoCycles_hom :
    cyclesMap f φ 2 ≫ (isoTwoCycles B).hom =
      (isoTwoCycles A).hom ≫ mapTwoCycles f φ := by
  simp_rw [← cancel_mono (moduleCatLeftHomologyData (shortComplexH2 B)).i, mapTwoCycles,
      Category.assoc, cyclesMap'_i, isoTwoCycles, ← Category.assoc]
  simp [chainsMap_f_2_comp_twoChainsLequiv f φ, mapShortComplexH2, ← LinearEquiv.toModuleIso_hom]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map `H₂(G, A) ⟶ H₂(H, B)`. -/
noncomputable abbrev H2Map : H2 A ⟶ H2 B :=
  ShortComplex.leftHomologyMap' (mapShortComplexH2 f φ)
    (shortComplexH2 A).moduleCatLeftHomologyData (shortComplexH2 B).moduleCatLeftHomologyData

@[simp]
theorem H2Map_id : H2Map (MonoidHom.id G) (𝟙 A) = 𝟙 _ := by
  simp only [H2Map, shortComplexH2, mapShortComplexH2_id, leftHomologyMap'_id]
  rfl

theorem H2Map_comp {G H K : Type u} [Group G] [Group H] [Group K]
    [DecidableEq G] [DecidableEq H] [DecidableEq K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G →* H) (g : H →* K)
    (φ : A ⟶ (Action.res _ f).obj B) (ψ : B ⟶ (Action.res _ g).obj C) :
    H2Map (g.comp f) (φ ≫ (Action.res _ f).map ψ) = H2Map f φ ≫ H2Map g ψ := by
  simpa [H2Map, shortComplexH2, mapShortComplexH2_comp] using leftHomologyMap'_comp _ _ _ _ _

theorem H2Map_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    H2Map (MonoidHom.id G) (φ ≫ ψ) = H2Map (MonoidHom.id G) φ ≫ H2Map (MonoidHom.id G) ψ :=
  H2Map_comp (MonoidHom.id G) (MonoidHom.id G) _ _

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma H2π_comp_H2Map :
     H2π A ≫ H2Map f φ = mapTwoCycles f φ ≫ H2π B :=
  leftHomologyπ_naturality' (mapShortComplexH2 f φ) _ _

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma map_comp_isoH2_hom :
    map f φ 2 ≫ (isoH2 B).hom = (isoH2 A).hom ≫ H2Map f φ := by
  simp [← cancel_epi (groupHomologyπ _ _), H2Map, Category.assoc]

variable (k G) in
/-- The functor sending a representation to its complex of inhomogeneous chains. -/
@[simps]
noncomputable def chainsFunctor [DecidableEq G] :
    Rep k G ⥤ ChainComplex (ModuleCat k) ℕ where
  obj A := inhomogeneousChains A
  map f := chainsMap (MonoidHom.id _) f
  map_id _ := chainsMap_id
  map_comp φ ψ := chainsMap_comp (MonoidHom.id G) (MonoidHom.id G) φ ψ

instance : (chainsFunctor k G).PreservesZeroMorphisms where
  map_zero X Y := by
    ext i : 1
    refine ModuleCat.hom_ext <| Finsupp.lhom_ext fun _ _ => ?_
    simp

variable (k G) in
/-- The functor sending a `G`-representation `A` to `Hₙ(G, A)`. -/
@[simps]
noncomputable def functor (n : ℕ) : Rep k G ⥤ ModuleCat k where
  obj A := groupHomology A n
  map {A B} φ := map (MonoidHom.id _) φ n
  map_id A := by simp [map, groupHomology]
  map_comp f g := by
    simp only [← HomologicalComplex.homologyMap_comp, ← chainsMap_comp]
    rfl

instance (n : ℕ) : (functor k G n).PreservesZeroMorphisms where
  map_zero _ _ := by simp [map]

end groupHomology
