/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupCohomology.ToMove

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
this is the chain map sending `∑ aᵢ·gᵢ : Gⁿ →₀ A` to
`∑ φ(aᵢ)·(f ∘ gᵢ) : Hⁿ →₀ B`. -/
@[simps! (config := .lemmasOnly) f f_hom]
noncomputable def chainsMap :
    inhomogeneousChains A ⟶ inhomogeneousChains B where
  f i := ModuleCat.ofHom <| mapRange.linearMap φ.hom.hom ∘ₗ lmapDomain A k (f ∘ ·)
  comm' i j (hij : _ = _) := by
    subst hij
    refine ModuleCat.hom_ext <| lhom_ext fun _ _ => ?_
    simpa [Fin.comp_contractNth, map_add, res_obj_ρ] using
      congr(single _ $((hom_comm_apply φ (_)⁻¹ _).symm))

@[reassoc (attr := simp), elementwise (attr := simp)]
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
lemma chainsMap_f_id_eq_mapRange {A B : Rep k G} (i : ℕ) (φ : A ⟶ B) :
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
`∑ φ(aᵢ)·(f(gᵢ₁), f(gᵢ₂)) : H × H →₀ B`. -/
noncomputable abbrev fTwo : (G × G →₀ A) →ₗ[k] H × H →₀ B :=
  mapRange.linearMap φ.hom.hom ∘ₗ lmapDomain A k (Prod.map f f)

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map sending `∑ aᵢ·(gᵢ₁, gᵢ₂, gᵢ₃) : G × G × G →₀ A` to
`∑ φ(aᵢ)·(f(gᵢ₁), f(gᵢ₂), f(gᵢ₃)) : H × H × H →₀ B`. -/
noncomputable abbrev fThree : (G × G × G →₀ A) →ₗ[k] H × H × H →₀ B :=
  mapRange.linearMap φ.hom.hom ∘ₗ lmapDomain A k (Prod.map f (Prod.map f f))

@[reassoc]
lemma chainsMap_f_0_comp_zeroChainsIso :
    (chainsMap f φ).f 0 ≫ (zeroChainsIso B).hom = (zeroChainsIso A).hom ≫ φ.hom := by
  ext
  simp [zeroChainsIso, Unique.eq_default]

@[reassoc]
lemma chainsMap_f_1_comp_oneChainsIso :
    (chainsMap f φ).f 1 ≫ (oneChainsIso B).hom =
      (oneChainsIso A).hom ≫ ModuleCat.ofHom (fOne f φ) := by
  ext
  simp [oneChainsIso, fOne]

@[reassoc]
lemma chainsMap_f_2_comp_twoChainsIso :
    (chainsMap f φ).f 2 ≫ (twoChainsIso B).hom =
      (twoChainsIso A).hom ≫ ModuleCat.ofHom (fTwo f φ) := by
  ext
  simp [twoChainsIso, fTwo]

@[reassoc]
lemma chainsMap_f_3_comp_threeChainsIso :
    (chainsMap f φ).f 3 ≫ (threeChainsIso B).hom =
      (threeChainsIso A).hom ≫ ModuleCat.ofHom (fThree f φ) := by
  ext
  simp [threeChainsIso, fThree, ← Fin.comp_tail]

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
theorem H0Map_eq_coinvariantsMap {A B : Rep k G} (f : A ⟶ B) :
    H0Map (MonoidHom.id G) f = ModuleCat.ofHom (coinvariantsMap f) := by
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
    chainsMap_f_0_comp_zeroChainsIso_assoc f φ, ← LinearEquiv.toModuleIso_hom]

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
theorem mapShortComplexH1_add (φ ψ : A ⟶ (Action.res _ f).obj B) :
    mapShortComplexH1 f (φ + ψ) = mapShortComplexH1 f φ + mapShortComplexH1 f ψ := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ rfl
  all_goals
  { refine ModuleCat.hom_ext <| lhom_ext fun _ _ => ?_
    simp [shortComplexH1] }

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
lemma mapOneCycles_comp_i :
    mapOneCycles f φ ≫ (shortComplexH1 B).moduleCatLeftHomologyData.i =
      (shortComplexH1 A).moduleCatLeftHomologyData.i ≫ ModuleCat.ofHom (fOne f φ) :=
  ShortComplex.cyclesMap'_i (mapShortComplexH1 f φ) (moduleCatLeftHomologyData _)
    (moduleCatLeftHomologyData _)

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma cyclesMap_comp_isoOneCycles_hom :
    cyclesMap f φ 1 ≫ (isoOneCycles B).hom = (isoOneCycles A).hom ≫ mapOneCycles f φ := by
  simp [← cancel_mono (shortComplexH1 B).moduleCatLeftHomologyData.i,
    chainsMap_f_1_comp_oneChainsIso f φ, ← LinearEquiv.toModuleIso_hom]

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
  simp [← cancel_epi (groupHomologyπ _ _)]

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
theorem mapShortComplexH2_add (φ ψ : A ⟶ (Action.res _ f).obj B) :
    mapShortComplexH2 f (φ + ψ) = mapShortComplexH2 f φ + mapShortComplexH2 f ψ := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  all_goals
  { refine ModuleCat.hom_ext <| lhom_ext fun _ _ => ?_
    simp [shortComplexH2] }

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
lemma mapTwoCycles_comp_i :
    mapTwoCycles f φ ≫ (shortComplexH2 B).moduleCatLeftHomologyData.i =
      (shortComplexH2 A).moduleCatLeftHomologyData.i ≫ ModuleCat.ofHom (fTwo f φ) :=
  ShortComplex.cyclesMap'_i (mapShortComplexH2 f φ) (moduleCatLeftHomologyData _)
    (moduleCatLeftHomologyData _)

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma cyclesMap_comp_isoTwoCycles_hom :
    cyclesMap f φ 2 ≫ (isoTwoCycles B).hom = (isoTwoCycles A).hom ≫ mapTwoCycles f φ := by
  simp [← cancel_mono (shortComplexH2 B).moduleCatLeftHomologyData.i,
    chainsMap_f_2_comp_twoChainsIso f φ, ← LinearEquiv.toModuleIso_hom]

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
  simp [← cancel_epi (groupHomologyπ _ _), Category.assoc]

section Functors

variable (k G)

/-- The functor sending a representation to its complex of inhomogeneous chains. -/
@[simps]
noncomputable def chainsFunctor [DecidableEq G] :
    Rep k G ⥤ ChainComplex (ModuleCat k) ℕ where
  obj A := inhomogeneousChains A
  map f := chainsMap (MonoidHom.id _) f
  map_id _ := chainsMap_id
  map_comp φ ψ := chainsMap_comp (MonoidHom.id G) (MonoidHom.id G) φ ψ

instance : (chainsFunctor k G).PreservesZeroMorphisms where

instance : (chainsFunctor k G).Additive where

/-- The functor sending a `G`-representation `A` to `Zₙ(G, A)`. -/
noncomputable abbrev cyclesFunctor (n : ℕ) : Rep k G ⥤ ModuleCat k :=
  chainsFunctor k G ⋙ HomologicalComplex.cyclesFunctor _ _ n

instance (n : ℕ) : (cyclesFunctor k G n).PreservesZeroMorphisms where
instance (n : ℕ) : (cyclesFunctor k G n).Additive := inferInstance

/-- The functor sending a `G`-representation `A` to `Cₙ(G, A)/Bₙ(G, A)`. -/
noncomputable abbrev opcyclesFunctor (n : ℕ) : Rep k G ⥤ ModuleCat k :=
  chainsFunctor k G ⋙ HomologicalComplex.opcyclesFunctor _ _ n

instance (n : ℕ) : (opcyclesFunctor k G n).PreservesZeroMorphisms where
instance (n : ℕ) : (opcyclesFunctor k G n).Additive := inferInstance

/-- The functor sending a `G`-representation `A` to `Hₙ(G, A)`. -/
noncomputable abbrev functor (n : ℕ) : Rep k G ⥤ ModuleCat k :=
  chainsFunctor k G ⋙ HomologicalComplex.homologyFunctor _ _ n

instance (n : ℕ) : (functor k G n).PreservesZeroMorphisms where
  map_zero _ _ := by simp [map]

instance (n : ℕ) : (functor k G n).Additive := inferInstance

section LowDegree

/-- The functor sending a `G`-representation `A` to its augmentation submodule. -/
@[simps]
noncomputable def augmentationSubmoduleFunctor : Rep k G ⥤ ModuleCat k where
  obj X := ModuleCat.of k (augmentationSubmodule X.ρ)
  map {X Y} f := ModuleCat.ofHom (LinearMap.restrict f.hom.hom fun x hx =>
    (Submodule.span_le (p := Y.ρ.augmentationSubmodule.comap f.hom.hom)).2 (by
     rintro y ⟨z, rfl⟩
     exact mem_augmentationSubmodule_of_eq z.1 (f.hom z.2) _
       (by simp [(hom_comm_apply f z.1 z.2).symm])) hx)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor sending a `G`-representation `A` to `Z₁(G, A)`, using a convenient expression
for `Z₁`. -/
@[simps]
noncomputable def oneCyclesFunctor : Rep k G ⥤ ModuleCat k where
  obj X := ModuleCat.of k (oneCycles X)
  map f := mapOneCycles (MonoidHom.id G) f
  map_id _ := by simp [mapOneCycles, shortComplexH1]
  map_comp _ _ := by simp [mapOneCycles, ← mapShortComplexH1_id_comp, ← cyclesMap'_comp]

instance : (oneCyclesFunctor k G).PreservesZeroMorphisms where
instance : (oneCyclesFunctor k G).Additive where

/-- The functor sending a `G`-representation `A` to `C₁(G, A)/B₁(G, A)`, using a convenient
expression for `C₁/B₁`. . -/
@[simps]
noncomputable def oneOpcyclesFunctor : Rep k G ⥤ ModuleCat k where
  obj X := (shortComplexH1 X).moduleCatRightHomologyData.Q
  map f := (rightHomologyMapData' (mapShortComplexH1 (MonoidHom.id G) f) _ _).φQ
  map_id _ := by ext; simp
  map_comp _ _ := by ext : 1; simp [mapShortComplexH1_id_comp]

instance : (oneOpcyclesFunctor k G).PreservesZeroMorphisms where
  map_zero _ _ := by
    simp only [oneOpcyclesFunctor_obj, oneOpcyclesFunctor_map]
    rw [mapShortComplexH1_zero]
    ext
    simp

instance : (oneOpcyclesFunctor k G).Additive where
  map_add {_ _ _ _} := by
    simp only [oneOpcyclesFunctor_obj, oneOpcyclesFunctor_map]
    rw [mapShortComplexH1_add]
    ext
    simp

/-- The functor sending a `G`-representation `A` to `H₁(G, A)`, using a convenient expression
for `H₁`. . -/
@[simps]
noncomputable def H1Functor : Rep k G ⥤ ModuleCat k where
  obj X := H1 X
  map f := H1Map (MonoidHom.id G) f
  map_comp _ _ := by rw [← H1Map_comp, congr (MonoidHom.id_comp _) H1Map]; rfl

instance : (H1Functor k G).PreservesZeroMorphisms where
  map_zero _ _ := ModuleCat.hom_ext <| by simp [H1Map]

instance : (H1Functor k G).Additive where
  map_add := ModuleCat.hom_ext <| by simp [H1Map, mapShortComplexH1_add (MonoidHom.id G)]

/-- The functor sending a `G`-representation `A` to `Z₂(G, A)`, using a convenient expression
for `Z₂`. -/
@[simps]
noncomputable def twoCyclesFunctor : Rep k G ⥤ ModuleCat k where
  obj X := ModuleCat.of k (twoCycles X)
  map f := mapTwoCycles (MonoidHom.id G) f
  map_id _ := by simp [mapTwoCycles, shortComplexH2]
  map_comp _ _ := by simp [mapTwoCycles, ← mapShortComplexH2_id_comp, ← cyclesMap'_comp]

instance : (twoCyclesFunctor k G).PreservesZeroMorphisms where
instance : (twoCyclesFunctor k G).Additive where

/-- The functor sending a `G`-representation `A` to `C₂(G, A)/B₂(G, A)`, using a convenient
expression for `C₂/B₂`. -/
@[simps]
noncomputable def twoOpcyclesFunctor : Rep k G ⥤ ModuleCat k where
  obj X := (shortComplexH2 X).moduleCatRightHomologyData.Q
  map f := (rightHomologyMapData' (mapShortComplexH2 (MonoidHom.id G) f) _ _).φQ
  map_id _ := by ext; simp
  map_comp _ _ := by ext : 1; simp [mapShortComplexH2_id_comp]

instance : (twoOpcyclesFunctor k G).PreservesZeroMorphisms where
  map_zero _ _ := by
    simp only [twoOpcyclesFunctor_obj, twoOpcyclesFunctor_map]
    rw [mapShortComplexH2_zero]
    ext
    simp

instance : (twoOpcyclesFunctor k G).Additive where
  map_add {_ _ _ _} := by
    simp only [twoOpcyclesFunctor_obj, twoOpcyclesFunctor_map]
    rw [mapShortComplexH2_add]
    ext
    simp

/-- The functor sending a `G`-representation `A` to `H₂(G, A)`, using a convenient expression
for `H₂`. -/
@[simps]
noncomputable def H2Functor : Rep k G ⥤ ModuleCat k where
  obj X := H2 X
  map f := H2Map (MonoidHom.id G) f
  map_comp _ _ := by rw [← H2Map_comp, congr (MonoidHom.id_comp _) H2Map]; rfl

instance : (H2Functor k G).PreservesZeroMorphisms where
  map_zero _ _ := ModuleCat.hom_ext <| by simp [H2Map]

instance : (H2Functor k G).Additive where
  map_add := ModuleCat.hom_ext <| by simp [H2Map, mapShortComplexH2_add (MonoidHom.id G)]

end LowDegree
section NatIsos

/-- The functor sending a `G`-representation `A` to `H₀(G, A) := A_G` is naturally isomorphic to
the general group homology functor at 0. -/
@[simps! hom_app inv_app]
noncomputable def isoCoinvariantsFunctor :
    functor k G 0 ≅ coinvariantsFunctor k G :=
  NatIso.ofComponents (fun _ => isoH0 _) fun f => by simp [H0Map_eq_coinvariantsMap]

/-- The functor sending a `G`-representation `A` to its 0th cycles is naturally isomorphic to the
forgetful functor `Rep k G ⥤ ModuleCat k`. -/
@[simps! hom_app inv_app]
noncomputable def zeroCyclesFunctorIso :
    cyclesFunctor k G 0 ≅ Action.forget (ModuleCat k) G :=
  NatIso.ofComponents (fun A => isoZeroCycles A) fun f => by
    have := chainsMap_f_0_comp_zeroChainsIso (MonoidHom.id G) f
    simp_all [isoZeroCycles]

/-- The functor sending a `G`-representation `A` to its 0th opcycles is naturally isomorphic to the
coinvariants functor `Rep k G ⥤ ModuleCat k`. -/
@[simps! hom_app inv_app]
noncomputable def zeroOpcyclesFunctorIso :
    opcyclesFunctor k G 0 ≅ coinvariantsFunctor k G :=
  NatIso.ofComponents (fun A => isoZeroOpcycles A) fun {X Y} f => by
    have := chainsMap_f_0_comp_zeroChainsIso_assoc (MonoidHom.id G) f (H0π _)
    simp_all [← cancel_epi (HomologicalComplex.pOpcycles _ _), ← H0Map_eq_coinvariantsMap]

@[reassoc, elementwise]
theorem pOpcycles_comp_zeroOpcyclesFunctorIso_hom_app :
    (inhomogeneousChains A).pOpcycles 0 ≫ (zeroOpcyclesFunctorIso k G).hom.app A =
      (zeroChainsIso A).hom ≫ (shortComplexH0 A).g := by
  simp

/-- The functor sending a `G`-representation `A` to `Z₁(G, A)` is naturally isomorphic to the
general cycles functor at 1. -/
@[simps! hom_app inv_app]
noncomputable def isoOneCyclesFunctor :
    cyclesFunctor k G 1 ≅ oneCyclesFunctor k G :=
  NatIso.ofComponents (fun _ => isoOneCycles _) fun f => by simp

/-- The functor sending a `G`-representation `A` to `C₁(G, A)/B₁(G, A)` is naturally isomorphic to
the general opcocycles functor at 1. -/
@[simps! hom_app inv_app]
noncomputable def isoOneOpcyclesFunctor :
    opcyclesFunctor k G 1 ≅ oneOpcyclesFunctor k G :=
  NatIso.ofComponents
    (fun A => (inhomogeneousChains A).opcyclesIsoSc' _ _ _ (by simp) (by simp) ≪≫ opcyclesMapIso
      (shortComplexH1Iso A) ≪≫ (shortComplexH1 A).moduleCatOpcyclesIso) fun f =>
        (cancel_epi (pOpcycles _)).1 <| ModuleCat.hom_ext <| Finsupp.lhom_ext fun a b => by
        have := congr($(chainsMap_f_1_comp_oneChainsIso (MonoidHom.id G) f) (single a b))
        simp_all [HomologicalComplex.opcyclesIsoSc', HomologicalComplex.opcyclesMap,
          shortComplexH1]

@[reassoc, elementwise]
theorem pOpcycles_comp_isoOneOpcyclesFunctor_hom_app :
    (inhomogeneousChains A).pOpcycles 1 ≫ (isoOneOpcyclesFunctor k G).hom.app A =
      (oneChainsIso _).hom ≫ (shortComplexH1 A).moduleCatRightHomologyData.p := by
  simp

/-- The functor sending a `G`-representation `A` to `H₁(G, A)` is naturally isomorphic to the
general group homology functor at 1. -/
@[simps! hom_app inv_app]
noncomputable def isoH1Functor :
    functor k G 1 ≅ H1Functor k G :=
  NatIso.ofComponents (fun _ => isoH1 _) fun f => by simp

/-- The functor sending a `G`-representation `A` to `Z₂(G, A)` is naturally isomorphic to the
general cycles functor at 2. -/
@[simps! hom_app inv_app]
noncomputable def isoTwoCyclesFunctor :
    cyclesFunctor k G 2 ≅ twoCyclesFunctor k G :=
  NatIso.ofComponents (fun _ => isoTwoCycles _) fun f => by simp

/-- The functor sending a `G`-representation `A` to `C₂(G, A)/B₂(G, A)` is naturally isomorphic to
the general opcocycles functor at 2. -/
@[simps! hom_app inv_app]
noncomputable def isoTwoOpcyclesFunctor :
    opcyclesFunctor k G 2 ≅ twoOpcyclesFunctor k G :=
  NatIso.ofComponents
    (fun A => (inhomogeneousChains A).opcyclesIsoSc' _ _ _ (by simp) (by simp) ≪≫ opcyclesMapIso
      (shortComplexH2Iso A) ≪≫ (shortComplexH2 A).moduleCatOpcyclesIso) fun f =>
        (cancel_epi (pOpcycles _)).1 <| ModuleCat.hom_ext <| Finsupp.lhom_ext fun a b => by
        have := congr($(chainsMap_f_2_comp_twoChainsIso (MonoidHom.id G) f) (single a b))
        simp_all [HomologicalComplex.opcyclesIsoSc', HomologicalComplex.opcyclesMap,
          shortComplexH2]

@[reassoc, elementwise]
theorem pOpcycles_comp_isoTwoOpcyclesFunctor_hom_app :
    (inhomogeneousChains A).pOpcycles 2 ≫ (isoTwoOpcyclesFunctor k G).hom.app A =
      (twoChainsIso _).hom ≫ (shortComplexH2 A).moduleCatRightHomologyData.p := by
  simp

/-- The functor sending a `G`-representation `A` to `H₂(G, A)` is naturally isomorphic to the
general group homology functor at 2. -/
@[simps! hom_app inv_app]
noncomputable def isoH2Functor :
    functor k G 2 ≅ H2Functor k G :=
  NatIso.ofComponents (fun _ => isoH2 _) fun f => by simp

end NatIsos
end Functors
end groupHomology
