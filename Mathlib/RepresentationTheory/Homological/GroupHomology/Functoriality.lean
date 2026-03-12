/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree

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
* `groupHomology.coresNatTrans f n`: given a group homomorphism `f : G →* H`, this is a natural
  transformation of `n`th group homology functors which sends `A : Rep k H` to the "corestriction"
  map `Hₙ(G, Res(f)(A)) ⟶ Hₙ(H, A)` induced by `f` and the identity map on `Res(f)(A)`.
* `groupHomology.coinfNatTrans f n`: given a normal subgroup `S ≤ G`, this is a natural
  transformation of `n`th group homology functors which sends `A : Rep k G` to the "coinflation"
  map `Hₙ(G, A) ⟶ Hₙ(G ⧸ S, A_S)` induced by the quotient maps `G →* G ⧸ S` and `A →ₗ A_S`.
* `groupHomology.H1CoresCoinf A S` is the (exact) short complex
  `H₁(S, A) ⟶ H₁(G, A) ⟶ H₁(G ⧸ S, A_S)` for a normal subgroup `S ≤ G` and a `G`-representation
  `A`, defined using the corestriction and coinflation map in degree 1.

-/

@[expose] public section

universe v u

namespace groupHomology

open CategoryTheory Rep Finsupp Representation

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
  {A : Rep k G} {B : Rep k H} (f : G →* H) (φ : A ⟶ res f B) (n : ℕ)

theorem congr {f₁ f₂ : G →* H} (h : f₁ = f₂) {φ : A ⟶ res f₁ B} {T : Type*}
    (F : (f : G →* H) → (φ : A ⟶ res f B) → T) :
    F f₁ φ = F f₂ (h ▸ φ) := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the chain map sending `∑ aᵢ·gᵢ : Gⁿ →₀ A` to `∑ φ(aᵢ)·(f ∘ gᵢ) : Hⁿ →₀ B`. -/
@[simps! -isSimp f f_hom]
noncomputable def chainsMap :
    inhomogeneousChains A ⟶ inhomogeneousChains B where
  f i := ModuleCat.ofHom <| mapRange.linearMap φ.hom.toLinearMap ∘ₗ lmapDomain A k (f ∘ ·)
  comm' i j (hij : _ = _) := by
    subst hij
    ext
    simpa [Fin.comp_contractNth, map_add, inhomogeneousChains.d]
      using congr(single _ $((hom_comm_apply φ (_)⁻¹ _).symm))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma lsingle_comp_chainsMap_f (n : ℕ) (x : Fin n → G) :
    ModuleCat.ofHom (lsingle x) ≫ (chainsMap f φ).f n =
      ModuleCat.ofHom (lsingle (f ∘ x) ∘ₗ φ.hom.toLinearMap) := by
  ext
  simp [chainsMap_f]

set_option backward.isDefEq.respectTransparency false in
lemma chainsMap_f_single (n : ℕ) (x : Fin n → G) (a : A) :
    (chainsMap f φ).f n (single x a) = single (f ∘ x) (φ.hom a) := by
  simp [chainsMap_f]

@[simp]
lemma chainsMap_id :
    chainsMap (MonoidHom.id G) (𝟙 A) = 𝟙 (inhomogeneousChains A) :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext <| lhom_ext' fun _ =>
    ModuleCat.hom_ext_iff.1 <| lsingle_comp_chainsMap_f (k := k) (MonoidHom.id G) ..

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma chainsMap_id_f_hom_eq_mapRange {A B : Rep k G} (i : ℕ) (φ : A ⟶ B) :
    ((chainsMap (MonoidHom.id G) φ).f i).hom = mapRange.linearMap φ.hom.toLinearMap := by
  refine lhom_ext fun _ _ => ?_
  simp [chainsMap_f, MonoidHom.coe_id]

set_option backward.isDefEq.respectTransparency false in
lemma chainsMap_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K}
    (f : G →* H) (g : H →* K) (φ : A ⟶ res f B) (ψ : B ⟶ res g C) :
    chainsMap (g.comp f) (φ ≫ (resFunctor f).map ψ) = chainsMap f φ ≫ chainsMap g ψ := by
  ext
  simp [chainsMap_f, Function.comp_assoc]

lemma chainsMap_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    chainsMap (MonoidHom.id G) (φ ≫ ψ) =
      chainsMap (MonoidHom.id G) φ ≫ chainsMap (MonoidHom.id G) ψ :=
  chainsMap_comp (MonoidHom.id G) (MonoidHom.id G) _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma chainsMap_zero : chainsMap f (0 : A ⟶ res f B) = 0 := by
  ext; simp [chainsMap_f, LinearMap.zero_apply (M₂ := B)]

set_option backward.isDefEq.respectTransparency false in
lemma chainsMap_f_map_mono (hf : Function.Injective f) [Mono φ] (i : ℕ) :
    Mono ((chainsMap f φ).f i) := by
  simpa [ModuleCat.mono_iff_injective] using
    (mapRange_injective φ.hom (map_zero _) <| (Rep.mono_iff_injective k G φ).1
    inferInstance).comp (mapDomain_injective hf.comp_left)

set_option backward.isDefEq.respectTransparency false in
instance chainsMap_id_f_map_mono {A B : Rep k G} (φ : A ⟶ B) [Mono φ] (i : ℕ) :
    Mono ((chainsMap (MonoidHom.id G) φ).f i) :=
  chainsMap_f_map_mono (MonoidHom.id G) φ (fun _ _ h => h) _

set_option backward.isDefEq.respectTransparency false in
lemma chainsMap_f_map_epi (hf : Function.Surjective f) [Epi φ] (i : ℕ) :
    Epi ((chainsMap f φ).f i) := by
  simpa [ModuleCat.epi_iff_surjective] using
    (mapRange_surjective φ.hom (map_zero _) ((Rep.epi_iff_surjective k G φ).1 inferInstance)).comp
    (mapDomain_surjective hf.comp_left)

set_option backward.isDefEq.respectTransparency false in
instance chainsMap_id_f_map_epi {A B : Rep k G} (φ : A ⟶ B) [Epi φ] (i : ℕ) :
    Epi ((chainsMap (MonoidHom.id G) φ).f i) :=
  chainsMap_f_map_epi _ _ (fun x => ⟨x, rfl⟩) _

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map `Zₙ(G, A) ⟶ Zₙ(H, B)` sending `∑ aᵢ·gᵢ : Gⁿ →₀ A` to
`∑ φ(aᵢ)·(f ∘ gᵢ) : Hⁿ →₀ B`. -/
noncomputable abbrev cyclesMap (n : ℕ) :
    groupHomology.cycles A n ⟶ groupHomology.cycles B n :=
  HomologicalComplex.cyclesMap (chainsMap f φ) n

@[simp]
lemma cyclesMap_id : cyclesMap (MonoidHom.id G) (𝟙 A) n = 𝟙 _ := by
  simp [cyclesMap]

@[reassoc]
lemma cyclesMap_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G →* H) (g : H →* K)
    (φ : A ⟶ res f B) (ψ : B ⟶ res g C) (n : ℕ) :
    cyclesMap (g.comp f) (φ ≫ (resFunctor f).map ψ) n = cyclesMap f φ n ≫ cyclesMap g ψ n := by
  simp [cyclesMap, ← HomologicalComplex.cyclesMap_comp, ← chainsMap_comp]

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

set_option backward.isDefEq.respectTransparency false in
@[reassoc, elementwise]
theorem π_map (n : ℕ) :
    π A n ≫ map f φ n = cyclesMap f φ n ≫ π B n := by
  simp [map, cyclesMap]

@[simp]
lemma map_id : map (MonoidHom.id G) (𝟙 A) n = 𝟙 _ := by
  simp [map, groupHomology]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma map_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G →* H) (g : H →* K)
    (φ : A ⟶ res f B) (ψ : B ⟶ res g C) (n : ℕ) :
    map (g.comp f) (φ ≫ (resFunctor f).map ψ) n = map f φ n ≫ map g ψ n := by
  simp [map, ← HomologicalComplex.homologyMap_comp, ← chainsMap_comp]

set_option backward.isDefEq.respectTransparency false in
theorem map_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℕ) :
    map (MonoidHom.id G) (φ ≫ ψ) n =
      map (MonoidHom.id G) φ n ≫ map (MonoidHom.id G) ψ n := by
  rw [map, chainsMap_id_comp, HomologicalComplex.homologyMap_comp]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map sending `∑ aᵢ·gᵢ : G →₀ A` to `∑ φ(aᵢ)·f(gᵢ) : H →₀ B`. -/
noncomputable abbrev chainsMap₁ : ModuleCat.of k (G →₀ A) ⟶ ModuleCat.of k (H →₀ B) :=
  ModuleCat.ofHom <| mapRange.linearMap φ.hom.toLinearMap ∘ₗ lmapDomain A k f

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map sending `∑ aᵢ·(gᵢ₁, gᵢ₂) : G × G →₀ A` to
`∑ φ(aᵢ)·(f(gᵢ₁), f(gᵢ₂)) : H × H →₀ B`. -/
noncomputable abbrev chainsMap₂ : ModuleCat.of k (G × G →₀ A) ⟶ ModuleCat.of k (H × H →₀ B) :=
  ModuleCat.ofHom <| mapRange.linearMap φ.hom.toLinearMap ∘ₗ lmapDomain A k (Prod.map f f)

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map sending `∑ aᵢ·(gᵢ₁, gᵢ₂, gᵢ₃) : G × G × G →₀ A` to
`∑ φ(aᵢ)·(f(gᵢ₁), f(gᵢ₂), f(gᵢ₃)) : H × H × H →₀ B`. -/
noncomputable abbrev chainsMap₃ :
    ModuleCat.of k (G × G × G →₀ A) ⟶ ModuleCat.of k (H × H × H →₀ B) :=
  ModuleCat.ofHom <| mapRange.linearMap φ.hom.toLinearMap ∘ₗ
    lmapDomain A k (Prod.map f (Prod.map f f))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma chainsMap_f_0_comp_chainsIso₀ :
    (chainsMap f φ).f 0 ≫ (chainsIso₀ B).hom = (chainsIso₀ A).hom ≫
      ModuleCat.ofHom φ.hom.toLinearMap := by
  ext
  simp [chainsMap_f, Unique.eq_default (α := Fin 0 → G), Unique.eq_default (α := Fin 0 → H),
    chainsIso₀]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma chainsMap_f_1_comp_chainsIso₁ :
    (chainsMap f φ).f 1 ≫ (chainsIso₁ B).hom = (chainsIso₁ A).hom ≫ chainsMap₁ f φ := by
  ext x
  simp [chainsMap_f, chainsIso₁]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma chainsMap_f_2_comp_chainsIso₂ :
    (chainsMap f φ).f 2 ≫ (chainsIso₂ B).hom = (chainsIso₂ A).hom ≫ chainsMap₂ f φ := by
  ext
  simp [chainsMap_f, chainsIso₂]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma chainsMap_f_3_comp_chainsIso₃ :
    (chainsMap f φ).f 3 ≫ (chainsIso₃ B).hom = (chainsIso₃ A).hom ≫ chainsMap₃ f φ := by
  ext
  simp [chainsMap_f, chainsIso₃, ← Fin.comp_tail]

open ShortComplex

section H0

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem cyclesMap_comp_cyclesIso₀_hom :
    cyclesMap f φ 0 ≫ (cyclesIso₀ B).hom = (cyclesIso₀ A).hom ≫
      ModuleCat.ofHom φ.hom.toLinearMap := by
  simp [cyclesIso₀]

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem cyclesIso₀_inv_comp_cyclesMap :
    (cyclesIso₀ A).inv ≫ cyclesMap f φ 0 = ModuleCat.ofHom φ.hom.toLinearMap ≫ (cyclesIso₀ B).inv :=
  (CommSq.vert_inv ⟨cyclesMap_comp_cyclesIso₀_hom f φ⟩).w.symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem H0π_comp_map :
    H0π A ≫ map f φ 0 = ModuleCat.ofHom φ.hom.toLinearMap ≫ H0π B := by
  simp [H0π]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem map_id_comp_H0Iso_hom {A B : Rep k G} (f : A ⟶ B) :
    map (MonoidHom.id G) f 0 ≫ (H0Iso B).hom =
      (H0Iso A).hom ≫ (coinvariantsFunctor k G).map f := by
  rw [← cancel_epi (H0π A)]
  ext
  simp

set_option backward.isDefEq.respectTransparency false in
instance epi_map_0_of_epi {A B : Rep k G} (f : A ⟶ B) [Epi f] :
    Epi (map (MonoidHom.id G) f 0) where
  left_cancellation g h hgh := by
    simp only [← cancel_epi (H0π A)] at hgh
    simp_all [cancel_epi]

end H0

section H1

set_option backward.isDefEq.respectTransparency false in
/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map from the short complex `(G × G →₀ A) --d₂₁--> (G →₀ A) --d₁₀--> A`
to `(H × H →₀ B) --d₂₁--> (H →₀ B) --d₁₀--> B`. -/
@[simps]
noncomputable def mapShortComplexH1 :
    shortComplexH1 A ⟶ shortComplexH1 B where
  τ₁ := chainsMap₂ f φ
  τ₂ := chainsMap₁ f φ
  τ₃ := ModuleCat.ofHom φ.hom.toLinearMap
  comm₁₂ := by
    simp only [shortComplexH1]
    ext : 3
    simpa [d₂₁, map_add, map_sub, ← map_inv] using congr(single _ $((hom_comm_apply φ _ _).symm))
  comm₂₃ := by
    simp only [shortComplexH1]
    ext : 3
    simpa [← map_inv, d₁₀] using (hom_comm_apply φ _ _).symm

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem mapShortComplexH1_zero :
    mapShortComplexH1 (A := A) (B := B) f 0 = 0 := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ rfl
  all_goals
  { simp only [shortComplexH1]
    ext
    simp }

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem mapShortComplexH1_id : mapShortComplexH1 (MonoidHom.id G) (𝟙 A) = 𝟙 _ := by
  simp only [shortComplexH1]
  ext <;> simp

set_option backward.isDefEq.respectTransparency false in
theorem mapShortComplexH1_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G →* H) (g : H →* K)
    (φ : A ⟶ res f B) (ψ : B ⟶ res g C) :
    mapShortComplexH1 (g.comp f) (φ ≫ (resFunctor f).map ψ) =
      (mapShortComplexH1 f φ) ≫ (mapShortComplexH1 g ψ) := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ rfl
  all_goals
  { simp only [shortComplexH1]
    ext
    simp [Prod.map]}

theorem mapShortComplexH1_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapShortComplexH1 (MonoidHom.id G) (φ ≫ ψ) =
      mapShortComplexH1 (MonoidHom.id G) φ ≫ mapShortComplexH1 (MonoidHom.id G) ψ :=
  mapShortComplexH1_comp (MonoidHom.id G) (MonoidHom.id G) _ _

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map `Z₁(G, A) ⟶ Z₁(H, B)`. -/
noncomputable abbrev mapCycles₁ :
    ModuleCat.of k (cycles₁ A) ⟶ ModuleCat.of k (cycles₁ B) :=
  ShortComplex.cyclesMap' (mapShortComplexH1 f φ) (shortComplexH1 A).moduleCatLeftHomologyData
    (shortComplexH1 B).moduleCatLeftHomologyData

set_option backward.isDefEq.respectTransparency false in
lemma mapCycles₁_hom :
    (mapCycles₁ f φ).hom = (chainsMap₁ f φ).hom.restrict (fun x _ => by
      have := congr($((mapShortComplexH1 f φ).comm₂₃) x); simp_all [cycles₁, shortComplexH1]) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc, elementwise]
lemma mapCycles₁_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G →* H) (g : H →* K)
    (φ : A ⟶ res f B) (ψ : B ⟶ res g C) :
    mapCycles₁ (g.comp f) (φ ≫ (resFunctor f).map ψ) =
      mapCycles₁ f φ ≫ mapCycles₁ g ψ := by
  rw [← cyclesMap'_comp, ← mapShortComplexH1_comp]

@[reassoc, elementwise]
theorem mapCycles₁_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapCycles₁ (MonoidHom.id G) (φ ≫ ψ) =
      mapCycles₁ (MonoidHom.id G) φ ≫ mapCycles₁ (MonoidHom.id G) ψ :=
  mapCycles₁_comp (MonoidHom.id G) (MonoidHom.id G) _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc, elementwise]
lemma mapCycles₁_comp_i :
    mapCycles₁ f φ ≫ (shortComplexH1 B).moduleCatLeftHomologyData.i =
      (shortComplexH1 A).moduleCatLeftHomologyData.i ≫ chainsMap₁ f φ := by
  simp

@[simp]
lemma coe_mapCycles₁ (x) :
    (mapCycles₁ f φ x).1 = chainsMap₁ f φ x := rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma cyclesMap_comp_isoCycles₁_hom :
    cyclesMap f φ 1 ≫ (isoCycles₁ B).hom = (isoCycles₁ A).hom ≫ mapCycles₁ f φ := by
  simp [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 B)).i, mapShortComplexH1,
    chainsMap_f_1_comp_chainsIso₁ f]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma H1π_comp_map :
    H1π A ≫ map f φ 1 = mapCycles₁ f φ ≫ H1π B := by
  simp [H1π, Iso.inv_comp_eq, ← cyclesMap_comp_isoCycles₁_hom_assoc]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma map₁_one (φ : A ⟶ res (1 : G →* H) B) :
    map (1 : G →* H) φ 1 = 0 := by
  simp only [← cancel_epi (H1π A), H1π_comp_map, Limits.comp_zero]
  ext x
  rw [ModuleCat.hom_comp]
  refine (H1π_eq_zero_iff _).2 ?_
  simpa [coe_mapCycles₁ _ φ x, mapDomain, map_finsuppSum] using
    (boundaries₁ B).finsuppSum_mem k x.1 _ fun _ _ => single_one_mem_boundaries₁ (A := B) _

section CoresCoinf

/-!
### Exactness of the corestriction-coinflation sequence in degree 1

Given a group homomorphism `f : G →* H`, the `n`th corestriction map is the map
`Hₙ(G, Res(f)(A)) ⟶ Hₙ(H, A)` induced by `f` and the identity map on `Res(f)(A)`. Similarly, given
a normal subgroup `S ≤ G`, we define the `n`th coinflation map `Hₙ(G, A) ⟶ Hₙ(G ⧸ S, A_S)` as the
map induced by the quotient maps `G →* G ⧸ S` and `A →ₗ A_S`.

In particular, for `S ≤ G` normal and `A : Rep k G`, the corestriction map
`Hₙ(S, Res(ι)(A)) ⟶ Hₙ(G, A)` and the coinflation map `Hₙ(G, A) ⟶ Hₙ(G ⧸ S, A_S)` form a short
complex, where `ι : S →* G` is the natural inclusion. In this section we define this short complex
for degree 1, `groupHomology.H1CoresCoinf A S`, and prove it is exact.

We do this first when `A` is `S`-trivial, and then extend to the general case.

-/

variable (A) (S : Subgroup G) [S.Normal]

section OfTrivial

variable [IsTrivial (A.ρ.comp S.subtype)]

set_option backward.isDefEq.respectTransparency false in
instance mapCycles₁_quotientGroupMk'_epi :
    Epi (mapCycles₁ (QuotientGroup.mk' S) (resOfQuotientIso A S).inv) := by
  rw [ModuleCat.epi_iff_surjective]
  rintro ⟨x, hx⟩
  choose! s hs using QuotientGroup.mk_surjective (s := S)
  have hs₁ : QuotientGroup.mk ∘ s = id := funext hs
  refine ⟨⟨mapDomain s x, ?_⟩, Subtype.ext <| by
    simp [mapCycles₁_hom, ← mapDomain_comp, hs₁, res, Rep.hom_id (of _)]⟩
  simpa [mem_cycles₁_iff, ← (mem_cycles₁_iff _).1 hx, sum_mapDomain_index_inj (f := s)
      (fun x y h => by rw [← hs x, ← hs y, h])]
    using Finsupp.sum_congr fun a b => QuotientGroup.induction_on a fun a => by
      simp [← QuotientGroup.mk_inv, apply_eq_of_coe_eq A.ρ S (s a)⁻¹ a⁻¹ (by simp [hs])]

/-- Given a `G`-representation `A` on which a normal subgroup `S ≤ G` acts trivially, this is the
short complex `H₁(S, A) ⟶ H₁(G, A) ⟶ H₁(G ⧸ S, A)`. (This is a simplified expression for the
degree 1 corestriction-coinflation sequence when `A` is `S`-trivial.) -/
@[simps X₁ X₂ X₃ f g]
noncomputable def H1CoresCoinfOfTrivial :
    ShortComplex (ModuleCat k) where
  X₁ := H1 (res S.subtype A)
  X₂ := H1 A
  X₃ := H1 (ofQuotient A S)
  f := map S.subtype (𝟙 _) 1
  g := map (QuotientGroup.mk' S) (resOfQuotientIso A S).inv 1
  zero := by rw [← map_comp, congr (QuotientGroup.mk'_comp_subtype S) (map (n := 1)), map₁_one]

instance map₁_quotientGroupMk'_epi :
    Epi (map (QuotientGroup.mk' S) (resOfQuotientIso A S).inv 1) := by
  convert epi_of_epi (H1π A) _
  rw [H1π_comp_map]
  exact @epi_comp _ _ _ _ _ _ (mapCycles₁_quotientGroupMk'_epi A S) (H1π _) inferInstance

/-- Given a `G`-representation `A` on which a normal subgroup `S ≤ G` acts trivially, the
induced map `H₁(G, A) ⟶ H₁(G ⧸ S, A)` is an epimorphism. -/
instance H1CoresCoinfOfTrivial_g_epi :
    Epi (H1CoresCoinfOfTrivial A S).g :=
  inferInstanceAs <| Epi (map _ _ 1)

lemma _root_.Finsupp.mapDomain_sub {α β M : Type*} [AddCommGroup M] {v₁ v₂ : α →₀ M} {f : α → β} :
    mapDomain f (v₁ - v₂) = mapDomain f v₁ - mapDomain f v₂ := by
  simp [mapDomain, sum_sub_index]

set_option backward.isDefEq.respectTransparency false in
/-- Given a `G`-representation `A` on which a normal subgroup `S ≤ G` acts trivially, the short
complex `H₁(S, A) ⟶ H₁(G, A) ⟶ H₁(G ⧸ S, A)` is exact. -/
theorem H1CoresCoinfOfTrivial_exact :
    (H1CoresCoinfOfTrivial A S).Exact := by
  classical
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
  intro x hx
/- Denote `C(i) : C(S, A) ⟶ C(G, A), C(π) : C(G, A) ⟶ C(G ⧸ S, A)` and let `x : Z₁(G, A)` map to
0 in `H₁(G ⧸ S, A)`. -/
  induction x using H1_induction_on with | @h x =>
  rcases x with ⟨x, hxc⟩
  simp_all only [H1CoresCoinfOfTrivial_X₂, H1CoresCoinfOfTrivial_X₃, H1CoresCoinfOfTrivial_g,
    LinearMap.mem_ker, H1π_comp_map_apply (QuotientGroup.mk' S)]
/- Choose `y := ∑ y(σ, τ)·(σ, τ) ∈ C₂(G ⧸ S, A)` such that `C₁(π)(x) = d(y)`. -/
  rcases (H1π_eq_zero_iff _).1 hx with ⟨y, hy⟩
/- Let `s : G ⧸ S → G` be a section of the quotient map. -/
  choose! s hs using QuotientGroup.mk'_surjective S
  have hs₁ : QuotientGroup.mk (s := S) ∘ s = id := funext hs
/- Let `z := ∑ y(σ, τ)·(s(σ), s(τ))`. -/
  let z : G × G →₀ A := lmapDomain _ k (Prod.map s s) y
/- We have that `C₂(π)(z) = y`. -/
  have hz : lmapDomain _ k (QuotientGroup.mk' S) ((d₂₁ A).hom z) =
      (d₂₁ (A.ofQuotient S)).hom y := by
    have := congr($((mapShortComplexH1 (QuotientGroup.mk' S)
      (resOfQuotientIso A S).inv).comm₁₂.symm) z)
    simp_all [shortComplexH1, z, ← mapDomain_comp, Prod.map_comp_map, Rep.hom_id (res _ _)]
  let v := x - (d₂₁ _).hom z
/- We have `C₁(s ∘ π)(v) = ∑ v(g)·s(π(g)) = 0`, since `C₁(π)(v) = dC₁(π)(z) - C₁(π)(dz) = 0` by
previous assumptions. -/
  have hv : mapDomain (s ∘ QuotientGroup.mk) v = 0 := by
    rw [mapDomain_comp]
    simp only [QuotientGroup.coe_mk', lmapDomain_apply, mapDomain_sub, v] at hz ⊢
    simp [hz, hy, coe_mapCycles₁ (QuotientGroup.mk' S), Rep.hom_id (of _)]
  let e : G → G × G := fun (g : G) => (s (g : G ⧸ S), (s (g : G ⧸ S))⁻¹ * g)
  have he : e.Injective := fun x y hxy => by
    obtain ⟨(h₁ : s _ = s _), (h₂ : _ * _ = _ * _)⟩ := Prod.ext_iff.1 hxy
    exact (mul_right_inj _).1 (h₁ ▸ h₂)
/- Let `ve := ∑ v(g)·(s(π(g)), s(π(g))⁻¹g)`. -/
  let ve : G × G →₀ A := mapDomain e v
  have hS : ((v + d₂₁ _ ve).support : Set G) ⊆ S := by
  /- We have `d(ve) = ∑ ρ(s(π(g))⁻¹)(v(g))·s(π(g))⁻¹g - ∑ v(g)·g + ∑ v(g)·s(π(g))`.
    The second sum is `v`, so cancels: -/
    simp only [d₂₁, ve, ModuleCat.hom_ofHom, coe_lsum, sum_mapDomain_index_inj he, sum_single,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
      lsingle_apply, sum_add, sum_sub, mul_inv_cancel_left, ← add_assoc, add_sub_cancel, e]
    intro w hw
    · obtain (hl | hr) := Finset.mem_union.1 (support_add hw)
    /- The first sum clearly has support in `S`: -/
      · obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.1 (support_sum hl)
        apply support_single_subset at ht
        simp_all [← QuotientGroup.eq]
    /- The third sum is 0, by `hv`. -/
      · simp_all [mapDomain]
  /- Now `v + d(ve)` has support in `S` and agrees with `x` in `H₁(G, A)`: -/
  use H1π _ ⟨comapDomain Subtype.val (v + d₂₁ _ ve) <|
    Set.injOn_of_injective Subtype.val_injective, ?_⟩
  · simp only [H1CoresCoinfOfTrivial_f, H1CoresCoinfOfTrivial_X₁, H1π_comp_map_apply]
    refine (H1π_eq_iff _ _).2 ?_
  /- Indeed, `v + d(ve) - x = d(ve - z) ∈ B₁(G, A)`, since `v := x - dz`. -/
    use ve - z
    have := mapDomain_comapDomain (α := S) Subtype.val Subtype.val_injective
      (v + d₂₁ A ve) (fun x hx => ⟨⟨x, hS hx⟩, rfl⟩)
    simp_all [mapCycles₁_hom, v, add_sub_assoc, sub_add_sub_cancel']
  /- And `v + d(ve) := x - dz + d(ve)` is a 1-cycle because `x` is. -/
  · have : v + d₂₁ _ ve ∈ cycles₁ A := Submodule.add_mem _
      (Submodule.sub_mem _ hxc <| d₂₁_apply_mem_cycles₁ _) (d₂₁_apply_mem_cycles₁ _)
    rw [mem_cycles₁_iff] at this ⊢
    rwa [← sum_comapDomain, ← sum_comapDomain (g := fun _ a => a)] at this <;>
    exact ⟨Set.mapsTo_preimage _ _, Set.injOn_of_injective Subtype.val_injective,
      fun x hx => ⟨⟨x, hS hx⟩, hx, rfl⟩⟩

end OfTrivial

/-- The short complex `H₁(S, A) ⟶ H₁(G, A) ⟶ H₁(G ⧸ S, A_S)`. The first map is the
"corestriction" map induced by the inclusion `ι : S →* G` and the identity on `Res(ι)(A)`, and the
second map is the "coinflation" map induced by the quotient maps `G →* G ⧸ S` and `A →ₗ A_S`. -/
@[simps X₁ X₂ X₃ f g]
noncomputable def H1CoresCoinf :
    ShortComplex (ModuleCat k) where
  X₁ := H1 (res S.subtype A)
  X₂ := H1 A
  X₃ := H1 (quotientToCoinvariants A S)
  f := map S.subtype (𝟙 _) 1
  g := map (QuotientGroup.mk' S) (Rep.toCoinvariantsMkQ A S) 1
  zero := by rw [← map_comp, congr (QuotientGroup.mk'_comp_subtype S) (map (n := 1)), map₁_one]

set_option backward.isDefEq.respectTransparency false in
/-- Given a `G`-representation `A` and a normal subgroup `S ≤ G`, let `I(S)A` denote the submodule
of `A` spanned by elements of the form `ρ(s)(a) - a` for `s : S, a : A`. Then the image of
`C₁(G, I(S)A)` in `C₁(G, A)⧸B₁(G, A)` is contained in the image of `C₁(S, A)`. -/
theorem comap_coinvariantsKer_pOpcycles_range_subtype_pOpcycles_eq_top :
    Submodule.comap ((mapShortComplexH1 (MonoidHom.id G) (coinvariantsShortComplex A S).f).τ₂ ≫
      (shortComplexH1 _).pOpcycles).hom (LinearMap.range ((mapShortComplexH1 S.subtype (𝟙 _)).τ₂ ≫
      (shortComplexH1 _).pOpcycles).hom) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rcases mapRange_surjective _ (map_zero _) (chains₁ToCoinvariantsKer_surjective
    (res S.subtype A)) x with ⟨(X : G →₀ S →₀ A), hX⟩
  let Y : S →₀ A := X.sum fun g f =>
    mapRange.linearMap (A.ρ g⁻¹) (lmapDomain _ k (fun s => MulAut.conjNormal g⁻¹ s) f) - f
  let Z : G × G →₀ A := X.sum fun g f =>
    lmapDomain _ k (fun s => (g, g⁻¹ * s.1 * g)) f - lmapDomain _ k (fun s => (s.1, g)) f
  use Y
  apply (moduleCat_pOpcycles_eq_iff _ _ _).2 ⟨Z, ?_⟩
  change d₂₁ A Z = mapRange id rfl (lmapDomain _ k Subtype.val Y) -
    mapRange.linearMap (Submodule.subtype _) (mapDomain id x)
  simpa [map_finsuppSum, mapDomain, map_sub, ← hX, sum_single_index, curryLinearEquiv,
    curryEquiv, Finsupp.uncurry, d₂₁, Y, Z, sum_mapRange_index,
    chains₁ToCoinvariantsKer, d₁₀, single_sum, mul_assoc, sub_add_eq_add_sub,
    sum_sum_index, add_smul, sub_sub_sub_eq, lsingle, singleAddHom] using add_comm _ _

#print "change mkQ to Representation level"
set_option backward.isDefEq.respectTransparency false in
/-- Given a `G`-representation `A` and a normal subgroup `S ≤ G`, the map
`H₁(G, A) ⟶ H₁(G ⧸ S, A_S)` induced by the quotient maps `G →* G ⧸ S` and `A →ₗ A_S` is an
epimorphism. -/
instance : Epi (H1CoresCoinf A S).g := by
  rw [ModuleCat.epi_iff_surjective]
  intro x
  induction x using H1_induction_on with | @h x =>
/- Let `x : Z₁(G ⧸ S, A_S)`. We know `Z₁(G, A_S) ⟶ Z₁(G ⧸ S, A_S)` is surjective, so pick
`y : Z₁(G, A_S)` in the preimage of `x`. -/
  rcases (ModuleCat.epi_iff_surjective _).1
    (mapCycles₁_quotientGroupMk'_epi (A.toCoinvariants S) S) x with ⟨y, hy⟩
/- We know `C₁(G, A) ⟶ C₁(G, A_S)` is surjective, so pick `Y` in the preimage of `y`. -/
  rcases mapRange_surjective _ (map_zero _)
    (Coinvariants.mk_surjective (A.ρ.comp S.subtype)) y.1 with ⟨Y, hY⟩
/- Then `d(Y) ∈ I(S)A,` since `d(y) = 0`. -/
  have : d₁₀ _ Y ∈ Coinvariants.ker (A.ρ.comp S.subtype) := by
    have h' := congr($((mapShortComplexH1 (B := toCoinvariants A S)
      (MonoidHom.id G) (toCoinvariantsMkQ A S)).comm₂₃) Y)
    simp only [shortComplexH1, mapShortComplexH1_τ₂, ModuleCat.ofHom_comp, MonoidHom.coe_id,
      lmapDomain_id, ModuleCat.ofHom_id, res_obj_ρ, hom_ofHom, Category.id_comp, ModuleCat.hom_comp,
      ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply, mapRange.linearMap_apply,
      IntertwiningMap.coe_toLinearMap, mapShortComplexH1_τ₃] at h'
    change (d₁₀ (A.toCoinvariants S)).hom (mapRange (Coinvariants.mk _) _ _) =
      Coinvariants.mk _ _ at h'
    simp [← Coinvariants.mk_eq_zero, ← h', hY]
  /- Thus we can pick a representation of `d(Y)` as a sum `∑ ρ(sᵢ⁻¹)(aᵢ) - aᵢ`, `sᵢ ∈ S, aᵢ ∈ A`,
and `Y - ∑ aᵢ·sᵢ` is a cycle. -/
  rcases chains₁ToCoinvariantsKer_surjective
    (res S.subtype A) ⟨d₁₀ A Y, this⟩ with ⟨(Z : S →₀ A), hZ⟩
  have H : d₁₀ A (Y - mapDomain S.subtype Z) = 0 := by
    simpa [map_sub, sub_eq_zero, chains₁ToCoinvariantsKer, - LinearMap.sub_apply, d₁₀,
      sum_mapDomain_index_inj] using Subtype.ext_iff.1 hZ.symm
  use H1π A ⟨Y - mapDomain S.subtype Z, H⟩
  simp only [H1CoresCoinf_X₃, H1CoresCoinf_X₂, H1CoresCoinf_g,
    Subgroup.coe_subtype, H1π_comp_map_apply]
/- Moreover, the image of `Y - ∑ aᵢ·sᵢ` in `Z₁(G ⧸ S, A_S)` is `x - ∑ aᵢ·1`, and hence differs from
`x` by a boundary, since `aᵢ·1 = d(aᵢ·(1, 1))`. -/
  refine (H1π_eq_iff _ _).2 ?_
  change mapRange (A.ρ.toCoinvariantsMkQ S) _ Y = _ at hY
  simpa [← hy, mapCycles₁_hom, map_sub, Rep.hom_id (res _ _), ← mapDomain_comp,
    ← mapDomain_mapRange, hY, Function.comp_def, (QuotientGroup.eq_one_iff <| Subtype.val _).2
    (Subtype.prop _)] using Submodule.finsuppSum_mem _ _ _ _ fun _ _ ↦ single_one_mem_boundaries₁ _

set_option backward.isDefEq.respectTransparency false in
/-- Given a `G`-representation `A` and a normal subgroup `S ≤ G`, the degree 1
corestriction-coinflation sequence `H₁(S, A) ⟶ H₁(G, A) ⟶ H₁(G ⧸ S, A_S)` is exact. `simp`s
squeezed for performance. -/
theorem H1CoresCoinf_exact :
    (H1CoresCoinf A S).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
  intro x hx
  induction x using H1_induction_on with | @h x =>
  simp only [H1CoresCoinf_X₂, H1CoresCoinf_X₃, LinearMap.mem_ker, H1CoresCoinf_g,
    H1π_comp_map_apply (QuotientGroup.mk' S)] at hx
/- Let `x : Z₁(G, A)` map to 0 in `H₁(G, ⧸ S, A_S)`. Pick `y : C₂(G ⧸ S, A_S)` such that `d(y)`
equals `Z₁(π, π)(x) : Z₁(G ⧸ S, A_S)`. -/
  rcases (H1π_eq_zero_iff _).1 hx with ⟨y, hy⟩
/- Then `Z₁(π, Id)(x) : Z₁(G, A_S)` maps to 0 in `H₁(G ⧸ S, A_S)`. We know
`H₁(S, A_S) ⟶ H₁(G, A_S) ⟶ H₁(G ⧸ S, A_S)` is exact by `H1CoresCoinfOfTrivial_exact`, since
`S` acts trivially on `A_S`. So we can choose `z : Z₁(S, A_S)` with the same homology class as
`Z₁(π, Id)(π)` in `H₁(G, A_S)`. -/
  rcases @(ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    (H1CoresCoinfOfTrivial_exact (toCoinvariants A S) S)
    (H1π _ <| mapCycles₁ (MonoidHom.id G) (Rep.toCoinvariantsMkQ A S) x) (by
    simpa only [H1CoresCoinfOfTrivial_X₂, H1CoresCoinfOfTrivial_X₃, H1CoresCoinfOfTrivial_g,
      Iso.refl_inv, LinearMap.mem_ker, H1π_comp_map_apply (QuotientGroup.mk' S),
      ← mapCycles₁_comp_apply (x := x)] using hx) with ⟨z, hz⟩
  induction z using H1_induction_on with | @h z =>
  simp only [H1CoresCoinfOfTrivial_X₂, H1CoresCoinfOfTrivial_X₁, H1CoresCoinfOfTrivial_f] at hz
  rw [H1π_comp_map_apply] at hz
/- Choose `w : C₂(G, A_S)` such that `d(w) = Z₁(i, Id)(z) - Z₁(Id, π)(x)`. -/
  rcases (H1π_eq_iff _ _).1 hz with ⟨w, hzw⟩
/- Choose `Z : C₁(S, A)` mapping to `z : C₁(S, A_S)`, and `W : C₂(G, A)` mapping to
`w : C₂(G, A_S)`. -/
  rcases mapRange_surjective (Coinvariants.mk _) (map_zero _)
    (Coinvariants.mk_surjective _) z.1 with ⟨Z, hZ⟩
  rcases mapRange_surjective (Coinvariants.mk _) (map_zero _)
    (Coinvariants.mk_surjective _) w with ⟨W, hW⟩
/- Let `b : C₁(G, A)` denote `x + d(W) - C₁(i, Id)(z)`. -/
  let b : G →₀ A := (x.1 : G →₀ A) + d₂₁ A W - lmapDomain _ k S.subtype Z
/- Then `b` has coefficients in `I(S)A := ⟨{ρ(s)(a) - a | s ∈ S, a ∈ A}⟩`, since
`C₁(G, I(S)(A)) ⟶ C₁(G, A) ⟶ C₁(G, A_S)` is exact, and `b` is in the kernel of the second map. -/
  have hb : ∀ g, b g ∈ Coinvariants.ker (A.ρ.comp S.subtype) :=
    fun g => (Coinvariants.mk_eq_iff _).1 <| by
      have := Finsupp.ext_iff.1 (congr($((mapShortComplexH1 (B := toCoinvariants A S)
        (MonoidHom.id G) (toCoinvariantsMkQ A S)).comm₁₂.symm) W)) g
      simp only [shortComplexH1, mapShortComplexH1_τ₂, ModuleCat.ofHom_comp, MonoidHom.coe_id,
        lmapDomain_id, ModuleCat.ofHom_id, res_obj_ρ, hom_ofHom, Category.id_comp,
        mapShortComplexH1_τ₁, Prod.map_id, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
        LinearMap.coe_comp, Function.comp_apply, mapRange.linearMap_apply, mapRange_apply] at this
      simp only [← mapRange_apply (f := Coinvariants.mk <| A.ρ.comp S.subtype)
        (hf := map_zero _) (a := g), ← mapRange.linearMap_apply (R := k)]
      simp only [map_add, mapRange.linearMap_apply, coe_add, Pi.add_apply, mapRange_apply,
        Subgroup.coe_subtype, lmapDomain_apply, implies_true, ← mapDomain_mapRange, hZ]
      simp only [Representation.toCoinvariantsMkQ] at this
      change Representation.Coinvariants.mk _ _ = ((d₂₁ (A.toCoinvariants S)).hom
        (mapRange (Coinvariants.mk (MonoidHom.comp A.ρ S.subtype)) _ W)) g at this
      rw [this, hW, hzw]
      simp only [coe_mapCycles₁ S.subtype, ModuleCat.ofHom_comp, Subgroup.coe_subtype, res_obj_ρ,
        Rep.hom_id, IntertwiningMap.toLinearMap_id, mapRange.linearMap_id, ModuleCat.ofHom_id,
        Category.comp_id, ModuleCat.hom_ofHom, lmapDomain_apply, coe_mapCycles₁ (MonoidHom.id G),
        MonoidHom.coe_id, lmapDomain_id, hom_ofHom, Category.id_comp, mapRange.linearMap_apply,
        coe_sub, Pi.sub_apply, mapRange_apply]
      change _ + (_ - Coinvariants.mk _ _) = _
      rw [add_sub_cancel]
/- Let `β` be `b` considered as an element of `C₁(G, I(S)(A))`, so that `C₁(Id, i)(β) = b`. -/
  let β : G →₀ Coinvariants.ker (A.ρ.comp S.subtype) :=
    mapRange (Function.invFun <| (Coinvariants.ker (A.ρ.comp S.subtype)).subtype)
    (Function.leftInverse_invFun Subtype.val_injective (0 : Coinvariants.ker _)) b
  have hβb : mapRange Subtype.val rfl β = b := Finsupp.ext fun g => Subtype.ext_iff.1 <|
    Function.leftInverse_invFun Subtype.val_injective ⟨b g, hb g⟩
/- Then, since the image of `C₁(G, I(S)A)` in `C₁(G, A)⧸B₁(G, A)` is contained in the image of
`C₁(S, A)` by `comap_coinvariantsKer_pOpcycles_range_subtype_pOpcycles_eq_top`, we can choose
`α : C₁(S, A)`, `δ : C₂(G, A)` such that `d(δ) = Z₁(i, Id)(α) - Z₁(Id, i)(β)`. -/
  rcases eq_top_iff.1 (comap_coinvariantsKer_pOpcycles_range_subtype_pOpcycles_eq_top A S)
    (by trivial : β ∈ ⊤) with ⟨(α : S →₀ A), hα⟩
  dsimp only [ModuleCat.hom_comp] at hα
  rcases (moduleCat_pOpcycles_eq_iff _ _ _).1 hα with ⟨(δ : G × G →₀ A), hβ⟩
/- Then, by assumption, `d(W + δ) = C₁(i, Id)(α + Z) - x`. -/
  have hαZ : d₂₁ A (W + δ) = mapDomain Subtype.val (α + Z) - x := by
    simp_all [shortComplexH1, coinvariantsShortComplex_X₁,
      ← sub_add, ← sub_sub, sub_add_eq_add_sub, mapDomain_add, b]
/- So we claim that `α + Z` is an element of `Z₁(S, A)` which differs from `x` by a boundary in
`Z₁(G, A)`. -/
  use H1π _ ⟨α + Z, ?_⟩
/- Indeed, by `hαZ`, `d(W + δ)` is the desired boundary: -/
  · simp only [H1CoresCoinf_X₂, H1CoresCoinf_X₁, H1CoresCoinf_f, H1π_comp_map_apply]
    refine (H1π_eq_iff _ _).2 ⟨W + δ, ?_⟩
    simp [hαZ, mapCycles₁_hom]
/- And `α + Z` is a cycle, since `d(W + δ) + x` is. -/
  · rw [mem_cycles₁_iff]
    have : x + d₂₁ A (W + δ) ∈ cycles₁ A := Submodule.add_mem _ x.2 (d₂₁_apply_mem_cycles₁ _)
    rwa [eq_sub_iff_add_eq'.1 hαZ, mem_cycles₁_iff, sum_mapDomain_index_inj
      Subtype.val_injective, sum_mapDomain_index_inj Subtype.val_injective] at this

end CoresCoinf

end H1

section H2

set_option backward.isDefEq.respectTransparency false in
/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map from the short complex
`(G × G × G →₀ A) --d₃₂--> (G × G →₀ A) --d₂₁--> (G →₀ A)` to
`(H × H × H →₀ B) --d₃₂--> (H × H →₀ B) --d₂₁--> (H →₀ B)`. -/
@[simps]
noncomputable def mapShortComplexH2 :
    shortComplexH2 A ⟶ shortComplexH2 B where
  τ₁ := chainsMap₃ f φ
  τ₂ := chainsMap₂ f φ
  τ₃ := chainsMap₁ f φ
  comm₁₂ := by
    simp only [shortComplexH2]
    ext : 3
    simpa [d₃₂, map_add, map_sub, ← map_inv]
      using congr(Finsupp.single _ $((hom_comm_apply φ _ _).symm))
  comm₂₃ := by
    simp only [shortComplexH2]
    ext : 3
    simpa [d₂₁, map_add, map_sub, ← map_inv]
      using congr(Finsupp.single _ $((hom_comm_apply φ _ _).symm))

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem mapShortComplexH2_zero :
    mapShortComplexH2 (A := A) (B := B) f 0 = 0 := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  all_goals
  { simp only [shortComplexH2]
    ext
    simp }

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem mapShortComplexH2_id : mapShortComplexH2 (MonoidHom.id _) (𝟙 A) = 𝟙 _ := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  all_goals
  { simp only [shortComplexH2]
    ext
    simp }

set_option backward.isDefEq.respectTransparency false in
theorem mapShortComplexH2_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G →* H) (g : H →* K)
    (φ : A ⟶ res f B) (ψ : B ⟶ res g C) :
    mapShortComplexH2 (g.comp f) (φ ≫ (resFunctor f).map ψ) =
      (mapShortComplexH2 f φ) ≫ (mapShortComplexH2 g ψ) := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  all_goals
  { simp only [shortComplexH2]
    ext
    simp [Prod.map] }

theorem mapShortComplexH2_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapShortComplexH2 (MonoidHom.id G) (φ ≫ ψ) =
      mapShortComplexH2 (MonoidHom.id G) φ ≫ mapShortComplexH2 (MonoidHom.id G) ψ :=
  mapShortComplexH2_comp (MonoidHom.id G) (MonoidHom.id G) _ _

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map `Z₂(G, A) ⟶ Z₂(H, B)`. -/
noncomputable abbrev mapCycles₂ :
    ModuleCat.of k (cycles₂ A) ⟶ ModuleCat.of k (cycles₂ B) :=
  ShortComplex.cyclesMap' (mapShortComplexH2 f φ) (shortComplexH2 A).moduleCatLeftHomologyData
    (shortComplexH2 B).moduleCatLeftHomologyData

set_option backward.isDefEq.respectTransparency false in
lemma mapCycles₂_hom :
    (mapCycles₂ f φ).hom = (chainsMap₂ f φ).hom.restrict (fun x _ => by
      have := congr($((mapShortComplexH2 f φ).comm₂₃) x); simp_all [cycles₂, shortComplexH2]) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc, elementwise]
lemma mapCycles₂_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G →* H) (g : H →* K)
    (φ : A ⟶ res f B) (ψ : B ⟶ res g C) :
    mapCycles₂ (g.comp f) (φ ≫ (resFunctor f).map ψ) =
      mapCycles₂ f φ ≫ mapCycles₂ g ψ := by
  rw [← cyclesMap'_comp, ← mapShortComplexH2_comp]

@[reassoc, elementwise]
theorem mapCycles₂_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapCycles₂ (MonoidHom.id G) (φ ≫ ψ) =
      mapCycles₂ (MonoidHom.id G) φ ≫ mapCycles₂ (MonoidHom.id G) ψ :=
  mapCycles₂_comp (MonoidHom.id G) (MonoidHom.id G) _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc, elementwise]
lemma mapCycles₂_comp_i :
    mapCycles₂ f φ ≫ (shortComplexH2 B).moduleCatLeftHomologyData.i =
      (shortComplexH2 A).moduleCatLeftHomologyData.i ≫ chainsMap₂ f φ := by
  simp

@[simp]
lemma coe_mapCycles₂ (x) :
    (mapCycles₂ f φ x).1 = chainsMap₂ f φ x := rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma cyclesMap_comp_isoCycles₂_hom :
    cyclesMap f φ 2 ≫ (isoCycles₂ B).hom = (isoCycles₂ A).hom ≫ mapCycles₂ f φ := by
  simp [← cancel_mono (moduleCatLeftHomologyData (shortComplexH2 B)).i, mapShortComplexH2,
    chainsMap_f_2_comp_chainsIso₂ f]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma H2π_comp_map :
    H2π A ≫ map f φ 2 = mapCycles₂ f φ ≫ H2π B := by
  simp [H2π, Iso.inv_comp_eq, ← cyclesMap_comp_isoCycles₂_hom_assoc]

end H2

variable (k G)

/-- The functor sending a representation to its complex of inhomogeneous chains. -/
@[simps]
noncomputable def chainsFunctor :
    Rep k G ⥤ ChainComplex (ModuleCat k) ℕ where
  obj A := inhomogeneousChains A
  map f := chainsMap (MonoidHom.id _) f
  map_id _ := chainsMap_id
  map_comp φ ψ := chainsMap_comp (MonoidHom.id G) (MonoidHom.id G) φ ψ

instance : (chainsFunctor k G).PreservesZeroMorphisms where

set_option backward.isDefEq.respectTransparency false in
/-- The functor sending a `G`-representation `A` to `Hₙ(G, A)`. -/
@[simps]
noncomputable def functor (n : ℕ) : Rep k G ⥤ ModuleCat k where
  obj A := groupHomology A n
  map {A B} φ := map (MonoidHom.id _) φ n
  map_id A := by simp [map, groupHomology]
  map_comp f g := by
    simp only [← HomologicalComplex.homologyMap_comp, ← chainsMap_comp]
    rfl

set_option backward.isDefEq.respectTransparency false in
instance (n : ℕ) : (functor k G n).PreservesZeroMorphisms where
  map_zero _ _ := by simp [map]

variable {G}

set_option backward.isDefEq.respectTransparency false in
/-- Given a group homomorphism `f : G →* H` this sends `A : Rep k H` to the `n`th
"corestriction" map `Hₙ(G, Res(f)(A)) ⟶ Hₙ(H, A)` induced by `f` and the identity
map on `Res(f)(A)`. -/
@[simps]
noncomputable def coresNatTrans (n : ℕ) :
    resFunctor f ⋙ functor k G n ⟶ functor k H n where
  app X := map f (𝟙 _) n
  naturality {X Y} φ := by
    simp only [← cancel_epi (groupHomology.π _ n), functor_obj, Functor.comp_obj, Functor.comp_map,
      functor_map, HomologicalComplex.homologyπ_naturality_assoc,
      HomologicalComplex.homologyπ_naturality, ← HomologicalComplex.cyclesMap_comp_assoc,
      ← chainsMap_comp, res_obj_ρ, Rep.hom_id, Category.id_comp]
    rfl



set_option backward.isDefEq.respectTransparency false in
/-- Given a normal subgroup `S ≤ G`, this sends `A : Rep k G` to the `n`th "coinflation" map
`Hₙ(G, A) ⟶ Hₙ(G ⧸ S, A_S)` induced by the quotient maps `G →* G ⧸ S` and `A →ₗ A_S`. -/
@[simps]
noncomputable def coinfNatTrans (S : Subgroup G) [S.Normal] (n : ℕ) :
    functor k G n ⟶ quotientToCoinvariantsFunctor k S ⋙ functor k (G ⧸ S) n where
  app A := map (QuotientGroup.mk' S) (Rep.toCoinvariantsMkQ _ _) n
  naturality {X Y} φ := by
    simp only [Functor.comp_map, functor_map, ← cancel_epi (groupHomology.π _ n),
      HomologicalComplex.homologyπ_naturality_assoc, HomologicalComplex.homologyπ_naturality,
      ← HomologicalComplex.cyclesMap_comp_assoc, ← chainsMap_comp]
    congr 1

end groupHomology
