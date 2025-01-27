/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

/-! -/

universe u

namespace groupHomology

open CategoryTheory ShortComplex

variable {k G : Type u} [CommRing k] [Group G] {X : ShortComplex (Rep k G)} (hX : ShortExact X)

include hX

lemma chainsMap_shortExact :
    ShortExact ((chainsFunctor k G).mapShortComplex.obj X) :=
  letI := hX.2
  letI := hX.3
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => {
    exact := by
      rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
      have : LinearMap.range X.f.hom.hom = LinearMap.ker X.g.hom.hom :=
        (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
      show LinearMap.range ((chainsMap (MonoidHom.id G) X.f).f i).hom =
        LinearMap.ker ((chainsMap (MonoidHom.id G) X.g).f i).hom
      rw [chainsMap_id_eq_mapRange, chainsMap_id_eq_mapRange, ker_mapRange,
        range_mapRange_linearMap, this]
      exact LinearMap.ker_eq_bot.2 ((ModuleCat.mono_iff_injective _).1 <|
        (forget₂ (Rep k G) (ModuleCat k)).map_mono X.f)
    mono_f := chainsMap_id_f_map_mono X.f i
    epi_g := chainsMap_id_f_map_epi X.g i }

/-- The short complex  `Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁) ⟶ Hⱼ(G, X₂)` associated to an exact sequence
of representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev mapShortComplex₁ {i j : ℕ} (hij : j + 1 = i) :=
  ShortComplex.mk _ _ ((chainsMap_shortExact hX).δ_comp i j hij)

variable (X) in
/-- The short complex `Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃)` associated to a short complex of
representations `X₁ ⟶ X₂ ⟶ X₃`. -/
noncomputable abbrev mapShortComplex₂ (i : ℕ) :=
  ShortComplex.mk (map (MonoidHom.id G) X.f i) (map (MonoidHom.id G) X.g i) <| by
    simp [← map_id_comp, X.zero, map]

/-- The short complex `Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)` associated to an exact sequence of
representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev mapShortComplex₃ {i j : ℕ} (hij : j + 1 = i) :=
  ShortComplex.mk _ _ ((chainsMap_shortExact hX).comp_δ i j hij)

/-- Exactness of `Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁) ⟶ Hⱼ(G, X₂)`. -/
lemma mapShortComplex₁_exact {i j : ℕ} (hij : j + 1 = i) :
    (mapShortComplex₁ hX hij).Exact :=
  (chainsMap_shortExact hX).homology_exact₁ i j hij

/-- Exactness of `Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃)`. -/
lemma mapShortComplex₂_exact (i : ℕ) :
    (mapShortComplex₂ X i).Exact :=
  (chainsMap_shortExact hX).homology_exact₂ i

/--  Exactness of `Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)`. -/
lemma mapShortComplex₃_exact {i j : ℕ} (hij : j + 1 = i) :
    (mapShortComplex₃ hX hij).Exact :=
  (chainsMap_shortExact hX).homology_exact₃ i j hij

theorem δ_apply (i j l : ℕ) (hij : j + 1 = i) (hjl : (ComplexShape.down ℕ).next j = l)
    (z : (Fin i → G) →₀ X.X₃) (hz : (inhomogeneousChains X.X₃).d i j z = 0)
    (y : (Fin i → G) →₀ X.X₂) (hy : (chainsMap (MonoidHom.id G) X.g).f i y = z)
    (x : (Fin j → G) →₀ X.X₁)
    (hx : Finsupp.mapRange.linearMap X.f.hom.hom x = (inhomogeneousChains X.X₂).d i j y) :
    (chainsMap_shortExact hX).δ i j hij (groupHomologyπ X.X₃ i <|
      (moduleCatCyclesIso _).inv ⟨z, show ((inhomogeneousChains X.X₃).dFrom i).hom z = 0 by
        simp_all [(inhomogeneousChains X.X₃).dFrom_eq hij]⟩) = groupHomologyπ X.X₁ j
      ((moduleCatCyclesIso _).inv ⟨x, (chainsMap_shortExact hX).δ_apply_aux i j y x
        (by simpa [chainsMap_id_eq_mapRange] using hx) _⟩) := by
  convert (chainsMap_shortExact hX).δ_apply i j hij z
    hz y hy x (by simpa [chainsMap_id_eq_mapRange] using hx) l hjl
  <;> rw [moduleCatCyclesIso_inv_apply]
  <;> rfl

/-- The degree 0 connecting homomorphism `H₁(G, X₃) ⟶ X₁_G` associated to an exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations. Uses a simpler expression for `H₀` and `H₁` than
general `δ`. -/
noncomputable def δ₀ :
    ModuleCat.of k (H1 X.X₃) ⟶ ModuleCat.of k (H0 X.X₁) :=
  (isoH1 X.X₃).inv ≫ (chainsMap_shortExact hX).δ 1 0 rfl ≫ (isoH0 X.X₁).hom

theorem δ₀_apply (z : G →₀ X.X₃) (hz : dZero X.X₃ z = 0) (y : G →₀ X.X₂)
    (hy : mapRange.linearMap X.g.hom.hom y = z) (x : X.X₁) (hx : X.f.hom x = dZero X.X₂ y) :
    δ₀ hX (H1π X.X₃ ⟨z, hz⟩) = H0π X.X₁ x := by
  have hxy : mapRange.linearMap X.f.hom.hom ((zeroChainsLequiv X.X₁).symm x) =
      (inhomogeneousChains X.X₂).d 1 0 ((oneChainsLequiv X.X₂).symm y) := by
    have := congr($((CommSq.horiz_inv ⟨dZero_comp_eq X.X₂⟩).w) y)
    simp_all [← hx, zeroChainsLequiv, single_eq_same]
  have δ_1_0 := congr((isoH0 X.X₁).hom $((chainsMap_shortExact hX).δ_apply 1 0 rfl
    ((oneChainsLequiv X.X₃).symm z)
    (by simpa [hz] using congr($((CommSq.horiz_inv ⟨dZero_comp_eq X.X₃⟩).w) z))
    ((oneChainsLequiv X.X₂).symm y) (Finsupp.ext fun _ => by simp [← hy, oneChainsLequiv])
    ((zeroChainsLequiv X.X₁).symm x) (by simpa using hxy) 0 (by simp)))
  · convert δ_1_0
    · show (H1π X.X₃ ≫ δ₀ hX) ⟨z, hz⟩ = _
      simp [δ₀, ← Category.assoc, (CommSq.vert_inv ⟨groupHomologyπ_comp_isoH1_hom X.X₃⟩).w,
        isoOneCycles_inv_apply_eq_cyclesMk X.X₃ ⟨z, hz⟩]
    · simp [(Iso.eq_inv_comp _).2 (π_comp_isoH0_hom X.X₁).symm, -π_comp_isoH0_hom,
        isoZeroCycles_inv_apply_eq_cyclesMk X.X₁ x]

open Limits

theorem epi_δ₀_of_isZero (h0 : IsZero (ModuleCat.of k <| H0 X.X₂)) : Epi (δ₀ hX) := by
  letI : Epi ((chainsMap_shortExact hX).δ 1 0 rfl) := (chainsMap_shortExact hX).epi_δ _ _ rfl
    (h0.of_iso (isoH0 X.X₂))
  exact epi_comp _ _

/-- The degree 1 connecting homomorphism `H₂(G, X₃) ⟶ H₁(G, X₁)` associated to an exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations. Uses a simpler expression for `H₁` and `H₂` than
general `δ`. -/
noncomputable def δ₁ :
    ModuleCat.of k (H2 X.X₃) ⟶ ModuleCat.of k (H1 X.X₁) :=
  (isoH2 X.X₃).inv ≫ (chainsMap_shortExact hX).δ 2 1 rfl ≫ (isoH1 X.X₁).hom

theorem δ₁_apply_aux (y : G × G →₀ X.X₂) (x : G →₀ X.X₁)
    (hx : mapRange.linearMap X.f.hom.hom x = dOne X.X₂ y) :
    dZero X.X₁ x = 0 := by
  have h1 :=  (chainsMap_shortExact hX).δ_apply_aux 2 1 ((twoChainsLequiv X.X₂).symm y)
    ((oneChainsLequiv X.X₁).symm x)
  have h2 := congr($((CommSq.horiz_inv ⟨(shortComplexH1Iso X.X₂).hom.comm₁₂⟩).w) y)
  have h3 := congr($((Iso.eq_inv_comp _).2 (shortComplexH1Iso X.X₁).hom.comm₂₃) x)
  have h4 := congr($((CommSq.vert_inv (h := (oneChainsLequiv X.X₂).toModuleIso)
    ⟨(chainsMap_f_1_comp_oneChainsLequiv (MonoidHom.id G) X.f)⟩).w) x)
  simp_all [shortComplexH1, fOne, MonoidHom.coe_id]

theorem δ₁_apply (z : G × G →₀ X.X₃) (hz : dOne X.X₃ z = 0) (y : G × G →₀ X.X₂)
    (hy : mapRange.linearMap X.g.hom.hom y = z) (x : G →₀ X.X₁)
    (hx : mapRange.linearMap X.f.hom.hom x = dOne X.X₂ y) :
    δ₁ hX (H2π X.X₃ ⟨z, hz⟩) = H1π X.X₁ ⟨x, δ₁_apply_aux hX y x hx⟩ := by
  have hxy : Finsupp.mapRange.linearMap X.f.hom.hom ((oneChainsLequiv X.X₁).symm x) =
        (inhomogeneousChains X.X₂).d 2 1 ((twoChainsLequiv X.X₂).symm y) :=
    have := congr($((CommSq.horiz_inv ⟨dOne_comp_eq X.X₂⟩).w) y)
    Finsupp.ext fun _ => by simp_all [← hx, oneChainsLequiv]
  have δ_2_1 := congr((isoH1 X.X₁).hom $(δ_succ_apply hX _ _ 0 rfl (by simp)
    ((twoChainsLequiv X.X₃).symm z)
    (by simpa [hz] using congr($((CommSq.horiz_inv ⟨dOne_comp_eq X.X₃⟩).w) z))
    ((twoChainsLequiv X.X₂).symm y) (Finsupp.ext fun _ => by simp [← hy, twoChainsLequiv])
    ((oneChainsLequiv X.X₁).symm x) hxy))
  · convert δ_2_1
    · show (H2π X.X₃ ≫ δ₁ hX) ⟨z, hz⟩ = _
      rw [moduleCatCyclesIso_inv_apply]
      simp [δ₁, ← Category.assoc, (CommSq.vert_inv ⟨groupHomologyπ_comp_isoH2_hom X.X₃⟩).w,
        isoTwoCycles_inv_apply_eq_cyclesMk X.X₃ ⟨z, hz⟩, HomologicalComplex.cyclesMk]
    · rw [moduleCatCyclesIso_inv_apply]
      simp [(Iso.eq_inv_comp _).2 (groupHomologyπ_comp_isoH1_hom X.X₁).symm,
        -groupHomologyπ_comp_isoH1_hom, isoOneCycles_inv_apply_eq_cyclesMk X.X₁ ⟨x, _⟩,
        HomologicalComplex.cyclesMk]

theorem epi_δ₁_of_isZero (h1 : IsZero (ModuleCat.of k <| H1 X.X₂)) :
    Epi (δ₁ hX) := by
  letI : Epi ((chainsMap_shortExact hX).δ 2 1 rfl) := (chainsMap_shortExact hX).epi_δ _ _ rfl
    (h1.of_iso (isoH1 X.X₂))
  exact epi_comp _ _

variable (X) in
/-- The short complex `X₁_G ⟶ X₂_G ⟶ X₃_G` associated to a short complex of representations
`X₁ ⟶ X₂ ⟶ X₃`. -/
noncomputable abbrev H0ShortComplex₂ :=
  ShortComplex.mk (H0Map (MonoidHom.id G) X.f) (H0Map (MonoidHom.id G) X.g) <|
    ModuleCat.hom_ext <| Submodule.linearMap_qext _ <| by
      ext x
      have := congr(Action.Hom.hom $(X.zero) x)
      simp_all [-ShortComplex.zero, H0Map, LinearMap.zero_apply (M₂ := X.X₃) x]

variable (X) in
/-- When `i = 0`, the general short complex `Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃)` associated to a
short complex of representations agrees with our simpler expression of `X₁_G ⟶ X₂_G ⟶ X₃_G.` -/
noncomputable def isoH0ShortComplex₂ :
    mapShortComplex₂ X 0 ≅ H0ShortComplex₂ X :=
  isoMk (isoH0 _) (isoH0 _) (isoH0 _) (map_comp_isoH0_hom (MonoidHom.id G) X.f).symm
    (map_comp_isoH0_hom (MonoidHom.id G) X.g).symm

theorem H0ShortComplex₂_exact :
    (H0ShortComplex₂ X).Exact :=
  exact_of_iso (isoH0ShortComplex₂ X) (mapShortComplex₂_exact hX _)

/-- The short complex `H₁(G, X₃) ⟶ X₁_G ⟶ X₂_G` associated to an exact sequence of
representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev H0ShortComplex₁ :=
  ShortComplex.mk (δ₀ hX) (H0Map (MonoidHom.id G) X.f) <| by
    simpa [δ₀, ← map_comp_isoH0_hom] using (chainsMap_shortExact hX).δ_comp_assoc 1 0 rfl _

/-- When `i = 0`, the general short complex `Hᵢ₊₁(G, X₃) ⟶ Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂)` associated to a
short exact sequence of representations agrees with our simpler expression for
`H₁(G, X₃) ⟶ X₁_G ⟶ X₂_G.` -/
noncomputable def isoH0ShortComplex₁ :
    mapShortComplex₁ hX (i := 1) rfl ≅ H0ShortComplex₁ hX :=
  isoMk (isoH1 _) (isoH0 _) (isoH0 _) (by simp [δ₀])
    (map_comp_isoH0_hom (MonoidHom.id G) _).symm

theorem H0ShortComplex₁_exact :
    (H0ShortComplex₁ hX).Exact :=
  exact_of_iso (isoH0ShortComplex₁ hX) (mapShortComplex₁_exact _ _)

/-- The short complex  `H₁(G, X₂) ⟶ H₁(G, X₃) ⟶ X₁_G` associated to an exact sequence of
representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev H1ShortComplex₃ :=
  ShortComplex.mk (H1Map (MonoidHom.id G) X.g) (δ₀ hX) <| by
    have := (CommSq.vert_inv ⟨map_comp_isoH1_hom (MonoidHom.id G) X.g⟩).w
    have h := (chainsMap_shortExact hX).comp_δ 1 0 rfl
    simp_all only [δ₀, ← Category.assoc, Preadditive.IsIso.comp_right_eq_zero]
    simp_all

/-- When `i = 0`, the general short complex `Hᵢ₊₁(G, X₂) ⟶ Hᵢ₊₁(G, X₃) ⟶ Hᵢ(G, X₁)` associated to
a short exact sequence of representations agrees with our simpler expression for
`H₁(G, X₂) ⟶ H₁(G, X₃) ⟶ X₁_G.` -/
noncomputable def isoH1ShortComplex₃ :
    mapShortComplex₃ hX (j := 0) rfl ≅ H1ShortComplex₃ hX :=
  isoMk (isoH1 _) (isoH1 _) (isoH0 _)
    (map_comp_isoH1_hom (MonoidHom.id G) _).symm (by simp [δ₀])

theorem H1ShortComplex₃_exact :
    (H1ShortComplex₃ hX).Exact :=
  exact_of_iso (isoH1ShortComplex₃ hX) (mapShortComplex₃_exact _ _)

variable (X) in
/-- The short complex `H₁(G, X₁) ⟶ H₁(G, X₂) ⟶ H₁(G, X₃)` associated to a short complex of
representations `X₁ ⟶ X₂ ⟶ X₃`. -/
noncomputable abbrev H1ShortComplex₂ :=
  ShortComplex.mk (H1Map (MonoidHom.id G) X.f) (H1Map (MonoidHom.id G) X.g) <| by
    simp [← H1Map_id_comp, X.zero, H1Map]

variable (X) in
/-- When `i = 1`, the general short complex `Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃)` associated to
a short complex of representations agrees with our simpler expression for
`H₁(G, X₁) ⟶ H₁(G, X₂) ⟶ H₁(G, X₃).` -/
noncomputable def isoH1ShortComplex₂ :
    mapShortComplex₂ X 1 ≅ H1ShortComplex₂ X :=
  isoMk (isoH1 _) (isoH1 _) (isoH1 _) (map_comp_isoH1_hom _ _).symm
    (map_comp_isoH1_hom _ _).symm

theorem H1ShortComplex₂_exact :
    (H1ShortComplex₂ X).Exact :=
  exact_of_iso (isoH1ShortComplex₂ X) (mapShortComplex₂_exact hX _)

/-- The short complex `H₂(G, X₃) ⟶ H₁(G, X₁) ⟶ H₁(G, X₂)` associated to an exact sequence of
representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev H1ShortComplex₁ :=
  ShortComplex.mk (δ₁ hX) (H1Map (MonoidHom.id G) X.f) <| by
    simpa [δ₁, ← map_comp_isoH1_hom] using (chainsMap_shortExact hX).δ_comp_assoc 2 1 rfl _

/-- When `i = 1`, the general short complex `Hᵢ₊₁(G, X₃) ⟶ Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂)` associated to a
short exact sequence of representations agrees with our simpler expression for
`H₂(G, X₃) ⟶ H₁(G, X₁) ⟶ H₁(G, X₂).` -/
noncomputable def isoH1ShortComplex₁ :
    mapShortComplex₁ hX (i := 2) rfl ≅ H1ShortComplex₁ hX :=
  isoMk (isoH2 _) (isoH1 _) (isoH1 _) (by simp [δ₁])
    (map_comp_isoH1_hom (MonoidHom.id G) _).symm

theorem H1ShortComplex₁_exact :
    (H1ShortComplex₁ hX).Exact :=
  exact_of_iso (isoH1ShortComplex₁ hX) (mapShortComplex₁_exact _ _)

/-- The short complex  `H₂(G, X₂) ⟶ H₂(G, X₃) ⟶ H₁(G, X₁)` associated to an exact sequence of
representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev H2ShortComplex₃ :=
  ShortComplex.mk (H2Map (MonoidHom.id G) X.g) (δ₁ hX) <| by
    have := (CommSq.vert_inv ⟨map_comp_isoH2_hom (MonoidHom.id G) X.g⟩).w
    have h := (chainsMap_shortExact hX).comp_δ 2 1 rfl
    simp_all only [δ₁, ← Category.assoc, Preadditive.IsIso.comp_right_eq_zero]
    simp_all

/-- When `i = 1`, the general short complex `Hᵢ₊₁(G, X₂) ⟶ Hᵢ₊₁(G, X₃) ⟶ Hᵢ(G, X₁)` associated to
a short exact sequence of representations agrees with our simpler expression for
`H₂(G, X₂) ⟶ H₂(G, X₃) ⟶ H₁(G, X₁).` -/
noncomputable def isoH2ShortComplex₃ :
    mapShortComplex₃ hX (j := 1) rfl ≅ H2ShortComplex₃ hX :=
  isoMk (isoH2 _) (isoH2 _) (isoH1 _) (map_comp_isoH2_hom _ _).symm (by simp [δ₁])

theorem H2ShortComplex₃_exact :
    (H2ShortComplex₃ hX).Exact :=
  exact_of_iso (isoH2ShortComplex₃ hX) (mapShortComplex₃_exact _ _)

end groupHomology
