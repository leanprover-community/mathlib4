/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RepresentationTheory.GroupCohomology.Functoriality

/-!
# Long exact sequence in group cohomology

Given a commutative ring `k` and a group `G`, this file shows that a short exact sequence of
`k`-linear `G`-representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` induces a short exact sequence of
complexes of inhomogeneous cochains `0 ⟶ C(X₁) ⟶ C(X₂) ⟶ C(X₃) ⟶ 0`, where `Hⁿ(C(Xᵢ))`
is the `n`th group cohomology of `Xᵢ`.

This allows us to specialize API about long exact sequences to group cohomology.

## Main definitions

* `groupCohomology.δ hX i j hij`: the connecting homomorphism `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)` associated
  to an exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations.
-/

universe u

namespace groupCohomology

open CategoryTheory ShortComplex

variable {k G : Type u} [CommRing k] [Group G] {X : ShortComplex (Rep k G)} (hX : ShortExact X)

include hX

lemma map_cochainsFunctor_shortExact :
    ShortExact (X.map (cochainsFunctor k G)) :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => {
    exact := by
      have : LinearMap.range X.f.hom.hom = LinearMap.ker X.g.hom.hom :=
        (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
      simp_all [moduleCat_exact_iff_range_eq_ker, LinearMap.range_compLeft, LinearMap.ker_compLeft]
    mono_f := letI := hX.2; cochainsMap_id_f_map_mono X.f i
    epi_g := letI := hX.3; cochainsMap_id_f_map_epi X.g i }

/-- The short complex `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁) ⟶ Hʲ(G, X₂)` associated to an exact
sequence of representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev mapShortComplex₁ {i j : ℕ} (hij : i + 1 = j) :=
  ShortComplex.mk _ _ ((map_cochainsFunctor_shortExact hX).δ_comp i j hij)

variable (X) in
/-- The short complex `Hⁱ(G, X₁) ⟶ Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃)` associated to a short complex of
representations `X₁ ⟶ X₂ ⟶ X₃`. -/
noncomputable abbrev mapShortComplex₂ (i : ℕ) :=
  ShortComplex.mk (map (MonoidHom.id G) X.f i)
    (map (MonoidHom.id G) X.g i) <| by simp [← map_id_comp, X.zero, map]

/-- The short complex `Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)`. -/
noncomputable abbrev mapShortComplex₃ {i j : ℕ} (hij : i + 1 = j) :=
  ShortComplex.mk _ _ ((map_cochainsFunctor_shortExact hX).comp_δ i j hij)

/-- Exactness of `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁) ⟶ Hʲ(G, X₂)`. -/
lemma mapShortComplex₁_exact {i j : ℕ} (hij : i + 1 = j) :
    (mapShortComplex₁ hX hij).Exact :=
  (map_cochainsFunctor_shortExact hX).homology_exact₁ i j hij

/-- Exactness of `Hⁱ(G, X₁) ⟶ Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃)`. -/
lemma mapShortComplex₂_exact (i : ℕ) :
    (mapShortComplex₂ X i).Exact :=
  (map_cochainsFunctor_shortExact hX).homology_exact₂ i

/--  Exactness of `Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)`. -/
lemma mapShortComplex₃_exact {i j : ℕ} (hij : i + 1 = j) :
    (mapShortComplex₃ hX hij).Exact :=
  (map_cochainsFunctor_shortExact hX).homology_exact₃ i j hij

/-- The connecting homomorphism `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)` associated to an exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations. -/
noncomputable abbrev δ (i j : ℕ) (hij : i + 1 = j) :
    groupCohomology X.X₃ i ⟶ groupCohomology X.X₁ j :=
  (map_cochainsFunctor_shortExact hX).δ i j hij

theorem δ_apply (i j : ℕ) (hij : i + 1 = j)
    (z : (Fin i → G) → X.X₃) (hz : (inhomogeneousCochains X.X₃).d i j z = 0)
    (y : (Fin i → G) → X.X₂) (hy : (cochainsMap (MonoidHom.id G) X.g).f i y = z)
    (x : (Fin j → G) → X.X₁) (hx : X.f.hom ∘ x = (inhomogeneousCochains X.X₂).d i j y) :
    δ hX i j hij (groupCohomologyπ X.X₃ i <| (moduleCatCyclesIso _).inv
      ⟨z, show ((inhomogeneousCochains X.X₃).dFrom i).hom z = 0 by
        simp_all [(inhomogeneousCochains X.X₃).dFrom_eq hij]⟩) =
      groupCohomologyπ X.X₁ j ((moduleCatCyclesIso _).inv
        ⟨x, by convert ((map_cochainsFunctor_shortExact hX).d_eq_zero_of_f_eq_d_apply i j y x
          (by simpa [cochainsMap_id_f_eq_compLeft] using hx) <| (ComplexShape.up ℕ).next j)⟩) := by
  convert (map_cochainsFunctor_shortExact hX).δ_apply i j hij z
    hz y hy x (by simpa [cochainsMap_id_f_eq_compLeft] using hx) ((ComplexShape.up ℕ).next j) rfl
  <;> rw [moduleCatCyclesIso_inv_apply]
  <;> rfl

/-- The degree 0 connecting homomorphism `X₃ᴳ ⟶ H¹(G, X₁)` associated to an exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations. Uses a simpler expression for `H⁰` and `H¹` than
general `δ`. -/
noncomputable def δ₀ : H0 X.X₃ ⟶ H1 X.X₁ :=
  (isoH0 X.X₃).inv ≫ (map_cochainsFunctor_shortExact hX).δ 0 1 rfl ≫ (isoH1 X.X₁).hom

theorem δ₀_apply_aux (y : X.X₂) (x : G → X.X₁) (hx : X.f.hom ∘ x = dZero X.X₂ y) :
    dOne X.X₁ x = 0 := by
  have hδ := (map_cochainsFunctor_shortExact hX).δ_apply_aux 0 1 ((zeroCochainsLequiv X.X₂).symm y)
    ((oneCochainsLequiv X.X₁).symm x)
  have hy := congr($((CommSq.horiz_inv ⟨(shortComplexH1Iso X.X₂).hom.comm₁₂⟩).w) y)
  have h := congr($((Iso.eq_inv_comp _).2 (shortComplexH1Iso X.X₁).hom.comm₂₃) x)
  have h0 := congr($((CommSq.vert_inv
    ⟨(cochainsMap_f_1_comp_oneCochainsLequiv (MonoidHom.id G) X.f)⟩).w) x)
  simp_all [LinearMap.compLeft, shortComplexH1, MonoidHom.coe_id, ← hx,
    -inhomogeneousCochains.d_def]

theorem δ₀_apply (z : X.X₃) (hz : z ∈ X.X₃.ρ.invariants) (y : X.X₂) (hy : X.g.hom y = z)
    (x : G → X.X₁) (hx : X.f.hom ∘ x = dZero X.X₂ y) :
    δ₀ hX ⟨z, hz⟩ = H1π X.X₁ ⟨x, δ₀_apply_aux hX y x hx⟩ := by
  have h0z : ((inhomogeneousCochains X.X₃).d 0 1) ((zeroCochainsLequiv X.X₃).symm z) = 0 := by
    have := congr($((CommSq.horiz_inv ⟨dZero_comp_eq X.X₃⟩).w) z)
    simp_all [← dZero_ker_eq_invariants]
  have hxy : X.f.hom ∘ (oneCochainsLequiv X.X₁).symm x = (inhomogeneousCochains X.X₂).d 0 1
      ((zeroCochainsLequiv X.X₂).symm y) := by
    have := congr($((CommSq.horiz_inv ⟨dZero_comp_eq X.X₂⟩).w) y)
    ext i
    simp_all [← hx, oneCochainsLequiv, -inhomogeneousCochains.d_def]
  have δ_0_1 := congr((isoH1 X.X₁).hom
    $(δ_apply hX 0 1 rfl ((zeroCochainsLequiv X.X₃).symm z) h0z
    ((zeroCochainsLequiv X.X₂).symm y) (hy ▸ rfl) ((oneCochainsLequiv X.X₁).symm x) hxy))
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

theorem epi_δ₀_of_isZero (h1 : IsZero (H1 X.X₂)) :
    Epi (δ₀ hX) := by
  letI : Epi ((map_cochainsFunctor_shortExact hX).δ 0 1 rfl) :=
    (map_cochainsFunctor_shortExact hX).epi_δ _ _ rfl (h1.of_iso (isoH1 X.X₂))
  exact epi_comp _ _

/-- The degree 1 connecting homomorphism `H¹(G, X₃) ⟶ H²(G, X₁)` associated to an exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations. Uses a simpler expression for `H¹` and `H²` than
general `δ`. -/
noncomputable def δ₁ : H1 X.X₃ ⟶ H2 X.X₁ :=
  (isoH1 X.X₃).inv ≫ (map_cochainsFunctor_shortExact hX).δ 1 2 rfl ≫ (isoH2 X.X₁).hom

theorem δ₁_apply_aux (y : G → X.X₂) (x : G × G → X.X₁) (hx : X.f.hom ∘ x = dOne X.X₂ y) :
    dTwo X.X₁ x = 0 := by
  have hδ := (map_cochainsFunctor_shortExact hX).δ_apply_aux 1 2 ((oneCochainsLequiv X.X₂).symm y)
    ((twoCochainsLequiv X.X₁).symm x)
  have hy := congr($((CommSq.horiz_inv ⟨(shortComplexH2Iso X.X₂).hom.comm₁₂⟩).w) y)
  have h := congr($((Iso.eq_inv_comp _).2 (shortComplexH2Iso X.X₁).hom.comm₂₃) x)
  have h2 := congr($((CommSq.vert_inv
    ⟨(cochainsMap_f_2_comp_twoCochainsLequiv (MonoidHom.id G) X.f)⟩).w) x)
  simp_all [LinearMap.compLeft, shortComplexH2, MonoidHom.coe_id, ← hx,
    -inhomogeneousCochains.d_def]

theorem δ₁_apply (z : G → X.X₃) (hz : z ∈ oneCocycles X.X₃) (y : G → X.X₂) (hy : X.g.hom ∘ y = z)
    (x : G × G → X.X₁) (hx : X.f.hom ∘ x = dOne X.X₂ y) :
    δ₁ hX (H1π X.X₃ ⟨z, hz⟩) = H2π X.X₁ ⟨x, δ₁_apply_aux hX y x hx⟩ := by
  have h1z : ((inhomogeneousCochains X.X₃).d 1 2) ((oneCochainsLequiv X.X₃).symm z) = 0 := by
    have := congr($((CommSq.horiz_inv ⟨dOne_comp_eq X.X₃⟩).w) z)
    simp_all [oneCocycles]
  have hxy : X.f.hom ∘ (twoCochainsLequiv X.X₁).symm x =
      (inhomogeneousCochains X.X₂).d 1 2 ((oneCochainsLequiv X.X₂).symm y) := by
    have := congr($((CommSq.horiz_inv ⟨dOne_comp_eq X.X₂⟩).w) y)
    ext i
    simp_all [← hx, twoCochainsLequiv, -inhomogeneousCochains.d_def]
  have δ_1_2 := congr((isoH2 X.X₁).hom
    $(δ_apply hX 1 2 rfl ((oneCochainsLequiv X.X₃).symm z) h1z
    ((oneCochainsLequiv X.X₂).symm y) (hy ▸ rfl) ((twoCochainsLequiv X.X₁).symm x) hxy))
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

theorem epi_δ₁_of_isZero (h2 : IsZero (H2 X.X₂)) :
    Epi (δ₁ hX) := by
  letI : Epi ((map_cochainsFunctor_shortExact hX).δ 1 2 rfl) :=
    (map_cochainsFunctor_shortExact hX).epi_δ _ _ rfl (h2.of_iso (isoH2 X.X₂))
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
    rw [δ₀, ← Category.assoc, (CommSq.vert_inv ⟨map_comp_isoH0_hom (MonoidHom.id G) X.g⟩).w]
    simpa using (map_cochainsFunctor_shortExact H).comp_δ_assoc 0 1 rfl _

/-- When `i = 0`, the general short complex `Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃) ⟶ Hⁱ⁺¹(G, X₁)` associated to a
short exact sequence of representations agrees with our simpler expression for
`X₂ᴳ ⟶ X₃ᴳ ⟶ H¹(G, X₁).` -/
noncomputable def isoH0ShortComplex₃ (H : ShortExact X) :
    mapShortComplex₃ H (j := 1) rfl ≅ H0ShortComplex₃ H :=
  isoMk (isoH0 _) (isoH0 _) (isoH1 _) (map_comp_isoH0_hom (MonoidHom.id G) _).symm (by simp [δ₀])

theorem H0ShortComplex₃_exact :
    (H0ShortComplex₃ hX).Exact :=
  exact_of_iso (isoH0ShortComplex₃ hX) (mapShortComplex₃_exact hX _)

/-- The short complex  `X₃ᴳ ⟶ H¹(G, X₁) ⟶ H¹(G, X₂)` associated to a short exact sequence of
representations. -/
noncomputable abbrev H1ShortComplex₁ :=
  ShortComplex.mk (δ₀ hX) (H1Map (MonoidHom.id G) X.f) <| by
    simpa [δ₀, ← map_comp_isoH1_hom]
      using (map_cochainsFunctor_shortExact hX).δ_comp_assoc 0 1 rfl _

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
    simpa using (map_cochainsFunctor_shortExact hX).comp_δ_assoc 1 2 rfl _

/-- When `i = 1`, the general short complex `Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃) ⟶ Hⁱ⁺¹(G, X₁)` associated to
a short exact sequence of representations agrees with our simpler expression for
`H¹(G, X₂) ⟶ H¹(G, X₃) ⟶ H²(G, X₁).` -/
noncomputable def isoH1ShortComplex₃ :
    mapShortComplex₃ hX (i := 1) rfl ≅ H1ShortComplex₃ hX :=
  isoMk (isoH1 _) (isoH1 _) (isoH2 _) (map_comp_isoH1_hom (MonoidHom.id G) _).symm (by simp [δ₁])

theorem H1ShortComplex₃_exact :
    (H1ShortComplex₃ hX).Exact :=
  exact_of_iso (isoH1ShortComplex₃ hX) (mapShortComplex₃_exact _ _)

/-- The short complex  `H¹(G, X₃) ⟶ H²(G, X₁) ⟶ H²(G, X₂)` associated to a short exact
sequence of representations. -/
noncomputable abbrev H2ShortComplex₁ :=
  ShortComplex.mk (δ₁ hX) (H2Map (MonoidHom.id G) X.f) <| by
    simpa [δ₁, ← map_comp_isoH2_hom]
      using (map_cochainsFunctor_shortExact hX).δ_comp_assoc 1 2 rfl _

/-- When `i = 1`, the general short complex `Hⁱ(G, X₃) ⟶ Hⁱ⁺¹(G, X₁) ⟶ Hⁱ⁺¹(G, X₂)` associated to
a short exact sequence of representations agrees with our simpler expression for
`H¹(G, X₃) ⟶ H²(G, X₁) ⟶ H²(G, X₂).` -/
noncomputable def isoH2ShortComplex₁ :
    mapShortComplex₁ hX (i := 1) rfl ≅ H2ShortComplex₁ hX :=
  isoMk (isoH1 _) (isoH2 _) (isoH2 _) (by simp [δ₁]) (map_comp_isoH2_hom (MonoidHom.id G) _).symm

theorem H2ShortComplex₁_exact :
    (H2ShortComplex₁ hX).Exact :=
  exact_of_iso (isoH2ShortComplex₁ hX) (mapShortComplex₁_exact _ _)

end groupCohomology
