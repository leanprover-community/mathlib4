/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Long exact sequence in group cohomology

Given a commutative ring `k` and a group `G`, this file shows that a short exact sequence of
`k`-linear `G`-representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` induces a short exact sequence of
complexes
`0 ⟶ inhomogeneousCochains X₁ ⟶ inhomogeneousCochains X₂ ⟶ inhomogeneousCochains X₃ ⟶ 0`.

Since the cohomology of `inhomogeneousCochains Xᵢ` is the group cohomology of `Xᵢ`, this allows us
to specialize API about long exact sequences to group cohomology.

## Main definitions

* `groupCohomology.δ hX i j hij`: the connecting homomorphism `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)` associated
  to an exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations.

-/

universe u v

namespace groupCohomology

open CategoryTheory ShortComplex

variable {k G : Type u} [CommRing k] [Group G]
  {X : ShortComplex (Rep k G)} (hX : ShortExact X)

include hX

lemma map_cochainsFunctor_shortExact :
    ShortExact (X.map (cochainsFunctor k G)) :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => {
    exact := by
      have : LinearMap.range X.f.hom.hom = LinearMap.ker X.g.hom.hom :=
        (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
      simp [moduleCat_exact_iff_range_eq_ker, LinearMap.range_compLeft,
        LinearMap.ker_compLeft, this]
    mono_f := letI := hX.mono_f; cochainsMap_id_f_map_mono X.f i
    epi_g := letI := hX.epi_g; cochainsMap_id_f_map_epi X.g i }

open HomologicalComplex.HomologySequence

/-- The short complex `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁) ⟶ Hʲ(G, X₂)` associated to an exact
sequence of representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev mapShortComplex₁ {i j : ℕ} (hij : i + 1 = j) :=
  (snakeInput (map_cochainsFunctor_shortExact hX) _ _ hij).L₂'

variable (X) in
/-- The short complex `Hⁱ(G, X₁) ⟶ Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃)` associated to a short complex of
representations `X₁ ⟶ X₂ ⟶ X₃`. -/
noncomputable abbrev mapShortComplex₂ (i : ℕ) := X.map (functor k G i)

/-- The short complex `Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)`. -/
noncomputable abbrev mapShortComplex₃ {i j : ℕ} (hij : i + 1 = j) :=
  (snakeInput (map_cochainsFunctor_shortExact hX) _ _ hij).L₁'

/-- Exactness of `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁) ⟶ Hʲ(G, X₂)`. -/
lemma mapShortComplex₁_exact {i j : ℕ} (hij : i + 1 = j) :
    (mapShortComplex₁ hX hij).Exact :=
  (map_cochainsFunctor_shortExact hX).homology_exact₁ i j hij

/-- Exactness of `Hⁱ(G, X₁) ⟶ Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃)`. -/
lemma mapShortComplex₂_exact (i : ℕ) :
    (mapShortComplex₂ X i).Exact :=
  (map_cochainsFunctor_shortExact hX).homology_exact₂ i

/-- Exactness of `Hⁱ(G, X₂) ⟶ Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)`. -/
lemma mapShortComplex₃_exact {i j : ℕ} (hij : i + 1 = j) :
    (mapShortComplex₃ hX hij).Exact :=
  (map_cochainsFunctor_shortExact hX).homology_exact₃ i j hij

/-- The connecting homomorphism `Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)` associated to an exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations. -/
noncomputable abbrev δ (i j : ℕ) (hij : i + 1 = j) :
    groupCohomology X.X₃ i ⟶ groupCohomology X.X₁ j :=
  (map_cochainsFunctor_shortExact hX).δ i j hij

open Limits

theorem epi_δ_of_isZero (n : ℕ) (h : IsZero (groupCohomology X.X₂ (n + 1))) :
    Epi (δ hX n (n + 1) rfl) := SnakeInput.epi_δ _ h

theorem mono_δ_of_isZero (n : ℕ) (h : IsZero (groupCohomology X.X₂ n)) :
    Mono (δ hX n (n + 1) rfl) := SnakeInput.mono_δ _ h

theorem isIso_δ_of_isZero (n : ℕ) (h : IsZero (groupCohomology X.X₂ n))
    (hs : IsZero (groupCohomology X.X₂ (n + 1))) :
    IsIso (δ hX n (n + 1) rfl) := SnakeInput.isIso_δ _ h hs

/-- Given an exact sequence of `G`-representations `0 ⟶ X₁ ⟶f X₂ ⟶g X₃ ⟶ 0`, this expresses an
`n + 1`-cochain `x : Gⁿ⁺¹ → X₁` such that `f ∘ x ∈ Bⁿ⁺¹(G, X₂)` as a cocycle.
Stated for readability of `δ_apply`. -/
noncomputable abbrev cocyclesMkOfCompEqD {i j : ℕ} {y : (Fin i → G) → X.X₂}
    {x : (Fin j → G) → X.X₁} (hx : X.f.hom ∘ x = (inhomogeneousCochains X.X₂).d i j y) :
    cocycles X.X₁ j :=
  cocyclesMk x <| by simpa using
    ((map_cochainsFunctor_shortExact hX).d_eq_zero_of_f_eq_d_apply i j y x
      (by simpa using hx) (j + 1))

theorem δ_apply {i j : ℕ} (hij : i + 1 = j)
    -- Let `0 ⟶ X₁ ⟶f X₂ ⟶g X₃ ⟶ 0` be a short exact sequence of `G`-representations.
    -- Let `z` be an `i`-cocycle for `X₃`
    (z : (Fin i → G) → X.X₃) (hz : (inhomogeneousCochains X.X₃).d i j z = 0)
    -- Let `y` be an `i`-cochain for `X₂` such that `g ∘ y = z`
    (y : (Fin i → G) → X.X₂) (hy : (cochainsMap (MonoidHom.id G) X.g).f i y = z)
    -- Let `x` be an `i + 1`-cochain for `X₁` such that `f ∘ x = d(y)`
    (x : (Fin j → G) → X.X₁) (hx : X.f.hom ∘ x = (inhomogeneousCochains X.X₂).d i j y) :
    -- Then `x` is an `i + 1`-cocycle and `δ z = x` in `Hⁱ⁺¹(X₁)`.
    δ hX i j hij (π X.X₃ i <| cocyclesMk z (by subst hij; simpa using hz)) =
      π X.X₁ j (cocyclesMkOfCompEqD hX hx) := by
  exact (map_cochainsFunctor_shortExact hX).δ_apply i j hij z hz y hy x
    (by simpa using hx) (j + 1) (by simp)

/-- Stated for readability of `δ₀_apply`. -/
theorem mem_cocycles₁_of_comp_eq_d₀₁
    {y : X.X₂} {x : G → X.X₁} (hx : X.f.hom ∘ x = d₀₁ X.X₂ y) :
    x ∈ cocycles₁ X.X₁ := by
  apply Function.Injective.comp_left ((Rep.mono_iff_injective X.f).1 hX.2)
  have := congr($((mapShortComplexH1 (MonoidHom.id G) X.f).comm₂₃.symm) x)
  simp_all [shortComplexH1, LinearMap.compLeft]

@[deprecated (since := "2025-07-02")]
alias mem_oneCocycles_of_comp_eq_dZero := mem_cocycles₁_of_comp_eq_d₀₁

theorem δ₀_apply
    -- Let `0 ⟶ X₁ ⟶f X₂ ⟶g X₃ ⟶ 0` be a short exact sequence of `G`-representations.
    -- Let `z : X₃ᴳ` and `y : X₂` be such that `g(y) = z`.
    (z : X.X₃.ρ.invariants) (y : X.X₂) (hy : X.g.hom y = z)
    -- Let `x` be a 1-cochain for `X₁` such that `f ∘ x = d(y)`.
    (x : G → X.X₁) (hx : X.f.hom ∘ x = d₀₁ X.X₂ y) :
    -- Then `x` is a 1-cocycle and `δ z = x` in `H¹(X₁)`.
    δ hX 0 1 rfl ((H0Iso X.X₃).inv z) = H1π X.X₁ ⟨x, mem_cocycles₁_of_comp_eq_d₀₁ hX hx⟩ := by
  simpa [H0Iso, H1π, ← cocyclesMk₁_eq X.X₁, ← cocyclesMk₀_eq z] using
    δ_apply hX rfl ((cochainsIso₀ X.X₃).inv z.1) (by simp) ((cochainsIso₀ X.X₂).inv y)
    (by ext; simp [← hy, cochainsIso₀]) ((cochainsIso₁ X.X₁).inv x) <| by
      ext g
      simpa [← hx] using congr_fun (congr($((CommSq.vert_inv
        ⟨cochainsMap_f_1_comp_cochainsIso₁ (MonoidHom.id G) X.f⟩).w) x)) g

/-- Stated for readability of `δ₁_apply`. -/
theorem mem_cocycles₂_of_comp_eq_d₁₂
    {y : G → X.X₂} {x : G × G → X.X₁} (hx : X.f.hom ∘ x = d₁₂ X.X₂ y) :
    x ∈ cocycles₂ X.X₁ := by
  apply Function.Injective.comp_left ((Rep.mono_iff_injective X.f).1 hX.2)
  have := congr($((mapShortComplexH2 (MonoidHom.id G) X.f).comm₂₃.symm) x)
  simp_all [shortComplexH2, LinearMap.compLeft]

@[deprecated (since := "2025-07-02")]
alias mem_twoCocycles_of_comp_eq_dOne := mem_cocycles₂_of_comp_eq_d₁₂

theorem δ₁_apply
    -- Let `0 ⟶ X₁ ⟶f X₂ ⟶g X₃ ⟶ 0` be a short exact sequence of `G`-representations.
    -- Let `z` be a 1-cocycle for `X₃` and `y` be a 1-cochain for `X₂` such that `g ∘ y = z`.
    (z : cocycles₁ X.X₃) (y : G → X.X₂) (hy : X.g.hom ∘ y = z)
    -- Let `x` be a 2-cochain for `X₁` such that `f ∘ x = d(y)`.
    (x : G × G → X.X₁) (hx : X.f.hom ∘ x = d₁₂ X.X₂ y) :
    -- Then `x` is a 2-cocycle and `δ z = x` in `H²(X₁)`.
    δ hX 1 2 rfl (H1π X.X₃ z) = H2π X.X₁ ⟨x, mem_cocycles₂_of_comp_eq_d₁₂ hX hx⟩ := by
  simpa [H1π, H2π, ← cocyclesMk₂_eq X.X₁, ← cocyclesMk₁_eq X.X₃] using
    δ_apply hX rfl ((cochainsIso₁ X.X₃).inv z) (by simp [cocycles₁.d₁₂_apply z])
    ((cochainsIso₁ X.X₂).inv y) (by ext; simp [cochainsIso₁, ← hy])
    ((cochainsIso₂ X.X₁).inv x) <| by
      ext g
      simpa [← hx] using congr_fun (congr($((CommSq.vert_inv
        ⟨cochainsMap_f_2_comp_cochainsIso₂ (MonoidHom.id G) X.f⟩).w) x)) g

end groupCohomology
