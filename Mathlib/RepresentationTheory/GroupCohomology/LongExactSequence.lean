/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Homology.ConcreteCategory
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
      simp [moduleCat_exact_iff_range_eq_ker, LinearMap.range_compLeft,
        LinearMap.ker_compLeft, this]
    mono_f := letI := hX.2; cochainsMap_id_f_map_mono X.f i
    epi_g := letI := hX.3; cochainsMap_id_f_map_epi X.g i }

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

noncomputable abbrev cocyclesMkOfCompEqD {i j : ℕ} {y : (Fin i → G) → X.X₂}
    {x : (Fin j → G) → X.X₁} (hx : X.f.hom ∘ x = (inhomogeneousCochains X.X₂).d i j y) :
    cocycles X.X₁ j :=
  cocyclesMk x <| by simpa using
    ((map_cochainsFunctor_shortExact hX).d_eq_zero_of_f_eq_d_apply i j y x
      (by simpa [cochainsMap_id_f_eq_compLeft] using hx) (j + 1))

theorem δ_apply {i j : ℕ} (hij : i + 1 = j)
    (z : (Fin i → G) → X.X₃) (hz : (inhomogeneousCochains X.X₃).d i j z = 0)
    (y : (Fin i → G) → X.X₂) (hy : (cochainsMap (MonoidHom.id G) X.g).f i y = z)
    (x : (Fin j → G) → X.X₁) (hx : X.f.hom ∘ x = (inhomogeneousCochains X.X₂).d i j y) :
    δ hX i j hij (groupCohomologyπ X.X₃ i <| cocyclesMk z (by subst hij; simpa using hz)) =
      groupCohomologyπ X.X₁ j (cocyclesMkOfCompEqD hx) := by
  exact (map_cochainsFunctor_shortExact hX).δ_apply i j hij z hz y hy x
    (by simpa [cochainsMap_id_f_eq_compLeft] using hx) (j + 1) (by simp)

theorem memOneCocycles_of_comp_eq_dZero {y : X.X₂} {x : G → X.X₁} (hx : X.f.hom ∘ x = dZero X.X₂ y) :
    MemOneCocycles x := by
  apply Function.Injective.comp_left ((Rep.mono_iff_injective X.f).1 hX.2)
  have := congr($((mapShortComplexH1 (MonoidHom.id G) X.f).comm₂₃.symm) x)
  have := congr($(dZero_comp_dOne X.X₂) y)
  simp_all [shortComplexH1, LinearMap.compLeft]

theorem δ₀_apply (z : X.X₃.ρ.invariants) (y : X.X₂)
    (hy : X.g.hom y = z) (x : G → X.X₁) (hx : X.f.hom ∘ x = dZero X.X₂ y) :
    δ hX 0 1 rfl ((H0Iso X.X₃).inv z) =
      groupCohomologyπ X.X₁ 1 (mkOneCocycles x <| memOneCocycles_of_comp_eq_dZero hX hx) := by
  have := δ_apply hX rfl ((zeroCochainsIso X.X₃).inv z.1) ?_
    ((zeroCochainsIso X.X₂).inv y) ?_ ((oneCochainsIso X.X₁).inv x) ?_
  convert this
  · rw [mk_eq_zeroCocyclesIso_inv_apply]
    rfl
  · sorry
  · funext
    simp [zeroCochainsIso, hy]
  · sorry

theorem memCocycles₂_of_comp_eq_dOne
    {y : G → X.X₂} {x : G × G → X.X₁} (hx : X.f.hom ∘ x = dOne X.X₂ y) :
    MemTwoCocycles x := by
  apply Function.Injective.comp_left ((Rep.mono_iff_injective X.f).1 hX.2)
  have := congr($((mapShortComplexH2 (MonoidHom.id G) X.f).comm₂₃.symm) x)
  have := congr($(dOne_comp_dTwo X.X₂) y)
  simp_all [shortComplexH2, LinearMap.compLeft]

theorem δ₁_apply (z : G → X.X₃) (hz : MemOneCocycles z) (y : G → X.X₂)
    (hy : X.g.hom ∘ y = z) (x : G × G → X.X₁) (hx : X.f.hom ∘ x = dOne X.X₂ y) :
    δ hX 1 2 rfl (groupCohomologyπ _ 1 <| mkOneCocycles z hz) =
      groupCohomologyπ X.X₁ _ (mkTwoCocycles x <| memCocycles₂_of_comp_eq_dOne hX hx) := by
  have := δ_apply hX rfl ((oneCochainsIso X.X₃).inv z) ?_
    ((oneCochainsIso X.X₂).inv y) ?_ ((twoCochainsIso X.X₁).inv x) ?_
  convert this
  · sorry
  · funext g
    simp [oneCochainsIso, ← hy]
  · simp
    sorry

open Limits

theorem epi_δ_of_isZero (n : ℕ) (h : IsZero (groupCohomology X.X₂ (n + 1))) :
    Epi (δ hX n (n + 1) rfl) := SnakeInput.epi_δ _ h

end groupCohomology
