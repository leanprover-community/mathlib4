/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

/-!
# Long exact sequence in group homology

Given a commutative ring `k` and a group `G`, this file shows that a short exact sequence of
`k`-linear `G`-representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` induces a short exact sequence of
complexes of inhomogeneous chains `0 ⟶ C(X₁) ⟶ C(X₂) ⟶ C(X₃) ⟶ 0`, where `Hₙ(C(Xᵢ))`
is the `n`th group homology of `Xᵢ`.

This allows us to specialize API about long exact sequences to group homology.

## Main definitions

* `groupHomology.δ hX i j hij`: the connecting homomorphism `Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)` associated
  to an exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations.

-/

universe u

namespace groupHomology

open CategoryTheory ShortComplex Finsupp

variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]
  {X : ShortComplex (Rep k G)} (hX : ShortExact X)

include hX

lemma map_chainsFunctor_shortExact :
    ShortExact (X.map (chainsFunctor k G)) :=
  letI := hX.2
  letI := hX.3
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => {
    exact := by
      have : LinearMap.range X.f.hom.hom = LinearMap.ker X.g.hom.hom :=
        (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
      simp [moduleCat_exact_iff_range_eq_ker, ker_mapRange, range_mapRange_linearMap X.f.hom.hom
        (LinearMap.ker_eq_bot.2 ((ModuleCat.mono_iff_injective _).1 <|
        (forget₂ (Rep k G) (ModuleCat k)).map_mono X.f)), this]
    mono_f := chainsMap_id_f_map_mono X.f i
    epi_g := chainsMap_id_f_map_epi X.g i }

/-- The short complex  `Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁) ⟶ Hⱼ(G, X₂)` associated to an exact sequence
of representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev mapShortComplex₁ {i j : ℕ} (hij : j + 1 = i) :=
  ShortComplex.mk _ _ ((map_chainsFunctor_shortExact hX).δ_comp i j hij)

variable (X) in
/-- The short complex `Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃)` associated to a short complex of
representations `X₁ ⟶ X₂ ⟶ X₃`. -/
noncomputable abbrev mapShortComplex₂ (i : ℕ) :=
  ShortComplex.mk (map (MonoidHom.id G) X.f i) (map (MonoidHom.id G) X.g i) <| by
    simp [← map_id_comp, X.zero, map]

/-- The short complex `Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)` associated to an exact sequence of
representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev mapShortComplex₃ {i j : ℕ} (hij : j + 1 = i) :=
  ShortComplex.mk _ _ ((map_chainsFunctor_shortExact hX).comp_δ i j hij)

/-- Exactness of `Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁) ⟶ Hⱼ(G, X₂)`. -/
lemma mapShortComplex₁_exact {i j : ℕ} (hij : j + 1 = i) :
    (mapShortComplex₁ hX hij).Exact :=
  (map_chainsFunctor_shortExact hX).homology_exact₁ i j hij

/-- Exactness of `Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃)`. -/
lemma mapShortComplex₂_exact (i : ℕ) :
    (mapShortComplex₂ X i).Exact :=
  (map_chainsFunctor_shortExact hX).homology_exact₂ i

/--  Exactness of `Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)`. -/
lemma mapShortComplex₃_exact {i j : ℕ} (hij : j + 1 = i) :
    (mapShortComplex₃ hX hij).Exact :=
  (map_chainsFunctor_shortExact hX).homology_exact₃ i j hij

/-- The connecting homomorphism `Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)` associated to an exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations. -/
noncomputable abbrev δ (i j : ℕ) (hij : j + 1 = i) :
    groupHomology X.X₃ i ⟶ groupHomology X.X₁ j :=
  (map_chainsFunctor_shortExact hX).δ i j hij

theorem δ_apply (i j : ℕ) (hij : j + 1 = i)
    (z : (Fin i → G) →₀ X.X₃) (hz : (inhomogeneousChains X.X₃).d i j z = 0)
    (y : (Fin i → G) →₀ X.X₂) (hy : (chainsMap (MonoidHom.id G) X.g).f i y = z)
    (x : (Fin j → G) →₀ X.X₁)
    (hx : mapRange.linearMap X.f.hom.hom x = (inhomogeneousChains X.X₂).d i j y) :
    δ hX i j hij (groupHomologyπ X.X₃ i <|
      (moduleCatCyclesIso _).inv ⟨z, show ((inhomogeneousChains X.X₃).dFrom i).hom z = 0 by
        simp_all [(inhomogeneousChains X.X₃).dFrom_eq hij]⟩) = groupHomologyπ X.X₁ j
      ((moduleCatCyclesIso _).inv ⟨x, (map_chainsFunctor_shortExact hX).δ_apply_aux i j y x
        (by simpa [chainsMap_id_f_eq_mapRange] using hx) _⟩) := by
  convert (map_chainsFunctor_shortExact hX).δ_apply i j hij z
    hz y hy x (by simpa [chainsMap_id_f_eq_mapRange] using hx) _ rfl
  <;> rw [moduleCatCyclesIso_inv_apply]
  <;> rfl

end groupHomology
