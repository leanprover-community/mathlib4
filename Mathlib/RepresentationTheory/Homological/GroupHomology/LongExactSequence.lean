/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Homology.ConcreteCategory
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

universe v u

namespace groupHomology

open CategoryTheory ShortComplex Finsupp

variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]
  {X : ShortComplex (Rep k G)} (hX : ShortExact X)

include hX

lemma map_chainsFunctor_shortExact :
    ShortExact (X.map (chainsFunctor k G)) :=
  letI := hX.mono_f
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => {
    exact := by
      have : LinearMap.range X.f.hom.hom = LinearMap.ker X.g.hom.hom :=
        (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
      simp [moduleCat_exact_iff_range_eq_ker, ker_mapRange, range_mapRange_linearMap X.f.hom.hom
        (LinearMap.ker_eq_bot.2 <| (ModuleCat.mono_iff_injective _).1 _), this]
    mono_f := chainsMap_id_f_map_mono X.f i
    epi_g := letI := hX.epi_g; chainsMap_id_f_map_epi X.g i }

open HomologicalComplex.HomologySequence

/-- The short complex  `Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁) ⟶ Hⱼ(G, X₂)` associated to an exact sequence
of representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev mapShortComplex₁ {i j : ℕ} (hij : j + 1 = i) :=
  (snakeInput (map_chainsFunctor_shortExact hX) _ _ hij).L₂'

variable (X) in
/-- The short complex `Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃)` associated to a short complex of
representations `X₁ ⟶ X₂ ⟶ X₃`. -/
noncomputable abbrev mapShortComplex₂ (i : ℕ) := X.map (functor k G i)

/-- The short complex `Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)` associated to an exact sequence of
representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
noncomputable abbrev mapShortComplex₃ {i j : ℕ} (hij : j + 1 = i) :=
  (snakeInput (map_chainsFunctor_shortExact hX) _ _ hij).L₁'

/-- Exactness of `Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁) ⟶ Hⱼ(G, X₂)`. -/
lemma mapShortComplex₁_exact {i j : ℕ} (hij : j + 1 = i) :
    (mapShortComplex₁ hX hij).Exact :=
  (map_chainsFunctor_shortExact hX).homology_exact₁ i j hij

/-- Exactness of `Hᵢ(G, X₁) ⟶ Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃)`. -/
lemma mapShortComplex₂_exact (i : ℕ) :
    (mapShortComplex₂ X i).Exact :=
  (map_chainsFunctor_shortExact hX).homology_exact₂ i

/-- Exactness of `Hᵢ(G, X₂) ⟶ Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)`. -/
lemma mapShortComplex₃_exact {i j : ℕ} (hij : j + 1 = i) :
    (mapShortComplex₃ hX hij).Exact :=
  (map_chainsFunctor_shortExact hX).homology_exact₃ i j hij

/-- The connecting homomorphism `Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)` associated to an exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations. -/
noncomputable abbrev δ (i j : ℕ) (hij : j + 1 = i) :
    groupHomology X.X₃ i ⟶ groupHomology X.X₁ j :=
  (map_chainsFunctor_shortExact hX).δ i j hij

open Limits
theorem epi_δ_of_isZero (n : ℕ) (h : IsZero (groupHomology X.X₂ n)) :
    Epi (δ hX (n + 1) n rfl) := SnakeInput.epi_δ _ h

theorem mono_δ_of_isZero (n : ℕ) (h : IsZero (groupHomology X.X₂ (n + 1))) :
    Mono (δ hX (n + 1) n rfl) := SnakeInput.mono_δ _ h

theorem isIso_δ_of_isZero (n : ℕ) (hs : IsZero (groupHomology X.X₂ (n + 1)))
    (h : IsZero (groupHomology X.X₂ n)) :
    IsIso (δ hX (n + 1) n rfl) := SnakeInput.isIso_δ _ hs h

/-- Given an exact sequence of `G`-representations `0 ⟶ X₁ ⟶f X₂ ⟶g X₃ ⟶ 0`, this expresses an
`n`-chain `x : Gⁿ →₀ X₁` such that `f ∘ x ∈ Bⁿ(G, X₂)` as a cycle. -/
noncomputable abbrev cyclesMkOfCompEqD {i j : ℕ} {y : (Fin i → G) →₀ X.X₂}
    {x : (Fin j → G) →₀ X.X₁}
    (hx : mapRange.linearMap X.f.hom.hom x = (inhomogeneousChains X.X₂).d i j y) :
    cycles X.X₁ j :=
  cyclesMk ((ComplexShape.down ℕ).next j) rfl x <| by
    simpa using (map_chainsFunctor_shortExact hX).d_eq_zero_of_f_eq_d_apply i j y x
      (by simpa using hx) _

theorem δ_apply {i j : ℕ} (hij : j + 1 = i)
    (z : (Fin i → G) →₀ X.X₃) (hz : (inhomogeneousChains X.X₃).d i j z = 0)
    (y : (Fin i → G) →₀ X.X₂) (hy : (chainsMap (MonoidHom.id G) X.g).f i y = z)
    (x : (Fin j → G) →₀ X.X₁)
    (hx : mapRange.linearMap X.f.hom.hom x = (inhomogeneousChains X.X₂).d i j y) :
    δ hX i j hij (π X.X₃ i <| cyclesMk j (by simp [← hij]) z (by simpa using hz)) =
      π X.X₁ j (cyclesMkOfCompEqD hX hx) := by
  exact (map_chainsFunctor_shortExact hX).δ_apply i j hij z hz y hy x (by simpa using hx) _ rfl

theorem δ₀_apply (z : oneCycles X.X₃) (y : G →₀ X.X₂)
    (hy : mapRange.linearMap X.g.hom.hom y = z.1) (x : X.X₁) (hx : X.f.hom x = dZero X.X₂ y) :
    δ hX 1 0 rfl (H1π X.X₃ z) = H0π X.X₁ x := by
  simpa only [H1π, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, H0π,
    ← cyclesMk_0_eq X.X₁, ← cyclesMk_1_eq X.X₃]
  using δ_apply hX (i := 1) (j := 0) rfl ((oneChainsIso X.X₃).inv z.1) (by simp)
    ((oneChainsIso X.X₂).inv y) (Finsupp.ext fun _ => by simp [oneChainsIso, ← hy])
    ((zeroChainsIso X.X₁).inv x) (Finsupp.ext fun _ => by simp [zeroChainsIso, ← hx])

theorem mem_oneCycles_of_comp_eq_dOne
    {y : G × G →₀ X.X₂} {x : G →₀ X.X₁} (hx : mapRange.linearMap X.f.hom.hom x = dOne X.X₂ y) :
    x ∈ oneCycles X.X₁ := LinearMap.mem_ker.2 <| (Rep.mono_iff_injective X.f).1 hX.2 <| by
  have := congr($((mapShortComplexH1 (MonoidHom.id G) X.f).comm₂₃.symm) x)
  simp_all [shortComplexH1, LinearMap.compLeft]

theorem δ₁_apply (z : twoCycles X.X₃) (y : G × G →₀ X.X₂)
    (hy : mapRange.linearMap X.g.hom.hom y = z.1) (x : G →₀ X.X₁)
    (hx : mapRange.linearMap X.f.hom.hom x = dOne X.X₂ y) :
    δ hX 2 1 rfl (H2π X.X₃ z) = H1π X.X₁ ⟨x, mem_oneCycles_of_comp_eq_dOne hX hx⟩ := by
  simpa only [H2π, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, H1π,
    ← cyclesMk_2_eq X.X₃, ← cyclesMk_1_eq X.X₁]
  using δ_apply hX (i := 2) (j := 1) rfl ((twoChainsIso X.X₃).inv z.1) (by simp)
    ((twoChainsIso X.X₂).inv y) (Finsupp.ext fun _ => by simp [twoChainsIso, ← hy])
    ((oneChainsIso X.X₁).inv x) (Finsupp.ext fun _ => by simp [oneChainsIso, ← hx])

end groupHomology
