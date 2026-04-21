/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

/-!
# Long exact sequence in group homology

Given a commutative ring `k` and a group `G`, this file shows that a short exact sequence of
`k`-linear `G`-representations `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` induces a short exact sequence of
complexes
`0 ⟶ inhomogeneousChains X₁ ⟶ inhomogeneousChains X₂ ⟶ inhomogeneousChains X₃ ⟶ 0`.

Since the homology of `inhomogeneousChains Xᵢ` is the group homology of `Xᵢ`, this allows us
to specialize API about long exact sequences to group homology.

## Main definitions

* `groupHomology.δ hX i j hij`: the connecting homomorphism `Hᵢ(G, X₃) ⟶ Hⱼ(G, X₁)` associated
  to an exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations.

-/
set_option backward.defeqAttrib.useBackward true

public section

universe v u

namespace groupHomology

open CategoryTheory ShortComplex Finsupp

variable {k G : Type u} [CommRing k] [Group G] {X : ShortComplex (Rep k G)} (hX : ShortExact X)

include hX

set_option backward.isDefEq.respectTransparency false in
lemma map_chainsFunctor_shortExact :
    ShortExact (X.map (chainsFunctor k G)) :=
  letI := hX.mono_f
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => {
    exact := by
      have : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
        (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
      simp [moduleCat_exact_iff_range_eq_ker, ker_mapRange,
        range_mapRange_linearMap X.f.hom.toLinearMap (LinearMap.ker_eq_bot.2 <|
        (Rep.mono_iff_injective X.f).1 hX.mono_f), this]
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

set_option backward.isDefEq.respectTransparency false in
/-- Given an exact sequence of `G`-representations `0 ⟶ X₁ ⟶f X₂ ⟶g X₃ ⟶ 0`, this expresses an
`n`-chain `x : Gⁿ →₀ X₁` such that `f ∘ x ∈ Bₙ(G, X₂)` as a cycle. Stated for readability of
`δ_apply`. -/
noncomputable abbrev cyclesMkOfCompEqD {i j : ℕ} {y : (Fin i → G) →₀ X.X₂}
    {x : (Fin j → G) →₀ X.X₁}
    (hx : mapRange.linearMap X.f.hom.toLinearMap x = (inhomogeneousChains X.X₂).d i j y) :
    cycles X.X₁ j :=
  cyclesMk j _ rfl x <| by
    simpa using (map_chainsFunctor_shortExact hX).d_eq_zero_of_f_eq_d_apply i j y x
      (by simpa using hx) _

set_option backward.isDefEq.respectTransparency false in
theorem δ_apply {i j : ℕ} (hij : j + 1 = i)
    -- Let `0 ⟶ X₁ ⟶f X₂ ⟶g X₃ ⟶ 0` be a short exact sequence of `G`-representations.
    -- Let `z` be an `j + 1`-cycle for `X₃`
    (z : (Fin i → G) →₀ X.X₃) (hz : (inhomogeneousChains X.X₃).d i j z = 0)
    -- Let `y` be an `j + 1`-chain for `X₂` such that `g ∘ y = z`
    (y : (Fin i → G) →₀ X.X₂) (hy : (chainsMap (MonoidHom.id G) X.g).f i y = z)
    -- Let `x` be an `j`-chain for `X₁` such that `f ∘ x = d(y)`
    (x : (Fin j → G) →₀ X.X₁)
    -- Then `x` is an `j`-cycle and `δ z = x` in `Hⱼ(X₁)`.
    (hx : mapRange.linearMap X.f.hom.toLinearMap x = (inhomogeneousChains X.X₂).d i j y) :
    δ hX i j hij (π X.X₃ i <| cyclesMk i j (by simp [← hij]) z (by simpa using hz)) =
      π X.X₁ j (cyclesMkOfCompEqD hX hx) := by
  exact (map_chainsFunctor_shortExact hX).δ_apply i j hij z hz y hy x (by simpa using hx) _ rfl

set_option backward.isDefEq.respectTransparency false in
theorem δ₀_apply
    -- Let `0 ⟶ X₁ ⟶f X₂ ⟶g X₃ ⟶ 0` be a short exact sequence of `G`-representations.
    -- Let `z` by a 1-cycle for `X₃` and `y` a 1-chain for `X₂` such that `g ∘ y = z`.
    (z : cycles₁ X.X₃) (y : G →₀ X.X₂) (hy : mapRange.linearMap X.g.hom.toLinearMap y = z.1)
    -- Let `x : X₁` be such that `f(x) = d(y)`.
    (x : X.X₁) (hx : X.f.hom x = d₁₀ X.X₂ y) :
    -- Then `δ z = x` in `H₀(X₁)`.
    δ hX 1 0 rfl (H1π X.X₃ z) = H0π X.X₁ x := by
  simpa only [H1π, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, H0π,
    ← cyclesMk₀_eq X.X₁, ← cyclesMk₁_eq X.X₃]
  using δ_apply hX (i := 1) (j := 0) rfl ((chainsIso₁ X.X₃).inv z.1) (by simp +instances)
    ((chainsIso₁ X.X₂).inv y) (Finsupp.ext fun _ => by simp [chainsIso₁, ← hy])
    ((chainsIso₀ X.X₁).inv x) (Finsupp.ext fun _ => by simp [chainsIso₀, ← hx])

set_option backward.isDefEq.respectTransparency false in
/-- Stated for readability of `δ₁_apply`. -/
theorem mem_cycles₁_of_comp_eq_d₂₁
    {y : G × G →₀ X.X₂} {x : G →₀ X.X₁} (hx : mapRange.linearMap X.f.hom.toLinearMap x =
    d₂₁ X.X₂ y) :
    x ∈ cycles₁ X.X₁ := LinearMap.mem_ker.2 <| (Rep.mono_iff_injective X.f).1 hX.2 <| by
  have := congr($((mapShortComplexH1 (MonoidHom.id G) X.f).comm₂₃.symm) x)
  simp_all [shortComplexH1]

set_option backward.isDefEq.respectTransparency false in
theorem δ₁_apply
    -- Let `0 ⟶ X₁ ⟶f X₂ ⟶g X₃ ⟶ 0` be a short exact sequence of `G`-representations.
    -- Let `z` by a 2-cycle for `X₃` and `y` a 2-chain for `X₂` such that `g ∘ y = z`.
    (z : cycles₂ X.X₃) (y : G × G →₀ X.X₂) (hy : mapRange.linearMap X.g.hom.toLinearMap y = z.1)
    -- Let `x` be a 1-chain for `X₁` such that `f ∘ x = d(y)`.
    (x : G →₀ X.X₁) (hx : mapRange.linearMap X.f.hom.toLinearMap x = d₂₁ X.X₂ y) :
    -- Then `x` is a 1-cycle and `δ z = x` in `H₁(X₁)`.
    δ hX 2 1 rfl (H2π X.X₃ z) = H1π X.X₁ ⟨x, mem_cycles₁_of_comp_eq_d₂₁ hX hx⟩ := by
  simpa only [H2π, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, H1π,
    ← cyclesMk₂_eq X.X₃, ← cyclesMk₁_eq X.X₁]
  using δ_apply hX (i := 2) (j := 1) rfl ((chainsIso₂ X.X₃).inv z.1) (by simp +instances)
    ((chainsIso₂ X.X₂).inv y) (Finsupp.ext fun _ => by simp [chainsIso₂, ← hy])
    ((chainsIso₁ X.X₁).inv x) (Finsupp.ext fun _ => by simp [chainsIso₁, ← hx])

end groupHomology
