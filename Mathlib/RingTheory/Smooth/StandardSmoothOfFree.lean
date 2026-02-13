/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.Basis
public import Mathlib.RingTheory.Extension.Cotangent.Free
public import Mathlib.RingTheory.Smooth.Locus

/-!
# Standard smooth of free Kaehler differentials

In this file we show a presentation independent characterization of being
standard smooth: An `R`-algebra `S` of finite presentation is standard smooth if and only if
`H¹(S/R) = 0` and `Ω[S⁄R]` is free on `{d sᵢ}ᵢ` for some `sᵢ : S`.

From this we deduce relations of standard smooth with other local properties.

## Main results

- `IsStandardSmooth.iff_exists_basis_kaehlerDifferential`: An `R`-algebra `S` of finite
  presentation is standard smooth if and only if `H¹(S/R) = 0` and `Ω[S⁄R]` is free on
  `{d sᵢ}ᵢ` for some `sᵢ : S`.
- `Etale.iff_isStandardSmoothOfRelativeDimension_zero`: An `R`-algebra `S` is
  étale if and only if it is standard smooth of relative dimension zero.
- `IsSmoothAt.exists_notMem_isStandardSmooth`: If `S` is `R`-smooth at a prime `p`,
  it is standard smooth on a standard open containing `p`.

## Notes

For an example of an algebra with `H¹(S/R) = 0` and `Ω[S⁄R]` finite and free, but
`S` not standard smooth over `R`, consider `R = ℝ` and `S = R[x,y]/(x² + y² - 1)` the
coordinate ring of the circle. One can show that then `Ω[S⁄R]` is `S`-free on `ω = xdy - ydx`,
but there are no `f g : S` such that `ω = g df`.
-/

public section

namespace Algebra

open KaehlerDifferential

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- If `H¹(S/R) = 0` and `Ω[S⁄R]` is free on `{d sᵢ}ᵢ` for some `sᵢ : S`, then `S`
is `R`-standard smooth. -/
theorem IsStandardSmooth.of_basis_kaehlerDifferential [FinitePresentation R S]
    [Subsingleton (H1Cotangent R S)]
    {I : Type*} (b : Module.Basis I S (Ω[S⁄R])) (hb : Set.range b ⊆ Set.range (D R S)) :
    IsStandardSmooth R S := by
  nontriviality S
  obtain ⟨n, ⟨P⟩⟩ := (FiniteType.iff_exists_generators (R := R) (S := S)).mp inferInstance
  choose f' hf' using hb
  let P := P.extend fun i ↦ f' ⟨i, rfl⟩
  have hb (i : I) : b i = D R S (P.val (Sum.inr i)) := by simp [P, hf']
  have : Function.Bijective (P.cotangentRestrict _) :=
    P.cotangentRestrict_bijective_of_basis_kaehlerDifferential Sum.inl_injective
      Set.isCompl_range_inl_range_inr.symm b hb
  let bcot' : Module.Basis (Fin n) S P.toExtension.Cotangent :=
    .ofRepr (.ofBijective (P.cotangentRestrict _) this)
  have : Finite I := Module.Finite.finite_basis b
  obtain ⟨Q, bcot, hcomp, hbcot⟩ := P.exists_presentation_of_basis_cotangent bcot'
  let P' : PreSubmersivePresentation R S (Unit ⊕ Fin n ⊕ I) (Unit ⊕ Fin n) :=
    { __ := Q
      map := Sum.map _root_.id Sum.inl
      map_inj := Sum.map_injective.mpr ⟨fun _ _ h ↦ h, Sum.inl_injective⟩ }
  have hcompl : IsCompl (Set.range (Sum.inr ∘ Sum.inr)) (Set.range P'.map) := by
    simp [P', ← eq_compl_iff_isCompl, Set.ext_iff, Set.mem_compl_iff]
  have hbij : Function.Bijective (P'.cotangentRestrict P'.map_inj) := by
    apply P'.cotangentRestrict_bijective_of_basis_kaehlerDifferential P'.map_inj hcompl b
    intro k
    simp only [hb, ← hcomp, P', Function.comp_def]
  let P'' : SubmersivePresentation R S _ _ :=
    ⟨P', P'.isUnit_jacobian_of_cotangentRestrict_bijective bcot hbcot hbij⟩
  exact P''.isStandardSmooth

/-- An `R`-algebra `S` of finite presentation is standard smooth if and only if
`H¹(S/R) = 0` and `Ω[S⁄R]` is free on `{d sᵢ}ᵢ` for some `sᵢ : S`. -/
theorem IsStandardSmooth.iff_exists_basis_kaehlerDifferential [FinitePresentation R S] :
    IsStandardSmooth R S ↔ Subsingleton (H1Cotangent R S) ∧
      ∃ (I : Type) (b : Module.Basis I S (Ω[S⁄R])), Set.range b ⊆ Set.range (D R S) := by
  refine ⟨fun h ↦ ⟨inferInstance, ?_⟩, fun ⟨h, ⟨_, b, hb⟩⟩ ↦ .of_basis_kaehlerDifferential b hb⟩
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := Algebra.IsStandardSmooth.out (R := R) (S := S)
  exact ⟨_, P.basisKaehler, by simp [Set.range_subset_iff]⟩

/-- `S` is an étale `R`-algebra if and only if it is standard smooth of relative dimension `0`. -/
theorem Etale.iff_isStandardSmoothOfRelativeDimension_zero :
    Etale R S ↔ IsStandardSmoothOfRelativeDimension 0 R S := by
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  nontriviality S
  suffices h : IsStandardSmooth R S by
    simp [IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth]
  rw [IsStandardSmooth.iff_exists_basis_kaehlerDifferential]
  refine ⟨inferInstance, ⟨Empty, Module.Basis.empty Ω[S⁄R], ?_⟩⟩
  simp [Set.range_subset_iff]

variable (R) in
/-- If `S` is `R`-smooth at a prime `p`, then `S` is `R`-standard-smooth in a neighbourhood of `p`:
there exists a basic open `p ∈ D(f)` of `Spec S` such that `S[1/f]` is standard smooth. -/
theorem IsSmoothAt.exists_notMem_isStandardSmooth [FinitePresentation R S] (p : Ideal S) [p.IsPrime]
    [IsSmoothAt R p] :
    ∃ (f : S), f ∉ p ∧ IsStandardSmooth R (Localization.Away f) := by
  -- By replacing `S` by some `S[1/g]` we may assume `S` is globally smooth.
  wlog h : Smooth R S
  · obtain ⟨g, hg, hsm⟩ := IsSmoothAt.exists_notMem_smooth R p
    have _ : (Ideal.map (algebraMap S (Localization.Away g)) p).IsPrime := by
      apply IsLocalization.isPrime_of_isPrime_disjoint (.powers g) _ _ ‹_›
      rwa [Ideal.disjoint_powers_iff_notMem _ (Ideal.IsPrime.isRadical ‹_›)]
    obtain ⟨g', hg', hstd⟩ := this (R := R) (p.map (algebraMap S (Localization.Away g))) hsm
    have : IsLocalization.Away (g * (IsLocalization.Away.sec g g').1) (Localization.Away g') :=
      .mul_of_associated _ _ g' <| IsLocalization.Away.associated_sec_fst g g'
    let e : Localization.Away (g * (IsLocalization.Away.sec g g').1) ≃ₐ[S] Localization.Away g' :=
      Localization.algEquiv _ _
    refine ⟨g * (IsLocalization.Away.sec g g').1, ?_, .of_algEquiv (e.restrictScalars R).symm⟩
    refine Ideal.IsPrime.mul_notMem ‹_› hg fun hmem ↦ hg' ?_
    rw [Ideal.mem_iff_of_associated (IsLocalization.Away.associated_sec_fst g g').symm]
    exact Ideal.mem_map_of_mem (algebraMap S (Localization.Away g)) hmem
  -- `Ω[Sₚ⁄R]` is projective, so free over the local ring `Sₚ` and
  -- a basis extends to a neighbourhood `D(g)`.
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat _
    (span_range_map_derivation_of_isLocalization R _ (Localization.AtPrime p) p.primeCompl)
  let e : (κ →₀ S) →ₗ[S] Ω[S⁄R] :=
    Finsupp.linearCombination S fun i : κ ↦ D R S (a i)
  let l₁ : (κ →₀ S) →ₗ[S] (κ →₀ Localization.AtPrime p) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S (Localization.AtPrime p))
  let l₂ : Ω[S⁄R] →ₗ[S] Ω[Localization.AtPrime p⁄R] := map R R S (Localization.AtPrime p)
  let eₚ : (κ →₀ Localization.AtPrime p) →ₗ[Localization.AtPrime p] Ω[Localization.AtPrime p⁄R] :=
    IsLocalizedModule.mapExtendScalars p.primeCompl l₁ l₂ (Localization.AtPrime p) e
  have : eₚ = b.repr.symm := by
    ext i
    trans IsLocalizedModule.map p.primeCompl l₁ l₂ e <| l₁ <| Finsupp.single i 1
    · simp [eₚ, -IsLocalizedModule.map_apply, l₁]
    · simp [l₂, e, hb]
  have heₚ : Function.Bijective eₚ := this ▸ b.repr.symm.bijective
  have : Finite κ := Module.Finite.finite_basis b
  obtain ⟨g, hg, h⟩ := Module.FinitePresentation.exists_notMem_bijective e p l₁ l₂ heₚ
  let l₁ₜ : (κ →₀ S) →ₗ[S] (κ →₀ Localization.Away g) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S _)
  let l₂ₜ : Ω[S⁄R] →ₗ[S] Ω[Localization.Away g⁄R] :=
    map R R S (Localization.Away g)
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective l₁ₜ l₂ₜ] at h
  let eₜ' : (κ →₀ Localization.Away g) →ₗ[Localization.Away g] Ω[Localization.Away g⁄R] :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers g) l₁ₜ l₂ₜ (Localization.Away g) e
  refine ⟨g, hg, .of_basis_kaehlerDifferential (.ofRepr (LinearEquiv.ofBijective eₜ' h).symm) ?_⟩
  rintro - ⟨i, rfl⟩
  exact ⟨algebraMap S _ (a i), by simp +zetaDelta [IsLocalizedModule.map_linearCombination]⟩

variable (R S) in
/-- If `S` is `R`-smooth, there exists a cover by basic opens `D(sᵢ)` such that
`S[1/sᵢ]` is `R`-standard-smooth. -/
theorem Smooth.exists_span_eq_top_isStandardSmooth [Smooth R S] :
    ∃ (s : Set S), Ideal.span s = ⊤ ∧ ∀ x ∈ s, IsStandardSmooth R (Localization.Away x) := by
  choose f hf₁ hf₂ using IsSmoothAt.exists_notMem_isStandardSmooth R (S := S)
  refine ⟨Set.range (fun p : PrimeSpectrum S ↦ f p.asIdeal), ?_, by grind⟩
  simp [← PrimeSpectrum.iSup_basicOpen_eq_top_iff, TopologicalSpace.Opens.ext_iff, Set.ext_iff]
  grind

end Algebra
