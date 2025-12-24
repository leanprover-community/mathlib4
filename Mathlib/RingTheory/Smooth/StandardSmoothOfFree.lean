/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.Basis
public import Mathlib.RingTheory.Extension.Cotangent.Free

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

## Notes

For an example of an algebra with `H¹(S/R) = 0` and `Ω[S⁄R]` finite and free, but
`S` not standard smooth over `R`, consider `R = ℝ` and `S = R[x,y]/(x² + y² - 1)` the
coordinate ring of the circle. One can show that then `Ω[S⁄R]` is `S`-free on `ω = xdy - ydx`,
but there are no `f g : S` such that `ω = g df`.

## TODOs

- Deduce from this that smooth is equivalent to locally standard smooth (TODO @chrisflav).
-/

@[expose] public section

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

end Algebra
