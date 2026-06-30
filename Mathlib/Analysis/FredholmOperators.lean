/-
Copyright (c) 2026 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Anatole Dedecker, Patrick Massot, Yongxi Lin, Oliver Nash, Filippo A. E. Nuccio
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.Perturbation.StrictByFinite
public import Mathlib.Algebra.Module.LinearMap.Index

/-!
# Fredholm operators between topological vector spaces
-/

@[expose] public noncomputable section

open Topology Submodule LinearMap
open LinearMap.FiniteRangeSetoid

section TVS
namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [AddCommGroup F]
    [Module 𝕜 E] [Module 𝕜 F] [TopologicalSpace E] [TopologicalSpace F]

/-!
## Definition and equivalent conditions
-/

section DefTFAE

section IsFredholm

structure IsFredholm (f : E →L[𝕜] F) : Prop where
  isStrictMap : IsStrictMap f
  isClosed_range : IsClosed (f.range : Set F)
  finite_ker : FiniteDimensional 𝕜 f.ker
  finite_coker : FiniteDimensional 𝕜 (F ⧸ f.range)
  closedComplemented_ker : f.ker.ClosedComplemented

variable [CompleteSpace 𝕜] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] in
lemma IsFredholm.closedComplemented_range {f : E →L[𝕜] F} (f_fred : IsFredholm f) :
    f.range.ClosedComplemented :=
  have := f_fred.finite_coker
  ClosedComplemented.of_finiteDimensional_quotient f_fred.isClosed_range

end IsFredholm

section FredholmDecomposition

variable [ContinuousSub E]

structure FredholmDecomposition (f : E →L[𝕜] F) where
  dom₀ : Submodule 𝕜 E
  dom₁ : Submodule 𝕜 E
  finite_dom₀ : FiniteDimensional 𝕜 dom₀
  isTopCompl_dom : IsTopCompl dom₀ dom₁
  codom₀ : Submodule 𝕜 F
  codom₁ : Submodule 𝕜 F
  finite_codom₀ : FiniteDimensional 𝕜 codom₀
  isTopCompl_codom : IsTopCompl codom₀ codom₁
  equiv : dom₁ ≃L[𝕜] codom₁
  eq_equiv' : f = codom₁.subtypeL ∘L equiv ∘L (dom₁.projectionOntoL dom₀ isTopCompl_dom.symm)

abbrev FredholmDecomposition.domProj {f : E →L[𝕜] F} (dec : FredholmDecomposition f) :
    E →L[𝕜] dec.dom₁ := dec.dom₁.projectionOntoL dec.dom₀ dec.isTopCompl_dom.symm

variable [ContinuousSub F] in
abbrev FredholmDecomposition.codomProj {f : E →L[𝕜] F} (dec : FredholmDecomposition f) :
    F →L[𝕜] dec.codom₁ := dec.codom₁.projectionOntoL dec.codom₀ dec.isTopCompl_codom.symm

lemma FredholmDecomposition.eq_equiv {f : E →L[𝕜] F} (dec : FredholmDecomposition f) :
    f = dec.codom₁.subtypeL ∘L dec.equiv ∘L dec.domProj :=
  dec.eq_equiv'

lemma FredholmDecomposition.ker_eq {f : E →L[𝕜] F} (dec : FredholmDecomposition f) :
    f.ker = dec.dom₀ := by
  simp [dec.eq_equiv, ker_comp]

lemma FredholmDecomposition.range_eq {f : E →L[𝕜] F} (dec : FredholmDecomposition f) :
    f.range = dec.codom₁ := by
  simp [dec.eq_equiv, range_comp]

end FredholmDecomposition

section TFAE

end TFAE

variable [IsTopologicalAddGroup E]
-- missing hyps

theorem isFredholmTFAE (f : E →L[𝕜] F) : List.TFAE
    [
      IsFredholm f,
      ∃ g : F →L[𝕜] E, g.IsQuasiInverse f,
      ∃ (E₁ : Submodule 𝕜 E) (F₁ : Submodule 𝕜 F),
        IsClosed (E₁ : Set E) ∧ IsClosed (F₁ : Set F) ∧
        E₁.CoFG ∧ F₁.CoFG ∧
        ∃ h : Set.MapsTo f E₁ F₁, (f.restrict h).IsInvertible,
      Nonempty (FredholmDecomposition f)
    ] := by
  sorry

end DefTFAE

end ContinuousLinearMap
end TVS

end
