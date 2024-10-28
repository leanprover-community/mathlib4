/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Module.Presentation.Basic

/-!
# Presentation of a cokernel

If `f : M₁ →ₗ[A] M₂` is a linear map between modules, and
`pres₂` is a presentation of `M₂` and `g₁ : ι → M₁` is
a family of generators of `M₁` (which is expresses as
`hg₁ : Submodule.span A (Set.range g₁) = ⊤`), then we
provide a way to obtain a presentation of the cokernel of `f`.
It requires an additional data `data : pres₂.CokernelData f g₁`,
which consists of liftings of the images by `f` of
the generators of `M₁` as linear combinations of the
generators of `M₂`. Then, we obtain a presentation
`pres₂.cokernel data hg₁ : Presentation A (M₂ ⧸ LinearMap.range f)`.

-/

universe w w₁ w₂₀ w₂₁ v₁ v₂ u

namespace Module

variable {A : Type u} [Ring A] {M₁ : Type v₁} {M₂ : Type v₂}
  [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
  (pres₂ : Presentation.{w₂₀, w₂₁} A M₂) (f : M₁ →ₗ[A] M₂)
  {ι : Type w₁} (g₁ : ι → M₁)

namespace Presentation

structure CokernelData where
  lift (i : ι) : pres₂.G →₀ A
  π_lift (i : ι) : pres₂.π (lift i) = f (g₁ i)

instance nonempty_cokernelData :
    Nonempty (pres₂.CokernelData f g₁) :=
  ⟨_, fun i ↦ (pres₂.surjective_π (f (g₁ i))).choose_spec⟩

@[simps]
def CokernelData.ofSection (s : M₂ → (pres₂.G →₀ A))
    (hs : ∀ (m₂ : M₂), pres₂.π (s m₂) = m₂) :
    pres₂.CokernelData f g₁ where
  lift i := s (f (g₁ i))
  π_lift i := by simp [hs]

variable {g₁ f} (data : pres₂.CokernelData f g₁)

@[simps]
def cokernelRelations : Relations A where
  G := pres₂.G
  R := Sum pres₂.R ι
  relation x := match x with
    | .inl r => pres₂.relation r
    | .inr i => data.lift i

def cokernelSolution :
    (pres₂.cokernelRelations data).Solution (M₂ ⧸ LinearMap.range f) where
  var g := Submodule.mkQ _ (pres₂.var g)
  linearCombination_var_relation := by
    intro x
    erw [← Finsupp.apply_linearCombination]
    obtain (r | i) := x
    · erw [pres₂.linearCombination_var_relation]
      dsimp
    · erw [data.π_lift]
      simp

variable (hg₁ : Submodule.span A (Set.range g₁) = ⊤)

namespace cokernelSolution

def isPresentationCore :
    Relations.Solution.IsPresentationCore.{w}
      (pres₂.cokernelSolution data) := by
  have := hg₁
  sorry

include hg₁ in
lemma isPresentation : (pres₂.cokernelSolution data).IsPresentation :=
  (isPresentationCore pres₂ data hg₁).isPresentation

end cokernelSolution

@[simps!]
def cokernel : Presentation A (M₂ ⧸ LinearMap.range f) :=
  ofIsPresentation (cokernelSolution.isPresentation pres₂ data hg₁)

end Presentation

end Module
