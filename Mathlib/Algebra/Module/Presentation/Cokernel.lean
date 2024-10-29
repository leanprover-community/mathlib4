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

## TODO
* deduce that if we have an exact sequence `M₁ → M₂ → M₃ → 0`,
then we also get a presentation of `M₃`

-/

universe w w₁ w₂₀ w₂₁ v₁ v₂ v₃ u

-- to be moved to Algebra.Exact
section

variable {A : Type u} [Ring A]
variable {M₁ : Type v₁} {M₂ : Type v₂} {M₃ : Type v₃}

variable [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module A M₁] [Module A M₂] [Module A M₃]
  {f : M₁ →ₗ[A] M₂} {g : M₂ →ₗ[A] M₃}

namespace LinearMap

lemma surjective_range_liftQ (h : range f ≤ ker g) (hg : Function.Surjective g) :
    Function.Surjective ((range f).liftQ g h) := by
  intro x₃
  obtain ⟨x₂, rfl⟩ := hg x₃
  exact ⟨Submodule.Quotient.mk x₂, rfl⟩

lemma ker_eq_bot_range_liftQ_iff (h : range f ≤ ker g) :
    ker ((range f).liftQ g h) = ⊥ ↔ ker g = range f := by
  simp only [Submodule.ext_iff, mem_ker, Submodule.mem_bot, mem_range]
  constructor
  · intro hfg x
    simpa using hfg (Submodule.Quotient.mk x)
  · intro hfg x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simpa using hfg x

lemma injective_range_liftQ_of_exact (h : Function.Exact f g) :
    Function.Injective ((range f).liftQ g (by simp only [h.linearMap_ker_eq, le_refl])) := by
  simpa only [← LinearMap.ker_eq_bot, ker_eq_bot_range_liftQ_iff, exact_iff] using h

end LinearMap

namespace LinearEquiv

/-- The linear equivalence `(M₂ ⧸ LinearMap.range f) ≃ₗ[A] M₃` associated to
an exact sequence `M₁ → M₂ → M₃ → 0` of `A`-modules. -/
@[simps! apply]
noncomputable def ofExactOfSurjective (h : Function.Exact f g) (hg : Function.Surjective g) :
    (M₂ ⧸ LinearMap.range f) ≃ₗ[A] M₃ :=
  ofBijective ((LinearMap.range f).liftQ g
    (by simp only [h.linearMap_ker_eq, le_refl]))
      ⟨LinearMap.injective_range_liftQ_of_exact h,
        LinearMap.surjective_range_liftQ _ hg⟩

end LinearEquiv

end

namespace Module

variable {A : Type u} [Ring A] {M₁ : Type v₁} {M₂ : Type v₂} {M₃ : Type v₃}
  [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
  [AddCommGroup M₃] [Module A M₃]

namespace Presentation

section Cokernel

variable (pres₂ : Presentation.{w₂₀, w₂₁} A M₂) (f : M₁ →ₗ[A] M₂)
  {ι : Type w₁} (g₁ : ι → M₁)

/-- Given a linear map `f : M₁ →ₗ[A] M₂`, a presentation of `M₂` and a choice
of generators of `M₁`, this structure specifies a lifting of the image by `f`
of each generator of `M₁` as a linear combination of the generators of `M₂`. -/
structure CokernelData where
  /-- a lifting of `f (g₁ i)` in `pres₂.G →₀ A` -/
  lift (i : ι) : pres₂.G →₀ A
  π_lift (i : ι) : pres₂.π (lift i) = f (g₁ i)

instance nonempty_cokernelData :
    Nonempty (pres₂.CokernelData f g₁) :=
  ⟨_, fun i ↦ (pres₂.surjective_π (f (g₁ i))).choose_spec⟩

/-- Constructor for `Presentation.CokernelData` in case we have a chosen set-theoretic
section of the projection `(pres₂.G →₀ A) → M₂`. -/
@[simps]
def CokernelData.ofSection (s : M₂ → (pres₂.G →₀ A))
    (hs : ∀ (m₂ : M₂), pres₂.π (s m₂) = m₂) :
    pres₂.CokernelData f g₁ where
  lift i := s (f (g₁ i))
  π_lift i := by simp [hs]

variable {g₁ f} (data : pres₂.CokernelData f g₁)

/-- The shape of the presentation by generators and relations of the cokernel
of `f : M₁ →ₗ[A] M₂`. It consists of a generator for each generator of `M₂`, and
there are two types of relations: one for each relation in the presentation in `M₂`,
and for each generator of `M₁`. -/
@[simps]
def cokernelRelations : Relations A where
  G := pres₂.G
  R := Sum pres₂.R ι
  relation x := match x with
    | .inl r => pres₂.relation r
    | .inr i => data.lift i

/-- The obvious solution in `M₂ ⧸ LinearMap.range f` to the equations in
`pres₂.cokernelRelations data`. -/
@[simps]
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

/-- The cokernel can be defined by generators and relations. -/
noncomputable def isPresentationCore :
    Relations.Solution.IsPresentationCore.{w}
      (pres₂.cokernelSolution data) where
  desc s := (LinearMap.range f).liftQ (pres₂.desc
    { var := s.var
      linearCombination_var_relation :=
        fun r ↦ s.linearCombination_var_relation (.inl r) }) (by
          rw [LinearMap.range_eq_map, ← hg₁, Submodule.map_span, Submodule.span_le,
            Set.image_subset_iff]
          rintro _ ⟨i, rfl⟩
          rw [Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_ker, ← data.π_lift,
            Relations.Solution.IsPresentation.π_desc_apply]
          exact s.linearCombination_var_relation (.inr i))
  postcomp_desc s := by aesop
  postcomp_injective h := by
    ext : 1
    apply pres₂.toIsPresentation.postcomp_injective
    ext g
    exact Relations.Solution.congr_var h g

include hg₁ in
lemma isPresentation : (pres₂.cokernelSolution data).IsPresentation :=
  (isPresentationCore pres₂ data hg₁).isPresentation

end cokernelSolution

/-- The presentation of the cokernel of a linear map `f : M₁ →ₗ[A] M₂` that is obtained
from a presentation `pres₂` of `M₂`, a choice of generators `g₁ : ι → M₁` of `M₁`,
and an additional `data : pres₂.CokernelData f g₁`. -/
@[simps!]
def cokernel : Presentation A (M₂ ⧸ LinearMap.range f) :=
  ofIsPresentation (cokernelSolution.isPresentation pres₂ data hg₁)

end Cokernel

section OfExact

variable {f : M₁ →ₗ[A] M₂} {g : M₂ →ₗ[A] M₃}
  (pres₂ : Presentation.{w₂₀, w₂₁} A M₂)
  {ι : Type w₁} {g₁ : ι → M₁}
  (data : pres₂.CokernelData f g₁)
  (hfg : Function.Exact f g) (hg : Function.Surjective g)
  (hg₁ : Submodule.span A (Set.range g₁) = ⊤)

/-- Given an exact sequence of `A`-modules `M₁ → M₂ → M₃ → 0`, this is the presentation
of `M₃` that is obtained from a presentation `pres₂` of `M₂`, a choice of generators
`g₁ : ι → M₁` of `M₁`, and an additional data in a `Presentation.CokernelData` structure. -/
noncomputable def ofExact : Presentation A M₃ :=
  (pres₂.cokernel data hg₁).ofLinearEquiv
    (LinearEquiv.ofExactOfSurjective hfg hg)

end OfExact

end Presentation

end Module
