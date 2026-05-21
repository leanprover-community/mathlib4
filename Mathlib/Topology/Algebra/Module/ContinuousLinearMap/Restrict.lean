/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Restrictions of continuous linear maps to submodules

In this file, we collect the various operations of restrictions of `ContinuousLinearMap`s
to subspaces of the domain/codomain.

## Main definitions

* `Submodule.subtypeL S` is the inclusion map `S →L[R] M` when `S : Submodule R M`.
  In other words, it is `Submodule.subtype S` bundled as a `ContinuousLinearMap`.
* `ContinuousLinearMap.domRestrict f S` is the map `S →SL[σ] N` obtained by restricting
  `f : M →SL[σ] N` to a subspace `S` of the *domain*.
  This is the continuous version of `LinearMap.domRestrict`.
* `ContinuousLinearMap.codRestrict f S h` is the map `M →SL[σ] S` obtained by co-restricting
  `f : M →SL[σ] N` to a subspace `S` of the *codomain*; this requires a proof `h` that all values
  of `f` indeed belong to `S`.
  This is the continuous version of `LinearMap.codRestrict`.
* `ContinuousLinearMap.rangeRestrict f` is an abbreviation for
  `f.codRestrict f.range ⋯ : M →SL[σ] f.range`.
  This is the continuous version of `LinearMap.rangeRestrict`.
* `ContinuousLinearMap.restrict f h` is the map `S →SL[σ] T` obtained by restricting from
  `f : M →SL[σ] N` and a proof `h` that `f` maps `S` inside `T`.
  This is the continuous version of `LinearMap.restrict`.
-/

@[expose] public section

open LinearMap (ker range)

namespace Submodule

section Semiring

variable {R : Type*} [Semiring R] {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M]

/-- `Submodule.subtype` as a `ContinuousLinearMap`. -/
def subtypeL (p : Submodule R M) : p →L[R] M where
  toLinearMap := p.subtype

@[simp, norm_cast]
theorem toLinearMap_subtypeL (p : Submodule R M) : (p.subtypeL : p →ₗ[R] M) = p.subtype := rfl

@[simp]
theorem coe_subtypeL (p : Submodule R M) : ⇑p.subtypeL = p.subtype := rfl

@[deprecated (since := "2026-05-06")]
alias coe_subtypeL' := coe_subtypeL

theorem subtypeL_apply (p : Submodule R M) (x : p) : p.subtypeL x = x := by simp

@[deprecated range_subtype (since := "2026-05-06")]
theorem range_subtypeL (p : Submodule R M) : (p.subtypeL : p →ₗ[R] M).range = p :=
  Submodule.range_subtype _

@[deprecated ker_subtype (since := "2026-05-06")]
theorem ker_subtypeL (p : Submodule R M) : (p.subtypeL : p →ₗ[R] M).ker = ⊥ :=
  Submodule.ker_subtype _

end Semiring

end Submodule

namespace ContinuousLinearMap

section Restrict

variable {R₁ R₂ R₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃]
  {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
  {M₁ M₂ M₃ : Type*}
  [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R₁ M₁]
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₂ M₂]
  [TopologicalSpace M₃] [AddCommMonoid M₃] [Module R₃ M₃]

/-- The restriction of a linear map `f : M → M₂` to a submodule `p ⊆ M` gives a linear map
`p → M₂`. -/
@[simps!]
def domRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₁ M₁) : p →SL[σ₁₂] M₂ :=
  f ∘SL p.subtypeL

@[simp]
theorem toLinearMap_domRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₁ M₁) :
    (f.domRestrict p).toLinearMap = f.toLinearMap.domRestrict p :=
  rfl

lemma coe_domRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₁ M₁) :
    ⇑(f.domRestrict p) = Set.restrict p f :=
  rfl

/-- Restrict codomain of a continuous linear map. -/
def codRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
    M₁ →SL[σ₁₂] p where
  cont := f.continuous.subtype_mk _
  toLinearMap := (f : M₁ →ₛₗ[σ₁₂] M₂).codRestrict p h

@[simp, norm_cast]
theorem toLinearMap_codRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
    (f.codRestrict p h).toLinearMap = f.toLinearMap.codRestrict p h :=
  rfl

theorem coe_codRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
    (f.codRestrict p h : M₁ → p) = Set.codRestrict (f : M₁ → M₂) p h :=
  rfl

@[simp]
theorem coe_codRestrict_apply (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) (x) :
    (f.codRestrict p h x : M₂) = f x :=
  rfl

theorem ker_codRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
    ker (f.codRestrict p h : M₁ →ₛₗ[σ₁₂] p) = ker (f : M₁ →ₛₗ[σ₁₂] M₂) :=
  f.toLinearMap.ker_codRestrict p h

@[simp]
theorem domRestrict_comp_codRestrict (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂)
    (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
    g.domRestrict p ∘SL f.codRestrict p h = g ∘SL f :=
  rfl

/-- Restrict the codomain of a continuous linear map `f` to `f.range`. -/
abbrev rangeRestrict [RingHomSurjective σ₁₂] (f : M₁ →SL[σ₁₂] M₂) :=
  f.codRestrict (LinearMap.range (f : M₁ →ₛₗ[σ₁₂] M₂)) (LinearMap.mem_range_self _)

theorem toLinearMap_rangeRestrict [RingHomSurjective σ₁₂] (f : M₁ →SL[σ₁₂] M₂) :
    f.rangeRestrict.toLinearMap = f.toLinearMap.rangeRestrict := by simp

@[simp]
theorem coe_rangeRestrict [RingHomSurjective σ₁₂] (f : M₁ →SL[σ₁₂] M₂) :
    (f.rangeRestrict : M₁ → f.range) = Set.rangeFactorization f := rfl

/-- Restrict codomain of a continuous linear map. -/
def restrict (f : M₁ →SL[σ₁₂] M₂) {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
    (h : ∀ x ∈ p, f x ∈ q) : p →SL[σ₁₂] q :=
  (f.domRestrict p).codRestrict q <| SetLike.forall.2 h

@[simp, norm_cast]
theorem toLinearMap_restrict {f : M₁ →SL[σ₁₂] M₂} {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
    (h : ∀ x ∈ p, f x ∈ q) :
    (f.restrict h).toLinearMap = f.toLinearMap.restrict h :=
  rfl

@[simp]
theorem coe_restrict_apply {f : M₁ →SL[σ₁₂] M₂} {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
    (hf : ∀ x ∈ p, f x ∈ q) (x : p) : ↑(f.restrict hf x) = f x :=
  rfl

theorem restrict_apply {f : M₁ →SL[σ₁₂] M₂} {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
    (hf : ∀ x ∈ p, f x ∈ q) (x : p) : f.restrict hf x = ⟨f x, hf x.1 x.2⟩ :=
  rfl

open Set in
lemma restrict_comp {p : Submodule R₁ M₁} {p₂ : Submodule R₂ M₂} {p₃ : Submodule R₃ M₃}
    {f : M₁ →SL[σ₁₂] M₂} {g : M₂ →SL[σ₂₃] M₃}
    (hf : MapsTo f p p₂) (hg : MapsTo g p₂ p₃) (hfg : MapsTo (g ∘SL f) p p₃ := hg.comp hf) :
    (g ∘SL f).restrict hfg = (g.restrict hg) ∘SL (f.restrict hf) :=
  rfl

theorem subtypeL_comp_restrict {f : M₁ →SL[σ₁₂] M₂} {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
    (hf : ∀ x ∈ p, f x ∈ q) : q.subtypeL ∘SL (f.restrict hf) = f.domRestrict p :=
  rfl

theorem restrict_eq_codRestrict_domRestrict {f : M₁ →SL[σ₁₂] M₂} {p : Submodule R₁ M₁}
    {q : Submodule R₂ M₂} (hf : ∀ x ∈ p, f x ∈ q) :
    f.restrict hf = (f.domRestrict p).codRestrict q fun x => hf x.1 x.2 :=
  rfl

theorem restrict_eq_domRestrict_codRestrict {f : M₁ →SL[σ₁₂] M₂} {p : Submodule R₁ M₁}
    {q : Submodule R₂ M₂} (hf : ∀ x, f x ∈ q) :
    (f.restrict fun x _ => hf x) = (f.codRestrict q hf).domRestrict p :=
  rfl

end Restrict

section

variable {R₁ R₂ R₃ : Type*} [Ring R₁] [Ring R₂]
  {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁]
  {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [AddCommGroup M₁] [Module R₁ M₁]
  [TopologicalSpace M₂] [AddCommGroup M₂] [Module R₂ M₂]

/-- Given a right inverse `f₂ : M₂ →L[R] M₁` to `f₁ : M₁ →L[R] M₂`,
`projKerOfRightInverse f₁ f₂ h` is the projection `M₁ →L[R] LinearMap.ker f₁` along
`LinearMap.range f₂`. -/
def projKerOfRightInverse [IsTopologicalAddGroup M₁] (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M₁)
    (h : Function.RightInverse f₂ f₁) : M₁ →L[R₁] LinearMap.ker (f₁ : M₁ →ₛₗ[σ₁₂] M₂) :=
  (.id R₁ M₁ - f₂ ∘SL f₁).codRestrict (LinearMap.ker f₁.toLinearMap) fun x => by simp [h (f₁ x)]

@[simp]
theorem coe_projKerOfRightInverse_apply [IsTopologicalAddGroup M₁] (f₁ : M₁ →SL[σ₁₂] M₂)
    (f₂ : M₂ →SL[σ₂₁] M₁) (h : Function.RightInverse f₂ f₁) (x : M₁) :
    (f₁.projKerOfRightInverse f₂ h x : M₁) = x - f₂ (f₁ x) :=
  rfl

@[simp]
theorem projKerOfRightInverse_apply_idem [IsTopologicalAddGroup M₁] (f₁ : M₁ →SL[σ₁₂] M₂)
    (f₂ : M₂ →SL[σ₂₁] M₁) (h : Function.RightInverse f₂ f₁) (x : f₁.ker) :
    f₁.projKerOfRightInverse f₂ h x = x := by
  ext1
  simp

@[simp]
theorem projKerOfRightInverse_comp_inv [IsTopologicalAddGroup M₁] (f₁ : M₁ →SL[σ₁₂] M₂)
    (f₂ : M₂ →SL[σ₂₁] M₁) (h : Function.RightInverse f₂ f₁) (y : M₂) :
    f₁.projKerOfRightInverse f₂ h (f₂ y) = 0 :=
  Subtype.ext_iff.2 <| by simp [h y]

end

end ContinuousLinearMap
