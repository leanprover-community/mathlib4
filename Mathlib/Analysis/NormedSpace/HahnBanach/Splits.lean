/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Analysis.Normed.Module.Complemented
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension

/-! # Linear maps which split

This file defines split continuous linear maps: an injective continuous linear map splits if and
only if it has closed range and its image has a closed complement. We prove that
* the product of split maps is split,
* (in progress/under discussion) the composition of split maps between Banach spaces is split,
as well as various weakenings: for instance, an injective linear map on a finite-dimensional space
always splits.

This concept is used to give a conceptual definition of immersions between Banach manifolds.

-/

open Function Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E E' F F' G : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

noncomputable section

namespace LinearMap

lemma range_prodMap {f : E →L[𝕜] F} {g : E' →L[𝕜] F'} :
    range (f.prodMap g) = (range f).prod (range g) := by
  ext x
  rw [Submodule.mem_prod]
  simp_rw [LinearMap.mem_range]
  constructor <;> intro h
  · have : x ∈ Set.range (Prod.map f g) := h
    rcases h with ⟨⟨y1, y₂⟩, hy⟩
    all_goals simp_all
  · choose y₁ hy₁ using h.1
    choose y₂ hy₂ using h.2
    use (y₁, y₂), by simp [hy₁, hy₂]

end LinearMap

/-- A continuous linear map `f : E → F` **splits** iff it is injective, has closed range and
its image has a closed complement. -/
protected def ContinuousLinearMap.Splits (f : E →L[𝕜] F) : Prop :=
  Injective f ∧ IsClosed (Set.range f) ∧ Submodule.ClosedComplemented (LinearMap.range f)

-- XXX: should this be about ContinuousLinearMapClass?
namespace ContinuousLinearMap.Splits

variable {f : E →L[𝕜] F} {g : E' →L[𝕜] F'}

lemma injective (h : f.Splits) : Injective f := h.1

lemma isClosed_range (h : f.Splits) : IsClosed (Set.range f) := h.2.1

lemma closedComplemented (h : f.Splits) : Submodule.ClosedComplemented (LinearMap.range f) :=
  h.2.2

/-- Choice of a closed complement of `range f` -/
def complement (h : f.Splits) : Submodule 𝕜 F :=
  Classical.choose h.closedComplemented.exists_isClosed_isCompl

lemma complement_isClosed (h : f.Splits) : IsClosed (X := F) h.complement :=
  (Classical.choose_spec h.closedComplemented.exists_isClosed_isCompl).1

lemma complement_isCompl (h : f.Splits) : IsCompl (LinearMap.range f) h.complement :=
  (Classical.choose_spec h.closedComplemented.exists_isClosed_isCompl).2

/-- A continuous linear equivalence splits. -/
lemma _root_.ContinuousLinearEquiv.splits (f : E ≃L[𝕜] F) : f.toContinuousLinearMap.Splits := by
  refine ⟨?_, ?_, ?_⟩
  · rw [f.coe_coe]
    apply EquivLike.injective
  · rw [f.coe_coe, EquivLike.range_eq_univ]
    exact isClosed_univ
  · erw [LinearMap.range_eq_top_of_surjective f (EquivLike.surjective f)]
    exact Submodule.closedComplemented_top

/-- If `f` and `g` split, then so does `f × g`. -/
lemma prodMap (hf : f.Splits) (hg : g.Splits) : (f.prodMap g).Splits := by
  refine ⟨hf.injective.prodMap hg.injective, ?_, ?_⟩
  · rw [coe_prodMap', range_prod_map]
    exact (hf.isClosed_range).prod hg.isClosed_range
  · rw [LinearMap.range_prodMap]
    sorry -- also missing: Submodule.ClosedComplemented.prod

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {E E' F F' G : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] {f : E →L[𝕜] F} {g : E' →L[𝕜] F'}

/-- If `f : E → F` splits and `E`, `F` are real or complex Banach spaces, `f` is anti-Lipschitz.
This result is unseful to prove that the composition of split maps is a split map. -/
lemma antilipschitz_aux (hf : f.Splits) : ∃ K, AntilipschitzWith K f :=
  ContinuousLinearMap.antilipschitz_of_injective_of_isClosed_range f hf.injective hf.isClosed_range

/-- Some anti-Lipschitz constant for `f` -/
def antilipschitzConstant (hf : f.Splits) := Classical.choose hf.antilipschitz_aux

lemma antilipschitzWith (hf : f.Splits) : AntilipschitzWith hf.antilipschitzConstant f :=
  Classical.choose_spec hf.antilipschitz_aux

lemma isClosedMap (hf : f.Splits) : IsClosedMap f :=
  (hf.antilipschitzWith.isClosedEmbedding f.uniformContinuous).isClosedMap

lemma disjoint_aux  {g : F →L[𝕜] G} {F₁ F₂ : Submodule 𝕜 F} {G' : Submodule 𝕜 G}
    (hF : Disjoint F₁ F₂) (hG' : Disjoint (LinearMap.range g) G') (hg : Injective g) :
    Disjoint (Submodule.map g F₁) (Submodule.map g F₂ + G') := by
  rw [Submodule.disjoint_def] at hF hG' ⊢
  intro x h1 h2
  -- Write x = g (f x₀)
  choose x₀ hx₀ hgx₀ using h1
  -- Write x = y + z, for y = g y₀ ∈ g(F') and z ∈ h.complement.
  rw [Submodule.add_eq_sup, Submodule.mem_sup] at h2
  choose y hy aux using h2
  choose y₀ hy₀ hgy₀ using hy
  choose z hz hxyz using aux
  -- Since z in range g and hg.complement is complementary to range g, z = 0 follows.
  -- These lines are too tedious.
  have : z = x - y := by rw [← hxyz]; module
  have : z ∈ range g := by
    rw [this, ← hgx₀, ← hgy₀, ← map_sub]
    use x₀ - y₀ -- Can or should this be a simproc?
  have : z = 0 := hG' z this hz
  -- g y₀ = y = x = g x₀, thus x₀ = y₀.
  have hxy : x = y := by rw [← add_zero y, ← this, hxyz]
  have aux := calc g y₀
    _ = y := hgy₀
    _ = x := hxy.symm
    _ = g x₀ := hgx₀.symm
  -- Now, y₀ ∈ range f and y₀ ∈ F', hence y₀ = 0.
  have : y₀ = 0 := hF y₀ ((hg aux) ▸ hx₀) hy₀
  simp [hxy, ← hgy₀, this]

/-- The composition of split continuous linear maps between real or complex Banach spaces splits. -/
lemma comp {g : F →L[𝕜] G} (hf : f.Splits) (hg : g.Splits) : (g.comp f).Splits := by
  have h : IsClosed (range (g ∘ f)) := by
    rw [range_comp]
    apply hg.isClosedMap _ hf.isClosed_range
  refine ⟨hg.injective.comp hf.injective, h, ?_⟩
  · rw [Submodule.closedComplemented_iff_isClosed_exists_isClosed_isCompl]
    let F' := hf.complement
    refine ⟨h, (F'.map g) + hg.complement, ?_, ?_⟩
    · have : IsClosed (X := G) (F'.map g) := hg.isClosedMap _ hf.complement_isClosed
      have : IsClosed (X := G) hg.complement := hg.complement_isClosed
      -- In general, the sum of closed subspaces need not be closed.
      -- In this case, however, this is true (as F'.map G is a closed subspace of range g,
      -- and range g + hg.complement = G' is closed.
      -- TODO: think about the best proof for formalising.
      sorry
    · constructor
      · have : LinearMap.range (g.comp f) = Submodule.map g (LinearMap.range f) := by aesop
        --rw [LinearMap.range_comp]
        -- rw [LinearMap.range_eq_map]
        -- rw [Submodule.map_comp f g ⊤]
        --rw [← LinearMap.range_eq_map f]
        rw [this]
        exact disjoint_aux hf.complement_isCompl.1 hg.complement_isCompl.1 hg.injective
      · -- rw [Submodule.codisjoint_iff]
        intro h hg hf' s _hx -- they span...
        sorry

lemma compCLE_left [CompleteSpace F'] {f₀ : F' ≃L[𝕜] E} (hf : f.Splits) :
    (f.comp f₀.toContinuousLinearMap).Splits :=
  f₀.splits.comp hf

lemma compCLE_right [CompleteSpace F'] {g : F ≃L[𝕜] F'} (hf : f.Splits) :
    (g.toContinuousLinearMap.comp f).Splits :=
  hf.comp g.splits

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]

/-- If `f : E → F` is injective and `F` is finite-dimensional, then `f` splits. -/
lemma of_injective_of_finiteDimensional [FiniteDimensional 𝕜 F] (hf : Injective f) : f.Splits := by
  have aux : IsClosed (X := F) (LinearMap.range f) := Submodule.closed_of_finiteDimensional _
  exact ⟨hf, aux, Submodule.ClosedComplemented.of_finiteDimensional (LinearMap.range f)⟩

/-- If `f : E → F` is injective and `E` is finite-dimensional, then `f` splits. -/
lemma of_injective_of_finiteDimensional_of_completeSpace
    [FiniteDimensional 𝕜 E] (hf : Injective f) : f.Splits := by
  have aux : IsClosed (X := F) (LinearMap.range f) := Submodule.closed_of_finiteDimensional _
  exact ⟨hf, aux, Submodule.ClosedComplemented.of_finiteDimensional (LinearMap.range f)⟩

-- If `f : E → F` is injective, `E` and `F` are Banach and `f` is Fredholm, then `f` splits.

end RCLike

end ContinuousLinearMap.Splits

end
