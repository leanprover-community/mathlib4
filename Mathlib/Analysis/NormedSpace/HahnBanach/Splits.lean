/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Analysis.Normed.Module.Complemented
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-! # Linear maps which split

This file defines split continuous linear maps: an injective continuous linear map splits if and
only if it has closed range and its image has a closed complement. We prove that
* the product of split maps is split,
* (in progress/under discussion) the composition of split maps between Banach spaces is split,
as well as various weakenings: for instance, an injective linear map on a finite-dimensional space
always splits.

This concept is used to give a conceptual definition of immersions between Banach manifolds.

-/

public section

open Function Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E E' F F' G : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

noncomputable section

lemma Submodule.map_add {f : E →L[𝕜] F} {p q : Submodule 𝕜 E} :
    p.map (f : E →ₛₗ[.id _] F) + q.map (f : E →ₛₗ[.id _] F) = (p + q).map (f : E →ₛₗ[.id _] F) := by
  ext x
  simp

section

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

lemma Submodule.sum_assoc {p q r : Submodule R M} : p + (q + r) = (p + q) + r := by
  ext x
  simp only [add_eq_sup, mem_sup, exists_exists_and_exists_and_eq_and]
  exact ⟨fun ⟨y, hy, a, ha, b, hb, hyab⟩ ↦ ⟨y, hy, a, ha, b, hb, by rw [← hyab]; module⟩,
    fun ⟨a, ha, b, hb, z, hz, h⟩ ↦ ⟨a, ha, b, hb, z, hz, by rw [← h]; module⟩⟩

variable {R M M' : Type*} [Ring R] [TopologicalSpace M] [TopologicalSpace M']
    [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R M']
lemma Submodule.ClosedComplemented.prod {p : Submodule R M} {q : Submodule R M'}
    (hp : p.ClosedComplemented) (hq : q.ClosedComplemented) : (p.prod q).ClosedComplemented := by
  sorry

end

/-- A continuous linear map `f : E → F` **splits** iff it is injective, has closed range and
its image has a closed complement. -/
protected def ContinuousLinearMap.Splits (f : E →L[𝕜] F) : Prop :=
  Injective f ∧ IsClosed (Set.range f) ∧ Submodule.ClosedComplemented (f.range)

-- XXX: should this be about ContinuousLinearMapClass?
namespace ContinuousLinearMap.Splits

variable {f : E →L[𝕜] F} {g : E' →L[𝕜] F'}

lemma injective (h : f.Splits) : Injective f := h.1

lemma isClosed_range (h : f.Splits) : IsClosed (Set.range f) := h.2.1

lemma closedComplemented (h : f.Splits) : Submodule.ClosedComplemented (f.range) :=
  h.2.2

/-- Choice of a closed complement of `range f` -/
def complement (h : f.Splits) : Submodule 𝕜 F :=
  Classical.choose h.closedComplemented.exists_isClosed_isCompl

lemma complement_isClosed (h : f.Splits) : IsClosed (X := F) h.complement :=
  (Classical.choose_spec h.closedComplemented.exists_isClosed_isCompl).1

lemma complement_isCompl (h : f.Splits) : IsCompl f.range h.complement :=
  (Classical.choose_spec h.closedComplemented.exists_isClosed_isCompl).2

lemma congr {g : E →L[𝕜] F} (hf : f.Splits) (hfg : g = f) : g.Splits :=
  hfg ▸ hf

/-- A continuous linear equivalence splits. -/
lemma _root_.ContinuousLinearEquiv.splits (f : E ≃L[𝕜] F) : f.toContinuousLinearMap.Splits := by
  refine ⟨?_, ?_, ?_⟩
  · rw [f.coe_coe]
    apply EquivLike.injective
  · rw [f.coe_coe, EquivLike.range_eq_univ]
    exact isClosed_univ
  · erw [f.range_eq_top_of_surjective (EquivLike.surjective f)]
    exact Submodule.closedComplemented_top

/-- If `f` and `g` split, then so does `f × g`. -/
lemma prodMap (hf : f.Splits) (hg : g.Splits) : (f.prodMap g).Splits := by
  refine ⟨hf.injective.prodMap hg.injective, ?_, ?_⟩
  · rw [coe_prodMap', range_prodMap]
    exact (hf.isClosed_range).prod hg.isClosed_range
  · simpa using hf.closedComplemented.prod hg.closedComplemented

section

variable [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]

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

omit [CompleteSpace F] [CompleteSpace G] in
lemma disjoint_aux {g : F →L[𝕜] G} {F₁ F₂ : Submodule 𝕜 F} {G' : Submodule 𝕜 G}
    (hF : Disjoint F₁ F₂) (hG' : Disjoint g.range G') (hg : Injective g) :
    Disjoint (F₁.map (g : F →ₛₗ[.id _] G)) (F₂.map (g : F →ₛₗ[.id _] G) + G') := by
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
    simp only [map_sub, coe_coe]
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

-- I **think** this argument works over any field: if not, will need to adapt downstream files!
/-- The composition of split continuous linear maps between real or complex Banach spaces splits. -/
lemma comp {g : F →L[𝕜] G} (hg : g.Splits) (hf : f.Splits) : (g.comp f).Splits := by
  have h : IsClosed (range (g ∘ f)) := by
    rw [range_comp]
    apply hg.isClosedMap _ hf.isClosed_range
  refine ⟨hg.injective.comp hf.injective, h, ?_⟩
  · rw [Submodule.closedComplemented_iff_isClosed_exists_isClosed_isCompl]
    let F' := hf.complement
    refine ⟨h, (F'.map (g : F →ₛₗ[.id _] G)) + hg.complement, ?_, ?_⟩
    · have : IsClosed (X := G) (F'.map (g : F →ₛₗ[.id _] G)) :=
        hg.isClosedMap _ hf.complement_isClosed
      have : IsClosed (X := G) hg.complement := hg.complement_isClosed
      -- In general, the sum of closed subspaces need not be closed.
      -- In this case, however, this is true as F'.map G is a closed subspace of range g,
      -- and range g + hg.complement = G' is closed.
      -- TODO: what's the best proof to formalise?

      -- Here is an outline of a proof using sequential closedness.
      rw [← isSeqClosed_iff_isClosed]
      -- Let (u_n) be a converging sequence in g(F') + G'.
      intro u u₀ hu hconv
      simp_rw [Submodule.add_eq_sup, SetLike.mem_coe, Submodule.mem_sup] at hu
      -- Write u_n = x_n + y_n, for x_n in g(F') and y_n in G'.
      let x : ℕ → Submodule.map (g : F →ₛₗ[.id _] G) F' := by
        intro n
        choose y hy z hz hyz using hu n
        exact ⟨y, hy⟩
      let y : ℕ → hg.complement := by
        intro n
        choose y hy z hz hyz using hu n
        exact ⟨z, hz⟩
      -- By construction, u_n = x_n + y_n.
      have (n : ℕ) : u n = x n + y n := by
        simp [x, y]
        sorry -- need more API lemmas
      -- x equals the projection into g(F'); y equals the projection onto hg.complement.
      -- Since the coordinate projections are continuous, x and y are both convergent sequences.

      -- Since g is anti-Lipschitz, the sequence of preimages of x_n is also converging.
      -- These preimages belong to F', which is closed, hence the limit also lies in F'.

      -- Thus, by continuity, x_n converges to some point in g(F').
      -- By linearity, u_n converges to a point in g(F')+G', qed.
      sorry
    · have : LinearMap.range (g.comp f : E →ₛₗ[.id _] G) = f.range.map (g : F →ₛₗ[.id _] G) := by
        aesop
      -- some lemmas which could be useful for a manual proof:
      -- rw [LinearMap.range_comp]; rw [LinearMap.range_eq_map]; rw [Submodule.map_comp f g ⊤]
      -- rw [← LinearMap.range_eq_map f]
      constructor
      · exact this ▸ disjoint_aux hf.complement_isCompl.1 hg.complement_isCompl.1 hg.injective
      · rw [codisjoint_iff, this, ← Submodule.add_eq_sup, Submodule.sum_assoc, Submodule.map_add]
        rw [LinearMap.range_eq_map]
        trans Submodule.map (g : F →ₛₗ[.id _] G) ⊤ + hg.complement
        · congr
          rw [Submodule.add_eq_sup, ← codisjoint_iff]
          simpa using hf.complement_isCompl.2
        · rw [Submodule.add_eq_sup, ← codisjoint_iff, ← LinearMap.range_eq_map]
          exact hg.complement_isCompl.2

lemma compCLE_left [CompleteSpace F'] {f₀ : F' ≃L[𝕜] E} (hf : f.Splits) :
    (f.comp f₀.toContinuousLinearMap).Splits :=
  hf.comp f₀.splits

lemma compCLE_right [CompleteSpace F'] {g : F ≃L[𝕜] F'} (hf : f.Splits) :
    (g.toContinuousLinearMap.comp f).Splits :=
  g.splits.comp hf

end

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {E E' F F' G : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : E →L[𝕜] F} {g : E' →L[𝕜] F'}

/-- If `f : E → F` is injective and `F` is finite-dimensional, then `f` splits. -/
lemma of_injective_of_finiteDimensional [FiniteDimensional 𝕜 F] (hf : Injective f) : f.Splits := by
  have aux : IsClosed (X := F) f.range := Submodule.closed_of_finiteDimensional _
  exact ⟨hf, aux, Submodule.ClosedComplemented.of_finiteDimensional f.range⟩

/-- If `f : E → F` is injective and `E` is finite-dimensional, then `f` splits. -/
lemma of_injective_of_finiteDimensional_of_completeSpace
    [FiniteDimensional 𝕜 E] (hf : Injective f) : f.Splits := by
  have aux : IsClosed (X := F) f.range := Submodule.closed_of_finiteDimensional _
  exact ⟨hf, aux, Submodule.ClosedComplemented.of_finiteDimensional f.range⟩

-- FUTURE (once mathlib has a notion of Fredholm operators):
-- If `f : E → F` is injective, `E` and `F` are Banach and `f` is Fredholm, then `f` splits.

end RCLike

end ContinuousLinearMap.Splits

end
