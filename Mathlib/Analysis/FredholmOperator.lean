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
open Set (MapsTo)
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

structure IsFredholm (u : E →L[𝕜] F) : Prop where
  isStrictMap : IsStrictMap u
  isClosed_range : IsClosed (u.range : Set F)
  finite_ker : FiniteDimensional 𝕜 u.ker
  finite_coker : u.range.CoFG
  closedComplemented_ker : u.ker.ClosedComplemented

variable [CompleteSpace 𝕜] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] in
lemma IsFredholm.closedComplemented_range {u : E →L[𝕜] F} (u_fred : IsFredholm u) :
    u.range.ClosedComplemented :=
  have := u_fred.finite_coker
  ClosedComplemented.of_finiteDimensional_quotient u_fred.isClosed_range

end IsFredholm

section FredholmDecomposition

variable [ContinuousSub E]

structure FredholmDecomposition (u : E →L[𝕜] F) where
  dom₀ : Submodule 𝕜 E
  dom₁ : Submodule 𝕜 E
  finite_dom₀ : FiniteDimensional 𝕜 dom₀
  isTopCompl_dom : IsTopCompl dom₀ dom₁
  codom₀ : Submodule 𝕜 F
  codom₁ : Submodule 𝕜 F
  finite_codom₀ : FiniteDimensional 𝕜 codom₀
  isTopCompl_codom : IsTopCompl codom₀ codom₁
  equiv : dom₁ ≃L[𝕜] codom₁
  eq_equiv' : u = codom₁.subtypeL ∘L equiv ∘L (dom₁.projectionOntoL dom₀ isTopCompl_dom.symm)

abbrev FredholmDecomposition.domProj {u : E →L[𝕜] F} (dec : FredholmDecomposition u) :
    E →L[𝕜] dec.dom₁ := dec.dom₁.projectionOntoL dec.dom₀ dec.isTopCompl_dom.symm

variable [ContinuousSub F] in
abbrev FredholmDecomposition.codomProj {u : E →L[𝕜] F} (dec : FredholmDecomposition u) :
    F →L[𝕜] dec.codom₁ := dec.codom₁.projectionOntoL dec.codom₀ dec.isTopCompl_codom.symm

lemma FredholmDecomposition.eq_equiv {u : E →L[𝕜] F} (dec : FredholmDecomposition u) :
    u = dec.codom₁.subtypeL ∘L dec.equiv ∘L dec.domProj :=
  dec.eq_equiv'

lemma FredholmDecomposition.ker_eq {u : E →L[𝕜] F} (dec : FredholmDecomposition u) :
    u.ker = dec.dom₀ := by
  simp [dec.eq_equiv, ker_comp]

lemma FredholmDecomposition.range_eq {u : E →L[𝕜] F} (dec : FredholmDecomposition u) :
    u.range = dec.codom₁ := by
  simp [dec.eq_equiv, range_comp]

variable [ContinuousSub F] in
def FredholmDecomposition.quasiInverse {u : E →L[𝕜] F} (dec : FredholmDecomposition u) :
    F →L[𝕜] E :=
  dec.dom₁.subtypeL ∘L dec.equiv.symm ∘L dec.codomProj

variable [ContinuousSub F] in
lemma FredholmDecomposition.isQuasiInverse {u : E →L[𝕜] F} (dec : FredholmDecomposition u) :
    u.IsQuasiInverse dec.quasiInverse := by
  nth_rw 1 [dec.eq_equiv, quasiInverse]
  have hdom : IsQuasiInverse dec.dom₁.subtype dec.domProj :=
    have := dec.finite_dom₀
    isQuasiInverse_subtype_projectionOnto _
  have hcodom : IsQuasiInverse dec.codom₁.subtype dec.codomProj :=
    have := dec.finite_codom₀
    isQuasiInverse_subtype_projectionOnto _
  refine .of_comp_left hcodom.symm <| .of_comp_right hdom ?_
  simp_rw [domProj, codomProj, toLinearMap_comp, toLinearMap_subtypeL, toLinearMap_projectionOntoL,
    LinearMap.comp_assoc, projectionOnto_comp_subtype, LinearMap.comp_id,
    ← LinearMap.comp_assoc, projectionOnto_comp_subtype, LinearMap.id_comp]
  simp [IsQuasiInverse, IsLeftQuasiInverse, IsRightQuasiInverse]

end FredholmDecomposition

section TFAE

end TFAE

variable [T2Space E] [T2Space F] in
private theorem exists_restrict_isInvertible_of_isQuasiInverse {u : E →L[𝕜] F}
    {v : F →L[𝕜] E} (huv : u.IsQuasiInverse v) :
    ∃ (E₁ : Submodule 𝕜 E) (F₁ : Submodule 𝕜 F),
      IsClosed (E₁ : Set E) ∧ IsClosed (F₁ : Set F) ∧
      E₁.CoFG ∧ F₁.CoFG ∧
      ∃ h : MapsTo u E₁ F₁, (u.restrict h).IsInvertible := by
  obtain ⟨huv, hvu⟩ := huv
  rw [IsLeftQuasiInverse, Setoid.comm, equiv_iff_eqLocus_coFG] at huv
  rw [IsRightQuasiInverse, Setoid.comm, equiv_iff_eqLocus_coFG] at hvu
  set E₁ := (ContinuousLinearMap.id 𝕜 E).eqLocus (v ∘L u)
  set F₁ := (ContinuousLinearMap.id 𝕜 F).eqLocus (u ∘L v)
  have u_mapsto : MapsTo u E₁ F₁ := fun x hx ↦ congr(u $hx)
  have v_mapsto : MapsTo v F₁ E₁ := fun x hx ↦ congr(v $hx)
  refine ⟨E₁, F₁, isClosed_eqLocus _ _, isClosed_eqLocus _ _, hvu, huv, u_mapsto, ?_⟩
  refine .of_inverse (g := v.restrict v_mapsto) ?_ ?_
  · ext ⟨x, hx : x = u (v x)⟩; simp [← hx]
  · ext ⟨x, hx : x = v (u x)⟩; simp [← hx]

variable [CompleteSpace 𝕜]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]

variable [T2Space F] in
/-- Assume that `u : E →L[𝕜] F` restricts to an isomorphism between closed finite co-dimension
subspaces `E₁` and `F₁`. Then `u` is Fredholm.

In fact it is enough to assume that the restriction `E₁ →L[𝕜] F₁` is Fredholm, see
`IsFredholm.of_restrict`. -/
theorem IsFredholm.of_isInvertible_restrict {u : E →L[𝕜] F}
    {E₁ : Submodule 𝕜 E} (E₁_closed : IsClosed (E₁ : Set E)) [E₁_coFG : E₁.CoFG]
    {F₁ : Submodule 𝕜 F} (F₁_closed : IsClosed (F₁ : Set F)) [F₁_coFG : F₁.CoFG]
    (h_mapsto : MapsTo u E₁ F₁) (h_inv : (u.restrict h_mapsto).IsInvertible) :
    IsFredholm u := by
  obtain ⟨e, he⟩ := h_inv
  have eqL : u.domRestrict E₁ = F₁.subtypeL ∘L e := congr(F₁.subtypeL ∘L $he).symm
  have eqₗ : u.toLinearMap.domRestrict E₁ = F₁.subtype ∘ₗ e := congr(($eqL).toLinearMap)
  have h : Topology.IsStrictMap u ∧ IsClosed (u.range : Set F) := by
    rw [u.isStrictMap_isClosed_range_iff_restrict E₁ E₁_closed, ← LinearMap.range_domRestrict,
      eqₗ, eqL]
    exact ⟨F₁.isEmbedding_subtype.comp e.isHomeomorph.isEmbedding |>.isStrictMap, by simpa⟩
  have disj : Disjoint E₁ u.ker := by
    rw [disjoint_iff_comap_eq_bot, ← LinearMap.ker_domRestrict, eqₗ,
      LinearMap.ker_comp, ker_subtype, comap_bot, LinearEquiv.ker]
  constructor
  · exact h.1
  · exact h.2
  · rw [← Submodule.fg_iff_finiteDimensional]
    exact E₁_coFG.fg_of_disjoint disj.symm
  · refine F₁_coFG.of_le (le_trans ?_ (u.range_domRestrict_le_range E₁))
    rw [eqₗ, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, range_subtype]
  · exact .of_disjoint_of_finiteDimensional_quotient E₁_closed disj.symm

omit [ContinuousSMul 𝕜 E] in
def IsFredholm.fredholmDecomposition {u : E →L[𝕜] F}
    (u_fred : IsFredholm u) {dom₁ : Submodule 𝕜 E} {codom₀ : Submodule 𝕜 F}
    (h_dom : IsTopCompl u.ker dom₁) (h_codom : IsTopCompl codom₀ u.range) :
    FredholmDecomposition u :=
  haveI u_mapsto : MapsTo u dom₁ u.range := Set.mapsTo_range _ _
  haveI uₗ_mapsto : MapsTo u.toLinearMap dom₁ u.range := u_mapsto
  haveI u_eq_u_restr : u = u.range.subtypeL ∘L u.restrict u_mapsto ∘L
      dom₁.projectionOntoL u.ker h_dom.symm := by
    refine LinearMap.ext_on_codisjoint h_dom.isCompl.codisjoint ?_ ?_
    · intro x (hx : u x = 0)
      simp [hx, projection_apply_of_mem_right]
    · intro x (hx : x ∈ dom₁)
      simp [hx, projection_apply_of_mem_left]
  haveI u_restr_isHomeo : IsHomeomorph (u.restrict u_mapsto) := by
    -- This is a bit messy
    rw [isHomeomorph_iff_isStrictMap_bijective]
    constructor
    · rw [u.range.isEmbedding_subtypeL.isStrictMap_iff, ← coe_comp,
          (isQuotientMap_projectionOntoL h_dom.symm).isStrictMap_iff, ← coe_comp,
          comp_assoc, ← u_eq_u_restr]
      exact u_fred.isStrictMap
    · constructor
      · simpa [← coe_coe, injective_restrict_iff_disjoint] using h_dom.isCompl.symm.disjoint
      · suffices u.range ≤ map u.toLinearMap dom₁ by simpa [← coe_coe, ← LinearMap.range_eq_top]
        simpa [← Submodule.map_top, Submodule.map_le_iff_le_comap, Submodule.comap_map_eq]
          using h_dom.isCompl.symm.sup_eq_top
  { dom₀ := u.ker
    dom₁ := dom₁
    finite_dom₀ := u_fred.finite_ker
    isTopCompl_dom := h_dom
    codom₀ := codom₀
    codom₁ := u.range
    finite_codom₀ := Module.Finite.of_fg <| u_fred.finite_coker.fg_of_isCompl h_codom.isCompl.symm
    isTopCompl_codom := h_codom
    equiv :=
      .ofIsHomeomorph (.ofBijective _ u_restr_isHomeo.bijective) u_restr_isHomeo
    eq_equiv' := u_eq_u_restr }

omit [ContinuousSMul 𝕜 E] in
theorem IsFredholm.nonempty_fredholmDecomposition {u : E →L[𝕜] F}
    (u_fred : IsFredholm u) : Nonempty (FredholmDecomposition u) := by
  obtain ⟨codom₀, h_codom⟩ := u_fred.closedComplemented_range.exists_isTopCompl
  obtain ⟨dom₁, h_dom⟩ := u_fred.closedComplemented_ker.exists_isTopCompl
  exact ⟨u_fred.fredholmDecomposition h_dom h_codom.symm⟩

variable [T2Space E] [T2Space F]

theorem isFredholmTFAE (u : E →L[𝕜] F) : List.TFAE
    [
      IsFredholm u,
      ∃ v : F →L[𝕜] E, u.IsQuasiInverse v,
      ∃ (E₁ : Submodule 𝕜 E) (F₁ : Submodule 𝕜 F),
        IsClosed (E₁ : Set E) ∧ IsClosed (F₁ : Set F) ∧
        E₁.CoFG ∧ F₁.CoFG ∧
        ∃ h : MapsTo u E₁ F₁, (u.restrict h).IsInvertible,
      Nonempty (FredholmDecomposition u)
    ] := by
  tfae_have 1 → 4 := IsFredholm.nonempty_fredholmDecomposition
  tfae_have 4 → 2 := by
    rintro ⟨dec⟩
    exact ⟨dec.quasiInverse, dec.isQuasiInverse⟩
  tfae_have 2 → 3 := by
    rintro ⟨v, huv⟩
    exact exists_restrict_isInvertible_of_isQuasiInverse huv
  tfae_have 3 → 1 := by
    rintro ⟨E₁, F₁, E₁_closed, F₁_closed, E₁_coFG, F₁_coFG, u_mapsto, u_invertible⟩
    exact .of_isInvertible_restrict E₁_closed F₁_closed u_mapsto u_invertible
  tfae_finish

end DefTFAE

end ContinuousLinearMap
end TVS

end
