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

Fix `𝕜` a complete `NontriviallyNormedField`, and `E`, `F` be two Hausdorff topological vector
spaces over `𝕜`.

In this file, we define what it means for a continuous linear map `T : E →L[𝕜] F` to be
a **Fredholm operator**.
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

/-- A continuous linear map `u : E →L[𝕜] F` is a **Fredholm operator** if it is strict,
its range is closed and has finite codimension, and its kernel is (topologically) complemented and
has finite dimension.

See also `isFredholm_tfae` for other equivalent characterizations.
We will also prove later (not in Mathlib yet) that for maps between Banach (or even Fréchet)
spaces, all the conditions follow from the kernel and cokernel having finite dimension.
-/
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

variable (𝕜 E) in
/-- A **Fredholm decomposition** of a topological vector space `E` is the data of two subspaces
`X₀` and `X₁` which are topological complements, and where `X₀` is finite dimensional.

Note that we purposefully use the index `₀` for the "inessential" (i.e finite dimensional)
part of the decomposition. -/
structure FredholmDecomposition where
  X₀ : Submodule 𝕜 E
  X₁ : Submodule 𝕜 E
  isTopCompl : IsTopCompl X₁ X₀
  finite_X₀ : FiniteDimensional 𝕜 X₀

/-- Given a fredhom decomposition `dec` of the space `E`, `dec.proj` is the (continuous linear)
projection onto the "essential part" `dec.X₁` along the "inessential part" `dec.X₀`.
This is a Fredholm operator. -/
abbrev FredholmDecomposition.proj (dec : FredholmDecomposition 𝕜 E) :
    E →L[𝕜] dec.X₁ := dec.X₁.projectionOntoL dec.X₀ dec.isTopCompl

/-- Let `u : E →L[𝕜] F` be a continuous linear map. A **Fredholm package** for `u` is the data of
Fredholm decompositions `dec_dom` and `dec_codom` of `E` and `F` respectively, together with
a continuous linear equivalence `equiv : dec_dom.X₁ ≃ₗ[𝕜] dec_codom.X₁` between the "essential"
(i.e finite codimension) parts of these decompositions, such that `u` equals the composition
`u = dec_codom.X₁.subtypeL ∘L equiv ∘L dec_dom.proj`. In other words, in these
"essential ⊕ inessential" decompositions, the matrix of `u` is
```
equiv 0
0     0
```

We will show in `isFredholm_tfae` that an operator is Fredholm if and only if it admits
a Fredholm package. In practice, the condition that `u` is Fredholm is always easier to
prove, so if you need a Fredholm package you should probably get it from
`IsFredholm.nonempty_fredholmPackage` or `IsFredholm.fredholmPackage`. -/
structure FredholmPackage (u : E →L[𝕜] F) where
  dec_dom : FredholmDecomposition 𝕜 E
  dec_codom : FredholmDecomposition 𝕜 F
  equiv : dec_dom.X₁ ≃L[𝕜] dec_codom.X₁
  eq_equiv : u = dec_codom.X₁.subtypeL ∘L equiv ∘L dec_dom.proj

lemma FredholmPackage.ker_eq {u : E →L[𝕜] F} (pkg : FredholmPackage u) :
    u.ker = pkg.dec_dom.X₀ := by simp [pkg.eq_equiv, ker_comp]

lemma FredholmPackage.range_eq {u : E →L[𝕜] F} (pkg : FredholmPackage u) :
    u.range = pkg.dec_codom.X₁ := by
  simp [pkg.eq_equiv, range_comp]

/-- The data of a Fredholm package for `u` determines a canonical quasi-inverse of `u`. -/
def FredholmPackage.quasiInverse {u : E →L[𝕜] F} (pkg : FredholmPackage u) :
    F →L[𝕜] E :=
  pkg.dec_dom.X₁.subtypeL ∘L pkg.equiv.symm ∘L pkg.dec_codom.proj

/-- The data of a Fredholm package for `u` determines a canonical quasi-inverse of `u`. -/
lemma FredholmPackage.isQuasiInverse {u : E →L[𝕜] F} (pkg : FredholmPackage u) :
    u.IsQuasiInverse pkg.quasiInverse := by
  nth_rw 1 [pkg.eq_equiv, quasiInverse]
  have hdom : IsQuasiInverse pkg.dec_dom.X₁.subtype pkg.dec_dom.proj :=
    have := pkg.dec_dom.finite_X₀
    isQuasiInverse_subtype_projectionOnto _
  have hcodom : IsQuasiInverse pkg.dec_codom.X₁.subtype pkg.dec_codom.proj :=
    have := pkg.dec_codom.finite_X₀
    isQuasiInverse_subtype_projectionOnto _
  refine .of_comp_left hcodom.symm <| .of_comp_right hdom ?_
  simp_rw [FredholmDecomposition.proj, toLinearMap_comp, toLinearMap_subtypeL,
    toLinearMap_projectionOntoL, LinearMap.comp_assoc, projectionOnto_comp_subtype,
    LinearMap.comp_id, ← LinearMap.comp_assoc, projectionOnto_comp_subtype, LinearMap.id_comp]
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
`IsFredholm.of_restrict` (not in Mathlib yet). -/
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
/-- Let `u : E →L[𝕜] F` be a Fredholm operator. Given `dom₁` (resp. `codom₀`) be an arbitrary
topological complement of `u.ker` (resp. `u.range`), we get a `FredholmPackage` for `u`
by considering the decompositions `E = dom₁ ⊕ u.ker`, `F = u.range ⊕ codom₀`, and the isomorphism
`dom₁ ≃L[𝕜] u.range` induced by `u`.

If you need control over the decompositions, this is the primary way to get a `FredholmPackage`.
Otherwise, see `IsFredholm.nonempty_fredholmPackage`. -/
def IsFredholm.fredholmPackage {u : E →L[𝕜] F}
    (u_fred : IsFredholm u) {dom₁ : Submodule 𝕜 E} {codom₀ : Submodule 𝕜 F}
    (h_dom : IsTopCompl u.ker dom₁) (h_codom : IsTopCompl u.range codom₀) :
    FredholmPackage u where
  dec_dom := {
    X₀ := u.ker
    X₁ := dom₁
    isTopCompl := h_dom.symm
    finite_X₀ := u_fred.finite_ker }
  dec_codom := {
    X₀ := codom₀
    X₁ := u.range
    isTopCompl := h_codom
    finite_X₀ := .of_fg <| u_fred.finite_coker.fg_of_isCompl h_codom.isCompl  }
  equiv :=
    letI Φ : dom₁ ≃L[𝕜] E ⧸ u.ker := u.ker.quotientEquivOfIsTopCompl dom₁ h_dom |>.symm
    letI Ψ : (E ⧸ u.ker) ≃L[𝕜] u.range := .quotKerEquivRange u.toLinearMap u_fred.isStrictMap
    Φ.trans Ψ
  eq_equiv := by
    refine LinearMap.ext_on_codisjoint h_dom.isCompl.codisjoint ?_ ?_
    · intro x (hx : u x = 0)
      simp [hx, projection_apply_of_mem_right]
    · intro x (hx : x ∈ dom₁)
      simp [hx, projection_apply_of_mem_left, ContinuousLinearEquiv.quotKerEquivRange]

omit [ContinuousSMul 𝕜 E] in
/-- Every Fredholm operator admits a `FredholmPackage`.

This is the primary way to get a `FredholmPackage` if you don't need control of the decompositions.
If you do, see `IsFredholm.fredholmPackage`. -/
theorem IsFredholm.nonempty_fredholmPackage {u : E →L[𝕜] F}
    (u_fred : IsFredholm u) : Nonempty (FredholmPackage u) := by
  obtain ⟨codom₂, h_codom⟩ := u_fred.closedComplemented_range.exists_isTopCompl
  obtain ⟨dom₁, h_dom⟩ := u_fred.closedComplemented_ker.exists_isTopCompl
  exact ⟨u_fred.fredholmPackage h_dom h_codom⟩

variable [T2Space E] [T2Space F]

theorem isFredholm_tfae (u : E →L[𝕜] F) : List.TFAE
    [
      IsFredholm u,
      ∃ v : F →L[𝕜] E, u.IsQuasiInverse v,
      ∃ (E₁ : Submodule 𝕜 E) (F₁ : Submodule 𝕜 F),
        IsClosed (E₁ : Set E) ∧ IsClosed (F₁ : Set F) ∧
        E₁.CoFG ∧ F₁.CoFG ∧
        ∃ h : MapsTo u E₁ F₁, (u.restrict h).IsInvertible,
      Nonempty (FredholmPackage u)
    ] := by
  tfae_have 1 → 4 := IsFredholm.nonempty_fredholmPackage
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

theorem FredholmPackage.isFredholm {u : E →L[𝕜] F} (pkg : FredholmPackage u) :
    IsFredholm u :=
  isFredholm_tfae u |>.out 3 0 |>.mp (Nonempty.intro pkg)

end DefTFAE

end ContinuousLinearMap
end TVS

end
