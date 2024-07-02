/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.NormedSpace.lpSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

#align_import analysis.inner_product_space.l2_space from "leanprover-community/mathlib"@"46b633fd842bef9469441c0209906f6dddd2b4f5"

/-!
# Hilbert sum of a family of inner product spaces

Given a family `(G : ι → Type*) [Π i, InnerProductSpace 𝕜 (G i)]` of inner product spaces, this
file equips `lp G 2` with an inner product space structure, where `lp G 2` consists of those
dependent functions `f : Π i, G i` for which `∑' i, ‖f i‖ ^ 2`, the sum of the norms-squared, is
summable.  This construction is sometimes called the *Hilbert sum* of the family `G`.  By choosing
`G` to be `ι → 𝕜`, the Hilbert space `ℓ²(ι, 𝕜)` may be seen as a special case of this construction.

We also define a *predicate* `IsHilbertSum 𝕜 G V`, where `V : Π i, G i →ₗᵢ[𝕜] E`, expressing that
`V` is an `OrthogonalFamily` and that the associated map `lp G 2 →ₗᵢ[𝕜] E` is surjective.

## Main definitions

* `OrthogonalFamily.linearIsometry`: Given a Hilbert space `E`, a family `G` of inner product
  spaces and a family `V : Π i, G i →ₗᵢ[𝕜] E` of isometric embeddings of the `G i` into `E` with
  mutually-orthogonal images, there is an induced isometric embedding of the Hilbert sum of `G`
  into `E`.

* `IsHilbertSum`: Given a Hilbert space `E`, a family `G` of inner product
  spaces and a family `V : Π i, G i →ₗᵢ[𝕜] E` of isometric embeddings of the `G i` into `E`,
  `IsHilbertSum 𝕜 G V` means that `V` is an `OrthogonalFamily` and that the above
  linear isometry is surjective.

* `IsHilbertSum.linearIsometryEquiv`: If a Hilbert space `E` is a Hilbert sum of the
  inner product spaces `G i` with respect to the family `V : Π i, G i →ₗᵢ[𝕜] E`, then the
  corresponding `OrthogonalFamily.linearIsometry` can be upgraded to a `LinearIsometryEquiv`.

* `HilbertBasis`: We define a *Hilbert basis* of a Hilbert space `E` to be a structure whose single
  field `HilbertBasis.repr` is an isometric isomorphism of `E` with `ℓ²(ι, 𝕜)` (i.e., the Hilbert
  sum of `ι` copies of `𝕜`).  This parallels the definition of `Basis`, in `LinearAlgebra.Basis`,
  as an isomorphism of an `R`-module with `ι →₀ R`.

* `HilbertBasis.instCoeFun`: More conventionally a Hilbert basis is thought of as a family
  `ι → E` of vectors in `E` satisfying certain properties (orthonormality, completeness).  We obtain
  this interpretation of a Hilbert basis `b` by defining `⇑b`, of type `ι → E`, to be the image
  under `b.repr` of `lp.single 2 i (1:𝕜)`.  This parallels the definition `Basis.coeFun` in
  `LinearAlgebra.Basis`.

* `HilbertBasis.mk`: Make a Hilbert basis of `E` from an orthonormal family `v : ι → E` of vectors
  in `E` whose span is dense.  This parallels the definition `Basis.mk` in `LinearAlgebra.Basis`.

* `HilbertBasis.mkOfOrthogonalEqBot`: Make a Hilbert basis of `E` from an orthonormal family
  `v : ι → E` of vectors in `E` whose span has trivial orthogonal complement.

## Main results

* `lp.instInnerProductSpace`: Construction of the inner product space instance on the Hilbert sum
  `lp G 2`. Note that from the file `Analysis.NormedSpace.lpSpace`, the space `lp G 2` already
  held a normed space instance (`lp.normedSpace`), and if each `G i` is a Hilbert space (i.e.,
  complete), then `lp G 2` was already known to be complete (`lp.completeSpace`). So the work
  here is to define the inner product and show it is compatible.

* `OrthogonalFamily.range_linearIsometry`: Given a family `G` of inner product spaces and a family
  `V : Π i, G i →ₗᵢ[𝕜] E` of isometric embeddings of the `G i` into `E` with mutually-orthogonal
  images, the image of the embedding `OrthogonalFamily.linearIsometry` of the Hilbert sum of `G`
  into `E` is the closure of the span of the images of the `G i`.

* `HilbertBasis.repr_apply_apply`: Given a Hilbert basis `b` of `E`, the entry `b.repr x i` of
  `x`'s representation in `ℓ²(ι, 𝕜)` is the inner product `⟪b i, x⟫`.

* `HilbertBasis.hasSum_repr`: Given a Hilbert basis `b` of `E`, a vector `x` in `E` can be
  expressed as the "infinite linear combination" `∑' i, b.repr x i • b i` of the basis vectors
  `b i`, with coefficients given by the entries `b.repr x i` of `x`'s representation in `ℓ²(ι, 𝕜)`.

* `exists_hilbertBasis`: A Hilbert space admits a Hilbert basis.

## Keywords

Hilbert space, Hilbert sum, l2, Hilbert basis, unitary equivalence, isometric isomorphism
-/


open RCLike Submodule Filter

open scoped NNReal ENNReal Classical ComplexConjugate Topology

noncomputable section

variable {ι 𝕜 : Type*} [RCLike 𝕜] {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [cplt : CompleteSpace E]
variable {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace 𝕜 (G i)]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-- `ℓ²(ι, 𝕜)` is the Hilbert space of square-summable functions `ι → 𝕜`, herein implemented
as `lp (fun i : ι => 𝕜) 2`. -/
notation "ℓ²(" ι ", " 𝕜 ")" => lp (fun i : ι => 𝕜) 2

/-! ### Inner product space structure on `lp G 2` -/


namespace lp

theorem summable_inner (f g : lp G 2) : Summable fun i => ⟪f i, g i⟫ := by
  -- Apply the Direct Comparison Test, comparing with ∑' i, ‖f i‖ * ‖g i‖ (summable by Hölder)
  refine .of_norm_bounded (fun i => ‖f i‖ * ‖g i‖) (lp.summable_mul ?_ f g) ?_
  · rw [Real.isConjExponent_iff]; norm_num
  intro i
  -- Then apply Cauchy-Schwarz pointwise
  exact norm_inner_le_norm (𝕜 := 𝕜) _ _
#align lp.summable_inner lp.summable_inner

instance instInnerProductSpace : InnerProductSpace 𝕜 (lp G 2) :=
  { lp.normedAddCommGroup (E := G) (p := 2) with
    inner := fun f g => ∑' i, ⟪f i, g i⟫
    norm_sq_eq_inner := fun f => by
      calc
        ‖f‖ ^ 2 = ‖f‖ ^ (2 : ℝ≥0∞).toReal := by norm_cast
        _ = ∑' i, ‖f i‖ ^ (2 : ℝ≥0∞).toReal := lp.norm_rpow_eq_tsum ?_ f
        _ = ∑' i, ‖f i‖ ^ (2 : ℕ) := by norm_cast
        _ = ∑' i, re ⟪f i, f i⟫ := by
          congr
          funext i
          rw [norm_sq_eq_inner (𝕜 := 𝕜)]
          -- Porting note: `simp` couldn't do this anymore
        _ = re (∑' i, ⟪f i, f i⟫) := (RCLike.reCLM.map_tsum ?_).symm
      · norm_num
      · exact summable_inner f f
    conj_symm := fun f g => by
      calc
        conj _ = conj (∑' i, ⟪g i, f i⟫) := by congr
        _ = ∑' i, conj ⟪g i, f i⟫ := RCLike.conjCLE.map_tsum
        _ = ∑' i, ⟪f i, g i⟫ := by simp only [inner_conj_symm]
        _ = _ := by congr
    add_left := fun f₁ f₂ g => by
      calc
        _ = ∑' i, ⟪(f₁ + f₂) i, g i⟫ := ?_
        _ = ∑' i, (⟪f₁ i, g i⟫ + ⟪f₂ i, g i⟫) := by
          simp only [inner_add_left, Pi.add_apply, coeFn_add]
        _ = (∑' i, ⟪f₁ i, g i⟫) + ∑' i, ⟪f₂ i, g i⟫ := tsum_add ?_ ?_
        _ = _ := by congr
      · congr
      · exact summable_inner f₁ g
      · exact summable_inner f₂ g
    smul_left := fun f g c => by
      calc
        _ = ∑' i, ⟪c • f i, g i⟫ := ?_
        _ = ∑' i, conj c * ⟪f i, g i⟫ := by simp only [inner_smul_left]
        _ = conj c * ∑' i, ⟪f i, g i⟫ := tsum_mul_left
        _ = _ := ?_
      · simp only [coeFn_smul, Pi.smul_apply]
      · congr }

theorem inner_eq_tsum (f g : lp G 2) : ⟪f, g⟫ = ∑' i, ⟪f i, g i⟫ :=
  rfl
#align lp.inner_eq_tsum lp.inner_eq_tsum

theorem hasSum_inner (f g : lp G 2) : HasSum (fun i => ⟪f i, g i⟫) ⟪f, g⟫ :=
  (summable_inner f g).hasSum
#align lp.has_sum_inner lp.hasSum_inner

theorem inner_single_left (i : ι) (a : G i) (f : lp G 2) : ⟪lp.single 2 i a, f⟫ = ⟪a, f i⟫ := by
  refine (hasSum_inner (lp.single 2 i a) f).unique ?_
  convert hasSum_ite_eq i ⟪a, f i⟫ using 1
  ext j
  rw [lp.single_apply]
  split_ifs with h
  · subst h; rfl
  · simp
#align lp.inner_single_left lp.inner_single_left

theorem inner_single_right (i : ι) (a : G i) (f : lp G 2) : ⟪f, lp.single 2 i a⟫ = ⟪f i, a⟫ := by
  simpa [inner_conj_symm] using congr_arg conj (@inner_single_left _ 𝕜 _ _ _ _ i a f)
#align lp.inner_single_right lp.inner_single_right

end lp

/-! ### Identification of a general Hilbert space `E` with a Hilbert sum -/


namespace OrthogonalFamily

variable {V : ∀ i, G i →ₗᵢ[𝕜] E} (hV : OrthogonalFamily 𝕜 G V)

protected theorem summable_of_lp (f : lp G 2) : Summable fun i => V i (f i) := by
  rw [hV.summable_iff_norm_sq_summable]
  convert (lp.memℓp f).summable _
  · norm_cast
  · norm_num
#align orthogonal_family.summable_of_lp OrthogonalFamily.summable_of_lp

/-- A mutually orthogonal family of subspaces of `E` induce a linear isometry from `lp 2` of the
subspaces into `E`. -/
protected def linearIsometry : lp G 2 →ₗᵢ[𝕜] E where
  toFun f := ∑' i, V i (f i)
  map_add' f g := by
    simp only [tsum_add (hV.summable_of_lp f) (hV.summable_of_lp g), lp.coeFn_add, Pi.add_apply,
      LinearIsometry.map_add]
  map_smul' c f := by
    simpa only [LinearIsometry.map_smul, Pi.smul_apply, lp.coeFn_smul] using
      tsum_const_smul c (hV.summable_of_lp f)
  norm_map' f := by
    classical
      -- needed for lattice instance on `Finset ι`, for `Filter.atTop_neBot`
      have H : 0 < (2 : ℝ≥0∞).toReal := by norm_num
      suffices ‖∑' i : ι, V i (f i)‖ ^ (2 : ℝ≥0∞).toReal = ‖f‖ ^ (2 : ℝ≥0∞).toReal by
        exact Real.rpow_left_injOn H.ne' (norm_nonneg _) (norm_nonneg _) this
      refine tendsto_nhds_unique ?_ (lp.hasSum_norm H f)
      convert (hV.summable_of_lp f).hasSum.norm.rpow_const (Or.inr H.le) using 1
      ext s
      exact mod_cast (hV.norm_sum f s).symm
#align orthogonal_family.linear_isometry OrthogonalFamily.linearIsometry

protected theorem linearIsometry_apply (f : lp G 2) : hV.linearIsometry f = ∑' i, V i (f i) :=
  rfl
#align orthogonal_family.linear_isometry_apply OrthogonalFamily.linearIsometry_apply

protected theorem hasSum_linearIsometry (f : lp G 2) :
    HasSum (fun i => V i (f i)) (hV.linearIsometry f) :=
  (hV.summable_of_lp f).hasSum
#align orthogonal_family.has_sum_linear_isometry OrthogonalFamily.hasSum_linearIsometry

@[simp]
protected theorem linearIsometry_apply_single {i : ι} (x : G i) :
    hV.linearIsometry (lp.single 2 i x) = V i x := by
  rw [hV.linearIsometry_apply, ← tsum_ite_eq i (V i x)]
  congr
  ext j
  rw [lp.single_apply]
  split_ifs with h
  · subst h; simp
  · simp [h]
#align orthogonal_family.linear_isometry_apply_single OrthogonalFamily.linearIsometry_apply_single

protected theorem linearIsometry_apply_dfinsupp_sum_single (W₀ : Π₀ i : ι, G i) :
    hV.linearIsometry (W₀.sum (lp.single 2)) = W₀.sum fun i => V i := by
  simp
#align orthogonal_family.linear_isometry_apply_dfinsupp_sum_single OrthogonalFamily.linearIsometry_apply_dfinsupp_sum_single

/-- The canonical linear isometry from the `lp 2` of a mutually orthogonal family of subspaces of
`E` into E, has range the closure of the span of the subspaces. -/
protected theorem range_linearIsometry [∀ i, CompleteSpace (G i)] :
    LinearMap.range hV.linearIsometry.toLinearMap =
      (⨆ i, LinearMap.range (V i).toLinearMap).topologicalClosure := by
    -- Porting note: dot notation broken
  refine le_antisymm ?_ ?_
  · rintro x ⟨f, rfl⟩
    refine mem_closure_of_tendsto (hV.hasSum_linearIsometry f) (eventually_of_forall ?_)
    intro s
    rw [SetLike.mem_coe]
    refine sum_mem ?_
    intro i _
    refine mem_iSup_of_mem i ?_
    exact LinearMap.mem_range_self _ (f i)
  · apply topologicalClosure_minimal
    · refine iSup_le ?_
      rintro i x ⟨x, rfl⟩
      use lp.single 2 i x
      exact hV.linearIsometry_apply_single x
    exact hV.linearIsometry.isometry.uniformInducing.isComplete_range.isClosed
#align orthogonal_family.range_linear_isometry OrthogonalFamily.range_linearIsometry

end OrthogonalFamily

section IsHilbertSum

variable (𝕜 G)
variable (V : ∀ i, G i →ₗᵢ[𝕜] E) (F : ι → Submodule 𝕜 E)

/-- Given a family of Hilbert spaces `G : ι → Type*`, a Hilbert sum of `G` consists of a Hilbert
space `E` and an orthogonal family `V : Π i, G i →ₗᵢ[𝕜] E` such that the induced isometry
`Φ : lp G 2 → E` is surjective.

Keeping in mind that `lp G 2` is "the" external Hilbert sum of `G : ι → Type*`, this is analogous
to `DirectSum.IsInternal`, except that we don't express it in terms of actual submodules. -/
structure IsHilbertSum : Prop where
  ofSurjective ::
  /-- The orthogonal family constituting the summands in the Hilbert sum. -/
  protected OrthogonalFamily : OrthogonalFamily 𝕜 G V
  /-- The isometry `lp G 2 → E` induced by the orthogonal family is surjective. -/
  protected surjective_isometry : Function.Surjective OrthogonalFamily.linearIsometry
#align is_hilbert_sum IsHilbertSum

variable {𝕜 G V}

/-- If `V : Π i, G i →ₗᵢ[𝕜] E` is an orthogonal family such that the supremum of the ranges of
`V i` is dense, then `(E, V)` is a Hilbert sum of `G`. -/
theorem IsHilbertSum.mk [∀ i, CompleteSpace <| G i] (hVortho : OrthogonalFamily 𝕜 G V)
    (hVtotal : ⊤ ≤ (⨆ i, LinearMap.range (V i).toLinearMap).topologicalClosure) :
    IsHilbertSum 𝕜 G V :=
  { OrthogonalFamily := hVortho
    surjective_isometry := by
      rw [← LinearIsometry.coe_toLinearMap]
      exact LinearMap.range_eq_top.mp
        (eq_top_iff.mpr <| hVtotal.trans_eq hVortho.range_linearIsometry.symm) }
#align is_hilbert_sum.mk IsHilbertSum.mk

/-- This is `Orthonormal.isHilbertSum` in the case of actual inclusions from subspaces. -/
theorem IsHilbertSum.mkInternal [∀ i, CompleteSpace <| F i]
    (hFortho : OrthogonalFamily 𝕜 (fun i => F i) fun i => (F i).subtypeₗᵢ)
    (hFtotal : ⊤ ≤ (⨆ i, F i).topologicalClosure) :
    IsHilbertSum 𝕜 (fun i => F i) fun i => (F i).subtypeₗᵢ :=
  IsHilbertSum.mk hFortho (by simpa [subtypeₗᵢ_toLinearMap, range_subtype] using hFtotal)
#align is_hilbert_sum.mk_internal IsHilbertSum.mkInternal

/-- *A* Hilbert sum `(E, V)` of `G` is canonically isomorphic to *the* Hilbert sum of `G`,
i.e `lp G 2`.

Note that this goes in the opposite direction from `OrthogonalFamily.linearIsometry`. -/
noncomputable def IsHilbertSum.linearIsometryEquiv (hV : IsHilbertSum 𝕜 G V) : E ≃ₗᵢ[𝕜] lp G 2 :=
  LinearIsometryEquiv.symm <|
    LinearIsometryEquiv.ofSurjective hV.OrthogonalFamily.linearIsometry hV.surjective_isometry
#align is_hilbert_sum.linear_isometry_equiv IsHilbertSum.linearIsometryEquiv

/-- In the canonical isometric isomorphism between a Hilbert sum `E` of `G` and `lp G 2`,
a vector `w : lp G 2` is the image of the infinite sum of the associated elements in `E`. -/
protected theorem IsHilbertSum.linearIsometryEquiv_symm_apply (hV : IsHilbertSum 𝕜 G V)
    (w : lp G 2) : hV.linearIsometryEquiv.symm w = ∑' i, V i (w i) := by
  simp [IsHilbertSum.linearIsometryEquiv, OrthogonalFamily.linearIsometry_apply]
#align is_hilbert_sum.linear_isometry_equiv_symm_apply IsHilbertSum.linearIsometryEquiv_symm_apply

/-- In the canonical isometric isomorphism between a Hilbert sum `E` of `G` and `lp G 2`,
a vector `w : lp G 2` is the image of the infinite sum of the associated elements in `E`, and this
sum indeed converges. -/
protected theorem IsHilbertSum.hasSum_linearIsometryEquiv_symm (hV : IsHilbertSum 𝕜 G V)
    (w : lp G 2) : HasSum (fun i => V i (w i)) (hV.linearIsometryEquiv.symm w) := by
  simp [IsHilbertSum.linearIsometryEquiv, OrthogonalFamily.hasSum_linearIsometry]
#align is_hilbert_sum.has_sum_linear_isometry_equiv_symm IsHilbertSum.hasSum_linearIsometryEquiv_symm

/-- In the canonical isometric isomorphism between a Hilbert sum `E` of `G : ι → Type*` and
`lp G 2`, an "elementary basis vector" in `lp G 2` supported at `i : ι` is the image of the
associated element in `E`. -/
@[simp]
protected theorem IsHilbertSum.linearIsometryEquiv_symm_apply_single (hV : IsHilbertSum 𝕜 G V)
    {i : ι} (x : G i) : hV.linearIsometryEquiv.symm (lp.single 2 i x) = V i x := by
  simp [IsHilbertSum.linearIsometryEquiv, OrthogonalFamily.linearIsometry_apply_single]
#align is_hilbert_sum.linear_isometry_equiv_symm_apply_single IsHilbertSum.linearIsometryEquiv_symm_apply_single

/-- In the canonical isometric isomorphism between a Hilbert sum `E` of `G : ι → Type*` and
`lp G 2`, a finitely-supported vector in `lp G 2` is the image of the associated finite sum of
elements of `E`. -/
protected theorem IsHilbertSum.linearIsometryEquiv_symm_apply_dfinsupp_sum_single
    (hV : IsHilbertSum 𝕜 G V) (W₀ : Π₀ i : ι, G i) :
    hV.linearIsometryEquiv.symm (W₀.sum (lp.single 2)) = W₀.sum fun i => V i := by
  simp only [map_dfinsupp_sum, IsHilbertSum.linearIsometryEquiv_symm_apply_single]
#align is_hilbert_sum.linear_isometry_equiv_symm_apply_dfinsupp_sum_single IsHilbertSum.linearIsometryEquiv_symm_apply_dfinsupp_sum_single

/-- In the canonical isometric isomorphism between a Hilbert sum `E` of `G : ι → Type*` and
`lp G 2`, a finitely-supported vector in `lp G 2` is the image of the associated finite sum of
elements of `E`. -/
@[simp]
protected theorem IsHilbertSum.linearIsometryEquiv_apply_dfinsupp_sum_single
    (hV : IsHilbertSum 𝕜 G V) (W₀ : Π₀ i : ι, G i) :
    ((W₀.sum (γ := lp G 2) fun a b ↦ hV.linearIsometryEquiv (V a b)) : ∀ i, G i) = W₀ := by
  rw [← map_dfinsupp_sum]
  rw [← hV.linearIsometryEquiv_symm_apply_dfinsupp_sum_single]
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext i
  simp (config := { contextual := true }) [DFinsupp.sum, lp.single_apply]
#align is_hilbert_sum.linear_isometry_equiv_apply_dfinsupp_sum_single IsHilbertSum.linearIsometryEquiv_apply_dfinsupp_sum_single

/-- Given a total orthonormal family `v : ι → E`, `E` is a Hilbert sum of `fun i : ι => 𝕜`
relative to the family of linear isometries `fun i k => k • v i`. -/
theorem Orthonormal.isHilbertSum {v : ι → E} (hv : Orthonormal 𝕜 v)
    (hsp : ⊤ ≤ (span 𝕜 (Set.range v)).topologicalClosure) :
    IsHilbertSum 𝕜 (fun _ : ι => 𝕜) fun i => LinearIsometry.toSpanSingleton 𝕜 E (hv.1 i) :=
  IsHilbertSum.mk hv.orthogonalFamily (by
    convert hsp
    simp [← LinearMap.span_singleton_eq_range, ← Submodule.span_iUnion])
#align orthonormal.is_hilbert_sum Orthonormal.isHilbertSum

theorem Submodule.isHilbertSumOrthogonal (K : Submodule 𝕜 E) [hK : CompleteSpace K] :
    IsHilbertSum 𝕜 (fun b => ↥(cond b K Kᗮ)) fun b => (cond b K Kᗮ).subtypeₗᵢ := by
  have : ∀ b, CompleteSpace (↥(cond b K Kᗮ)) := by
    intro b
    cases b <;> first | exact instOrthogonalCompleteSpace K | assumption
  refine IsHilbertSum.mkInternal _ K.orthogonalFamily_self ?_
  refine le_trans ?_ (Submodule.le_topologicalClosure _)
  rw [iSup_bool_eq, cond, cond]
  refine Codisjoint.top_le ?_
  exact Submodule.isCompl_orthogonal_of_completeSpace.codisjoint
#align submodule.is_hilbert_sum_orthogonal Submodule.isHilbertSumOrthogonal

end IsHilbertSum

/-! ### Hilbert bases -/


section

variable (ι) (𝕜) (E)

/-- A Hilbert basis on `ι` for an inner product space `E` is an identification of `E` with the `lp`
space `ℓ²(ι, 𝕜)`. -/
structure HilbertBasis where ofRepr ::
  /-- The linear isometric equivalence implementing identifying the Hilbert space with `ℓ²`. -/
  repr : E ≃ₗᵢ[𝕜] ℓ²(ι, 𝕜)
#align hilbert_basis HilbertBasis

end

namespace HilbertBasis

instance {ι : Type*} : Inhabited (HilbertBasis ι 𝕜 ℓ²(ι, 𝕜)) :=
  ⟨ofRepr (LinearIsometryEquiv.refl 𝕜 _)⟩

/-- `b i` is the `i`th basis vector. -/
instance instCoeFun : CoeFun (HilbertBasis ι 𝕜 E) fun _ => ι → E where
  coe b i := b.repr.symm (lp.single 2 i (1 : 𝕜))

-- This is a bad `@[simp]` lemma: the RHS is a coercion containing the LHS.
protected theorem repr_symm_single (b : HilbertBasis ι 𝕜 E) (i : ι) :
    b.repr.symm (lp.single 2 i (1 : 𝕜)) = b i :=
  rfl
#align hilbert_basis.repr_symm_single HilbertBasis.repr_symm_single

protected theorem repr_self (b : HilbertBasis ι 𝕜 E) (i : ι) :
    b.repr (b i) = lp.single 2 i (1 : 𝕜) := by
  simp only [LinearIsometryEquiv.apply_symm_apply]
#align hilbert_basis.repr_self HilbertBasis.repr_self

protected theorem repr_apply_apply (b : HilbertBasis ι 𝕜 E) (v : E) (i : ι) :
    b.repr v i = ⟪b i, v⟫ := by
  rw [← b.repr.inner_map_map (b i) v, b.repr_self, lp.inner_single_left]
  simp
#align hilbert_basis.repr_apply_apply HilbertBasis.repr_apply_apply

@[simp]
protected theorem orthonormal (b : HilbertBasis ι 𝕜 E) : Orthonormal 𝕜 b := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [← b.repr.inner_map_map (b i) (b j), b.repr_self, b.repr_self, lp.inner_single_left,
    lp.single_apply]
  simp
#align hilbert_basis.orthonormal HilbertBasis.orthonormal

protected theorem hasSum_repr_symm (b : HilbertBasis ι 𝕜 E) (f : ℓ²(ι, 𝕜)) :
    HasSum (fun i => f i • b i) (b.repr.symm f) := by
  suffices H : (fun i : ι => f i • b i) = fun b_1 : ι => b.repr.symm.toContinuousLinearEquiv <|
      (fun i : ι => lp.single 2 i (f i) (E := (fun _ : ι => 𝕜))) b_1 by
    rw [H]
    have : HasSum (fun i : ι => lp.single 2 i (f i)) f := lp.hasSum_single ENNReal.two_ne_top f
    exact (↑b.repr.symm.toContinuousLinearEquiv : ℓ²(ι, 𝕜) →L[𝕜] E).hasSum this
  ext i
  apply b.repr.injective
  letI : NormedSpace 𝕜 (lp (fun _i : ι => 𝕜) 2) := by infer_instance
  have : lp.single (E := (fun _ : ι => 𝕜)) 2 i (f i * 1) = f i • lp.single 2 i 1 :=
    lp.single_smul (E := (fun _ : ι => 𝕜)) 2 i (1 : 𝕜) (f i)
  rw [mul_one] at this
  rw [LinearIsometryEquiv.map_smul, b.repr_self, ← this,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  exact (b.repr.apply_symm_apply (lp.single 2 i (f i))).symm
#align hilbert_basis.has_sum_repr_symm HilbertBasis.hasSum_repr_symm

protected theorem hasSum_repr (b : HilbertBasis ι 𝕜 E) (x : E) :
    HasSum (fun i => b.repr x i • b i) x := by simpa using b.hasSum_repr_symm (b.repr x)
#align hilbert_basis.has_sum_repr HilbertBasis.hasSum_repr

@[simp]
protected theorem dense_span (b : HilbertBasis ι 𝕜 E) :
    (span 𝕜 (Set.range b)).topologicalClosure = ⊤ := by
  classical
    rw [eq_top_iff]
    rintro x -
    refine mem_closure_of_tendsto (b.hasSum_repr x) (eventually_of_forall ?_)
    intro s
    simp only [SetLike.mem_coe]
    refine sum_mem ?_
    rintro i -
    refine smul_mem _ _ ?_
    exact subset_span ⟨i, rfl⟩
#align hilbert_basis.dense_span HilbertBasis.dense_span

protected theorem hasSum_inner_mul_inner (b : HilbertBasis ι 𝕜 E) (x y : E) :
    HasSum (fun i => ⟪x, b i⟫ * ⟪b i, y⟫) ⟪x, y⟫ := by
  convert (b.hasSum_repr y).mapL (innerSL 𝕜 x) using 1
  ext i
  rw [innerSL_apply, b.repr_apply_apply, inner_smul_right, mul_comm]
#align hilbert_basis.has_sum_inner_mul_inner HilbertBasis.hasSum_inner_mul_inner

protected theorem summable_inner_mul_inner (b : HilbertBasis ι 𝕜 E) (x y : E) :
    Summable fun i => ⟪x, b i⟫ * ⟪b i, y⟫ :=
  (b.hasSum_inner_mul_inner x y).summable
#align hilbert_basis.summable_inner_mul_inner HilbertBasis.summable_inner_mul_inner

protected theorem tsum_inner_mul_inner (b : HilbertBasis ι 𝕜 E) (x y : E) :
    ∑' i, ⟪x, b i⟫ * ⟪b i, y⟫ = ⟪x, y⟫ :=
  (b.hasSum_inner_mul_inner x y).tsum_eq
#align hilbert_basis.tsum_inner_mul_inner HilbertBasis.tsum_inner_mul_inner

-- Note: this should be `b.repr` composed with an identification of `lp (fun i : ι => 𝕜) p` with
-- `PiLp p (fun i : ι => 𝕜)` (in this case with `p = 2`), but we don't have this yet (July 2022).
/-- A finite Hilbert basis is an orthonormal basis. -/
protected def toOrthonormalBasis [Fintype ι] (b : HilbertBasis ι 𝕜 E) : OrthonormalBasis ι 𝕜 E :=
  OrthonormalBasis.mk b.orthonormal
    (by
      refine Eq.ge ?_
      have := (span 𝕜 (Finset.univ.image b : Set E)).closed_of_finiteDimensional
      simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ, HilbertBasis.dense_span] using
        this.submodule_topologicalClosure_eq.symm)
#align hilbert_basis.to_orthonormal_basis HilbertBasis.toOrthonormalBasis

@[simp]
theorem coe_toOrthonormalBasis [Fintype ι] (b : HilbertBasis ι 𝕜 E) :
    (b.toOrthonormalBasis : ι → E) = b :=
  OrthonormalBasis.coe_mk _ _
#align hilbert_basis.coe_to_orthonormal_basis HilbertBasis.coe_toOrthonormalBasis

protected theorem hasSum_orthogonalProjection {U : Submodule 𝕜 E} [CompleteSpace U]
    (b : HilbertBasis ι 𝕜 U) (x : E) :
    HasSum (fun i => ⟪(b i : E), x⟫ • b i) (orthogonalProjection U x) := by
  simpa only [b.repr_apply_apply, inner_orthogonalProjection_eq_of_mem_left] using
    b.hasSum_repr (orthogonalProjection U x)
#align hilbert_basis.has_sum_orthogonal_projection HilbertBasis.hasSum_orthogonalProjection

theorem finite_spans_dense (b : HilbertBasis ι 𝕜 E) :
    (⨆ J : Finset ι, span 𝕜 (J.image b : Set E)).topologicalClosure = ⊤ :=
  eq_top_iff.mpr <| b.dense_span.ge.trans (by
    simp_rw [← Submodule.span_iUnion]
    exact topologicalClosure_mono (span_mono <| Set.range_subset_iff.mpr fun i =>
      Set.mem_iUnion_of_mem {i} <| Finset.mem_coe.mpr <| Finset.mem_image_of_mem _ <|
      Finset.mem_singleton_self i))
#align hilbert_basis.finite_spans_dense HilbertBasis.finite_spans_dense

variable {v : ι → E} (hv : Orthonormal 𝕜 v)

/-- An orthonormal family of vectors whose span is dense in the whole module is a Hilbert basis. -/
protected def mk (hsp : ⊤ ≤ (span 𝕜 (Set.range v)).topologicalClosure) : HilbertBasis ι 𝕜 E :=
  HilbertBasis.ofRepr <| (hv.isHilbertSum hsp).linearIsometryEquiv
#align hilbert_basis.mk HilbertBasis.mk

theorem _root_.Orthonormal.linearIsometryEquiv_symm_apply_single_one (h i) :
    (hv.isHilbertSum h).linearIsometryEquiv.symm (lp.single 2 i 1) = v i := by
  rw [IsHilbertSum.linearIsometryEquiv_symm_apply_single, LinearIsometry.toSpanSingleton_apply,
    one_smul]
#align orthonormal.linear_isometry_equiv_symm_apply_single_one Orthonormal.linearIsometryEquiv_symm_apply_single_one

@[simp]
protected theorem coe_mk (hsp : ⊤ ≤ (span 𝕜 (Set.range v)).topologicalClosure) :
    ⇑(HilbertBasis.mk hv hsp) = v := by
  apply funext <| Orthonormal.linearIsometryEquiv_symm_apply_single_one hv hsp
#align hilbert_basis.coe_mk HilbertBasis.coe_mk

/-- An orthonormal family of vectors whose span has trivial orthogonal complement is a Hilbert
basis. -/
protected def mkOfOrthogonalEqBot (hsp : (span 𝕜 (Set.range v))ᗮ = ⊥) : HilbertBasis ι 𝕜 E :=
  HilbertBasis.mk hv
    (by rw [← orthogonal_orthogonal_eq_closure, ← eq_top_iff, orthogonal_eq_top_iff, hsp])
#align hilbert_basis.mk_of_orthogonal_eq_bot HilbertBasis.mkOfOrthogonalEqBot

@[simp]
protected theorem coe_mkOfOrthogonalEqBot (hsp : (span 𝕜 (Set.range v))ᗮ = ⊥) :
    ⇑(HilbertBasis.mkOfOrthogonalEqBot hv hsp) = v :=
  HilbertBasis.coe_mk hv _
#align hilbert_basis.coe_of_orthogonal_eq_bot_mk HilbertBasis.coe_mkOfOrthogonalEqBot

-- Note : this should be `b.repr` composed with an identification of `lp (fun i : ι => 𝕜) p` with
-- `PiLp p (fun i : ι => 𝕜)` (in this case with `p = 2`), but we don't have this yet (July 2022).
/-- An orthonormal basis is a Hilbert basis. -/
protected def _root_.OrthonormalBasis.toHilbertBasis [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) :
    HilbertBasis ι 𝕜 E :=
  HilbertBasis.mk b.orthonormal <| by
    simpa only [← OrthonormalBasis.coe_toBasis, b.toBasis.span_eq, eq_top_iff] using
      @subset_closure E _ _
#align orthonormal_basis.to_hilbert_basis OrthonormalBasis.toHilbertBasis

@[simp]
theorem _root_.OrthonormalBasis.coe_toHilbertBasis [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) :
    (b.toHilbertBasis : ι → E) = b :=
  HilbertBasis.coe_mk _ _
#align orthonormal_basis.coe_to_hilbert_basis OrthonormalBasis.coe_toHilbertBasis

/-- A Hilbert space admits a Hilbert basis extending a given orthonormal subset. -/
theorem _root_.Orthonormal.exists_hilbertBasis_extension {s : Set E}
    (hs : Orthonormal 𝕜 ((↑) : s → E)) :
    ∃ (w : Set E) (b : HilbertBasis w 𝕜 E), s ⊆ w ∧ ⇑b = ((↑) : w → E) :=
  let ⟨w, hws, hw_ortho, hw_max⟩ := exists_maximal_orthonormal hs
  ⟨w, HilbertBasis.mkOfOrthogonalEqBot hw_ortho
    (by simpa only [Subtype.range_coe_subtype, Set.setOf_mem_eq,
      maximal_orthonormal_iff_orthogonalComplement_eq_bot hw_ortho] using hw_max),
    hws, HilbertBasis.coe_mkOfOrthogonalEqBot _ _⟩
#align orthonormal.exists_hilbert_basis_extension Orthonormal.exists_hilbertBasis_extension

variable (𝕜 E)

/-- A Hilbert space admits a Hilbert basis. -/
theorem _root_.exists_hilbertBasis : ∃ (w : Set E) (b : HilbertBasis w 𝕜 E), ⇑b = ((↑) : w → E) :=
  let ⟨w, hw, _, hw''⟩ := (orthonormal_empty 𝕜 E).exists_hilbertBasis_extension
  ⟨w, hw, hw''⟩
#align exists_hilbert_basis exists_hilbertBasis

end HilbertBasis
