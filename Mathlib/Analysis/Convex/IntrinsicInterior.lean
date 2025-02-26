/-
Copyright (c) 2025 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Chenyi Li, ZaiWen Wen
-/
import Mathlib.Analysis.Convex.Intrinsic
/-!
# Intrinsic Interior, Closure, and Related Properties of Convex Sets
This file explores the intrinsic interior, intrinsic closure,
and related properties of convex sets in a normed vector space,
focusing on their interactions with affine spans, closures, and intersections.
These concepts are essential in convex analysis and finite-dimensional spaces.
The intrinsic interior and closure of a convex set are defined based on its affine span,
while the intrinsic interior is generally larger than the topological interior,
and the intrinsic closure coincides with the topological closure under certain conditions.

## References

* Chapter 6 of [R. T. Rockafellar, *Convex Analysis*][rockafellar1970].
-/

open AffineSubspace Set

open scoped Pointwise

variable {𝕜 V P : Type*}

noncomputable section

variable (𝕜) [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]

/-
Given a nonempty set s, it defines an isomorphism
between the affine span and its direction
-/
@[simp]
def affSpanEquiv {s : Set P} (hs : s.Nonempty):
    affineSpan 𝕜 s ≃ (affineSpan 𝕜 s).direction where
  toFun := fun x => ⟨x.1 -ᵥ hs.choose,
    AffineSubspace.vsub_mem_direction (SetLike.coe_mem x) (mem_affineSpan _ hs.choose_spec)⟩
  invFun := fun x => ⟨x +ᵥ hs.choose,
    AffineSubspace.vadd_mem_of_mem_direction (Submodule.coe_mem x)
    (mem_affineSpan _ hs.choose_spec)⟩
  left_inv := by
    simp [Function.LeftInverse]
    intro a _
    exact ((eq_vadd_iff_vsub_eq a _ _).mpr rfl).symm
  right_inv := by
    simp [Function.RightInverse, Function.LeftInverse]
    intro a _
    exact AddTorsor.vadd_vsub' _ _

section

theorem intrinsicInterior_sub_intrinsicClosure_intrinsicInterior [TopologicalSpace V]
    {s : Set V}:
    intrinsicInterior 𝕜 s ⊆ intrinsicInterior 𝕜 (intrinsicClosure 𝕜 s) := by
  simp [intrinsicInterior]
  rw [affineSpan_intrinsicClosure s, Function.Injective.preimage_image Subtype.val_injective]
  apply interior_mono (preimage_mono subset_intrinsicClosure)

end

end

noncomputable section

variable (𝕜) [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  [ContinuousSub V] [ContinuousAdd V]

/-
This defines an affine span equivalence between a set s in the vector space V and its direction.
-/
@[simp]
def affSpanDirEquiv
    {s : Set V} (hs : s.Nonempty):
  affineSpan 𝕜 s ≃ₜ (affineSpan 𝕜 s).direction:=
    ⟨affSpanEquiv 𝕜 hs, by
      simpa only [affSpanEquiv, Equiv.toFun_as_coe, Equiv.coe_fn_mk]
      using .subtype_mk (.comp (continuous_sub_right _) continuous_subtype_val) _
      , by
      simpa only [affSpanEquiv, Equiv.toFun_as_coe, Equiv.coe_fn_mk]
      using .subtype_mk (.comp (continuous_add_right _) continuous_subtype_val) _⟩

/-
It is a function that maps affine space elements to the vector space V.
This is prepared for defining integers **affSpanCoerce**
-/
@[simp]
def affSpanCoerce_pre'  {s : Set V} (hs : s.Nonempty) :=
  ((↑) : (affineSpan 𝕜 s) → V) ∘ (affSpanDirEquiv 𝕜 hs).symm

lemma sub_range {s : Set V} (hs : s.Nonempty) :
    s ⊆ range (affSpanCoerce_pre' 𝕜 hs) := by
  intro x hx
  simp only [affSpanCoerce_pre', affSpanDirEquiv, affSpanEquiv, vsub_eq_sub,
    Homeomorph.homeomorph_mk_coe_symm, Equiv.coe_fn_symm_mk, mem_range, Function.comp_apply,
    Subtype.exists]
  have b : x -ᵥ Exists.choose hs ∈ (affineSpan 𝕜 s).direction := by
    refine vsub_mem_direction ?hp1 ?hp2
    exact mem_affineSpan 𝕜 hx
    refine mem_affineSpan 𝕜 hs.choose_spec
  use x -ᵥ Exists.choose hs, b
  symm
  exact (eq_vadd_iff_vsub_eq x _ _).mpr rfl

lemma inv_eq_self {s : Set V} (hs : s.Nonempty){x}(hx : x ∈ range (affSpanCoerce_pre' 𝕜 hs)):
   (affSpanCoerce_pre' 𝕜 hs) (Function.invFun (affSpanCoerce_pre' 𝕜 hs) x) = x := by
  let g := (affSpanCoerce_pre' 𝕜 hs)
  show g (Function.invFun g x) = x
  simp only [Function.invFun]
  have : ∃ x_1, g x_1 = x := ⟨hx.choose, hx.choose_spec⟩
  simpa [this] using this.choose_spec

lemma eq_image_preimage {s : Set V} (hs : s.Nonempty) :
    s = (affSpanCoerce_pre' 𝕜 hs) '' ((affSpanCoerce_pre' 𝕜 hs) ⁻¹' s) := by
  refine Eq.symm (image_preimage_eq_of_subset ?hs)
  exact sub_range 𝕜 hs

/-
This defines a linear map from the direction of the affine span of s back to the vector space V.
-/
def affSpanCoerce_pre {s : Set V} (hs : s.Nonempty) :
    (affineSpan 𝕜 s).direction →ᵃ[𝕜] V where
  toFun := affSpanCoerce_pre' 𝕜 hs
  linear := (affineSpan 𝕜 s).direction.subtype
  map_vadd' := by
    simp [affSpanCoerce_pre']
    intro x _ y _
    exact add_assoc y x _

lemma pre_eq_image_preimage {s : Set V} (hs : s.Nonempty) :
    s = (affSpanCoerce_pre 𝕜 hs) '' ((affSpanCoerce_pre 𝕜 hs) ⁻¹' s) := by
  refine Eq.symm (image_preimage_eq_of_subset ?hs)
  exact sub_range 𝕜 hs

lemma affSpanCoerce_pre_Injective {s : Set V} (hs : s.Nonempty) :
    Function.Injective (affSpanCoerce_pre 𝕜 hs) :=
  (AffineMap.linear_injective_iff _).mp <|
   (injective_codRestrict Subtype.property).mp fun _ _ a ↦ a

lemma pre_inv_self_eq_id {s : Set V} (hs : s.Nonempty) (u)  :
  (Function.invFun (affSpanCoerce_pre 𝕜 hs)) '' ((affSpanCoerce_pre 𝕜 hs) '' u) = u :=
  Function.LeftInverse.image_image (Function.leftInverse_invFun
    (affSpanCoerce_pre_Injective 𝕜 hs)) u


theorem intrinsicInterior_equiv_pre {s : Set V} (hs : s.Nonempty):
    intrinsicInterior 𝕜 s = (affSpanCoerce_pre 𝕜 hs) ''
      (interior ((affSpanCoerce_pre 𝕜 hs) ⁻¹' s)) := by
  show intrinsicInterior 𝕜 s = (affSpanCoerce_pre' 𝕜 hs) ''
    (interior ((affSpanCoerce_pre' 𝕜 hs) ⁻¹' s))
  rw [affSpanCoerce_pre', preimage_comp, image_comp,
    ((affSpanDirEquiv 𝕜 hs).symm).image_interior, ((affSpanDirEquiv 𝕜 hs).symm).image_preimage]
  rfl

theorem intrinsicClosure_equiv_pre {s : Set V} (hs : s.Nonempty):
    intrinsicClosure 𝕜 s = (affSpanCoerce_pre 𝕜 hs) ''
      (closure ((affSpanCoerce_pre 𝕜 hs) ⁻¹' s)) := by
  show intrinsicClosure 𝕜 s = (affSpanCoerce_pre' 𝕜 hs) ''
    (closure ((affSpanCoerce_pre' 𝕜 hs) ⁻¹' s))
  rw [affSpanCoerce_pre', preimage_comp, image_comp,
    ((affSpanDirEquiv 𝕜 hs).symm).image_closure, ((affSpanDirEquiv 𝕜 hs).symm).image_preimage]
  rfl

end

noncomputable section

variable (𝕜) [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-
This defines an affine map (affineMap) from the direction of
the affine span of s to the vector space V.
-/
def affSpanCoerce {s : Set V} (hs : s.Nonempty) :
    (affineSpan 𝕜 s).direction →ᵃⁱ[𝕜] V :=
    .mk (affSpanCoerce_pre 𝕜 hs) (by simp [affSpanCoerce_pre])

lemma inv_self_eq_id {s : Set V} (hs : s.Nonempty) (u)  :
  (Function.invFun (affSpanCoerce 𝕜 hs)) '' ((affSpanCoerce 𝕜 hs) '' u) = u :=
  Function.LeftInverse.image_image (Function.leftInverse_invFun (affSpanCoerce 𝕜 hs).injective) u

theorem intrinsicInterior_equiv {s : Set V} (hs : s.Nonempty):
    intrinsicInterior 𝕜 s = (affSpanCoerce 𝕜 hs) '' (interior ((affSpanCoerce 𝕜 hs) ⁻¹' s)) := by
  show intrinsicInterior 𝕜 s = (affSpanCoerce_pre' 𝕜 hs) ''
    (interior ((affSpanCoerce_pre' 𝕜 hs) ⁻¹' s))
  rw [affSpanCoerce_pre', preimage_comp, image_comp,
    ((affSpanDirEquiv 𝕜 hs).symm).image_interior, ((affSpanDirEquiv 𝕜 hs).symm).image_preimage]
  rfl

theorem intrinsicClosure_equiv {s : Set V} (hs : s.Nonempty):
    intrinsicClosure 𝕜 s = (affSpanCoerce 𝕜 hs) '' (closure ((affSpanCoerce 𝕜 hs) ⁻¹' s)) := by
  show intrinsicClosure 𝕜 s = (affSpanCoerce_pre' 𝕜 hs) ''
    (closure ((affSpanCoerce_pre' 𝕜 hs) ⁻¹' s))
  rw [affSpanCoerce_pre', preimage_comp, image_comp,
    ((affSpanDirEquiv 𝕜 hs).symm).image_closure, ((affSpanDirEquiv 𝕜 hs).symm).image_preimage]
  rfl


end

section LineSegmentPrinciple

variable (𝕜) [LinearOrderedField 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousConstSMul 𝕜 V] [ContinuousSub V] [ContinuousAdd V]

instance {s : Set V} : ContinuousConstSMul 𝕜 (affineSpan 𝕜 s).direction where
  continuous_const_smul := by
    intro c
    let f := fun x : ↥(affineSpan 𝕜 s).direction ↦ c • x.1
    have : Continuous f :=
      Continuous.comp' (continuous_const_smul c) continuous_subtype_val
    exact continuous_induced_rng.mpr this

/-
If s is convex, and x belongs to the intrinsic interior of s
while y belongs to the intrinsic closure of s,
then the open segment between x and y is contained within the intrinsic interior of s.
-/
theorem openSegment_sub_intrinsicInterior {s : Set V} (hsc : Convex 𝕜 s) {x y : V}
    (hx : x ∈ intrinsicInterior 𝕜 s) (hy : y ∈ intrinsicClosure 𝕜 s) :
    openSegment 𝕜 x y ⊆ intrinsicInterior 𝕜 s := by
  by_cases hs : s.Nonempty
  · rw [intrinsicInterior_equiv_pre 𝕜 hs] at *
    rw [intrinsicClosure_equiv_pre 𝕜 hs] at hy
    let h := affSpanCoerce_pre 𝕜  hs
    let g := Function.invFun h
    have hgu (u) : g '' (h '' u) = u := pre_inv_self_eq_id 𝕜 hs u

    have hx' : g x ∈ interior (h ⁻¹' s) := by
      rw [← hgu (interior (h ⁻¹' s))]
      exact mem_image_of_mem g hx

    have hy' : g y ∈ closure (h ⁻¹' s) := by
      rw [← hgu (closure (h ⁻¹' s))]
      exact mem_image_of_mem g hy

    have hgx : h (g x) = x :=
      inv_eq_self 𝕜 hs (mem_range_of_mem_image _ _ hx)

    have hgy : h (g y) = y :=
      inv_eq_self 𝕜 hs (mem_range_of_mem_image _ _ hy)

    show openSegment 𝕜 x y ⊆ h '' interior (h ⁻¹' s)
    have hop : h '' (openSegment 𝕜 (g x) (g y)) = openSegment 𝕜 (h (g x)) (h (g y)) := by
      apply image_openSegment 𝕜 _ (g x) (g y)
    rw [← hgx, ← hgy, ← hop]
    apply image_mono
    exact Convex.openSegment_interior_closure_subset_interior (Convex.affine_preimage _ hsc) hx' hy'
  simp [not_nonempty_iff_eq_empty.mp hs] at *



end LineSegmentPrinciple

section affinespan
/-
This section prove that if a set s is convex,
then the intrinsicInterior and intrinsicClosure of s is also convex and
they have same affinespan。
-/
section

variable (𝕜) [LinearOrderedField 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousConstSMul 𝕜 V][ContinuousSub V] [ContinuousAdd V]{s : Set V}

/-
If a set s is convex, then the intrinsic Interior and Closure of s is also convex
-/
theorem convex_intrinsicInterior (hsc : Convex 𝕜 s) :
    Convex 𝕜 (intrinsicInterior 𝕜 s) := by
  by_cases hs : s.Nonempty
  · rw [intrinsicInterior_equiv_pre 𝕜 hs]
    apply Convex.affine_image _ <| Convex.interior (Convex.affine_preimage _ hsc)
  simpa [not_nonempty_iff_eq_empty.mp hs] using convex_empty

theorem convex_intrinsicClosure (hsc : Convex 𝕜 s) :
    Convex 𝕜 (intrinsicClosure 𝕜 s) := by
  by_cases hs : s.Nonempty
  · rw [intrinsicClosure_equiv_pre 𝕜 hs]
    apply Convex.affine_image _ <| Convex.closure (Convex.affine_preimage _ hsc)
  simpa [not_nonempty_iff_eq_empty.mp hs] using convex_empty

end

variable [NormedAddCommGroup V] [NormedSpace ℝ V] {s : Set V}

theorem convex_intrinsicInterior' (hsc : Convex ℝ s) :
    Convex ℝ (intrinsicInterior ℝ s) :=
  convex_intrinsicInterior ℝ hsc

theorem affinespan_sub_intrinsicInterior_sub [FiniteDimensional ℝ V] (hsc : Convex ℝ s) :
    affineSpan ℝ s ≤ (affineSpan ℝ (intrinsicInterior ℝ s)) := by
  by_cases hs : s.Nonempty
  · rw [intrinsicInterior_equiv_pre ℝ hs]
    let h := affSpanCoerce_pre ℝ hs
    show affineSpan ℝ s ≤ affineSpan ℝ (h '' interior (h ⁻¹' s))
    rw [← AffineSubspace.map_span]
    have : (interior (h ⁻¹' s)).Nonempty :=
      image_nonempty.mp (intrinsicInterior_equiv_pre ℝ hs ▸
        Set.Nonempty.intrinsicInterior hsc hs)
    have : (affineSpan ℝ (interior (h ⁻¹' s))) = ⊤ :=
      IsOpen.affineSpan_eq_top isOpen_interior this
    simp [this]
    refine affineSpan_le.mpr ?_
    simp only [coe_map, top_coe, image_univ]
    apply sub_range
  simp [not_nonempty_iff_eq_empty.mp hs]


theorem intrinsicInterior_subset_affineSpan  {𝕜 : Type*} {V : Type*} {P : Type*} [Ring 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace P] [AddTorsor V P] {s : Set P} :
  intrinsicInterior 𝕜 s ⊆ affineSpan 𝕜 s :=
    affineSpan_le.mp <| affineSpan_mono 𝕜 intrinsicInterior_subset
/-
In finite-dimensional real spaces,
the affine span of the intrinsic interior of a convex set s is equal to the affine span of s.
-/
theorem affinespan_intrinsicInterior [FiniteDimensional ℝ V] (hsc : Convex ℝ s) :
  affineSpan ℝ (intrinsicInterior ℝ s) = affineSpan ℝ s :=
  (affineSpan_le.2 intrinsicInterior_subset_affineSpan).antisymm <|
  affinespan_sub_intrinsicInterior_sub hsc

/-
in finite-dimensional real spaces,
the intrinsic interior of the intrinsic interior of a convex set s is
equal to the intrinsic interior of s.
-/
theorem intrinsicInterior_intrinsicInterior [FiniteDimensional ℝ V] (hsc : Convex ℝ s) :
    intrinsicInterior ℝ (intrinsicInterior ℝ s) = intrinsicInterior ℝ s := by
  apply intrinsicInterior_subset.antisymm
  nth_rw 1 [intrinsicInterior]
  rw [intrinsicInterior, image_subset_iff]
  rw [affinespan_intrinsicInterior hsc]
  rw [Function.Injective.preimage_image Subtype.val_injective]
  simp [intrinsicInterior]

end affinespan


section Prolongation
/-
Let s be a non-empty convex subset. Then z ∈ ri s (intrinsic interior of C)
if and only if for every x ∈ s, there exists μ > 1 such that (1 - μ) • x + μ • z ∈ s.
-/

variable [NormedAddCommGroup V] [NormedSpace ℝ V] {s : Set V}

lemma prolongation_of_interior {x} (h : x ∈ interior s) :
    ∀ d , ∃ r > (0 : ℝ), (x + r • d) ∈ s := by
  intro d
  by_cases hd : d = 0
  · use 1; simp [hd, h]
    exact interior_subset h
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff] at h
  rcases h with ⟨t, ht, hts1, hts2⟩
  rw [Metric.isOpen_iff] at hts1
  obtain ⟨ε, hε, hε1⟩ := hts1 x hts2
  have dnorm : ‖d‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr hd
  use ε / (2 * ‖d‖); constructor; · positivity
  have : x + (ε / (2 * ‖d‖)) • d ∈  Metric.ball x ε := by
    refine add_mem_ball_iff_norm.mpr ?_
    rw [norm_smul]; field_simp; rw [abs_of_nonneg (a := ε) (by linarith)]
    rw [← mul_div, mul_comm 2, ← div_div ‖d‖, div_self dnorm];
    linarith
  exact ht (hε1 this)

lemma prolongation_of_interior' {z} (h : z ∈ interior s) :
    ∀ x, ∃ μ > (1 : ℝ), (1 - μ) • x + μ • z ∈ s := by
  intro x
  have ⟨r, hr⟩:= prolongation_of_interior h (z - x)
  use r + 1
  simp
  constructor
  · exact hr.1
  have : -(r • x) + (r + 1) • z = z + r • (z - x) := by
    rw [add_smul, smul_sub, add_sub, neg_add_eq_iff_eq_add,
      add_sub_cancel, add_comm, one_smul]
  simpa [this] using hr.2

theorem intrinsicInterior_forall_exist_of_intrinsicInterior {z : V}
    (hs : s.Nonempty) (hz : z ∈ intrinsicInterior ℝ s) :
    ∀ x ∈ s, ∃ μ > (1 : ℝ), (1 - μ) • x + μ • z ∈ s := by
  intro x hx
  rw [intrinsicInterior_equiv_pre ℝ hs] at hz
  let h := affSpanCoerce_pre ℝ hs
  let g := Function.invFun h

  have hgu (u) : g '' (h '' u) = u :=  Function.LeftInverse.image_image
    (Function.leftInverse_invFun <| affSpanCoerce_pre_Injective ℝ hs) u

  have hx' : g z ∈ interior (h ⁻¹' s) := by
    rw [← hgu (interior (h ⁻¹' s))]
    exact mem_image_of_mem g hz

  have hgx : h (g x) = x := inv_eq_self ℝ hs <| sub_range ℝ hs hx

  have hgz : h (g z) = z := inv_eq_self ℝ hs <| mem_range_of_mem_image _ _ hz

  have ⟨μ ,hu1, hu⟩:= prolongation_of_interior' hx' (g x)
  use μ ,hu1
  have : h ((1 - μ) • g x + μ • g z) ∈ h '' (⇑h ⁻¹' s) := mem_image_of_mem _ hu
  rwa [Convex.combo_affine_apply (by simp), hgx, hgz, ← pre_eq_image_preimage] at this

theorem intrinsicInterior_of_intrinsicClosure_of_intrinsicInterior
    (hsc : Convex ℝ s) {x z} (hx : x ∈ intrinsicInterior ℝ s) {μ : ℝ} (hμ1 : μ > 1)
    (hu : (1 - μ) • x + μ • z ∈ intrinsicClosure ℝ s) : z ∈ intrinsicInterior ℝ s := by
  let y := (1 - μ) • x + μ • z

  let t := 1 / μ
  have hz : z = (1 - t) • x + t • y := by
    field_simp [y, t]
    rw [← add_assoc, smul_smul, smul_smul, ← add_smul]
    field_simp

  apply openSegment_sub_intrinsicInterior ℝ hsc hx hu
  rw [openSegment_eq_image]
  nth_rw 2 [hz]
  apply mem_image_of_mem _ (mem_Ioo.mpr ?_)
  simpa [t] using ⟨by linarith, inv_lt_one_of_one_lt₀ hμ1⟩



theorem in_intrinsicInterior_of_intrinsicInterior
    (hsc : Convex ℝ s) {x z} (hx : x ∈ intrinsicInterior ℝ s) {μ : ℝ} (hμ1 : μ > 1)
    (hu : (1 - μ) • x + μ • z ∈ s) : z ∈ intrinsicInterior ℝ s := by
  apply intrinsicInterior_of_intrinsicClosure_of_intrinsicInterior hsc hx hμ1
  apply subset_intrinsicClosure hu


theorem intrinsicInterior_of_forall_exist
    {z : V} (hsc : Convex ℝ s) (hn : (intrinsicInterior ℝ s).Nonempty)
    (h :  ∀ x ∈ s, ∃ μ > (1 : ℝ), (1 - μ) • x + μ • z ∈ s) :
    z ∈ intrinsicInterior ℝ s := by
  have ⟨x, hx⟩ : ∃ x, x ∈ intrinsicInterior ℝ s := hn
  have ⟨μ , hμ1, hu⟩:= h x (intrinsicInterior_subset hx)
  exact in_intrinsicInterior_of_intrinsicInterior hsc hx hμ1 hu

/-
This theorem provides an equivalence condition for the intrinsic interior of a convex set s.
It states that a point z lies in the intrinsic interior of s if and only if for every x ∈ s,
there exists a μ > 1 such that the point (1 - μ) • x + μ • z lies in s.
-/
theorem intrinsicInterior_iff
    {z : V} (hs : Convex ℝ s)(hn : (intrinsicInterior ℝ s).Nonempty) :
    z ∈ intrinsicInterior ℝ s ↔ ∀ x ∈ s, ∃ μ > (1 : ℝ), (1 - μ) • x + μ • z ∈ s := by
  constructor
  · exact fun a x a_1 ↦ intrinsicInterior_forall_exist_of_intrinsicInterior
      (nonempty_of_mem a_1) a x a_1
  exact fun a ↦ intrinsicInterior_of_forall_exist hs hn a

end Prolongation

section

variable [NormedAddCommGroup V] [NormedSpace ℝ V] {s : Set V}

theorem intrinsicInterior_intrinsicClosure_sub_intrinsicInterior (h : Convex ℝ s)
    (hn : (intrinsicInterior ℝ s).Nonempty) :
    intrinsicInterior ℝ (intrinsicClosure ℝ s) ⊆  intrinsicInterior ℝ s := by
  intro z hz
  rw [intrinsicInterior_iff (convex_intrinsicClosure ℝ h) (nonempty_of_mem hz)] at hz
  have ⟨x, hx⟩ : ∃ x, x ∈ intrinsicInterior ℝ s := hn
  have ⟨μ , hμ1, hu⟩ := hz x (subset_intrinsicClosure <| intrinsicInterior_subset hx)
  exact intrinsicInterior_of_intrinsicClosure_of_intrinsicInterior h hx hμ1 hu

/-
If s is a convex set and the intrinsic interior of s is non-empty,
then the intrinsic interior of the intrinsic closure of s is
equal to the intrinsic interior of s.
-/
theorem intrinsicInterior_intrinsicClosure (h : Convex ℝ s) (hc : (intrinsicInterior ℝ s).Nonempty):
    intrinsicInterior ℝ (intrinsicClosure ℝ s) = intrinsicInterior ℝ s :=
  Set.Subset.antisymm (intrinsicInterior_intrinsicClosure_sub_intrinsicInterior h hc) <|
    intrinsicInterior_sub_intrinsicClosure_intrinsicInterior ℝ


end



section intrinsicInterior_closure_comm
/-
Convex analysis (Ralph Tyrell Rockafellar) thm6.3
This section prove that
for any convex set C, we have
1. cl(ri(C)) = cl(C)
2. ri(cl(C)) = ri(C)
3. If C_bar is nonempty convex set，the following conditions are equivalent:
  (i) C and C_bar have same intrinsicInterior
  (ii) C and C_bar have same intrinsicClosure
  (iii) ri(C) ⊆ C_bar ⊆ cl(C)
-/
section
variable (𝕜) [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [AddCommGroup V] [Module 𝕜 V]
  [TopologicalSpace V]
  [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V]
  [ContinuousSub V] [ContinuousAdd V]{s : Set V}

omit [TopologicalSpace 𝕜] [OrderTopology 𝕜] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V] [ContinuousSub V] [ContinuousAdd V] in
lemma in_affineSpan_openSegment {x y : V} (h : x ≠ y) :
    x ∈ affineSpan 𝕜 (openSegment 𝕜 x y) := by
  refine (mem_coe ..).mp ?_
  simp [affineSpan, spanPoints]
  simp [vectorSpan]

  let u := midpoint 𝕜 x y

  have hu : u ∈ openSegment 𝕜 x y :=
    mem_openSegment_of_ne_left_right (by simpa [u]) (by simpa [u])
      (midpoint_mem_segment x y)

  let z := midpoint 𝕜 x u

  have seg : segment 𝕜 x u ⊆ segment 𝕜 x y := by
    simpa [u] using  Convex.segment_subset  (convex_segment x y)
      (left_mem_segment 𝕜 x y) (midpoint_mem_segment x y)

  have hz : z ∈ openSegment 𝕜 x y := by
    refine mem_openSegment_of_ne_left_right (by simpa [z, u]) ?_ (seg <| midpoint_mem_segment x u)
    simp [z, u, midpoint_eq_smul_add]
    rw [smul_smul, smul_smul, ← add_assoc, ← add_smul, ← add_neg_eq_iff_eq_add, ← sub_eq_add_neg]
    nth_rw 1 [← one_smul 𝕜 y]
    rw [← sub_smul]
    norm_num
    rw [smul_right_inj (by norm_num)]
    exact h.symm

  let v := z -ᵥ u
  have hv : v ∈ Submodule.span 𝕜 (openSegment 𝕜 x y -ᵥ openSegment 𝕜 x y) :=
    Submodule.subset_span (vsub_mem_vsub hz hu)
  have huz : u + (x - z) ∈ openSegment 𝕜 x y := by
    simp [u, z, midpoint_eq_smul_add]
    rw [smul_smul, smul_smul, ← add_assoc, ← add_smul, ← sub_sub]
    nth_rw 3 [← one_smul 𝕜 x]
    rw [← sub_smul, sub_eq_add_neg, add_add_add_comm, ← add_smul, ← neg_smul, ← add_smul]
    norm_num
    refine mem_openSegment_iff_div.mpr ?_
    use (3 : 𝕜), (1 : 𝕜)
    norm_num

  use u + (x - z), huz, v, hv
  simp [v]
  rw [add_sub, add_sub, ← add_assoc, sub_add]
  simp

theorem  intrinsicClosure_openSegment {x y : V} (hn : x ≠ y) :
    y ∈ intrinsicClosure 𝕜 (openSegment 𝕜 x y) := by
  have hs : (openSegment 𝕜 x y).Nonempty := by
    use midpoint 𝕜 x y
    simp [openSegment, midpoint_eq_smul_add]
    use 2⁻¹, ?_, 2⁻¹,?_, ?_
    repeat norm_num
  rw [intrinsicClosure_equiv_pre 𝕜 hs]
  let h := affSpanCoerce_pre 𝕜 hs
  let g := Function.invFun h
  have hgx : h (g x) = x:= by
    apply inv_eq_self 𝕜 hs
    simp
    have b : x -ᵥ Exists.choose hs ∈ (affineSpan 𝕜 (openSegment 𝕜 x y)).direction := by
      refine (vsub_right_mem_direction_iff_mem ?hp x).mpr ?_
      refine mem_affineSpan 𝕜  hs.choose_spec
      exact in_affineSpan_openSegment 𝕜 hn
    use x - Exists.choose hs, b
    symm
    exact (eq_vadd_iff_vsub_eq x _ _).mpr rfl

  have hgy : h (g y) = y := by
    apply inv_eq_self 𝕜 hs
    simp
    have b : y -ᵥ Exists.choose hs ∈ (affineSpan 𝕜 (openSegment 𝕜 x y)).direction := by
      refine (vsub_right_mem_direction_iff_mem ?hp y).mpr ?_
      rw [openSegment_symm]
      exact in_affineSpan_openSegment 𝕜 hn.symm
    use y - Exists.choose hs, b
    symm
    exact (eq_vadd_iff_vsub_eq y _ _).mpr rfl

  have : openSegment 𝕜 x y = h '' (openSegment 𝕜 (g x) (g y)) := by
    simp_rw [image_openSegment 𝕜 _ (g x) (g y), hgx, hgy]

  have : h ⁻¹' openSegment 𝕜 x y = openSegment 𝕜 (g x) (g y) := by
    simp_rw [this]
    apply preimage_image_eq _
    exact affSpanCoerce_pre_Injective 𝕜 hs

  show y ∈ h '' (closure (h ⁻¹' _))

  simp_rw [this]

  apply (image_mono segment_subset_closure_openSegment)
  use (g y), right_mem_segment 𝕜 (g x) (g y), hgy

theorem segment_subset_intrinsicClosure_openSegment {x y : V}:
    segment 𝕜 x y ⊆ intrinsicClosure 𝕜 (openSegment 𝕜 x y) := by
  by_cases hn : x = y
  · simp [hn]
  apply Convex.segment_subset (convex_intrinsicClosure 𝕜 <| convex_openSegment x y)
  · rw [openSegment_symm]
    exact intrinsicClosure_openSegment 𝕜 fun a ↦ hn a.symm
  exact intrinsicClosure_openSegment 𝕜 hn

/-
The intrinsic closure of the interior of a convex set s equals the intrinsic closure of s.
-/
theorem intrinsicClosure_intrinsicInterior (h : Convex 𝕜 s)
      (hc : (intrinsicInterior 𝕜 s).Nonempty) :
    intrinsicClosure 𝕜 (intrinsicInterior 𝕜 s) = intrinsicClosure 𝕜 s := by
  apply Set.Subset.antisymm (intrinsicClosure_mono intrinsicInterior_subset)
  by_cases hs : Set.Nonempty s
  · intro x h2
    apply intrinsicClosure_mono (openSegment_sub_intrinsicInterior 𝕜 h hc.choose_spec h2)
    apply segment_subset_intrinsicClosure_openSegment
    exact right_mem_segment 𝕜 (Exists.choose hc) x
  simp [not_nonempty_iff_eq_empty.1 hs]

end

variable [NormedAddCommGroup V] [NormedSpace ℝ V] {s : Set V}

theorem closure_intrinsicInterior [FiniteDimensional ℝ V] (h : Convex ℝ s) :
    closure (intrinsicInterior ℝ s) = closure s := by
  by_cases hs : Set.Nonempty s
  · rw [← intrinsicClosure_eq_closure ℝ s, ← intrinsicClosure_eq_closure ℝ _]
    exact intrinsicClosure_intrinsicInterior ℝ h <|
      (intrinsicInterior_nonempty h).mpr hs
  simp [not_nonempty_iff_eq_empty.1 hs]

theorem intrinsicInterior_closure [FiniteDimensional ℝ V] (h : Convex ℝ s) :
    intrinsicInterior ℝ (closure s) = intrinsicInterior ℝ s := by
  by_cases hs : s.Nonempty
  · rw [← intrinsicClosure_eq_closure ℝ s]
    exact intrinsicInterior_intrinsicClosure h <|
      (intrinsicInterior_nonempty h).mpr hs
  simp [not_nonempty_iff_eq_empty.mp hs]

/-
In finite-dimensional space, the following conditions are equivalent:
	1.	Closure of s equals closure of t.
	2.	Intrinsic interior of s equals intrinsic interior of t.
	3.	intrinsicInterior ℝ s ⊆ t and t ⊆ closure s.
-/
theorem intrinsicInterior_tfae [FiniteDimensional ℝ V] (hs : Convex ℝ s) {t} (ht : Convex ℝ t) :
  [closure s = closure t, intrinsicInterior ℝ s = intrinsicInterior ℝ t,
  intrinsicInterior ℝ s ⊆ t ∧ t ⊆ closure s].TFAE :=  by
  tfae_have  1 → 2 := by
    intro x
    rw[← intrinsicInterior_closure hs,x,intrinsicInterior_closure ht]
  tfae_have  2 → 1 := by
    intro x
    rw[← closure_intrinsicInterior ht,←x,closure_intrinsicInterior hs]
  tfae_have  3 → 1 := by
    rintro ⟨a, b⟩
    apply Subset.antisymm ((closure_intrinsicInterior hs) ▸ closure_mono a)
    nth_rw 2 [← closure_closure]
    exact closure_mono b
  tfae_have  2 → 3 := by
    intro x
    constructor
    rw [x]
    exact intrinsicInterior_subset
    have re := tfae_2_to_1
    apply re at x
    simpa [x] using subset_closure
  tfae_finish

end intrinsicInterior_closure_comm

section intersection

/-
If {C_i}_I is convex sets，and ⋂ i, (intrinsicInterior ℝ (C_i)) ≠ ∅
1. cl(⋂ C_i) = ⋂ cl(C_i)
2. If I is finite，then ri(⋂ C_i) = ⋂ ri(C_i)
-/

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Sort*} {s : ι → Set V}

theorem iIntersection_closure_sub_closure_iIntersection
    (h : ∀ (i : ι), Convex ℝ (s i))
    (hinter : ∃ x, ∀ i, x ∈ intrinsicInterior ℝ (s i)) :
    ⋂ i, closure (s i) ⊆  closure (⋂ i, s i) := by
  obtain ⟨x, hx⟩ := hinter
  have h₀ : closure (⋂ i, intrinsicInterior ℝ (s i)) ⊆ closure (⋂ i, s i) :=
    closure_mono (iInter_mono'' (fun i => intrinsicInterior_subset))
  have h₁ : ⋂ i, closure (s i) ⊆  closure ( ⋂ i, intrinsicInterior ℝ (s i) ) := by
    rintro y hy; rw[Set.mem_iInter] at hy
    have h₂ : openSegment ℝ x y ⊆ ⋂ i, intrinsicInterior ℝ (s i) := by
        simp [subset_iInter]
        intro i
        apply openSegment_sub_intrinsicInterior ℝ (h i) (hx i) --(hy i)
        rw [intrinsicClosure_eq_closure ℝ _]
        exact hy i
    apply closure_mono h₂
    apply segment_subset_closure_openSegment
    exact right_mem_segment ℝ x y
  exact fun _ a_1 => h₀ (h₁ a_1)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
theorem closure_iIntersection_sub_iIntersection_closure:
  closure (⋂ i, s i) ⊆ ⋂ i, closure (s i) := by
  apply closure_minimal _ (isClosed_iInter <| fun i ↦ isClosed_closure)
  intro x hx
  rw [mem_iInter] at hx
  exact mem_iInter.mpr <| fun i => subset_closure (hx i)

/-
The closure of the intersection of convex sets equals
the closure of the intersection of their intrinsic interiors.
-/
theorem iIntersection_closure_eq_intrinsicInterior_closure
    (h : ∀ (i : ι), Convex ℝ (s i))
    (hinter : ∃ x, ∀ i, x ∈ intrinsicInterior ℝ (s i)) :
    ⋂ i, closure (s i) = closure (⋂ i, s i) :=
  Subset.antisymm (iIntersection_closure_sub_closure_iIntersection h hinter) <|
    closure_iIntersection_sub_iIntersection_closure

lemma intrinsicInterior_tfae13 {s t : Set V}(hs : Convex ℝ s) (ht : Convex ℝ t) :
    closure s = closure t ↔ intrinsicInterior ℝ s ⊆ t ∧ t ⊆ closure s := by
   apply (intrinsicInterior_tfae hs ht) <;> simp

lemma from_closure_to_interior_subset {s t : Set V} (hs : Convex ℝ s) (ht : Convex ℝ t)
  (h_closure_eq : closure s= closure t) : intrinsicInterior ℝ s ⊆ t :=
    ((intrinsicInterior_tfae13 hs ht).1 h_closure_eq).1

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
lemma exist_of_inter_ne_empty (hinter : ⋂ i, (s i) ≠ ∅) :
    ∃ x, ∀ (i : ι), x ∈ s i :=
  nonempty_iInter.mp <| nonempty_iff_ne_empty.mpr hinter

theorem intrinsicInterior_iIntersection_sub_iIntersection_intrinsicInterior
    (h : ∀ (i : ι), Convex ℝ (s i))
    (hinter : ⋂ i, (intrinsicInterior ℝ (s i)) ≠ ∅) :
  intrinsicInterior ℝ (⋂ i, s i) ⊆ ⋂ i, intrinsicInterior ℝ (s i):= by
  have  hr : ∀ (i : ι), Convex ℝ (intrinsicInterior ℝ (s i)) :=
    fun i => convex_intrinsicInterior ℝ (h i)
  have ri_inter :  ⋂ i, intrinsicInterior ℝ (intrinsicInterior ℝ (s i)) ≠ ∅ := by
    rw [iInter_congr fun i ↦ intrinsicInterior_intrinsicInterior (h i)]; exact hinter
  have ht  :⋂ i, closure (s i) = closure (⋂ i, s i):=
    iIntersection_closure_eq_intrinsicInterior_closure h  (exist_of_inter_ne_empty hinter)
  have hrt : ⋂ i, closure (intrinsicInterior ℝ (s i) )= closure (⋂ i,intrinsicInterior ℝ (s i)) :=
    iIntersection_closure_eq_intrinsicInterior_closure hr (exist_of_inter_ne_empty ri_inter)
  apply from_closure_to_interior_subset (convex_iInter h) (convex_iInter hr)
  rw [ht.symm , hrt.symm, iInter_congr fun i ↦ closure_intrinsicInterior (h i)]

omit [FiniteDimensional ℝ V] in
theorem iIntersection_intrinsicInterior_sub_intrinsicInterior_iIntersection
    [Finite ι] :
    ⋂ i, intrinsicInterior ℝ (s i) ⊆ intrinsicInterior ℝ (⋂ i, s i) := by
  intro x hx
  have xinaff : x ∈ affineSpan ℝ (⋂ i, s i) :=
    mem_affineSpan ℝ <| mem_iInter.2 <| fun i ↦ intrinsicInterior_subset ((mem_iInter.1 hx) i)
  simp only [mem_intrinsicInterior, Subtype.exists, exists_and_right, exists_eq_right]
  let f : (affineSpan ℝ (⋂ i, s i)) → V := Subtype.val
  have inter_sub : ⋂ i, f ⁻¹' (s i) ⊆  (f ⁻¹' ⋂ i, s i) := by
    rw[Set.preimage_iInter]
  simp at hx
  use xinaff
  apply interior_mono inter_sub
  rw [interior_iInter_of_finite]
  simp only [mem_iInter]
  intro i
  let g : (affineSpan ℝ (s i)) → V := Subtype.val
  let u : (affineSpan ℝ (⋂ i, s i)) → (affineSpan ℝ (s i)) :=
    fun x => ⟨x, (affineSpan_mono _  <| iInter_subset_of_subset i fun _ a ↦ a) x.2⟩
  let g_u : (affineSpan ℝ (⋂ i, s i)) → V := g ∘ u
  have hug' : f = g_u := by
    simp [g_u, u, g, f]
    exact rfl
  show _ ∈ interior (f ⁻¹' s i)
  rw [hug', preimage_comp]
  apply preimage_interior_subset_interior_preimage
  · apply (Continuous.subtype_mk (Continuous.subtype_val continuous_id'))
  simpa [u] using (hx i).2

/-
For a finite index set, the intrinsic interior of the intersection of convex sets
equals the intersection of their intrinsic interiors.
-/
theorem iIntersection_intrinsicInterior_eq_intrinsicInterior_iIntersection [Finite ι]
    (h : ∀ (i : ι), Convex ℝ (s i))
    (hinter : ⋂ i, (intrinsicInterior ℝ (s i)) ≠ ∅):
    ⋂ i, intrinsicInterior ℝ (s i) = intrinsicInterior ℝ (⋂ i, s i) :=
  Subset.antisymm iIntersection_intrinsicInterior_sub_intrinsicInterior_iIntersection <|
  intrinsicInterior_iIntersection_sub_iIntersection_intrinsicInterior h hinter

end intersection
