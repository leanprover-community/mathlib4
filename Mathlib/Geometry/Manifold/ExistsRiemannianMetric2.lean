/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! ## Existence of a Riemannian bundle metric

Using a partition of unity, we prove that every finite-dimensional smooth vector bundle
admits a smooth Riemannian metric.
Second attempt.

## TODO
- this should work for C^n; prove the same for topological bundles and add it there
- also deduce that every manifold can be made Riemannian...

-/

open Bundle ContDiff Manifold

-- Let E be a smooth vector bundle over a manifold E

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  [IsManifold IB n B] [ContMDiffVectorBundle n F E IB]

section

variable (E) in
/-- This is the bundle `Hom_ℝ(E, T)`, where `T` is the rank one trivial bundle over `B`. -/
private def V : (b : B) → Type _ := (fun b ↦ E b →L[ℝ] Trivial B ℝ b)

noncomputable instance : (x : B) → TopologicalSpace (V E x) := by
  unfold V
  infer_instance

noncomputable instance : (x : B) → AddCommGroup (V E x) := by
  unfold V
  infer_instance

noncomputable instance (x : B) : Module ℝ (V E x) := by
  unfold V
  infer_instance

noncomputable instance : TopologicalSpace (TotalSpace (F →L[ℝ] ℝ) (V E)) := by
  unfold V
  infer_instance

noncomputable instance : FiberBundle (F →L[ℝ] ℝ) (V E) := by
  unfold V
  infer_instance

noncomputable instance : VectorBundle ℝ (F →L[ℝ] ℝ) (V E) := by
  unfold V
  infer_instance

noncomputable instance : ContMDiffVectorBundle n (F →L[ℝ] ℝ) (V E) IB := by
  unfold V
  infer_instance

instance (x : B) : ContinuousAdd (V E x) := by
  unfold V
  infer_instance

instance (x : B) : ContinuousSMul ℝ (V E x) := by
  unfold V
  infer_instance

instance (x : B) : IsTopologicalAddGroup (V E x) := by
  unfold V
  infer_instance

example : ContMDiffVectorBundle n (F →L[ℝ] F →L[ℝ] ℝ) (fun b ↦ E b →L[ℝ] V E b) IB :=
  ContMDiffVectorBundle.continuousLinearMap (IB := IB) (n := n)
    (F₁ := F) (E₁ := E) (F₂ := F →L[ℝ] ℝ) (E₂ := V E)

variable (E) in
/-- The real vector bundle `Hom(E, Hom(E, T)) = Hom(E, V)`, whose fiber at `x` is
(equivalent to) the space of continuous real bilinear maps `E x → E x → ℝ`. -/
private def W : (b : B) → Type _ := fun b ↦ E b →L[ℝ] V E b

noncomputable instance (x : B) : AddCommGroup (W E x) := by
  unfold W
  infer_instance

noncomputable instance (x : B) : Module ℝ (W E x) := by
  unfold W
  infer_instance

noncomputable instance : TopologicalSpace (TotalSpace (F →L[ℝ] F →L[ℝ] ℝ) (W E)) := by
  unfold W
  infer_instance

noncomputable instance (x : B) : TopologicalSpace (W E x) := by
  unfold W
  infer_instance

noncomputable instance : FiberBundle (F →L[ℝ] F →L[ℝ] ℝ) (W E) := by
  unfold W
  infer_instance

noncomputable instance : VectorBundle ℝ (F →L[ℝ] F →L[ℝ] ℝ) (W E) := by
  unfold W
  infer_instance

noncomputable instance : ContMDiffVectorBundle n (F →L[ℝ] F →L[ℝ] ℝ) (W E) IB := by
  unfold W
  infer_instance

end

variable (E) in
/-- The first condition imposed on sections of `W`: they should give rise to a symmetric
pairing on each fibre `E x`. -/
private def condition1 (x : B) : Set (E x →L[ℝ] E x →L[ℝ] ℝ) :=
  {φ | ∀ v w : E x, φ v w = φ w v}

variable (E) in
/-- The second condition imposed on sections of `W`: they should give rise to a positive definite
pairing on each fibre `E x`. -/
private def condition2 (x : B) : Set (E x →L[ℝ] E x →L[ℝ] ℝ) :=
  {φ | ∀ v : E x, v ≠ 0 → 0 < φ v v}

omit [TopologicalSpace B] in
lemma convex_condition1 (x : B) : Convex ℝ (condition1 E x) := by
  intro φ hφ ψ hψ s t hs ht hst v w
  simp [hφ v w, hψ v w]

omit [TopologicalSpace B] in
lemma convex_condition2 (x : B) : Convex ℝ (condition2 E x) := by
  unfold condition2
  intro φ hφ ψ hψ s t hs ht hst
  intro v hv
  rw [Set.mem_setOf] at hφ hψ
  have aux := Convex.min_le_combo ((φ v) v) ((ψ v) v) hs ht hst
  have : 0 < min ((φ v) v) ((ψ v) v) := lt_min (hφ v hv) (hψ v hv)
  simpa using gt_of_ge_of_gt aux this

variable (E) in
/-- Conditions imposed on sections of `W`: they should give rise to a positive definite symmetric
pairing on each fibre `E x`. -/
def condition (x : B) : Set (W E x) := by
  unfold W V Bundle.Trivial
  exact condition1 E x ∩ condition2 E x

omit [TopologicalSpace B] in
lemma convex_condition (x : B) : Convex ℝ (condition E x) :=
  Convex.inter (convex_condition1 x) (convex_condition2 x)

variable [FiniteDimensional ℝ EB] [IsManifold IB ∞ B] [SigmaCompactSpace B] [T2Space B]

section extend

-- copy-paste extend from my branch and its smoothness; sorry those, then use them!

-- Copied from #26221 (in `LocalFrame.lean`)
noncomputable def localExtensionOn {ι : Type*} (b : Module.Basis ι ℝ F)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F E → B)) [MemTrivializationAtlas e]
    (x : B) (v : E x) : (x' : B) → E x' :=
  sorry


-- variable (F) in
-- --omit [IsManifold I 0 M] in
-- lemma contMDiffOn_localExtensionOn [FiniteDimensional ℝ F] {ι : Type*} (b : Module.Basis ι ℝ F)
--     (e : Trivialization F (TotalSpace.proj : TotalSpace F E → B)) [MemTrivializationAtlas e]
--     {x : B} (hx : x ∈ e.baseSet) (v : E x) :
--     ContMDiffOn IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
--       (fun x' ↦ TotalSpace.mk' F x' (localExtensionOn b e x v x')) [e.baseSet] := by
--   sorry

end extend

#exit

-- TODO: construct a local section which is smooth in my coords,
-- and has all the definiteness properties I'll want later!
variable (E) in
def local_section_at (x₀ : B) : (x : B) → W E x := sorry

variable (E F) in
lemma contMDiff_localSection (x₀ : B) :
    letI t := trivializationAt F E x₀
    ContMDiffOn IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (local_section_at E x₀ x)) t.baseSet :=
  sorry

-- MAYBE: also make a definition nhd, which is the nhd on which local_section_at stays pos. def.
lemma is_good_localSection (x₀ : B) :
    ∀ y ∈ (trivializationAt F E x₀).baseSet, local_section_at E x₀ y ∈ condition E y := by
  intro y hy
  unfold condition
  simp only [id_eq]
  erw [Set.mem_setOf]
  refine ⟨?_, ?_⟩
  · sorry -- symmetry
  · sorry -- pos. definite

lemma hloc_TODO (x₀ : B) :
    ∃ U_x₀ ∈ nhds x₀, ∃ s_loc : (x : B) → W E x,
      ContMDiffOn IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
        (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (s_loc x)) U_x₀ ∧
      ∀ y ∈ U_x₀, s_loc y ∈ condition E y := by
  letI t := trivializationAt F E x₀
  have := t.open_baseSet.mem_nhds <| FiberBundle.mem_baseSet_trivializationAt' x₀
  use t.baseSet, this, local_section_at E x₀
  exact ⟨contMDiff_localSection F E x₀, is_good_localSection x₀⟩

variable (E F IB) in
/-- Key step in the construction of a Riemannian metric on `E`: we construct a smooth section
of the bundle `W = Hom(E, Hom(E, T))` with the right properties (translating into symmetric
and positive definiteness of the resulting metric. -/
noncomputable def foo_aux : Cₛ^∞⟮IB; F →L[ℝ] F →L[ℝ] ℝ, W E⟯ :=
  Classical.choose <|
    exists_contMDiffOn_section_forall_mem_convex_of_local IB (V := W E) (n := (⊤ : ℕ∞))
      (condition E) convex_condition hloc_TODO

variable (E F IB) in
lemma foo_aux_prop (x₀ : B) : foo_aux IB F E x₀ ∈ condition E x₀ := by
  apply Classical.choose_spec <|
    exists_contMDiffOn_section_forall_mem_convex_of_local IB (V := W E) (n := (⊤ : ℕ∞))
      (condition E) convex_condition hloc_TODO

-- In what generality does this hold?
lemma aux_special (G : Type*) [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (φ : G →L[ℝ] G →L[ℝ] ℝ) (hpos : ∀ v : G, v ≠ 0 → 0 < φ v v) :
    Bornology.IsVonNBounded ℝ {v | (φ v) v < 1} := by
  -- Proof sketch: choose a basis {b_i} of G.
  -- Each `φ b_i b_i` is non-zero by hypothesis, hence has positive norm.
  -- By finite-dimensionality of `G`, we have `0 < r := min ‖φ b_i b_i‖`,
  -- thus B(r, 0) is contained in the image of the unit ball under v ↦ φ v v.
  sorry

-- TODO: is this version also true?
lemma aux_special2 (G : Type*) [AddCommGroup G] [TopologicalSpace G] [Module ℝ G]
    [FiniteDimensional ℝ G]
    (φ : G →L[ℝ] G →L[ℝ] ℝ) (hpos : ∀ v : G, v ≠ 0 → 0 < φ v v) :
    Bornology.IsVonNBounded ℝ {v | (φ v) v < 1} := by
  sorry

-- TODO: is the finite-dimensionality actually required?
noncomputable def foo [∀ x, FiniteDimensional ℝ (E x)] : ContMDiffRiemannianMetric IB ∞ F E where
  inner := foo_aux IB F E
  symm b := (foo_aux_prop IB F E b).1
  pos b := (foo_aux_prop IB F E b).2
  isVonNBounded b := aux_special2 (E b) (foo_aux IB F E b) (foo_aux_prop IB F E b).2
  contMDiff := (foo_aux IB F E).contMDiff

-- /-- Every `C^n` vector bundle whose fibre admits a `C^n` partition of unity
-- is a `C^n` Riemannian vector bundle. (The Lean statement assumes an inner product on each fibre
-- already, which is why there are no other assumptions yet??) -/
-- lemma ContDiffVectorBundle.isContMDiffRiemannianBundle : IsContMDiffRiemannianBundle IB n F E :=
--   ⟨RMetric IB E, rMetric_contMDiff, fun x v w ↦ rMetric_eq x v w⟩
