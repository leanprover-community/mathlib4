import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! Existence of a Riemannian metric, using partitions of unity

Using a partition of unity, we prove that every finite-dimensional smooth vector bundle
admits a smooth Riemannian metric.
TODO: this should work for C^n; prove the same for topological bundles and add it there
  also deduce that every manifold can be made Riemannian...

-/

open Bundle ContDiff Manifold

-- Let E be a smooth vector bundle over a manifold E

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  [IsManifold IB n B] [ContMDiffVectorBundle n F E IB]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable (F E) in
/-- The set of bounded bi-continuous ℝ-bilinear maps from `F` to `ℝ` which agree with the given
inner product structure on `E`, when read through the trivialisations of `E`. -/
def mapsMatchingInner (x : B) : Set (F →L[ℝ] F →L[ℝ] ℝ) :=
  letI t := trivializationAt F E x
  {φ | ∀ v w : E x, φ (t v).2 (t w).2 = ⟪v, w⟫ }

omit [VectorBundle ℝ F E] in
lemma convex_mapsMatchingInner (x : B) : Convex ℝ (mapsMatchingInner F E x) := by
  intro φ hφ ψ hψ r s hr hs hrs
  simp only [mapsMatchingInner, Set.mem_setOf] at hφ hψ ⊢
  intro v w
  simp [hφ v w, hψ v w]
  grind

variable (F E) in
def RMetric_local (x : B) : F →L[ℝ] F →L[ℝ] ℝ := sorry

lemma hloc (x : B) :
    ∃ U ∈ nhds x, ∃ g,
      ContMDiffOn IB 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) ∞ g U ∧ ∀ y ∈ U, g y ∈ mapsMatchingInner F E y := by
  letI t := trivializationAt F E x
  have : t.baseSet ∈ nhds x := sorry
  use t.baseSet, this, (fun x ↦ RMetric_local F x)
  refine ⟨?_, ?_⟩
  · sorry
  · sorry

variable [SigmaCompactSpace B] [T2Space B] [IsManifold IB ∞ B] [FiniteDimensional ℝ EB]

variable (E F IB) in
noncomputable def RMetric_aux : C^∞⟮IB, B; 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ), F →L[ℝ] F →L[ℝ] ℝ⟯ :=
  Classical.choose <|
    exists_contMDiffOn_forall_mem_convex_of_local (n := (⊤ : ℕ∞)) (I := IB)
    (t := fun x ↦ mapsMatchingInner F E x) convex_mapsMatchingInner hloc

variable (E F IB) in
/-- An arbitrary choice of bundle metric on `E`, which is smooth in the fibre. -/
def RMetric [SigmaCompactSpace B] [T2Space B] [IsManifold IB ∞ B] [FiniteDimensional ℝ EB] :
    Π (x : B), E x →L[ℝ] E x →L[ℝ] ℝ := by
  let aux := RMetric_aux IB F E
  intro x
  let aux' := aux x
  -- TODO: translate everything back (and prove this preserves smoothness...)
  sorry

lemma rMetric_contMDiff [FiniteDimensional ℝ EB] :
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (RMetric IB F E b)) :=
  sorry

lemma rMetric_eq (x : B) (v w : E x) : ⟪v, w⟫ = (RMetric IB F E) x v w := sorry

/-- Every `C^n` vector bundle whose fibre admits a `C^n` partition of unity
is a `C^n` Riemannian vector bundle. (The Lean statement assumes an inner product on each fibre
already, which is why there are no other assumptions yet??) -/
lemma ContDiffVectorBundle.isContMDiffRiemannianBundle : IsContMDiffRiemannianBundle IB n F E :=
  ⟨RMetric IB F E, rMetric_contMDiff, fun x v w ↦ rMetric_eq x v w⟩
