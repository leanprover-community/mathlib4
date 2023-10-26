/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Geometry.Manifold.DiffeomorphOn
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners

/-!
# Charts are local diffeos
-/

open Function Manifold Set SmoothManifoldWithCorners TopologicalSpace Topology
set_option autoImplicit false

variable
  -- Let `M` be a smooth manifold over the pair `(E, H)`. xxx: remove smoothness
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]
  -- Let `N` be a smooth manifold over the pair `(F, G)`.
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type*} [TopologicalSpace G]
  (J : ModelWithCorners ℝ F G) {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [SmoothManifoldWithCorners J N]

-- proper statements belonging here: the remainder should eventually move to LocalDiffeomorph
-- on any topological manifold (any charted space??!!), charts are structomorphisms

-- if M is a C^m manifold, charts are C^m. (are they even smooth? do we require M to be C^m? we do, though, because of transition maps)

-- if M is a C^m manifold, charts are DiffeomorphOn (easy)
-- cor: differentials of charts are linear isos
-- cor: differentials of charts are bijective

-- add to Init.Function
lemma bijective_iff_inverses {X Y : Type*} {f : X → Y} {g : Y → X}
    (h1 : LeftInverse g f) (h2 : LeftInverse f g) : Bijective f :=
  ⟨h1.injective, h2.surjective⟩

/-- A local diffeomorphism has bijective differential at each point. -/
lemma DiffeomorphOn.differential_bijective {r : ℕ} (hr : 1 ≤ r) {x : M}
    (h : DiffeomorphOn I J M N r) (hx : x ∈ h.source) : Bijective (mfderiv I J h.toFun x) := by
  let aux := h.differential_toContinuousLinearEquiv hr hx
  have h : aux.toFun = mfderiv I J h.toFun x := sorry -- should be obvious!
  rw [← h]
  exact bijective_iff_inverses aux.left_inv aux.right_inv

/-- A diffeomorphism has bijective differential at each point. -/
lemma Diffeomorph.differential_bijective {r : ℕ} (hr : 1 ≤ r) (f : Diffeomorph I J M N r) {x : M} :
    Bijective (mfderiv I J f.toFun x) := by
  -- FIXME: `(f.toDiffeomorphOn).differential_bijective hr (by exact trivial)` or so should suffice.
  -- These are trivial.
  have : f.toLocalEquiv.source = univ := rfl
  have t : x ∈ f.toLocalEquiv.source := by exact trivial
  -- However, I need to hese statements, and to rewrite by them.
  have : x ∈ (toDiffeomorphOn I J M N (↑r) f).toLocalHomeomorph.toLocalEquiv.source := sorry
  have h : (toDiffeomorphOn I J M N (↑r) f).toLocalHomeomorph.toLocalEquiv = f.toLocalEquiv := sorry
  apply h ▸ (f.toDiffeomorphOn).differential_bijective hr this

-- auxiliary results, not needed for my proof, but perhaps still useful
section aux
-- TODO: PRed to Data.Set.Image, drop once that is merged
/-- Variant of `image_congr`, for one function being the identity. -/
theorem image_congr'' {α β : Type*} {f : α → β} {g : β → α} {s : Set α}
    (h : ∀ x : α, x ∈ s → (g ∘ f) x = x) : g ∘ f '' s = s := by
  rw [image_congr h, image_id']

-- TODO: I feel this should be in mathlib already, but exact? cannot find it...
lemma LocalHomeomorph.image_symm_target_eq_source {e : LocalHomeomorph M H} :
    e.invFun '' e.target = e.source := by
  rw [← e.toLocalEquiv.image_source_eq_target, ← image_comp]
  exact image_congr'' (fun x hx ↦ e.left_inv' hx)

-- is this worth being a separate lemma?
lemma LocalHomeomorph.isBLA {e : LocalHomeomorph M H} : IsOpen (e.invFun '' e.target) := by
  rw [e.image_symm_target_eq_source]
  exact e.open_source

-- is this worth being a separate lemma in mathlib?
lemma LocalHomeomorph.asdf {e : LocalHomeomorph M H} {x : M} (hx : x ∈ e.source) :
    e.source ∈ 𝓝 x := by sorry
end aux
