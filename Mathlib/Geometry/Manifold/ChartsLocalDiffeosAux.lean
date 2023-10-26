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


-- similar to `fderivWithin_of_open`; seems missing
lemma hasFDerivWithinAt_of_open {s : Set E} {x : E} (h : IsOpen s) (hx : x ∈ s) {f : E → F}
    {f' : E →L[ℝ] F} : HasFDerivWithinAt f f' s x ↔ HasFDerivAt f f' x := by
  simp only [HasFDerivAt, HasFDerivWithinAt]
  rw [IsOpen.nhdsWithin_eq h hx]

-- I have not compared FDeriv.Basic to MFDeriv and added all analogous lemmas.
-- analogous to `fderivWithin_of_mem_nhds`
theorem mfderivWithin_of_mem_nhds {f : M → N} {s : Set M} {x : M} (h : s ∈ 𝓝 x) :
    mfderivWithin I J f s x = mfderiv I J f x := by
  rw [← mfderivWithin_univ, ← univ_inter s, mfderivWithin_inter h]

-- similar to `fderivWith_of_open`
lemma mfderivWithin_of_open {s : Set M} {x : M} (hs : IsOpen s) (hx : x ∈ s) {f : M → N} :
    mfderivWithin I J f s x = mfderiv I J f x :=
  mfderivWithin_of_mem_nhds I J (hs.mem_nhds hx)

-- analogous to `mfderivWithin_eq_mfderiv`
theorem mfderivWithin_eq_mfderiv {s : Set M} {x : M} {f : M → N}
    (hs : UniqueMDiffWithinAt I s x) (h : MDifferentiableAt I J f x) :
    mfderivWithin I J f s x = mfderiv I J f x := by
  rw [← mfderivWithin_univ]
  exact mfderivWithin_subset (subset_univ _) hs h.mdifferentiableWithinAt

-- TODO: PRed to Data.Set.Image, drop once that is merged
/-- Variant of `image_congr`, for one function being the identity. -/
theorem image_congr'' {α β : Type*} {f : α → β} {g : β → α} {s : Set α}
    (h : ∀ x : α, x ∈ s → (g ∘ f) x = x) : g ∘ f '' s = s := by
  rw [image_congr h, image_id']

-- xxx: all the toFun and invFun should not be needed. want to write h.symm instead!
/-- The differential of a  local diffeomorphism is a linear isomorphism
  at each point in its source. -/
noncomputable def DiffeomorphOn.differential_toContinuousLinearEquiv {r : ℕ} (hr : 1 ≤ r) {x : M}
    (h : DiffeomorphOn I J M N r) (hx : x ∈ h.source) :
    ContinuousLinearEquiv (RingHom.id ℝ) (TangentSpace I x) (TangentSpace J (h.toFun x)) := by
  let y := h.toFun x
  have hy : y ∈ h.target := h.toLocalEquiv.mapsTo hx
  let A := mfderiv I J h.toFun x
  let B := mfderiv J I h.invFun (h.toFun x)

  have hr : 1 ≤ (r : ℕ∞) := Nat.one_le_cast.mpr (Nat.one_le_of_lt hr)
  -- FUTURE: can the `differentiability` tactic show this?
  have hgat : MDifferentiableAt J I h.invFun y :=
    (h.contMDiffAt_symm (h.toLocalEquiv.mapsTo hx)).mdifferentiableAt hr
  have hfat : MDifferentiableAt I J h.toFun x :=
    (h.contMDiffAt hx).mdifferentiableAt hr
  have inv1 : B.comp A = ContinuousLinearMap.id ℝ (TangentSpace I x) := calc B.comp A
    _ = mfderiv I I (h.invFun ∘ h.toFun) x := (mfderiv_comp x hgat hfat).symm
    _ = mfderivWithin I I (h.invFun ∘ h.toFun) h.source x :=
      (mfderivWithin_of_open I I h.open_source hx).symm
    _ = mfderivWithin I I id h.source x :=
      mfderivWithin_congr (h.open_source.uniqueMDiffWithinAt hx) h.left_inv' (h.left_inv' hx)
    _ = mfderiv I I id x := mfderivWithin_of_open I I h.open_source hx
    _ = ContinuousLinearMap.id ℝ (TangentSpace I x) := mfderiv_id I
  have inv2 : A.comp B = ContinuousLinearMap.id ℝ (TangentSpace J (h.toFun x)) := calc A.comp B
    _ = mfderiv J J (h.toFun ∘ h.invFun) y := by
          -- Use the chain rule: rewrite the base point (I ∘ e ∘ e.invFun ∘ I.invFun) x = x, ...
          rw [← (h.left_inv' hx)] at hfat
          -- ... but also the points x and y under the map.
          -- for some reason, cannot plug this in directly
          have : (LocalEquiv.invFun h.toLocalEquiv y) = x := (h.left_inv' hx)
          exact (this ▸ (mfderiv_comp y hfat hgat)).symm
    _ = mfderivWithin J J (h.toFun ∘ h.invFun) h.target y :=
      (mfderivWithin_of_open J J h.open_target hy).symm
    _ = mfderivWithin J J id h.target y :=
      mfderivWithin_congr (h.open_target.uniqueMDiffWithinAt hy) h.right_inv' (h.right_inv' hy)
    _ = mfderiv J J id y := mfderivWithin_of_open J J h.open_target hy
    _ = ContinuousLinearMap.id ℝ (TangentSpace J y) := mfderiv_id J

  have h1 : Function.LeftInverse B A := sorry -- TODO: should be obvious from inv1
  have h2 : Function.RightInverse B A := sorry -- same here
  exact {
    toFun := A
    invFun := B
    left_inv := h1
    right_inv := h2
    continuous_toFun := A.cont
    continuous_invFun := B.cont
    map_add' := fun x_1 y ↦ ContinuousLinearMap.map_add A x_1 y
    map_smul' := by intros; simp
  }

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
