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

-- similar to `fderivWithin_of_open`; seems missing
lemma hasFDerivWithinAt_of_open {s : Set E} {x : E} (h : IsOpen s) (hx : x ∈ s) {f : E → F} {f' : E →L[ℝ] F}:
    HasFDerivWithinAt f f' s x ↔ HasFDerivAt f f' x := by
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


lemma diffeoOn_differential_bijective {r : ℕ} (hr : 1 ≤ r) {x : M}
    (h : DiffeomorphOn I J M N r) (hx : x ∈ h.source) : Bijective (mfderiv I J h.toFun x) := by
  let f := h.toFun
  let g := h.invFun
  let s := h.source
  let t := h.target

  set A := mfderiv I J f x
  -- Initial observations about x, s and t.
  let y := f x
  have hyx : g y = x := h.left_inv' hx
  have hysource : y ∈ t := h.toLocalEquiv.mapsTo hx
  let hst := h.toLocalEquiv.mapsTo
  have : f '' s = t := subset_antisymm (mapsTo'.mp hst) (fun y hy ↦ ⟨g y, h.map_target hy, h.right_inv' hy⟩)
  have : g '' t = s := by
    rw [← this, ← image_comp]
    sorry --exact Set.image_congr'' (fun x hx ↦ h.left_inv' hx)
  have hopen : IsOpen (g '' t) := by rw [this]; exact h.open_source
  have hx2 : x ∈ g '' t := by simp_rw [this]; exact hx

  let A' := mfderiv J I g y
  have hr : 1 ≤ (r : ℕ∞) := Nat.one_le_cast.mpr (Nat.one_le_of_lt hr)
  have hgat : MDifferentiableAt J I g y :=
    (h.contMDiffAt_symm (hst hx)).mdifferentiableAt hr
  have hfat : MDifferentiableAt I J f x :=
    (h.contMDiffAt hx).mdifferentiableAt hr
  have inv1 := calc A'.comp A
    _ = mfderiv I I (g ∘ f) x := (mfderiv_comp x hgat hfat).symm
    _ = mfderivWithin I I (g ∘ f) (g '' t) x := (mfderivWithin_of_open I I hopen hx2).symm
    _ = mfderivWithin I I id (g '' t) x :=
      sorry --mfderivWithin_congr (hopen.uniqueMDiffWithinAt hx2) (this ▸ h.left_inv') (h.left_inv' x (this ▸ hx2))
    _ = mfderiv I I id x := mfderivWithin_of_open I I hopen hx2
    _ = ContinuousLinearMap.id ℝ (TangentSpace I x) := mfderiv_id I
  have inv2 := calc A.comp A'
    _ = mfderiv J J (f ∘ g) y := by
          -- Use the chain rule: rewrite the base point (I ∘ e ∘ e.invFun ∘ I.invFun) x = x, ...
          rw [← (h.left_inv' hx)] at hfat
          -- ... but also the points x and y under the map.
          sorry --exact (hyx ▸ (mfderiv_comp (f x) hfat hgat)).symm
    _ = mfderivWithin J J (f ∘ g) t y := (mfderivWithin_of_open J J h.open_target hysource).symm
    _ = mfderivWithin J J id t y :=
          sorry --mfderivWithin_congr (h.open_target.uniqueMDiffWithinAt hysource) h.right_inv' (h.right_inv' y hysource)
    _ = mfderiv J J id y := mfderivWithin_of_open J J h.open_target hysource
    _ = ContinuousLinearMap.id ℝ (TangentSpace J (f x)) := mfderiv_id J


  sorry
