/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Differentiability of specific functions

In this file, we establish differentiability results for
- continuous linear maps and continuous linear equivalences
- the identity
- constant functions
- products
- arithmetic operations (such as addition and scalar multiplication).

-/

noncomputable section

open scoped Manifold
open Bundle Set Topology

section SpecificFunctions

/-! ### Differentiability of specific functions -/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M] {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  (I' : ModelWithCorners 𝕜 E' H') {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [SmoothManifoldWithCorners I' M'] {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] (I'' : ModelWithCorners 𝕜 E'' H'') {M'' : Type*}
  [TopologicalSpace M''] [ChartedSpace H'' M''] [SmoothManifoldWithCorners I'' M'']

namespace ContinuousLinearMap

variable (f : E →L[𝕜] E') {s : Set E} {x : E}

protected theorem hasMFDerivWithinAt : HasMFDerivWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x f :=
  f.hasFDerivWithinAt.hasMFDerivWithinAt
#align continuous_linear_map.has_mfderiv_within_at ContinuousLinearMap.hasMFDerivWithinAt

protected theorem hasMFDerivAt : HasMFDerivAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x f :=
  f.hasFDerivAt.hasMFDerivAt
#align continuous_linear_map.has_mfderiv_at ContinuousLinearMap.hasMFDerivAt

protected theorem mdifferentiableWithinAt : MDifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x :=
  f.differentiableWithinAt.mdifferentiableWithinAt
#align continuous_linear_map.mdifferentiable_within_at ContinuousLinearMap.mdifferentiableWithinAt

protected theorem mdifferentiableOn : MDifferentiableOn 𝓘(𝕜, E) 𝓘(𝕜, E') f s :=
  f.differentiableOn.mdifferentiableOn
#align continuous_linear_map.mdifferentiable_on ContinuousLinearMap.mdifferentiableOn

protected theorem mdifferentiableAt : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x :=
  f.differentiableAt.mdifferentiableAt
#align continuous_linear_map.mdifferentiable_at ContinuousLinearMap.mdifferentiableAt

protected theorem mdifferentiable : MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, E') f :=
  f.differentiable.mdifferentiable
#align continuous_linear_map.mdifferentiable ContinuousLinearMap.mdifferentiable

theorem mfderiv_eq : mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E') f x = f :=
  f.hasMFDerivAt.mfderiv
#align continuous_linear_map.mfderiv_eq ContinuousLinearMap.mfderiv_eq

theorem mfderivWithin_eq (hs : UniqueMDiffWithinAt 𝓘(𝕜, E) s x) :
    mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E') f s x = f :=
  f.hasMFDerivWithinAt.mfderivWithin hs
#align continuous_linear_map.mfderiv_within_eq ContinuousLinearMap.mfderivWithin_eq

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable (f : E ≃L[𝕜] E') {s : Set E} {x : E}

protected theorem hasMFDerivWithinAt : HasMFDerivWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x (f : E →L[𝕜] E') :=
  f.hasFDerivWithinAt.hasMFDerivWithinAt
#align continuous_linear_equiv.has_mfderiv_within_at ContinuousLinearEquiv.hasMFDerivWithinAt

protected theorem hasMFDerivAt : HasMFDerivAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x (f : E →L[𝕜] E') :=
  f.hasFDerivAt.hasMFDerivAt
#align continuous_linear_equiv.has_mfderiv_at ContinuousLinearEquiv.hasMFDerivAt

protected theorem mdifferentiableWithinAt : MDifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x :=
  f.differentiableWithinAt.mdifferentiableWithinAt
#align continuous_linear_equiv.mdifferentiable_within_at ContinuousLinearEquiv.mdifferentiableWithinAt

protected theorem mdifferentiableOn : MDifferentiableOn 𝓘(𝕜, E) 𝓘(𝕜, E') f s :=
  f.differentiableOn.mdifferentiableOn
#align continuous_linear_equiv.mdifferentiable_on ContinuousLinearEquiv.mdifferentiableOn

protected theorem mdifferentiableAt : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x :=
  f.differentiableAt.mdifferentiableAt
#align continuous_linear_equiv.mdifferentiable_at ContinuousLinearEquiv.mdifferentiableAt

protected theorem mdifferentiable : MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, E') f :=
  f.differentiable.mdifferentiable
#align continuous_linear_equiv.mdifferentiable ContinuousLinearEquiv.mdifferentiable

theorem mfderiv_eq : mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E') f x = (f : E →L[𝕜] E') :=
  f.hasMFDerivAt.mfderiv
#align continuous_linear_equiv.mfderiv_eq ContinuousLinearEquiv.mfderiv_eq

theorem mfderivWithin_eq (hs : UniqueMDiffWithinAt 𝓘(𝕜, E) s x) :
    mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E') f s x = (f : E →L[𝕜] E') :=
  f.hasMFDerivWithinAt.mfderivWithin hs
#align continuous_linear_equiv.mfderiv_within_eq ContinuousLinearEquiv.mfderivWithin_eq

end ContinuousLinearEquiv

variable {s : Set M} {x : M}

section id

/-! #### Identity -/

theorem hasMFDerivAt_id (x : M) :
    HasMFDerivAt I I (@id M) x (ContinuousLinearMap.id 𝕜 (TangentSpace I x)) := by
  refine ⟨continuousAt_id, ?_⟩
  have : ∀ᶠ y in 𝓝[range I] (extChartAt I x) x, (extChartAt I x ∘ (extChartAt I x).symm) y = y := by
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin I x)
    mfld_set_tac
  apply HasFDerivWithinAt.congr_of_eventuallyEq (hasFDerivWithinAt_id _ _) this
  simp only [mfld_simps]
#align has_mfderiv_at_id hasMFDerivAt_id

theorem hasMFDerivWithinAt_id (s : Set M) (x : M) :
    HasMFDerivWithinAt I I (@id M) s x (ContinuousLinearMap.id 𝕜 (TangentSpace I x)) :=
  (hasMFDerivAt_id I x).hasMFDerivWithinAt
#align has_mfderiv_within_at_id hasMFDerivWithinAt_id

theorem mdifferentiableAt_id : MDifferentiableAt I I (@id M) x :=
  (hasMFDerivAt_id I x).mdifferentiableAt
#align mdifferentiable_at_id mdifferentiableAt_id

theorem mdifferentiableWithinAt_id : MDifferentiableWithinAt I I (@id M) s x :=
  (mdifferentiableAt_id I).mdifferentiableWithinAt
#align mdifferentiable_within_at_id mdifferentiableWithinAt_id

theorem mdifferentiable_id : MDifferentiable I I (@id M) := fun _ => mdifferentiableAt_id I
#align mdifferentiable_id mdifferentiable_id

theorem mdifferentiableOn_id : MDifferentiableOn I I (@id M) s :=
  (mdifferentiable_id I).mdifferentiableOn
#align mdifferentiable_on_id mdifferentiableOn_id

@[simp, mfld_simps]
theorem mfderiv_id : mfderiv I I (@id M) x = ContinuousLinearMap.id 𝕜 (TangentSpace I x) :=
  HasMFDerivAt.mfderiv (hasMFDerivAt_id I x)
#align mfderiv_id mfderiv_id

theorem mfderivWithin_id (hxs : UniqueMDiffWithinAt I s x) :
    mfderivWithin I I (@id M) s x = ContinuousLinearMap.id 𝕜 (TangentSpace I x) := by
  rw [MDifferentiable.mfderivWithin (mdifferentiableAt_id I) hxs]
  exact mfderiv_id I
#align mfderiv_within_id mfderivWithin_id

@[simp, mfld_simps]
theorem tangentMap_id : tangentMap I I (id : M → M) = id := by ext1 ⟨x, v⟩; simp [tangentMap]
#align tangent_map_id tangentMap_id

theorem tangentMapWithin_id {p : TangentBundle I M} (hs : UniqueMDiffWithinAt I s p.proj) :
    tangentMapWithin I I (id : M → M) s p = p := by
  simp only [tangentMapWithin, id]
  rw [mfderivWithin_id]
  · rcases p with ⟨⟩; rfl
  · exact hs
#align tangent_map_within_id tangentMapWithin_id

end id

section Const

/-! #### Constants -/


variable {c : M'}

theorem hasMFDerivAt_const (c : M') (x : M) :
    HasMFDerivAt I I' (fun _ : M => c) x (0 : TangentSpace I x →L[𝕜] TangentSpace I' c) := by
  refine ⟨continuous_const.continuousAt, ?_⟩
  simp only [writtenInExtChartAt, (· ∘ ·), hasFDerivWithinAt_const]
#align has_mfderiv_at_const hasMFDerivAt_const

theorem hasMFDerivWithinAt_const (c : M') (s : Set M) (x : M) :
    HasMFDerivWithinAt I I' (fun _ : M => c) s x (0 : TangentSpace I x →L[𝕜] TangentSpace I' c) :=
  (hasMFDerivAt_const I I' c x).hasMFDerivWithinAt
#align has_mfderiv_within_at_const hasMFDerivWithinAt_const

theorem mdifferentiableAt_const : MDifferentiableAt I I' (fun _ : M => c) x :=
  (hasMFDerivAt_const I I' c x).mdifferentiableAt
#align mdifferentiable_at_const mdifferentiableAt_const

theorem mdifferentiableWithinAt_const : MDifferentiableWithinAt I I' (fun _ : M => c) s x :=
  (mdifferentiableAt_const I I').mdifferentiableWithinAt
#align mdifferentiable_within_at_const mdifferentiableWithinAt_const

theorem mdifferentiable_const : MDifferentiable I I' fun _ : M => c := fun _ =>
  mdifferentiableAt_const I I'
#align mdifferentiable_const mdifferentiable_const

theorem mdifferentiableOn_const : MDifferentiableOn I I' (fun _ : M => c) s :=
  (mdifferentiable_const I I').mdifferentiableOn
#align mdifferentiable_on_const mdifferentiableOn_const

@[simp, mfld_simps]
theorem mfderiv_const :
    mfderiv I I' (fun _ : M => c) x = (0 : TangentSpace I x →L[𝕜] TangentSpace I' c) :=
  HasMFDerivAt.mfderiv (hasMFDerivAt_const I I' c x)
#align mfderiv_const mfderiv_const

theorem mfderivWithin_const (hxs : UniqueMDiffWithinAt I s x) :
    mfderivWithin I I' (fun _ : M => c) s x = (0 : TangentSpace I x →L[𝕜] TangentSpace I' c) :=
  (hasMFDerivWithinAt_const _ _ _ _ _).mfderivWithin hxs
#align mfderiv_within_const mfderivWithin_const

end Const

section Prod

/-! ### Operations on the product of two manifolds -/

theorem hasMFDerivAt_fst (x : M × M') :
    HasMFDerivAt (I.prod I') I Prod.fst x
      (ContinuousLinearMap.fst 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2)) := by
  refine ⟨continuous_fst.continuousAt, ?_⟩
  have :
    ∀ᶠ y in 𝓝[range (I.prod I')] extChartAt (I.prod I') x x,
      (extChartAt I x.1 ∘ Prod.fst ∘ (extChartAt (I.prod I') x).symm) y = y.1 := by
    /- porting note: was
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin (I.prod I') x)
    mfld_set_tac
    -/
    filter_upwards [extChartAt_target_mem_nhdsWithin (I.prod I') x] with y hy
    rw [extChartAt_prod] at hy
    exact (extChartAt I x.1).right_inv hy.1
  apply HasFDerivWithinAt.congr_of_eventuallyEq hasFDerivWithinAt_fst this
  -- Porting note: next line was `simp only [mfld_simps]`
  exact (extChartAt I x.1).right_inv <| (extChartAt I x.1).map_source (mem_extChartAt_source _ _)
#align has_mfderiv_at_fst hasMFDerivAt_fst

theorem hasMFDerivWithinAt_fst (s : Set (M × M')) (x : M × M') :
    HasMFDerivWithinAt (I.prod I') I Prod.fst s x
      (ContinuousLinearMap.fst 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2)) :=
  (hasMFDerivAt_fst I I' x).hasMFDerivWithinAt
#align has_mfderiv_within_at_fst hasMFDerivWithinAt_fst

theorem mdifferentiableAt_fst {x : M × M'} : MDifferentiableAt (I.prod I') I Prod.fst x :=
  (hasMFDerivAt_fst I I' x).mdifferentiableAt
#align mdifferentiable_at_fst mdifferentiableAt_fst

theorem mdifferentiableWithinAt_fst {s : Set (M × M')} {x : M × M'} :
    MDifferentiableWithinAt (I.prod I') I Prod.fst s x :=
  (mdifferentiableAt_fst I I').mdifferentiableWithinAt
#align mdifferentiable_within_at_fst mdifferentiableWithinAt_fst

theorem mdifferentiable_fst : MDifferentiable (I.prod I') I (Prod.fst : M × M' → M) := fun _ =>
  mdifferentiableAt_fst I I'
#align mdifferentiable_fst mdifferentiable_fst

theorem mdifferentiableOn_fst {s : Set (M × M')} : MDifferentiableOn (I.prod I') I Prod.fst s :=
  (mdifferentiable_fst I I').mdifferentiableOn
#align mdifferentiable_on_fst mdifferentiableOn_fst

@[simp, mfld_simps]
theorem mfderiv_fst {x : M × M'} :
    mfderiv (I.prod I') I Prod.fst x =
      ContinuousLinearMap.fst 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2) :=
  (hasMFDerivAt_fst I I' x).mfderiv
#align mfderiv_fst mfderiv_fst

theorem mfderivWithin_fst {s : Set (M × M')} {x : M × M'}
    (hxs : UniqueMDiffWithinAt (I.prod I') s x) :
    mfderivWithin (I.prod I') I Prod.fst s x =
      ContinuousLinearMap.fst 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2) := by
  rw [MDifferentiable.mfderivWithin (mdifferentiableAt_fst I I') hxs]; exact mfderiv_fst I I'
#align mfderiv_within_fst mfderivWithin_fst

@[simp, mfld_simps]
theorem tangentMap_prod_fst {p : TangentBundle (I.prod I') (M × M')} :
    tangentMap (I.prod I') I Prod.fst p = ⟨p.proj.1, p.2.1⟩ := by
  -- Porting note: `rfl` wasn't needed
  simp [tangentMap]; rfl
#align tangent_map_prod_fst tangentMap_prod_fst

theorem tangentMapWithin_prod_fst {s : Set (M × M')} {p : TangentBundle (I.prod I') (M × M')}
    (hs : UniqueMDiffWithinAt (I.prod I') s p.proj) :
    tangentMapWithin (I.prod I') I Prod.fst s p = ⟨p.proj.1, p.2.1⟩ := by
  simp only [tangentMapWithin]
  rw [mfderivWithin_fst]
  · rcases p with ⟨⟩; rfl
  · exact hs
#align tangent_map_within_prod_fst tangentMapWithin_prod_fst

theorem hasMFDerivAt_snd (x : M × M') :
    HasMFDerivAt (I.prod I') I' Prod.snd x
      (ContinuousLinearMap.snd 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2)) := by
  refine ⟨continuous_snd.continuousAt, ?_⟩
  have :
    ∀ᶠ y in 𝓝[range (I.prod I')] extChartAt (I.prod I') x x,
      (extChartAt I' x.2 ∘ Prod.snd ∘ (extChartAt (I.prod I') x).symm) y = y.2 := by
    /- porting note: was
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin (I.prod I') x)
    mfld_set_tac
    -/
    filter_upwards [extChartAt_target_mem_nhdsWithin (I.prod I') x] with y hy
    rw [extChartAt_prod] at hy
    exact (extChartAt I' x.2).right_inv hy.2
  apply HasFDerivWithinAt.congr_of_eventuallyEq hasFDerivWithinAt_snd this
  -- Porting note: the next line was `simp only [mfld_simps]`
  exact (extChartAt I' x.2).right_inv <| (extChartAt I' x.2).map_source (mem_extChartAt_source _ _)
#align has_mfderiv_at_snd hasMFDerivAt_snd

theorem hasMFDerivWithinAt_snd (s : Set (M × M')) (x : M × M') :
    HasMFDerivWithinAt (I.prod I') I' Prod.snd s x
      (ContinuousLinearMap.snd 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2)) :=
  (hasMFDerivAt_snd I I' x).hasMFDerivWithinAt
#align has_mfderiv_within_at_snd hasMFDerivWithinAt_snd

theorem mdifferentiableAt_snd {x : M × M'} : MDifferentiableAt (I.prod I') I' Prod.snd x :=
  (hasMFDerivAt_snd I I' x).mdifferentiableAt
#align mdifferentiable_at_snd mdifferentiableAt_snd

theorem mdifferentiableWithinAt_snd {s : Set (M × M')} {x : M × M'} :
    MDifferentiableWithinAt (I.prod I') I' Prod.snd s x :=
  (mdifferentiableAt_snd I I').mdifferentiableWithinAt
#align mdifferentiable_within_at_snd mdifferentiableWithinAt_snd

theorem mdifferentiable_snd : MDifferentiable (I.prod I') I' (Prod.snd : M × M' → M') := fun _ =>
  mdifferentiableAt_snd I I'
#align mdifferentiable_snd mdifferentiable_snd

theorem mdifferentiableOn_snd {s : Set (M × M')} : MDifferentiableOn (I.prod I') I' Prod.snd s :=
  (mdifferentiable_snd I I').mdifferentiableOn
#align mdifferentiable_on_snd mdifferentiableOn_snd

@[simp, mfld_simps]
theorem mfderiv_snd {x : M × M'} :
    mfderiv (I.prod I') I' Prod.snd x =
      ContinuousLinearMap.snd 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2) :=
  (hasMFDerivAt_snd I I' x).mfderiv
#align mfderiv_snd mfderiv_snd

theorem mfderivWithin_snd {s : Set (M × M')} {x : M × M'}
    (hxs : UniqueMDiffWithinAt (I.prod I') s x) :
    mfderivWithin (I.prod I') I' Prod.snd s x =
      ContinuousLinearMap.snd 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2) := by
  rw [MDifferentiable.mfderivWithin (mdifferentiableAt_snd I I') hxs]; exact mfderiv_snd I I'
#align mfderiv_within_snd mfderivWithin_snd

@[simp, mfld_simps]
theorem tangentMap_prod_snd {p : TangentBundle (I.prod I') (M × M')} :
    tangentMap (I.prod I') I' Prod.snd p = ⟨p.proj.2, p.2.2⟩ := by
  -- Porting note: `rfl` wasn't needed
  simp [tangentMap]; rfl
#align tangent_map_prod_snd tangentMap_prod_snd

theorem tangentMapWithin_prod_snd {s : Set (M × M')} {p : TangentBundle (I.prod I') (M × M')}
    (hs : UniqueMDiffWithinAt (I.prod I') s p.proj) :
    tangentMapWithin (I.prod I') I' Prod.snd s p = ⟨p.proj.2, p.2.2⟩ := by
  simp only [tangentMapWithin]
  rw [mfderivWithin_snd]
  · rcases p with ⟨⟩; rfl
  · exact hs
#align tangent_map_within_prod_snd tangentMapWithin_prod_snd

variable {I I' I''}

theorem MDifferentiableAt.mfderiv_prod {f : M → M'} {g : M → M''} {x : M}
    (hf : MDifferentiableAt I I' f x) (hg : MDifferentiableAt I I'' g x) :
    mfderiv I (I'.prod I'') (fun x => (f x, g x)) x =
      (mfderiv I I' f x).prod (mfderiv I I'' g x) := by
  classical
  simp_rw [mfderiv, if_pos (hf.prod_mk hg), if_pos hf, if_pos hg]
  exact hf.differentiableWithinAt_writtenInExtChartAt.fderivWithin_prod
    hg.differentiableWithinAt_writtenInExtChartAt (I.unique_diff _ (mem_range_self _))
#align mdifferentiable_at.mfderiv_prod MDifferentiableAt.mfderiv_prod

variable (I I' I'')

theorem mfderiv_prod_left {x₀ : M} {y₀ : M'} :
    mfderiv I (I.prod I') (fun x => (x, y₀)) x₀ =
      ContinuousLinearMap.inl 𝕜 (TangentSpace I x₀) (TangentSpace I' y₀) := by
  refine ((mdifferentiableAt_id I).mfderiv_prod (mdifferentiableAt_const I I')).trans ?_
  rw [mfderiv_id, mfderiv_const, ContinuousLinearMap.inl]
#align mfderiv_prod_left mfderiv_prod_left

theorem mfderiv_prod_right {x₀ : M} {y₀ : M'} :
    mfderiv I' (I.prod I') (fun y => (x₀, y)) y₀ =
      ContinuousLinearMap.inr 𝕜 (TangentSpace I x₀) (TangentSpace I' y₀) := by
  refine ((mdifferentiableAt_const I' I).mfderiv_prod (mdifferentiableAt_id I')).trans ?_
  rw [mfderiv_id, mfderiv_const, ContinuousLinearMap.inr]
#align mfderiv_prod_right mfderiv_prod_right

/-- The total derivative of a function in two variables is the sum of the partial derivatives.
  Note that to state this (without casts) we need to be able to see through the definition of
  `TangentSpace`. -/
theorem mfderiv_prod_eq_add {f : M × M' → M''} {p : M × M'}
    (hf : MDifferentiableAt (I.prod I') I'' f p) :
    mfderiv (I.prod I') I'' f p =
      show E × E' →L[𝕜] E'' from
        mfderiv (I.prod I') I'' (fun z : M × M' => f (z.1, p.2)) p +
          mfderiv (I.prod I') I'' (fun z : M × M' => f (p.1, z.2)) p := by
  dsimp only
  erw [mfderiv_comp_of_eq hf ((mdifferentiableAt_fst I I').prod_mk (mdifferentiableAt_const _ _))
      rfl,
    mfderiv_comp_of_eq hf ((mdifferentiableAt_const _ _).prod_mk (mdifferentiableAt_snd I I')) rfl,
    ← ContinuousLinearMap.comp_add,
    (mdifferentiableAt_fst I I').mfderiv_prod (mdifferentiableAt_const (I.prod I') I'),
    (mdifferentiableAt_const (I.prod I') I).mfderiv_prod (mdifferentiableAt_snd I I'), mfderiv_fst,
    mfderiv_snd, mfderiv_const, mfderiv_const]
  symm
  convert ContinuousLinearMap.comp_id <| mfderiv (.prod I I') I'' f (p.1, p.2)
  exact ContinuousLinearMap.coprod_inl_inr
#align mfderiv_prod_eq_add mfderiv_prod_eq_add

end Prod

section Arithmetic

/-! #### Arithmetic

Note that in the `HasMFDerivAt` lemmas there is an abuse of the defeq between `E'` and
`TangentSpace 𝓘(𝕜, E') (f z)` (similarly for `g',F',p',q'`). In general this defeq is not
canonical, but in this case (the tangent space of a vector space) it is canonical.
 -/

section Group

variable {I}
variable {z : M} {f g : M → E'} {f' g' : TangentSpace I z →L[𝕜] E'}

theorem HasMFDerivAt.add (hf : HasMFDerivAt I 𝓘(𝕜, E') f z f')
    (hg : HasMFDerivAt I 𝓘(𝕜, E') g z g') : HasMFDerivAt I 𝓘(𝕜, E') (f + g) z (f' + g') :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩
#align has_mfderiv_at.add HasMFDerivAt.add

theorem MDifferentiableAt.add (hf : MDifferentiableAt I 𝓘(𝕜, E') f z)
    (hg : MDifferentiableAt I 𝓘(𝕜, E') g z) : MDifferentiableAt I 𝓘(𝕜, E') (f + g) z :=
  (hf.hasMFDerivAt.add hg.hasMFDerivAt).mdifferentiableAt
#align mdifferentiable_at.add MDifferentiableAt.add

theorem MDifferentiable.add (hf : MDifferentiable I 𝓘(𝕜, E') f)
    (hg : MDifferentiable I 𝓘(𝕜, E') g) : MDifferentiable I 𝓘(𝕜, E') (f + g) := fun x =>
  (hf x).add (hg x)
#align mdifferentiable.add MDifferentiable.add

-- Porting note: forcing types using `by exact`
theorem mfderiv_add (hf : MDifferentiableAt I 𝓘(𝕜, E') f z)
    (hg : MDifferentiableAt I 𝓘(𝕜, E') g z) :
    (by exact mfderiv I 𝓘(𝕜, E') (f + g) z : TangentSpace I z →L[𝕜] E') =
      (by exact mfderiv I 𝓘(𝕜, E') f z) + (by exact mfderiv I 𝓘(𝕜, E') g z) :=
  (hf.hasMFDerivAt.add hg.hasMFDerivAt).mfderiv
#align mfderiv_add mfderiv_add

theorem HasMFDerivAt.const_smul (hf : HasMFDerivAt I 𝓘(𝕜, E') f z f') (s : 𝕜) :
    HasMFDerivAt I 𝓘(𝕜, E') (s • f) z (s • f') :=
  ⟨hf.1.const_smul s, hf.2.const_smul s⟩
#align has_mfderiv_at.const_smul HasMFDerivAt.const_smul

theorem MDifferentiableAt.const_smul (hf : MDifferentiableAt I 𝓘(𝕜, E') f z) (s : 𝕜) :
    MDifferentiableAt I 𝓘(𝕜, E') (s • f) z :=
  (hf.hasMFDerivAt.const_smul s).mdifferentiableAt
#align mdifferentiable_at.const_smul MDifferentiableAt.const_smul

theorem MDifferentiable.const_smul (s : 𝕜) (hf : MDifferentiable I 𝓘(𝕜, E') f) :
    MDifferentiable I 𝓘(𝕜, E') (s • f) := fun x => (hf x).const_smul s
#align mdifferentiable.const_smul MDifferentiable.const_smul

theorem const_smul_mfderiv (hf : MDifferentiableAt I 𝓘(𝕜, E') f z) (s : 𝕜) :
    (mfderiv I 𝓘(𝕜, E') (s • f) z : TangentSpace I z →L[𝕜] E') =
      (s • mfderiv I 𝓘(𝕜, E') f z : TangentSpace I z →L[𝕜] E') :=
  (hf.hasMFDerivAt.const_smul s).mfderiv
#align const_smul_mfderiv const_smul_mfderiv

theorem HasMFDerivAt.neg (hf : HasMFDerivAt I 𝓘(𝕜, E') f z f') :
    HasMFDerivAt I 𝓘(𝕜, E') (-f) z (-f') :=
  ⟨hf.1.neg, hf.2.neg⟩
#align has_mfderiv_at.neg HasMFDerivAt.neg

theorem hasMFDerivAt_neg : HasMFDerivAt I 𝓘(𝕜, E') (-f) z (-f') ↔ HasMFDerivAt I 𝓘(𝕜, E') f z f' :=
  ⟨fun hf => by convert hf.neg <;> rw [neg_neg], fun hf => hf.neg⟩
#align has_mfderiv_at_neg hasMFDerivAt_neg

theorem MDifferentiableAt.neg (hf : MDifferentiableAt I 𝓘(𝕜, E') f z) :
    MDifferentiableAt I 𝓘(𝕜, E') (-f) z :=
  hf.hasMFDerivAt.neg.mdifferentiableAt
#align mdifferentiable_at.neg MDifferentiableAt.neg

theorem mdifferentiableAt_neg :
    MDifferentiableAt I 𝓘(𝕜, E') (-f) z ↔ MDifferentiableAt I 𝓘(𝕜, E') f z :=
  ⟨fun hf => by convert hf.neg; rw [neg_neg], fun hf => hf.neg⟩
#align mdifferentiable_at_neg mdifferentiableAt_neg

theorem MDifferentiable.neg (hf : MDifferentiable I 𝓘(𝕜, E') f) : MDifferentiable I 𝓘(𝕜, E') (-f) :=
  fun x => (hf x).neg
#align mdifferentiable.neg MDifferentiable.neg

theorem mfderiv_neg (f : M → E') (x : M) :
    (mfderiv I 𝓘(𝕜, E') (-f) x : TangentSpace I x →L[𝕜] E') =
      (-mfderiv I 𝓘(𝕜, E') f x : TangentSpace I x →L[𝕜] E') := by
  simp_rw [mfderiv]
  by_cases hf : MDifferentiableAt I 𝓘(𝕜, E') f x
  · exact hf.hasMFDerivAt.neg.mfderiv
  · rw [if_neg hf]; rw [← mdifferentiableAt_neg] at hf; rw [if_neg hf, neg_zero]
#align mfderiv_neg mfderiv_neg

theorem HasMFDerivAt.sub (hf : HasMFDerivAt I 𝓘(𝕜, E') f z f')
    (hg : HasMFDerivAt I 𝓘(𝕜, E') g z g') : HasMFDerivAt I 𝓘(𝕜, E') (f - g) z (f' - g') :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩
#align has_mfderiv_at.sub HasMFDerivAt.sub

theorem MDifferentiableAt.sub (hf : MDifferentiableAt I 𝓘(𝕜, E') f z)
    (hg : MDifferentiableAt I 𝓘(𝕜, E') g z) : MDifferentiableAt I 𝓘(𝕜, E') (f - g) z :=
  (hf.hasMFDerivAt.sub hg.hasMFDerivAt).mdifferentiableAt
#align mdifferentiable_at.sub MDifferentiableAt.sub

theorem MDifferentiable.sub (hf : MDifferentiable I 𝓘(𝕜, E') f)
    (hg : MDifferentiable I 𝓘(𝕜, E') g) : MDifferentiable I 𝓘(𝕜, E') (f - g) := fun x =>
  (hf x).sub (hg x)
#align mdifferentiable.sub MDifferentiable.sub

theorem mfderiv_sub (hf : MDifferentiableAt I 𝓘(𝕜, E') f z)
    (hg : MDifferentiableAt I 𝓘(𝕜, E') g z) :
    (by exact mfderiv I 𝓘(𝕜, E') (f - g) z : TangentSpace I z →L[𝕜] E') =
      (by exact mfderiv I 𝓘(𝕜, E') f z) - (by exact mfderiv I 𝓘(𝕜, E') g z) :=
  (hf.hasMFDerivAt.sub hg.hasMFDerivAt).mfderiv
#align mfderiv_sub mfderiv_sub

end Group

section AlgebraOverRing

variable {I}
variable {z : M} {F' : Type*} [NormedRing F'] [NormedAlgebra 𝕜 F'] {p q : M → F'}
  {p' q' : TangentSpace I z →L[𝕜] F'}

theorem HasMFDerivWithinAt.mul' (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
    (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (p * q) s z (p z • q' + p'.smulRight (q z) : E →L[𝕜] F') :=
  ⟨hp.1.mul hq.1, by simpa only [mfld_simps] using hp.2.mul' hq.2⟩
#align has_mfderiv_within_at.mul' HasMFDerivWithinAt.mul'

theorem HasMFDerivAt.mul' (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
    (hq : HasMFDerivAt I 𝓘(𝕜, F') q z q') :
    HasMFDerivAt I 𝓘(𝕜, F') (p * q) z (p z • q' + p'.smulRight (q z) : E →L[𝕜] F') :=
  hasMFDerivWithinAt_univ.mp <| hp.hasMFDerivWithinAt.mul' hq.hasMFDerivWithinAt
#align has_mfderiv_at.mul' HasMFDerivAt.mul'

theorem MDifferentiableWithinAt.mul (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
    (hq : MDifferentiableWithinAt I 𝓘(𝕜, F') q s z) :
    MDifferentiableWithinAt I 𝓘(𝕜, F') (p * q) s z :=
  (hp.hasMFDerivWithinAt.mul' hq.hasMFDerivWithinAt).mdifferentiableWithinAt
#align mdifferentiable_within_at.mul MDifferentiableWithinAt.mul

theorem MDifferentiableAt.mul (hp : MDifferentiableAt I 𝓘(𝕜, F') p z)
    (hq : MDifferentiableAt I 𝓘(𝕜, F') q z) : MDifferentiableAt I 𝓘(𝕜, F') (p * q) z :=
  (hp.hasMFDerivAt.mul' hq.hasMFDerivAt).mdifferentiableAt
#align mdifferentiable_at.mul MDifferentiableAt.mul

theorem MDifferentiableOn.mul (hp : MDifferentiableOn I 𝓘(𝕜, F') p s)
    (hq : MDifferentiableOn I 𝓘(𝕜, F') q s) : MDifferentiableOn I 𝓘(𝕜, F') (p * q) s := fun x hx =>
  (hp x hx).mul <| hq x hx
#align mdifferentiable_on.mul MDifferentiableOn.mul

theorem MDifferentiable.mul (hp : MDifferentiable I 𝓘(𝕜, F') p)
    (hq : MDifferentiable I 𝓘(𝕜, F') q) : MDifferentiable I 𝓘(𝕜, F') (p * q) := fun x =>
  (hp x).mul (hq x)
#align mdifferentiable.mul MDifferentiable.mul

end AlgebraOverRing

section AlgebraOverCommRing

variable {I}
variable {z : M} {F' : Type*} [NormedCommRing F'] [NormedAlgebra 𝕜 F'] {p q : M → F'}
  {p' q' : TangentSpace I z →L[𝕜] F'}

theorem HasMFDerivWithinAt.mul (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
    (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (p * q) s z (p z • q' + q z • p' : E →L[𝕜] F') := by
  convert hp.mul' hq; ext _; apply mul_comm
#align has_mfderiv_within_at.mul HasMFDerivWithinAt.mul

theorem HasMFDerivAt.mul (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
    (hq : HasMFDerivAt I 𝓘(𝕜, F') q z q') :
    HasMFDerivAt I 𝓘(𝕜, F') (p * q) z (p z • q' + q z • p' : E →L[𝕜] F') :=
  hasMFDerivWithinAt_univ.mp <| hp.hasMFDerivWithinAt.mul hq.hasMFDerivWithinAt
#align has_mfderiv_at.mul HasMFDerivAt.mul

end AlgebraOverCommRing

end Arithmetic

end SpecificFunctions
