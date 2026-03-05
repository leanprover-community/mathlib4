/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Differentiability of specific functions

In this file, we establish differentiability results for
- continuous linear maps and continuous linear equivalences
- the identity
- constant functions
- products
- arithmetic operations (such as addition and scalar multiplication).

-/

public section

noncomputable section

open scoped Manifold
open Bundle Set Topology

section SpecificFunctions

/-! ### Differentiability of specific functions -/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a charted space `M` over the pair `(E, H)`.
  {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M]
  -- declare a charted space `M'` over the pair `(E', H')`.
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  -- declare a charted space `M''` over the pair `(E'', H'')`.
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*}
  [TopologicalSpace M''] [ChartedSpace H'' M'']
  -- declare a charted space `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  -- declare a charted space `N'` over the pair `(F', G')`.
  {F' : Type*}
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type*} [TopologicalSpace G']
  {J' : ModelWithCorners 𝕜 F' G'} {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  -- F₁, F₂, F₃, F₄ are normed spaces
  {F₁ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {F₂ : Type*} [NormedAddCommGroup F₂]
  [NormedSpace 𝕜 F₂] {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] {F₄ : Type*}
  [NormedAddCommGroup F₄] [NormedSpace 𝕜 F₄]

namespace ContinuousLinearMap

variable (f : E →L[𝕜] E') {s : Set E} {x : E}

protected theorem hasMFDerivWithinAt : HasMFDerivWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x f :=
  f.hasFDerivWithinAt.hasMFDerivWithinAt

protected theorem hasMFDerivAt : HasMFDerivAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x f :=
  f.hasFDerivAt.hasMFDerivAt

protected theorem mdifferentiableWithinAt : MDifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x :=
  f.differentiableWithinAt.mdifferentiableWithinAt

protected theorem mdifferentiableOn : MDifferentiableOn 𝓘(𝕜, E) 𝓘(𝕜, E') f s :=
  f.differentiableOn.mdifferentiableOn

protected theorem mdifferentiableAt : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x :=
  f.differentiableAt.mdifferentiableAt

protected theorem mdifferentiable : MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, E') f :=
  f.differentiable.mdifferentiable

theorem mfderiv_eq : mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E') f x = f :=
  f.hasMFDerivAt.mfderiv

theorem mfderivWithin_eq (hs : UniqueMDiffWithinAt 𝓘(𝕜, E) s x) :
    mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E') f s x = f :=
  f.hasMFDerivWithinAt.mfderivWithin hs

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable (f : E ≃L[𝕜] E') {s : Set E} {x : E}

protected theorem hasMFDerivWithinAt : HasMFDerivWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x (f : E →L[𝕜] E') :=
  f.hasFDerivWithinAt.hasMFDerivWithinAt

protected theorem hasMFDerivAt : HasMFDerivAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x (f : E →L[𝕜] E') :=
  f.hasFDerivAt.hasMFDerivAt

protected theorem mdifferentiableWithinAt : MDifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x :=
  f.differentiableWithinAt.mdifferentiableWithinAt

protected theorem mdifferentiableOn : MDifferentiableOn 𝓘(𝕜, E) 𝓘(𝕜, E') f s :=
  f.differentiableOn.mdifferentiableOn

protected theorem mdifferentiableAt : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x :=
  f.differentiableAt.mdifferentiableAt

protected theorem mdifferentiable : MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, E') f :=
  f.differentiable.mdifferentiable

theorem mfderiv_eq : mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E') f x = (f : E →L[𝕜] E') :=
  f.hasMFDerivAt.mfderiv

theorem mfderivWithin_eq (hs : UniqueMDiffWithinAt 𝓘(𝕜, E) s x) :
    mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E') f s x = (f : E →L[𝕜] E') :=
  f.hasMFDerivWithinAt.mfderivWithin hs

end ContinuousLinearEquiv

variable {s : Set M} {x : M}

section id

/-! #### Identity -/

theorem hasMFDerivAt_id (x : M) :
    HasMFDerivAt I I (@id M) x (ContinuousLinearMap.id 𝕜 (TangentSpace I x)) := by
  refine ⟨continuousAt_id, ?_⟩
  have : ∀ᶠ y in 𝓝[range I] (extChartAt I x) x, (extChartAt I x ∘ (extChartAt I x).symm) y = y := by
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin x)
    mfld_set_tac
  apply HasFDerivWithinAt.congr_of_eventuallyEq (hasFDerivWithinAt_id _ _) this
  simp only [mfld_simps]

theorem hasMFDerivWithinAt_id (s : Set M) (x : M) :
    HasMFDerivWithinAt I I (@id M) s x (ContinuousLinearMap.id 𝕜 (TangentSpace I x)) :=
  (hasMFDerivAt_id x).hasMFDerivWithinAt

theorem mdifferentiableAt_id : MDifferentiableAt I I (@id M) x :=
  (hasMFDerivAt_id x).mdifferentiableAt

theorem mdifferentiableWithinAt_id : MDifferentiableWithinAt I I (@id M) s x :=
  mdifferentiableAt_id.mdifferentiableWithinAt

@[fun_prop]
theorem mdifferentiable_id : MDifferentiable I I (@id M) := fun _ => mdifferentiableAt_id

theorem mdifferentiableOn_id : MDifferentiableOn I I (@id M) s :=
  mdifferentiable_id.mdifferentiableOn

@[simp, mfld_simps]
theorem mfderiv_id : mfderiv I I (@id M) x = ContinuousLinearMap.id 𝕜 (TangentSpace I x) :=
  HasMFDerivAt.mfderiv (hasMFDerivAt_id x)

theorem mfderivWithin_id (hxs : UniqueMDiffWithinAt I s x) :
    mfderivWithin I I (@id M) s x = ContinuousLinearMap.id 𝕜 (TangentSpace I x) := by
  rw [MDifferentiable.mfderivWithin mdifferentiableAt_id hxs]
  exact mfderiv_id

set_option backward.isDefEq.respectTransparency false in
@[simp, mfld_simps]
theorem tangentMap_id : tangentMap I I (id : M → M) = id := by ext1 ⟨x, v⟩; simp [tangentMap]

theorem tangentMapWithin_id {p : TangentBundle I M} (hs : UniqueMDiffWithinAt I s p.proj) :
    tangentMapWithin I I (id : M → M) s p = p := by
  simp only [tangentMapWithin, id]
  rw [mfderivWithin_id]
  · rcases p with ⟨⟩; rfl
  · exact hs

end id

section Const

/-! #### Constants -/


variable {c : M'}

set_option backward.isDefEq.respectTransparency false in
theorem hasMFDerivAt_const (c : M') (x : M) :
    HasMFDerivAt I I' (fun _ : M => c) x (0 : TangentSpace I x →L[𝕜] TangentSpace I' c) :=
  ⟨by fun_prop, by simp [Function.comp_def, hasFDerivWithinAt_const]⟩

theorem hasMFDerivWithinAt_const (c : M') (s : Set M) (x : M) :
    HasMFDerivWithinAt I I' (fun _ : M => c) s x (0 : TangentSpace I x →L[𝕜] TangentSpace I' c) :=
  (hasMFDerivAt_const c x).hasMFDerivWithinAt

theorem mdifferentiableAt_const : MDifferentiableAt I I' (fun _ : M => c) x :=
  (hasMFDerivAt_const c x).mdifferentiableAt

theorem mdifferentiableWithinAt_const : MDifferentiableWithinAt I I' (fun _ : M => c) s x :=
  mdifferentiableAt_const.mdifferentiableWithinAt

@[fun_prop]
theorem mdifferentiable_const : MDifferentiable I I' fun _ : M => c := fun _ =>
  mdifferentiableAt_const

theorem mdifferentiableOn_const : MDifferentiableOn I I' (fun _ : M => c) s :=
  mdifferentiable_const.mdifferentiableOn

@[simp, mfld_simps]
theorem mfderiv_const :
    mfderiv I I' (fun _ : M => c) x = (0 : TangentSpace I x →L[𝕜] TangentSpace I' c) :=
  HasMFDerivAt.mfderiv (hasMFDerivAt_const c x)

theorem mfderivWithin_const :
    mfderivWithin I I' (fun _ : M => c) s x = (0 : TangentSpace I x →L[𝕜] TangentSpace I' c) :=
  (hasMFDerivWithinAt_const _ _ _).mfderivWithin_eq_zero

end Const

section Prod

/-! ### Operations on the product of two manifolds -/

theorem MDifferentiableWithinAt.prodMk {f : M → M'} {g : M → M''}
    (hf : MDifferentiableWithinAt I I' f s x) (hg : MDifferentiableWithinAt I I'' g s x) :
    MDifferentiableWithinAt I (I'.prod I'') (fun x => (f x, g x)) s x :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

/-- If `f` and `g` have derivatives `df` and `dg` within `s` at `x`, respectively,
then `x ↦ (f x, g x)` has derivative `df.prod dg` within `s`. -/
theorem HasMFDerivWithinAt.prodMk {f : M → M'} {g : M → M''}
    {df : TangentSpace I x →L[𝕜] TangentSpace I' (f x)} (hf : HasMFDerivWithinAt I I' f s x df)
    {dg : TangentSpace I x →L[𝕜] TangentSpace I'' (g x)} (hg : HasMFDerivWithinAt I I'' g s x dg) :
    HasMFDerivWithinAt I (I'.prod I'') (fun y ↦ (f y, g y)) s x (df.prod dg) :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

lemma mfderivWithin_prodMk {f : M → M'} {g : M → M''}
    (hf : MDifferentiableWithinAt I I' f s x) (hg : MDifferentiableWithinAt I I'' g s x)
    (hs : UniqueMDiffWithinAt I s x) :
    mfderivWithin I (I'.prod I'') (fun x => (f x, g x)) s x
      = (mfderivWithin I I' f s x).prod (mfderivWithin I I'' g s x) :=
  (hf.hasMFDerivWithinAt.prodMk hg.hasMFDerivWithinAt).mfderivWithin hs

lemma mfderiv_prodMk {f : M → M'} {g : M → M''}
    (hf : MDifferentiableAt I I' f x) (hg : MDifferentiableAt I I'' g x) :
    mfderiv I (I'.prod I'') (fun x => (f x, g x)) x
      = (mfderiv I I' f x).prod (mfderiv I I'' g x) := by
  simp_rw [← mfderivWithin_univ]
  exact mfderivWithin_prodMk hf.mdifferentiableWithinAt hg.mdifferentiableWithinAt
    (uniqueMDiffWithinAt_univ I)

theorem MDifferentiableAt.prodMk {f : M → M'} {g : M → M''} (hf : MDifferentiableAt I I' f x)
    (hg : MDifferentiableAt I I'' g x) :
    MDifferentiableAt I (I'.prod I'') (fun x => (f x, g x)) x :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

/-- If `f` and `g` have derivatives `df` and `dg` at `x`, respectively,
then `x ↦ (f x, g x)` has derivative `df.prod dg`. -/
theorem HasMFDerivAt.prodMk {f : M → M'} {g : M → M''}
    {df : TangentSpace I x →L[𝕜] TangentSpace I' (f x)} (hf : HasMFDerivAt I I' f x df)
    {dg : TangentSpace I x →L[𝕜] TangentSpace I'' (g x)} (hg : HasMFDerivAt I I'' g x dg) :
    HasMFDerivAt I (I'.prod I'') (fun y ↦ (f y, g y)) x (df.prod dg) :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

theorem MDifferentiableWithinAt.prodMk_space {f : M → E'} {g : M → E''}
    (hf : MDifferentiableWithinAt I 𝓘(𝕜, E') f s x)
    (hg : MDifferentiableWithinAt I 𝓘(𝕜, E'') g s x) :
    MDifferentiableWithinAt I 𝓘(𝕜, E' × E'') (fun x => (f x, g x)) s x :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

theorem MDifferentiableAt.prodMk_space {f : M → E'} {g : M → E''}
    (hf : MDifferentiableAt I 𝓘(𝕜, E') f x) (hg : MDifferentiableAt I 𝓘(𝕜, E'') g x) :
    MDifferentiableAt I 𝓘(𝕜, E' × E'') (fun x => (f x, g x)) x :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

theorem MDifferentiableOn.prodMk {f : M → M'} {g : M → M''} (hf : MDifferentiableOn I I' f s)
    (hg : MDifferentiableOn I I'' g s) :
    MDifferentiableOn I (I'.prod I'') (fun x => (f x, g x)) s := fun x hx =>
  (hf x hx).prodMk (hg x hx)

theorem MDifferentiable.prodMk {f : M → M'} {g : M → M''} (hf : MDifferentiable I I' f)
    (hg : MDifferentiable I I'' g) : MDifferentiable I (I'.prod I'') fun x => (f x, g x) := fun x =>
  (hf x).prodMk (hg x)

theorem MDifferentiableOn.prodMk_space {f : M → E'} {g : M → E''}
    (hf : MDifferentiableOn I 𝓘(𝕜, E') f s) (hg : MDifferentiableOn I 𝓘(𝕜, E'') g s) :
    MDifferentiableOn I 𝓘(𝕜, E' × E'') (fun x => (f x, g x)) s := fun x hx =>
  (hf x hx).prodMk_space (hg x hx)

theorem MDifferentiable.prodMk_space {f : M → E'} {g : M → E''} (hf : MDifferentiable I 𝓘(𝕜, E') f)
    (hg : MDifferentiable I 𝓘(𝕜, E'') g) : MDifferentiable I 𝓘(𝕜, E' × E'') fun x => (f x, g x) :=
  fun x => (hf x).prodMk_space (hg x)

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
    filter_upwards [extChartAt_target_mem_nhdsWithin x] with y hy
    rw [extChartAt_prod] at hy
    exact (extChartAt I x.1).right_inv hy.1
  apply HasFDerivWithinAt.congr_of_eventuallyEq hasFDerivWithinAt_fst this
  -- Porting note: next line was `simp only [mfld_simps]`
  exact (extChartAt I x.1).right_inv <| (extChartAt I x.1).map_source (mem_extChartAt_source _)

theorem hasMFDerivWithinAt_fst (s : Set (M × M')) (x : M × M') :
    HasMFDerivWithinAt (I.prod I') I Prod.fst s x
      (ContinuousLinearMap.fst 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2)) :=
  (hasMFDerivAt_fst x).hasMFDerivWithinAt

theorem mdifferentiableAt_fst {x : M × M'} : MDifferentiableAt (I.prod I') I Prod.fst x :=
  (hasMFDerivAt_fst x).mdifferentiableAt

theorem mdifferentiableWithinAt_fst {s : Set (M × M')} {x : M × M'} :
    MDifferentiableWithinAt (I.prod I') I Prod.fst s x :=
  mdifferentiableAt_fst.mdifferentiableWithinAt

@[fun_prop]
theorem mdifferentiable_fst : MDifferentiable (I.prod I') I (Prod.fst : M × M' → M) := fun _ =>
  mdifferentiableAt_fst

theorem mdifferentiableOn_fst {s : Set (M × M')} : MDifferentiableOn (I.prod I') I Prod.fst s :=
  mdifferentiable_fst.mdifferentiableOn

@[simp, mfld_simps]
theorem mfderiv_fst {x : M × M'} :
    mfderiv (I.prod I') I Prod.fst x =
      ContinuousLinearMap.fst 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2) :=
  (hasMFDerivAt_fst x).mfderiv

theorem mfderivWithin_fst {s : Set (M × M')} {x : M × M'}
    (hxs : UniqueMDiffWithinAt (I.prod I') s x) :
    mfderivWithin (I.prod I') I Prod.fst s x =
      ContinuousLinearMap.fst 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2) := by
  rw [MDifferentiable.mfderivWithin mdifferentiableAt_fst hxs]; exact mfderiv_fst

@[simp, mfld_simps]
theorem tangentMap_prodFst {p : TangentBundle (I.prod I') (M × M')} :
    tangentMap (I.prod I') I Prod.fst p = ⟨p.proj.1, p.2.1⟩ := by
  simp [tangentMap]; rfl

theorem tangentMapWithin_prodFst {s : Set (M × M')} {p : TangentBundle (I.prod I') (M × M')}
    (hs : UniqueMDiffWithinAt (I.prod I') s p.proj) :
    tangentMapWithin (I.prod I') I Prod.fst s p = ⟨p.proj.1, p.2.1⟩ := by
  simp only [tangentMapWithin]
  rw [mfderivWithin_fst]
  · rcases p with ⟨⟩; rfl
  · exact hs

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
    filter_upwards [extChartAt_target_mem_nhdsWithin x] with y hy
    rw [extChartAt_prod] at hy
    exact (extChartAt I' x.2).right_inv hy.2
  apply HasFDerivWithinAt.congr_of_eventuallyEq hasFDerivWithinAt_snd this
  -- Porting note: the next line was `simp only [mfld_simps]`
  exact (extChartAt I' x.2).right_inv <| (extChartAt I' x.2).map_source (mem_extChartAt_source _)

theorem hasMFDerivWithinAt_snd (s : Set (M × M')) (x : M × M') :
    HasMFDerivWithinAt (I.prod I') I' Prod.snd s x
      (ContinuousLinearMap.snd 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2)) :=
  (hasMFDerivAt_snd x).hasMFDerivWithinAt

theorem mdifferentiableAt_snd {x : M × M'} : MDifferentiableAt (I.prod I') I' Prod.snd x :=
  (hasMFDerivAt_snd x).mdifferentiableAt

theorem mdifferentiableWithinAt_snd {s : Set (M × M')} {x : M × M'} :
    MDifferentiableWithinAt (I.prod I') I' Prod.snd s x :=
  mdifferentiableAt_snd.mdifferentiableWithinAt

@[fun_prop]
theorem mdifferentiable_snd : MDifferentiable (I.prod I') I' (Prod.snd : M × M' → M') := fun _ =>
  mdifferentiableAt_snd

theorem mdifferentiableOn_snd {s : Set (M × M')} : MDifferentiableOn (I.prod I') I' Prod.snd s :=
  mdifferentiable_snd.mdifferentiableOn

@[simp, mfld_simps]
theorem mfderiv_snd {x : M × M'} :
    mfderiv (I.prod I') I' Prod.snd x =
      ContinuousLinearMap.snd 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2) :=
  (hasMFDerivAt_snd x).mfderiv

theorem mfderivWithin_snd {s : Set (M × M')} {x : M × M'}
    (hxs : UniqueMDiffWithinAt (I.prod I') s x) :
    mfderivWithin (I.prod I') I' Prod.snd s x =
      ContinuousLinearMap.snd 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2) := by
  rw [MDifferentiable.mfderivWithin mdifferentiableAt_snd hxs]; exact mfderiv_snd

theorem MDifferentiableWithinAt.fst {f : N → M × M'} {s : Set N} {x : N}
    (hf : MDifferentiableWithinAt J (I.prod I') f s x) :
    MDifferentiableWithinAt J I (fun x => (f x).1) s x :=
  mdifferentiableAt_fst.comp_mdifferentiableWithinAt x hf

theorem MDifferentiableAt.fst {f : N → M × M'} {x : N} (hf : MDifferentiableAt J (I.prod I') f x) :
    MDifferentiableAt J I (fun x => (f x).1) x :=
  mdifferentiableAt_fst.comp x hf

@[fun_prop]
theorem MDifferentiable.fst {f : N → M × M'} (hf : MDifferentiable J (I.prod I') f) :
    MDifferentiable J I fun x => (f x).1 :=
  mdifferentiable_fst.comp hf

theorem MDifferentiableWithinAt.snd {f : N → M × M'} {s : Set N} {x : N}
    (hf : MDifferentiableWithinAt J (I.prod I') f s x) :
    MDifferentiableWithinAt J I' (fun x => (f x).2) s x :=
  mdifferentiableAt_snd.comp_mdifferentiableWithinAt x hf

theorem MDifferentiableAt.snd {f : N → M × M'} {x : N} (hf : MDifferentiableAt J (I.prod I') f x) :
    MDifferentiableAt J I' (fun x => (f x).2) x :=
  mdifferentiableAt_snd.comp x hf

@[fun_prop]
theorem MDifferentiable.snd {f : N → M × M'} (hf : MDifferentiable J (I.prod I') f) :
    MDifferentiable J I' fun x => (f x).2 :=
  mdifferentiable_snd.comp hf

theorem mdifferentiableWithinAt_prod_iff (f : M → M' × N') :
    MDifferentiableWithinAt I (I'.prod J') f s x ↔
      MDifferentiableWithinAt I I' (Prod.fst ∘ f) s x
      ∧ MDifferentiableWithinAt I J' (Prod.snd ∘ f) s x :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prodMk h.2⟩

theorem mdifferentiableWithinAt_prod_module_iff (f : M → F₁ × F₂) :
    MDifferentiableWithinAt I 𝓘(𝕜, F₁ × F₂) f s x ↔
      MDifferentiableWithinAt I 𝓘(𝕜, F₁) (Prod.fst ∘ f) s x ∧
      MDifferentiableWithinAt I 𝓘(𝕜, F₂) (Prod.snd ∘ f) s x := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mdifferentiableWithinAt_prod_iff f

theorem mdifferentiableAt_prod_iff (f : M → M' × N') :
    MDifferentiableAt I (I'.prod J') f x ↔
      MDifferentiableAt I I' (Prod.fst ∘ f) x ∧ MDifferentiableAt I J' (Prod.snd ∘ f) x := by
  simp_rw [← mdifferentiableWithinAt_univ]; exact mdifferentiableWithinAt_prod_iff f

theorem mdifferentiableAt_prod_module_iff (f : M → F₁ × F₂) :
    MDifferentiableAt I 𝓘(𝕜, F₁ × F₂) f x ↔
      MDifferentiableAt I 𝓘(𝕜, F₁) (Prod.fst ∘ f) x
      ∧ MDifferentiableAt I 𝓘(𝕜, F₂) (Prod.snd ∘ f) x := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mdifferentiableAt_prod_iff f

theorem mdifferentiableOn_prod_iff (f : M → M' × N') :
    MDifferentiableOn I (I'.prod J') f s ↔
      MDifferentiableOn I I' (Prod.fst ∘ f) s ∧ MDifferentiableOn I J' (Prod.snd ∘ f) s :=
  ⟨fun h ↦ ⟨fun x hx ↦ ((mdifferentiableWithinAt_prod_iff f).1 (h x hx)).1,
      fun x hx ↦ ((mdifferentiableWithinAt_prod_iff f).1 (h x hx)).2⟩,
    fun h x hx ↦ (mdifferentiableWithinAt_prod_iff f).2 ⟨h.1 x hx, h.2 x hx⟩⟩

theorem mdifferentiableOn_prod_module_iff (f : M → F₁ × F₂) :
    MDifferentiableOn I 𝓘(𝕜, F₁ × F₂) f s ↔
      MDifferentiableOn I 𝓘(𝕜, F₁) (Prod.fst ∘ f) s
      ∧ MDifferentiableOn I 𝓘(𝕜, F₂) (Prod.snd ∘ f) s := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mdifferentiableOn_prod_iff f

theorem mdifferentiable_prod_iff (f : M → M' × N') :
    MDifferentiable I (I'.prod J') f ↔
      MDifferentiable I I' (Prod.fst ∘ f) ∧ MDifferentiable I J' (Prod.snd ∘ f) :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => by convert h.1.prodMk h.2⟩

theorem mdifferentiable_prod_module_iff (f : M → F₁ × F₂) :
    MDifferentiable I 𝓘(𝕜, F₁ × F₂) f ↔
      MDifferentiable I 𝓘(𝕜, F₁) (Prod.fst ∘ f) ∧ MDifferentiable I 𝓘(𝕜, F₂) (Prod.snd ∘ f) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mdifferentiable_prod_iff f


section prodMap

variable {f : M → M'} {g : N → N'} {r : Set N} {y : N}

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
theorem MDifferentiableWithinAt.prodMap' {p : M × N} (hf : MDifferentiableWithinAt I I' f s p.1)
    (hg : MDifferentiableWithinAt J J' g r p.2) :
    MDifferentiableWithinAt (I.prod J) (I'.prod J') (Prod.map f g) (s ×ˢ r) p :=
  (hf.comp p mdifferentiableWithinAt_fst (prod_subset_preimage_fst _ _)).prodMk <|
    hg.comp p mdifferentiableWithinAt_snd (prod_subset_preimage_snd _ _)

theorem MDifferentiableWithinAt.prodMap (hf : MDifferentiableWithinAt I I' f s x)
    (hg : MDifferentiableWithinAt J J' g r y) :
    MDifferentiableWithinAt (I.prod J) (I'.prod J') (Prod.map f g) (s ×ˢ r) (x, y) :=
  MDifferentiableWithinAt.prodMap' hf hg

theorem MDifferentiableAt.prodMap (hf : MDifferentiableAt I I' f x)
    (hg : MDifferentiableAt J J' g y) :
    MDifferentiableAt (I.prod J) (I'.prod J') (Prod.map f g) (x, y) := by
  rw [← mdifferentiableWithinAt_univ] at *
  convert hf.prodMap hg
  exact univ_prod_univ.symm

/-- Variant of `MDifferentiableAt.prod_map` in which the point in the product is given as `p`
instead of a pair `(x, y)`. -/
theorem MDifferentiableAt.prodMap' {p : M × N} (hf : MDifferentiableAt I I' f p.1)
    (hg : MDifferentiableAt J J' g p.2) :
    MDifferentiableAt (I.prod J) (I'.prod J') (Prod.map f g) p :=
  hf.prodMap hg

theorem MDifferentiableOn.prodMap (hf : MDifferentiableOn I I' f s)
    (hg : MDifferentiableOn J J' g r) :
    MDifferentiableOn (I.prod J) (I'.prod J') (Prod.map f g) (s ×ˢ r) :=
  (hf.comp mdifferentiableOn_fst (prod_subset_preimage_fst _ _)).prodMk <|
    hg.comp mdifferentiableOn_snd (prod_subset_preimage_snd _ _)

theorem MDifferentiable.prodMap (hf : MDifferentiable I I' f) (hg : MDifferentiable J J' g) :
    MDifferentiable (I.prod J) (I'.prod J') (Prod.map f g) := fun p ↦
  (hf p.1).prodMap' (hg p.2)

set_option backward.isDefEq.respectTransparency false in
set_option linter.flexible false in -- TODO: fix non-terminal simp_all followed by use
lemma HasMFDerivWithinAt.prodMap {s : Set <| M × M'} {p : M × M'} {f : M → N} {g : M' → N'}
    {df : TangentSpace I p.1 →L[𝕜] TangentSpace J (f p.1)}
    (hf : HasMFDerivWithinAt I J f (Prod.fst '' s) p.1 df)
    {dg : TangentSpace I' p.2 →L[𝕜] TangentSpace J' (g p.2)}
    (hg : HasMFDerivWithinAt I' J' g (Prod.snd '' s) p.2 dg) :
    HasMFDerivWithinAt (I.prod I') (J.prod J') (Prod.map f g) s p (df.prodMap dg) := by
  refine ⟨hf.1.prodMap hg.1 |>.mono (by grind), ?_⟩
  have better : ((extChartAt (I.prod I') p).symm ⁻¹' s ∩ range ↑(I.prod I')) ⊆
      ((extChartAt I p.1).symm ⁻¹' (Prod.fst '' s) ∩ range I) ×ˢ
        ((extChartAt I' p.2).symm ⁻¹' (Prod.snd '' s) ∩ range I') := by
    simp only [mfld_simps]
    rw [range_prodMap, I.toPartialEquiv.prod_symm, (chartAt H p.1).toPartialEquiv.prod_symm]
    -- This is very tedious; a nicer proof is welcome!
    intro p₀ ⟨hp₀, ⟨hp₁₁, hp₁₂⟩⟩
    refine ⟨⟨?_, by assumption⟩, ⟨?_, by assumption⟩⟩
    · simp_all
      use (chartAt H' p.2).symm <| I'.symm p₀.2
    · simp_all
      use (chartAt H p.1).symm <| I.symm p₀.1
  rw [writtenInExtChartAt_prod]
  apply HasFDerivWithinAt.mono ?_ better
  apply HasFDerivWithinAt.prodMap
  exacts [hf.2.mono (fst_image_prod_subset ..), hg.2.mono (snd_image_prod_subset ..)]

set_option backward.isDefEq.respectTransparency false in
lemma HasMFDerivAt.prodMap {p : M × M'} {f : M → N} {g : M' → N'}
    {df : TangentSpace I p.1 →L[𝕜] TangentSpace J (f p.1)} (hf : HasMFDerivAt I J f p.1 df)
    {dg : TangentSpace I' p.2 →L[𝕜] TangentSpace J' (g p.2)} (hg : HasMFDerivAt I' J' g p.2 dg) :
    HasMFDerivAt (I.prod I') (J.prod J') (Prod.map f g) p
      ((mfderiv I J f p.1).prodMap (mfderiv I' J' g p.2)) := by
  simp_rw [← hasMFDerivWithinAt_univ, ← mfderivWithin_univ, ← univ_prod_univ]
  convert hf.hasMFDerivWithinAt.prodMap hg.hasMFDerivWithinAt
  · rw [mfderivWithin_univ]; exact hf.mfderiv
  · rw [mfderivWithin_univ]; exact hg.mfderiv

-- Note: this lemma does not apply easily to an arbitrary subset `s ⊆ M × M'` as
-- unique differentiability on `(Prod.fst '' s)` and `(Prod.snd '' s)` does not imply
-- unique differentiability on `s`: a priori, `(Prod.fst '' s) × (Prod.fst '' s)`
-- could be a strict superset of `s`.
lemma mfderivWithin_prodMap {p : M × M'} {t : Set M'} {f : M → N} {g : M' → N'}
    (hf : MDifferentiableWithinAt I J f s p.1) (hg : MDifferentiableWithinAt I' J' g t p.2)
    (hs : UniqueMDiffWithinAt I s p.1) (ht : UniqueMDiffWithinAt I' t p.2) :
    mfderivWithin (I.prod I') (J.prod J') (Prod.map f g) (s ×ˢ t) p
      = (mfderivWithin I J f s p.1).prodMap (mfderivWithin I' J' g t p.2) := by
  have hf' : HasMFDerivWithinAt I J f (Prod.fst '' s ×ˢ t) p.1 (mfderivWithin I J f s p.1) :=
    hf.hasMFDerivWithinAt.mono (by grind)
  have hg' : HasMFDerivWithinAt I' J' g (Prod.snd '' s ×ˢ t) p.2 (mfderivWithin I' J' g t p.2) :=
    hg.hasMFDerivWithinAt.mono (by grind)
  exact (hf'.prodMap hg').mfderivWithin (hs.prod ht)

lemma mfderiv_prodMap {p : M × M'} {f : M → N} {g : M' → N'}
    (hf : MDifferentiableAt I J f p.1) (hg : MDifferentiableAt I' J' g p.2) :
    mfderiv (I.prod I') (J.prod J') (Prod.map f g) p
      = (mfderiv I J f p.1).prodMap (mfderiv I' J' g p.2) := by
  simp_rw [← mfderivWithin_univ, ← univ_prod_univ]
  exact mfderivWithin_prodMap hf.mdifferentiableWithinAt hg.mdifferentiableWithinAt
    (uniqueMDiffWithinAt_univ I) (uniqueMDiffWithinAt_univ I')

end prodMap

@[simp, mfld_simps]
theorem tangentMap_prodSnd {p : TangentBundle (I.prod I') (M × M')} :
    tangentMap (I.prod I') I' Prod.snd p = ⟨p.proj.2, p.2.2⟩ := by
  simp [tangentMap]; rfl

theorem tangentMapWithin_prodSnd {s : Set (M × M')} {p : TangentBundle (I.prod I') (M × M')}
    (hs : UniqueMDiffWithinAt (I.prod I') s p.proj) :
    tangentMapWithin (I.prod I') I' Prod.snd s p = ⟨p.proj.2, p.2.2⟩ := by
  simp only [tangentMapWithin]
  rw [mfderivWithin_snd hs]
  rcases p with ⟨⟩; rfl

-- Kept as an alias for discoverability.
alias MDifferentiableAt.mfderiv_prod := mfderiv_prodMk

set_option backward.isDefEq.respectTransparency false in
theorem mfderiv_prod_left {x₀ : M} {y₀ : M'} :
    mfderiv I (I.prod I') (fun x => (x, y₀)) x₀ =
      ContinuousLinearMap.inl 𝕜 (TangentSpace I x₀) (TangentSpace I' y₀) := by
  refine (mdifferentiableAt_id.mfderiv_prod mdifferentiableAt_const).trans ?_
  rw [mfderiv_id, mfderiv_const, ContinuousLinearMap.inl]

theorem tangentMap_prod_left {p : TangentBundle I M} {y₀ : M'} :
    tangentMap I (I.prod I') (fun x => (x, y₀)) p = ⟨(p.1, y₀), (p.2, 0)⟩ := by
  simp only [tangentMap, mfderiv_prod_left, TotalSpace.mk_inj]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem mfderiv_prod_right {x₀ : M} {y₀ : M'} :
    mfderiv I' (I.prod I') (fun y => (x₀, y)) y₀ =
      ContinuousLinearMap.inr 𝕜 (TangentSpace I x₀) (TangentSpace I' y₀) := by
  refine (mdifferentiableAt_const.mfderiv_prod mdifferentiableAt_id).trans ?_
  rw [mfderiv_id, mfderiv_const, ContinuousLinearMap.inr]

theorem tangentMap_prod_right {p : TangentBundle I' M'} {x₀ : M} :
    tangentMap I' (I.prod I') (fun y => (x₀, y)) p = ⟨(x₀, p.1), (0, p.2)⟩ := by
  simp only [tangentMap, mfderiv_prod_right, TotalSpace.mk_inj]
  rfl

/-- The total derivative of a function in two variables is the sum of the partial derivatives.
  Note that to state this (without casts) we need to be able to see through the definition of
  `TangentSpace`. -/
theorem mfderiv_prod_eq_add {f : M × M' → M''} {p : M × M'}
    (hf : MDifferentiableAt (I.prod I') I'' f p) :
    mfderiv (I.prod I') I'' f p =
        mfderiv (I.prod I') I'' (fun z : M × M' => f (z.1, p.2)) p +
          mfderiv (I.prod I') I'' (fun z : M × M' => f (p.1, z.2)) p := by
  erw [mfderiv_comp_of_eq hf (mdifferentiableAt_fst.prodMk mdifferentiableAt_const) rfl,
    mfderiv_comp_of_eq hf (mdifferentiableAt_const.prodMk mdifferentiableAt_snd) rfl,
    ← ContinuousLinearMap.comp_add,
    mdifferentiableAt_fst.mfderiv_prod mdifferentiableAt_const,
    mdifferentiableAt_const.mfderiv_prod mdifferentiableAt_snd, mfderiv_fst,
    mfderiv_snd, mfderiv_const, mfderiv_const]
  symm
  convert ContinuousLinearMap.comp_id <| mfderiv (.prod I I') I'' f (p.1, p.2)
  exact ContinuousLinearMap.coprod_inl_inr

/-- The total derivative of a function in two variables is the sum of the partial derivatives.
  Note that to state this (without casts) we need to be able to see through the definition of
  `TangentSpace`. Version in terms of the one-variable derivatives. -/
theorem mfderiv_prod_eq_add_comp {f : M × M' → M''} {p : M × M'}
    (hf : MDifferentiableAt (I.prod I') I'' f p) :
    mfderiv (I.prod I') I'' f p =
        (mfderiv I I'' (fun z : M => f (z, p.2)) p.1) ∘L (id (ContinuousLinearMap.fst 𝕜 E E') :
          (TangentSpace (I.prod I') p) →L[𝕜] (TangentSpace I p.1)) +
        (mfderiv I' I'' (fun z : M' => f (p.1, z)) p.2) ∘L (id (ContinuousLinearMap.snd 𝕜 E E') :
          (TangentSpace (I.prod I') p) →L[𝕜] (TangentSpace I' p.2)) := by
  rw [mfderiv_prod_eq_add hf]
  congr
  · have : (fun z : M × M' => f (z.1, p.2)) = (fun z : M => f (z, p.2)) ∘ Prod.fst := rfl
    rw [this, mfderiv_comp (I' := I)]
    · simp only [mfderiv_fst, id_eq]
      rfl
    · exact hf.comp _ (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
    · exact mdifferentiableAt_fst
  · have : (fun z : M × M' => f (p.1, z.2)) = (fun z : M' => f (p.1, z)) ∘ Prod.snd := rfl
    rw [this, mfderiv_comp (I' := I')]
    · simp only [mfderiv_snd, id_eq]
      rfl
    · exact hf.comp _ (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
    · exact mdifferentiableAt_snd

/-- The total derivative of a function in two variables is the sum of the partial derivatives.
  Note that to state this (without casts) we need to be able to see through the definition of
  `TangentSpace`. Version in terms of the one-variable derivatives. -/
theorem mfderiv_prod_eq_add_apply {f : M × M' → M''} {p : M × M'} {v : TangentSpace (I.prod I') p}
    (hf : MDifferentiableAt (I.prod I') I'' f p) :
    mfderiv (I.prod I') I'' f p v =
      mfderiv I I'' (fun z : M => f (z, p.2)) p.1 v.1 +
      mfderiv I' I'' (fun z : M' => f (p.1, z)) p.2 v.2 := by
  rw [mfderiv_prod_eq_add_comp hf]
  rfl

end Prod

section disjointUnion

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] {p : M ⊕ M'}

/-- In extended charts at `p`, `Sum.swap` looks like the identity near `p`. -/
lemma writtenInExtChartAt_sumSwap_eventuallyEq_id :
    writtenInExtChartAt I I p Sum.swap =ᶠ[𝓝[range I] (I <| chartAt H p p)] id := by
  cases p with
    | inl x =>
      let t := I.symm ⁻¹' (chartAt H x).target ∩ range I
      have : EqOn (writtenInExtChartAt I I (Sum.inl x) (@Sum.swap M M')) id t := by
        intro y hy
        simp only [writtenInExtChartAt, extChartAt, Sum.swap_inl,
          ChartedSpace.sum_chartAt_inl, ChartedSpace.sum_chartAt_inr]
        dsimp
        rw [Sum.inr_injective.extend_apply, (chartAt H x).right_inv (by grind)]
        exact I.right_inv (by grind)
      apply Filter.eventually_of_mem ?_ this
      rw [Filter.inter_mem_iff]
      refine ⟨I.continuousWithinAt_symm.preimage_mem_nhdsWithin ?_, self_mem_nhdsWithin⟩
      exact (chartAt H x).open_target.mem_nhds (by simp)
    | inr x =>
      let t := I.symm ⁻¹' (chartAt H x).target ∩ range I
      have : EqOn (writtenInExtChartAt I I (Sum.inr x) (@Sum.swap M M')) id t := by
        intro y hy
        simp only [writtenInExtChartAt, extChartAt, Sum.swap_inr,
          ChartedSpace.sum_chartAt_inl, ChartedSpace.sum_chartAt_inr]
        dsimp
        rw [Sum.inl_injective.extend_apply, (chartAt H x).right_inv (by grind)]
        exact I.right_inv (by grind)
      apply Filter.eventually_of_mem ?_ this
      rw [Filter.inter_mem_iff]
      refine ⟨I.continuousWithinAt_symm.preimage_mem_nhdsWithin ?_, self_mem_nhdsWithin⟩
      exact (chartAt H x).open_target.mem_nhds (by simp)

theorem hasMFDerivAt_sumSwap :
    HasMFDerivAt I I (@Sum.swap M M') p (ContinuousLinearMap.id 𝕜 (TangentSpace I p)) := by
  refine ⟨by fun_prop, ?_⟩
  apply (hasFDerivWithinAt_id _ (range I)).congr_of_eventuallyEq
  · exact writtenInExtChartAt_sumSwap_eventuallyEq_id
  · simp only [mfld_simps]
    cases p <;> simp

@[simp]
theorem mfderivWithin_sumSwap {s : Set (M ⊕ M')} (hs : UniqueMDiffWithinAt I s p) :
    mfderivWithin I I (@Sum.swap M M') s p = ContinuousLinearMap.id 𝕜 (TangentSpace I p) :=
  hasMFDerivAt_sumSwap.hasMFDerivWithinAt.mfderivWithin hs

@[simp]
theorem mfderiv_sumSwap :
    mfderiv I I (@Sum.swap M M') p = ContinuousLinearMap.id 𝕜 (TangentSpace I p) := by
  simpa [mfderivWithin_univ] using (mfderivWithin_sumSwap (uniqueMDiffWithinAt_univ I))

variable {f : M → N} (g : M' → N') {q : M} {q' : M'}

lemma writtenInExtChartAt_sumInl_eventuallyEq_id :
    (writtenInExtChartAt I I q (@Sum.inl M M')) =ᶠ[𝓝[Set.range I] (extChartAt I q q)] id := by
  have hmem : I.symm ⁻¹'
      (chartAt H q).target ∩ Set.range I ∈ 𝓝[Set.range I] (extChartAt I q q) := by
    rw [← I.image_eq (chartAt H q).target]
    exact (chartAt H q).extend_image_target_mem_nhds (mem_chart_source H q)
  filter_upwards [hmem] with y hy
  rcases hy with ⟨hyT, ⟨z, rfl⟩⟩
  simp [writtenInExtChartAt, extChartAt, ChartedSpace.sum_chartAt_inl,
    Sum.inl_injective.extend_apply <| chartAt H q,
    (chartAt H q).right_inv (by simpa [Set.mem_preimage, I.left_inv] using hyT)]

lemma writtenInExtChartAt_sumInr_eventuallyEq_id :
    (writtenInExtChartAt I I q' (@Sum.inr M M')) =ᶠ[𝓝[Set.range I] (extChartAt I q' q')] id := by
  have hmem : I.symm ⁻¹'
      (chartAt H q').target ∩ Set.range I ∈ 𝓝[Set.range I] (extChartAt I q' q') := by
    rw [← I.image_eq (chartAt H q').target]
    exact (chartAt H q').extend_image_target_mem_nhds (mem_chart_source H q')
  filter_upwards [hmem] with y hy
  rcases hy with ⟨hyT, ⟨z, rfl⟩⟩
  simp [writtenInExtChartAt, extChartAt, ChartedSpace.sum_chartAt_inr,
    Sum.inr_injective.extend_apply <| chartAt H q',
    (chartAt H q').right_inv (by simpa [Set.mem_preimage, I.left_inv] using hyT)]

theorem hasMFDerivWithinAt_inl :
    HasMFDerivWithinAt I I (@Sum.inl M M') s q (ContinuousLinearMap.id 𝕜 (TangentSpace I q)) := by
  refine ⟨by fun_prop, ?_⟩
  have : (writtenInExtChartAt I I q (@Sum.inl M M'))
      =ᶠ[𝓝[(extChartAt I q).symm ⁻¹' s ∩ Set.range I] (extChartAt I q q)] id :=
    writtenInExtChartAt_sumInl_eventuallyEq_id.filter_mono (nhdsWithin_mono _ (fun _y hy ↦ hy.2))
  exact (hasFDerivWithinAt_id (extChartAt I q q) _).congr_of_eventuallyEq this
    (by simp [writtenInExtChartAt, extChartAt])

theorem hasMFDerivAt_inl :
    HasMFDerivAt I I (@Sum.inl M M') q (ContinuousLinearMap.id 𝕜 (TangentSpace I p)) := by
  simpa [HasMFDerivAt, hasMFDerivWithinAt_univ] using hasMFDerivWithinAt_inl (s := Set.univ)

theorem hasMFDerivWithinAt_inr {t : Set M'} :
    HasMFDerivWithinAt I I (@Sum.inr M M') t q' (ContinuousLinearMap.id 𝕜 (TangentSpace I q')) := by
  refine ⟨by fun_prop, ?_⟩
  have : (writtenInExtChartAt I I q' (@Sum.inr M M'))
      =ᶠ[𝓝[(extChartAt I q').symm ⁻¹' t ∩ Set.range I] (extChartAt I q' q')] id :=
    writtenInExtChartAt_sumInr_eventuallyEq_id.filter_mono (nhdsWithin_mono _ (fun _y hy ↦ hy.2))
  exact (hasFDerivWithinAt_id (extChartAt I q' q') _).congr_of_eventuallyEq this
    (by simp [writtenInExtChartAt, extChartAt])

theorem hasMFDerivAt_inr :
    HasMFDerivAt I I (@Sum.inr M M') q' (ContinuousLinearMap.id 𝕜 (TangentSpace I p)) := by
  simpa [HasMFDerivAt, hasMFDerivWithinAt_univ] using hasMFDerivWithinAt_inr (t := Set.univ)

theorem mfderivWithin_sumInl (hU : UniqueMDiffWithinAt I s q) :
    mfderivWithin I I (@Sum.inl M M') s q = ContinuousLinearMap.id 𝕜 (TangentSpace I p) :=
  (hasMFDerivWithinAt_inl).mfderivWithin hU

theorem mfderiv_sumInl :
    mfderiv I I (@Sum.inl M M') q = ContinuousLinearMap.id 𝕜 (TangentSpace I p) := by
  simpa [mfderivWithin_univ] using (mfderivWithin_sumInl (uniqueMDiffWithinAt_univ I))

theorem mfderivWithin_sumInr {t : Set M'} (hU : UniqueMDiffWithinAt I t q') :
    mfderivWithin I I (@Sum.inr M M') t q' = ContinuousLinearMap.id 𝕜 (TangentSpace I q') :=
  (hasMFDerivWithinAt_inr).mfderivWithin hU

theorem mfderiv_sumInr :
    mfderiv I I (@Sum.inr M M') q' = ContinuousLinearMap.id 𝕜 (TangentSpace I q') := by
  simpa [mfderivWithin_univ] using (mfderivWithin_sumInr (uniqueMDiffWithinAt_univ I))

end disjointUnion

section Arithmetic

/-! #### Arithmetic

Note that in the `HasMFDerivAt` lemmas there is an abuse of the defeq between `E'` and
`TangentSpace 𝓘(𝕜, E') (f z)` (similarly for `g',F',p',q'`). In general this defeq is not
canonical, but in this case (the tangent space of a vector space) it is canonical.
-/

section Group

variable {z : M} {f g : M → E'} {f' g' : TangentSpace I z →L[𝕜] E'}

theorem HasMFDerivWithinAt.add {s : Set M} (hf : HasMFDerivWithinAt I 𝓘(𝕜, E') f s z f')
    (hg : HasMFDerivWithinAt I 𝓘(𝕜, E') g s z g') :
    HasMFDerivWithinAt I 𝓘(𝕜, E') (f + g) s z (f' + g') :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

theorem HasMFDerivAt.add (hf : HasMFDerivAt I 𝓘(𝕜, E') f z f')
    (hg : HasMFDerivAt I 𝓘(𝕜, E') g z g') : HasMFDerivAt I 𝓘(𝕜, E') (f + g) z (f' + g') :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

theorem MDifferentiableWithinAt.add {s : Set M} (hf : MDifferentiableWithinAt I 𝓘(𝕜, E') f s z)
    (hg : MDifferentiableWithinAt I 𝓘(𝕜, E') g s z) :
    MDifferentiableWithinAt I 𝓘(𝕜, E') (f + g) s z :=
  (hf.hasMFDerivWithinAt.add hg.hasMFDerivWithinAt).mdifferentiableWithinAt

theorem MDifferentiableAt.add (hf : MDifferentiableAt I 𝓘(𝕜, E') f z)
    (hg : MDifferentiableAt I 𝓘(𝕜, E') g z) : MDifferentiableAt I 𝓘(𝕜, E') (f + g) z :=
  (hf.hasMFDerivAt.add hg.hasMFDerivAt).mdifferentiableAt

theorem MDifferentiableOn.add {s : Set M} (hf : MDifferentiableOn I 𝓘(𝕜, E') f s)
    (hg : MDifferentiableOn I 𝓘(𝕜, E') g s) : MDifferentiableOn I 𝓘(𝕜, E') (f + g) s :=
  fun x hx ↦ (hf x hx).add (hg x hx)

@[fun_prop]
theorem MDifferentiable.add (hf : MDifferentiable I 𝓘(𝕜, E') f)
    (hg : MDifferentiable I 𝓘(𝕜, E') g) : MDifferentiable I 𝓘(𝕜, E') (f + g) := fun x =>
  (hf x).add (hg x)

-- Porting note: forcing types using `by exact`
theorem mfderiv_add (hf : MDifferentiableAt I 𝓘(𝕜, E') f z)
    (hg : MDifferentiableAt I 𝓘(𝕜, E') g z) :
    (by exact mfderiv I 𝓘(𝕜, E') (f + g) z : TangentSpace I z →L[𝕜] E') =
      (by exact mfderiv I 𝓘(𝕜, E') f z) + (by exact mfderiv I 𝓘(𝕜, E') g z) :=
  (hf.hasMFDerivAt.add hg.hasMFDerivAt).mfderiv

section sum
variable {ι : Type} {t : Finset ι} {f : ι → M → E'} {f' : ι → TangentSpace I z →L[𝕜] E'}

lemma HasMFDerivWithinAt.sum (hf : ∀ i ∈ t, HasMFDerivWithinAt I 𝓘(𝕜, E') (f i) s z (f' i)) :
    HasMFDerivWithinAt I 𝓘(𝕜, E') (∑ i ∈ t, f i) s z (∑ i ∈ t, f' i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hasMFDerivWithinAt_const ..
  | insert i s hi IH => grind [HasMFDerivWithinAt.add]

lemma HasMFDerivAt.sum (hf : ∀ i ∈ t, HasMFDerivAt I 𝓘(𝕜, E') (f i) z (f' i)) :
    HasMFDerivAt I 𝓘(𝕜, E') (∑ i ∈ t, f i) z (∑ i ∈ t, f' i) := by
  simp_all only [← hasMFDerivWithinAt_univ]
  exact HasMFDerivWithinAt.sum hf

lemma MDifferentiableWithinAt.sum
    (hf : ∀ i ∈ t, MDifferentiableWithinAt I 𝓘(𝕜, E') (f i) s z) :
    MDifferentiableWithinAt I 𝓘(𝕜, E') (∑ i ∈ t, f i) s z :=
  (HasMFDerivWithinAt.sum fun i hi ↦ (hf i hi).hasMFDerivWithinAt).mdifferentiableWithinAt

lemma MDifferentiableAt.sum (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(𝕜, E') (f i) z) :
    MDifferentiableAt I 𝓘(𝕜, E') (∑ i ∈ t, f i) z := by
  simp_all only [← mdifferentiableWithinAt_univ]
  exact .sum hf

lemma MDifferentiableOn.sum (hf : ∀ i ∈ t, MDifferentiableOn I 𝓘(𝕜, E') (f i) s) :
    MDifferentiableOn I 𝓘(𝕜, E') (∑ i ∈ t, f i) s :=
  fun z hz ↦ .sum fun i hi ↦ hf i hi z hz

@[fun_prop]
lemma MDifferentiable.sum (hf : ∀ i ∈ t, MDifferentiable I 𝓘(𝕜, E') (f i)) :
    MDifferentiable I 𝓘(𝕜, E') (∑ i ∈ t, f i) :=
  fun z ↦ .sum fun i hi ↦ hf i hi z

end sum

theorem HasMFDerivAt.const_smul (hf : HasMFDerivAt I 𝓘(𝕜, E') f z f') (s : 𝕜) :
    HasMFDerivAt I 𝓘(𝕜, E') (s • f) z (s • f') :=
  ⟨hf.1.const_smul s, hf.2.const_smul s⟩

theorem MDifferentiableAt.const_smul (hf : MDifferentiableAt I 𝓘(𝕜, E') f z) (s : 𝕜) :
    MDifferentiableAt I 𝓘(𝕜, E') (s • f) z :=
  (hf.hasMFDerivAt.const_smul s).mdifferentiableAt

@[fun_prop]
theorem MDifferentiable.const_smul (s : 𝕜) (hf : MDifferentiable I 𝓘(𝕜, E') f) :
    MDifferentiable I 𝓘(𝕜, E') (s • f) := fun x => (hf x).const_smul s

theorem const_smul_mfderiv (hf : MDifferentiableAt I 𝓘(𝕜, E') f z) (s : 𝕜) :
    (mfderiv I 𝓘(𝕜, E') (s • f) z : TangentSpace I z →L[𝕜] E') =
      (s • mfderiv I 𝓘(𝕜, E') f z : TangentSpace I z →L[𝕜] E') :=
  (hf.hasMFDerivAt.const_smul s).mfderiv

theorem HasMFDerivWithinAt.neg {s : Set M} (hf : HasMFDerivWithinAt I 𝓘(𝕜, E') f s z f') :
    HasMFDerivWithinAt I 𝓘(𝕜, E') (-f) s z (-f') :=
  ⟨hf.1.neg, hf.2.neg⟩

theorem HasMFDerivAt.neg (hf : HasMFDerivAt I 𝓘(𝕜, E') f z f') :
    HasMFDerivAt I 𝓘(𝕜, E') (-f) z (-f') :=
  ⟨hf.1.neg, hf.2.neg⟩

theorem hasMFDerivAt_neg : HasMFDerivAt I 𝓘(𝕜, E') (-f) z (-f') ↔ HasMFDerivAt I 𝓘(𝕜, E') f z f' :=
  ⟨fun hf => by convert hf.neg <;> rw [neg_neg], fun hf => hf.neg⟩

theorem MDifferentiableWithinAt.neg {s : Set M} (hf : MDifferentiableWithinAt I 𝓘(𝕜, E') f s z) :
    MDifferentiableWithinAt I 𝓘(𝕜, E') (-f) s z :=
  (hf.hasMFDerivWithinAt.neg).mdifferentiableWithinAt

theorem MDifferentiableAt.neg (hf : MDifferentiableAt I 𝓘(𝕜, E') f z) :
    MDifferentiableAt I 𝓘(𝕜, E') (-f) z :=
  hf.hasMFDerivAt.neg.mdifferentiableAt

theorem MDifferentiableOn.neg {s : Set M} (hf : MDifferentiableOn I 𝓘(𝕜, E') f s) :
    MDifferentiableOn I 𝓘(𝕜, E') (-f) s :=
  fun x hx ↦ (hf x hx).neg

theorem mdifferentiableAt_neg :
    MDifferentiableAt I 𝓘(𝕜, E') (-f) z ↔ MDifferentiableAt I 𝓘(𝕜, E') f z :=
  ⟨fun hf => by convert hf.neg; rw [neg_neg], fun hf => hf.neg⟩

@[fun_prop]
theorem MDifferentiable.neg (hf : MDifferentiable I 𝓘(𝕜, E') f) : MDifferentiable I 𝓘(𝕜, E') (-f) :=
  fun x => (hf x).neg

set_option backward.isDefEq.respectTransparency false in
theorem mfderiv_neg (f : M → E') (x : M) :
    (mfderiv I 𝓘(𝕜, E') (-f) x : TangentSpace I x →L[𝕜] E') =
      (-mfderiv I 𝓘(𝕜, E') f x : TangentSpace I x →L[𝕜] E') := by
  simp_rw [mfderiv]
  by_cases hf : MDifferentiableAt I 𝓘(𝕜, E') f x
  · exact hf.hasMFDerivAt.neg.mfderiv
  · rw [if_neg hf]; rw [← mdifferentiableAt_neg] at hf; rw [if_neg hf, neg_zero]

theorem HasMFDerivAt.sub (hf : HasMFDerivAt I 𝓘(𝕜, E') f z f')
    (hg : HasMFDerivAt I 𝓘(𝕜, E') g z g') : HasMFDerivAt I 𝓘(𝕜, E') (f - g) z (f' - g') :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

theorem MDifferentiableAt.sub (hf : MDifferentiableAt I 𝓘(𝕜, E') f z)
    (hg : MDifferentiableAt I 𝓘(𝕜, E') g z) : MDifferentiableAt I 𝓘(𝕜, E') (f - g) z :=
  (hf.hasMFDerivAt.sub hg.hasMFDerivAt).mdifferentiableAt

@[fun_prop]
theorem MDifferentiable.sub (hf : MDifferentiable I 𝓘(𝕜, E') f)
    (hg : MDifferentiable I 𝓘(𝕜, E') g) : MDifferentiable I 𝓘(𝕜, E') (f - g) := fun x =>
  (hf x).sub (hg x)

theorem mfderiv_sub (hf : MDifferentiableAt I 𝓘(𝕜, E') f z)
    (hg : MDifferentiableAt I 𝓘(𝕜, E') g z) :
    (by exact mfderiv I 𝓘(𝕜, E') (f - g) z : TangentSpace I z →L[𝕜] E') =
      (by exact mfderiv I 𝓘(𝕜, E') f z) - (by exact mfderiv I 𝓘(𝕜, E') g z) :=
  (hf.hasMFDerivAt.sub hg.hasMFDerivAt).mfderiv

end Group

section AlgebraOverRing
open scoped RightActions

variable {z : M} {F' : Type*} [NormedRing F'] [NormedAlgebra 𝕜 F'] {p q : M → F'}
  {p' q' : TangentSpace I z →L[𝕜] F'}

theorem HasMFDerivWithinAt.mul' (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
    (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (p * q) s z (p z • q' + p' <• q z : E →L[𝕜] F') :=
  ⟨hp.1.mul hq.1, by simpa only [mfld_simps] using hp.2.mul' hq.2⟩

theorem HasMFDerivAt.mul' (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
    (hq : HasMFDerivAt I 𝓘(𝕜, F') q z q') :
    HasMFDerivAt I 𝓘(𝕜, F') (p * q) z (p z • q' + p' <• q z : E →L[𝕜] F') :=
  hasMFDerivWithinAt_univ.mp <| hp.hasMFDerivWithinAt.mul' hq.hasMFDerivWithinAt

theorem MDifferentiableWithinAt.mul (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
    (hq : MDifferentiableWithinAt I 𝓘(𝕜, F') q s z) :
    MDifferentiableWithinAt I 𝓘(𝕜, F') (p * q) s z :=
  (hp.hasMFDerivWithinAt.mul' hq.hasMFDerivWithinAt).mdifferentiableWithinAt

theorem MDifferentiableAt.mul (hp : MDifferentiableAt I 𝓘(𝕜, F') p z)
    (hq : MDifferentiableAt I 𝓘(𝕜, F') q z) : MDifferentiableAt I 𝓘(𝕜, F') (p * q) z :=
  (hp.hasMFDerivAt.mul' hq.hasMFDerivAt).mdifferentiableAt

theorem MDifferentiableOn.mul (hp : MDifferentiableOn I 𝓘(𝕜, F') p s)
    (hq : MDifferentiableOn I 𝓘(𝕜, F') q s) : MDifferentiableOn I 𝓘(𝕜, F') (p * q) s := fun x hx =>
  (hp x hx).mul <| hq x hx

@[fun_prop]
theorem MDifferentiable.mul (hp : MDifferentiable I 𝓘(𝕜, F') p)
    (hq : MDifferentiable I 𝓘(𝕜, F') q) : MDifferentiable I 𝓘(𝕜, F') (p * q) := fun x =>
  (hp x).mul (hq x)

theorem MDifferentiableWithinAt.pow (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
    (n : ℕ) : MDifferentiableWithinAt I 𝓘(𝕜, F') (p ^ n) s z := by
  induction n with
  | zero => simpa [pow_zero] using mdifferentiableWithinAt_const
  | succ n hn => simpa [pow_succ] using hn.mul hp

theorem MDifferentiableAt.pow (hp : MDifferentiableAt I 𝓘(𝕜, F') p z) (n : ℕ) :
    MDifferentiableAt I 𝓘(𝕜, F') (p ^ n) z :=
  mdifferentiableWithinAt_univ.mp (hp.mdifferentiableWithinAt.pow n)

theorem MDifferentiableOn.pow (hp : MDifferentiableOn I 𝓘(𝕜, F') p s) (n : ℕ) :
    MDifferentiableOn I 𝓘(𝕜, F') (p ^ n) s := fun x hx => (hp x hx).pow n

theorem MDifferentiable.pow (hp : MDifferentiable I 𝓘(𝕜, F') p) (n : ℕ) :
    MDifferentiable I 𝓘(𝕜, F') (p ^ n) := fun x => (hp x).pow n

end AlgebraOverRing

section AlgebraOverCommRing

variable {z : M} {F' : Type*} [NormedCommRing F'] [NormedAlgebra 𝕜 F'] {p q : M → F'}
  {p' q' : TangentSpace I z →L[𝕜] F'}

set_option backward.isDefEq.respectTransparency false in
theorem HasMFDerivWithinAt.mul (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
    (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (p * q) s z (p z • q' + q z • p' : E →L[𝕜] F') := by
  convert hp.mul' hq; ext _; apply mul_comm

theorem HasMFDerivAt.mul (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
    (hq : HasMFDerivAt I 𝓘(𝕜, F') q z q') :
    HasMFDerivAt I 𝓘(𝕜, F') (p * q) z (p z • q' + q z • p' : E →L[𝕜] F') :=
  hasMFDerivWithinAt_univ.mp <| hp.hasMFDerivWithinAt.mul hq.hasMFDerivWithinAt

section prod
variable {ι : Type} {t : Finset ι} {f : ι → M → F'} {f' : ι → TangentSpace I z →L[𝕜] F'}

set_option backward.isDefEq.respectTransparency false in
lemma HasMFDerivWithinAt.prod [DecidableEq ι]
    (hf : ∀ i ∈ t, HasMFDerivWithinAt I 𝓘(𝕜, F') (f i) s z (f' i)) :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (∏ i ∈ t, f i) s z
      (∑ i ∈ t, (∏ j ∈ t.erase i, f j z) • (f' i)) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hasMFDerivWithinAt_const ..
  | insert i t hi IH =>
    rw [t.sum_insert hi, t.erase_insert hi, t.prod_insert hi, add_comm]
    rw [t.forall_mem_insert] at hf
    convert hf.1.mul (IH hf.2) using 2
    · simp only [t.smul_sum, ← mul_smul]
      refine t.sum_congr rfl (fun j hj ↦ ?_)
      rw [t.erase_insert_of_ne (by grind), Finset.prod_insert (by grind)]
    · simp

lemma HasMFDerivAt.prod [DecidableEq ι]
    (hf : ∀ i ∈ t, HasMFDerivAt I 𝓘(𝕜, F') (f i) z (f' i)) :
    HasMFDerivAt I 𝓘(𝕜, F') (∏ i ∈ t, f i) z (∑ i ∈ t, (∏ j ∈ t.erase i, f j z) • (f' i)) := by
  simp_all only [← hasMFDerivWithinAt_univ]
  exact HasMFDerivWithinAt.prod hf

lemma MDifferentiableWithinAt.prod
    (hf : ∀ i ∈ t, MDifferentiableWithinAt I 𝓘(𝕜, F') (f i) s z) :
    MDifferentiableWithinAt I 𝓘(𝕜, F') (∏ i ∈ t, f i) s z := by
  -- `by classical exact` to avoid needing a `DecidableEq` argument
  classical exact (HasMFDerivWithinAt.prod
    fun i hi ↦ (hf i hi).hasMFDerivWithinAt).mdifferentiableWithinAt

lemma MDifferentiableAt.prod (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(𝕜, F') (f i) z) :
    MDifferentiableAt I 𝓘(𝕜, F') (∏ i ∈ t, f i) z := by
  simp_all only [← mdifferentiableWithinAt_univ]
  exact MDifferentiableWithinAt.prod hf

lemma MDifferentiableOn.prod (hf : ∀ i ∈ t, MDifferentiableOn I 𝓘(𝕜, F') (f i) s) :
    MDifferentiableOn I 𝓘(𝕜, F') (∏ i ∈ t, f i) s :=
  fun z hz ↦ .prod fun i hi ↦ hf i hi z hz

@[fun_prop]
lemma MDifferentiable.prod (hf : ∀ i ∈ t, MDifferentiable I 𝓘(𝕜, F') (f i)) :
    MDifferentiable I 𝓘(𝕜, F') (∏ i ∈ t, f i) :=
  fun z ↦ .prod fun i hi ↦ hf i hi z

end prod

end AlgebraOverCommRing

end Arithmetic

end SpecificFunctions
