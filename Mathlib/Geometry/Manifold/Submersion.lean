/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.LocalSourceTargetProperty
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.Analysis.Normed.Module.Shrink
public import Mathlib.Topology.Algebra.Module.TransferInstance

/-! # Smooth submersions

A detailed module doc-string will be written in due time.

**Please do not work** on this file without prior discussion with Michael Rothgang.
This will be the topic of Samantha Naranjo's master's thesis, and it's nice to coordinate.

-/

open scoped Topology ContDiff

open Function Set Manifold

public noncomputable section

universe u
variable {E : Type u} {𝕜 E' E'' E''' F F' H H' G G' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E''']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}

variable {M M' N N' : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {n : WithTop ℕ∞}

variable (F I J M N) in
/-- The local property of being a submersion at `x` -/
def SubmersionAtProp :
    ((M → N) → OpenPartialHomeomorph M H → OpenPartialHomeomorph N G → Prop) :=
  fun f domChart codChart ↦
    ∃ equiv : E ≃L[𝕜] (E'' × F),
    EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv)
      (domChart.extend I).target

omit [ChartedSpace H M] [ChartedSpace G N] in
/-- Being a submersion at `x` is a local property. -/
lemma isLocalSourceTargetProperty_submersionAtProp :
    IsLocalSourceTargetProperty (SubmersionAtProp F I J M N) where
  mono_source {f φ ψ s} hs := fun ⟨equiv, hf⟩ ↦ ⟨equiv, hf.mono (by simp; grind)⟩
  congr {f g φ ψ} hfg hf := by
    obtain ⟨equiv, hf⟩ := hf
    refine ⟨equiv, EqOn.trans (fun x hx ↦ ?_) (hf.mono (by simp))⟩
    have : ((φ.extend I).symm) x ∈ φ.source := by simp_all
    grind

variable (F I J n) in
/-- `f : M → N` is a `C^k` submersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `(u, v) ↦ u`.
Additionally, we demand that `f` map `φ.source` into `ψ.source`.

NB. We don't know the particular atlasses used for `M` and `N`, so asking for `φ` and `ψ` to be
in the `atlas` would be too optimistic: lying in the `maximalAtlas` is sufficient.
-/
def IsSubmersionAtOfComplement (f : M → N) (x : M) : Prop :=
  LiftSourceTargetPropertyAt I J n f x (SubmersionAtProp F I J M N)

variable (I J n) in
def IsSubmersionAt (f : M → N) (x : M) : Prop :=
  ∃ (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F),
    IsSubmersionAtOfComplement F I J n f x

namespace IsSubmersionAtOfComplement

variable {f : M → N} {x : M}

-- TODO(Samantha): add basic API lemmas, such as
-- constructors
-- data fields like `codChart` and their basic properties
-- congruence lemmas

def equiv (h : IsSubmersionAtOfComplement F I J n f x) : E ≃L[𝕜] E'' × F := by
  sorry

lemma small (hf : IsSubmersionAtOfComplement F I J n f x) : Small.{u} F :=
  small_of_injective <| hf.equiv.symm.injective.comp (Prod.mk_right_injective 0)

/-- Given a submersion `f` at `x`, this is a choice of complement which lives in the same universe
as the model space for the co-domain of `f`: this is useful to avoid universe restrictions. -/
@[expose] def smallComplement (hf : IsSubmersionAtOfComplement F I J n f x) : Type u :=
  haveI := hf.small
  Shrink.{u} F

instance (hf : IsSubmersionAtOfComplement F I J n f x) : NormedAddCommGroup hf.smallComplement := by
  haveI := hf.small
  unfold smallComplement
  infer_instance

instance (hf : IsSubmersionAtOfComplement F I J n f x) : NormedSpace 𝕜 hf.smallComplement := by
  haveI := hf.small
  unfold smallComplement
  infer_instance

-- smallEquiv and friends

/- The set of points where `IsSubmersionAtOfComplement` holds is open. -/
lemma _root_.IsOpen.isSubmersionAtOfComplement :
    IsOpen {x | IsSubmersionAtOfComplement F I J n f x} := by
  simp_rw [IsSubmersionAtOfComplement]
  exact .liftSourceTargetPropertyAt

/-- If `f: M → N` and `g: M' × N'` are submersions at `x` and `x'`, respectively,
then `f × g: M × N → M' × N'` is a submersion at `(x, x')`. -/
theorem prodMap {f : M → N} {g : M' → N'} {x' : M'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsSubmersionAtOfComplement F I J n f x)
    (hg : IsSubmersionAtOfComplement F' I' J' n g x') :
    IsSubmersionAtOfComplement (F × F') (I.prod I') (J.prod J') n (Prod.map f g) (x, x') := by
  sorry

/-- If `f` is a submersion at `x` w.r.t. some complement `F`, it is a submersion at `x`.

Note that the proof contains a small formalisation-related subtlety: `F` can live in any universe,
while being a submersion at `x` requires the existence of a complement in the same universe as
the model normed space of `N`. This is solved by `smallComplement` and `smallEquiv`.
-/
lemma isSubmersionAt (h : IsSubmersionAtOfComplement F I J n f x) :
    IsSubmersionAt I J n f x := by
  rw [IsSubmersionAt]
  use h.smallComplement, by infer_instance, by infer_instance
  sorry -- will follow once the API is added!
  -- exact (IsSubmersionAtOfComplement.congr_F h.smallEquiv).mp h

/-- A `C^n` submersion at `x` is `C^n` at `x`. -/
theorem contMDiffAt (h : IsSubmersionAtOfComplement F I J n f x) : ContMDiffAt I J n f x :=
  sorry

-- TODO: add characterisation in terms of the differential admitting a bounded right inverse!

end IsSubmersionAtOfComplement

namespace IsSubmersionAt

variable {f : M → N} {x : M}

-- TODO(Samantha): add basic API lemmas, such as
-- constructors
-- data fields like `codChart` and their basic properties
-- congruence lemmas

/-- A choice of complement of the model normed space `E` of `M` in the model normed space
`E'` of `N` -/
def complement (h : IsSubmersionAt I J n f x) : Type u := by sorry

noncomputable instance (h : IsSubmersionAt I J n f x) : NormedAddCommGroup h.complement := by
  sorry

noncomputable instance (h : IsSubmersionAt I J n f x) : NormedSpace 𝕜 h.complement := by
  sorry

lemma isSubmersionAtOfComplement_complement (h : IsSubmersionAt I J n f x) :
    IsSubmersionAtOfComplement h.complement I J n f x := by
  sorry

def equiv (h : IsSubmersionAt I J n f x) : E ≃L[𝕜] E'' × F := by
  sorry

/- The set of points where `IsSubmersionAt` holds is open. -/
lemma _root_.IsOpen.isSubmersionAt :
    IsOpen {x | IsSubmersionAt I J n f x} := sorry

/-- If `f: M → N` and `g: M' × N'` are submersions at `x` and `x'`, respectively,
then `f × g: M × N → M' × N'` is a submersion at `(x, x')`. -/
theorem prodMap {f : M → N} {g : M' → N'} {x' : M'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsSubmersionAt I J n f x)
    (hg : IsSubmersionAt I' J' n g x') :
    IsSubmersionAt (I.prod I') (J.prod J') n (Prod.map f g) (x, x') := by
  sorry

/-- A `C^n` submersion at `x` is `C^n` at `x`. -/
theorem contMDiffAt (h : IsSubmersionAtOfComplement F I J n f x) : ContMDiffAt I J n f x :=
  sorry

-- TODO: add characterisation in terms of the differential admitting a bounded right inverse!

end IsSubmersionAt

variable (F I J n) in
/-- `f : M → N` is a `C^k` submersion if around each point `x ∈ M`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
such that in these charts, `f` looks like `(u, v) ↦ u`.

In other words, `f` is a submersion at each `x ∈ M`.
-/
def IsSubmersionOfComplement (f : M → N) : Prop := ∀ x, IsSubmersionAtOfComplement F I J n f x

variable (I J n) in
/-- `f : M → N` is a `C^n` submersion if around each point `x ∈ M`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
such that in these charts, `f` looks like `(u, v) ↦ u`.

Implicit in this definition is an abstract choice `F` of a complement of `E` in `E'`:
being a submersion includes a choice of linear isomorphism between `E × F` and `E'`, which is where
the choice of `F` enters. If you need stronger control over the complement `F`,
use `IsSubmersionOfComplement` instead.

Note that our global choice of complement is a bit stronger than asking `f` to be a submersion at
each `x ∈ M` w.r.t. potentially varying complements: see `isSubmersionAt` for details.
-/
@[expose] def IsSubmersion (f : M → N) : Prop :=
  ∃ (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F),
    IsSubmersionOfComplement F I J n f

namespace IsSubmersionOfComplement

variable {f g : M → N}

/-- If `f` is a submersion, it is a submersion at each point. -/
lemma isSubmersionAt (h : IsSubmersionOfComplement F I J n f) (x : M) :
    IsSubmersionAtOfComplement F I J n f x :=
  h x

/-- If `f = g` and `f` is a submersion, so is `g`. -/
theorem congr (h : IsSubmersionOfComplement F I J n f) (heq : f = g) : IsSubmersionOfComplement F I J n g :=
  heq ▸ h

lemma trans_F (h : IsSubmersionOfComplement F I J n f) (e : F ≃L[𝕜] F') :
    IsSubmersionOfComplement F' I J n f :=
  sorry -- fun x ↦ (h x).trans_F e

/-- Being an immersion w.r.t. `F` is stable under replacing `F` by an isomorphic copy. -/
lemma congr_F (e : F ≃L[𝕜] F') :
    IsSubmersionOfComplement F I J n f ↔ IsSubmersionOfComplement F' I J n f :=
  ⟨fun h ↦ trans_F (e := e) h, fun h ↦ trans_F (e := e.symm) h⟩

/-- If `f` is a submersion w.r.t. some complement `F`, it is a submersion.

Note that the proof contains a small formalisation-related subtlety: `F` can live in any universe,
while being a submersion requires the existence of a complement in the same universe as
the model normed space of `N`. This is solved by `smallComplement` and `smallEquiv`.
-/
lemma isSubmersion (h : IsSubmersionOfComplement F I J n f) : IsSubmersion I J n f := by
  by_cases! hM : IsEmpty M
  · rw [IsSubmersion]
    use PUnit, by infer_instance, by infer_instance
    exact fun x ↦ (IsEmpty.false x).elim
  inhabit M
  let x : M := Inhabited.default
  use (h x).smallComplement, by infer_instance, by infer_instance
  sorry -- exact (IsSubmersionOfComplement.congr_F (h x).smallEquiv).mp h

open IsManifold in
/-- The identity map is a submersion with complement `PUnit`. -/
protected lemma id [IsManifold I n M] : IsSubmersionOfComplement PUnit I I n (@id M) := by
  intro x
  sorry /- apply IsSubmersionAtOfComplement.mk_of_continuousAt (continuousAt_id) (.prodUnique 𝕜 E _)
    (chartAt H x) (chartAt H x) (mem_chart_source H x) (mem_chart_source H x)
    (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas x)
  intro y hy
  have : I ((chartAt H x) ((chartAt H x).symm (I.symm y))) = y := by
    rw [(chartAt H x).right_inv (by simp_all), I.right_inv (by simp_all)]
  simpa -/

/-- If `f: M → N` and `g: M' × N'` are submersions, so is `f × g: M × N → M' × N'`. -/
theorem prodMap {f : M → N} {g : M' → N'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsSubmersionOfComplement F I J n f) (hg : IsSubmersionOfComplement F' I' J' n g) :
    IsSubmersionOfComplement (F × F') (I.prod I') (J.prod J') n (Prod.map f g) :=
  sorry --hf.isSubmersionAtOfComplement_complement.prodMap hg.isSubmersionAtOfComplement_complement
  --  |>.isSubmersionAt

/-- A `C^n` submersion is `C^n`. -/
theorem contMDiffAt (h : IsSubmersionOfComplement F I J n f) : ContMDiff I J n f :=
  sorry

-- TODO: add characterisation in terms of the differential admitting a bounded right inverse,
-- the the composition property

end IsSubmersionOfComplement

namespace IsSubmersion

variable {f g : M → N}

/-- A choice of complement of the model normed space `E` of `M` in the model normed space
`E'` of `N` -/
@[expose] def complement (h : IsSubmersion I J n f) : Type u := Classical.choose h

noncomputable instance (h : IsSubmersion I J n f) : NormedAddCommGroup h.complement :=
  Classical.choose <| Classical.choose_spec h

noncomputable instance (h : IsSubmersion I J n f) : NormedSpace 𝕜 h.complement :=
  Classical.choose <| Classical.choose_spec <| Classical.choose_spec h

lemma isSubmersionOfComplement_complement (h : IsSubmersion I J n f) :
    IsSubmersionOfComplement h.complement I J n f :=
  Classical.choose_spec <| Classical.choose_spec <| Classical.choose_spec h

/-- If `f: M → N` and `g: M' × N'` are submersions, so is `f × g: M × N → M' × N'`. -/
theorem prodMap {f : M → N} {g : M' → N'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsSubmersion I J n f) (hg : IsSubmersion I' J' n g) :
    IsSubmersion (I.prod I') (J.prod J') n (Prod.map f g) :=
  hf.isSubmersionOfComplement_complement.prodMap hg.isSubmersionOfComplement_complement
    |>.isSubmersion
#check IsSubmersionOfComplement.id
open IsManifold in
/-- The identity map is a submersion. -/
protected lemma id [IsManifold I n M] : IsSubmersion I I n (@id M) :=
  ⟨PUnit, by infer_instance, by infer_instance, sorry /-IsSubmersionOfComplement.id-/⟩

/-- A `C^n` submersion is `C^n`. -/
theorem contMDiff (h : IsSubmersion I J n f) : ContMDiff I J n f :=
  sorry

-- TODO: add characterisation in terms of the differential admitting a bounded right inverse,
-- the the composition property

end IsSubmersion

end
