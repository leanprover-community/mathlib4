/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv

/-!
# Local diffeomorphisms between smooth manifolds

In this file, we define `C^n` local diffeomorphisms between manifolds.

A `C^n` map `f : M → N` is a **local diffeomorphism at `x`** iff there are neighbourhoods `s`
and `t` of `x` and `f x`, respectively such that `f` restricts to a diffeomorphism from `s` and `t`.
`f` is called a **local diffeomorphism** iff it is a local diffeomorphism at every `x ∈ M`.

## Main definitions
* `LocalDiffeomorphAt I J M N n f x`: `f` is a `C^n` local diffeomorphism at `x`
* `LocalDiffeomorph I J M N n f`: `f` is a `C^n` local diffeomorphism

## Main results
* Each of `Diffeomorph`, `LocalDiffeomorph`, and `LocalDiffeomorphAt` implies the next condition.
* `Diffeomorph.of_bijective_local_diffeomorph`: a bijective local diffeomorphisms is a diffeomorphism.
TODO: a local diffeomorphism is a diffeomorphism to its image

* `LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv`: if `f` is a local diffeomorphism
at `x`, the differential `mfderiv I J n f x` is a continuous linear isomorphism.
* `LocalDiffeomorphAt.of_DifferentialIsoAt`: conversely, if `f` is `C^n` at `x` and
`mfderiv I J n f x` is a linear isomorphism, `f` is a local diffeomorphism at `x`.

* `LocalDiffeomorph.differential_toContinuousLinearEquiv`: if `f` is a local diffeomorphism,
each differential `mfderiv I J n f x` is a continuous linear isomorphism.
* `LocalDiffeomorph.of_differentialInvertible`: Conversely, if `f` is `C^n` and each differential
is a linear isomorphism, `f` is a local diffeomorphism.

## Design decisions
xxx: fix this up: we don't do this, but instead model after IsLocalStructomorphAt

For all definitions, we use the junk value pattern: a local diffeomorphism at `x` is still given
by a function on all of `M`; its values outside its `source` are irrelevant. (This matches the
treatment of smooth manifolds and `LocalHomeomorph`.)

This combines with the second major design decision: all our definitions are bundled. That is,
we consider `f` together with a choice `g` of inverse. For local diffeomorphisms, `g` can take any
values outside of `f.target`.
A local diffeomorphism contains the data `f` and `g`, together with proofs that these define a
local diffeomorphism at each point.

## Tags
local diffeomorphism, manifold

-/

open Function Manifold Set SmoothManifoldWithCorners TopologicalSpace Topology
set_option autoImplicit false

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H]
  {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] {n : ℕ∞}

variable (I J M N n)

section LocalDiffeomorphAux
/-- A "diffeomorphism on" `s` is a function `f : M → N` such that `f` restricts to a diffeomorphism
`s → t` between open subsets of `M` and `N`, respectively.
This is an auxiliary definition and should not be used outside of this file. -/
structure LocalDiffeomorphAux extends LocalHomeomorph M N where
  contMDiffOn_toFun : ContMDiffOn I J n toFun source
  contMDiffOn_invFun : ContMDiffOn J I n invFun target

/-- Coercion of a `LocalDiffeomorphAux` to function.
Note that a `LocalDiffeomorphAux` is not `FunLike` (like `LocalHomeomorph`),
as `toFun` doesn't determine `invFun` outside of `target`. -/
instance : CoeFun (LocalDiffeomorphAux I J M N n) fun _ => M → N :=
  ⟨fun Φ => Φ.toFun'⟩

-- -- /-- For each `x : M`, a local diffeomorph is a diffeomorphism on some open set containing `x`. -/
-- -- FIXME: do I want to expose this outside of this file?
-- private noncomputable def LocalDiffeomorph.toDiffeomorphOn (h : LocalDiffeomorph I J M N n)
--     (x : M) : DiffeomorphOn I J M N n :=
--   (h.toLocalDiffeomorphAt x).toDiffeomorphOn

/-- A diffeomorphism is a local diffeomorphism. -/
def Diffeomorph.toLocalDiffeomorphAux (h : Diffeomorph I J M N n) : LocalDiffeomorphAux I J M N n :=
  {
    toLocalHomeomorph := h.toHomeomorph.toLocalHomeomorph
    contMDiffOn_toFun := fun x _ ↦ h.contMDiff_toFun x
    contMDiffOn_invFun := fun _ _ ↦ h.symm.contMDiffWithinAt
  }

/- We could add lots of additional API (following Diffeomorph and LocalHomeomorph), such as
- continuity and differentiability lemmas
- refl, symm and trans instances; lemmas between them.
As this declaration is meant for internal use only, we keep it simple. -/
end LocalDiffeomorphAux

/-- `f : M → N` is called a **`C^n` local diffeomorphism at *x*** iff there exist
  open sets `U ∋ x` and `V ∋ f x` and a diffeomorphism `Φ : U → V` such that `f = Φ` on `U`. -/
def IsLocalDiffeomorphAt (f : M → N) (x : M) : Prop :=
  ∃ Φ : LocalDiffeomorphAux I J M N n, x ∈ Φ.source ∧ EqOn f Φ Φ.source

/-- `f : M → N` is a **`C^n` local diffeomorph** iff it is a local diffeomorphism at each point. -/
def IsLocalDiffeomorph (f : M → N) : Prop :=
  ∀ x : M, IsLocalDiffeomorphAt I J M N n f x

lemma isLocalDiffeomorph_iff {f : M → N} :
  IsLocalDiffeomorph I J M N n f ↔ ∀ x : M, IsLocalDiffeomorphAt I J M N n f x := by rfl

/-- A `C^n` diffeomorphism is a local diffeomorphism. -/
lemma Diffeomorph.isLocalDiffeomorph (Φ : M ≃ₘ^n⟮I, J⟯ N) : IsLocalDiffeomorph I J M N n Φ :=
  fun _ ↦ ⟨Φ.toLocalDiffeomorphAux, by trivial, eqOn_refl Φ _⟩

/-- The image of a local diffeomorphism is open. -/
def LocalDiffeomorph.image {f : M → N} (hf : IsLocalDiffeomorph I J M N n f) : Opens N := by
  refine ⟨range f, ?_⟩
  apply isOpen_iff_forall_mem_open.mpr
  intro y hy

  -- Given y = f x ∈ range f, we need to find V ⊆ N open containing y.
  rw [mem_range] at hy
  rcases hy with ⟨x, hxy⟩

  -- As f is a local diffeo at x, on some open set U ∋ x it agrees with a diffeo Φ : U → V.
  choose Φ hyp using hf x
  rcases hyp with ⟨hxU, heq⟩
  -- Then V=Φ.target has the desired properties.
  refine ⟨Φ.target, ?_, Φ.open_target, ?_⟩
  · calc Φ.target
      _ = Φ '' Φ.source := by rw [LocalHomeomorph.image_source_eq_target]
      _ = f '' Φ.source := by rw [heq.image_eq]
      _ ⊆ range f  := image_subset_range f Φ.source
  · rw [← hxy, heq hxU]
    exact Φ.toLocalHomeomorph.map_source hxU

lemma LocalDiffeomorph.image_coe {f : M → N} (hf : IsLocalDiffeomorph I J M N n f) :
  (LocalDiffeomorph.image I J M N n hf).1 = range f := rfl

/-- A local diffeomorphism is a diffeomorphism to its image. -/
def LocalDiffeomorph.toDiffeomorphImage {f : M → N} (hf : IsLocalDiffeomorph I J M N n f) :
    Diffeomorph I J M (LocalDiffeomorph.image I J M N n hf) n := sorry
  -- can glue the inverses at each point... omitted for now

/-- A bijective local diffeomorphism is a diffeomorphism. -/
def Diffeomorph.of_bijective_local_diffeomorph {f : M → N} (hf : IsLocalDiffeomorph I J M N n f)
    (hf' : Bijective f) : Diffeomorph I J M N n := by
  have : (LocalDiffeomorph.image I J M N n hf).1 = (univ : Set N) := by
    rw [LocalDiffeomorph.image_coe]
    exact range_iff_surjective.mpr hf'.surjective
  -- Hmm: I cannot easily conclude `LocalDiffeomorph.image I J M N n hf = N` for type reasons...
  let r := LocalDiffeomorph.toDiffeomorphImage I J M N n hf
  set im := LocalDiffeomorph.image I J M N n hf
  have : im = ⟨univ, isOpen_univ⟩ := sorry -- is this true, as "the second component is unique"??!!
  rw [this] at r -- doesn't give what I want!
  sorry

section Differential
variable [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners J N]
  {f : M → N} {x : M} (hn : 1 ≤ n)

/-- Each differential of a `C^n` diffeomorphism (`n ≥ 1`) is a linear equivalence. -/
noncomputable def Diffeomorph.mfderiv_toContinuousLinearEquiv (hn : 1 ≤ n) (Φ : M ≃ₘ^n⟮I, J⟯ N)
    (x : M) : ContinuousLinearEquiv (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace J (Φ x)) := by
  let A := mfderiv I J Φ x
  let B := mfderiv J I Φ.invFun (Φ x)
  have inv1 : B.comp A = ContinuousLinearMap.id 𝕜 (TangentSpace I x) := calc B.comp A
    _ = mfderiv I I (Φ.invFun ∘ Φ) x :=
      (mfderiv_comp x (Φ.symm.mdifferentiable hn (Φ x)) (Φ.mdifferentiable hn x)).symm
    _ = mfderiv I I id x := mfderiv_congr (funext (fun x ↦ Φ.left_inv x))
    _ = ContinuousLinearMap.id 𝕜 (TangentSpace I x) := mfderiv_id I
  have inv2 : A.comp B = ContinuousLinearMap.id 𝕜 (TangentSpace J (Φ x)) := calc A.comp B
    _ = mfderiv J J (Φ ∘ Φ.invFun) (Φ x) := by
          -- Use the chain rule: need to rewrite both the base point Φ (Φ.invFun x)
          -- and the map Φ.invFun ∘ Φ. FIXME: can this be golfed?
          have hfat : MDifferentiableAt I J Φ x := Φ.mdifferentiable hn x
          rw [← (Φ.left_inv x)] at hfat
          let r := mfderiv_comp (Φ x) hfat (Φ.symm.mdifferentiable hn (Φ x))
          have : (Equiv.invFun Φ.toEquiv (Φ x)) = x := Φ.left_inv x
          rw [this] at r
          exact r.symm
    _ = mfderiv J J id (Φ x) := mfderiv_congr (funext (fun x ↦ Φ.right_inv x))
    _ = ContinuousLinearMap.id 𝕜 (TangentSpace J (Φ x)) := mfderiv_id J
  exact {
    toFun := A
    invFun := B
    left_inv := LeftInverse.of_composition inv1
    right_inv := RightInverse.of_composition inv2
    continuous_toFun := A.cont
    continuous_invFun := B.cont
    map_add' := fun x_1 y ↦ ContinuousLinearMap.map_add A x_1 y
    map_smul' := by intros; simp
  }

lemma Diffeomorph.mfderiv_toContinuousLinearEquiv_coe (Φ : M ≃ₘ^n⟮I, J⟯ N) {x : M} (hn : 1 ≤ n) :
    (Φ.mfderiv_toContinuousLinearEquiv hn x).toFun = mfderiv I J Φ x := rfl

/-- If `f` is a `C^n` local diffeomorphism at `x`, for `n ≥ 1`,
  the differential `df_x` is a linear equivalence. -/
lemma LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv (hf : IsLocalDiffeomorphAt I J M N n f x)
    (hn : 1 ≤ n) : ContinuousLinearEquiv (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace J (f x)) := by
  choose Φ hyp using hf
  rcases hyp with ⟨hxU, heq⟩
  -- have : mfderiv I J f x = mfderiv I J Φ x := calc mfderiv I J f x
  --   _ = mfderivWithin I J f Φ.source x := (mfderivWithin_of_isOpen Φ.open_source hxU).symm
  --   _ = mfderivWithin I J Φ Φ.source x :=
  --     mfderivWithin_congr (Φ.open_source.uniqueMDiffWithinAt hxU) heq (heq hxU)
  --   _ = mfderiv I J Φ x := mfderivWithin_of_isOpen Φ.open_source hxU
  sorry --exact Φ.mfderiv_toContinuousLinearEquiv hn ⟨x, hxU⟩

lemma LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv_coe (hf : IsLocalDiffeomorphAt I J M N n f x) :
    LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv I J M N n hf hn = mfderiv I J f x := by
  -- choose U V Φ hyp using hf--: fails, as `hf` is also part of the conclusion...
  -- rcases hyp with ⟨hxU, h2⟩
  sorry

/-- If `f : M → N` is differentiable at `x` and `mfderiv I J f x` is a linear isomorphism,
  then `f` is a local diffeomorphism at `x`. -/
def LocalDiffeomorphAt.of_mfderivIsomorphism
    {f' : TangentSpace I x →L[𝕜] TangentSpace J (f x)} (hf' : HasMFDerivAt I J f x f')
    {g' : TangentSpace J (f x) →L[𝕜] TangentSpace I x} (hinv₁ : g' ∘ f' = id) (hinv₂ : f' ∘ g' = id)
    (hf : ContMDiffAt I J n f x) : IsLocalDiffeomorphAt I J M N n f x := by
  -- XXX: is hypothesis `hf` required?
  -- xxx: which is more convenient later: stating hinv₁₂ with ∘ or with comp?
  have : ContinuousLinearEquiv (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace J (f x)) :=
    {
      toFun := f'
      invFun := g'
      continuous_toFun := f'.cont
      continuous_invFun := g'.cont
      map_add' := fun x_1 y ↦ ContinuousLinearMap.map_add f' x_1 y
      map_smul' := by intros; simp
      left_inv := congrFun hinv₁
      right_inv := congrFun hinv₂
    }
  -- Now, we apply the inverse function theorem: not yet in mathlib.
  sorry

/-- If `f : M → N` is `C^n` and each differential `mfderiv I J f x` is a linear isomorphism,
  `f` is a local diffeomorphism. -/
-- TODO: that's not the right statement yet; need that each g_x is **continuous and linear**
-- how can I encode this nicely?
def LocalDiffeomorph.of_mfderivIsomorphism (hf : ContMDiff I J n f)
    {g' : TangentBundle J N → TangentBundle I M}
    (hg : ∀ x : M, Continuous (fun v ↦ (g' ⟨f x, v⟩).2))
    (hinv₁ : (tangentMap I J f) ∘ g' = id) (hinv₂ : g' ∘ (tangentMap I J f) = id) :
    IsLocalDiffeomorph I J M N n f := by
  intro x
  let realg' : TangentSpace J (f x) → TangentSpace I x := fun v ↦ (g' ⟨f x, v⟩).2
  -- TODO: upgrade this, once I have stated the right hypothesis
  let g' : TangentSpace J (f x) →L[𝕜] TangentSpace I x := sorry
  apply LocalDiffeomorphAt.of_mfderivIsomorphism (f' := mfderiv I J f x) (g' := g') (hf := hf x)
  · sorry -- routine stuff about differentiability
  · -- apply hinv₂ at point x and simp lemmas about tangentMap I J f
    have : realg' ∘ (mfderiv I J f x) = id := sorry
    sorry -- now, if g' were what I want, I'd be happy
  · sorry -- similar: apply hinv₁ instead

variable (x) in
/-- If `f` is a `C^n` local diffeomorphism (`n ≥ 1`), each differential is a linear equivalence. -/
lemma LocalDiffeomorph.mfderiv_toContinuousLinearEquiv (hf : IsLocalDiffeomorph I J M N n f)
    (hn : 1 ≤ n) : ContinuousLinearEquiv (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace J (f x)) :=
  LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv I J M N n (hf x) hn

variable (x) in
lemma LocalDiffeomorph.mfderiv_toContinuousLinearEquiv_coe (hf : IsLocalDiffeomorph I J M N n f):
    LocalDiffeomorph.mfderiv_toContinuousLinearEquiv I J M N n x hf hn = mfderiv I J f x := by
  let r := LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv_coe I J M N n hn (hf x)
  have : ↑(LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv I J M N n (hf x) hn) =
    ↑(LocalDiffeomorph.mfderiv_toContinuousLinearEquiv I J M N n x hf hn) :=
    sorry -- why is this not obvious?
  exact this ▸ r

end Differential
