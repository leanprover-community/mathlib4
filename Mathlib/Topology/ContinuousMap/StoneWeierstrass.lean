/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Heather Macbeth
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.Star.Real
public import Mathlib.Topology.Algebra.StarSubalgebra
public import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
public import Mathlib.Topology.ContinuousMap.ContinuousMapZero
public import Mathlib.Topology.ContinuousMap.Lattice
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Algebra.Order.Module.Basic

/-!
# The Stone-Weierstrass theorem

If a subalgebra `A` of `C(X, ℝ)`, where `X` is a compact topological space,
separates points, then it is dense.

We argue as follows.

* In any subalgebra `A` of `C(X, ℝ)`, if `f ∈ A`, then `abs f ∈ A.topologicalClosure`.
  This follows from the Weierstrass approximation theorem on `[-‖f‖, ‖f‖]` by
  approximating `abs` uniformly thereon by polynomials.
* This ensures that `A.topologicalClosure` is actually a sublattice:
  if it contains `f` and `g`, then it contains the pointwise supremum `f ⊔ g`
  and the pointwise infimum `f ⊓ g`.
* Any nonempty sublattice `L` of `C(X, ℝ)` which separates points is dense,
  by a nice argument approximating a given `f` above and below using separating functions.
  For each `x y : X`, we pick a function `g x y ∈ L` so `g x y x = f x` and `g x y y = f y`.
  By continuity these functions remain close to `f` on small patches around `x` and `y`.
  We use compactness to identify a certain finitely indexed infimum of finitely indexed supremums
  which is then close to `f` everywhere, obtaining the desired approximation.
* Finally we put these pieces together. `L = A.topologicalClosure` is a nonempty sublattice
  which separates points since `A` does, and so is dense (in fact equal to `⊤`).

We then prove the complex version for star subalgebras `A`, by separately approximating
the real and imaginary parts using the real subalgebra of real-valued functions in `A`
(which still separates points, by taking the norm-square of a separating function).

## Future work

Extend to cover the case of subalgebras of the continuous functions vanishing at infinity,
on non-compact spaces.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

assert_not_exists Unitization

noncomputable section

namespace ContinuousMap

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

open scoped Polynomial

/-- Turn a function `f : C(X, ℝ)` into a continuous map into `Set.Icc (-‖f‖) (‖f‖)`,
thereby explicitly attaching bounds.
-/
def attachBound (f : C(X, ℝ)) : C(X, Set.Icc (-‖f‖) ‖f‖) where
  toFun x := ⟨f x, ⟨neg_norm_le_apply f x, apply_le_norm f x⟩⟩

@[simp]
theorem attachBound_apply_coe (f : C(X, ℝ)) (x : X) : ((attachBound f) x : ℝ) = f x :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem polynomial_comp_attachBound (A : Subalgebra ℝ C(X, ℝ)) (f : A) (g : ℝ[X]) :
    (g.toContinuousMapOn (Set.Icc (-‖f‖) ‖f‖)).comp (f : C(X, ℝ)).attachBound =
      Polynomial.aeval f g := by
  ext
  simp only [Polynomial.aeval_subalgebra_coe, Polynomial.aeval_continuousMap_apply]
  simp

/-- Given a continuous function `f` in a subalgebra of `C(X, ℝ)`, postcomposing by a polynomial
gives another function in `A`.

This lemma proves something slightly more subtle than this:
we take `f`, and think of it as a function into the restricted target `Set.Icc (-‖f‖) ‖f‖)`,
and then postcompose with a polynomial function on that interval.
This is in fact the same situation as above, and so also gives a function in `A`.
-/
theorem polynomial_comp_attachBound_mem (A : Subalgebra ℝ C(X, ℝ)) (f : A) (g : ℝ[X]) :
    (g.toContinuousMapOn (Set.Icc (-‖f‖) ‖f‖)).comp (f : C(X, ℝ)).attachBound ∈ A := by
  rw [polynomial_comp_attachBound]
  apply SetLike.coe_mem

theorem comp_attachBound_mem_closure (A : Subalgebra ℝ C(X, ℝ)) (f : A)
    (p : C(Set.Icc (-‖f‖) ‖f‖, ℝ)) : p.comp (attachBound (f : C(X, ℝ))) ∈ A.topologicalClosure := by
  -- `p` itself is in the closure of polynomials, by the Weierstrass theorem,
  have mem_closure : p ∈ (polynomialFunctions (Set.Icc (-‖f‖) ‖f‖)).topologicalClosure :=
    continuousMap_mem_polynomialFunctions_closure _ _ p
  -- and so there are polynomials arbitrarily close.
  have frequently_mem_polynomials := mem_closure_iff_frequently.mp mem_closure
  -- To prove `p.comp (attachBound f)` is in the closure of `A`,
  -- we show there are elements of `A` arbitrarily close.
  apply mem_closure_iff_frequently.mpr
  -- To show that, we pull back the polynomials close to `p`,
  refine
    ((compRightContinuousMap ℝ (attachBound (f : C(X, ℝ)))).continuousAt
            p).tendsto.frequently_map
      _ ?_ frequently_mem_polynomials
  -- but need to show that those pullbacks are actually in `A`.
  rintro _ ⟨g, ⟨-, rfl⟩⟩
  simp only [SetLike.mem_coe, AlgHom.coe_toRingHom, compRightContinuousMap_apply,
    Polynomial.toContinuousMapOnAlgHom_apply]
  apply polynomial_comp_attachBound_mem

theorem abs_mem_subalgebra_closure (A : Subalgebra ℝ C(X, ℝ)) (f : A) :
    |(f : C(X, ℝ))| ∈ A.topologicalClosure := by
  let f' := attachBound (f : C(X, ℝ))
  let abs : C(Set.Icc (-‖f‖) ‖f‖, ℝ) := { toFun := fun x : Set.Icc (-‖f‖) ‖f‖ => |(x : ℝ)| }
  change abs.comp f' ∈ A.topologicalClosure
  apply comp_attachBound_mem_closure

theorem inf_mem_subalgebra_closure (A : Subalgebra ℝ C(X, ℝ)) (f g : A) :
    (f : C(X, ℝ)) ⊓ (g : C(X, ℝ)) ∈ A.topologicalClosure := by
  rw [inf_eq_half_smul_add_sub_abs_sub' ℝ]
  refine
    A.topologicalClosure.smul_mem
      (A.topologicalClosure.sub_mem
        (A.topologicalClosure.add_mem (A.le_topologicalClosure f.property)
          (A.le_topologicalClosure g.property))
        ?_)
      _
  exact mod_cast abs_mem_subalgebra_closure A _

theorem inf_mem_closed_subalgebra (A : Subalgebra ℝ C(X, ℝ)) (h : IsClosed (A : Set C(X, ℝ)))
    (f g : A) : (f : C(X, ℝ)) ⊓ (g : C(X, ℝ)) ∈ A := by
  convert inf_mem_subalgebra_closure A f g
  apply SetLike.ext'
  symm
  rw [Subalgebra.topologicalClosure_coe, closure_eq_iff_isClosed]
  exact h

theorem sup_mem_subalgebra_closure (A : Subalgebra ℝ C(X, ℝ)) (f g : A) :
    (f : C(X, ℝ)) ⊔ (g : C(X, ℝ)) ∈ A.topologicalClosure := by
  rw [sup_eq_half_smul_add_add_abs_sub' ℝ]
  refine
    A.topologicalClosure.smul_mem
      (A.topologicalClosure.add_mem
        (A.topologicalClosure.add_mem (A.le_topologicalClosure f.property)
          (A.le_topologicalClosure g.property))
        ?_)
      _
  exact mod_cast abs_mem_subalgebra_closure A _

theorem sup_mem_closed_subalgebra (A : Subalgebra ℝ C(X, ℝ)) (h : IsClosed (A : Set C(X, ℝ)))
    (f g : A) : (f : C(X, ℝ)) ⊔ (g : C(X, ℝ)) ∈ A := by
  convert sup_mem_subalgebra_closure A f g
  apply SetLike.ext'
  simp

open scoped Topology

-- Here's the fun part of Stone-Weierstrass!
theorem sublattice_closure_eq_top (L : Set C(X, ℝ)) (nA : L.Nonempty)
    (inf_mem : ∀ᵉ (f ∈ L) (g ∈ L), f ⊓ g ∈ L)
    (sup_mem : ∀ᵉ (f ∈ L) (g ∈ L), f ⊔ g ∈ L) (sep : L.SeparatesPointsStrongly) :
    closure L = ⊤ := by
  -- We start by boiling down to a statement about close approximation.
  rw [eq_top_iff]
  rintro f -
  refine
    Filter.Frequently.mem_closure
      ((Filter.HasBasis.frequently_iff Metric.nhds_basis_ball).mpr fun ε pos => ?_)
  simp only [Metric.mem_ball]
  -- It will be helpful to assume `X` is nonempty later,
  -- so we get that out of the way here.
  by_cases nX : Nonempty X
  swap
  · exact ⟨nA.some, (dist_lt_iff pos).mpr fun x => False.elim (nX ⟨x⟩), nA.choose_spec⟩
  /-
    The strategy now is to pick a family of continuous functions `g x y` in `A`
    with the property that `g x y x = f x` and `g x y y = f y`
    (this is immediate from `h : SeparatesPointsStrongly`)
    then use continuity to see that `g x y` is close to `f` near both `x` and `y`,
    and finally using compactness to produce the desired function `h`
    as a maximum over finitely many `x` of a minimum over finitely many `y` of the `g x y`.
    -/
  dsimp only [Set.SeparatesPointsStrongly] at sep
  choose g hg w₁ w₂ using sep f
  -- For each `x y`, we define `U x y` to be `{z | f z - ε < g x y z}`,
  -- and observe this is a neighbourhood of `y`.
  let U : X → X → Set X := fun x y => {z | f z - ε < g x y z}
  have U_nhds_y : ∀ x y, U x y ∈ 𝓝 y := by
    intro x y
    refine IsOpen.mem_nhds ?_ ?_
    · apply isOpen_lt <;> fun_prop
    · rw [Set.mem_setOf_eq, w₂]
      exact sub_lt_self _ pos
  -- Fixing `x` for a moment, we have a family of functions `fun y ↦ g x y`
  -- which on different patches (the `U x y`) are greater than `f z - ε`.
  -- Taking the supremum of these functions
  -- indexed by a finite collection of patches which cover `X`
  -- will give us an element of `A` that is globally greater than `f z - ε`
  -- and still equal to `f x` at `x`.
  -- Since `X` is compact, for every `x` there is some finset `ys t`
  -- so the union of the `U x y` for `y ∈ ys x` still covers everything.
  let ys : X → Finset X := fun x => (CompactSpace.elim_nhds_subcover (U x) (U_nhds_y x)).choose
  let ys_w : ∀ x, ⋃ y ∈ ys x, U x y = ⊤ := fun x =>
    (CompactSpace.elim_nhds_subcover (U x) (U_nhds_y x)).choose_spec
  have ys_nonempty : ∀ x, (ys x).Nonempty := fun x =>
    Set.nonempty_of_union_eq_top_of_nonempty _ _ nX (ys_w x)
  -- Thus for each `x` we have the desired `h x : A` so `f z - ε < h x z` everywhere
  -- and `h x x = f x`.
  let h : X → L := fun x =>
    ⟨(ys x).sup' (ys_nonempty x) fun y => (g x y : C(X, ℝ)),
      Finset.sup'_mem _ sup_mem _ _ _ fun y _ => hg x y⟩
  have lt_h : ∀ x z, f z - ε < (h x : X → ℝ) z := by
    intro x z
    obtain ⟨y, ym, zm⟩ := Set.exists_set_mem_of_union_eq_top _ _ (ys_w x) z
    dsimp [h]
    simp only [coe_sup', Finset.sup'_apply, Finset.lt_sup'_iff]
    exact ⟨y, ym, zm⟩
  have h_eq : ∀ x, (h x : X → ℝ) x = f x := by intro x; simp [h, w₁]
  -- For each `x`, we define `W x` to be `{z | h x z < f z + ε}`,
  let W : X → Set X := fun x => {z | (h x : X → ℝ) z < f z + ε}
  -- This is still a neighbourhood of `x`.
  have W_nhds : ∀ x, W x ∈ 𝓝 x := by
    intro x
    refine IsOpen.mem_nhds ?_ ?_
    · apply isOpen_lt <;> fun_prop
    · dsimp only [W, Set.mem_setOf_eq]
      rw [h_eq]
      exact lt_add_of_pos_right _ pos
  -- Since `X` is compact, there is some finset `ys t`
  -- so the union of the `W x` for `x ∈ xs` still covers everything.
  let xs : Finset X := (CompactSpace.elim_nhds_subcover W W_nhds).choose
  let xs_w : ⋃ x ∈ xs, W x = ⊤ := (CompactSpace.elim_nhds_subcover W W_nhds).choose_spec
  have xs_nonempty : xs.Nonempty := Set.nonempty_of_union_eq_top_of_nonempty _ _ nX xs_w
  -- Finally our candidate function is the infimum over `x ∈ xs` of the `h x`.
  -- This function is then globally less than `f z + ε`.
  let k : (L : Type _) :=
    ⟨xs.inf' xs_nonempty fun x => (h x : C(X, ℝ)),
      Finset.inf'_mem _ inf_mem _ _ _ fun x _ => (h x).2⟩
  refine ⟨k.1, ?_, k.2⟩
  -- We just need to verify the bound, which we do pointwise.
  rw [dist_lt_iff pos]
  intro z
  -- We rewrite into this particular form,
  -- so that simp lemmas about inequalities involving `Finset.inf'` can fire.
  rw [show ∀ a b ε : ℝ, dist a b < ε ↔ a < b + ε ∧ b - ε < a by
        intros; simp only [← Metric.mem_ball, Real.ball_eq_Ioo, Set.mem_Ioo, and_comm]]
  fconstructor
  · dsimp
    simp only [k, Finset.inf'_lt_iff, ContinuousMap.inf'_apply]
    exact Set.exists_set_mem_of_union_eq_top _ _ xs_w z
  · dsimp
    simp only [k, Finset.lt_inf'_iff, ContinuousMap.inf'_apply]
    rintro x -
    apply lt_h

/-- The **Stone-Weierstrass Approximation Theorem**,
that a subalgebra `A` of `C(X, ℝ)`, where `X` is a compact topological space,
is dense if it separates points.
-/
theorem subalgebra_topologicalClosure_eq_top_of_separatesPoints (A : Subalgebra ℝ C(X, ℝ))
    (w : A.SeparatesPoints) : A.topologicalClosure = ⊤ := by
  -- The closure of `A` is closed under taking `sup` and `inf`,
  -- and separates points strongly (since `A` does),
  -- so we can apply `sublattice_closure_eq_top`.
  apply SetLike.ext'
  let L := A.topologicalClosure
  have n : Set.Nonempty (L : Set C(X, ℝ)) := ⟨(1 : C(X, ℝ)), A.le_topologicalClosure A.one_mem⟩
  convert
    sublattice_closure_eq_top (L : Set C(X, ℝ)) n
      (fun f fm g gm => inf_mem_closed_subalgebra L A.isClosed_topologicalClosure ⟨f, fm⟩ ⟨g, gm⟩)
      (fun f fm g gm => sup_mem_closed_subalgebra L A.isClosed_topologicalClosure ⟨f, fm⟩ ⟨g, gm⟩)
      (Subalgebra.SeparatesPoints.strongly
        (Subalgebra.separatesPoints_monotone A.le_topologicalClosure w))
  simp [L]

/-- An alternative statement of the Stone-Weierstrass theorem.

If `A` is a subalgebra of `C(X, ℝ)` which separates points (and `X` is compact),
every real-valued continuous function on `X` is a uniform limit of elements of `A`.
-/
theorem continuousMap_mem_subalgebra_closure_of_separatesPoints (A : Subalgebra ℝ C(X, ℝ))
    (w : A.SeparatesPoints) (f : C(X, ℝ)) : f ∈ A.topologicalClosure := by
  rw [subalgebra_topologicalClosure_eq_top_of_separatesPoints A w]
  simp

/-- An alternative statement of the Stone-Weierstrass theorem,
for those who like their epsilons.

If `A` is a subalgebra of `C(X, ℝ)` which separates points (and `X` is compact),
every real-valued continuous function on `X` is within any `ε > 0` of some element of `A`.
-/
theorem exists_mem_subalgebra_near_continuousMap_of_separatesPoints (A : Subalgebra ℝ C(X, ℝ))
    (w : A.SeparatesPoints) (f : C(X, ℝ)) (ε : ℝ) (pos : 0 < ε) :
    ∃ g : A, ‖(g : C(X, ℝ)) - f‖ < ε := by
  have w :=
    mem_closure_iff_frequently.mp (continuousMap_mem_subalgebra_closure_of_separatesPoints A w f)
  rw [Metric.nhds_basis_ball.frequently_iff] at w
  obtain ⟨g, H, m⟩ := w ε pos
  rw [Metric.mem_ball, dist_eq_norm] at H
  exact ⟨⟨g, m⟩, H⟩

/-- An alternative statement of the Stone-Weierstrass theorem,
for those who like their epsilons and don't like bundled continuous functions.

If `A` is a subalgebra of `C(X, ℝ)` which separates points (and `X` is compact),
every real-valued continuous function on `X` is within any `ε > 0` of some element of `A`.
-/
theorem exists_mem_subalgebra_near_continuous_of_separatesPoints (A : Subalgebra ℝ C(X, ℝ))
    (w : A.SeparatesPoints) (f : X → ℝ) (c : Continuous f) (ε : ℝ) (pos : 0 < ε) :
    ∃ g : A, ∀ x, ‖(g : X → ℝ) x - f x‖ < ε := by
  obtain ⟨g, b⟩ := exists_mem_subalgebra_near_continuousMap_of_separatesPoints A w ⟨f, c⟩ ε pos
  use g
  rwa [norm_lt_iff _ pos] at b

/-- A variant of the Stone-Weierstrass theorem where `X` need not be compact:
If `A` is a subalgebra of `C(X, ℝ)` which separates points, then, for any compact set `K ⊆ X`,
every real-valued continuous function on `X` is within any `ε > 0` of some element of `A` on `K`. -/
theorem exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
    {X : Type*} [TopologicalSpace X] {A : Subalgebra ℝ C(X, ℝ)} (hA : A.SeparatesPoints)
    (f : C(X, ℝ)) {K : Set X} (hK : IsCompact K) {ε : ℝ} (pos : 0 < ε) :
    ∃ g ∈ A, ∀ x ∈ K, ‖(g : X → ℝ) x - f x‖ < ε := by
  let restrict_on_K : C(X, ℝ) →⋆ₐ[ℝ] C(K, ℝ) :=
    ContinuousMap.compStarAlgHom' ℝ ℝ ⟨(Subtype.val), continuous_subtype_val⟩
  --consider the subalgebra AK of functions with domain K
  let AK : Subalgebra ℝ C(K, ℝ) := Subalgebra.map (restrict_on_K) A
  have hsep : AK.SeparatesPoints := by
    intro x y hxy
    obtain ⟨_, ⟨g, hg1, hg2⟩, hg_sep⟩ := hA (Subtype.coe_ne_coe.mpr hxy)
    simp only [Set.mem_image, SetLike.mem_coe, exists_exists_and_eq_and]
    use restrict_on_K g
    refine ⟨Subalgebra.mem_map.mpr ?_,
      by simpa only [compStarAlgHom'_apply, comp_apply, coe_mk, ne_eq, restrict_on_K, hg2]⟩
    use g, hg1
    simp [AlgHom.coe_coe]
  obtain ⟨⟨gK, hgKAK⟩, hgapprox⟩ :=
    @ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints _ _
    (isCompact_iff_compactSpace.mp hK) AK hsep (K.restrict f)
    (ContinuousOn.restrict (Continuous.continuousOn f.continuous)) ε pos
  obtain ⟨g, hgA, hgKAK⟩ := Subalgebra.mem_map.mp hgKAK
  use g, hgA
  intro x hxK
  have eqg : g x = gK ⟨x, hxK⟩ := by
    rw [← hgKAK]; rfl
  rw [eqg]
  exact hgapprox ⟨x, hxK⟩

end ContinuousMap

section RCLike

open RCLike

-- Redefine `X`, since for the next lemma it need not be compact
variable {𝕜 : Type*} {X : Type*} [RCLike 𝕜] [TopologicalSpace X]

open ContinuousMap

/- a post-port refactor eliminated `conjInvariantSubalgebra`, which was only used to
state and prove the Stone-Weierstrass theorem, in favor of using `StarSubalgebra`s,
which didn't exist at the time Stone-Weierstrass was written. -/


/-- If a star subalgebra of `C(X, 𝕜)` separates points, then the real subalgebra
of its purely real-valued elements also separates points. -/
theorem Subalgebra.SeparatesPoints.rclike_to_real {A : StarSubalgebra 𝕜 C(X, 𝕜)}
    (hA : A.SeparatesPoints) :
      ((A.restrictScalars ℝ).comap
        (ofRealAm.compLeftContinuous ℝ continuous_ofReal)).SeparatesPoints := by
  intro x₁ x₂ hx
  -- Let `f` in the subalgebra `A` separate the points `x₁`, `x₂`
  obtain ⟨_, ⟨f, hfA, rfl⟩, hf⟩ := hA hx
  let F : C(X, 𝕜) := f - const _ (f x₂)
  -- Subtract the constant `f x₂` from `f`; this is still an element of the subalgebra
  have hFA : F ∈ A := by
    refine A.sub_mem hfA (@Eq.subst _ (· ∈ A) _ _ ?_ <| A.smul_mem A.one_mem <| f x₂)
    ext1
    simp only [smul_apply, one_apply, smul_eq_mul, mul_one,
      const_apply]
  -- Consider now the function `fun x ↦ |f x - f x₂| ^ 2`
  refine ⟨_, ⟨⟨(‖F ·‖ ^ 2), by fun_prop⟩, ?_, rfl⟩, ?_⟩
  · -- This is also an element of the subalgebra, and takes only real values
    rw [SetLike.mem_coe, Subalgebra.mem_comap]
    convert (A.restrictScalars ℝ).mul_mem hFA (star_mem hFA : star F ∈ A)
    ext1
    simp [← RCLike.mul_conj]
  · -- And it also separates the points `x₁`, `x₂`
    simpa [F] using sub_ne_zero.mpr hf

variable [CompactSpace X]

/-- The Stone-Weierstrass approximation theorem, `RCLike` version, that a star subalgebra `A` of
`C(X, 𝕜)`, where `X` is a compact topological space and `RCLike 𝕜`, is dense if it separates
points. -/
theorem ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (A : StarSubalgebra 𝕜 C(X, 𝕜)) (hA : A.SeparatesPoints) : A.topologicalClosure = ⊤ := by
  rw [StarSubalgebra.eq_top_iff]
  -- Let `I` be the natural inclusion of `C(X, ℝ)` into `C(X, 𝕜)`
  let I : C(X, ℝ) →L[ℝ] C(X, 𝕜) := ofRealCLM.compLeftContinuous ℝ X
  -- The main point of the proof is that its range (i.e., every real-valued function) is contained
  -- in the closure of `A`
  have key : I.range ≤ (A.toSubmodule.restrictScalars ℝ).topologicalClosure := by
    -- Let `A₀` be the subalgebra of `C(X, ℝ)` consisting of `A`'s purely real elements; it is the
    -- preimage of `A` under `I`.  In this argument we only need its submodule structure.
    let A₀ : Submodule ℝ C(X, ℝ) := (A.toSubmodule.restrictScalars ℝ).comap I.toLinearMap
    -- By `Subalgebra.SeparatesPoints.rclike_to_real`, this subalgebra also separates points, so
    -- we may apply the real Stone-Weierstrass result to it.
    have SW : A₀.topologicalClosure = ⊤ :=
      haveI := subalgebra_topologicalClosure_eq_top_of_separatesPoints _ hA.rclike_to_real
      congr_arg Subalgebra.toSubmodule this
    rw [← Submodule.map_top, ← SW]
    -- So it suffices to prove that the image under `I` of the closure of `A₀` is contained in the
    -- closure of `A`, which follows by abstract nonsense
    have h₁ := A₀.topologicalClosure_map I
    have h₂ := (A.toSubmodule.restrictScalars ℝ).map_comap_le I.toLinearMap
    exact h₁.trans (Submodule.topologicalClosure_mono h₂)
  -- In particular, for a function `f` in `C(X, 𝕜)`, the real and imaginary parts of `f` are in the
  -- closure of `A`
  intro f
  let f_re : C(X, ℝ) := (⟨RCLike.re, RCLike.reCLM.continuous⟩ : C(𝕜, ℝ)).comp f
  let f_im : C(X, ℝ) := (⟨RCLike.im, RCLike.imCLM.continuous⟩ : C(𝕜, ℝ)).comp f
  have h_f_re : I f_re ∈ A.topologicalClosure := key ⟨f_re, rfl⟩
  have h_f_im : I f_im ∈ A.topologicalClosure := key ⟨f_im, rfl⟩
  -- So `f_re + I • f_im` is in the closure of `A`
  have := A.topologicalClosure.add_mem h_f_re (A.topologicalClosure.smul_mem h_f_im RCLike.I)
  rw [StarSubalgebra.mem_toSubalgebra] at this
  convert this
  -- And this, of course, is just `f`
  ext
  apply Eq.symm
  simp [I, f_re, f_im, mul_comm RCLike.I _]

end RCLike

section PolynomialFunctions

open StarSubalgebra Polynomial
open scoped Polynomial

/-- Polynomial functions in are dense in `C(s, ℝ)` when `s` is compact.

See `polynomialFunctions_closure_eq_top` for the special case `s = Set.Icc a b` which does not use
the full Stone-Weierstrass theorem. Of course, that version could be used to prove this one as
well. -/
theorem polynomialFunctions.topologicalClosure (s : Set ℝ)
    [CompactSpace s] : (polynomialFunctions s).topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (polynomialFunctions_separatesPoints s)

/-- The star subalgebra generated by polynomials functions is dense in `C(s, 𝕜)` when `s` is
compact and `𝕜` is either `ℝ` or `ℂ`. -/
theorem polynomialFunctions.starClosure_topologicalClosure {𝕜 : Type*} [RCLike 𝕜] (s : Set 𝕜)
    [CompactSpace s] : (polynomialFunctions s).starClosure.topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (Subalgebra.separatesPoints_monotone le_sup_left (polynomialFunctions_separatesPoints s))

open StarAlgebra in
lemma ContinuousMap.elemental_id_eq_top {𝕜 : Type*} [RCLike 𝕜] (s : Set 𝕜) [CompactSpace s] :
    elemental 𝕜 (ContinuousMap.restrict s (.id 𝕜)) = ⊤ := by
  rw [StarAlgebra.elemental, ← polynomialFunctions.starClosure_topologicalClosure,
    polynomialFunctions.starClosure_eq_adjoin_X]
  congr
  exact Polynomial.toContinuousMap_X_eq_id.symm

/-- An induction principle for `C(s, 𝕜)`. -/
@[elab_as_elim]
theorem ContinuousMap.induction_on {𝕜 : Type*} [RCLike 𝕜] {s : Set 𝕜}
    {p : C(s, 𝕜) → Prop} (const : ∀ r, p (.const s r)) (id : p (.restrict s <| .id 𝕜))
    (star_id : p (star (.restrict s <| .id 𝕜)))
    (add : ∀ f g, p f → p g → p (f + g)) (mul : ∀ f g, p f → p g → p (f * g))
    (closure : (∀ f ∈ (polynomialFunctions s).starClosure, p f) → ∀ f, p f) (f : C(s, 𝕜)) :
    p f := by
  refine closure (fun f hf => ?_) f
  rw [polynomialFunctions.starClosure_eq_adjoin_X] at hf
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    push _ ∈ _ at hf
    rw [star_eq_iff_star_eq, eq_comm (b := f)] at hf
    obtain (rfl | rfl) := hf
    all_goals simpa only [toContinuousMapOnAlgHom_apply, toContinuousMapOn_X_eq_restrict_id]
  | algebraMap r => exact const r
  | add _ _ _ _ hf hg => exact add _ _ hf hg
  | mul _ _ _ _ hf hg => exact mul _ _ hf hg

open Topology in
@[elab_as_elim]
theorem ContinuousMap.induction_on_of_compact {𝕜 : Type*} [RCLike 𝕜] {s : Set 𝕜} [CompactSpace s]
    {p : C(s, 𝕜) → Prop} (const : ∀ r, p (.const s r)) (id : p (.restrict s <| .id 𝕜))
    (star_id : p (star (.restrict s <| .id 𝕜)))
    (add : ∀ f g, p f → p g → p (f + g)) (mul : ∀ f g, p f → p g → p (f * g))
    (frequently : ∀ f, (∃ᶠ g in 𝓝 f, p g) → p f) (f : C(s, 𝕜)) :
    p f := by
  refine f.induction_on const id star_id add mul fun h f ↦ frequently f ?_
  have := polynomialFunctions.starClosure_topologicalClosure s ▸ mem_top (x := f)
  rw [← SetLike.mem_coe, topologicalClosure_coe, mem_closure_iff_frequently] at this
  exact this.mp <| .of_forall h

/-- Continuous algebra homomorphisms from `C(s, ℝ)` into an `ℝ`-algebra `A` which agree
at `X : 𝕜[X]` (interpreted as a continuous map) are, in fact, equal. -/
@[ext (iff := false)]
theorem ContinuousMap.algHom_ext_map_X {A : Type*} [Semiring A]
    [Algebra ℝ A] [TopologicalSpace A] [T2Space A] {s : Set ℝ} [CompactSpace s]
    {φ ψ : C(s, ℝ) →ₐ[ℝ] A} (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ (toContinuousMapOnAlgHom s X) = ψ (toContinuousMapOnAlgHom s X)) : φ = ψ := by
  suffices (⊤ : Subalgebra ℝ C(s, ℝ)) ≤ AlgHom.equalizer φ ψ from
    AlgHom.ext fun x => this (by trivial)
  rw [← polynomialFunctions.topologicalClosure s]
  exact Subalgebra.topologicalClosure_minimal
    (polynomialFunctions.le_equalizer s φ ψ h) (isClosed_eq hφ hψ)

/-- Continuous star algebra homomorphisms from `C(s, 𝕜)` into a star `𝕜`-algebra `A` which agree
at `X : 𝕜[X]` (interpreted as a continuous map) are, in fact, equal. -/
@[ext (iff := false)]
theorem ContinuousMap.starAlgHom_ext_map_X {𝕜 A : Type*} [RCLike 𝕜] [Ring A] [StarRing A]
    [Algebra 𝕜 A] [TopologicalSpace A] [T2Space A] {s : Set 𝕜} [CompactSpace s]
    {φ ψ : C(s, 𝕜) →⋆ₐ[𝕜] A} (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ (toContinuousMapOnAlgHom s X) = ψ (toContinuousMapOnAlgHom s X)) : φ = ψ := by
  suffices (⊤ : StarSubalgebra 𝕜 C(s, 𝕜)) ≤ StarAlgHom.equalizer φ ψ from
    StarAlgHom.ext fun x => this mem_top
  rw [← polynomialFunctions.starClosure_topologicalClosure s]
  exact StarSubalgebra.topologicalClosure_minimal
    (polynomialFunctions.starClosure_le_equalizer s φ ψ h) (isClosed_eq hφ hψ)

end PolynomialFunctions

/-! ### Continuous maps sending zero to zero -/

section ContinuousMapZero

variable {𝕜 : Type*} [RCLike 𝕜]
open NonUnitalStarAlgebra Submodule

namespace ContinuousMap

lemma adjoin_id_eq_span_one_union (s : Set 𝕜) :
    ((StarAlgebra.adjoin 𝕜 {(restrict s (.id 𝕜) : C(s, 𝕜))}) : Set C(s, 𝕜)) =
      span 𝕜 ({(1 : C(s, 𝕜))} ∪ (adjoin 𝕜 {(restrict s (.id 𝕜) : C(s, 𝕜))})) := by
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe, ← StarAlgebra.adjoin_nonUnitalStarSubalgebra,
    ← StarSubalgebra.mem_toSubalgebra, ← Subalgebra.mem_toSubmodule,
    StarAlgebra.adjoin_nonUnitalStarSubalgebra_eq_span, span_union, span_eq_toSubmodule]

open Pointwise in
lemma adjoin_id_eq_span_one_add (s : Set 𝕜) :
    ((StarAlgebra.adjoin 𝕜 {(restrict s (.id 𝕜) : C(s, 𝕜))}) : Set C(s, 𝕜)) =
      (span 𝕜 {(1 : C(s, 𝕜))} : Set C(s, 𝕜)) + (adjoin 𝕜 {(restrict s (.id 𝕜) : C(s, 𝕜))}) := by
  ext x
  rw [SetLike.mem_coe, ← StarAlgebra.adjoin_nonUnitalStarSubalgebra,
    ← StarSubalgebra.mem_toSubalgebra, ← Subalgebra.mem_toSubmodule,
    StarAlgebra.adjoin_nonUnitalStarSubalgebra_eq_span, mem_sup]
  simp [Set.mem_add]

lemma nonUnitalStarAlgebraAdjoin_id_subset_ker_evalStarAlgHom {s : Set 𝕜} (h0 : 0 ∈ s) :
    (adjoin 𝕜 {restrict s (.id 𝕜)} : Set C(s, 𝕜)) ⊆
      RingHom.ker (evalStarAlgHom 𝕜 𝕜 (⟨0, h0⟩ : s)) := by
  intro f hf
  induction hf using adjoin_induction with
  | mem f hf =>
    obtain rfl := Set.mem_singleton_iff.mp hf
    rfl
  | add f g _ _ hf hg => exact add_mem hf hg
  | zero => exact zero_mem _
  | mul f g _ _ _ hg => exact Ideal.mul_mem_left _ f hg
  | smul r f _ hf =>
    rw [SetLike.mem_coe, RingHom.mem_ker] at hf ⊢
    rw [map_smul, hf, smul_zero]
  | star f _ hf =>
    rw [SetLike.mem_coe, RingHom.mem_ker] at hf ⊢
    rw [map_star, hf, star_zero]

lemma ker_evalStarAlgHom_inter_adjoin_id (s : Set 𝕜) (h0 : 0 ∈ s) :
    (StarAlgebra.adjoin 𝕜 {restrict s (.id 𝕜)} : Set C(s, 𝕜)) ∩
      RingHom.ker (evalStarAlgHom 𝕜 𝕜 (⟨0, h0⟩ : s)) = adjoin 𝕜 {restrict s (.id 𝕜)} := by
  ext f
  constructor
  · rintro ⟨hf₁, hf₂⟩
    rw [SetLike.mem_coe] at hf₂ ⊢
    simp_rw [adjoin_id_eq_span_one_add, Set.mem_add, SetLike.mem_coe, mem_span_singleton] at hf₁
    obtain ⟨-, ⟨r, rfl⟩, f, hf, rfl⟩ := hf₁
    have := nonUnitalStarAlgebraAdjoin_id_subset_ker_evalStarAlgHom h0 hf
    simp only [SetLike.mem_coe, RingHom.mem_ker, evalStarAlgHom_apply] at hf₂ this
    rw [add_apply, this, add_zero, smul_apply, one_apply, smul_eq_mul, mul_one] at hf₂
    rwa [hf₂, zero_smul, zero_add]
  · simp only [Set.mem_inter_iff, SetLike.mem_coe]
    refine fun hf ↦ ⟨?_, nonUnitalStarAlgebraAdjoin_id_subset_ker_evalStarAlgHom h0 hf⟩
    exact adjoin_le_starAlgebra_adjoin _ _ hf

-- the statement should be in terms of nonunital subalgebras, but we lack API
open RingHom Filter Topology in
theorem AlgHom.closure_ker_inter {F S K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    [TopologicalSpace K] [T1Space K] [TopologicalSpace A] [ContinuousSub A] [ContinuousSMul K A]
    [FunLike F A K] [AlgHomClass F K A K] [SetLike S A] [OneMemClass S A] [AddSubgroupClass S A]
    [SMulMemClass S K A] (φ : F) (hφ : Continuous φ) (s : S) :
    closure (s ∩ RingHom.ker φ) = closure s ∩ (ker φ : Set A) := by
  refine subset_antisymm ?_ ?_
  · simpa only [ker_eq, (isClosed_singleton.preimage hφ).closure_eq]
      using closure_inter_subset_inter_closure s (ker φ : Set A)
  · intro x ⟨hxs, (hxφ : φ x = 0)⟩
    rw [mem_closure_iff_clusterPt, ClusterPt] at hxs
    have : Tendsto (fun y ↦ y - φ y • 1) (𝓝 x ⊓ 𝓟 s) (𝓝 x) := by
      conv => congr; rfl; rfl; rw [← sub_zero x, ← zero_smul K 1, ← hxφ]
      exact Filter.tendsto_inf_left (Continuous.tendsto (by fun_prop) x)
    refine mem_closure_of_tendsto this <| eventually_inf_principal.mpr ?_
    filter_upwards [] with g hg using
      ⟨sub_mem hg (SMulMemClass.smul_mem _ <| one_mem _), by simp [RingHom.mem_ker]⟩

lemma ker_evalStarAlgHom_eq_closure_adjoin_id (s : Set 𝕜) (h0 : 0 ∈ s) [CompactSpace s] :
    (RingHom.ker (evalStarAlgHom 𝕜 𝕜 (⟨0, h0⟩ : s)) : Set C(s, 𝕜)) =
      closure (adjoin 𝕜 {(restrict s (.id 𝕜))}) := by
  rw [← ker_evalStarAlgHom_inter_adjoin_id s h0,
    AlgHom.closure_ker_inter (φ := evalStarAlgHom 𝕜 𝕜 (X := s) ⟨0, h0⟩) (continuous_eval_const _) _]
  convert (Set.univ_inter _).symm
  rw [← Polynomial.toContinuousMapOn_X_eq_restrict_id, ← Polynomial.toContinuousMapOnAlgHom_apply,
    ← polynomialFunctions.starClosure_eq_adjoin_X s]
  congrm (($(polynomialFunctions.starClosure_topologicalClosure s) : Set C(s, 𝕜)))

end ContinuousMap

open scoped ContinuousMapZero

/-- If `s : Set 𝕜` with `RCLike 𝕜` is compact and contains `0`, then the non-unital star subalgebra
generated by the identity function in `C(s, 𝕜)₀` is dense. This can be seen as a version of the
Weierstrass approximation theorem. -/
lemma ContinuousMapZero.adjoin_id_dense (s : Set 𝕜) [Fact (0 ∈ s)]
    [CompactSpace s] : Dense (adjoin 𝕜 {(.id s : C(s, 𝕜)₀)} : Set C(s, 𝕜)₀) := by
  have h0' : 0 ∈ s := Fact.out
  rw [dense_iff_closure_eq,
    ← isClosedEmbedding_toContinuousMap.injective.preimage_image (closure _),
    ← isClosedEmbedding_toContinuousMap.closure_image_eq, ← coe_toContinuousMapHom,
    ← NonUnitalStarSubalgebra.coe_map, NonUnitalStarAlgHom.map_adjoin_singleton,
    toContinuousMapHom_apply, toContinuousMap_id,
    ← ContinuousMap.ker_evalStarAlgHom_eq_closure_adjoin_id s h0']
  apply Set.eq_univ_of_forall fun f ↦ ?_
  simp only [Set.mem_preimage, toContinuousMapHom_apply, SetLike.mem_coe, RingHom.mem_ker,
    ContinuousMap.evalStarAlgHom_apply, ContinuousMap.coe_coe]
  exact map_zero f

set_option backward.isDefEq.respectTransparency false in
open NonUnitalStarAlgebra in
lemma ContinuousMapZero.elemental_eq_top {𝕜 : Type*} [RCLike 𝕜] (s : Set 𝕜) [Fact (0 ∈ s)]
    [CompactSpace s] : elemental 𝕜 (ContinuousMapZero.id s) = ⊤ :=
  SetLike.ext'_iff.mpr (adjoin_id_dense s).closure_eq

/-- An induction principle for `C(s, 𝕜)₀`. -/
@[elab_as_elim]
lemma ContinuousMapZero.induction_on {s : Set 𝕜} [Fact (0 ∈ s)]
    {p : C(s, 𝕜)₀ → Prop} (zero : p 0) (id : p (.id s)) (star_id : p (star (.id s)))
    (add : ∀ f g, p f → p g → p (f + g)) (mul : ∀ f g, p f → p g → p (f * g))
    (smul : ∀ (r : 𝕜) f, p f → p (r • f))
    (closure : (∀ f ∈ adjoin 𝕜 {(.id s : C(s, 𝕜)₀)}, p f) → ∀ f, p f) (f : C(s, 𝕜)₀) :
    p f := by
  refine closure (fun f hf => ?_) f
  induction hf using NonUnitalAlgebra.adjoin_induction with
  | mem f hf =>
    push _ ∈ _ at hf
    rw [star_eq_iff_star_eq] at hf
    obtain (rfl | rfl) := hf
    all_goals assumption
  | zero => exact zero
  | add _ _ _ _ hf hg => exact add _ _ hf hg
  | mul _ _ _ _ hf hg => exact mul _ _ hf hg
  | smul _ _ _ hf => exact smul _ _ hf

open Topology in
@[elab_as_elim]
theorem ContinuousMapZero.induction_on_of_compact {s : Set 𝕜} [Fact (0 ∈ s)]
    [CompactSpace s] {p : C(s, 𝕜)₀ → Prop} (zero : p 0) (id : p (.id s))
    (star_id : p (star (.id s))) (add : ∀ f g, p f → p g → p (f + g))
    (mul : ∀ f g, p f → p g → p (f * g)) (smul : ∀ (r : 𝕜) f, p f → p (r • f))
    (frequently : ∀ f, (∃ᶠ g in 𝓝 f, p g) → p f) (f : C(s, 𝕜)₀) :
    p f := by
  refine f.induction_on zero id star_id add mul smul fun h f ↦ frequently f ?_
  have := (ContinuousMapZero.adjoin_id_dense s).closure_eq ▸ Set.mem_univ (x := f)
  exact mem_closure_iff_frequently.mp this |>.mp <| .of_forall h

lemma ContinuousMapZero.nonUnitalStarAlgHom_apply_mul_eq_zero {𝕜 A : Type*}
    [RCLike 𝕜] [NonUnitalSemiring A] [Star A] [TopologicalSpace A] [SeparatelyContinuousMul A]
    [T2Space A] [DistribMulAction 𝕜 A] [IsScalarTower 𝕜 A A] {s : Set 𝕜} [Fact (0 ∈ s)]
    [CompactSpace s] (φ : C(s, 𝕜)₀ →⋆ₙₐ[𝕜] A) (a : A) (hmul_id : φ (.id s) * a = 0)
    (hmul_star_id : φ (star (.id s)) * a = 0) (hφ : Continuous φ) (f : C(s, 𝕜)₀) :
    φ f * a = 0 := by
  induction f using ContinuousMapZero.induction_on_of_compact with
  | zero => simp [map_zero]
  | id => exact hmul_id
  | star_id => exact hmul_star_id
  | add _ _ h₁ h₂ => simp only [map_add, add_mul, h₁, h₂, zero_add]
  | mul _ _ _ h => simp only [map_mul, mul_assoc, h, mul_zero]
  | smul _ _ h => rw [map_smul, smul_mul_assoc, h, smul_zero]
  | frequently f h => exact h.mem_of_closed <| isClosed_eq (by fun_prop) continuous_zero

lemma ContinuousMapZero.mul_nonUnitalStarAlgHom_apply_eq_zero {𝕜 A : Type*}
    [RCLike 𝕜] [NonUnitalSemiring A] [Star A] [TopologicalSpace A] [SeparatelyContinuousMul A]
    [T2Space A] [DistribMulAction 𝕜 A] [SMulCommClass 𝕜 A A] {s : Set 𝕜} [Fact (0 ∈ s)]
    [CompactSpace s] (φ : C(s, 𝕜)₀ →⋆ₙₐ[𝕜] A) (a : A) (hmul_id : a * φ (.id s) = 0)
    (hmul_star_id : a * φ (star (.id s)) = 0) (hφ : Continuous φ) (f : C(s, 𝕜)₀) :
    a * φ f = 0 := by
  induction f using ContinuousMapZero.induction_on_of_compact with
  | zero => simp [map_zero]
  | id => exact hmul_id
  | star_id => exact hmul_star_id
  | add _ _ h₁ h₂ => simp only [map_add, mul_add, h₁, h₂, zero_add]
  | mul _ _ h _ => simp only [map_mul, ← mul_assoc, h, zero_mul]
  | smul _ _ h => rw [map_smul, mul_smul_comm, h, smul_zero]
  | frequently f h => exact h.mem_of_closed <| isClosed_eq (by fun_prop) continuous_zero

end ContinuousMapZero
