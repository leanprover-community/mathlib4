/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.NormedSpace.Multilinear.Basic

#align_import analysis.normed_space.multilinear from "leanprover-community/mathlib"@"f40476639bac089693a489c9e354ebd75dc0f886"

/-!
# Currying and uncurrying continuous multilinear maps

We associate to a continuous multilinear map in `n+1` variables (i.e., based on `Fin n.succ`) two
curried functions, named `f.curryLeft` (which is a continuous linear map on `E 0` taking values
in continuous multilinear maps in `n` variables) and `f.curryRight` (which is a continuous
multilinear map in `n` variables taking values in continuous linear maps on `E (last n)`).
The inverse operations are called `uncurryLeft` and `uncurryRight`.

We also register continuous linear equiv versions of these correspondences, in
`continuousMultilinearCurryLeftEquiv` and `continuousMultilinearCurryRightEquiv`.

## Main results

* `ContinuousMultilinearMap.curryLeft`, `ContinuousLinearMap.uncurryLeft` and
  `continuousMultilinearCurryLeftEquiv`
* `ContinuousMultilinearMap.curryRight`, `ContinuousMultilinearMap.uncurryRight` and
  `continuousMultilinearCurryRightEquiv`.
-/

suppress_compilation

-- make instances connecting normed things and algebra have higher priority
open scoped AlgebraNormedInstances

noncomputable section

open BigOperators NNReal Finset Metric ContinuousMultilinearMap Fin Function

/-!
### Type variables

We use the following type variables in this file:

* `𝕜` : a `NontriviallyNormedField`;
* `ι`, `ι'` : finite index types with decidable equality;
* `E`, `E₁` : families of normed vector spaces over `𝕜` indexed by `i : ι`;
* `E'` : a family of normed vector spaces over `𝕜` indexed by `i' : ι'`;
* `Ei` : a family of normed vector spaces over `𝕜` indexed by `i : Fin (Nat.succ n)`;
* `G`, `G'` : normed vector spaces over `𝕜`.
-/


universe u v v' wE wE₁ wE' wEi wG wG'

variable {𝕜 : Type u} {ι : Type v} {ι' : Type v'} {n : ℕ} {E : ι → Type wE} {E₁ : ι → Type wE₁}
  {E' : ι' → Type wE'} {Ei : Fin n.succ → Type wEi} {G : Type wG} {G' : Type wG'} [Fintype ι]
  [Fintype ι'] [NontriviallyNormedField 𝕜] [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace 𝕜 (E i)] [∀ i, NormedAddCommGroup (E₁ i)] [∀ i, NormedSpace 𝕜 (E₁ i)]
  [∀ i, NormedAddCommGroup (E' i)] [∀ i, NormedSpace 𝕜 (E' i)] [∀ i, NormedAddCommGroup (Ei i)]
  [∀ i, NormedSpace 𝕜 (Ei i)] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup G']
  [NormedSpace 𝕜 G']


theorem ContinuousLinearMap.norm_map_tail_le
    (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) (m : ∀ i, Ei i) :
    ‖f (m 0) (tail m)‖ ≤ ‖f‖ * ∏ i, ‖m i‖ :=
  calc
    ‖f (m 0) (tail m)‖ ≤ ‖f (m 0)‖ * ∏ i, ‖(tail m) i‖ := (f (m 0)).le_opNorm _
    _ ≤ ‖f‖ * ‖m 0‖ * ∏ i, ‖tail m i‖ := mul_le_mul_of_nonneg_right (f.le_opNorm _) <| by positivity
    _ = ‖f‖ * (‖m 0‖ * ∏ i, ‖(tail m) i‖) := by ring
    _ = ‖f‖ * ∏ i, ‖m i‖ := by
      rw [prod_univ_succ]
      rfl
#align continuous_linear_map.norm_map_tail_le ContinuousLinearMap.norm_map_tail_le

theorem ContinuousMultilinearMap.norm_map_init_le
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G))
    (m : ∀ i, Ei i) : ‖f (init m) (m (last n))‖ ≤ ‖f‖ * ∏ i, ‖m i‖ :=
  calc
    ‖f (init m) (m (last n))‖ ≤ ‖f (init m)‖ * ‖m (last n)‖ := (f (init m)).le_opNorm _
    _ ≤ (‖f‖ * ∏ i, ‖(init m) i‖) * ‖m (last n)‖ :=
      (mul_le_mul_of_nonneg_right (f.le_opNorm _) (norm_nonneg _))
    _ = ‖f‖ * ((∏ i, ‖(init m) i‖) * ‖m (last n)‖) := mul_assoc _ _ _
    _ = ‖f‖ * ∏ i, ‖m i‖ := by
      rw [prod_univ_castSucc]
      rfl
#align continuous_multilinear_map.norm_map_init_le ContinuousMultilinearMap.norm_map_init_le

theorem ContinuousMultilinearMap.norm_map_cons_le (f : ContinuousMultilinearMap 𝕜 Ei G) (x : Ei 0)
    (m : ∀ i : Fin n, Ei i.succ) : ‖f (cons x m)‖ ≤ ‖f‖ * ‖x‖ * ∏ i, ‖m i‖ :=
  calc
    ‖f (cons x m)‖ ≤ ‖f‖ * ∏ i, ‖cons x m i‖ := f.le_opNorm _
    _ = ‖f‖ * ‖x‖ * ∏ i, ‖m i‖ := by
      rw [prod_univ_succ]
      simp [mul_assoc]
#align continuous_multilinear_map.norm_map_cons_le ContinuousMultilinearMap.norm_map_cons_le

theorem ContinuousMultilinearMap.norm_map_snoc_le (f : ContinuousMultilinearMap 𝕜 Ei G)
    (m : ∀ i : Fin n, Ei <| castSucc i) (x : Ei (last n)) :
    ‖f (snoc m x)‖ ≤ (‖f‖ * ∏ i, ‖m i‖) * ‖x‖ :=
  calc
    ‖f (snoc m x)‖ ≤ ‖f‖ * ∏ i, ‖snoc m x i‖ := f.le_opNorm _
    _ = (‖f‖ * ∏ i, ‖m i‖) * ‖x‖ := by
      rw [prod_univ_castSucc]
      simp [mul_assoc]
#align continuous_multilinear_map.norm_map_snoc_le ContinuousMultilinearMap.norm_map_snoc_le

/-! #### Left currying -/


/-- Given a continuous linear map `f` from `E 0` to continuous multilinear maps on `n` variables,
construct the corresponding continuous multilinear map on `n+1` variables obtained by concatenating
the variables, given by `m ↦ f (m 0) (tail m)`-/
def ContinuousLinearMap.uncurryLeft
    (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) :
    ContinuousMultilinearMap 𝕜 Ei G :=
  (@LinearMap.uncurryLeft 𝕜 n Ei G _ _ _ _ _
      (ContinuousMultilinearMap.toMultilinearMapLinear.comp f.toLinearMap)).mkContinuous
    ‖f‖ fun m => by exact ContinuousLinearMap.norm_map_tail_le f m
#align continuous_linear_map.uncurry_left ContinuousLinearMap.uncurryLeft

@[simp]
theorem ContinuousLinearMap.uncurryLeft_apply
    (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) (m : ∀ i, Ei i) :
    f.uncurryLeft m = f (m 0) (tail m) :=
  rfl
#align continuous_linear_map.uncurry_left_apply ContinuousLinearMap.uncurryLeft_apply

/-- Given a continuous multilinear map `f` in `n+1` variables, split the first variable to obtain
a continuous linear map into continuous multilinear maps in `n` variables, given by
`x ↦ (m ↦ f (cons x m))`. -/
def ContinuousMultilinearMap.curryLeft (f : ContinuousMultilinearMap 𝕜 Ei G) :
    Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G :=
  LinearMap.mkContinuous
    { -- define a linear map into `n` continuous multilinear maps
      -- from an `n+1` continuous multilinear map
      toFun := fun x =>
        (f.toMultilinearMap.curryLeft x).mkContinuous (‖f‖ * ‖x‖) (f.norm_map_cons_le x)
      map_add' := fun x y => by
        ext m
        exact f.cons_add m x y
      map_smul' := fun c x => by
        ext m
        exact
          f.cons_smul m c x }-- then register its continuity thanks to its boundedness properties.
    ‖f‖ fun x => by
      rw [LinearMap.coe_mk, AddHom.coe_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _
#align continuous_multilinear_map.curry_left ContinuousMultilinearMap.curryLeft

@[simp]
theorem ContinuousMultilinearMap.curryLeft_apply (f : ContinuousMultilinearMap 𝕜 Ei G) (x : Ei 0)
    (m : ∀ i : Fin n, Ei i.succ) : f.curryLeft x m = f (cons x m) :=
  rfl
#align continuous_multilinear_map.curry_left_apply ContinuousMultilinearMap.curryLeft_apply

@[simp]
theorem ContinuousLinearMap.curry_uncurryLeft
    (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) :
    f.uncurryLeft.curryLeft = f := by
  ext m x
  rw [ContinuousMultilinearMap.curryLeft_apply, ContinuousLinearMap.uncurryLeft_apply, tail_cons,
    cons_zero]
#align continuous_linear_map.curry_uncurry_left ContinuousLinearMap.curry_uncurryLeft

@[simp]
theorem ContinuousMultilinearMap.uncurry_curryLeft (f : ContinuousMultilinearMap 𝕜 Ei G) :
    f.curryLeft.uncurryLeft = f :=
  ContinuousMultilinearMap.toMultilinearMap_injective <| f.toMultilinearMap.uncurry_curryLeft
#align continuous_multilinear_map.uncurry_curry_left ContinuousMultilinearMap.uncurry_curryLeft

variable (𝕜 Ei G)

/-- The space of continuous multilinear maps on `Π(i : Fin (n+1)), E i` is canonically isomorphic to
the space of continuous linear maps from `E 0` to the space of continuous multilinear maps on
`Π(i : Fin n), E i.succ`, by separating the first variable. We register this isomorphism in
`continuousMultilinearCurryLeftEquiv 𝕜 E E₂`. The algebraic version (without topology) is given
in `multilinearCurryLeftEquiv 𝕜 E E₂`.

The direct and inverse maps are given by `f.uncurryLeft` and `f.curryLeft`. Use these
unless you need the full framework of linear isometric equivs. -/
def continuousMultilinearCurryLeftEquiv :
    (Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) ≃ₗᵢ[𝕜]
      ContinuousMultilinearMap 𝕜 Ei G :=
  LinearIsometryEquiv.ofBounds
    { toFun := ContinuousLinearMap.uncurryLeft
      map_add' := fun f₁ f₂ => by
        ext m
        rfl
      map_smul' := fun c f => by
        ext m
        rfl
      invFun := ContinuousMultilinearMap.curryLeft
      left_inv := ContinuousLinearMap.curry_uncurryLeft
      right_inv := ContinuousMultilinearMap.uncurry_curryLeft }
    (fun f => by
      simp only [LinearEquiv.coe_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)
    (fun f => by
      simp only [LinearEquiv.coe_symm_mk]
      exact LinearMap.mkContinuous_norm_le _ (norm_nonneg f) _)
#align continuous_multilinear_curry_left_equiv continuousMultilinearCurryLeftEquiv

variable {𝕜 Ei G}

@[simp]
theorem continuousMultilinearCurryLeftEquiv_apply
    (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) (v : ∀ i, Ei i) :
    continuousMultilinearCurryLeftEquiv 𝕜 Ei G f v = f (v 0) (tail v) :=
  rfl
#align continuous_multilinear_curry_left_equiv_apply continuousMultilinearCurryLeftEquiv_apply

@[simp]
theorem continuousMultilinearCurryLeftEquiv_symm_apply (f : ContinuousMultilinearMap 𝕜 Ei G)
    (x : Ei 0) (v : ∀ i : Fin n, Ei i.succ) :
    (continuousMultilinearCurryLeftEquiv 𝕜 Ei G).symm f x v = f (cons x v) :=
  rfl
#align continuous_multilinear_curry_left_equiv_symm_apply continuousMultilinearCurryLeftEquiv_symm_apply

@[simp]
theorem ContinuousMultilinearMap.curryLeft_norm (f : ContinuousMultilinearMap 𝕜 Ei G) :
    ‖f.curryLeft‖ = ‖f‖ :=
  (continuousMultilinearCurryLeftEquiv 𝕜 Ei G).symm.norm_map f
#align continuous_multilinear_map.curry_left_norm ContinuousMultilinearMap.curryLeft_norm

@[simp]
theorem ContinuousLinearMap.uncurryLeft_norm
    (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei i.succ) G) :
    ‖f.uncurryLeft‖ = ‖f‖ :=
  (continuousMultilinearCurryLeftEquiv 𝕜 Ei G).norm_map f
#align continuous_linear_map.uncurry_left_norm ContinuousLinearMap.uncurryLeft_norm

/-! #### Right currying -/


/-- Given a continuous linear map `f` from continuous multilinear maps on `n` variables to
continuous linear maps on `E 0`, construct the corresponding continuous multilinear map on `n+1`
variables obtained by concatenating the variables, given by `m ↦ f (init m) (m (last n))`. -/
def ContinuousMultilinearMap.uncurryRight
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G)) :
    ContinuousMultilinearMap 𝕜 Ei G :=
  let f' : MultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →ₗ[𝕜] G) :=
    { toFun := fun m => (f m).toLinearMap
      map_add' := fun m i x y => by simp
      map_smul' := fun m i c x => by simp }
  (@MultilinearMap.uncurryRight 𝕜 n Ei G _ _ _ _ _ f').mkContinuous ‖f‖ fun m =>
    f.norm_map_init_le m
#align continuous_multilinear_map.uncurry_right ContinuousMultilinearMap.uncurryRight

@[simp]
theorem ContinuousMultilinearMap.uncurryRight_apply
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G))
    (m : ∀ i, Ei i) : f.uncurryRight m = f (init m) (m (last n)) :=
  rfl
#align continuous_multilinear_map.uncurry_right_apply ContinuousMultilinearMap.uncurryRight_apply

/-- Given a continuous multilinear map `f` in `n+1` variables, split the last variable to obtain
a continuous multilinear map in `n` variables into continuous linear maps, given by
`m ↦ (x ↦ f (snoc m x))`. -/
def ContinuousMultilinearMap.curryRight (f : ContinuousMultilinearMap 𝕜 Ei G) :
    ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G) :=
  let f' : MultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G) :=
    { toFun := fun m =>
        (f.toMultilinearMap.curryRight m).mkContinuous (‖f‖ * ∏ i, ‖m i‖) fun x =>
          f.norm_map_snoc_le m x
      map_add' := fun m i x y => by
        ext
        simp
      map_smul' := fun m i c x => by
        ext
        simp }
  f'.mkContinuous ‖f‖ fun m => by
    simp only [f', MultilinearMap.coe_mk]
    exact LinearMap.mkContinuous_norm_le _ (by positivity) _
#align continuous_multilinear_map.curry_right ContinuousMultilinearMap.curryRight

@[simp]
theorem ContinuousMultilinearMap.curryRight_apply (f : ContinuousMultilinearMap 𝕜 Ei G)
    (m : ∀ i : Fin n, Ei <| castSucc i) (x : Ei (last n)) : f.curryRight m x = f (snoc m x) :=
  rfl
#align continuous_multilinear_map.curry_right_apply ContinuousMultilinearMap.curryRight_apply

@[simp]
theorem ContinuousMultilinearMap.curry_uncurryRight
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G)) :
    f.uncurryRight.curryRight = f := by
  ext m x
  rw [ContinuousMultilinearMap.curryRight_apply, ContinuousMultilinearMap.uncurryRight_apply,
    snoc_last, init_snoc]
#align continuous_multilinear_map.curry_uncurry_right ContinuousMultilinearMap.curry_uncurryRight

@[simp]
theorem ContinuousMultilinearMap.uncurry_curryRight (f : ContinuousMultilinearMap 𝕜 Ei G) :
    f.curryRight.uncurryRight = f := by
  ext m
  rw [uncurryRight_apply, curryRight_apply, snoc_init_self]
#align continuous_multilinear_map.uncurry_curry_right ContinuousMultilinearMap.uncurry_curryRight

variable (𝕜 Ei G)

/--
The space of continuous multilinear maps on `Π(i : Fin (n+1)), Ei i` is canonically isomorphic to
the space of continuous multilinear maps on `Π(i : Fin n), Ei <| castSucc i` with values in the
space of continuous linear maps on `Ei (last n)`, by separating the last variable. We register this
isomorphism as a continuous linear equiv in `continuousMultilinearCurryRightEquiv 𝕜 Ei G`.
The algebraic version (without topology) is given in `multilinearCurryRightEquiv 𝕜 Ei G`.

The direct and inverse maps are given by `f.uncurryRight` and `f.curryRight`. Use these
unless you need the full framework of linear isometric equivs.
-/
def continuousMultilinearCurryRightEquiv :
    ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G) ≃ₗᵢ[𝕜]
      ContinuousMultilinearMap 𝕜 Ei G :=
  LinearIsometryEquiv.ofBounds
    { toFun := ContinuousMultilinearMap.uncurryRight
      map_add' := fun f₁ f₂ => by
        ext m
        rfl
      map_smul' := fun c f => by
        ext m
        rfl
      invFun := ContinuousMultilinearMap.curryRight
      left_inv := ContinuousMultilinearMap.curry_uncurryRight
      right_inv := ContinuousMultilinearMap.uncurry_curryRight } (fun f => by
        simp only [uncurryRight, LinearEquiv.coe_mk]
        exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _) fun f => by
          simp only [curryRight, LinearEquiv.coe_symm_mk]
          exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _
#align continuous_multilinear_curry_right_equiv continuousMultilinearCurryRightEquiv

variable (n G')

/-- The space of continuous multilinear maps on `Π(i : Fin (n+1)), G` is canonically isomorphic to
the space of continuous multilinear maps on `Π(i : Fin n), G` with values in the space
of continuous linear maps on `G`, by separating the last variable. We register this
isomorphism as a continuous linear equiv in `continuousMultilinearCurryRightEquiv' 𝕜 n G G'`.
For a version allowing dependent types, see `continuousMultilinearCurryRightEquiv`. When there
are no dependent types, use the primed version as it helps Lean a lot for unification.

The direct and inverse maps are given by `f.uncurryRight` and `f.curryRight`. Use these
unless you need the full framework of linear isometric equivs. -/
def continuousMultilinearCurryRightEquiv' : (G[×n]→L[𝕜] G →L[𝕜] G') ≃ₗᵢ[𝕜] G[×n.succ]→L[𝕜] G' :=
  continuousMultilinearCurryRightEquiv 𝕜 (fun _ => G) G'
#align continuous_multilinear_curry_right_equiv' continuousMultilinearCurryRightEquiv'

variable {n 𝕜 G Ei G'}

@[simp]
theorem continuousMultilinearCurryRightEquiv_apply
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G))
    (v : ∀ i, Ei i) : (continuousMultilinearCurryRightEquiv 𝕜 Ei G) f v = f (init v) (v (last n)) :=
  rfl
#align continuous_multilinear_curry_right_equiv_apply continuousMultilinearCurryRightEquiv_apply

@[simp]
theorem continuousMultilinearCurryRightEquiv_symm_apply (f : ContinuousMultilinearMap 𝕜 Ei G)
    (v : ∀ i : Fin n, Ei <| castSucc i) (x : Ei (last n)) :
    (continuousMultilinearCurryRightEquiv 𝕜 Ei G).symm f v x = f (snoc v x) :=
  rfl
#align continuous_multilinear_curry_right_equiv_symm_apply continuousMultilinearCurryRightEquiv_symm_apply

@[simp]
theorem continuousMultilinearCurryRightEquiv_apply' (f : G[×n]→L[𝕜] G →L[𝕜] G')
    (v : Fin (n + 1) → G) :
    continuousMultilinearCurryRightEquiv' 𝕜 n G G' f v = f (init v) (v (last n)) :=
  rfl
#align continuous_multilinear_curry_right_equiv_apply' continuousMultilinearCurryRightEquiv_apply'

@[simp]
theorem continuousMultilinearCurryRightEquiv_symm_apply' (f : G[×n.succ]→L[𝕜] G')
    (v : Fin n → G) (x : G) :
    (continuousMultilinearCurryRightEquiv' 𝕜 n G G').symm f v x = f (snoc v x) :=
  rfl
#align continuous_multilinear_curry_right_equiv_symm_apply' continuousMultilinearCurryRightEquiv_symm_apply'

@[simp]
theorem ContinuousMultilinearMap.curryRight_norm (f : ContinuousMultilinearMap 𝕜 Ei G) :
    ‖f.curryRight‖ = ‖f‖ :=
  (continuousMultilinearCurryRightEquiv 𝕜 Ei G).symm.norm_map f
#align continuous_multilinear_map.curry_right_norm ContinuousMultilinearMap.curryRight_norm

@[simp]
theorem ContinuousMultilinearMap.uncurryRight_norm
    (f : ContinuousMultilinearMap 𝕜 (fun i : Fin n => Ei <| castSucc i) (Ei (last n) →L[𝕜] G)) :
    ‖f.uncurryRight‖ = ‖f‖ :=
  (continuousMultilinearCurryRightEquiv 𝕜 Ei G).norm_map f
#align continuous_multilinear_map.uncurry_right_norm ContinuousMultilinearMap.uncurryRight_norm

/-!
#### Currying with `0` variables

The space of multilinear maps with `0` variables is trivial: such a multilinear map is just an
arbitrary constant (note that multilinear maps in `0` variables need not map `0` to `0`!).
Therefore, the space of continuous multilinear maps on `(Fin 0) → G` with values in `E₂` is
isomorphic (and even isometric) to `E₂`. As this is the zeroth step in the construction of iterated
derivatives, we register this isomorphism. -/


section

/-- Associating to a continuous multilinear map in `0` variables the unique value it takes. -/
def ContinuousMultilinearMap.uncurry0 (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => G) G') :
    G' :=
  f 0
#align continuous_multilinear_map.uncurry0 ContinuousMultilinearMap.uncurry0

variable (𝕜 G)

/-- Associating to an element `x` of a vector space `E₂` the continuous multilinear map in `0`
variables taking the (unique) value `x` -/
def ContinuousMultilinearMap.curry0 (x : G') : G[×0]→L[𝕜] G' :=
  ContinuousMultilinearMap.constOfIsEmpty 𝕜 _ x
#align continuous_multilinear_map.curry0 ContinuousMultilinearMap.curry0

variable {G}

@[simp]
theorem ContinuousMultilinearMap.curry0_apply (x : G') (m : Fin 0 → G) :
    ContinuousMultilinearMap.curry0 𝕜 G x m = x :=
  rfl
#align continuous_multilinear_map.curry0_apply ContinuousMultilinearMap.curry0_apply

variable {𝕜}

@[simp]
theorem ContinuousMultilinearMap.uncurry0_apply (f : G[×0]→L[𝕜] G') : f.uncurry0 = f 0 :=
  rfl
#align continuous_multilinear_map.uncurry0_apply ContinuousMultilinearMap.uncurry0_apply

@[simp]
theorem ContinuousMultilinearMap.apply_zero_curry0 (f : G[×0]→L[𝕜] G') {x : Fin 0 → G} :
    ContinuousMultilinearMap.curry0 𝕜 G (f x) = f := by
  ext m
  simp [Subsingleton.elim x m]
#align continuous_multilinear_map.apply_zero_curry0 ContinuousMultilinearMap.apply_zero_curry0

theorem ContinuousMultilinearMap.uncurry0_curry0 (f : G[×0]→L[𝕜] G') :
    ContinuousMultilinearMap.curry0 𝕜 G f.uncurry0 = f := by simp
#align continuous_multilinear_map.uncurry0_curry0 ContinuousMultilinearMap.uncurry0_curry0

variable (𝕜 G)

theorem ContinuousMultilinearMap.curry0_uncurry0 (x : G') :
    (ContinuousMultilinearMap.curry0 𝕜 G x).uncurry0 = x :=
  rfl
#align continuous_multilinear_map.curry0_uncurry0 ContinuousMultilinearMap.curry0_uncurry0

@[simp]
theorem ContinuousMultilinearMap.curry0_norm (x : G') :
    ‖ContinuousMultilinearMap.curry0 𝕜 G x‖ = ‖x‖ :=
  norm_constOfIsEmpty _ _ _
#align continuous_multilinear_map.curry0_norm ContinuousMultilinearMap.curry0_norm

variable {𝕜 G}

@[simp]
theorem ContinuousMultilinearMap.fin0_apply_norm (f : G[×0]→L[𝕜] G') {x : Fin 0 → G} :
    ‖f x‖ = ‖f‖ := by
  obtain rfl : x = 0 := Subsingleton.elim _ _
  refine le_antisymm (by simpa using f.le_opNorm 0) ?_
  have : ‖ContinuousMultilinearMap.curry0 𝕜 G f.uncurry0‖ ≤ ‖f.uncurry0‖ :=
    ContinuousMultilinearMap.opNorm_le_bound _ (norm_nonneg _) fun m => by
      simp [-ContinuousMultilinearMap.apply_zero_curry0]
  simpa [-Matrix.zero_empty] using this
#align continuous_multilinear_map.fin0_apply_norm ContinuousMultilinearMap.fin0_apply_norm

theorem ContinuousMultilinearMap.uncurry0_norm (f : G[×0]→L[𝕜] G') : ‖f.uncurry0‖ = ‖f‖ := by simp
#align continuous_multilinear_map.uncurry0_norm ContinuousMultilinearMap.uncurry0_norm

variable (𝕜 G G')

/-- The continuous linear isomorphism between elements of a normed space, and continuous multilinear
maps in `0` variables with values in this normed space.

The direct and inverse maps are `uncurry0` and `curry0`. Use these unless you need the full
framework of linear isometric equivs. -/
def continuousMultilinearCurryFin0 : (G[×0]→L[𝕜] G') ≃ₗᵢ[𝕜] G' where
  toFun f := ContinuousMultilinearMap.uncurry0 f
  invFun f := ContinuousMultilinearMap.curry0 𝕜 G f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv := ContinuousMultilinearMap.uncurry0_curry0
  right_inv := ContinuousMultilinearMap.curry0_uncurry0 𝕜 G
  norm_map' := ContinuousMultilinearMap.uncurry0_norm
#align continuous_multilinear_curry_fin0 continuousMultilinearCurryFin0

variable {𝕜 G G'}

@[simp]
theorem continuousMultilinearCurryFin0_apply (f : G[×0]→L[𝕜] G') :
    continuousMultilinearCurryFin0 𝕜 G G' f = f 0 :=
  rfl
#align continuous_multilinear_curry_fin0_apply continuousMultilinearCurryFin0_apply

@[simp]
theorem continuousMultilinearCurryFin0_symm_apply (x : G') (v : Fin 0 → G) :
    (continuousMultilinearCurryFin0 𝕜 G G').symm x v = x :=
  rfl
#align continuous_multilinear_curry_fin0_symm_apply continuousMultilinearCurryFin0_symm_apply

end

/-! #### With 1 variable -/


variable (𝕜 G G')

/-- Continuous multilinear maps from `G^1` to `G'` are isomorphic with continuous linear maps from
`G` to `G'`. -/
def continuousMultilinearCurryFin1 : (G[×1]→L[𝕜] G') ≃ₗᵢ[𝕜] G →L[𝕜] G' :=
  (continuousMultilinearCurryRightEquiv 𝕜 (fun _ : Fin 1 => G) G').symm.trans
    (continuousMultilinearCurryFin0 𝕜 G (G →L[𝕜] G'))
#align continuous_multilinear_curry_fin1 continuousMultilinearCurryFin1

variable {𝕜 G G'}

@[simp]
theorem continuousMultilinearCurryFin1_apply (f : G[×1]→L[𝕜] G') (x : G) :
    continuousMultilinearCurryFin1 𝕜 G G' f x = f (Fin.snoc 0 x) :=
  rfl
#align continuous_multilinear_curry_fin1_apply continuousMultilinearCurryFin1_apply

@[simp]
theorem continuousMultilinearCurryFin1_symm_apply (f : G →L[𝕜] G') (v : Fin 1 → G) :
    (continuousMultilinearCurryFin1 𝕜 G G').symm f v = f (v 0) :=
  rfl
#align continuous_multilinear_curry_fin1_symm_apply continuousMultilinearCurryFin1_symm_apply

namespace ContinuousMultilinearMap

variable (𝕜 G G')

@[simp]
theorem norm_domDomCongr (σ : ι ≃ ι') (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => G) G') :
    ‖domDomCongr σ f‖ = ‖f‖ := by
  simp only [norm_def, LinearEquiv.coe_mk, ← σ.prod_comp,
    (σ.arrowCongr (Equiv.refl G)).surjective.forall, domDomCongr_apply, Equiv.arrowCongr_apply,
    Equiv.coe_refl, id_comp, comp_apply, Equiv.symm_apply_apply, id]
#align continuous_multilinear_map.norm_dom_dom_congr ContinuousMultilinearMap.norm_domDomCongr

/-- An equivalence of the index set defines a linear isometric equivalence between the spaces
of multilinear maps. -/
def domDomCongrₗᵢ (σ : ι ≃ ι') :
    ContinuousMultilinearMap 𝕜 (fun _ : ι => G) G' ≃ₗᵢ[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G' :=
  { domDomCongrEquiv σ with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    norm_map' := norm_domDomCongr 𝕜 G G' σ }
#align continuous_multilinear_map.dom_dom_congrₗᵢ ContinuousMultilinearMap.domDomCongrₗᵢ

variable {𝕜 G G'}

section

/-- A continuous multilinear map with variables indexed by `ι ⊕ ι'` defines a continuous
multilinear map with variables indexed by `ι` taking values in the space of continuous multilinear
maps with variables indexed by `ι'`. -/
def currySum (f : ContinuousMultilinearMap 𝕜 (fun _ : Sum ι ι' => G) G') :
    ContinuousMultilinearMap 𝕜 (fun _ : ι => G) (ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G') :=
  MultilinearMap.mkContinuousMultilinear (MultilinearMap.currySum f.toMultilinearMap) ‖f‖
    fun m m' => by simpa [Fintype.prod_sum_type, mul_assoc] using f.le_opNorm (Sum.elim m m')
#align continuous_multilinear_map.curry_sum ContinuousMultilinearMap.currySum

@[simp]
theorem currySum_apply (f : ContinuousMultilinearMap 𝕜 (fun _ : Sum ι ι' => G) G') (m : ι → G)
    (m' : ι' → G) : f.currySum m m' = f (Sum.elim m m') :=
  rfl
#align continuous_multilinear_map.curry_sum_apply ContinuousMultilinearMap.currySum_apply

/-- A continuous multilinear map with variables indexed by `ι` taking values in the space of
continuous multilinear maps with variables indexed by `ι'` defines a continuous multilinear map with
variables indexed by `ι ⊕ ι'`. -/
def uncurrySum (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => G)
    (ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G')) :
    ContinuousMultilinearMap 𝕜 (fun _ : Sum ι ι' => G) G' :=
  MultilinearMap.mkContinuous
    (toMultilinearMapLinear.compMultilinearMap f.toMultilinearMap).uncurrySum ‖f‖ fun m => by
    simpa [Fintype.prod_sum_type, mul_assoc] using
      (f (m ∘ Sum.inl)).le_of_opNorm_le (m ∘ Sum.inr) (f.le_opNorm _)
#align continuous_multilinear_map.uncurry_sum ContinuousMultilinearMap.uncurrySum

@[simp]
theorem uncurrySum_apply (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => G)
    (ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G'))
    (m : Sum ι ι' → G) : f.uncurrySum m = f (m ∘ Sum.inl) (m ∘ Sum.inr) :=
  rfl
#align continuous_multilinear_map.uncurry_sum_apply ContinuousMultilinearMap.uncurrySum_apply

variable (𝕜 ι ι' G G')

/-- Linear isometric equivalence between the space of continuous multilinear maps with variables
indexed by `ι ⊕ ι'` and the space of continuous multilinear maps with variables indexed by `ι`
taking values in the space of continuous multilinear maps with variables indexed by `ι'`.

The forward and inverse functions are `ContinuousMultilinearMap.currySum`
and `ContinuousMultilinearMap.uncurrySum`. Use this definition only if you need
some properties of `LinearIsometryEquiv`. -/
def currySumEquiv : ContinuousMultilinearMap 𝕜 (fun _ : Sum ι ι' => G) G' ≃ₗᵢ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : ι => G) (ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G') :=
  LinearIsometryEquiv.ofBounds
    { toFun := currySum
      invFun := uncurrySum
      map_add' := fun f g => by
        ext
        rfl
      map_smul' := fun c f => by
        ext
        rfl
      left_inv := fun f => by
        ext m
        exact congr_arg f (Sum.elim_comp_inl_inr m)
      right_inv := fun f => by
        ext m₁ m₂
        rfl }
    (fun f => MultilinearMap.mkContinuousMultilinear_norm_le _ (norm_nonneg f) _) fun f => by
      simp only [LinearEquiv.coe_symm_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _
#align continuous_multilinear_map.curry_sum_equiv ContinuousMultilinearMap.currySumEquiv

end

section

variable (𝕜 G G') {k l : ℕ} {s : Finset (Fin n)}

/-- If `s : Finset (Fin n)` is a finite set of cardinality `k` and its complement has cardinality
`l`, then the space of continuous multilinear maps `G [×n]→L[𝕜] G'` of `n` variables is isomorphic
to the space of continuous multilinear maps `G [×k]→L[𝕜] G [×l]→L[𝕜] G'` of `k` variables taking
values in the space of continuous multilinear maps of `l` variables. -/
def curryFinFinset {k l n : ℕ} {s : Finset (Fin n)} (hk : s.card = k) (hl : sᶜ.card = l) :
    (G[×n]→L[𝕜] G') ≃ₗᵢ[𝕜] G[×k]→L[𝕜] G[×l]→L[𝕜] G' :=
  (domDomCongrₗᵢ 𝕜 G G' (finSumEquivOfFinset hk hl).symm).trans
    (currySumEquiv 𝕜 (Fin k) (Fin l) G G')
#align continuous_multilinear_map.curry_fin_finset ContinuousMultilinearMap.curryFinFinset

variable {𝕜 G G'}

@[simp]
theorem curryFinFinset_apply (hk : s.card = k) (hl : sᶜ.card = l) (f : G[×n]→L[𝕜] G')
    (mk : Fin k → G) (ml : Fin l → G) : curryFinFinset 𝕜 G G' hk hl f mk ml =
      f fun i => Sum.elim mk ml ((finSumEquivOfFinset hk hl).symm i) :=
  rfl
#align continuous_multilinear_map.curry_fin_finset_apply ContinuousMultilinearMap.curryFinFinset_apply

@[simp]
theorem curryFinFinset_symm_apply (hk : s.card = k) (hl : sᶜ.card = l)
    (f : G[×k]→L[𝕜] G[×l]→L[𝕜] G') (m : Fin n → G) : (curryFinFinset 𝕜 G G' hk hl).symm f m =
      f (fun i => m <| finSumEquivOfFinset hk hl (Sum.inl i)) fun i =>
        m <| finSumEquivOfFinset hk hl (Sum.inr i) :=
  rfl
#align continuous_multilinear_map.curry_fin_finset_symm_apply ContinuousMultilinearMap.curryFinFinset_symm_apply

-- @[simp] -- Porting note (#10618): simp removed: simp can reduce LHS
theorem curryFinFinset_symm_apply_piecewise_const (hk : s.card = k) (hl : sᶜ.card = l)
    (f : G[×k]→L[𝕜] G[×l]→L[𝕜] G') (x y : G) :
    (curryFinFinset 𝕜 G G' hk hl).symm f (s.piecewise (fun _ => x) fun _ => y) =
      f (fun _ => x) fun _ => y :=
  MultilinearMap.curryFinFinset_symm_apply_piecewise_const hk hl _ x y
#align continuous_multilinear_map.curry_fin_finset_symm_apply_piecewise_const ContinuousMultilinearMap.curryFinFinset_symm_apply_piecewise_const

@[simp]
theorem curryFinFinset_symm_apply_const (hk : s.card = k) (hl : sᶜ.card = l)
    (f : G[×k]→L[𝕜] G[×l]→L[𝕜] G') (x : G) :
    ((curryFinFinset 𝕜 G G' hk hl).symm f fun _ => x) = f (fun _ => x) fun _ => x :=
  rfl
#align continuous_multilinear_map.curry_fin_finset_symm_apply_const ContinuousMultilinearMap.curryFinFinset_symm_apply_const

-- @[simp] -- Porting note (#10618): simp removed: simp can reduce LHS
theorem curryFinFinset_apply_const (hk : s.card = k) (hl : sᶜ.card = l) (f : G[×n]→L[𝕜] G')
    (x y : G) : (curryFinFinset 𝕜 G G' hk hl f (fun _ => x) fun _ => y) =
      f (s.piecewise (fun _ => x) fun _ => y) := by
  refine (curryFinFinset_symm_apply_piecewise_const hk hl _ _ _).symm.trans ?_
  rw [LinearIsometryEquiv.symm_apply_apply]
#align continuous_multilinear_map.curry_fin_finset_apply_const ContinuousMultilinearMap.curryFinFinset_apply_const

end

end ContinuousMultilinearMap
