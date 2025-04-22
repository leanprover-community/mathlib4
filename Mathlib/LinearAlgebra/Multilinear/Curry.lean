/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Data.Fintype.Sort
import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Currying of multilinear maps
We register isomorphisms corresponding to currying or uncurrying variables, transforming a
multilinear function `f` on `n+1` variables into a linear function taking values in multilinear
functions in `n` variables, and into a multilinear function in `n` variables taking values in linear
functions. These operations are called `f.curryLeft` and `f.curryRight` respectively
(with inverses `f.uncurryLeft` and `f.uncurryRight`). These operations induce linear equivalences
between spaces of multilinear functions in `n+1` variables and spaces of linear functions into
multilinear functions in `n` variables (resp. multilinear functions in `n` variables taking values
in linear functions), called respectively `multilinearCurryLeftEquiv` and
`multilinearCurryRightEquiv`.

-/

open Fin Function Finset Set

universe uR uS uι v v' v₁ v₂ v₃

variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₂ : Type v₂} {M₃ : Type v₃} {M' : Type v'}

/-!
### Currying

We associate to a multilinear map in `n+1` variables (i.e., based on `Fin n.succ`) two
curried functions, named `f.curryLeft` (which is a linear map on `E 0` taking values
in multilinear maps in `n` variables) and `f.curryRight` (which is a multilinear map in `n`
variables taking values in linear maps on `E 0`). In both constructions, the variable that is
singled out is `0`, to take advantage of the operations `cons` and `tail` on `Fin n`.
The inverse operations are called `uncurryLeft` and `uncurryRight`.

We also register linear equiv versions of these correspondences, in
`multilinearCurryLeftEquiv` and `multilinearCurryRightEquiv`.
-/


open MultilinearMap

variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [AddCommMonoid M'] [AddCommMonoid M₂]
  [∀ i, Module R (M i)] [Module R M'] [Module R M₂]

/-! #### Left currying -/


/-- Given a linear map `f` from `M 0` to multilinear maps on `n` variables,
construct the corresponding multilinear map on `n+1` variables obtained by concatenating
the variables, given by `m ↦ f (m 0) (tail m)` -/
def LinearMap.uncurryLeft (f : M 0 →ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂) :
    MultilinearMap R M M₂ :=
  MultilinearMap.mk' (fun m ↦ f (m 0) (tail m))
    (fun m i x y ↦ by
      by_cases h : i = 0
      · subst i
        simp only [update_self, map_add, tail_update_zero, MultilinearMap.add_apply]
      · simp_rw [update_of_ne (Ne.symm h)]
        revert x y
        rw [← succ_pred i h]
        intro x y
        rw [tail_update_succ, MultilinearMap.map_update_add, tail_update_succ, tail_update_succ])
    (fun m i c x ↦ by
      by_cases h : i = 0
      · subst i
        simp only [update_self, map_smul, tail_update_zero, MultilinearMap.smul_apply]
      · simp_rw [update_of_ne (Ne.symm h)]
        revert x
        rw [← succ_pred i h]
        intro x
        rw [tail_update_succ, tail_update_succ, MultilinearMap.map_update_smul])

@[simp]
theorem LinearMap.uncurryLeft_apply (f : M 0 →ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂)
    (m : ∀ i, M i) : f.uncurryLeft m = f (m 0) (tail m) :=
  rfl

/-- Given a multilinear map `f` in `n+1` variables, split the first variable to obtain
a linear map into multilinear maps in `n` variables, given by `x ↦ (m ↦ f (cons x m))`. -/
def MultilinearMap.curryLeft (f : MultilinearMap R M M₂) :
    M 0 →ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂ where
  toFun x := MultilinearMap.mk' (fun m => f (cons x m))
  map_add' x y := by
    ext m
    exact cons_add f m x y
  map_smul' c x := by
    ext m
    exact cons_smul f m c x

@[simp]
theorem MultilinearMap.curryLeft_apply (f : MultilinearMap R M M₂) (x : M 0)
    (m : ∀ i : Fin n, M i.succ) : f.curryLeft x m = f (cons x m) :=
  rfl

@[simp]
theorem LinearMap.curry_uncurryLeft (f : M 0 →ₗ[R] MultilinearMap R (fun i :
    Fin n => M i.succ) M₂) : f.uncurryLeft.curryLeft = f := by
  ext m x
  simp only [tail_cons, LinearMap.uncurryLeft_apply, MultilinearMap.curryLeft_apply]
  rw [cons_zero]

@[simp]
theorem MultilinearMap.uncurry_curryLeft (f : MultilinearMap R M M₂) :
    f.curryLeft.uncurryLeft = f := by
  ext m
  simp

variable (R M M₂)

/-- The space of multilinear maps on `Π (i : Fin (n+1)), M i` is canonically isomorphic to
the space of linear maps from `M 0` to the space of multilinear maps on
`Π (i : Fin n), M i.succ`, by separating the first variable. We register this isomorphism as a
linear isomorphism in `multilinearCurryLeftEquiv R M M₂`.

The direct and inverse maps are given by `f.curryLeft` and `f.uncurryLeft`. Use these
unless you need the full framework of linear equivs. -/
def multilinearCurryLeftEquiv :
    MultilinearMap R M M₂ ≃ₗ[R] (M 0 →ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂) where
  toFun := MultilinearMap.curryLeft
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := LinearMap.uncurryLeft
  left_inv := MultilinearMap.uncurry_curryLeft
  right_inv := LinearMap.curry_uncurryLeft

variable {R M M₂}

/-! #### Right currying -/


/-- Given a multilinear map `f` in `n` variables to the space of linear maps from `M (last n)` to
`M₂`, construct the corresponding multilinear map on `n+1` variables obtained by concatenating
the variables, given by `m ↦ f (init m) (m (last n))` -/
def MultilinearMap.uncurryRight
    (f : MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) →ₗ[R] M₂)) :
    MultilinearMap R M M₂ :=
  MultilinearMap.mk' (fun m ↦ f (init m) (m (last n)))
    (fun m i x y ↦ by
      by_cases h : i.val < n
      · have : last n ≠ i := Ne.symm (ne_of_lt h)
        simp_rw [update_of_ne this]
        revert x y
        rw [(castSucc_castLT i h).symm]
        intro x y
        rw [init_update_castSucc, MultilinearMap.map_update_add, init_update_castSucc,
          init_update_castSucc, LinearMap.add_apply]
      · revert x y
        rw [eq_last_of_not_lt h]
        intro x y
        simp_rw [init_update_last, update_self, LinearMap.map_add])
    (fun m i c x ↦ by
      by_cases h : i.val < n
      · have : last n ≠ i := Ne.symm (ne_of_lt h)
        simp_rw [update_of_ne this]
        revert x
        rw [(castSucc_castLT i h).symm]
        intro x
        rw [init_update_castSucc, init_update_castSucc, MultilinearMap.map_update_smul,
          LinearMap.smul_apply]
      · revert x
        rw [eq_last_of_not_lt h]
        intro x
        simp_rw [update_self, init_update_last, map_smul])

@[simp]
theorem MultilinearMap.uncurryRight_apply
    (f : MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) →ₗ[R] M₂))
    (m : ∀ i, M i) : f.uncurryRight m = f (init m) (m (last n)) :=
  rfl

/-- Given a multilinear map `f` in `n+1` variables, split the last variable to obtain
a multilinear map in `n` variables taking values in linear maps from `M (last n)` to `M₂`, given by
`m ↦ (x ↦ f (snoc m x))`. -/
def MultilinearMap.curryRight (f : MultilinearMap R M M₂) :
    MultilinearMap R (fun i : Fin n => M (Fin.castSucc i)) (M (last n) →ₗ[R] M₂) :=
  MultilinearMap.mk' (fun m ↦
    { toFun := fun x => f (snoc m x)
      map_add' := fun x y => by simp_rw [f.snoc_add]
      map_smul' := fun c x => by simp only [f.snoc_smul, RingHom.id_apply] })

@[simp]
theorem MultilinearMap.curryRight_apply (f : MultilinearMap R M M₂)
    (m : ∀ i : Fin n, M (castSucc i)) (x : M (last n)) : f.curryRight m x = f (snoc m x) :=
  rfl

@[simp]
theorem MultilinearMap.curry_uncurryRight
    (f : MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) →ₗ[R] M₂)) :
    f.uncurryRight.curryRight = f := by
  ext m x
  simp only [snoc_last, MultilinearMap.curryRight_apply, MultilinearMap.uncurryRight_apply]
  rw [init_snoc]

@[simp]
theorem MultilinearMap.uncurry_curryRight (f : MultilinearMap R M M₂) :
    f.curryRight.uncurryRight = f := by
  ext m
  simp

variable (R M M₂)

/-- The space of multilinear maps on `Π (i : Fin (n+1)), M i` is canonically isomorphic to
the space of linear maps from the space of multilinear maps on `Π (i : Fin n), M (castSucc i)` to
the space of linear maps on `M (last n)`, by separating the last variable. We register this
isomorphism as a linear isomorphism in `multilinearCurryRightEquiv R M M₂`.

The direct and inverse maps are given by `f.curryRight` and `f.uncurryRight`. Use these
unless you need the full framework of linear equivs. -/
def multilinearCurryRightEquiv :
    MultilinearMap R M M₂ ≃ₗ[R]
      MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) →ₗ[R] M₂) where
  toFun := MultilinearMap.curryRight
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := MultilinearMap.uncurryRight
  left_inv := MultilinearMap.uncurry_curryRight
  right_inv := MultilinearMap.curry_uncurryRight

namespace MultilinearMap

variable {ι' : Type*} {R M₂}

/-- A multilinear map on `∀ i : ι ⊕ ι', M'` defines a multilinear map on `∀ i : ι, M'`
taking values in the space of multilinear maps on `∀ i : ι', M'`. -/
def currySum (f : MultilinearMap R (fun _ : ι ⊕ ι' => M') M₂) :
    MultilinearMap R (fun _ : ι => M') (MultilinearMap R (fun _ : ι' => M') M₂) where
  toFun u :=
    { toFun := fun v => f (Sum.elim u v)
      map_update_add' := fun v i x y => by
        letI := Classical.decEq ι
        simp only [← Sum.update_elim_inr, f.map_update_add]
      map_update_smul' := fun v i c x => by
        letI := Classical.decEq ι
        simp only [← Sum.update_elim_inr, f.map_update_smul] }
  map_update_add' u i x y :=
    ext fun v => by
      letI := Classical.decEq ι'
      simp only [MultilinearMap.coe_mk, add_apply, ← Sum.update_elim_inl, f.map_update_add]
  map_update_smul' u i c x :=
    ext fun v => by
      letI := Classical.decEq ι'
      simp only [MultilinearMap.coe_mk, smul_apply, ← Sum.update_elim_inl, f.map_update_smul]

@[simp]
theorem currySum_apply (f : MultilinearMap R (fun _ : ι ⊕ ι' => M') M₂) (u : ι → M')
    (v : ι' → M') : f.currySum u v = f (Sum.elim u v) :=
  rfl

/-- A multilinear map on `∀ i : ι, M'` taking values in the space of multilinear maps
on `∀ i : ι', M'` defines a multilinear map on `∀ i : ι ⊕ ι', M'`. -/
def uncurrySum (f : MultilinearMap R (fun _ : ι => M') (MultilinearMap R (fun _ : ι' => M') M₂)) :
    MultilinearMap R (fun _ : ι ⊕ ι' => M') M₂ where
  toFun u := f (u ∘ Sum.inl) (u ∘ Sum.inr)
  map_update_add' u i x y := by
    letI := (@Sum.inl_injective ι ι').decidableEq
    letI := (@Sum.inr_injective ι ι').decidableEq
    cases i <;>
      simp only [MultilinearMap.map_update_add, add_apply, Sum.update_inl_comp_inl,
        Sum.update_inl_comp_inr, Sum.update_inr_comp_inl, Sum.update_inr_comp_inr]
  map_update_smul' u i c x := by
    letI := (@Sum.inl_injective ι ι').decidableEq
    letI := (@Sum.inr_injective ι ι').decidableEq
    cases i <;>
      simp only [MultilinearMap.map_update_smul, smul_apply, Sum.update_inl_comp_inl,
        Sum.update_inl_comp_inr, Sum.update_inr_comp_inl, Sum.update_inr_comp_inr]

@[simp]
theorem uncurrySum_aux_apply
    (f : MultilinearMap R (fun _ : ι => M') (MultilinearMap R (fun _ : ι' => M') M₂))
    (u : ι ⊕ ι' → M') : f.uncurrySum u = f (u ∘ Sum.inl) (u ∘ Sum.inr) :=
  rfl

variable (ι ι' R M₂ M')

/-- Linear equivalence between the space of multilinear maps on `∀ i : ι ⊕ ι', M'` and the space
of multilinear maps on `∀ i : ι, M'` taking values in the space of multilinear maps
on `∀ i : ι', M'`. -/
def currySumEquiv :
    MultilinearMap R (fun _ : ι ⊕ ι' => M') M₂ ≃ₗ[R]
      MultilinearMap R (fun _ : ι => M') (MultilinearMap R (fun _ : ι' => M') M₂) where
  toFun := currySum
  invFun := uncurrySum
  left_inv f := ext fun u => by simp
  right_inv f := by
    ext
    simp
  map_add' f g := by
    ext
    rfl
  map_smul' c f := by
    ext
    rfl

variable {ι ι' R M₂ M'}

@[simp]
theorem coe_currySumEquiv : ⇑(currySumEquiv R ι M₂ M' ι') = currySum :=
  rfl

-- Porting note: fixed missing letter `y` in name
@[simp]
theorem coe_currySumEquiv_symm : ⇑(currySumEquiv R ι M₂ M' ι').symm = uncurrySum :=
  rfl

variable (R M₂ M')

/-- If `s : Finset (Fin n)` is a finite set of cardinality `k` and its complement has cardinality
`l`, then the space of multilinear maps on `fun i : Fin n => M'` is isomorphic to the space of
multilinear maps on `fun i : Fin k => M'` taking values in the space of multilinear maps
on `fun i : Fin l => M'`. -/
def curryFinFinset {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k) (hl : #sᶜ = l) :
    MultilinearMap R (fun _ : Fin n => M') M₂ ≃ₗ[R]
      MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂) :=
  (domDomCongrLinearEquiv R R M' M₂ (finSumEquivOfFinset hk hl).symm).trans
    (currySumEquiv R (Fin k) M₂ M' (Fin l))

variable {R M₂ M'}

@[simp]
theorem curryFinFinset_apply {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k) (hl : #sᶜ = l)
    (f : MultilinearMap R (fun _ : Fin n => M') M₂) (mk : Fin k → M') (ml : Fin l → M') :
    curryFinFinset R M₂ M' hk hl f mk ml =
      f fun i => Sum.elim mk ml ((finSumEquivOfFinset hk hl).symm i) :=
  rfl

@[simp]
theorem curryFinFinset_symm_apply {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k)
    (hl : #sᶜ = l)
    (f : MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂))
    (m : Fin n → M') :
    (curryFinFinset R M₂ M' hk hl).symm f m =
      f (fun i => m <| finSumEquivOfFinset hk hl (Sum.inl i)) fun i =>
        m <| finSumEquivOfFinset hk hl (Sum.inr i) :=
  rfl

theorem curryFinFinset_symm_apply_piecewise_const {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k)
    (hl : #sᶜ = l)
    (f : MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂))
    (x y : M') :
    (curryFinFinset R M₂ M' hk hl).symm f (s.piecewise (fun _ => x) fun _ => y) =
      f (fun _ => x) fun _ => y := by
  rw [curryFinFinset_symm_apply]; congr
  · ext
    rw [finSumEquivOfFinset_inl, Finset.piecewise_eq_of_mem]
    apply Finset.orderEmbOfFin_mem
  · ext
    rw [finSumEquivOfFinset_inr, Finset.piecewise_eq_of_not_mem]
    exact Finset.mem_compl.1 (Finset.orderEmbOfFin_mem _ _ _)

@[simp]
theorem curryFinFinset_symm_apply_const {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k)
    (hl : #sᶜ = l)
    (f : MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂))
    (x : M') : ((curryFinFinset R M₂ M' hk hl).symm f fun _ => x) = f (fun _ => x) fun _ => x :=
  rfl

theorem curryFinFinset_apply_const {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k)
    (hl : #sᶜ = l) (f : MultilinearMap R (fun _ : Fin n => M') M₂) (x y : M') :
    (curryFinFinset R M₂ M' hk hl f (fun _ => x) fun _ => y) =
      f (s.piecewise (fun _ => x) fun _ => y) := by
  -- Porting note: `rw` fails
  refine (curryFinFinset_symm_apply_piecewise_const hk hl _ _ _).symm.trans ?_
  rw [LinearEquiv.symm_apply_apply]

end MultilinearMap
