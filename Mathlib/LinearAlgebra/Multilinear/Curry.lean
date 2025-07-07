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

universe uR uS uι uι' v v' v₁ v₂ v₃

variable {R : Type uR} {S : Type uS} {ι : Type uι} {ι' : Type uι'} {n : ℕ}
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
    (fun m i x y ↦ by cases i using Fin.cases <;> simp [Ne.symm])
    (fun m i c x ↦ by cases i using Fin.cases <;> simp [Ne.symm])

@[simp]
theorem LinearMap.uncurryLeft_apply (f : M 0 →ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂)
    (m : ∀ i, M i) : f.uncurryLeft m = f (m 0) (tail m) :=
  rfl

/-- Given a multilinear map `f` in `n+1` variables, split the first variable to obtain
a linear map into multilinear maps in `n` variables, given by `x ↦ (m ↦ f (cons x m))`. -/
def MultilinearMap.curryLeft (f : MultilinearMap R M M₂) :
    M 0 →ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂ where
  toFun x := MultilinearMap.mk' fun m => f (cons x m)
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
@[simps]
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
    (fun m i x y ↦ by cases i using Fin.lastCases <;> simp [Ne.symm])
    (fun m i c x ↦ by cases i using Fin.lastCases <;> simp [Ne.symm])

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
  MultilinearMap.mk' fun m ↦
    { toFun := fun x => f (snoc m x)
      map_add' := fun x y => by simp_rw [f.snoc_add]
      map_smul' := fun c x => by simp only [f.snoc_smul, RingHom.id_apply] }

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

variable {R M M₂}

/-- Given a linear map from `M p` to the space of multilinear maps
in `n` variables `M 0`, ..., `M n` with `M p` removed,
returns a multilinear map in all `n + 1` variables. -/
@[simps!]
def LinearMap.uncurryMid (p : Fin (n + 1))
    (f : M p →ₗ[R] MultilinearMap R (fun i ↦ M (p.succAbove i)) M₂) : MultilinearMap R M M₂ :=
  .mk' (fun m ↦ f (m p) (p.removeNth m))
    (fun m i x y ↦ by cases i using Fin.succAboveCases p <;> simp)
    (fun m i x y ↦ by cases i using Fin.succAboveCases p <;> simp)

/-- Interpret a multilinear map in `n + 1` variables
as a linear map in `p`th variable with values in the multilinear maps in the other variables. -/
@[simps!]
def MultilinearMap.curryMid (p : Fin (n + 1)) (f : MultilinearMap R M M₂) :
    M p →ₗ[R] MultilinearMap R (fun i ↦ M (p.succAbove i)) M₂ where
  toFun x := .mk' fun m ↦ f (p.insertNth x m)
  map_add' x y := by ext; simp [map_insertNth_add]
  map_smul' c x := by ext; simp [map_insertNth_smul]

@[simp]
theorem LinearMap.curryMid_uncurryMid (i : Fin (n + 1))
    (f : M i →ₗ[R] MultilinearMap R (fun j ↦ M (i.succAbove j)) M₂) :
    (f.uncurryMid i).curryMid i = f := by ext; simp

@[simp]
theorem MultilinearMap.uncurryMid_curryMid (i : Fin (n + 1)) (f : MultilinearMap R M M₂) :
    (f.curryMid i).uncurryMid i = f := by ext; simp

variable (R M M₂)

/-- `MultilinearMap.curryMid` as a linear equivalence. -/
@[simps]
def MultilinearMap.curryMidLinearEquiv (p : Fin (n + 1)) :
    MultilinearMap R M M₂ ≃ₗ[R] M p →ₗ[R] MultilinearMap R (fun i ↦ M (p.succAbove i)) M₂ where
  toFun := MultilinearMap.curryMid p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := LinearMap.uncurryMid p
  left_inv := MultilinearMap.uncurryMid_curryMid p
  right_inv := LinearMap.curryMid_uncurryMid p

namespace MultilinearMap

variable {R M₂} {N : (ι ⊕ ι') → Type*}
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

/-- Given a family of modules `N : (ι ⊕ ι') → Type*`, a multilinear map
on `(fun _ : ι ⊕ ι' => M')` induces a multilinear map on
`(fun (i : ι) ↦ N (.inl i))` taking values in the space of
linear maps on `(fun (i : ι') ↦ N (.inr i))`. -/
def currySum (f : MultilinearMap R N M₂) :
    MultilinearMap R (fun i : ι ↦ N (.inl i)) (MultilinearMap R (fun i : ι' ↦ N (.inr i)) M₂) where
  toFun u :=
    { toFun v := f (Sum.rec u v)
      map_update_add' := by letI := Classical.decEq ι; aesop
      map_update_smul' := by letI := Classical.decEq ι; aesop }
  map_update_add' u i x y :=
    ext fun _ ↦ by letI := Classical.decEq ι'; simp
  map_update_smul' u i c x :=
    ext fun _ ↦ by letI := Classical.decEq ι'; simp

@[simp low]
theorem currySum_apply (f : MultilinearMap R N M₂)
    (u : (i : ι) → N (Sum.inl i)) (v : (i : ι') → N (Sum.inr i)) :
    currySum f u v = f (Sum.rec u v) := rfl

@[simp]
theorem currySum_apply' {N : Type*} [AddCommMonoid N] [Module R N]
    (f : MultilinearMap R (fun _ : ι ⊕ ι' ↦ N) M₂)
    (u : ι → N) (v : ι' → N) :
    currySum f u v = f (Sum.elim u v) := rfl

@[simp]
lemma currySum_add (f₁ f₂ : MultilinearMap R N M₂) :
    currySum (f₁ + f₂) = currySum f₁ + currySum f₂ := rfl

@[simp]
lemma currySum_smul (r : R) (f : MultilinearMap R N M₂):
    currySum (r • f) = r • currySum f := rfl

/-- Given a family of modules `N : (ι ⊕ ι') → Type*`, a multilinear map on
`(fun (i : ι) ↦ N (.inl i))` taking values in the space of
linear maps on `(fun (i : ι') ↦ N (.inr i))` induces a multilinear map
on `(fun _ : ι ⊕ ι' => M')` induces. -/
def uncurrySum
    (g : MultilinearMap R (fun i : ι ↦ N (.inl i))
      (MultilinearMap R (fun i : ι' ↦ N (.inr i)) M₂)) :
    MultilinearMap R N M₂  where
  toFun u := g (fun i ↦ u (.inl i)) (fun i' ↦ u (.inr i'))
  map_update_add' := by
    letI := Classical.decEq ι
    letI := Classical.decEq ι'
    rintro _ _ (_ | _) _ _ <;> simp
  map_update_smul' := by
    letI := Classical.decEq ι
    letI := Classical.decEq ι'
    rintro _ _ (_ | _) _ _ <;> simp

@[simp]
theorem uncurrySum_apply
    (g : MultilinearMap R (fun i : ι ↦ N (.inl i))
      (MultilinearMap R (fun i : ι' ↦ N (.inr i)) M₂)) (u) :
    g.uncurrySum u =
      g (fun i ↦ u (.inl i)) (fun i' ↦ u (.inr i')) := rfl

@[simp]
lemma uncurrySum_add
    (g₁ g₂ : MultilinearMap R (fun i : ι ↦ N (.inl i))
      (MultilinearMap R (fun i : ι' ↦ N (.inr i)) M₂)) :
    uncurrySum (g₁ + g₂) = uncurrySum g₁ + uncurrySum g₂ :=
  rfl

lemma uncurrySum_smul
    (r : R) (g : MultilinearMap R (fun i : ι ↦ N (.inl i))
      (MultilinearMap R (fun i : ι' ↦ N (.inr i)) M₂)) :
    uncurrySum (r • g) = r • uncurrySum g :=
  rfl

@[deprecated (since := "2025-04-23")] alias uncurrySum_aux_apply := uncurrySum_apply

@[simp]
lemma uncurrySum_currySum (f : MultilinearMap R N M₂) :
    uncurrySum (currySum f) = f := by
  ext
  simp only [uncurrySum_apply, currySum_apply]
  congr
  ext (_ | _) <;> simp

@[simp]
lemma currySum_uncurrySum
    (g : MultilinearMap R (fun i : ι ↦ N (.inl i))
      (MultilinearMap R (fun i : ι' ↦ N (.inr i)) M₂)) :
    currySum (uncurrySum g) = g :=
  rfl

/-- Multilinear maps on `N : (ι ⊕ ι') → Type*` identify to multilinear maps
from `(fun (i : ι) ↦ N (.inl i))` taking values in the space of
linear maps on `(fun (i : ι') ↦ N (.inr i))`. -/
@[simps]
def currySumEquiv : MultilinearMap R N M₂ ≃ₗ[R]
    MultilinearMap R (fun i : ι ↦ N (.inl i))
      (MultilinearMap R (fun i : ι' ↦ N (.inr i)) M₂) where
  toFun := currySum
  invFun := uncurrySum
  left_inv _ := by simp
  map_add' := by aesop
  map_smul' := by aesop

@[simp]
theorem coe_currySumEquiv : ⇑(currySumEquiv (R := R) (N := N) (M₂ := M₂)) = currySum :=
  rfl

@[simp]
theorem coe_currySumEquiv_symm : ⇑(currySumEquiv (R := R) (N := N) (M₂ := M₂)).symm = uncurrySum :=
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
    currySumEquiv

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
    rw [finSumEquivOfFinset_inr, Finset.piecewise_eq_of_notMem]
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
  rw [← curryFinFinset_symm_apply_piecewise_const hk hl, LinearEquiv.symm_apply_apply]

end MultilinearMap
