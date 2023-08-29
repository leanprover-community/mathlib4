/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jujian Zhang
-/
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Submodule.Basic

#align_import algebra.direct_sum.decomposition from "leanprover-community/mathlib"@"4e861f25ba5ceef42ba0712d8ffeb32f38ad6441"

/-!
# Decompositions of additive monoids, groups, and modules into direct sums

## Main definitions

* `DirectSum.Decomposition ℳ`: A typeclass to provide a constructive decomposition from
  an additive monoid `M` into a family of additive submonoids `ℳ`
* `DirectSum.decompose ℳ`: The canonical equivalence provided by the above typeclass


## Main statements

* `DirectSum.Decomposition.isInternal`: The link to `DirectSum.IsInternal`.

## Implementation details

As we want to talk about different types of decomposition (additive monoids, modules, rings, ...),
we choose to avoid heavily bundling `DirectSum.decompose`, instead making copies for the
`AddEquiv`, `LinearEquiv`, etc. This means we have to repeat statements that follow from these
bundled homs, but means we don't have to repeat statements for different types of decomposition.
-/


variable {ι R M σ : Type*}

open DirectSum BigOperators

namespace DirectSum

section AddCommMonoid

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

/-- A decomposition is an equivalence between an additive monoid `M` and a direct sum of additive
submonoids `ℳ i` of that `M`, such that the "recomposition" is canonical. This definition also
works for additive groups and modules.

This is a version of `DirectSum.IsInternal` which comes with a constructive inverse to the
canonical "recomposition" rather than just a proof that the "recomposition" is bijective. -/
class Decomposition where
  decompose' : M → ⨁ i, ℳ i
  left_inv : Function.LeftInverse (DirectSum.coeAddMonoidHom ℳ) decompose'
  right_inv : Function.RightInverse (DirectSum.coeAddMonoidHom ℳ) decompose'
#align direct_sum.decomposition DirectSum.Decomposition

/-- `DirectSum.Decomposition` instances, while carrying data, are always equal. -/
instance : Subsingleton (Decomposition ℳ) :=
  ⟨fun x y ↦ by
    cases' x with x xl xr
    -- ⊢ { decompose' := x, left_inv := xl, right_inv := xr } = y
    cases' y with y yl yr
    -- ⊢ { decompose' := x, left_inv := xl, right_inv := xr } = { decompose' := y, le …
    congr
    -- ⊢ x = y
    exact Function.LeftInverse.eq_rightInverse xr yl⟩
    -- 🎉 no goals

variable [Decomposition ℳ]

protected theorem Decomposition.isInternal : DirectSum.IsInternal ℳ :=
  ⟨Decomposition.right_inv.injective, Decomposition.left_inv.surjective⟩
#align direct_sum.decomposition.is_internal DirectSum.Decomposition.isInternal

/-- If `M` is graded by `ι` with degree `i` component `ℳ i`, then it is isomorphic as
to a direct sum of components. This is the canonical spelling of the `decompose'` field. -/
def decompose : M ≃ ⨁ i, ℳ i where
  toFun := Decomposition.decompose'
  invFun := DirectSum.coeAddMonoidHom ℳ
  left_inv := Decomposition.left_inv
  right_inv := Decomposition.right_inv
#align direct_sum.decompose DirectSum.decompose

protected theorem Decomposition.inductionOn {p : M → Prop} (h_zero : p 0)
    (h_homogeneous : ∀ {i} (m : ℳ i), p (m : M)) (h_add : ∀ m m' : M, p m → p m' → p (m + m')) :
    ∀ m, p m := by
  let ℳ' : ι → AddSubmonoid M := fun i ↦
    (⟨⟨ℳ i, fun x y ↦ AddMemClass.add_mem x y⟩, (ZeroMemClass.zero_mem _)⟩ : AddSubmonoid M)
  haveI t : DirectSum.Decomposition ℳ' :=
    { decompose' := DirectSum.decompose ℳ
      left_inv := fun _ ↦ (decompose ℳ).left_inv _
      right_inv := fun _ ↦ (decompose ℳ).right_inv _ }
  have mem : ∀ m, m ∈ iSup ℳ' := fun _m ↦
    (DirectSum.IsInternal.addSubmonoid_iSup_eq_top ℳ' (Decomposition.isInternal ℳ')).symm ▸ trivial
  -- Porting note: needs to use @ even though no implicit argument is provided
  exact fun m ↦ @AddSubmonoid.iSup_induction _ _ _ ℳ' _ _ (mem m)
    (fun i m h ↦ h_homogeneous ⟨m, h⟩) h_zero h_add
--  exact fun m ↦
--    AddSubmonoid.iSup_induction ℳ' (mem m) (fun i m h ↦ h_homogeneous ⟨m, h⟩) h_zero h_add
#align direct_sum.decomposition.induction_on DirectSum.Decomposition.inductionOn

@[simp]
theorem Decomposition.decompose'_eq : Decomposition.decompose' = decompose ℳ := rfl
#align direct_sum.decomposition.decompose'_eq DirectSum.Decomposition.decompose'_eq

@[simp]
theorem decompose_symm_of {i : ι} (x : ℳ i) : (decompose ℳ).symm (DirectSum.of _ i x) = x :=
  DirectSum.coeAddMonoidHom_of ℳ _ _
#align direct_sum.decompose_symm_of DirectSum.decompose_symm_of

@[simp]
theorem decompose_coe {i : ι} (x : ℳ i) : decompose ℳ (x : M) = DirectSum.of _ i x := by
  rw [← decompose_symm_of _, Equiv.apply_symm_apply]
  -- 🎉 no goals
#align direct_sum.decompose_coe DirectSum.decompose_coe

theorem decompose_of_mem {x : M} {i : ι} (hx : x ∈ ℳ i) :
    decompose ℳ x = DirectSum.of (fun i ↦ ℳ i) i ⟨x, hx⟩ :=
  decompose_coe _ ⟨x, hx⟩
#align direct_sum.decompose_of_mem DirectSum.decompose_of_mem

theorem decompose_of_mem_same {x : M} {i : ι} (hx : x ∈ ℳ i) : (decompose ℳ x i : M) = x := by
  rw [decompose_of_mem _ hx, DirectSum.of_eq_same, Subtype.coe_mk]
  -- 🎉 no goals
#align direct_sum.decompose_of_mem_same DirectSum.decompose_of_mem_same

theorem decompose_of_mem_ne {x : M} {i j : ι} (hx : x ∈ ℳ i) (hij : i ≠ j) :
    (decompose ℳ x j : M) = 0 := by
  rw [decompose_of_mem _ hx, DirectSum.of_eq_of_ne _ _ _ _ hij, ZeroMemClass.coe_zero]
  -- 🎉 no goals
#align direct_sum.decompose_of_mem_ne DirectSum.decompose_of_mem_ne

/-- If `M` is graded by `ι` with degree `i` component `ℳ i`, then it is isomorphic as
an additive monoid to a direct sum of components. -/
-- Porting note: deleted [simps] and added the corresponding lemmas by hand
def decomposeAddEquiv : M ≃+ ⨁ i, ℳ i :=
  AddEquiv.symm { (decompose ℳ).symm with map_add' := map_add (DirectSum.coeAddMonoidHom ℳ) }
#align direct_sum.decompose_add_equiv DirectSum.decomposeAddEquiv

@[simp]
lemma decomposeAddEquiv_apply (a : M) :
    decomposeAddEquiv ℳ a = decompose ℳ a := rfl

@[simp]
lemma decomposeAddEquiv_symm_apply (a : ⨁ i, ℳ i) :
  (decomposeAddEquiv ℳ).symm a = (decompose ℳ).symm a := rfl

@[simp]
theorem decompose_zero : decompose ℳ (0 : M) = 0 :=
  map_zero (decomposeAddEquiv ℳ)
#align direct_sum.decompose_zero DirectSum.decompose_zero

@[simp]
theorem decompose_symm_zero : (decompose ℳ).symm 0 = (0 : M) :=
  map_zero (decomposeAddEquiv ℳ).symm
#align direct_sum.decompose_symm_zero DirectSum.decompose_symm_zero

@[simp]
theorem decompose_add (x y : M) : decompose ℳ (x + y) = decompose ℳ x + decompose ℳ y :=
  map_add (decomposeAddEquiv ℳ) x y
#align direct_sum.decompose_add DirectSum.decompose_add

@[simp]
theorem decompose_symm_add (x y : ⨁ i, ℳ i) :
    (decompose ℳ).symm (x + y) = (decompose ℳ).symm x + (decompose ℳ).symm y :=
  map_add (decomposeAddEquiv ℳ).symm x y
#align direct_sum.decompose_symm_add DirectSum.decompose_symm_add

@[simp]
theorem decompose_sum {ι'} (s : Finset ι') (f : ι' → M) :
    decompose ℳ (∑ i in s, f i) = ∑ i in s, decompose ℳ (f i) :=
  map_sum (decomposeAddEquiv ℳ) f s
#align direct_sum.decompose_sum DirectSum.decompose_sum

@[simp]
theorem decompose_symm_sum {ι'} (s : Finset ι') (f : ι' → ⨁ i, ℳ i) :
    (decompose ℳ).symm (∑ i in s, f i) = ∑ i in s, (decompose ℳ).symm (f i) :=
  map_sum (decomposeAddEquiv ℳ).symm f s
#align direct_sum.decompose_symm_sum DirectSum.decompose_symm_sum

theorem sum_support_decompose [∀ (i) (x : ℳ i), Decidable (x ≠ 0)] (r : M) :
    (∑ i in (decompose ℳ r).support, (decompose ℳ r i : M)) = r := by
  conv_rhs =>
    rw [← (decompose ℳ).symm_apply_apply r, ← sum_support_of (fun i ↦ ℳ i) (decompose ℳ r)]
  rw [decompose_symm_sum]
  -- ⊢ ∑ i in DFinsupp.support (↑(decompose ℳ) r), ↑(↑(↑(decompose ℳ) r) i) = ∑ i i …
  simp_rw [decompose_symm_of]
  -- 🎉 no goals
#align direct_sum.sum_support_decompose DirectSum.sum_support_decompose

end AddCommMonoid

/-- The `-` in the statements below doesn't resolve without this line.

This seems to be a problem of synthesized vs inferred typeclasses disagreeing. If we replace
the statement of `decompose_neg` with `@Eq (⨁ i, ℳ i) (decompose ℳ (-x)) (-decompose ℳ x)`
instead of `decompose ℳ (-x) = -decompose ℳ x`, which forces the typeclasses needed by `⨁ i, ℳ i`
to be found by unification rather than synthesis, then everything works fine without this
instance. -/
instance addCommGroupSetLike [AddCommGroup M] [SetLike σ M] [AddSubgroupClass σ M] (ℳ : ι → σ) :
    AddCommGroup (⨁ i, ℳ i) := by infer_instance
                                  -- 🎉 no goals
#align direct_sum.add_comm_group_set_like DirectSum.addCommGroupSetLike

section AddCommGroup

variable [DecidableEq ι] [AddCommGroup M]

variable [SetLike σ M] [AddSubgroupClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

@[simp]
theorem decompose_neg (x : M) : decompose ℳ (-x) = -decompose ℳ x :=
  map_neg (decomposeAddEquiv ℳ) x
#align direct_sum.decompose_neg DirectSum.decompose_neg

@[simp]
theorem decompose_symm_neg (x : ⨁ i, ℳ i) : (decompose ℳ).symm (-x) = -(decompose ℳ).symm x :=
  map_neg (decomposeAddEquiv ℳ).symm x
#align direct_sum.decompose_symm_neg DirectSum.decompose_symm_neg

@[simp]
theorem decompose_sub (x y : M) : decompose ℳ (x - y) = decompose ℳ x - decompose ℳ y :=
  map_sub (decomposeAddEquiv ℳ) x y
#align direct_sum.decompose_sub DirectSum.decompose_sub

@[simp]
theorem decompose_symm_sub (x y : ⨁ i, ℳ i) :
    (decompose ℳ).symm (x - y) = (decompose ℳ).symm x - (decompose ℳ).symm y :=
  map_sub (decomposeAddEquiv ℳ).symm x y
#align direct_sum.decompose_symm_sub DirectSum.decompose_symm_sub

end AddCommGroup

section Module

variable [DecidableEq ι] [Semiring R] [AddCommMonoid M] [Module R M]

variable (ℳ : ι → Submodule R M)

variable [Decomposition ℳ]

/-- If `M` is graded by `ι` with degree `i` component `ℳ i`, then it is isomorphic as
a module to a direct sum of components. -/
@[simps! (config := { fullyApplied := false })]
def decomposeLinearEquiv : M ≃ₗ[R] ⨁ i, ℳ i :=
  LinearEquiv.symm
    { (decomposeAddEquiv ℳ).symm with map_smul' := map_smul (DirectSum.coeLinearMap ℳ) }
#align direct_sum.decompose_linear_equiv DirectSum.decomposeLinearEquiv

@[simp]
theorem decompose_smul (r : R) (x : M) : decompose ℳ (r • x) = r • decompose ℳ x :=
  map_smul (decomposeLinearEquiv ℳ) r x
#align direct_sum.decompose_smul DirectSum.decompose_smul

end Module

end DirectSum
