/-
Copyright (c) 2020 Zhangir Azerbayev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Zhangir Azerbayev
-/
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.Multilinear.TensorProduct

#align_import linear_algebra.alternating from "leanprover-community/mathlib"@"bd65478311e4dfd41f48bf38c7e3b02fb75d0163"

/-!
# Alternating Maps

We construct the bundled function `AlternatingMap`, which extends `MultilinearMap` with all the
arguments of the same type.

## Main definitions
* `AlternatingMap R M N ι` is the space of `R`-linear alternating maps from `ι → M` to `N`.
* `f.map_eq_zero_of_eq` expresses that `f` is zero when two inputs are equal.
* `f.map_swap` expresses that `f` is negated when two inputs are swapped.
* `f.map_perm` expresses how `f` varies by a sign change under a permutation of its inputs.
* An `AddCommMonoid`, `AddCommGroup`, and `Module` structure over `AlternatingMap`s that
  matches the definitions over `MultilinearMap`s.
* `MultilinearMap.domDomCongr`, for permutating the elements within a family.
* `MultilinearMap.alternatization`, which makes an alternating map out of a non-alternating one.
* `AlternatingMap.domCoprod`, which behaves as a product between two alternating maps.
* `AlternatingMap.curryLeft`, for binding the leftmost argument of an alternating map indexed
  by `Fin n.succ`.

## Implementation notes
`AlternatingMap` is defined in terms of `map_eq_zero_of_eq`, as this is easier to work with than
using `map_swap` as a definition, and does not require `Neg N`.

`AlternatingMap`s are provided with a coercion to `MultilinearMap`, along with a set of
`norm_cast` lemmas that act on the algebraic structure:

* `AlternatingMap.coe_add`
* `AlternatingMap.coe_zero`
* `AlternatingMap.coe_sub`
* `AlternatingMap.coe_neg`
* `AlternatingMap.coe_smul`
-/


-- semiring / add_comm_monoid

variable {R : Type*} [Semiring R]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable {N : Type*} [AddCommMonoid N] [Module R N]

variable {P : Type*} [AddCommMonoid P] [Module R P]

-- semiring / add_comm_group

variable {M' : Type*} [AddCommGroup M'] [Module R M']

variable {N' : Type*} [AddCommGroup N'] [Module R N']

variable {ι ι' ι'' : Type*}

section

variable (R M N ι)

/-- An alternating map is a multilinear map that vanishes when two of its arguments are equal.
-/
structure AlternatingMap extends MultilinearMap R (fun _ : ι => M) N where
  /-- The map is alternating: if `v` has two equal coordinates, then `f v = 0`. -/
  map_eq_zero_of_eq' : ∀ (v : ι → M) (i j : ι), v i = v j → i ≠ j → toFun v = 0
#align alternating_map AlternatingMap

end

/-- The multilinear map associated to an alternating map -/
add_decl_doc AlternatingMap.toMultilinearMap

namespace AlternatingMap

variable (f f' : AlternatingMap R M N ι)

variable (g g₂ : AlternatingMap R M N' ι)

variable (g' : AlternatingMap R M' N' ι)

variable (v : ι → M) (v' : ι → M')

open Function

/-! Basic coercion simp lemmas, largely copied from `RingHom` and `MultilinearMap` -/


section Coercions

instance funLike : FunLike (AlternatingMap R M N ι) (ι → M) (fun _ => N) where
  coe f := f.toFun
  coe_injective' := fun f g h ↦ by
    rcases f with ⟨⟨_, _, _⟩, _⟩
    -- ⊢ { toMultilinearMap := { toFun := toFun✝, map_add' := map_add'✝, map_smul' := …
    rcases g with ⟨⟨_, _, _⟩, _⟩
    -- ⊢ { toMultilinearMap := { toFun := toFun✝¹, map_add' := map_add'✝¹, map_smul'  …
    congr
    -- 🎉 no goals
#align alternating_map.fun_like AlternatingMap.funLike

-- shortcut instance
instance coeFun : CoeFun (AlternatingMap R M N ι) fun _ => (ι → M) → N :=
  ⟨FunLike.coe⟩
#align alternating_map.has_coe_to_fun AlternatingMap.coeFun

initialize_simps_projections AlternatingMap (toFun → apply)

@[simp]
theorem toFun_eq_coe : f.toFun = f :=
  rfl
#align alternating_map.to_fun_eq_coe AlternatingMap.toFun_eq_coe

-- Porting note: changed statement to reflect new `mk` signature
@[simp]
theorem coe_mk (f : MultilinearMap R (fun _ : ι => M) N) (h) :
    ⇑(⟨f, h⟩ : AlternatingMap R M N ι) = f :=
  rfl
#align alternating_map.coe_mk AlternatingMap.coe_mkₓ

theorem congr_fun {f g : AlternatingMap R M N ι} (h : f = g) (x : ι → M) : f x = g x :=
  congr_arg (fun h : AlternatingMap R M N ι => h x) h
#align alternating_map.congr_fun AlternatingMap.congr_fun

theorem congr_arg (f : AlternatingMap R M N ι) {x y : ι → M} (h : x = y) : f x = f y :=
  _root_.congr_arg (fun x : ι → M => f x) h
#align alternating_map.congr_arg AlternatingMap.congr_arg

theorem coe_injective : Injective ((↑) : AlternatingMap R M N ι → (ι → M) → N) :=
  FunLike.coe_injective
#align alternating_map.coe_injective AlternatingMap.coe_injective

@[norm_cast] -- @[simp] -- Porting note: simp can prove this
theorem coe_inj {f g : AlternatingMap R M N ι} : (f : (ι → M) → N) = g ↔ f = g :=
  coe_injective.eq_iff
#align alternating_map.coe_inj AlternatingMap.coe_inj

@[ext]
theorem ext {f f' : AlternatingMap R M N ι} (H : ∀ x, f x = f' x) : f = f' :=
  FunLike.ext _ _ H
#align alternating_map.ext AlternatingMap.ext

theorem ext_iff {f g : AlternatingMap R M N ι} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h _ => h ▸ rfl, fun h => ext h⟩
#align alternating_map.ext_iff AlternatingMap.ext_iff

attribute [coe] AlternatingMap.toMultilinearMap

instance coe : Coe (AlternatingMap R M N ι) (MultilinearMap R (fun _ : ι => M) N) :=
  ⟨fun x => x.toMultilinearMap⟩
#align alternating_map.multilinear_map.has_coe AlternatingMap.coe

@[simp, norm_cast]
theorem coe_multilinearMap : ⇑(f : MultilinearMap R (fun _ : ι => M) N) = f :=
  rfl
#align alternating_map.coe_multilinear_map AlternatingMap.coe_multilinearMap

theorem coe_multilinearMap_injective :
    Function.Injective ((↑) : AlternatingMap R M N ι → MultilinearMap R (fun _ : ι => M) N) :=
  fun _ _ h => ext <| MultilinearMap.congr_fun h
#align alternating_map.coe_multilinear_map_injective AlternatingMap.coe_multilinearMap_injective

#noalign alternating_map.to_multilinear_map_eq_coe

-- Porting note: changed statement to reflect new `mk` signature.
-- Porting note: removed `simp`
-- @[simp]
theorem coe_multilinearMap_mk (f : (ι → M) → N) (h₁ h₂ h₃) :
    ((⟨⟨f, h₁, h₂⟩, h₃⟩ : AlternatingMap R M N ι) : MultilinearMap R (fun _ : ι => M) N) =
      ⟨f, @h₁, @h₂⟩ :=
  by simp
     -- 🎉 no goals
#align alternating_map.coe_multilinear_map_mk AlternatingMap.coe_multilinearMap_mk

end Coercions

/-!
### Simp-normal forms of the structure fields

These are expressed in terms of `⇑f` instead of `f.toFun`.
-/


@[simp]
theorem map_add [DecidableEq ι] (i : ι) (x y : M) :
    f (update v i (x + y)) = f (update v i x) + f (update v i y) :=
  f.toMultilinearMap.map_add' v i x y
#align alternating_map.map_add AlternatingMap.map_add

@[simp]
theorem map_sub [DecidableEq ι] (i : ι) (x y : M') :
    g' (update v' i (x - y)) = g' (update v' i x) - g' (update v' i y) :=
  g'.toMultilinearMap.map_sub v' i x y
#align alternating_map.map_sub AlternatingMap.map_sub

@[simp]
theorem map_neg [DecidableEq ι] (i : ι) (x : M') : g' (update v' i (-x)) = -g' (update v' i x) :=
  g'.toMultilinearMap.map_neg v' i x
#align alternating_map.map_neg AlternatingMap.map_neg

@[simp]
theorem map_smul [DecidableEq ι] (i : ι) (r : R) (x : M) :
    f (update v i (r • x)) = r • f (update v i x) :=
  f.toMultilinearMap.map_smul' v i r x
#align alternating_map.map_smul AlternatingMap.map_smul

@[simp]
theorem map_eq_zero_of_eq (v : ι → M) {i j : ι} (h : v i = v j) (hij : i ≠ j) : f v = 0 :=
  f.map_eq_zero_of_eq' v i j h hij
#align alternating_map.map_eq_zero_of_eq AlternatingMap.map_eq_zero_of_eq

theorem map_coord_zero {m : ι → M} (i : ι) (h : m i = 0) : f m = 0 :=
  f.toMultilinearMap.map_coord_zero i h
#align alternating_map.map_coord_zero AlternatingMap.map_coord_zero

@[simp]
theorem map_update_zero [DecidableEq ι] (m : ι → M) (i : ι) : f (update m i 0) = 0 :=
  f.toMultilinearMap.map_update_zero m i
#align alternating_map.map_update_zero AlternatingMap.map_update_zero

@[simp]
theorem map_zero [Nonempty ι] : f 0 = 0 :=
  f.toMultilinearMap.map_zero
#align alternating_map.map_zero AlternatingMap.map_zero

theorem map_eq_zero_of_not_injective (v : ι → M) (hv : ¬Function.Injective v) : f v = 0 := by
  rw [Function.Injective] at hv
  -- ⊢ ↑f v = 0
  push_neg at hv
  -- ⊢ ↑f v = 0
  rcases hv with ⟨i₁, i₂, heq, hne⟩
  -- ⊢ ↑f v = 0
  exact f.map_eq_zero_of_eq v heq hne
  -- 🎉 no goals
#align alternating_map.map_eq_zero_of_not_injective AlternatingMap.map_eq_zero_of_not_injective

/-!
### Algebraic structure inherited from `MultilinearMap`

`AlternatingMap` carries the same `AddCommMonoid`, `AddCommGroup`, and `Module` structure
as `MultilinearMap`
-/


section SMul

variable {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]

instance smul : SMul S (AlternatingMap R M N ι) :=
  ⟨fun c f =>
    { c • (f : MultilinearMap R (fun _ : ι => M) N) with
      map_eq_zero_of_eq' := fun v i j h hij => by simp [f.map_eq_zero_of_eq v h hij] }⟩
                                                  -- 🎉 no goals
#align alternating_map.has_smul AlternatingMap.smul

@[simp]
theorem smul_apply (c : S) (m : ι → M) : (c • f) m = c • f m :=
  rfl
#align alternating_map.smul_apply AlternatingMap.smul_apply

@[norm_cast]
theorem coe_smul (c : S) : (c • f : MultilinearMap R (fun _ : ι => M) N) =
    c • (f : MultilinearMap R (fun _ : ι => M) N) :=
  rfl
#align alternating_map.coe_smul AlternatingMap.coe_smul

theorem coeFn_smul (c : S) (f : AlternatingMap R M N ι) : ⇑(c • f) = c • ⇑f :=
  rfl
#align alternating_map.coe_fn_smul AlternatingMap.coeFn_smul

instance isCentralScalar [DistribMulAction Sᵐᵒᵖ N] [IsCentralScalar S N] :
    IsCentralScalar S (AlternatingMap R M N ι) :=
  ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩
#align alternating_map.is_central_scalar AlternatingMap.isCentralScalar

end SMul

/-- The cartesian product of two alternating maps, as an alternating map. -/
@[simps!]
def prod (f : AlternatingMap R M N ι) (g : AlternatingMap R M P ι) : AlternatingMap R M (N × P) ι :=
  { f.toMultilinearMap.prod g.toMultilinearMap with
    map_eq_zero_of_eq' := fun _ _ _ h hne =>
      Prod.ext (f.map_eq_zero_of_eq _ h hne) (g.map_eq_zero_of_eq _ h hne) }
#align alternating_map.prod AlternatingMap.prod
#align alternating_map.prod_apply AlternatingMap.prod_apply

@[simp]
theorem coe_prod (f : AlternatingMap R M N ι) (g : AlternatingMap R M P ι) :
    (f.prod g : MultilinearMap R (fun _ : ι => M) (N × P)) = MultilinearMap.prod f g :=
  rfl
#align alternating_map.coe_prod AlternatingMap.coe_prod

/-- Combine a family of alternating maps with the same domain and codomains `N i` into an
alternating map taking values in the space of functions `Π i, N i`. -/
@[simps!]
def pi {ι' : Type*} {N : ι' → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, AlternatingMap R M (N i) ι) : AlternatingMap R M (∀ i, N i) ι :=
  { MultilinearMap.pi fun a => (f a).toMultilinearMap with
    map_eq_zero_of_eq' := fun _ _ _ h hne => funext fun a => (f a).map_eq_zero_of_eq _ h hne }
#align alternating_map.pi AlternatingMap.pi
#align alternating_map.pi_apply AlternatingMap.pi_apply

@[simp]
theorem coe_pi {ι' : Type*} {N : ι' → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, AlternatingMap R M (N i) ι) :
    (pi f : MultilinearMap R (fun _ : ι => M) (∀ i, N i)) = MultilinearMap.pi fun a => f a :=
  rfl
#align alternating_map.coe_pi AlternatingMap.coe_pi

/-- Given an alternating `R`-multilinear map `f` taking values in `R`, `f.smul_right z` is the map
sending `m` to `f m • z`. -/
@[simps!]
def smulRight {R M₁ M₂ ι : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module R M₁] [Module R M₂] (f : AlternatingMap R M₁ R ι) (z : M₂) : AlternatingMap R M₁ M₂ ι :=
  { f.toMultilinearMap.smulRight z with
    map_eq_zero_of_eq' := fun v i j h hne => by simp [f.map_eq_zero_of_eq v h hne] }
                                                -- 🎉 no goals
#align alternating_map.smul_right AlternatingMap.smulRight
#align alternating_map.smul_right_apply AlternatingMap.smulRight_apply

@[simp]
theorem coe_smulRight {R M₁ M₂ ι : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module R M₁] [Module R M₂] (f : AlternatingMap R M₁ R ι) (z : M₂) :
    (f.smulRight z : MultilinearMap R (fun _ : ι => M₁) M₂) = MultilinearMap.smulRight f z :=
  rfl
#align alternating_map.coe_smul_right AlternatingMap.coe_smulRight

instance add : Add (AlternatingMap R M N ι) :=
  ⟨fun a b =>
    { (a + b : MultilinearMap R (fun _ : ι => M) N) with
      map_eq_zero_of_eq' := fun v i j h hij => by
        simp [a.map_eq_zero_of_eq v h hij, b.map_eq_zero_of_eq v h hij] }⟩
        -- 🎉 no goals
#align alternating_map.has_add AlternatingMap.add

@[simp]
theorem add_apply : (f + f') v = f v + f' v :=
  rfl
#align alternating_map.add_apply AlternatingMap.add_apply

@[norm_cast]
theorem coe_add : (↑(f + f') : MultilinearMap R (fun _ : ι => M) N) = f + f' :=
  rfl
#align alternating_map.coe_add AlternatingMap.coe_add

instance zero : Zero (AlternatingMap R M N ι) :=
  ⟨{ (0 : MultilinearMap R (fun _ : ι => M) N) with
      map_eq_zero_of_eq' := fun v i j _ _ => by simp }⟩
                                                -- 🎉 no goals
#align alternating_map.has_zero AlternatingMap.zero

@[simp]
theorem zero_apply : (0 : AlternatingMap R M N ι) v = 0 :=
  rfl
#align alternating_map.zero_apply AlternatingMap.zero_apply

@[norm_cast]
theorem coe_zero : ((0 : AlternatingMap R M N ι) : MultilinearMap R (fun _ : ι => M) N) = 0 :=
  rfl
#align alternating_map.coe_zero AlternatingMap.coe_zero

@[simp]
theorem mk_zero :
    mk (0 : MultilinearMap R (fun _ : ι ↦ M) N) (0 : AlternatingMap R M N ι).2 = 0 :=
  rfl

instance inhabited : Inhabited (AlternatingMap R M N ι) :=
  ⟨0⟩
#align alternating_map.inhabited AlternatingMap.inhabited

instance addCommMonoid : AddCommMonoid (AlternatingMap R M N ι) :=
  coe_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => coeFn_smul _ _
#align alternating_map.add_comm_monoid AlternatingMap.addCommMonoid

instance neg : Neg (AlternatingMap R M N' ι) :=
  ⟨fun f =>
    { -(f : MultilinearMap R (fun _ : ι => M) N') with
      map_eq_zero_of_eq' := fun v i j h hij => by simp [f.map_eq_zero_of_eq v h hij] }⟩
                                                  -- 🎉 no goals
#align alternating_map.has_neg AlternatingMap.neg

@[simp]
theorem neg_apply (m : ι → M) : (-g) m = -g m :=
  rfl
#align alternating_map.neg_apply AlternatingMap.neg_apply

@[norm_cast]
theorem coe_neg : ((-g : AlternatingMap R M N' ι) : MultilinearMap R (fun _ : ι => M) N') = -g :=
  rfl
#align alternating_map.coe_neg AlternatingMap.coe_neg

instance sub : Sub (AlternatingMap R M N' ι) :=
  ⟨fun f g =>
    { (f - g : MultilinearMap R (fun _ : ι => M) N') with
      map_eq_zero_of_eq' := fun v i j h hij => by
        simp [f.map_eq_zero_of_eq v h hij, g.map_eq_zero_of_eq v h hij] }⟩
        -- 🎉 no goals
#align alternating_map.has_sub AlternatingMap.sub

@[simp]
theorem sub_apply (m : ι → M) : (g - g₂) m = g m - g₂ m :=
  rfl
#align alternating_map.sub_apply AlternatingMap.sub_apply

@[norm_cast]
theorem coe_sub : (↑(g - g₂) : MultilinearMap R (fun _ : ι => M) N') = g - g₂ :=
  rfl
#align alternating_map.coe_sub AlternatingMap.coe_sub

instance addCommGroup : AddCommGroup (AlternatingMap R M N' ι) :=
  coe_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => coeFn_smul _ _) fun _ _ => coeFn_smul _ _
#align alternating_map.add_comm_group AlternatingMap.addCommGroup
section DistribMulAction

variable {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]

instance distribMulAction : DistribMulAction S (AlternatingMap R M N ι) where
  one_smul _ := ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _
  smul_zero _ := ext fun _ => smul_zero _
  smul_add _ _ _ := ext fun _ => smul_add _ _ _
#align alternating_map.distrib_mul_action AlternatingMap.distribMulAction

end DistribMulAction

section Module

variable {S : Type*} [Semiring S] [Module S N] [SMulCommClass R S N]

/-- The space of multilinear maps over an algebra over `R` is a module over `R`, for the pointwise
addition and scalar multiplication. -/
instance module : Module S (AlternatingMap R M N ι) where
  add_smul _ _ _ := ext fun _ => add_smul _ _ _
  zero_smul _ := ext fun _ => zero_smul _ _
#align alternating_map.module AlternatingMap.module

instance noZeroSMulDivisors [NoZeroSMulDivisors S N] :
    NoZeroSMulDivisors S (AlternatingMap R M N ι) :=
  coe_injective.noZeroSMulDivisors _ rfl coeFn_smul
#align alternating_map.no_zero_smul_divisors AlternatingMap.noZeroSMulDivisors

end Module

section

variable (R M)

/-- The evaluation map from `ι → M` to `M` at a given `i` is alternating when `ι` is subsingleton.
-/
@[simps]
def ofSubsingleton [Subsingleton ι] (i : ι) : AlternatingMap R M M ι :=
  { MultilinearMap.ofSubsingleton R M i with
    toFun := Function.eval i
    map_eq_zero_of_eq' := fun _ _ _ _ hij => (hij <| Subsingleton.elim _ _).elim }
#align alternating_map.of_subsingleton AlternatingMap.ofSubsingleton
#align alternating_map.of_subsingleton_apply AlternatingMap.ofSubsingleton_apply

variable (ι)

/-- The constant map is alternating when `ι` is empty. -/
@[simps (config := { fullyApplied := false })]
def constOfIsEmpty [IsEmpty ι] (m : N) : AlternatingMap R M N ι :=
  { MultilinearMap.constOfIsEmpty R _ m with
    toFun := Function.const _ m
    map_eq_zero_of_eq' := fun _ => isEmptyElim }
#align alternating_map.const_of_is_empty AlternatingMap.constOfIsEmpty
#align alternating_map.const_of_is_empty_apply AlternatingMap.constOfIsEmpty_apply

end

/-- Restrict the codomain of an alternating map to a submodule. -/
@[simps]
def codRestrict (f : AlternatingMap R M N ι) (p : Submodule R N) (h : ∀ v, f v ∈ p) :
    AlternatingMap R M p ι :=
  { f.toMultilinearMap.codRestrict p h with
    toFun := fun v => ⟨f v, h v⟩
    map_eq_zero_of_eq' := fun _ _ _ hv hij => Subtype.ext <| map_eq_zero_of_eq _ _ hv hij }
#align alternating_map.cod_restrict AlternatingMap.codRestrict
#align alternating_map.cod_restrict_apply_coe AlternatingMap.codRestrict_apply_coe

end AlternatingMap

/-!
### Composition with linear maps
-/


namespace LinearMap

variable {N₂ : Type*} [AddCommMonoid N₂] [Module R N₂]

/-- Composing an alternating map with a linear map on the left gives again an alternating map. -/
def compAlternatingMap (g : N →ₗ[R] N₂) : AlternatingMap R M N ι →+ AlternatingMap R M N₂ ι where
  toFun f :=
    { g.compMultilinearMap (f : MultilinearMap R (fun _ : ι => M) N) with
      map_eq_zero_of_eq' := fun v i j h hij => by simp [f.map_eq_zero_of_eq v h hij] }
                                                  -- 🎉 no goals
  map_zero' := by
    ext
    -- ⊢ ↑((fun f =>
    simp
    -- 🎉 no goals
  map_add' a b := by
    ext
    -- ⊢ ↑(ZeroHom.toFun
    simp
    -- 🎉 no goals
#align linear_map.comp_alternating_map LinearMap.compAlternatingMap

@[simp]
theorem coe_compAlternatingMap (g : N →ₗ[R] N₂) (f : AlternatingMap R M N ι) :
    ⇑(g.compAlternatingMap f) = g ∘ f :=
  rfl
#align linear_map.coe_comp_alternating_map LinearMap.coe_compAlternatingMap

@[simp]
theorem compAlternatingMap_apply (g : N →ₗ[R] N₂) (f : AlternatingMap R M N ι) (m : ι → M) :
    g.compAlternatingMap f m = g (f m) :=
  rfl
#align linear_map.comp_alternating_map_apply LinearMap.compAlternatingMap_apply

theorem smulRight_eq_comp {R M₁ M₂ ι : Type*} [CommSemiring R] [AddCommMonoid M₁]
    [AddCommMonoid M₂] [Module R M₁] [Module R M₂] (f : AlternatingMap R M₁ R ι) (z : M₂) :
    f.smulRight z = (LinearMap.id.smulRight z).compAlternatingMap f :=
  rfl
#align linear_map.smul_right_eq_comp LinearMap.smulRight_eq_comp

@[simp]
theorem subtype_compAlternatingMap_codRestrict (f : AlternatingMap R M N ι) (p : Submodule R N)
    (h) : p.subtype.compAlternatingMap (f.codRestrict p h) = f :=
  AlternatingMap.ext fun _ => rfl
#align linear_map.subtype_comp_alternating_map_cod_restrict LinearMap.subtype_compAlternatingMap_codRestrict

@[simp]
theorem compAlternatingMap_codRestrict (g : N →ₗ[R] N₂) (f : AlternatingMap R M N ι)
    (p : Submodule R N₂) (h) :
    (g.codRestrict p h).compAlternatingMap f =
      (g.compAlternatingMap f).codRestrict p fun v => h (f v) :=
  AlternatingMap.ext fun _ => rfl
#align linear_map.comp_alternating_map_cod_restrict LinearMap.compAlternatingMap_codRestrict

end LinearMap

namespace AlternatingMap

variable {M₂ : Type*} [AddCommMonoid M₂] [Module R M₂]

variable {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃]

/-- Composing an alternating map with the same linear map on each argument gives again an
alternating map. -/
def compLinearMap (f : AlternatingMap R M N ι) (g : M₂ →ₗ[R] M) : AlternatingMap R M₂ N ι :=
  { (f : MultilinearMap R (fun _ : ι => M) N).compLinearMap fun _ => g with
    map_eq_zero_of_eq' := fun _ _ _ h hij => f.map_eq_zero_of_eq _ (LinearMap.congr_arg h) hij }
#align alternating_map.comp_linear_map AlternatingMap.compLinearMap

theorem coe_compLinearMap (f : AlternatingMap R M N ι) (g : M₂ →ₗ[R] M) :
    ⇑(f.compLinearMap g) = f ∘ (· ∘ ·) g :=
  rfl
#align alternating_map.coe_comp_linear_map AlternatingMap.coe_compLinearMap

@[simp]
theorem compLinearMap_apply (f : AlternatingMap R M N ι) (g : M₂ →ₗ[R] M) (v : ι → M₂) :
    f.compLinearMap g v = f fun i => g (v i) :=
  rfl
#align alternating_map.comp_linear_map_apply AlternatingMap.compLinearMap_apply

/-- Composing an alternating map twice with the same linear map in each argument is
the same as composing with their composition. -/
theorem compLinearMap_assoc (f : AlternatingMap R M N ι) (g₁ : M₂ →ₗ[R] M) (g₂ : M₃ →ₗ[R] M₂) :
    (f.compLinearMap g₁).compLinearMap g₂ = f.compLinearMap (g₁ ∘ₗ g₂) :=
  rfl
#align alternating_map.comp_linear_map_assoc AlternatingMap.compLinearMap_assoc

@[simp]
theorem zero_compLinearMap (g : M₂ →ₗ[R] M) : (0 : AlternatingMap R M N ι).compLinearMap g = 0 := by
  ext
  -- ⊢ ↑(compLinearMap 0 g) x✝ = ↑0 x✝
  simp only [compLinearMap_apply, zero_apply]
  -- 🎉 no goals
#align alternating_map.zero_comp_linear_map AlternatingMap.zero_compLinearMap

@[simp]
theorem add_compLinearMap (f₁ f₂ : AlternatingMap R M N ι) (g : M₂ →ₗ[R] M) :
    (f₁ + f₂).compLinearMap g = f₁.compLinearMap g + f₂.compLinearMap g := by
  ext
  -- ⊢ ↑(compLinearMap (f₁ + f₂) g) x✝ = ↑(compLinearMap f₁ g + compLinearMap f₂ g) …
  simp only [compLinearMap_apply, add_apply]
  -- 🎉 no goals
#align alternating_map.add_comp_linear_map AlternatingMap.add_compLinearMap

@[simp]
theorem compLinearMap_zero [Nonempty ι] (f : AlternatingMap R M N ι) :
    f.compLinearMap (0 : M₂ →ₗ[R] M) = 0 := by
  ext
  -- ⊢ ↑(compLinearMap f 0) x✝ = ↑0 x✝
  -- Porting note: Was `simp_rw [.., ← Pi.zero_def, map_zero, zero_apply]`.
  simp_rw [compLinearMap_apply, LinearMap.zero_apply, ← Pi.zero_def, zero_apply]
  -- ⊢ ↑f 0 = 0
  exact map_zero f
  -- 🎉 no goals
#align alternating_map.comp_linear_map_zero AlternatingMap.compLinearMap_zero

/-- Composing an alternating map with the identity linear map in each argument. -/
@[simp]
theorem compLinearMap_id (f : AlternatingMap R M N ι) : f.compLinearMap LinearMap.id = f :=
  ext fun _ => rfl
#align alternating_map.comp_linear_map_id AlternatingMap.compLinearMap_id

/-- Composing with a surjective linear map is injective. -/
theorem compLinearMap_injective (f : M₂ →ₗ[R] M) (hf : Function.Surjective f) :
    Function.Injective fun g : AlternatingMap R M N ι => g.compLinearMap f := fun g₁ g₂ h =>
  ext fun x => by simpa [Function.surjInv_eq hf] using ext_iff.mp h (Function.surjInv hf ∘ x)
                  -- 🎉 no goals
#align alternating_map.comp_linear_map_injective AlternatingMap.compLinearMap_injective

theorem compLinearMap_inj (f : M₂ →ₗ[R] M) (hf : Function.Surjective f)
    (g₁ g₂ : AlternatingMap R M N ι) : g₁.compLinearMap f = g₂.compLinearMap f ↔ g₁ = g₂ :=
  (compLinearMap_injective _ hf).eq_iff
#align alternating_map.comp_linear_map_inj AlternatingMap.compLinearMap_inj

section DomLcongr

variable (ι R N)
variable (S : Type*) [Semiring S] [Module S N] [SMulCommClass R S N]

/-- Construct a linear equivalence between maps from a linear equivalence between domains. -/
@[simps apply]
def domLCongr (e : M ≃ₗ[R] M₂) : AlternatingMap R M N ι ≃ₗ[S] AlternatingMap R M₂ N ι where
  toFun f := f.compLinearMap e.symm
  invFun g := g.compLinearMap e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := AlternatingMap.ext fun _ => f.congr_arg <| funext fun _ => e.symm_apply_apply _
  right_inv f := AlternatingMap.ext fun _ => f.congr_arg <| funext fun _ => e.apply_symm_apply _
#align alternating_map.dom_lcongr AlternatingMap.domLCongr
#align alternating_map.dom_lcongr_apply AlternatingMap.domLCongr_apply

@[simp]
theorem domLCongr_refl : domLCongr R N ι S (LinearEquiv.refl R M) = LinearEquiv.refl S _ :=
  LinearEquiv.ext fun _ => AlternatingMap.ext fun _ => rfl
#align alternating_map.dom_lcongr_refl AlternatingMap.domLCongr_refl

@[simp]
theorem domLCongr_symm (e : M ≃ₗ[R] M₂) : (domLCongr R N ι S e).symm = domLCongr R N ι S e.symm :=
  rfl
#align alternating_map.dom_lcongr_symm AlternatingMap.domLCongr_symm

theorem domLCongr_trans (e : M ≃ₗ[R] M₂) (f : M₂ ≃ₗ[R] M₃) :
    (domLCongr R N ι S e).trans (domLCongr R N ι S f) = domLCongr R N ι S (e.trans f) :=
  rfl
#align alternating_map.dom_lcongr_trans AlternatingMap.domLCongr_trans

end DomLcongr

/-- Composing an alternating map with the same linear equiv on each argument gives the zero map
if and only if the alternating map is the zero map. -/
@[simp]
theorem compLinearEquiv_eq_zero_iff (f : AlternatingMap R M N ι) (g : M₂ ≃ₗ[R] M) :
    f.compLinearMap (g : M₂ →ₗ[R] M) = 0 ↔ f = 0 :=
  (domLCongr R N ι ℕ g.symm).map_eq_zero_iff
#align alternating_map.comp_linear_equiv_eq_zero_iff AlternatingMap.compLinearEquiv_eq_zero_iff

variable (f f' : AlternatingMap R M N ι)

variable (g g₂ : AlternatingMap R M N' ι)

variable (g' : AlternatingMap R M' N' ι)

variable (v : ι → M) (v' : ι → M')

open Function

/-!
### Other lemmas from `MultilinearMap`
-/


section

open BigOperators

theorem map_update_sum {α : Type*} [DecidableEq ι] (t : Finset α) (i : ι) (g : α → M) (m : ι → M) :
    f (update m i (∑ a in t, g a)) = ∑ a in t, f (update m i (g a)) :=
  f.toMultilinearMap.map_update_sum t i g m
#align alternating_map.map_update_sum AlternatingMap.map_update_sum

end

/-!
### Theorems specific to alternating maps

Various properties of reordered and repeated inputs which follow from
`AlternatingMap.map_eq_zero_of_eq`.
-/


theorem map_update_self [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    f (Function.update v i (v j)) = 0 :=
  f.map_eq_zero_of_eq _ (by rw [Function.update_same, Function.update_noteq hij.symm]) hij
                            -- 🎉 no goals
#align alternating_map.map_update_self AlternatingMap.map_update_self

theorem map_update_update [DecidableEq ι] {i j : ι} (hij : i ≠ j) (m : M) :
    f (Function.update (Function.update v i m) j m) = 0 :=
  f.map_eq_zero_of_eq _
    (by rw [Function.update_same, Function.update_noteq hij, Function.update_same]) hij
        -- 🎉 no goals
#align alternating_map.map_update_update AlternatingMap.map_update_update

theorem map_swap_add [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    f (v ∘ Equiv.swap i j) + f v = 0 := by
  rw [Equiv.comp_swap_eq_update]
  -- ⊢ ↑f (update (update v j (v i)) i (v j)) + ↑f v = 0
  convert f.map_update_update v hij (v i + v j)
  -- ⊢ ↑f (update (update v j (v i)) i (v j)) + ↑f v = ↑f (update (update v i (v i  …
  simp [f.map_update_self _ hij, f.map_update_self _ hij.symm,
    Function.update_comm hij (v i + v j) (v _) v, Function.update_comm hij.symm (v i) (v i) v]
#align alternating_map.map_swap_add AlternatingMap.map_swap_add

theorem map_add_swap [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    f v + f (v ∘ Equiv.swap i j) = 0 := by
  rw [add_comm]
  -- ⊢ ↑f (v ∘ ↑(Equiv.swap i j)) + ↑f v = 0
  exact f.map_swap_add v hij
  -- 🎉 no goals
#align alternating_map.map_add_swap AlternatingMap.map_add_swap

theorem map_swap [DecidableEq ι] {i j : ι} (hij : i ≠ j) : g (v ∘ Equiv.swap i j) = -g v :=
  eq_neg_of_add_eq_zero_left <| g.map_swap_add v hij
#align alternating_map.map_swap AlternatingMap.map_swap

theorem map_perm [DecidableEq ι] [Fintype ι] (v : ι → M) (σ : Equiv.Perm ι) :
    g (v ∘ σ) = Equiv.Perm.sign σ • g v := by
  -- Porting note: `apply` → `induction'`
  induction' σ using Equiv.Perm.swap_induction_on' with s x y hxy hI
  -- ⊢ ↑g (v ∘ ↑1) = ↑Equiv.Perm.sign 1 • ↑g v
  · simp
    -- 🎉 no goals
  · -- Porting note: `← Function.comp.assoc` & `-Equiv.Perm.sign_swap'` are required.
    simpa [← Function.comp.assoc, g.map_swap (v ∘ s) hxy,
      Equiv.Perm.sign_swap hxy, -Equiv.Perm.sign_swap'] using hI
#align alternating_map.map_perm AlternatingMap.map_perm

theorem map_congr_perm [DecidableEq ι] [Fintype ι] (σ : Equiv.Perm ι) :
    g v = Equiv.Perm.sign σ • g (v ∘ σ) := by
  rw [g.map_perm, smul_smul]
  -- ⊢ ↑g v = (↑Equiv.Perm.sign σ * ↑Equiv.Perm.sign σ) • ↑g v
  simp
  -- 🎉 no goals
#align alternating_map.map_congr_perm AlternatingMap.map_congr_perm

section DomDomCongr

/-- Transfer the arguments to a map along an equivalence between argument indices.

This is the alternating version of `MultilinearMap.domDomCongr`. -/
@[simps]
def domDomCongr (σ : ι ≃ ι') (f : AlternatingMap R M N ι) : AlternatingMap R M N ι' :=
  { f.toMultilinearMap.domDomCongr σ with
    toFun := fun v => f (v ∘ σ)
    map_eq_zero_of_eq' := fun v i j hv hij =>
      f.map_eq_zero_of_eq (v ∘ σ) (i := σ.symm i) (j := σ.symm j)
        (by simpa using hv) (σ.symm.injective.ne hij) }
            -- 🎉 no goals
#align alternating_map.dom_dom_congr AlternatingMap.domDomCongr
#align alternating_map.dom_dom_congr_apply AlternatingMap.domDomCongr_apply

@[simp]
theorem domDomCongr_refl (f : AlternatingMap R M N ι) : f.domDomCongr (Equiv.refl ι) = f :=
  ext fun _ => rfl
#align alternating_map.dom_dom_congr_refl AlternatingMap.domDomCongr_refl

theorem domDomCongr_trans (σ₁ : ι ≃ ι') (σ₂ : ι' ≃ ι'') (f : AlternatingMap R M N ι) :
    f.domDomCongr (σ₁.trans σ₂) = (f.domDomCongr σ₁).domDomCongr σ₂ :=
  rfl
#align alternating_map.dom_dom_congr_trans AlternatingMap.domDomCongr_trans

@[simp]
theorem domDomCongr_zero (σ : ι ≃ ι') : (0 : AlternatingMap R M N ι).domDomCongr σ = 0 :=
  rfl
#align alternating_map.dom_dom_congr_zero AlternatingMap.domDomCongr_zero

@[simp]
theorem domDomCongr_add (σ : ι ≃ ι') (f g : AlternatingMap R M N ι) :
    (f + g).domDomCongr σ = f.domDomCongr σ + g.domDomCongr σ :=
  rfl
#align alternating_map.dom_dom_congr_add AlternatingMap.domDomCongr_add

/-- `AlternatingMap.domDomCongr` as an equivalence.

This is declared separately because it does not work with dot notation. -/
@[simps apply symm_apply]
def domDomCongrEquiv (σ : ι ≃ ι') : AlternatingMap R M N ι ≃+ AlternatingMap R M N ι' where
  toFun := domDomCongr σ
  invFun := domDomCongr σ.symm
  left_inv f := by
    ext
    -- ⊢ ↑(domDomCongr σ.symm (domDomCongr σ f)) x✝ = ↑f x✝
    simp [Function.comp]
    -- 🎉 no goals
  right_inv m := by
    ext
    -- ⊢ ↑(domDomCongr σ (domDomCongr σ.symm m)) x✝ = ↑m x✝
    simp [Function.comp]
    -- 🎉 no goals
  map_add' := domDomCongr_add σ
#align alternating_map.dom_dom_congr_equiv AlternatingMap.domDomCongrEquiv
#align alternating_map.dom_dom_congr_equiv_apply AlternatingMap.domDomCongrEquiv_apply
#align alternating_map.dom_dom_congr_equiv_symm_apply AlternatingMap.domDomCongrEquiv_symm_apply

/-- The results of applying `domDomCongr` to two maps are equal if and only if those maps are. -/
@[simp]
theorem domDomCongr_eq_iff (σ : ι ≃ ι') (f g : AlternatingMap R M N ι) :
    f.domDomCongr σ = g.domDomCongr σ ↔ f = g :=
  (domDomCongrEquiv σ : _ ≃+ AlternatingMap R M N ι').apply_eq_iff_eq
#align alternating_map.dom_dom_congr_eq_iff AlternatingMap.domDomCongr_eq_iff

@[simp]
theorem domDomCongr_eq_zero_iff (σ : ι ≃ ι') (f : AlternatingMap R M N ι) :
    f.domDomCongr σ = 0 ↔ f = 0 :=
  (domDomCongrEquiv σ : AlternatingMap R M N ι ≃+ AlternatingMap R M N ι').map_eq_zero_iff
#align alternating_map.dom_dom_congr_eq_zero_iff AlternatingMap.domDomCongr_eq_zero_iff

theorem domDomCongr_perm [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) :
    g.domDomCongr σ = Equiv.Perm.sign σ • g :=
  AlternatingMap.ext fun v => g.map_perm v σ
#align alternating_map.dom_dom_congr_perm AlternatingMap.domDomCongr_perm

@[norm_cast]
theorem coe_domDomCongr (σ : ι ≃ ι') :
    ↑(f.domDomCongr σ) = (f : MultilinearMap R (fun _ : ι => M) N).domDomCongr σ :=
  MultilinearMap.ext fun _ => rfl
#align alternating_map.coe_dom_dom_congr AlternatingMap.coe_domDomCongr

end DomDomCongr

/-- If the arguments are linearly dependent then the result is `0`. -/
theorem map_linearDependent {K : Type*} [Ring K] {M : Type*} [AddCommGroup M] [Module K M]
    {N : Type*} [AddCommGroup N] [Module K N] [NoZeroSMulDivisors K N] (f : AlternatingMap K M N ι)
    (v : ι → M) (h : ¬LinearIndependent K v) : f v = 0 := by
  obtain ⟨s, g, h, i, hi, hz⟩ := not_linearIndependent_iff.mp h
  -- ⊢ ↑f v = 0
  letI := Classical.decEq ι
  -- ⊢ ↑f v = 0
  suffices f (update v i (g i • v i)) = 0 by
    rw [f.map_smul, Function.update_eq_self, smul_eq_zero] at this
    exact Or.resolve_left this hz
  -- Porting note: Was `conv at h in .. => ..`.
  rw [← (funext fun x => ite_self (c := i = x) (d := Classical.decEq ι i x) (g x • v x))] at h
  -- ⊢ ↑f (update v i (g i • v i)) = 0
  rw [Finset.sum_ite, Finset.filter_eq, Finset.filter_ne, if_pos hi, Finset.sum_singleton,
    add_eq_zero_iff_eq_neg] at h
  rw [h, f.map_neg, f.map_update_sum, neg_eq_zero]; apply Finset.sum_eq_zero
  -- ⊢ (Finset.sum (Finset.erase s i) fun a => ↑f (update v i (g a • v a))) = 0
                                                    -- ⊢ ∀ (x : ι), x ∈ Finset.erase s i → ↑f (update v i (g x • v x)) = 0
  intro j hj
  -- ⊢ ↑f (update v i (g j • v j)) = 0
  obtain ⟨hij, _⟩ := Finset.mem_erase.mp hj
  -- ⊢ ↑f (update v i (g j • v j)) = 0
  rw [f.map_smul, f.map_update_self _ hij.symm, smul_zero]
  -- 🎉 no goals
#align alternating_map.map_linear_dependent AlternatingMap.map_linearDependent

section Fin

open Fin

/-- A version of `MultilinearMap.cons_add` for `AlternatingMap`. -/
theorem map_vecCons_add {n : ℕ} (f : AlternatingMap R M N (Fin n.succ)) (m : Fin n → M) (x y : M) :
    f (Matrix.vecCons (x + y) m) = f (Matrix.vecCons x m) + f (Matrix.vecCons y m) :=
  f.toMultilinearMap.cons_add _ _ _
#align alternating_map.map_vec_cons_add AlternatingMap.map_vecCons_add

/-- A version of `MultilinearMap.cons_smul` for `AlternatingMap`. -/
theorem map_vecCons_smul {n : ℕ} (f : AlternatingMap R M N (Fin n.succ)) (m : Fin n → M) (c : R)
    (x : M) : f (Matrix.vecCons (c • x) m) = c • f (Matrix.vecCons x m) :=
  f.toMultilinearMap.cons_smul _ _ _
#align alternating_map.map_vec_cons_smul AlternatingMap.map_vecCons_smul

end Fin

end AlternatingMap

open BigOperators

namespace MultilinearMap

open Equiv

variable [Fintype ι] [DecidableEq ι]

private theorem alternization_map_eq_zero_of_eq_aux (m : MultilinearMap R (fun _ : ι => M) N')
    (v : ι → M) (i j : ι) (i_ne_j : i ≠ j) (hv : v i = v j) :
    (∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ) v = 0 := by
  rw [sum_apply]
  -- ⊢ ∑ a : Perm ι, ↑(↑Perm.sign a • domDomCongr a m) v = 0
  exact
    Finset.sum_involution (fun σ _ => swap i j * σ)
      -- Porting note: `-Equiv.Perm.sign_swap'` is required.
      (fun σ _ => by simp [Perm.sign_swap i_ne_j, apply_swap_eq_self hv, -Equiv.Perm.sign_swap'])
      (fun σ _ _ => (not_congr swap_mul_eq_iff).mpr i_ne_j) (fun σ _ => Finset.mem_univ _)
      fun σ _ => swap_mul_involutive i j σ

/-- Produce an `AlternatingMap` out of a `MultilinearMap`, by summing over all argument
permutations. -/
def alternatization : MultilinearMap R (fun _ : ι => M) N' →+ AlternatingMap R M N' ι where
  toFun m :=
    { ∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ with
      toFun := ⇑(∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ)
      map_eq_zero_of_eq' := fun v i j hvij hij =>
        alternization_map_eq_zero_of_eq_aux m v i j hij hvij }
  map_add' a b := by
    ext
    -- ⊢ ↑(ZeroHom.toFun
    simp only [mk_coe, AlternatingMap.coe_mk, sum_apply, smul_apply, domDomCongr_apply, add_apply,
      smul_add, Finset.sum_add_distrib, AlternatingMap.add_apply]
  map_zero' := by
    -- ⊢ ↑((fun m =>
    ext
    simp only [mk_coe, AlternatingMap.coe_mk, sum_apply, smul_apply, domDomCongr_apply,
      zero_apply, smul_zero, Finset.sum_const_zero, AlternatingMap.zero_apply]
#align multilinear_map.alternatization MultilinearMap.alternatization

theorem alternatization_def (m : MultilinearMap R (fun _ : ι => M) N') :
    ⇑(alternatization m) = (∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ : _) :=
  rfl
#align multilinear_map.alternatization_def MultilinearMap.alternatization_def

theorem alternatization_coe (m : MultilinearMap R (fun _ : ι => M) N') :
    ↑(alternatization m) = (∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ : _) :=
  coe_injective rfl
#align multilinear_map.alternatization_coe MultilinearMap.alternatization_coe

theorem alternatization_apply (m : MultilinearMap R (fun _ : ι => M) N') (v : ι → M) :
    alternatization m v = ∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ v := by
  simp only [alternatization_def, smul_apply, sum_apply]
  -- 🎉 no goals
#align multilinear_map.alternatization_apply MultilinearMap.alternatization_apply

end MultilinearMap

namespace AlternatingMap

/-- Alternatizing a multilinear map that is already alternating results in a scale factor of `n!`,
where `n` is the number of inputs. -/
theorem coe_alternatization [DecidableEq ι] [Fintype ι] (a : AlternatingMap R M N' ι) :
    MultilinearMap.alternatization (a : MultilinearMap R (fun _ => M) N')
    = Nat.factorial (Fintype.card ι) • a := by
  apply AlternatingMap.coe_injective
  -- ⊢ ↑(↑MultilinearMap.alternatization ↑a) = ↑(Nat.factorial (Fintype.card ι) • a)
  simp_rw [MultilinearMap.alternatization_def, ← coe_domDomCongr, domDomCongr_perm, coe_smul,
    smul_smul, Int.units_mul_self, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    ← coe_multilinearMap, coe_smul]
#align alternating_map.coe_alternatization AlternatingMap.coe_alternatization

end AlternatingMap

namespace LinearMap

variable {N'₂ : Type*} [AddCommGroup N'₂] [Module R N'₂] [DecidableEq ι] [Fintype ι]

/-- Composition with a linear map before and after alternatization are equivalent. -/
theorem compMultilinearMap_alternatization (g : N' →ₗ[R] N'₂)
    (f : MultilinearMap R (fun _ : ι => M) N') :
    MultilinearMap.alternatization (g.compMultilinearMap f)
      = g.compAlternatingMap (MultilinearMap.alternatization f) := by
  ext
  -- ⊢ ↑(↑MultilinearMap.alternatization (compMultilinearMap g f)) x✝ = ↑(↑(compAlt …
  simp [MultilinearMap.alternatization_def]
  -- 🎉 no goals
#align linear_map.comp_multilinear_map_alternatization LinearMap.compMultilinearMap_alternatization

end LinearMap

section Coprod

open BigOperators

open TensorProduct

variable {ιa ιb : Type*} [Fintype ιa] [Fintype ιb]

variable {R' : Type*} {Mᵢ N₁ N₂ : Type*} [CommSemiring R'] [AddCommGroup N₁] [Module R' N₁]
  [AddCommGroup N₂] [Module R' N₂] [AddCommMonoid Mᵢ] [Module R' Mᵢ]

namespace Equiv.Perm

/-- Elements which are considered equivalent if they differ only by swaps within α or β  -/
abbrev ModSumCongr (α β : Type*) :=
  _ ⧸ (Equiv.Perm.sumCongrHom α β).range
#align equiv.perm.mod_sum_congr Equiv.Perm.ModSumCongr

theorem ModSumCongr.swap_smul_involutive {α β : Type*} [DecidableEq (Sum α β)] (i j : Sum α β) :
    Function.Involutive (SMul.smul (Equiv.swap i j) : ModSumCongr α β → ModSumCongr α β) :=
  fun σ => by
    refine Quotient.inductionOn' σ fun σ => ?_
    -- ⊢ SMul.smul (swap i j) (SMul.smul (swap i j) (Quotient.mk'' σ)) = Quotient.mk' …
    exact _root_.congr_arg Quotient.mk'' (Equiv.swap_mul_involutive i j σ)
    -- 🎉 no goals
#align equiv.perm.mod_sum_congr.swap_smul_involutive Equiv.Perm.ModSumCongr.swap_smul_involutive

end Equiv.Perm

namespace AlternatingMap

open Equiv

variable [DecidableEq ιa] [DecidableEq ιb]

/-- summand used in `AlternatingMap.domCoprod` -/
def domCoprod.summand (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb)
    (σ : Perm.ModSumCongr ιa ιb) : MultilinearMap R' (fun _ : Sum ιa ιb => Mᵢ) (N₁ ⊗[R'] N₂) :=
  Quotient.liftOn' σ
    (fun σ =>
      Equiv.Perm.sign σ •
        (MultilinearMap.domCoprod ↑a ↑b : MultilinearMap R' (fun _ => Mᵢ) (N₁ ⊗ N₂)).domDomCongr σ)
    fun σ₁ σ₂ H => by
    rw [QuotientGroup.leftRel_apply] at H
    -- ⊢ (fun σ => ↑Perm.sign σ • MultilinearMap.domDomCongr σ (MultilinearMap.domCop …
    obtain ⟨⟨sl, sr⟩, h⟩ := H
    -- ⊢ (fun σ => ↑Perm.sign σ • MultilinearMap.domDomCongr σ (MultilinearMap.domCop …
    ext v
    -- ⊢ ↑((fun σ => ↑Perm.sign σ • MultilinearMap.domDomCongr σ (MultilinearMap.domC …
    simp only [MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
      coe_multilinearMap, MultilinearMap.smul_apply]
    replace h := inv_mul_eq_iff_eq_mul.mp h.symm
    -- ⊢ (↑Perm.sign σ₁ • (↑a fun i => v (↑σ₁ (Sum.inl i))) ⊗ₜ[R'] ↑b fun i => v (↑σ₁ …
    have : Equiv.Perm.sign (σ₁ * Perm.sumCongrHom _ _ (sl, sr))
      = Equiv.Perm.sign σ₁ * (Equiv.Perm.sign sl * Equiv.Perm.sign sr) := by simp
    rw [h, this, mul_smul, mul_smul, smul_left_cancel_iff, ← TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
    simp only [Sum.map_inr, Perm.sumCongrHom_apply, Perm.sumCongr_apply, Sum.map_inl,
      Function.comp_apply, Perm.coe_mul]
    -- Porting note: Was `rw`.
    erw [← a.map_congr_perm fun i => v (σ₁ _), ← b.map_congr_perm fun i => v (σ₁ _)]
    -- 🎉 no goals
#align alternating_map.dom_coprod.summand AlternatingMap.domCoprod.summand

theorem domCoprod.summand_mk'' (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb)
    (σ : Equiv.Perm (Sum ιa ιb)) :
    domCoprod.summand a b (Quotient.mk'' σ) =
      Equiv.Perm.sign σ •
        (MultilinearMap.domCoprod ↑a ↑b : MultilinearMap R' (fun _ => Mᵢ) (N₁ ⊗ N₂)).domDomCongr
          σ :=
  rfl
#align alternating_map.dom_coprod.summand_mk' AlternatingMap.domCoprod.summand_mk''

/-- Swapping elements in `σ` with equal values in `v` results in an addition that cancels -/
theorem domCoprod.summand_add_swap_smul_eq_zero (a : AlternatingMap R' Mᵢ N₁ ιa)
    (b : AlternatingMap R' Mᵢ N₂ ιb) (σ : Perm.ModSumCongr ιa ιb) {v : Sum ιa ιb → Mᵢ}
    {i j : Sum ιa ιb} (hv : v i = v j) (hij : i ≠ j) :
    domCoprod.summand a b σ v + domCoprod.summand a b (swap i j • σ) v = 0 := by
  refine Quotient.inductionOn' σ fun σ => ?_
  -- ⊢ ↑(summand a b (Quotient.mk'' σ)) v + ↑(summand a b (swap i j • Quotient.mk'' …
  dsimp only [Quotient.liftOn'_mk'', Quotient.map'_mk'', MulAction.Quotient.smul_mk,
    domCoprod.summand]
  rw [smul_eq_mul, Perm.sign_mul, Perm.sign_swap hij]
  -- ⊢ ↑(↑Perm.sign σ • MultilinearMap.domDomCongr σ (MultilinearMap.domCoprod ↑a ↑ …
  simp only [one_mul, neg_mul, Function.comp_apply, Units.neg_smul, Perm.coe_mul, Units.val_neg,
    MultilinearMap.smul_apply, MultilinearMap.neg_apply, MultilinearMap.domDomCongr_apply,
    MultilinearMap.domCoprod_apply]
  convert add_right_neg (G := N₁ ⊗[R'] N₂) _ using 6 <;>
  -- ⊢ (fun i_1 => v (↑(swap i j) (↑σ (Sum.inl i_1)))) = fun i => v (↑σ (Sum.inl i))
    · ext k
      -- ⊢ v (↑(swap i j) (↑σ (Sum.inl k))) = v (↑σ (Sum.inl k))
      -- ⊢ v (↑(swap i j) (↑σ (Sum.inr k))) = v (↑σ (Sum.inr k))
      -- 🎉 no goals
      rw [Equiv.apply_swap_eq_self hv]
      -- 🎉 no goals
#align alternating_map.dom_coprod.summand_add_swap_smul_eq_zero AlternatingMap.domCoprod.summand_add_swap_smul_eq_zero

/-- Swapping elements in `σ` with equal values in `v` result in zero if the swap has no effect
on the quotient. -/
theorem domCoprod.summand_eq_zero_of_smul_invariant (a : AlternatingMap R' Mᵢ N₁ ιa)
    (b : AlternatingMap R' Mᵢ N₂ ιb) (σ : Perm.ModSumCongr ιa ιb) {v : Sum ιa ιb → Mᵢ}
    {i j : Sum ιa ιb} (hv : v i = v j) (hij : i ≠ j) :
    swap i j • σ = σ → domCoprod.summand a b σ v = 0 := by
  refine Quotient.inductionOn' σ fun σ => ?_
  -- ⊢ swap i j • Quotient.mk'' σ = Quotient.mk'' σ → ↑(summand a b (Quotient.mk''  …
  dsimp only [Quotient.liftOn'_mk'', Quotient.map'_mk'', MultilinearMap.smul_apply,
    MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply, domCoprod.summand]
  intro hσ
  -- ⊢ (↑Perm.sign σ • (↑↑a fun i => v (↑σ (Sum.inl i))) ⊗ₜ[R'] ↑↑b fun i => v (↑σ  …
  cases' hi : σ⁻¹ i with val val <;> cases' hj : σ⁻¹ j with val_1 val_1 <;>
  -- ⊢ (↑Perm.sign σ • (↑↑a fun i => v (↑σ (Sum.inl i))) ⊗ₜ[R'] ↑↑b fun i => v (↑σ  …
                                     -- ⊢ (↑Perm.sign σ • (↑↑a fun i => v (↑σ (Sum.inl i))) ⊗ₜ[R'] ↑↑b fun i => v (↑σ  …
                                     -- ⊢ (↑Perm.sign σ • (↑↑a fun i => v (↑σ (Sum.inl i))) ⊗ₜ[R'] ↑↑b fun i => v (↑σ  …
    rw [Perm.inv_eq_iff_eq] at hi hj <;> substs hi hj <;> revert val val_1
    -- ⊢ (↑Perm.sign σ • (↑↑a fun i => v (↑σ (Sum.inl i))) ⊗ₜ[R'] ↑↑b fun i => v (↑σ  …
    -- ⊢ (↑Perm.sign σ • (↑↑a fun i => v (↑σ (Sum.inl i))) ⊗ₜ[R'] ↑↑b fun i => v (↑σ  …
    -- ⊢ (↑Perm.sign σ • (↑↑a fun i => v (↑σ (Sum.inl i))) ⊗ₜ[R'] ↑↑b fun i => v (↑σ  …
    -- ⊢ (↑Perm.sign σ • (↑↑a fun i => v (↑σ (Sum.inl i))) ⊗ₜ[R'] ↑↑b fun i => v (↑σ  …
                                         -- ⊢ (↑Perm.sign σ • (↑↑a fun i => v (↑σ (Sum.inl i))) ⊗ₜ[R'] ↑↑b fun i => v (↑σ  …
                                         -- ⊢ (↑Perm.sign σ • (↑↑a fun i => v (↑σ (Sum.inl i))) ⊗ₜ[R'] ↑↑b fun i => v (↑σ  …
                                         -- ⊢ (↑Perm.sign σ • (↑↑a fun i => v (↑σ (Sum.inl i))) ⊗ₜ[R'] ↑↑b fun i => v (↑σ  …
                                         -- ⊢ (↑Perm.sign σ • (↑↑a fun i => v (↑σ (Sum.inl i))) ⊗ₜ[R'] ↑↑b fun i => v (↑σ  …
                                                          -- ⊢ ∀ (val val_1 : ιa), v (↑σ (Sum.inl val)) = v (↑σ (Sum.inl val_1)) → ↑σ (Sum. …
                                                          -- ⊢ ∀ (val : ιa) (val_1 : ιb), v (↑σ (Sum.inl val)) = v (↑σ (Sum.inr val_1)) → ↑ …
                                                          -- ⊢ ∀ (val : ιb) (val_1 : ιa), v (↑σ (Sum.inr val)) = v (↑σ (Sum.inl val_1)) → ↑ …
                                                          -- ⊢ ∀ (val val_1 : ιb), v (↑σ (Sum.inr val)) = v (↑σ (Sum.inr val_1)) → ↑σ (Sum. …
  -- Porting note: `on_goal` is not available in `case _ | _ =>`, so the proof gets tedious.
  -- the term pairs with and cancels another term
  case inl.inr =>
    intro i' j' _ _ hσ
    obtain ⟨⟨sl, sr⟩, hσ⟩ := QuotientGroup.leftRel_apply.mp (Quotient.exact' hσ)
    replace hσ := Equiv.congr_fun hσ (Sum.inl i')
    dsimp only at hσ
    rw [smul_eq_mul, ← mul_swap_eq_swap_mul, mul_inv_rev, swap_inv, inv_mul_cancel_right] at hσ
    simp at hσ
  case inr.inl =>
    intro i' j' _ _ hσ
    obtain ⟨⟨sl, sr⟩, hσ⟩ := QuotientGroup.leftRel_apply.mp (Quotient.exact' hσ)
    replace hσ := Equiv.congr_fun hσ (Sum.inr i')
    dsimp only at hσ
    rw [smul_eq_mul, ← mul_swap_eq_swap_mul, mul_inv_rev, swap_inv, inv_mul_cancel_right] at hσ
    simp at hσ
  -- the term does not pair but is zero
  case inr.inr =>
    intro i' j' hv hij _
    convert smul_zero (M := ℤˣ) (A := N₁ ⊗[R'] N₂) _
    convert TensorProduct.tmul_zero (R := R') (M := N₁) N₂ _
    exact AlternatingMap.map_eq_zero_of_eq _ _ hv fun hij' => hij (hij' ▸ rfl)
  case inl.inl =>
    intro i' j' hv hij _
    convert smul_zero (M := ℤˣ) (A := N₁ ⊗[R'] N₂) _
    convert TensorProduct.zero_tmul (R := R') N₁ (N := N₂) _
    exact AlternatingMap.map_eq_zero_of_eq _ _ hv fun hij' => hij (hij' ▸ rfl)
#align alternating_map.dom_coprod.summand_eq_zero_of_smul_invariant AlternatingMap.domCoprod.summand_eq_zero_of_smul_invariant

/-- Like `MultilinearMap.domCoprod`, but ensures the result is also alternating.

Note that this is usually defined (for instance, as used in Proposition 22.24 in [Gallier2011Notes])
over integer indices `ιa = Fin n` and `ιb = Fin m`, as
$$
(f \wedge g)(u_1, \ldots, u_{m+n}) =
  \sum_{\operatorname{shuffle}(m, n)} \operatorname{sign}(\sigma)
    f(u_{\sigma(1)}, \ldots, u_{\sigma(m)}) g(u_{\sigma(m+1)}, \ldots, u_{\sigma(m+n)}),
$$
where $\operatorname{shuffle}(m, n)$ consists of all permutations of $[1, m+n]$ such that
$\sigma(1) < \cdots < \sigma(m)$ and $\sigma(m+1) < \cdots < \sigma(m+n)$.

Here, we generalize this by replacing:
* the product in the sum with a tensor product
* the filtering of $[1, m+n]$ to shuffles with an isomorphic quotient
* the additions in the subscripts of $\sigma$ with an index of type `Sum`

The specialized version can be obtained by combining this definition with `finSumFinEquiv` and
`LinearMap.mul'`.
-/
@[simps]
def domCoprod (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb) :
    AlternatingMap R' Mᵢ (N₁ ⊗[R'] N₂) (Sum ιa ιb) :=
  { ∑ σ : Perm.ModSumCongr ιa ιb, domCoprod.summand a b σ with
    toFun := fun v => (⇑(∑ σ : Perm.ModSumCongr ιa ιb, domCoprod.summand a b σ)) v
    map_eq_zero_of_eq' := fun v i j hv hij => by
      dsimp only
      -- ⊢ ↑(∑ σ : Perm.ModSumCongr ιa ιb, domCoprod.summand a b σ) v = 0
      rw [MultilinearMap.sum_apply]
      -- ⊢ ∑ a_1 : Perm.ModSumCongr ιa ιb, ↑(domCoprod.summand a b a_1) v = 0
      exact
        Finset.sum_involution (fun σ _ => Equiv.swap i j • σ)
          (fun σ _ => domCoprod.summand_add_swap_smul_eq_zero a b σ hv hij)
          (fun σ _ => mt <| domCoprod.summand_eq_zero_of_smul_invariant a b σ hv hij)
          (fun σ _ => Finset.mem_univ _) fun σ _ =>
          Equiv.Perm.ModSumCongr.swap_smul_involutive i j σ }
#align alternating_map.dom_coprod AlternatingMap.domCoprod
#align alternating_map.dom_coprod_apply AlternatingMap.domCoprod_apply

theorem domCoprod_coe (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb) :
    (↑(a.domCoprod b) : MultilinearMap R' (fun _ => Mᵢ) _) =
      ∑ σ : Perm.ModSumCongr ιa ιb, domCoprod.summand a b σ :=
  MultilinearMap.ext fun _ => rfl
#align alternating_map.dom_coprod_coe AlternatingMap.domCoprod_coe

/-- A more bundled version of `AlternatingMap.domCoprod` that maps
`((ι₁ → N) → N₁) ⊗ ((ι₂ → N) → N₂)` to `(ι₁ ⊕ ι₂ → N) → N₁ ⊗ N₂`. -/
def domCoprod' :
    AlternatingMap R' Mᵢ N₁ ιa ⊗[R'] AlternatingMap R' Mᵢ N₂ ιb →ₗ[R']
      AlternatingMap R' Mᵢ (N₁ ⊗[R'] N₂) (Sum ιa ιb) :=
  TensorProduct.lift <| by
    refine'
      LinearMap.mk₂ R' domCoprod (fun m₁ m₂ n => _) (fun c m n => _) (fun m n₁ n₂ => _)
        fun c m n => _ <;>
    · ext
      -- ⊢ ↑(domCoprod (m₁ + m₂) n) x✝ = ↑(domCoprod m₁ n + domCoprod m₂ n) x✝
      -- ⊢ ↑(domCoprod (c • m) n) x✝ = ↑(c • domCoprod m n) x✝
      -- ⊢ ↑(domCoprod m (n₁ + n₂)) x✝ = ↑(domCoprod m n₁ + domCoprod m n₂) x✝
      -- ⊢ ↑(domCoprod m (c • n)) x✝ = ↑(c • domCoprod m n) x✝
      -- ⊢ (fun x => ↑(Quotient.liftOn' x (fun σ => ↑Perm.sign σ • MultilinearMap.domDo …
      simp only [domCoprod_apply, add_apply, smul_apply, ← Finset.sum_add_distrib,
      -- ⊢ ↑(Quotient.liftOn' σ (fun σ => ↑Perm.sign σ • MultilinearMap.domDomCongr σ ( …
      -- ⊢ (fun x => ↑(Quotient.liftOn' x (fun σ => ↑Perm.sign σ • MultilinearMap.domDo …
      -- ⊢ ↑(Quotient.liftOn' (Quotient.mk'' σ) (fun σ => ↑Perm.sign σ • MultilinearMap …
        Finset.smul_sum, MultilinearMap.sum_apply, domCoprod.summand]
      -- ⊢ ↑(Quotient.liftOn' σ (fun σ => ↑Perm.sign σ • MultilinearMap.domDomCongr σ ( …
      -- ⊢ (fun x => ↑(Quotient.liftOn' x (fun σ => ↑Perm.sign σ • MultilinearMap.domDo …
      -- ⊢ ↑(Quotient.liftOn' (Quotient.mk'' σ) (fun σ => ↑Perm.sign σ • MultilinearMap …
      congr
      -- ⊢ ↑Perm.sign σ • ↑(MultilinearMap.domDomCongr σ (↑MultilinearMap.domCoprod' (↑ …
      -- ⊢ ↑(Quotient.liftOn' σ (fun σ => ↑Perm.sign σ • MultilinearMap.domDomCongr σ ( …
      -- 🎉 no goals
      -- ⊢ (fun x => ↑(Quotient.liftOn' x (fun σ => ↑Perm.sign σ • MultilinearMap.domDo …
      -- ⊢ ↑(Quotient.liftOn' (Quotient.mk'' σ) (fun σ => ↑Perm.sign σ • MultilinearMap …
      ext σ
      -- ⊢ ↑Perm.sign σ • ↑(MultilinearMap.domDomCongr σ (c • ↑MultilinearMap.domCoprod …
      -- ⊢ ↑(Quotient.liftOn' σ (fun σ => ↑Perm.sign σ • MultilinearMap.domDomCongr σ ( …
      -- 🎉 no goals
      refine Quotient.inductionOn' σ fun σ => ?_
      -- ⊢ ↑(Quotient.liftOn' (Quotient.mk'' σ) (fun σ => ↑Perm.sign σ • MultilinearMap …
      simp only [Quotient.liftOn'_mk'', coe_add, coe_smul, MultilinearMap.smul_apply,
      -- ⊢ ↑Perm.sign σ • ↑(MultilinearMap.domDomCongr σ (↑MultilinearMap.domCoprod' (↑ …
        ← MultilinearMap.domCoprod'_apply]
      -- 🎉 no goals
      simp only [TensorProduct.add_tmul, ← TensorProduct.smul_tmul', TensorProduct.tmul_add,
        TensorProduct.tmul_smul, LinearMap.map_add, LinearMap.map_smul]
      first | rw [← smul_add] | rw [smul_comm]
      -- ⊢ ↑Perm.sign σ • ↑(MultilinearMap.domDomCongr σ (c • ↑MultilinearMap.domCoprod …
      rfl
      -- 🎉 no goals
#align alternating_map.dom_coprod' AlternatingMap.domCoprod'

@[simp]
theorem domCoprod'_apply (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb) :
    domCoprod' (a ⊗ₜ[R'] b) = domCoprod a b :=
  rfl
#align alternating_map.dom_coprod'_apply AlternatingMap.domCoprod'_apply

end AlternatingMap

open Equiv

/-- A helper lemma for `MultilinearMap.domCoprod_alternization`. -/
theorem MultilinearMap.domCoprod_alternization_coe [DecidableEq ιa] [DecidableEq ιb]
    (a : MultilinearMap R' (fun _ : ιa => Mᵢ) N₁) (b : MultilinearMap R' (fun _ : ιb => Mᵢ) N₂) :
    MultilinearMap.domCoprod (MultilinearMap.alternatization a)
      (MultilinearMap.alternatization b) =
      ∑ σa : Perm ιa, ∑ σb : Perm ιb,
        Equiv.Perm.sign σa • Equiv.Perm.sign σb •
          MultilinearMap.domCoprod (a.domDomCongr σa) (b.domDomCongr σb) := by
  simp_rw [← MultilinearMap.domCoprod'_apply, MultilinearMap.alternatization_coe]
  -- ⊢ ↑domCoprod' ((∑ x : Perm ιa, ↑Perm.sign x • domDomCongr x a) ⊗ₜ[R'] ∑ x : Pe …
  simp_rw [TensorProduct.sum_tmul, TensorProduct.tmul_sum, LinearMap.map_sum, ←
    TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  rfl
  -- 🎉 no goals
#align multilinear_map.dom_coprod_alternization_coe MultilinearMap.domCoprod_alternization_coe

open AlternatingMap

/-- Computing the `MultilinearMap.alternatization` of the `MultilinearMap.domCoprod` is the same
as computing the `AlternatingMap.domCoprod` of the `MultilinearMap.alternatization`s.
-/
theorem MultilinearMap.domCoprod_alternization [DecidableEq ιa] [DecidableEq ιb]
    (a : MultilinearMap R' (fun _ : ιa => Mᵢ) N₁) (b : MultilinearMap R' (fun _ : ιb => Mᵢ) N₂) :
    MultilinearMap.alternatization (MultilinearMap.domCoprod a b) =
      a.alternatization.domCoprod (MultilinearMap.alternatization b) := by
  apply coe_multilinearMap_injective
  -- ⊢ ↑(↑alternatization (domCoprod a b)) = ↑(AlternatingMap.domCoprod (↑alternati …
  rw [domCoprod_coe, MultilinearMap.alternatization_coe,
    Finset.sum_partition (QuotientGroup.leftRel (Perm.sumCongrHom ιa ιb).range)]
  congr 1
  -- ⊢ (fun xbar => ∑ y in Finset.filter (fun x => Quotient.mk (QuotientGroup.leftR …
  ext1 σ
  -- ⊢ ∑ y in Finset.filter (fun x => Quotient.mk (QuotientGroup.leftRel (MonoidHom …
  refine Quotient.inductionOn' σ fun σ => ?_
  -- ⊢ ∑ y in Finset.filter (fun x => Quotient.mk (QuotientGroup.leftRel (MonoidHom …
  -- unfold the quotient mess left by `Finset.sum_partition`
  -- Porting note: Was `conv in .. => ..`.
  erw
    [@Finset.filter_congr _ _ (fun a => @Quotient.decidableEq _ _
      (QuotientGroup.leftRelDecidable (MonoidHom.range (Perm.sumCongrHom ιa ιb)))
      (Quotient.mk (QuotientGroup.leftRel (MonoidHom.range (Perm.sumCongrHom ιa ιb))) a)
      (Quotient.mk'' σ)) _ (s := Finset.univ)
    fun x _ => QuotientGroup.eq' (s := MonoidHom.range (Perm.sumCongrHom ιa ιb)) (a := x) (b := σ)]
  -- eliminate a multiplication
  rw [← Finset.map_univ_equiv (Equiv.mulLeft σ), Finset.filter_map, Finset.sum_map]
  -- ⊢ ∑ x in Finset.filter ((fun x => x⁻¹ * σ ∈ MonoidHom.range (Perm.sumCongrHom  …
  simp_rw [Equiv.coe_toEmbedding, Equiv.coe_mulLeft, (· ∘ ·), mul_inv_rev, inv_mul_cancel_right,
    Subgroup.inv_mem_iff, MonoidHom.mem_range, Finset.univ_filter_exists,
    Finset.sum_image (Perm.sumCongrHom_injective.injOn _)]
  -- now we're ready to clean up the RHS, pulling out the summation
  rw [domCoprod.summand_mk'', MultilinearMap.domCoprod_alternization_coe, ← Finset.sum_product',
    Finset.univ_product_univ, ← MultilinearMap.domDomCongrEquiv_apply, _root_.map_sum,
    Finset.smul_sum]
  congr 1
  -- ⊢ (fun x => ↑Perm.sign (σ * ↑(Perm.sumCongrHom ιa ιb) x) • domDomCongr (σ * ↑( …
  ext1 ⟨al, ar⟩
  -- ⊢ ↑Perm.sign (σ * ↑(Perm.sumCongrHom ιa ιb) (al, ar)) • domDomCongr (σ * ↑(Per …
  dsimp only
  -- ⊢ ↑Perm.sign (σ * ↑(Perm.sumCongrHom ιa ιb) (al, ar)) • domDomCongr (σ * ↑(Per …
  -- pull out the pair of smuls on the RHS, by rewriting to `_ →ₗ[ℤ] _` and back
  rw [← AddEquiv.coe_toAddMonoidHom, ← AddMonoidHom.coe_toIntLinearMap, LinearMap.map_smul_of_tower,
    LinearMap.map_smul_of_tower, AddMonoidHom.coe_toIntLinearMap, AddEquiv.coe_toAddMonoidHom,
    MultilinearMap.domDomCongrEquiv_apply]
  -- pick up the pieces
  rw [MultilinearMap.domDomCongr_mul, Perm.sign_mul, Perm.sumCongrHom_apply,
    MultilinearMap.domCoprod_domDomCongr_sumCongr, Perm.sign_sumCongr, mul_smul, mul_smul]
#align multilinear_map.dom_coprod_alternization MultilinearMap.domCoprod_alternization

/-- Taking the `MultilinearMap.alternatization` of the `MultilinearMap.domCoprod` of two
`AlternatingMap`s gives a scaled version of the `AlternatingMap.coprod` of those maps.
-/
theorem MultilinearMap.domCoprod_alternization_eq [DecidableEq ιa] [DecidableEq ιb]
    (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb) :
    MultilinearMap.alternatization
      (MultilinearMap.domCoprod a b : MultilinearMap R' (fun _ : Sum ιa ιb => Mᵢ) (N₁ ⊗ N₂)) =
      ((Fintype.card ιa).factorial * (Fintype.card ιb).factorial) • a.domCoprod b := by
  rw [MultilinearMap.domCoprod_alternization, coe_alternatization, coe_alternatization, mul_smul,
    ← AlternatingMap.domCoprod'_apply, ← AlternatingMap.domCoprod'_apply,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    LinearMap.map_smul_of_tower AlternatingMap.domCoprod',
    LinearMap.map_smul_of_tower AlternatingMap.domCoprod']
#align multilinear_map.dom_coprod_alternization_eq MultilinearMap.domCoprod_alternization_eq

end Coprod

section Basis

open AlternatingMap

variable {ι₁ : Type*} [Finite ι]

variable {R' : Type*} {N₁ N₂ : Type*} [CommSemiring R'] [AddCommMonoid N₁] [AddCommMonoid N₂]

variable [Module R' N₁] [Module R' N₂]

/-- Two alternating maps indexed by a `Fintype` are equal if they are equal when all arguments
are distinct basis vectors. -/
theorem Basis.ext_alternating {f g : AlternatingMap R' N₁ N₂ ι} (e : Basis ι₁ R' N₁)
    (h : ∀ v : ι → ι₁, Function.Injective v → (f fun i => e (v i)) = g fun i => e (v i)) :
    f = g := by
  classical
    refine' AlternatingMap.coe_multilinearMap_injective (Basis.ext_multilinear e fun v => _)
    by_cases hi : Function.Injective v
    · exact h v hi
    · have : ¬Function.Injective fun i => e (v i) := hi.imp Function.Injective.of_comp
      rw [coe_multilinearMap, coe_multilinearMap, f.map_eq_zero_of_not_injective _ this,
        g.map_eq_zero_of_not_injective _ this]
#align basis.ext_alternating Basis.ext_alternating

end Basis

/-! ### Currying -/


section Currying

variable {R' : Type*} {M'' M₂'' N'' N₂'' : Type*} [CommSemiring R'] [AddCommMonoid M'']
  [AddCommMonoid M₂''] [AddCommMonoid N''] [AddCommMonoid N₂''] [Module R' M''] [Module R' M₂'']
  [Module R' N''] [Module R' N₂'']

namespace AlternatingMap

/-- Given an alternating map `f` in `n+1` variables, split the first variable to obtain
a linear map into alternating maps in `n` variables, given by `x ↦ (m ↦ f (Matrix.vecCons x m))`.
It can be thought of as a map $Hom(\bigwedge^{n+1} M, N) \to Hom(M, Hom(\bigwedge^n M, N))$.

This is `MultilinearMap.curryLeft` for `AlternatingMap`. See also
`AlternatingMap.curryLeftLinearMap`. -/
@[simps]
def curryLeft {n : ℕ} (f : AlternatingMap R' M'' N'' (Fin n.succ)) :
    M'' →ₗ[R'] AlternatingMap R' M'' N'' (Fin n) where
  toFun m :=
    { f.toMultilinearMap.curryLeft m with
      toFun := fun v => f (Matrix.vecCons m v)
      map_eq_zero_of_eq' := fun v i j hv hij =>
        f.map_eq_zero_of_eq _ (by
          rwa [Matrix.cons_val_succ, Matrix.cons_val_succ]) ((Fin.succ_injective _).ne hij) }
          -- 🎉 no goals
  map_add' m₁ m₂ := ext fun v => f.map_vecCons_add _ _ _
  map_smul' r m := ext fun v => f.map_vecCons_smul _ _ _
#align alternating_map.curry_left AlternatingMap.curryLeft
#align alternating_map.curry_left_apply_apply AlternatingMap.curryLeft_apply_apply

@[simp]
theorem curryLeft_zero {n : ℕ} : curryLeft (0 : AlternatingMap R' M'' N'' (Fin n.succ)) = 0 :=
  rfl
#align alternating_map.curry_left_zero AlternatingMap.curryLeft_zero

@[simp]
theorem curryLeft_add {n : ℕ} (f g : AlternatingMap R' M'' N'' (Fin n.succ)) :
    curryLeft (f + g) = curryLeft f + curryLeft g :=
  rfl
#align alternating_map.curry_left_add AlternatingMap.curryLeft_add

@[simp]
theorem curryLeft_smul {n : ℕ} (r : R') (f : AlternatingMap R' M'' N'' (Fin n.succ)) :
    curryLeft (r • f) = r • curryLeft f :=
  rfl
#align alternating_map.curry_left_smul AlternatingMap.curryLeft_smul

/-- `AlternatingMap.curryLeft` as a `LinearMap`. This is a separate definition as dot notation
does not work for this version. -/
@[simps]
def curryLeftLinearMap {n : ℕ} :
    AlternatingMap R' M'' N'' (Fin n.succ) →ₗ[R'] M'' →ₗ[R'] AlternatingMap R' M'' N'' (Fin n) where
  toFun f := f.curryLeft
  map_add' := curryLeft_add
  map_smul' := curryLeft_smul
#align alternating_map.curry_left_linear_map AlternatingMap.curryLeftLinearMap
#align alternating_map.curry_left_linear_map_apply AlternatingMap.curryLeftLinearMap

/-- Currying with the same element twice gives the zero map. -/
@[simp]
theorem curryLeft_same {n : ℕ} (f : AlternatingMap R' M'' N'' (Fin n.succ.succ)) (m : M'') :
    (f.curryLeft m).curryLeft m = 0 :=
  ext fun x => f.map_eq_zero_of_eq _ (by simp) Fin.zero_ne_one
                                         -- 🎉 no goals
#align alternating_map.curry_left_same AlternatingMap.curryLeft_same

@[simp]
theorem curryLeft_compAlternatingMap {n : ℕ} (g : N'' →ₗ[R'] N₂'')
    (f : AlternatingMap R' M'' N'' (Fin n.succ)) (m : M'') :
    (g.compAlternatingMap f).curryLeft m = g.compAlternatingMap (f.curryLeft m) :=
  rfl
#align alternating_map.curry_left_comp_alternating_map AlternatingMap.curryLeft_compAlternatingMap

@[simp]
theorem curryLeft_compLinearMap {n : ℕ} (g : M₂'' →ₗ[R'] M'')
    (f : AlternatingMap R' M'' N'' (Fin n.succ)) (m : M₂'') :
    (f.compLinearMap g).curryLeft m = (f.curryLeft (g m)).compLinearMap g :=
  ext fun v =>
    congr_arg f <|
      funext <| by
        refine' Fin.cases _ _
        -- ⊢ ↑((fun x => g) 0) (Matrix.vecCons m v 0) = Matrix.vecCons (↑g m) (fun i => ↑ …
        · rfl
          -- 🎉 no goals
        · simp
          -- 🎉 no goals
#align alternating_map.curry_left_comp_linear_map AlternatingMap.curryLeft_compLinearMap

/-- The space of constant maps is equivalent to the space of maps that are alternating with respect
to an empty family. -/
@[simps]
def constLinearEquivOfIsEmpty [IsEmpty ι] : N'' ≃ₗ[R'] AlternatingMap R' M'' N'' ι where
  toFun := AlternatingMap.constOfIsEmpty R' M'' ι
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := f 0
  left_inv _ := rfl
  right_inv f := ext fun _ => AlternatingMap.congr_arg f <| Subsingleton.elim _ _
#align alternating_map.const_linear_equiv_of_is_empty AlternatingMap.constLinearEquivOfIsEmpty
#align alternating_map.const_linear_equiv_of_is_empty_apply AlternatingMap.constLinearEquivOfIsEmpty_apply
#align alternating_map.const_linear_equiv_of_is_empty_symm_apply AlternatingMap.constLinearEquivOfIsEmpty_symm_apply

end AlternatingMap

end Currying
