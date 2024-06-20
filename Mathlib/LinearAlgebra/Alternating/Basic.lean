/-
Copyright (c) 2020 Zhangir Azerbayev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Zhangir Azerbayev
-/
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fintype.Perm
import Mathlib.LinearAlgebra.Multilinear.Basis

#align_import linear_algebra.alternating from "leanprover-community/mathlib"@"0c1d80f5a86b36c1db32e021e8d19ae7809d5b79"

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
* `MultilinearMap.domDomCongr`, for permuting the elements within a family.
* `MultilinearMap.alternatization`, which makes an alternating map out of a non-alternating one.
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

/-- An alternating map from `ι → M` to `N`, denoted `M [⋀^ι]→ₗ[R] N`,
is a multilinear map that vanishes when two of its arguments are equal. -/
structure AlternatingMap extends MultilinearMap R (fun _ : ι => M) N where
  /-- The map is alternating: if `v` has two equal coordinates, then `f v = 0`. -/
  map_eq_zero_of_eq' : ∀ (v : ι → M) (i j : ι), v i = v j → i ≠ j → toFun v = 0
#align alternating_map AlternatingMap

@[inherit_doc]
notation M " [⋀^" ι "]→ₗ[" R "] " N:100 => AlternatingMap R M N ι

end

/-- The multilinear map associated to an alternating map -/
add_decl_doc AlternatingMap.toMultilinearMap

namespace AlternatingMap

variable (f f' : M [⋀^ι]→ₗ[R] N)
variable (g g₂ : M [⋀^ι]→ₗ[R] N')
variable (g' : M' [⋀^ι]→ₗ[R] N')
variable (v : ι → M) (v' : ι → M')

open Function

/-! Basic coercion simp lemmas, largely copied from `RingHom` and `MultilinearMap` -/


section Coercions

instance instFunLike : FunLike (M [⋀^ι]→ₗ[R] N) (ι → M) N where
  coe f := f.toFun
  coe_injective' := fun f g h ↦ by
    rcases f with ⟨⟨_, _, _⟩, _⟩
    rcases g with ⟨⟨_, _, _⟩, _⟩
    congr
#align alternating_map.fun_like AlternatingMap.instFunLike

-- shortcut instance
instance coeFun : CoeFun (M [⋀^ι]→ₗ[R] N) fun _ => (ι → M) → N :=
  ⟨DFunLike.coe⟩
#align alternating_map.has_coe_to_fun AlternatingMap.coeFun

initialize_simps_projections AlternatingMap (toFun → apply)

@[simp]
theorem toFun_eq_coe : f.toFun = f :=
  rfl
#align alternating_map.to_fun_eq_coe AlternatingMap.toFun_eq_coe

-- Porting note: changed statement to reflect new `mk` signature
@[simp]
theorem coe_mk (f : MultilinearMap R (fun _ : ι => M) N) (h) :
    ⇑(⟨f, h⟩ : M [⋀^ι]→ₗ[R] N) = f :=
  rfl
#align alternating_map.coe_mk AlternatingMap.coe_mkₓ

theorem congr_fun {f g : M [⋀^ι]→ₗ[R] N} (h : f = g) (x : ι → M) : f x = g x :=
  congr_arg (fun h : M [⋀^ι]→ₗ[R] N => h x) h
#align alternating_map.congr_fun AlternatingMap.congr_fun

theorem congr_arg (f : M [⋀^ι]→ₗ[R] N) {x y : ι → M} (h : x = y) : f x = f y :=
  _root_.congr_arg (fun x : ι → M => f x) h
#align alternating_map.congr_arg AlternatingMap.congr_arg

theorem coe_injective : Injective ((↑) : M [⋀^ι]→ₗ[R] N → (ι → M) → N) :=
  DFunLike.coe_injective
#align alternating_map.coe_injective AlternatingMap.coe_injective

@[norm_cast] -- @[simp] -- Porting note (#10618): simp can prove this
theorem coe_inj {f g : M [⋀^ι]→ₗ[R] N} : (f : (ι → M) → N) = g ↔ f = g :=
  coe_injective.eq_iff
#align alternating_map.coe_inj AlternatingMap.coe_inj

@[ext]
theorem ext {f f' : M [⋀^ι]→ₗ[R] N} (H : ∀ x, f x = f' x) : f = f' :=
  DFunLike.ext _ _ H
#align alternating_map.ext AlternatingMap.ext

theorem ext_iff {f g : M [⋀^ι]→ₗ[R] N} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h _ => h ▸ rfl, fun h => ext h⟩
#align alternating_map.ext_iff AlternatingMap.ext_iff

attribute [coe] AlternatingMap.toMultilinearMap

instance coe : Coe (M [⋀^ι]→ₗ[R] N) (MultilinearMap R (fun _ : ι => M) N) :=
  ⟨fun x => x.toMultilinearMap⟩
#align alternating_map.multilinear_map.has_coe AlternatingMap.coe

@[simp, norm_cast]
theorem coe_multilinearMap : ⇑(f : MultilinearMap R (fun _ : ι => M) N) = f :=
  rfl
#align alternating_map.coe_multilinear_map AlternatingMap.coe_multilinearMap

theorem coe_multilinearMap_injective :
    Function.Injective ((↑) : M [⋀^ι]→ₗ[R] N → MultilinearMap R (fun _ : ι => M) N) :=
  fun _ _ h => ext <| MultilinearMap.congr_fun h
#align alternating_map.coe_multilinear_map_injective AlternatingMap.coe_multilinearMap_injective

#noalign alternating_map.to_multilinear_map_eq_coe

-- Porting note: changed statement to reflect new `mk` signature.
-- Porting note: removed `simp`
-- @[simp]
theorem coe_multilinearMap_mk (f : (ι → M) → N) (h₁ h₂ h₃) :
    ((⟨⟨f, h₁, h₂⟩, h₃⟩ : M [⋀^ι]→ₗ[R] N) : MultilinearMap R (fun _ : ι => M) N) =
      ⟨f, @h₁, @h₂⟩ := by
  simp
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
  push_neg at hv
  rcases hv with ⟨i₁, i₂, heq, hne⟩
  exact f.map_eq_zero_of_eq v heq hne
#align alternating_map.map_eq_zero_of_not_injective AlternatingMap.map_eq_zero_of_not_injective

/-!
### Algebraic structure inherited from `MultilinearMap`

`AlternatingMap` carries the same `AddCommMonoid`, `AddCommGroup`, and `Module` structure
as `MultilinearMap`
-/


section SMul

variable {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]

instance smul : SMul S (M [⋀^ι]→ₗ[R] N) :=
  ⟨fun c f =>
    { c • (f : MultilinearMap R (fun _ : ι => M) N) with
      map_eq_zero_of_eq' := fun v i j h hij => by simp [f.map_eq_zero_of_eq v h hij] }⟩
#align alternating_map.has_smul AlternatingMap.smul

@[simp]
theorem smul_apply (c : S) (m : ι → M) : (c • f) m = c • f m :=
  rfl
#align alternating_map.smul_apply AlternatingMap.smul_apply

@[norm_cast]
theorem coe_smul (c : S) : ↑(c • f) = c • (f : MultilinearMap R (fun _ : ι => M) N) :=
  rfl
#align alternating_map.coe_smul AlternatingMap.coe_smul

theorem coeFn_smul (c : S) (f : M [⋀^ι]→ₗ[R] N) : ⇑(c • f) = c • ⇑f :=
  rfl
#align alternating_map.coe_fn_smul AlternatingMap.coeFn_smul

instance isCentralScalar [DistribMulAction Sᵐᵒᵖ N] [IsCentralScalar S N] :
    IsCentralScalar S (M [⋀^ι]→ₗ[R] N) :=
  ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩
#align alternating_map.is_central_scalar AlternatingMap.isCentralScalar

end SMul

/-- The cartesian product of two alternating maps, as an alternating map. -/
@[simps!]
def prod (f : M [⋀^ι]→ₗ[R] N) (g : M [⋀^ι]→ₗ[R] P) : M [⋀^ι]→ₗ[R] (N × P) :=
  { f.toMultilinearMap.prod g.toMultilinearMap with
    map_eq_zero_of_eq' := fun _ _ _ h hne =>
      Prod.ext (f.map_eq_zero_of_eq _ h hne) (g.map_eq_zero_of_eq _ h hne) }
#align alternating_map.prod AlternatingMap.prod
#align alternating_map.prod_apply AlternatingMap.prod_apply

@[simp]
theorem coe_prod (f : M [⋀^ι]→ₗ[R] N) (g : M [⋀^ι]→ₗ[R] P) :
    (f.prod g : MultilinearMap R (fun _ : ι => M) (N × P)) = MultilinearMap.prod f g :=
  rfl
#align alternating_map.coe_prod AlternatingMap.coe_prod

/-- Combine a family of alternating maps with the same domain and codomains `N i` into an
alternating map taking values in the space of functions `Π i, N i`. -/
@[simps!]
def pi {ι' : Type*} {N : ι' → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M [⋀^ι]→ₗ[R] N i) : M [⋀^ι]→ₗ[R] (∀ i, N i) :=
  { MultilinearMap.pi fun a => (f a).toMultilinearMap with
    map_eq_zero_of_eq' := fun _ _ _ h hne => funext fun a => (f a).map_eq_zero_of_eq _ h hne }
#align alternating_map.pi AlternatingMap.pi
#align alternating_map.pi_apply AlternatingMap.pi_apply

@[simp]
theorem coe_pi {ι' : Type*} {N : ι' → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M [⋀^ι]→ₗ[R] N i) :
    (pi f : MultilinearMap R (fun _ : ι => M) (∀ i, N i)) = MultilinearMap.pi fun a => f a :=
  rfl
#align alternating_map.coe_pi AlternatingMap.coe_pi

/-- Given an alternating `R`-multilinear map `f` taking values in `R`, `f.smul_right z` is the map
sending `m` to `f m • z`. -/
@[simps!]
def smulRight {R M₁ M₂ ι : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module R M₁] [Module R M₂] (f : M₁ [⋀^ι]→ₗ[R] R) (z : M₂) : M₁ [⋀^ι]→ₗ[R] M₂ :=
  { f.toMultilinearMap.smulRight z with
    map_eq_zero_of_eq' := fun v i j h hne => by simp [f.map_eq_zero_of_eq v h hne] }
#align alternating_map.smul_right AlternatingMap.smulRight
#align alternating_map.smul_right_apply AlternatingMap.smulRight_apply

@[simp]
theorem coe_smulRight {R M₁ M₂ ι : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module R M₁] [Module R M₂] (f : M₁ [⋀^ι]→ₗ[R] R) (z : M₂) :
    (f.smulRight z : MultilinearMap R (fun _ : ι => M₁) M₂) = MultilinearMap.smulRight f z :=
  rfl
#align alternating_map.coe_smul_right AlternatingMap.coe_smulRight

instance add : Add (M [⋀^ι]→ₗ[R] N) :=
  ⟨fun a b =>
    { (a + b : MultilinearMap R (fun _ : ι => M) N) with
      map_eq_zero_of_eq' := fun v i j h hij => by
        simp [a.map_eq_zero_of_eq v h hij, b.map_eq_zero_of_eq v h hij] }⟩
#align alternating_map.has_add AlternatingMap.add

@[simp]
theorem add_apply : (f + f') v = f v + f' v :=
  rfl
#align alternating_map.add_apply AlternatingMap.add_apply

@[norm_cast]
theorem coe_add : (↑(f + f') : MultilinearMap R (fun _ : ι => M) N) = f + f' :=
  rfl
#align alternating_map.coe_add AlternatingMap.coe_add

instance zero : Zero (M [⋀^ι]→ₗ[R] N) :=
  ⟨{ (0 : MultilinearMap R (fun _ : ι => M) N) with
      map_eq_zero_of_eq' := fun v i j _ _ => by simp }⟩
#align alternating_map.has_zero AlternatingMap.zero

@[simp]
theorem zero_apply : (0 : M [⋀^ι]→ₗ[R] N) v = 0 :=
  rfl
#align alternating_map.zero_apply AlternatingMap.zero_apply

@[norm_cast]
theorem coe_zero : ((0 : M [⋀^ι]→ₗ[R] N) : MultilinearMap R (fun _ : ι => M) N) = 0 :=
  rfl
#align alternating_map.coe_zero AlternatingMap.coe_zero

@[simp]
theorem mk_zero :
    mk (0 : MultilinearMap R (fun _ : ι ↦ M) N) (0 : M [⋀^ι]→ₗ[R] N).2 = 0 :=
  rfl

instance inhabited : Inhabited (M [⋀^ι]→ₗ[R] N) :=
  ⟨0⟩
#align alternating_map.inhabited AlternatingMap.inhabited

instance addCommMonoid : AddCommMonoid (M [⋀^ι]→ₗ[R] N) :=
  coe_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => coeFn_smul _ _
#align alternating_map.add_comm_monoid AlternatingMap.addCommMonoid

instance neg : Neg (M [⋀^ι]→ₗ[R] N') :=
  ⟨fun f =>
    { -(f : MultilinearMap R (fun _ : ι => M) N') with
      map_eq_zero_of_eq' := fun v i j h hij => by simp [f.map_eq_zero_of_eq v h hij] }⟩
#align alternating_map.has_neg AlternatingMap.neg

@[simp]
theorem neg_apply (m : ι → M) : (-g) m = -g m :=
  rfl
#align alternating_map.neg_apply AlternatingMap.neg_apply

@[norm_cast]
theorem coe_neg : ((-g : M [⋀^ι]→ₗ[R] N') : MultilinearMap R (fun _ : ι => M) N') = -g :=
  rfl
#align alternating_map.coe_neg AlternatingMap.coe_neg

instance sub : Sub (M [⋀^ι]→ₗ[R] N') :=
  ⟨fun f g =>
    { (f - g : MultilinearMap R (fun _ : ι => M) N') with
      map_eq_zero_of_eq' := fun v i j h hij => by
        simp [f.map_eq_zero_of_eq v h hij, g.map_eq_zero_of_eq v h hij] }⟩
#align alternating_map.has_sub AlternatingMap.sub

@[simp]
theorem sub_apply (m : ι → M) : (g - g₂) m = g m - g₂ m :=
  rfl
#align alternating_map.sub_apply AlternatingMap.sub_apply

@[norm_cast]
theorem coe_sub : (↑(g - g₂) : MultilinearMap R (fun _ : ι => M) N') = g - g₂ :=
  rfl
#align alternating_map.coe_sub AlternatingMap.coe_sub

instance addCommGroup : AddCommGroup (M [⋀^ι]→ₗ[R] N') :=
  coe_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => coeFn_smul _ _) fun _ _ => coeFn_smul _ _
#align alternating_map.add_comm_group AlternatingMap.addCommGroup
section DistribMulAction

variable {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]

instance distribMulAction : DistribMulAction S (M [⋀^ι]→ₗ[R] N) where
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
instance module : Module S (M [⋀^ι]→ₗ[R] N) where
  add_smul _ _ _ := ext fun _ => add_smul _ _ _
  zero_smul _ := ext fun _ => zero_smul _ _
#align alternating_map.module AlternatingMap.module

instance noZeroSMulDivisors [NoZeroSMulDivisors S N] :
    NoZeroSMulDivisors S (M [⋀^ι]→ₗ[R] N) :=
  coe_injective.noZeroSMulDivisors _ rfl coeFn_smul
#align alternating_map.no_zero_smul_divisors AlternatingMap.noZeroSMulDivisors

end Module

section

variable (R M N)

/-- The natural equivalence between linear maps from `M` to `N`
and `1`-multilinear alternating maps from `M` to `N`. -/
@[simps!]
def ofSubsingleton [Subsingleton ι] (i : ι) : (M →ₗ[R] N) ≃ (M [⋀^ι]→ₗ[R] N) where
  toFun f := ⟨MultilinearMap.ofSubsingleton R M N i f, fun _ _ _ _ ↦ absurd (Subsingleton.elim _ _)⟩
  invFun f := (MultilinearMap.ofSubsingleton R M N i).symm f
  left_inv _ := rfl
  right_inv _ := coe_multilinearMap_injective <|
    (MultilinearMap.ofSubsingleton R M N i).apply_symm_apply _
#align alternating_map.of_subsingleton AlternatingMap.ofSubsingleton
#align alternating_map.of_subsingleton_apply AlternatingMap.ofSubsingleton_apply_apply

variable (ι) {N}

/-- The constant map is alternating when `ι` is empty. -/
@[simps (config := .asFn)]
def constOfIsEmpty [IsEmpty ι] (m : N) : M [⋀^ι]→ₗ[R] N :=
  { MultilinearMap.constOfIsEmpty R _ m with
    toFun := Function.const _ m
    map_eq_zero_of_eq' := fun _ => isEmptyElim }
#align alternating_map.const_of_is_empty AlternatingMap.constOfIsEmpty
#align alternating_map.const_of_is_empty_apply AlternatingMap.constOfIsEmpty_apply

end

/-- Restrict the codomain of an alternating map to a submodule. -/
@[simps]
def codRestrict (f : M [⋀^ι]→ₗ[R] N) (p : Submodule R N) (h : ∀ v, f v ∈ p) :
    M [⋀^ι]→ₗ[R] p :=
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
def compAlternatingMap (g : N →ₗ[R] N₂) : (M [⋀^ι]→ₗ[R] N) →+ (M [⋀^ι]→ₗ[R] N₂) where
  toFun f :=
    { g.compMultilinearMap (f : MultilinearMap R (fun _ : ι => M) N) with
      map_eq_zero_of_eq' := fun v i j h hij => by simp [f.map_eq_zero_of_eq v h hij] }
  map_zero' := by
    ext
    simp
  map_add' a b := by
    ext
    simp
#align linear_map.comp_alternating_map LinearMap.compAlternatingMap

@[simp]
theorem coe_compAlternatingMap (g : N →ₗ[R] N₂) (f : M [⋀^ι]→ₗ[R] N) :
    ⇑(g.compAlternatingMap f) = g ∘ f :=
  rfl
#align linear_map.coe_comp_alternating_map LinearMap.coe_compAlternatingMap

@[simp]
theorem compAlternatingMap_apply (g : N →ₗ[R] N₂) (f : M [⋀^ι]→ₗ[R] N) (m : ι → M) :
    g.compAlternatingMap f m = g (f m) :=
  rfl
#align linear_map.comp_alternating_map_apply LinearMap.compAlternatingMap_apply

theorem smulRight_eq_comp {R M₁ M₂ ι : Type*} [CommSemiring R] [AddCommMonoid M₁]
    [AddCommMonoid M₂] [Module R M₁] [Module R M₂] (f : M₁ [⋀^ι]→ₗ[R] R) (z : M₂) :
    f.smulRight z = (LinearMap.id.smulRight z).compAlternatingMap f :=
  rfl
#align linear_map.smul_right_eq_comp LinearMap.smulRight_eq_comp

@[simp]
theorem subtype_compAlternatingMap_codRestrict (f : M [⋀^ι]→ₗ[R] N) (p : Submodule R N)
    (h) : p.subtype.compAlternatingMap (f.codRestrict p h) = f :=
  AlternatingMap.ext fun _ => rfl
#align linear_map.subtype_comp_alternating_map_cod_restrict LinearMap.subtype_compAlternatingMap_codRestrict

@[simp]
theorem compAlternatingMap_codRestrict (g : N →ₗ[R] N₂) (f : M [⋀^ι]→ₗ[R] N)
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
def compLinearMap (f : M [⋀^ι]→ₗ[R] N) (g : M₂ →ₗ[R] M) : M₂ [⋀^ι]→ₗ[R] N :=
  { (f : MultilinearMap R (fun _ : ι => M) N).compLinearMap fun _ => g with
    map_eq_zero_of_eq' := fun _ _ _ h hij => f.map_eq_zero_of_eq _ (LinearMap.congr_arg h) hij }
#align alternating_map.comp_linear_map AlternatingMap.compLinearMap

theorem coe_compLinearMap (f : M [⋀^ι]→ₗ[R] N) (g : M₂ →ₗ[R] M) :
    ⇑(f.compLinearMap g) = f ∘ (g ∘ ·) :=
  rfl
#align alternating_map.coe_comp_linear_map AlternatingMap.coe_compLinearMap

@[simp]
theorem compLinearMap_apply (f : M [⋀^ι]→ₗ[R] N) (g : M₂ →ₗ[R] M) (v : ι → M₂) :
    f.compLinearMap g v = f fun i => g (v i) :=
  rfl
#align alternating_map.comp_linear_map_apply AlternatingMap.compLinearMap_apply

/-- Composing an alternating map twice with the same linear map in each argument is
the same as composing with their composition. -/
theorem compLinearMap_assoc (f : M [⋀^ι]→ₗ[R] N) (g₁ : M₂ →ₗ[R] M) (g₂ : M₃ →ₗ[R] M₂) :
    (f.compLinearMap g₁).compLinearMap g₂ = f.compLinearMap (g₁ ∘ₗ g₂) :=
  rfl
#align alternating_map.comp_linear_map_assoc AlternatingMap.compLinearMap_assoc

@[simp]
theorem zero_compLinearMap (g : M₂ →ₗ[R] M) : (0 : M [⋀^ι]→ₗ[R] N).compLinearMap g = 0 := by
  ext
  simp only [compLinearMap_apply, zero_apply]
#align alternating_map.zero_comp_linear_map AlternatingMap.zero_compLinearMap

@[simp]
theorem add_compLinearMap (f₁ f₂ : M [⋀^ι]→ₗ[R] N) (g : M₂ →ₗ[R] M) :
    (f₁ + f₂).compLinearMap g = f₁.compLinearMap g + f₂.compLinearMap g := by
  ext
  simp only [compLinearMap_apply, add_apply]
#align alternating_map.add_comp_linear_map AlternatingMap.add_compLinearMap

@[simp]
theorem compLinearMap_zero [Nonempty ι] (f : M [⋀^ι]→ₗ[R] N) :
    f.compLinearMap (0 : M₂ →ₗ[R] M) = 0 := by
  ext
  -- Porting note: Was `simp_rw [.., ← Pi.zero_def, map_zero, zero_apply]`.
  simp_rw [compLinearMap_apply, LinearMap.zero_apply, ← Pi.zero_def, zero_apply]
  exact map_zero f
#align alternating_map.comp_linear_map_zero AlternatingMap.compLinearMap_zero

/-- Composing an alternating map with the identity linear map in each argument. -/
@[simp]
theorem compLinearMap_id (f : M [⋀^ι]→ₗ[R] N) : f.compLinearMap LinearMap.id = f :=
  ext fun _ => rfl
#align alternating_map.comp_linear_map_id AlternatingMap.compLinearMap_id

/-- Composing with a surjective linear map is injective. -/
theorem compLinearMap_injective (f : M₂ →ₗ[R] M) (hf : Function.Surjective f) :
    Function.Injective fun g : M [⋀^ι]→ₗ[R] N => g.compLinearMap f := fun g₁ g₂ h =>
  ext fun x => by simpa [Function.surjInv_eq hf] using ext_iff.mp h (Function.surjInv hf ∘ x)
#align alternating_map.comp_linear_map_injective AlternatingMap.compLinearMap_injective

theorem compLinearMap_inj (f : M₂ →ₗ[R] M) (hf : Function.Surjective f)
    (g₁ g₂ : M [⋀^ι]→ₗ[R] N) : g₁.compLinearMap f = g₂.compLinearMap f ↔ g₁ = g₂ :=
  (compLinearMap_injective _ hf).eq_iff
#align alternating_map.comp_linear_map_inj AlternatingMap.compLinearMap_inj

section DomLcongr

variable (ι R N)
variable (S : Type*) [Semiring S] [Module S N] [SMulCommClass R S N]

/-- Construct a linear equivalence between maps from a linear equivalence between domains. -/
@[simps apply]
def domLCongr (e : M ≃ₗ[R] M₂) : M [⋀^ι]→ₗ[R] N ≃ₗ[S] (M₂ [⋀^ι]→ₗ[R] N) where
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
theorem compLinearEquiv_eq_zero_iff (f : M [⋀^ι]→ₗ[R] N) (g : M₂ ≃ₗ[R] M) :
    f.compLinearMap (g : M₂ →ₗ[R] M) = 0 ↔ f = 0 :=
  (domLCongr R N ι ℕ g.symm).map_eq_zero_iff
#align alternating_map.comp_linear_equiv_eq_zero_iff AlternatingMap.compLinearEquiv_eq_zero_iff

variable (f f' : M [⋀^ι]→ₗ[R] N)
variable (g g₂ : M [⋀^ι]→ₗ[R] N')
variable (g' : M' [⋀^ι]→ₗ[R] N')
variable (v : ι → M) (v' : ι → M')

open Function

/-!
### Other lemmas from `MultilinearMap`
-/


section

theorem map_update_sum {α : Type*} [DecidableEq ι] (t : Finset α) (i : ι) (g : α → M) (m : ι → M) :
    f (update m i (∑ a ∈ t, g a)) = ∑ a ∈ t, f (update m i (g a)) :=
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
#align alternating_map.map_update_self AlternatingMap.map_update_self

theorem map_update_update [DecidableEq ι] {i j : ι} (hij : i ≠ j) (m : M) :
    f (Function.update (Function.update v i m) j m) = 0 :=
  f.map_eq_zero_of_eq _
    (by rw [Function.update_same, Function.update_noteq hij, Function.update_same]) hij
#align alternating_map.map_update_update AlternatingMap.map_update_update

theorem map_swap_add [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    f (v ∘ Equiv.swap i j) + f v = 0 := by
  rw [Equiv.comp_swap_eq_update]
  convert f.map_update_update v hij (v i + v j)
  simp [f.map_update_self _ hij, f.map_update_self _ hij.symm,
    Function.update_comm hij (v i + v j) (v _) v, Function.update_comm hij.symm (v i) (v i) v]
#align alternating_map.map_swap_add AlternatingMap.map_swap_add

theorem map_add_swap [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    f v + f (v ∘ Equiv.swap i j) = 0 := by
  rw [add_comm]
  exact f.map_swap_add v hij
#align alternating_map.map_add_swap AlternatingMap.map_add_swap

theorem map_swap [DecidableEq ι] {i j : ι} (hij : i ≠ j) : g (v ∘ Equiv.swap i j) = -g v :=
  eq_neg_of_add_eq_zero_left <| g.map_swap_add v hij
#align alternating_map.map_swap AlternatingMap.map_swap

theorem map_perm [DecidableEq ι] [Fintype ι] (v : ι → M) (σ : Equiv.Perm ι) :
    g (v ∘ σ) = Equiv.Perm.sign σ • g v := by
  -- Porting note: `apply` → `induction'`
  induction' σ using Equiv.Perm.swap_induction_on' with s x y hxy hI
  · simp
  · -- Porting note: `← Function.comp.assoc` & `-Equiv.Perm.sign_swap'` are required.
    simpa [← Function.comp.assoc, g.map_swap (v ∘ s) hxy,
      Equiv.Perm.sign_swap hxy, -Equiv.Perm.sign_swap'] using hI
#align alternating_map.map_perm AlternatingMap.map_perm

theorem map_congr_perm [DecidableEq ι] [Fintype ι] (σ : Equiv.Perm ι) :
    g v = Equiv.Perm.sign σ • g (v ∘ σ) := by
  rw [g.map_perm, smul_smul]
  simp
#align alternating_map.map_congr_perm AlternatingMap.map_congr_perm

section DomDomCongr

/-- Transfer the arguments to a map along an equivalence between argument indices.

This is the alternating version of `MultilinearMap.domDomCongr`. -/
@[simps]
def domDomCongr (σ : ι ≃ ι') (f : M [⋀^ι]→ₗ[R] N) : M [⋀^ι']→ₗ[R] N :=
  { f.toMultilinearMap.domDomCongr σ with
    toFun := fun v => f (v ∘ σ)
    map_eq_zero_of_eq' := fun v i j hv hij =>
      f.map_eq_zero_of_eq (v ∘ σ) (i := σ.symm i) (j := σ.symm j)
        (by simpa using hv) (σ.symm.injective.ne hij) }
#align alternating_map.dom_dom_congr AlternatingMap.domDomCongr
#align alternating_map.dom_dom_congr_apply AlternatingMap.domDomCongr_apply

@[simp]
theorem domDomCongr_refl (f : M [⋀^ι]→ₗ[R] N) : f.domDomCongr (Equiv.refl ι) = f := rfl
#align alternating_map.dom_dom_congr_refl AlternatingMap.domDomCongr_refl

theorem domDomCongr_trans (σ₁ : ι ≃ ι') (σ₂ : ι' ≃ ι'') (f : M [⋀^ι]→ₗ[R] N) :
    f.domDomCongr (σ₁.trans σ₂) = (f.domDomCongr σ₁).domDomCongr σ₂ :=
  rfl
#align alternating_map.dom_dom_congr_trans AlternatingMap.domDomCongr_trans

@[simp]
theorem domDomCongr_zero (σ : ι ≃ ι') : (0 : M [⋀^ι]→ₗ[R] N).domDomCongr σ = 0 :=
  rfl
#align alternating_map.dom_dom_congr_zero AlternatingMap.domDomCongr_zero

@[simp]
theorem domDomCongr_add (σ : ι ≃ ι') (f g : M [⋀^ι]→ₗ[R] N) :
    (f + g).domDomCongr σ = f.domDomCongr σ + g.domDomCongr σ :=
  rfl
#align alternating_map.dom_dom_congr_add AlternatingMap.domDomCongr_add

@[simp]
theorem domDomCongr_smul {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]
    (σ : ι ≃ ι') (c : S) (f : M [⋀^ι]→ₗ[R] N) :
    (c • f).domDomCongr σ = c • f.domDomCongr σ :=
  rfl
#align alternating_map.dom_dom_congr_smul AlternatingMap.domDomCongr_smul

/-- `AlternatingMap.domDomCongr` as an equivalence.

This is declared separately because it does not work with dot notation. -/
@[simps apply symm_apply]
def domDomCongrEquiv (σ : ι ≃ ι') : M [⋀^ι]→ₗ[R] N ≃+ M [⋀^ι']→ₗ[R] N where
  toFun := domDomCongr σ
  invFun := domDomCongr σ.symm
  left_inv f := by
    ext
    simp [Function.comp]
  right_inv m := by
    ext
    simp [Function.comp]
  map_add' := domDomCongr_add σ
#align alternating_map.dom_dom_congr_equiv AlternatingMap.domDomCongrEquiv
#align alternating_map.dom_dom_congr_equiv_apply AlternatingMap.domDomCongrEquiv_apply
#align alternating_map.dom_dom_congr_equiv_symm_apply AlternatingMap.domDomCongrEquiv_symm_apply

section DomDomLcongr

variable (S : Type*) [Semiring S] [Module S N] [SMulCommClass R S N]

/-- `AlternatingMap.domDomCongr` as a linear equivalence. -/
@[simps apply symm_apply]
def domDomCongrₗ (σ : ι ≃ ι') : M [⋀^ι]→ₗ[R] N ≃ₗ[S] M [⋀^ι']→ₗ[R] N where
  toFun := domDomCongr σ
  invFun := domDomCongr σ.symm
  left_inv f := by ext; simp [Function.comp]
  right_inv m := by ext; simp [Function.comp]
  map_add' := domDomCongr_add σ
  map_smul' := domDomCongr_smul σ
#align alternating_map.dom_dom_lcongr AlternatingMap.domDomCongrₗ

@[simp]
theorem domDomCongrₗ_refl :
    (domDomCongrₗ S (Equiv.refl ι) : M [⋀^ι]→ₗ[R] N ≃ₗ[S] M [⋀^ι]→ₗ[R] N) =
      LinearEquiv.refl _ _ :=
  rfl
#align alternating_map.dom_dom_lcongr_refl AlternatingMap.domDomCongrₗ_refl

@[simp]
theorem domDomCongrₗ_toAddEquiv (σ : ι ≃ ι') :
    (↑(domDomCongrₗ S σ : M [⋀^ι]→ₗ[R] N ≃ₗ[S] _) : M [⋀^ι]→ₗ[R] N ≃+ _) =
      domDomCongrEquiv σ :=
  rfl
#align alternating_map.dom_dom_lcongr_to_add_equiv AlternatingMap.domDomCongrₗ_toAddEquiv

end DomDomLcongr

/-- The results of applying `domDomCongr` to two maps are equal if and only if those maps are. -/
@[simp]
theorem domDomCongr_eq_iff (σ : ι ≃ ι') (f g : M [⋀^ι]→ₗ[R] N) :
    f.domDomCongr σ = g.domDomCongr σ ↔ f = g :=
  (domDomCongrEquiv σ : _ ≃+ M [⋀^ι']→ₗ[R] N).apply_eq_iff_eq
#align alternating_map.dom_dom_congr_eq_iff AlternatingMap.domDomCongr_eq_iff

@[simp]
theorem domDomCongr_eq_zero_iff (σ : ι ≃ ι') (f : M [⋀^ι]→ₗ[R] N) :
    f.domDomCongr σ = 0 ↔ f = 0 :=
  (domDomCongrEquiv σ : M [⋀^ι]→ₗ[R] N ≃+ M [⋀^ι']→ₗ[R] N).map_eq_zero_iff
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
    {N : Type*} [AddCommGroup N] [Module K N] [NoZeroSMulDivisors K N] (f : M [⋀^ι]→ₗ[K] N)
    (v : ι → M) (h : ¬LinearIndependent K v) : f v = 0 := by
  obtain ⟨s, g, h, i, hi, hz⟩ := not_linearIndependent_iff.mp h
  letI := Classical.decEq ι
  suffices f (update v i (g i • v i)) = 0 by
    rw [f.map_smul, Function.update_eq_self, smul_eq_zero] at this
    exact Or.resolve_left this hz
  -- Porting note: Was `conv at h in .. => ..`.
  rw [← (funext fun x => ite_self (c := i = x) (d := Classical.decEq ι i x) (g x • v x))] at h
  rw [Finset.sum_ite, Finset.filter_eq, Finset.filter_ne, if_pos hi, Finset.sum_singleton,
    add_eq_zero_iff_eq_neg] at h
  rw [h, f.map_neg, f.map_update_sum, neg_eq_zero]; apply Finset.sum_eq_zero
  intro j hj
  obtain ⟨hij, _⟩ := Finset.mem_erase.mp hj
  rw [f.map_smul, f.map_update_self _ hij.symm, smul_zero]
#align alternating_map.map_linear_dependent AlternatingMap.map_linearDependent

section Fin

open Fin

/-- A version of `MultilinearMap.cons_add` for `AlternatingMap`. -/
theorem map_vecCons_add {n : ℕ} (f : M [⋀^Fin n.succ]→ₗ[R] N) (m : Fin n → M) (x y : M) :
    f (Matrix.vecCons (x + y) m) = f (Matrix.vecCons x m) + f (Matrix.vecCons y m) :=
  f.toMultilinearMap.cons_add _ _ _
#align alternating_map.map_vec_cons_add AlternatingMap.map_vecCons_add

/-- A version of `MultilinearMap.cons_smul` for `AlternatingMap`. -/
theorem map_vecCons_smul {n : ℕ} (f : M [⋀^Fin n.succ]→ₗ[R] N) (m : Fin n → M) (c : R)
    (x : M) : f (Matrix.vecCons (c • x) m) = c • f (Matrix.vecCons x m) :=
  f.toMultilinearMap.cons_smul _ _ _
#align alternating_map.map_vec_cons_smul AlternatingMap.map_vecCons_smul

end Fin

end AlternatingMap

namespace MultilinearMap

open Equiv

variable [Fintype ι] [DecidableEq ι]

private theorem alternization_map_eq_zero_of_eq_aux (m : MultilinearMap R (fun _ : ι => M) N')
    (v : ι → M) (i j : ι) (i_ne_j : i ≠ j) (hv : v i = v j) :
    (∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ) v = 0 := by
  rw [sum_apply]
  exact
    Finset.sum_involution (fun σ _ => swap i j * σ)
      -- Porting note: `-Equiv.Perm.sign_swap'` is required.
      (fun σ _ => by simp [Perm.sign_swap i_ne_j, apply_swap_eq_self hv, -Equiv.Perm.sign_swap'])
      (fun σ _ _ => (not_congr swap_mul_eq_iff).mpr i_ne_j) (fun σ _ => Finset.mem_univ _)
      fun σ _ => swap_mul_involutive i j σ

/-- Produce an `AlternatingMap` out of a `MultilinearMap`, by summing over all argument
permutations. -/
def alternatization : MultilinearMap R (fun _ : ι => M) N' →+ M [⋀^ι]→ₗ[R] N' where
  toFun m :=
    { ∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ with
      toFun := ⇑(∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ)
      map_eq_zero_of_eq' := fun v i j hvij hij =>
        alternization_map_eq_zero_of_eq_aux m v i j hij hvij }
  map_add' a b := by
    ext
    simp only [mk_coe, AlternatingMap.coe_mk, sum_apply, smul_apply, domDomCongr_apply, add_apply,
      smul_add, Finset.sum_add_distrib, AlternatingMap.add_apply]
  map_zero' := by
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
#align multilinear_map.alternatization_apply MultilinearMap.alternatization_apply

end MultilinearMap

namespace AlternatingMap

/-- Alternatizing a multilinear map that is already alternating results in a scale factor of `n!`,
where `n` is the number of inputs. -/
theorem coe_alternatization [DecidableEq ι] [Fintype ι] (a : M [⋀^ι]→ₗ[R] N') :
    MultilinearMap.alternatization (a : MultilinearMap R (fun _ => M) N')
    = Nat.factorial (Fintype.card ι) • a := by
  apply AlternatingMap.coe_injective
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
  simp [MultilinearMap.alternatization_def]
#align linear_map.comp_multilinear_map_alternatization LinearMap.compMultilinearMap_alternatization

end LinearMap

section Basis

open AlternatingMap

variable {ι₁ : Type*} [Finite ι]
variable {R' : Type*} {N₁ N₂ : Type*} [CommSemiring R'] [AddCommMonoid N₁] [AddCommMonoid N₂]
variable [Module R' N₁] [Module R' N₂]

/-- Two alternating maps indexed by a `Fintype` are equal if they are equal when all arguments
are distinct basis vectors. -/
theorem Basis.ext_alternating {f g : N₁ [⋀^ι]→ₗ[R'] N₂} (e : Basis ι₁ R' N₁)
    (h : ∀ v : ι → ι₁, Function.Injective v → (f fun i => e (v i)) = g fun i => e (v i)) :
    f = g := by
  classical
    refine AlternatingMap.coe_multilinearMap_injective (Basis.ext_multilinear e fun v => ?_)
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
def curryLeft {n : ℕ} (f : M'' [⋀^Fin n.succ]→ₗ[R'] N'') :
    M'' →ₗ[R'] M'' [⋀^Fin n]→ₗ[R'] N'' where
  toFun m :=
    { f.toMultilinearMap.curryLeft m with
      toFun := fun v => f (Matrix.vecCons m v)
      map_eq_zero_of_eq' := fun v i j hv hij =>
        f.map_eq_zero_of_eq _ (by
          rwa [Matrix.cons_val_succ, Matrix.cons_val_succ]) ((Fin.succ_injective _).ne hij) }
  map_add' m₁ m₂ := ext fun v => f.map_vecCons_add _ _ _
  map_smul' r m := ext fun v => f.map_vecCons_smul _ _ _
#align alternating_map.curry_left AlternatingMap.curryLeft
#align alternating_map.curry_left_apply_apply AlternatingMap.curryLeft_apply_apply

@[simp]
theorem curryLeft_zero {n : ℕ} : curryLeft (0 : M'' [⋀^Fin n.succ]→ₗ[R'] N'') = 0 :=
  rfl
#align alternating_map.curry_left_zero AlternatingMap.curryLeft_zero

@[simp]
theorem curryLeft_add {n : ℕ} (f g : M'' [⋀^Fin n.succ]→ₗ[R'] N'') :
    curryLeft (f + g) = curryLeft f + curryLeft g :=
  rfl
#align alternating_map.curry_left_add AlternatingMap.curryLeft_add

@[simp]
theorem curryLeft_smul {n : ℕ} (r : R') (f : M'' [⋀^Fin n.succ]→ₗ[R'] N'') :
    curryLeft (r • f) = r • curryLeft f :=
  rfl
#align alternating_map.curry_left_smul AlternatingMap.curryLeft_smul

/-- `AlternatingMap.curryLeft` as a `LinearMap`. This is a separate definition as dot notation
does not work for this version. -/
@[simps]
def curryLeftLinearMap {n : ℕ} :
    (M'' [⋀^Fin n.succ]→ₗ[R'] N'') →ₗ[R'] M'' →ₗ[R'] M'' [⋀^Fin n]→ₗ[R'] N'' where
  toFun f := f.curryLeft
  map_add' := curryLeft_add
  map_smul' := curryLeft_smul
#align alternating_map.curry_left_linear_map AlternatingMap.curryLeftLinearMap
#align alternating_map.curry_left_linear_map_apply AlternatingMap.curryLeftLinearMap

/-- Currying with the same element twice gives the zero map. -/
@[simp]
theorem curryLeft_same {n : ℕ} (f : M'' [⋀^Fin n.succ.succ]→ₗ[R'] N'') (m : M'') :
    (f.curryLeft m).curryLeft m = 0 :=
  ext fun x => f.map_eq_zero_of_eq _ (by simp) Fin.zero_ne_one
#align alternating_map.curry_left_same AlternatingMap.curryLeft_same

@[simp]
theorem curryLeft_compAlternatingMap {n : ℕ} (g : N'' →ₗ[R'] N₂'')
    (f : M'' [⋀^Fin n.succ]→ₗ[R'] N'') (m : M'') :
    (g.compAlternatingMap f).curryLeft m = g.compAlternatingMap (f.curryLeft m) :=
  rfl
#align alternating_map.curry_left_comp_alternating_map AlternatingMap.curryLeft_compAlternatingMap

@[simp]
theorem curryLeft_compLinearMap {n : ℕ} (g : M₂'' →ₗ[R'] M'')
    (f : M'' [⋀^Fin n.succ]→ₗ[R'] N'') (m : M₂'') :
    (f.compLinearMap g).curryLeft m = (f.curryLeft (g m)).compLinearMap g :=
  ext fun v => congr_arg f <| funext <| by
    refine Fin.cases ?_ ?_
    · rfl
    · simp
#align alternating_map.curry_left_comp_linear_map AlternatingMap.curryLeft_compLinearMap

/-- The space of constant maps is equivalent to the space of maps that are alternating with respect
to an empty family. -/
@[simps]
def constLinearEquivOfIsEmpty [IsEmpty ι] : N'' ≃ₗ[R'] (M'' [⋀^ι]→ₗ[R'] N'') where
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
