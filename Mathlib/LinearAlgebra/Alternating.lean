/-
Copyright (c) 2020 Zhangir Azerbayev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Zhangir Azerbayev

! This file was ported from Lean 3 source module linear_algebra.alternating
! leanprover-community/mathlib commit ce11c3c2a285bbe6937e26d9792fda4e51f3fe1a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.GroupAction.Quotient
import Mathbin.GroupTheory.Perm.Sign
import Mathbin.GroupTheory.Perm.Subgroup
import Mathbin.LinearAlgebra.LinearIndependent
import Mathbin.LinearAlgebra.Multilinear.Basis
import Mathbin.LinearAlgebra.Multilinear.TensorProduct

/-!
# Alternating Maps

We construct the bundled function `alternating_map`, which extends `multilinear_map` with all the
arguments of the same type.

## Main definitions
* `alternating_map R M N ι` is the space of `R`-linear alternating maps from `ι → M` to `N`.
* `f.map_eq_zero_of_eq` expresses that `f` is zero when two inputs are equal.
* `f.map_swap` expresses that `f` is negated when two inputs are swapped.
* `f.map_perm` expresses how `f` varies by a sign change under a permutation of its inputs.
* An `add_comm_monoid`, `add_comm_group`, and `module` structure over `alternating_map`s that
  matches the definitions over `multilinear_map`s.
* `multilinear_map.dom_dom_congr`, for permutating the elements within a family.
* `multilinear_map.alternatization`, which makes an alternating map out of a non-alternating one.
* `alternating_map.dom_coprod`, which behaves as a product between two alternating maps.
* `alternating_map.curry_left`, for binding the leftmost argument of an alternating map indexed
  by `fin n.succ`.

## Implementation notes
`alternating_map` is defined in terms of `map_eq_zero_of_eq`, as this is easier to work with than
using `map_swap` as a definition, and does not require `has_neg N`.

`alternating_map`s are provided with a coercion to `multilinear_map`, along with a set of
`norm_cast` lemmas that act on the algebraic structure:

* `alternating_map.coe_add`
* `alternating_map.coe_zero`
* `alternating_map.coe_sub`
* `alternating_map.coe_neg`
* `alternating_map.coe_smul`
-/


-- semiring / add_comm_monoid
variable {R : Type _} [Semiring R]

variable {M : Type _} [AddCommMonoid M] [Module R M]

variable {N : Type _} [AddCommMonoid N] [Module R N]

-- semiring / add_comm_group
variable {M' : Type _} [AddCommGroup M'] [Module R M']

variable {N' : Type _} [AddCommGroup N'] [Module R N']

variable {ι ι' ι'' : Type _}

section

variable (R M N ι)

/-- An alternating map is a multilinear map that vanishes when two of its arguments are equal.
-/
structure AlternatingMap extends MultilinearMap R (fun i : ι => M) N where
  map_eq_zero_of_eq' : ∀ (v : ι → M) (i j : ι) (h : v i = v j) (hij : i ≠ j), to_fun v = 0
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

/-! Basic coercion simp lemmas, largely copied from `ring_hom` and `multilinear_map` -/


section Coercions

instance : CoeFun (AlternatingMap R M N ι) fun _ => (ι → M) → N :=
  ⟨fun x => x.toFun⟩

initialize_simps_projections AlternatingMap (toFun → apply)

@[simp]
theorem toFun_eq_coe : f.toFun = f :=
  rfl
#align alternating_map.to_fun_eq_coe AlternatingMap.toFun_eq_coe

@[simp]
theorem coe_mk (f : (ι → M) → N) (h₁ h₂ h₃) : ⇑(⟨f, h₁, h₂, h₃⟩ : AlternatingMap R M N ι) = f :=
  rfl
#align alternating_map.coe_mk AlternatingMap.coe_mk

theorem congr_fun {f g : AlternatingMap R M N ι} (h : f = g) (x : ι → M) : f x = g x :=
  congr_arg (fun h : AlternatingMap R M N ι => h x) h
#align alternating_map.congr_fun AlternatingMap.congr_fun

theorem congr_arg (f : AlternatingMap R M N ι) {x y : ι → M} (h : x = y) : f x = f y :=
  congr_arg (fun x : ι → M => f x) h
#align alternating_map.congr_arg AlternatingMap.congr_arg

theorem coe_injective : Injective (coeFn : AlternatingMap R M N ι → (ι → M) → N) := fun f g h =>
  by
  cases f
  cases g
  cases h
  rfl
#align alternating_map.coe_injective AlternatingMap.coe_injective

@[simp, norm_cast]
theorem coe_inj {f g : AlternatingMap R M N ι} : (f : (ι → M) → N) = g ↔ f = g :=
  coe_injective.eq_iff
#align alternating_map.coe_inj AlternatingMap.coe_inj

@[ext]
theorem ext {f f' : AlternatingMap R M N ι} (H : ∀ x, f x = f' x) : f = f' :=
  coe_injective (funext H)
#align alternating_map.ext AlternatingMap.ext

theorem ext_iff {f g : AlternatingMap R M N ι} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => h ▸ rfl, fun h => ext h⟩
#align alternating_map.ext_iff AlternatingMap.ext_iff

instance : Coe (AlternatingMap R M N ι) (MultilinearMap R (fun i : ι => M) N) :=
  ⟨fun x => x.toMultilinearMap⟩

@[simp, norm_cast]
theorem coe_multilinearMap : ⇑(f : MultilinearMap R (fun i : ι => M) N) = f :=
  rfl
#align alternating_map.coe_multilinear_map AlternatingMap.coe_multilinearMap

theorem coe_multilinearMap_injective :
    Function.Injective (coe : AlternatingMap R M N ι → MultilinearMap R (fun i : ι => M) N) :=
  fun x y h => ext <| MultilinearMap.congr_fun h
#align alternating_map.coe_multilinear_map_injective AlternatingMap.coe_multilinearMap_injective

@[simp]
theorem toMultilinearMap_eq_coe : f.toMultilinearMap = f :=
  rfl
#align alternating_map.to_multilinear_map_eq_coe AlternatingMap.toMultilinearMap_eq_coe

@[simp]
theorem coe_multilinearMap_mk (f : (ι → M) → N) (h₁ h₂ h₃) :
    ((⟨f, h₁, h₂, h₃⟩ : AlternatingMap R M N ι) : MultilinearMap R (fun i : ι => M) N) =
      ⟨f, @h₁, @h₂⟩ :=
  rfl
#align alternating_map.coe_multilinear_map_mk AlternatingMap.coe_multilinearMap_mk

end Coercions

/-!
### Simp-normal forms of the structure fields

These are expressed in terms of `⇑f` instead of `f.to_fun`.
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

theorem map_eq_zero_of_not_injective (v : ι → M) (hv : ¬Function.Injective v) : f v = 0 :=
  by
  rw [Function.Injective] at hv
  push_neg  at hv
  rcases hv with ⟨i₁, i₂, heq, hne⟩
  exact f.map_eq_zero_of_eq v HEq hne
#align alternating_map.map_eq_zero_of_not_injective AlternatingMap.map_eq_zero_of_not_injective

/-!
### Algebraic structure inherited from `multilinear_map`

`alternating_map` carries the same `add_comm_monoid`, `add_comm_group`, and `module` structure
as `multilinear_map`
-/


section SMul

variable {S : Type _} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]

instance : SMul S (AlternatingMap R M N ι) :=
  ⟨fun c f =>
    { (c • f : MultilinearMap R (fun i : ι => M) N) with
      map_eq_zero_of_eq' := fun v i j h hij => by simp [f.map_eq_zero_of_eq v h hij] }⟩

@[simp]
theorem smul_apply (c : S) (m : ι → M) : (c • f) m = c • f m :=
  rfl
#align alternating_map.smul_apply AlternatingMap.smul_apply

@[norm_cast]
theorem coe_smul (c : S) :
    ((c • f : AlternatingMap R M N ι) : MultilinearMap R (fun i : ι => M) N) = c • f :=
  rfl
#align alternating_map.coe_smul AlternatingMap.coe_smul

theorem coeFn_smul (c : S) (f : AlternatingMap R M N ι) : ⇑(c • f) = c • f :=
  rfl
#align alternating_map.coe_fn_smul AlternatingMap.coeFn_smul

instance [DistribMulAction Sᵐᵒᵖ N] [IsCentralScalar S N] :
    IsCentralScalar S (AlternatingMap R M N ι) :=
  ⟨fun c f => ext fun x => op_smul_eq_smul _ _⟩

end SMul

instance : Add (AlternatingMap R M N ι) :=
  ⟨fun a b =>
    { (a + b : MultilinearMap R (fun i : ι => M) N) with
      map_eq_zero_of_eq' := fun v i j h hij => by
        simp [a.map_eq_zero_of_eq v h hij, b.map_eq_zero_of_eq v h hij] }⟩

@[simp]
theorem add_apply : (f + f') v = f v + f' v :=
  rfl
#align alternating_map.add_apply AlternatingMap.add_apply

@[norm_cast]
theorem coe_add : (↑(f + f') : MultilinearMap R (fun i : ι => M) N) = f + f' :=
  rfl
#align alternating_map.coe_add AlternatingMap.coe_add

instance : Zero (AlternatingMap R M N ι) :=
  ⟨{ (0 : MultilinearMap R (fun i : ι => M) N) with
      map_eq_zero_of_eq' := fun v i j h hij => by simp }⟩

@[simp]
theorem zero_apply : (0 : AlternatingMap R M N ι) v = 0 :=
  rfl
#align alternating_map.zero_apply AlternatingMap.zero_apply

@[norm_cast]
theorem coe_zero : ((0 : AlternatingMap R M N ι) : MultilinearMap R (fun i : ι => M) N) = 0 :=
  rfl
#align alternating_map.coe_zero AlternatingMap.coe_zero

instance : Inhabited (AlternatingMap R M N ι) :=
  ⟨0⟩

instance : AddCommMonoid (AlternatingMap R M N ι) :=
  coe_injective.AddCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => coeFn_smul _ _

instance : Neg (AlternatingMap R M N' ι) :=
  ⟨fun f =>
    { -(f : MultilinearMap R (fun i : ι => M) N') with
      map_eq_zero_of_eq' := fun v i j h hij => by simp [f.map_eq_zero_of_eq v h hij] }⟩

@[simp]
theorem neg_apply (m : ι → M) : (-g) m = -g m :=
  rfl
#align alternating_map.neg_apply AlternatingMap.neg_apply

@[norm_cast]
theorem coe_neg : ((-g : AlternatingMap R M N' ι) : MultilinearMap R (fun i : ι => M) N') = -g :=
  rfl
#align alternating_map.coe_neg AlternatingMap.coe_neg

instance : Sub (AlternatingMap R M N' ι) :=
  ⟨fun f g =>
    { (f - g : MultilinearMap R (fun i : ι => M) N') with
      map_eq_zero_of_eq' := fun v i j h hij => by
        simp [f.map_eq_zero_of_eq v h hij, g.map_eq_zero_of_eq v h hij] }⟩

@[simp]
theorem sub_apply (m : ι → M) : (g - g₂) m = g m - g₂ m :=
  rfl
#align alternating_map.sub_apply AlternatingMap.sub_apply

@[norm_cast]
theorem coe_sub : (↑(g - g₂) : MultilinearMap R (fun i : ι => M) N') = g - g₂ :=
  rfl
#align alternating_map.coe_sub AlternatingMap.coe_sub

instance : AddCommGroup (AlternatingMap R M N' ι) :=
  coe_injective.AddCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => coeFn_smul _ _) fun _ _ => coeFn_smul _ _

section DistribMulAction

variable {S : Type _} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]

instance : DistribMulAction S (AlternatingMap R M N ι)
    where
  one_smul f := ext fun x => one_smul _ _
  mul_smul c₁ c₂ f := ext fun x => mul_smul _ _ _
  smul_zero r := ext fun x => smul_zero _
  smul_add r f₁ f₂ := ext fun x => smul_add _ _ _

end DistribMulAction

section Module

variable {S : Type _} [Semiring S] [Module S N] [SMulCommClass R S N]

/-- The space of multilinear maps over an algebra over `R` is a module over `R`, for the pointwise
addition and scalar multiplication. -/
instance : Module S (AlternatingMap R M N ι)
    where
  add_smul r₁ r₂ f := ext fun x => add_smul _ _ _
  zero_smul f := ext fun x => zero_smul _ _

instance [NoZeroSMulDivisors S N] : NoZeroSMulDivisors S (AlternatingMap R M N ι) :=
  coe_injective.NoZeroSMulDivisors _ rfl coeFn_smul

end Module

section

variable (R M)

/-- The evaluation map from `ι → M` to `M` at a given `i` is alternating when `ι` is subsingleton.
-/
@[simps]
def ofSubsingleton [Subsingleton ι] (i : ι) : AlternatingMap R M M ι :=
  {
    MultilinearMap.ofSubsingleton R M
      i with
    toFun := Function.eval i
    map_eq_zero_of_eq' := fun v i j hv hij => (hij <| Subsingleton.elim _ _).elim }
#align alternating_map.of_subsingleton AlternatingMap.ofSubsingleton

/-- The constant map is alternating when `ι` is empty. -/
@[simps (config := { fullyApplied := false })]
def constOfIsEmpty [IsEmpty ι] (m : N) : AlternatingMap R M N ι :=
  {
    MultilinearMap.constOfIsEmpty R _
      m with
    toFun := Function.const _ m
    map_eq_zero_of_eq' := fun v => isEmptyElim }
#align alternating_map.const_of_is_empty AlternatingMap.constOfIsEmpty

end

/-- Restrict the codomain of an alternating map to a submodule. -/
@[simps]
def codRestrict (f : AlternatingMap R M N ι) (p : Submodule R N) (h : ∀ v, f v ∈ p) :
    AlternatingMap R M p ι :=
  {
    f.toMultilinearMap.codRestrict p
      h with
    toFun := fun v => ⟨f v, h v⟩
    map_eq_zero_of_eq' := fun v i j hv hij => Subtype.ext <| map_eq_zero_of_eq _ _ hv hij }
#align alternating_map.cod_restrict AlternatingMap.codRestrict

end AlternatingMap

/-!
### Composition with linear maps
-/


namespace LinearMap

variable {N₂ : Type _} [AddCommMonoid N₂] [Module R N₂]

/-- Composing a alternating map with a linear map on the left gives again an alternating map. -/
def compAlternatingMap (g : N →ₗ[R] N₂) : AlternatingMap R M N ι →+ AlternatingMap R M N₂ ι
    where
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
theorem coe_compAlternatingMap (g : N →ₗ[R] N₂) (f : AlternatingMap R M N ι) :
    ⇑(g.compAlternatingMap f) = g ∘ f :=
  rfl
#align linear_map.coe_comp_alternating_map LinearMap.coe_compAlternatingMap

@[simp]
theorem compAlternatingMap_apply (g : N →ₗ[R] N₂) (f : AlternatingMap R M N ι) (m : ι → M) :
    g.compAlternatingMap f m = g (f m) :=
  rfl
#align linear_map.comp_alternating_map_apply LinearMap.compAlternatingMap_apply

@[simp]
theorem subtype_compAlternatingMap_codRestrict (f : AlternatingMap R M N ι) (p : Submodule R N)
    (h) : p.Subtype.compAlternatingMap (f.codRestrict p h) = f :=
  AlternatingMap.ext fun v => rfl
#align linear_map.subtype_comp_alternating_map_cod_restrict LinearMap.subtype_compAlternatingMap_codRestrict

@[simp]
theorem compAlternatingMap_codRestrict (g : N →ₗ[R] N₂) (f : AlternatingMap R M N ι)
    (p : Submodule R N₂) (h) :
    (g.codRestrict p h).compAlternatingMap f =
      (g.compAlternatingMap f).codRestrict p fun v => h (f v) :=
  AlternatingMap.ext fun v => rfl
#align linear_map.comp_alternating_map_cod_restrict LinearMap.compAlternatingMap_codRestrict

end LinearMap

namespace AlternatingMap

variable {M₂ : Type _} [AddCommMonoid M₂] [Module R M₂]

variable {M₃ : Type _} [AddCommMonoid M₃] [Module R M₃]

/-- Composing a alternating map with the same linear map on each argument gives again an
alternating map. -/
def compLinearMap (f : AlternatingMap R M N ι) (g : M₂ →ₗ[R] M) : AlternatingMap R M₂ N ι :=
  { (f : MultilinearMap R (fun _ : ι => M) N).compLinearMap fun _ => g with
    map_eq_zero_of_eq' := fun v i j h hij => f.map_eq_zero_of_eq _ (LinearMap.congr_arg h) hij }
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
theorem zero_compLinearMap (g : M₂ →ₗ[R] M) : (0 : AlternatingMap R M N ι).compLinearMap g = 0 :=
  by
  ext
  simp only [comp_linear_map_apply, zero_apply]
#align alternating_map.zero_comp_linear_map AlternatingMap.zero_compLinearMap

@[simp]
theorem add_compLinearMap (f₁ f₂ : AlternatingMap R M N ι) (g : M₂ →ₗ[R] M) :
    (f₁ + f₂).compLinearMap g = f₁.compLinearMap g + f₂.compLinearMap g :=
  by
  ext
  simp only [comp_linear_map_apply, add_apply]
#align alternating_map.add_comp_linear_map AlternatingMap.add_compLinearMap

@[simp]
theorem compLinearMap_zero [Nonempty ι] (f : AlternatingMap R M N ι) :
    f.compLinearMap (0 : M₂ →ₗ[R] M) = 0 := by
  ext
  simp_rw [comp_linear_map_apply, LinearMap.zero_apply, ← Pi.zero_def, map_zero, zero_apply]
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
#align alternating_map.comp_linear_map_injective AlternatingMap.compLinearMap_injective

theorem compLinearMap_inj (f : M₂ →ₗ[R] M) (hf : Function.Surjective f)
    (g₁ g₂ : AlternatingMap R M N ι) : g₁.compLinearMap f = g₂.compLinearMap f ↔ g₁ = g₂ :=
  (compLinearMap_injective _ hf).eq_iff
#align alternating_map.comp_linear_map_inj AlternatingMap.compLinearMap_inj

section DomLcongr

variable (ι R N) (S : Type _) [Semiring S] [Module S N] [SMulCommClass R S N]

/-- Construct a linear equivalence between maps from a linear equivalence between domains. -/
@[simps apply]
def domLcongr (e : M ≃ₗ[R] M₂) : AlternatingMap R M N ι ≃ₗ[S] AlternatingMap R M₂ N ι
    where
  toFun f := f.compLinearMap e.symm
  invFun g := g.compLinearMap e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := AlternatingMap.ext fun v => f.congr_arg <| funext fun i => e.symm_apply_apply _
  right_inv f := AlternatingMap.ext fun v => f.congr_arg <| funext fun i => e.apply_symm_apply _
#align alternating_map.dom_lcongr AlternatingMap.domLcongr

@[simp]
theorem domLcongr_refl : domLcongr R N ι S (LinearEquiv.refl R M) = LinearEquiv.refl S _ :=
  LinearEquiv.ext fun _ => AlternatingMap.ext fun v => rfl
#align alternating_map.dom_lcongr_refl AlternatingMap.domLcongr_refl

@[simp]
theorem domLcongr_symm (e : M ≃ₗ[R] M₂) : (domLcongr R N ι S e).symm = domLcongr R N ι S e.symm :=
  rfl
#align alternating_map.dom_lcongr_symm AlternatingMap.domLcongr_symm

theorem domLcongr_trans (e : M ≃ₗ[R] M₂) (f : M₂ ≃ₗ[R] M₃) :
    (domLcongr R N ι S e).trans (domLcongr R N ι S f) = domLcongr R N ι S (e.trans f) :=
  rfl
#align alternating_map.dom_lcongr_trans AlternatingMap.domLcongr_trans

end DomLcongr

/-- Composing an alternating map with the same linear equiv on each argument gives the zero map
if and only if the alternating map is the zero map. -/
@[simp]
theorem comp_linearEquiv_eq_zero_iff (f : AlternatingMap R M N ι) (g : M₂ ≃ₗ[R] M) :
    f.compLinearMap (g : M₂ →ₗ[R] M) = 0 ↔ f = 0 :=
  (domLcongr R N ι ℕ g.symm).map_eq_zero_iff
#align alternating_map.comp_linear_equiv_eq_zero_iff AlternatingMap.comp_linearEquiv_eq_zero_iff

variable (f f' : AlternatingMap R M N ι)

variable (g g₂ : AlternatingMap R M N' ι)

variable (g' : AlternatingMap R M' N' ι)

variable (v : ι → M) (v' : ι → M')

open Function

/-!
### Other lemmas from `multilinear_map`
-/


section

open BigOperators

theorem map_update_sum {α : Type _} [DecidableEq ι] (t : Finset α) (i : ι) (g : α → M) (m : ι → M) :
    f (update m i (∑ a in t, g a)) = ∑ a in t, f (update m i (g a)) :=
  f.toMultilinearMap.map_update_sum t i g m
#align alternating_map.map_update_sum AlternatingMap.map_update_sum

end

/-!
### Theorems specific to alternating maps

Various properties of reordered and repeated inputs which follow from
`alternating_map.map_eq_zero_of_eq`.
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

theorem map_swap_add [DecidableEq ι] {i j : ι} (hij : i ≠ j) : f (v ∘ Equiv.swap i j) + f v = 0 :=
  by
  rw [Equiv.comp_swap_eq_update]
  convert f.map_update_update v hij (v i + v j)
  simp [f.map_update_self _ hij, f.map_update_self _ hij.symm,
    Function.update_comm hij (v i + v j) (v _) v, Function.update_comm hij.symm (v i) (v i) v]
#align alternating_map.map_swap_add AlternatingMap.map_swap_add

theorem map_add_swap [DecidableEq ι] {i j : ι} (hij : i ≠ j) : f v + f (v ∘ Equiv.swap i j) = 0 :=
  by
  rw [add_comm]
  exact f.map_swap_add v hij
#align alternating_map.map_add_swap AlternatingMap.map_add_swap

theorem map_swap [DecidableEq ι] {i j : ι} (hij : i ≠ j) : g (v ∘ Equiv.swap i j) = -g v :=
  eq_neg_of_add_eq_zero_left <| g.map_swap_add v hij
#align alternating_map.map_swap AlternatingMap.map_swap

theorem map_perm [DecidableEq ι] [Fintype ι] (v : ι → M) (σ : Equiv.Perm ι) :
    g (v ∘ σ) = σ.sign • g v :=
  by
  apply Equiv.Perm.swap_induction_on' σ
  · simp
  · intro s x y hxy hI
    simpa [g.map_swap (v ∘ s) hxy, Equiv.Perm.sign_swap hxy] using hI
#align alternating_map.map_perm AlternatingMap.map_perm

theorem map_congr_perm [DecidableEq ι] [Fintype ι] (σ : Equiv.Perm ι) : g v = σ.sign • g (v ∘ σ) :=
  by
  rw [g.map_perm, smul_smul]
  simp
#align alternating_map.map_congr_perm AlternatingMap.map_congr_perm

section DomDomCongr

/-- Transfer the arguments to a map along an equivalence between argument indices.

This is the alternating version of `multilinear_map.dom_dom_congr`. -/
@[simps]
def domDomCongr (σ : ι ≃ ι') (f : AlternatingMap R M N ι) : AlternatingMap R M N ι' :=
  {
    f.toMultilinearMap.domDomCongr
      σ with
    toFun := fun v => f (v ∘ σ)
    map_eq_zero_of_eq' := fun v i j hv hij =>
      f.map_eq_zero_of_eq (v ∘ σ) (by simpa using hv) (σ.symm.Injective.Ne hij) }
#align alternating_map.dom_dom_congr AlternatingMap.domDomCongr

@[simp]
theorem domDomCongr_refl (f : AlternatingMap R M N ι) : f.domDomCongr (Equiv.refl ι) = f :=
  ext fun v => rfl
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

/-- `alternating_map.dom_dom_congr` as an equivalence.

This is declared separately because it does not work with dot notation. -/
@[simps apply symm_apply]
def domDomCongrEquiv (σ : ι ≃ ι') : AlternatingMap R M N ι ≃+ AlternatingMap R M N ι'
    where
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

/-- The results of applying `dom_dom_congr` to two maps are equal if and only if those maps are. -/
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
    g.domDomCongr σ = σ.sign • g :=
  AlternatingMap.ext fun v => g.map_perm v σ
#align alternating_map.dom_dom_congr_perm AlternatingMap.domDomCongr_perm

@[norm_cast]
theorem coe_domDomCongr (σ : ι ≃ ι') :
    ↑(f.domDomCongr σ) = (f : MultilinearMap R (fun _ : ι => M) N).domDomCongr σ :=
  MultilinearMap.ext fun v => rfl
#align alternating_map.coe_dom_dom_congr AlternatingMap.coe_domDomCongr

end DomDomCongr

/-- If the arguments are linearly dependent then the result is `0`. -/
theorem map_linear_dependent {K : Type _} [Ring K] {M : Type _} [AddCommGroup M] [Module K M]
    {N : Type _} [AddCommGroup N] [Module K N] [NoZeroSMulDivisors K N] (f : AlternatingMap K M N ι)
    (v : ι → M) (h : ¬LinearIndependent K v) : f v = 0 :=
  by
  obtain ⟨s, g, h, i, hi, hz⟩ := not_linear_independent_iff.mp h
  letI := Classical.decEq ι
  suffices f (update v i (g i • v i)) = 0
    by
    rw [f.map_smul, Function.update_eq_self, smul_eq_zero] at this
    exact Or.resolve_left this hz
  conv at h in g _ • v _ => rw [← if_t_t (i = x) (g _ • v _)]
  rw [Finset.sum_ite, Finset.filter_eq, Finset.filter_ne, if_pos hi, Finset.sum_singleton,
    add_eq_zero_iff_eq_neg] at h
  rw [h, f.map_neg, f.map_update_sum, neg_eq_zero, Finset.sum_eq_zero]
  intro j hj
  obtain ⟨hij, _⟩ := finset.mem_erase.mp hj
  rw [f.map_smul, f.map_update_self _ hij.symm, smul_zero]
#align alternating_map.map_linear_dependent AlternatingMap.map_linear_dependent

section Fin

open Fin

/-- A version of `multilinear_map.cons_add` for `alternating_map`. -/
theorem map_vecCons_add {n : ℕ} (f : AlternatingMap R M N (Fin n.succ)) (m : Fin n → M) (x y : M) :
    f (Matrix.vecCons (x + y) m) = f (Matrix.vecCons x m) + f (Matrix.vecCons y m) :=
  f.toMultilinearMap.cons_add _ _ _
#align alternating_map.map_vec_cons_add AlternatingMap.map_vecCons_add

/-- A version of `multilinear_map.cons_smul` for `alternating_map`. -/
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

private theorem alternization_map_eq_zero_of_eq_aux (m : MultilinearMap R (fun i : ι => M) N')
    (v : ι → M) (i j : ι) (i_ne_j : i ≠ j) (hv : v i = v j) :
    (∑ σ : Perm ι, σ.sign • m.domDomCongr σ) v = 0 :=
  by
  rw [sum_apply]
  exact
    Finset.sum_involution (fun σ _ => swap i j * σ)
      (fun σ _ => by simp [perm.sign_swap i_ne_j, apply_swap_eq_self hv])
      (fun σ _ _ => (not_congr swap_mul_eq_iff).mpr i_ne_j) (fun σ _ => Finset.mem_univ _)
      fun σ _ => swap_mul_involutive i j σ
#align multilinear_map.alternization_map_eq_zero_of_eq_aux multilinear_map.alternization_map_eq_zero_of_eq_aux

/-- Produce an `alternating_map` out of a `multilinear_map`, by summing over all argument
permutations. -/
def alternatization : MultilinearMap R (fun i : ι => M) N' →+ AlternatingMap R M N' ι
    where
  toFun m :=
    {
      ∑ σ : Perm ι,
        σ.sign •
          m.domDomCongr
            σ with
      toFun := ⇑(∑ σ : Perm ι, σ.sign • m.domDomCongr σ)
      map_eq_zero_of_eq' := fun v i j hvij hij =>
        alternization_map_eq_zero_of_eq_aux m v i j hij hvij }
  map_add' a b := by
    ext
    simp only [Finset.sum_add_distrib, smul_add, add_apply, dom_dom_congr_apply,
      AlternatingMap.add_apply, AlternatingMap.coe_mk, smul_apply, sum_apply]
  map_zero' := by
    ext
    simp only [Finset.sum_const_zero, smul_zero, zero_apply, dom_dom_congr_apply,
      AlternatingMap.zero_apply, AlternatingMap.coe_mk, smul_apply, sum_apply]
#align multilinear_map.alternatization MultilinearMap.alternatization

theorem alternatization_def (m : MultilinearMap R (fun i : ι => M) N') :
    ⇑(alternatization m) = (∑ σ : Perm ι, σ.sign • m.domDomCongr σ : _) :=
  rfl
#align multilinear_map.alternatization_def MultilinearMap.alternatization_def

theorem alternatization_coe (m : MultilinearMap R (fun i : ι => M) N') :
    ↑m.alternatization = (∑ σ : Perm ι, σ.sign • m.domDomCongr σ : _) :=
  coe_injective rfl
#align multilinear_map.alternatization_coe MultilinearMap.alternatization_coe

theorem alternatization_apply (m : MultilinearMap R (fun i : ι => M) N') (v : ι → M) :
    alternatization m v = ∑ σ : Perm ι, σ.sign • m.domDomCongr σ v := by
  simp only [alternatization_def, smul_apply, sum_apply]
#align multilinear_map.alternatization_apply MultilinearMap.alternatization_apply

end MultilinearMap

namespace AlternatingMap

/-- Alternatizing a multilinear map that is already alternating results in a scale factor of `n!`,
where `n` is the number of inputs. -/
theorem coe_alternatization [DecidableEq ι] [Fintype ι] (a : AlternatingMap R M N' ι) :
    (↑a : MultilinearMap R (fun ι => M) N').alternatization = Nat.factorial (Fintype.card ι) • a :=
  by
  apply AlternatingMap.coe_injective
  simp_rw [MultilinearMap.alternatization_def, ← coe_dom_dom_congr, dom_dom_congr_perm, coe_smul,
    smul_smul, Int.units_mul_self, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    ← coe_multilinear_map, coe_smul]
#align alternating_map.coe_alternatization AlternatingMap.coe_alternatization

end AlternatingMap

namespace LinearMap

variable {N'₂ : Type _} [AddCommGroup N'₂] [Module R N'₂] [DecidableEq ι] [Fintype ι]

/-- Composition with a linear map before and after alternatization are equivalent. -/
theorem compMultilinearMap_alternatization (g : N' →ₗ[R] N'₂)
    (f : MultilinearMap R (fun _ : ι => M) N') :
    (g.compMultilinearMap f).alternatization = g.compAlternatingMap f.alternatization :=
  by
  ext
  simp [MultilinearMap.alternatization_def]
#align linear_map.comp_multilinear_map_alternatization LinearMap.compMultilinearMap_alternatization

end LinearMap

section Coprod

open BigOperators

open TensorProduct

variable {ιa ιb : Type _} [Fintype ιa] [Fintype ιb]

variable {R' : Type _} {Mᵢ N₁ N₂ : Type _} [CommSemiring R'] [AddCommGroup N₁] [Module R' N₁]
  [AddCommGroup N₂] [Module R' N₂] [AddCommMonoid Mᵢ] [Module R' Mᵢ]

namespace Equiv.Perm

/-- Elements which are considered equivalent if they differ only by swaps within α or β  -/
abbrev ModSumCongr (α β : Type _) :=
  _ ⧸ (Equiv.Perm.sumCongrHom α β).range
#align equiv.perm.mod_sum_congr Equiv.Perm.ModSumCongr

theorem ModSumCongr.swap_smul_involutive {α β : Type _} [DecidableEq (Sum α β)] (i j : Sum α β) :
    Function.Involutive (SMul.smul (Equiv.swap i j) : ModSumCongr α β → ModSumCongr α β) := fun σ =>
  by
  apply σ.induction_on' fun σ => _
  exact _root_.congr_arg Quotient.mk'' (Equiv.swap_mul_involutive i j σ)
#align equiv.perm.mod_sum_congr.swap_smul_involutive Equiv.Perm.ModSumCongr.swap_smul_involutive

end Equiv.Perm

namespace AlternatingMap

open Equiv

variable [DecidableEq ιa] [DecidableEq ιb]

/-- summand used in `alternating_map.dom_coprod` -/
def DomCoprod.summand (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb)
    (σ : Perm.ModSumCongr ιa ιb) : MultilinearMap R' (fun _ : Sum ιa ιb => Mᵢ) (N₁ ⊗[R'] N₂) :=
  Quotient.liftOn' σ
    (fun σ =>
      σ.sign •
        (MultilinearMap.domCoprod ↑a ↑b : MultilinearMap R' (fun _ => Mᵢ) (N₁ ⊗ N₂)).domDomCongr σ)
    fun σ₁ σ₂ H => by
    rw [QuotientGroup.leftRel_apply] at H
    obtain ⟨⟨sl, sr⟩, h⟩ := H
    ext v
    simp only [MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
      coe_multilinear_map, MultilinearMap.smul_apply]
    replace h := inv_mul_eq_iff_eq_mul.mp h.symm
    have : (σ₁ * perm.sum_congr_hom _ _ (sl, sr)).sign = σ₁.sign * (sl.sign * sr.sign) := by simp
    rw [h, this, mul_smul, mul_smul, smul_left_cancel_iff, ← TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
    simp only [Sum.map_inr, perm.sum_congr_hom_apply, perm.sum_congr_apply, Sum.map_inl,
      Function.comp_apply, perm.coe_mul]
    rw [← a.map_congr_perm fun i => v (σ₁ _), ← b.map_congr_perm fun i => v (σ₁ _)]
#align alternating_map.dom_coprod.summand AlternatingMap.DomCoprod.summand

theorem DomCoprod.summand_mk'' (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb)
    (σ : Equiv.Perm (Sum ιa ιb)) :
    DomCoprod.summand a b (Quotient.mk'' σ) =
      σ.sign •
        (MultilinearMap.domCoprod ↑a ↑b : MultilinearMap R' (fun _ => Mᵢ) (N₁ ⊗ N₂)).domDomCongr
          σ :=
  rfl
#align alternating_map.dom_coprod.summand_mk' AlternatingMap.DomCoprod.summand_mk''

/-- Swapping elements in `σ` with equal values in `v` results in an addition that cancels -/
theorem DomCoprod.summand_add_swap_smul_eq_zero (a : AlternatingMap R' Mᵢ N₁ ιa)
    (b : AlternatingMap R' Mᵢ N₂ ιb) (σ : Perm.ModSumCongr ιa ιb) {v : Sum ιa ιb → Mᵢ}
    {i j : Sum ιa ιb} (hv : v i = v j) (hij : i ≠ j) :
    DomCoprod.summand a b σ v + DomCoprod.summand a b (swap i j • σ) v = 0 :=
  by
  apply σ.induction_on' fun σ => _
  dsimp only [Quotient.liftOn'_mk'', Quotient.map'_mk'', MulAction.Quotient.smul_mk,
    dom_coprod.summand]
  rw [smul_eq_mul, perm.sign_mul, perm.sign_swap hij]
  simp only [one_mul, neg_mul, Function.comp_apply, Units.neg_smul, perm.coe_mul, Units.val_neg,
    MultilinearMap.smul_apply, MultilinearMap.neg_apply, MultilinearMap.domDomCongr_apply,
    MultilinearMap.domCoprod_apply]
  convert add_right_neg _ <;>
    · ext k
      rw [Equiv.apply_swap_eq_self hv]
#align alternating_map.dom_coprod.summand_add_swap_smul_eq_zero AlternatingMap.DomCoprod.summand_add_swap_smul_eq_zero

/-- Swapping elements in `σ` with equal values in `v` result in zero if the swap has no effect
on the quotient. -/
theorem DomCoprod.summand_eq_zero_of_smul_invariant (a : AlternatingMap R' Mᵢ N₁ ιa)
    (b : AlternatingMap R' Mᵢ N₂ ιb) (σ : Perm.ModSumCongr ιa ιb) {v : Sum ιa ιb → Mᵢ}
    {i j : Sum ιa ιb} (hv : v i = v j) (hij : i ≠ j) :
    swap i j • σ = σ → DomCoprod.summand a b σ v = 0 :=
  by
  apply σ.induction_on' fun σ => _
  dsimp only [Quotient.liftOn'_mk'', Quotient.map'_mk'', MultilinearMap.smul_apply,
    MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply, dom_coprod.summand]
  intro hσ
  cases hi : σ⁻¹ i <;> cases hj : σ⁻¹ j <;> rw [perm.inv_eq_iff_eq] at hi hj <;> substs hi hj <;>
    revert val val_1
  case inl.inr |
    inr.inl =>
    -- the term pairs with and cancels another term
    all_goals
      intro i' j' hv hij hσ
      obtain ⟨⟨sl, sr⟩, hσ⟩ := quotient_group.left_rel_apply.mp (Quotient.exact' hσ)
    on_goal 1 => replace hσ := Equiv.congr_fun hσ (Sum.inl i')
    on_goal 2 => replace hσ := Equiv.congr_fun hσ (Sum.inr i')
    all_goals
      rw [smul_eq_mul, ← mul_swap_eq_swap_mul, mul_inv_rev, swap_inv, inv_mul_cancel_right] at hσ
      simpa using hσ
  case inr.inr |
    inl.inl =>
    -- the term does not pair but is zero
    all_goals
      intro i' j' hv hij hσ
      convert smul_zero _
    on_goal 1 => convert TensorProduct.tmul_zero _ _
    on_goal 2 => convert TensorProduct.zero_tmul _ _
    all_goals exact AlternatingMap.map_eq_zero_of_eq _ _ hv fun hij' => hij (hij' ▸ rfl)
#align alternating_map.dom_coprod.summand_eq_zero_of_smul_invariant AlternatingMap.DomCoprod.summand_eq_zero_of_smul_invariant

/-- Like `multilinear_map.dom_coprod`, but ensures the result is also alternating.

Note that this is usually defined (for instance, as used in Proposition 22.24 in [Gallier2011Notes])
over integer indices `ιa = fin n` and `ιb = fin m`, as
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
* the additions in the subscripts of $\sigma$ with an index of type `sum`

The specialized version can be obtained by combining this definition with `fin_sum_fin_equiv` and
`linear_map.mul'`.
-/
@[simps]
def domCoprod (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb) :
    AlternatingMap R' Mᵢ (N₁ ⊗[R'] N₂) (Sum ιa ιb) :=
  {
    ∑ σ : Perm.ModSumCongr ιa ιb,
      DomCoprod.summand a b
        σ with
    toFun := fun v => (⇑(∑ σ : Perm.ModSumCongr ιa ιb, DomCoprod.summand a b σ)) v
    map_eq_zero_of_eq' := fun v i j hv hij => by
      dsimp only
      rw [MultilinearMap.sum_apply]
      exact
        Finset.sum_involution (fun σ _ => Equiv.swap i j • σ)
          (fun σ _ => dom_coprod.summand_add_swap_smul_eq_zero a b σ hv hij)
          (fun σ _ => mt <| dom_coprod.summand_eq_zero_of_smul_invariant a b σ hv hij)
          (fun σ _ => Finset.mem_univ _) fun σ _ =>
          Equiv.Perm.ModSumCongr.swap_smul_involutive i j σ }
#align alternating_map.dom_coprod AlternatingMap.domCoprod

theorem domCoprod_coe (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb) :
    (↑(a.domCoprod b) : MultilinearMap R' (fun _ => Mᵢ) _) =
      ∑ σ : Perm.ModSumCongr ιa ιb, DomCoprod.summand a b σ :=
  MultilinearMap.ext fun _ => rfl
#align alternating_map.dom_coprod_coe AlternatingMap.domCoprod_coe

/-- A more bundled version of `alternating_map.dom_coprod` that maps
`((ι₁ → N) → N₁) ⊗ ((ι₂ → N) → N₂)` to `(ι₁ ⊕ ι₂ → N) → N₁ ⊗ N₂`. -/
def domCoprod' :
    AlternatingMap R' Mᵢ N₁ ιa ⊗[R'] AlternatingMap R' Mᵢ N₂ ιb →ₗ[R']
      AlternatingMap R' Mᵢ (N₁ ⊗[R'] N₂) (Sum ιa ιb) :=
  TensorProduct.lift <| by
    refine'
        LinearMap.mk₂ R' dom_coprod (fun m₁ m₂ n => _) (fun c m n => _) (fun m n₁ n₂ => _)
          fun c m n => _ <;>
      · ext
        simp only [dom_coprod_apply, add_apply, smul_apply, ← Finset.sum_add_distrib,
          Finset.smul_sum, MultilinearMap.sum_apply, dom_coprod.summand]
        congr
        ext σ
        apply σ.induction_on' fun σ => _
        simp only [Quotient.liftOn'_mk'', coe_add, coe_smul, MultilinearMap.smul_apply, ←
          MultilinearMap.domCoprod'_apply]
        simp only [TensorProduct.add_tmul, ← TensorProduct.smul_tmul', TensorProduct.tmul_add,
          TensorProduct.tmul_smul, LinearMap.map_add, LinearMap.map_smul]
        first |rw [← smul_add]|rw [smul_comm]
        congr
#align alternating_map.dom_coprod' AlternatingMap.domCoprod'

@[simp]
theorem domCoprod'_apply (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb) :
    domCoprod' (a ⊗ₜ[R'] b) = domCoprod a b :=
  rfl
#align alternating_map.dom_coprod'_apply AlternatingMap.domCoprod'_apply

end AlternatingMap

open Equiv

/-- A helper lemma for `multilinear_map.dom_coprod_alternization`. -/
theorem MultilinearMap.domCoprod_alternization_coe [DecidableEq ιa] [DecidableEq ιb]
    (a : MultilinearMap R' (fun _ : ιa => Mᵢ) N₁) (b : MultilinearMap R' (fun _ : ιb => Mᵢ) N₂) :
    MultilinearMap.domCoprod ↑a.alternatization ↑b.alternatization =
      ∑ (σa : Perm ιa) (σb : Perm ιb),
        σa.sign • σb.sign • MultilinearMap.domCoprod (a.domDomCongr σa) (b.domDomCongr σb) :=
  by
  simp_rw [← MultilinearMap.domCoprod'_apply, MultilinearMap.alternatization_coe]
  simp_rw [TensorProduct.sum_tmul, TensorProduct.tmul_sum, LinearMap.map_sum, ←
    TensorProduct.smul_tmul', TensorProduct.tmul_smul, LinearMap.map_smul_of_tower]
#align multilinear_map.dom_coprod_alternization_coe MultilinearMap.domCoprod_alternization_coe

open AlternatingMap

/-- Computing the `multilinear_map.alternatization` of the `multilinear_map.dom_coprod` is the same
as computing the `alternating_map.dom_coprod` of the `multilinear_map.alternatization`s.
-/
theorem MultilinearMap.domCoprod_alternization [DecidableEq ιa] [DecidableEq ιb]
    (a : MultilinearMap R' (fun _ : ιa => Mᵢ) N₁) (b : MultilinearMap R' (fun _ : ιb => Mᵢ) N₂) :
    (MultilinearMap.domCoprod a b).alternatization =
      a.alternatization.domCoprod b.alternatization :=
  by
  apply coe_multilinear_map_injective
  rw [dom_coprod_coe, MultilinearMap.alternatization_coe,
    Finset.sum_partition (QuotientGroup.leftRel (perm.sum_congr_hom ιa ιb).range)]
  congr 1
  ext1 σ
  apply σ.induction_on' fun σ => _
  -- unfold the quotient mess left by `finset.sum_partition`
  conv in _ = Quotient.mk'' _ =>
    change Quotient.mk'' _ = Quotient.mk'' _
    rw [QuotientGroup.eq']
  -- eliminate a multiplication
  rw [← Finset.map_univ_equiv (Equiv.mulLeft σ), Finset.filter_map, Finset.sum_map]
  simp_rw [Equiv.coe_toEmbedding, Equiv.coe_mulLeft, (· ∘ ·), mul_inv_rev, inv_mul_cancel_right,
    Subgroup.inv_mem_iff, MonoidHom.mem_range, Finset.univ_filter_exists,
    Finset.sum_image (perm.sum_congr_hom_injective.inj_on _)]
  -- now we're ready to clean up the RHS, pulling out the summation
  rw [dom_coprod.summand_mk', MultilinearMap.domCoprod_alternization_coe, ← Finset.sum_product',
    Finset.univ_product_univ, ← MultilinearMap.domDomCongrEquiv_apply, AddEquiv.map_sum,
    Finset.smul_sum]
  congr 1
  ext1 ⟨al, ar⟩
  dsimp only
  -- pull out the pair of smuls on the RHS, by rewriting to `_ →ₗ[ℤ] _` and back
  rw [← AddEquiv.coe_toAddMonoidHom, ← AddMonoidHom.coe_toIntLinearMap, LinearMap.map_smul_of_tower,
    LinearMap.map_smul_of_tower, AddMonoidHom.coe_toIntLinearMap, AddEquiv.coe_toAddMonoidHom,
    MultilinearMap.domDomCongrEquiv_apply]
  -- pick up the pieces
  rw [MultilinearMap.domDomCongr_mul, perm.sign_mul, perm.sum_congr_hom_apply,
    MultilinearMap.domCoprod_domDomCongr_sumCongr, perm.sign_sum_congr, mul_smul, mul_smul]
#align multilinear_map.dom_coprod_alternization MultilinearMap.domCoprod_alternization

/-- Taking the `multilinear_map.alternatization` of the `multilinear_map.dom_coprod` of two
`alternating_map`s gives a scaled version of the `alternating_map.coprod` of those maps.
-/
theorem MultilinearMap.domCoprod_alternization_eq [DecidableEq ιa] [DecidableEq ιb]
    (a : AlternatingMap R' Mᵢ N₁ ιa) (b : AlternatingMap R' Mᵢ N₂ ιb) :
    (MultilinearMap.domCoprod a b :
          MultilinearMap R' (fun _ : Sum ιa ιb => Mᵢ) (N₁ ⊗ N₂)).alternatization =
      ((Fintype.card ιa).factorial * (Fintype.card ιb).factorial) • a.domCoprod b :=
  by
  rw [MultilinearMap.domCoprod_alternization, coe_alternatization, coe_alternatization, mul_smul, ←
    dom_coprod'_apply, ← dom_coprod'_apply, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    LinearMap.map_smul_of_tower dom_coprod', LinearMap.map_smul_of_tower dom_coprod']
  -- typeclass resolution is a little confused here
  infer_instance;
  infer_instance
#align multilinear_map.dom_coprod_alternization_eq MultilinearMap.domCoprod_alternization_eq

end Coprod

section Basis

open AlternatingMap

variable {ι₁ : Type _} [Finite ι]

variable {R' : Type _} {N₁ N₂ : Type _} [CommSemiring R'] [AddCommMonoid N₁] [AddCommMonoid N₂]

variable [Module R' N₁] [Module R' N₂]

/-- Two alternating maps indexed by a `fintype` are equal if they are equal when all arguments
are distinct basis vectors. -/
theorem Basis.ext_alternating {f g : AlternatingMap R' N₁ N₂ ι} (e : Basis ι₁ R' N₁)
    (h : ∀ v : ι → ι₁, Function.Injective v → (f fun i => e (v i)) = g fun i => e (v i)) : f = g :=
  by
  classical
    refine' AlternatingMap.coe_multilinearMap_injective (Basis.ext_multilinear e fun v => _)
    by_cases hi : Function.Injective v
    · exact h v hi
    · have : ¬Function.Injective fun i => e (v i) := hi.imp Function.Injective.of_comp
      rw [coe_multilinear_map, coe_multilinear_map, f.map_eq_zero_of_not_injective _ this,
        g.map_eq_zero_of_not_injective _ this]
#align basis.ext_alternating Basis.ext_alternating

end Basis

/-! ### Currying -/


section Currying

variable {R' : Type _} {M'' M₂'' N'' N₂'' : Type _} [CommSemiring R'] [AddCommMonoid M'']
  [AddCommMonoid M₂''] [AddCommMonoid N''] [AddCommMonoid N₂''] [Module R' M''] [Module R' M₂'']
  [Module R' N''] [Module R' N₂'']

namespace AlternatingMap

/-- Given an alternating map `f` in `n+1` variables, split the first variable to obtain
a linear map into alternating maps in `n` variables, given by `x ↦ (m ↦ f (matrix.vec_cons x m))`.
It can be thought of as a map $Hom(\bigwedge^{n+1} M, N) \to Hom(M, Hom(\bigwedge^n M, N))$.

This is `multilinear_map.curry_left` for `alternating_map`. See also
`alternating_map.curry_left_linear_map`. -/
@[simps]
def curryLeft {n : ℕ} (f : AlternatingMap R' M'' N'' (Fin n.succ)) :
    M'' →ₗ[R'] AlternatingMap R' M'' N'' (Fin n)
    where
  toFun m :=
    {
      f.toMultilinearMap.curryLeft
        m with
      toFun := fun v => f (Matrix.vecCons m v)
      map_eq_zero_of_eq' := fun v i j hv hij =>
        f.map_eq_zero_of_eq _ (by rwa [Matrix.cons_val_succ, Matrix.cons_val_succ])
          ((Fin.succ_injective _).Ne hij) }
  map_add' m₁ m₂ := ext fun v => f.map_vecCons_add _ _ _
  map_smul' r m := ext fun v => f.map_vecCons_smul _ _ _
#align alternating_map.curry_left AlternatingMap.curryLeft

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

/-- `alternating_map.curry_left` as a `linear_map`. This is a separate definition as dot notation
does not work for this version. -/
@[simps]
def curryLeftLinearMap {n : ℕ} :
    AlternatingMap R' M'' N'' (Fin n.succ) →ₗ[R'] M'' →ₗ[R'] AlternatingMap R' M'' N'' (Fin n)
    where
  toFun f := f.curryLeft
  map_add' := curryLeft_add
  map_smul' := curryLeft_smul
#align alternating_map.curry_left_linear_map AlternatingMap.curryLeftLinearMap

/-- Currying with the same element twice gives the zero map. -/
@[simp]
theorem curryLeft_same {n : ℕ} (f : AlternatingMap R' M'' N'' (Fin n.succ.succ)) (m : M'') :
    (f.curryLeft m).curryLeft m = 0 :=
  ext fun x => f.map_eq_zero_of_eq _ (by simp) Fin.zero_ne_one
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
        · rfl
        · simp
#align alternating_map.curry_left_comp_linear_map AlternatingMap.curryLeft_compLinearMap

/-- The space of constant maps is equivalent to the space of maps that are alternating with respect
to an empty family. -/
@[simps]
def constLinearEquivOfIsEmpty [IsEmpty ι] : N'' ≃ₗ[R'] AlternatingMap R' M'' N'' ι
    where
  toFun := AlternatingMap.constOfIsEmpty R' M''
  map_add' x y := rfl
  map_smul' t x := rfl
  invFun f := f 0
  left_inv _ := rfl
  right_inv f := ext fun x => AlternatingMap.congr_arg f <| Subsingleton.elim _ _
#align alternating_map.const_linear_equiv_of_is_empty AlternatingMap.constLinearEquivOfIsEmpty

end AlternatingMap

end Currying

