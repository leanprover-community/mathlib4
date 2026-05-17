/-
Copyright (c) 2020 Zhangir Azerbayev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Zhangir Azerbayev
-/
module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basis


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
* `AlternatingMap.domDomCongr`, for permuting the elements within a family.
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

@[expose] public section

open Module

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
  coe_injective' f g h := by
    rcases f with ⟨⟨_, _, _⟩, _⟩
    rcases g with ⟨⟨_, _, _⟩, _⟩
    congr

initialize_simps_projections AlternatingMap (toFun → apply)

@[simp]
theorem toFun_eq_coe : f.toFun = f :=
  rfl

@[simp]
theorem coe_mk (f : MultilinearMap R (fun _ : ι => M) N) (h) :
    ⇑(⟨f, h⟩ : M [⋀^ι]→ₗ[R] N) = f :=
  rfl

protected theorem congr_fun {f g : M [⋀^ι]→ₗ[R] N} (h : f = g) (x : ι → M) : f x = g x :=
  congr_arg (fun h : M [⋀^ι]→ₗ[R] N => h x) h

protected theorem congr_arg (f : M [⋀^ι]→ₗ[R] N) {x y : ι → M} (h : x = y) : f x = f y :=
  congr_arg (fun x : ι → M => f x) h

theorem coe_injective : Injective ((↑) : M [⋀^ι]→ₗ[R] N → (ι → M) → N) :=
  DFunLike.coe_injective

@[norm_cast]
theorem coe_inj {f g : M [⋀^ι]→ₗ[R] N} : (f : (ι → M) → N) = g ↔ f = g :=
  coe_injective.eq_iff

@[ext]
theorem ext {f f' : M [⋀^ι]→ₗ[R] N} (H : ∀ x, f x = f' x) : f = f' :=
  DFunLike.ext _ _ H

attribute [coe] AlternatingMap.toMultilinearMap

instance instCoe : Coe (M [⋀^ι]→ₗ[R] N) (MultilinearMap R (fun _ : ι => M) N) :=
  ⟨fun x => x.toMultilinearMap⟩

@[simp, norm_cast]
theorem coe_multilinearMap : ⇑(f : MultilinearMap R (fun _ : ι => M) N) = f :=
  rfl

theorem coe_multilinearMap_injective :
    Function.Injective ((↑) : M [⋀^ι]→ₗ[R] N → MultilinearMap R (fun _ : ι => M) N) :=
  fun _ _ h => ext <| MultilinearMap.congr_fun h

theorem coe_multilinearMap_mk (f : (ι → M) → N) (h₁ h₂ h₃) :
    ((⟨⟨f, h₁, h₂⟩, h₃⟩ : M [⋀^ι]→ₗ[R] N) : MultilinearMap R (fun _ : ι => M) N) =
      ⟨f, @h₁, @h₂⟩ := by
  simp

end Coercions

/-!
### Simp-normal forms of the structure fields

These are expressed in terms of `⇑f` instead of `f.toFun`.
-/


@[simp]
theorem map_update_add [DecidableEq ι] (i : ι) (x y : M) :
    f (update v i (x + y)) = f (update v i x) + f (update v i y) :=
  f.map_update_add' v i x y

@[simp]
theorem map_update_sub [DecidableEq ι] (i : ι) (x y : M') :
    g' (update v' i (x - y)) = g' (update v' i x) - g' (update v' i y) :=
  g'.toMultilinearMap.map_update_sub v' i x y

@[simp]
theorem map_update_neg [DecidableEq ι] (i : ι) (x : M') :
    g' (update v' i (-x)) = -g' (update v' i x) :=
  g'.toMultilinearMap.map_update_neg v' i x

@[simp]
theorem map_update_smul [DecidableEq ι] (i : ι) (r : R) (x : M) :
    f (update v i (r • x)) = r • f (update v i x) :=
  f.map_update_smul' v i r x

-- Cannot be @[simp] because `i` and `j` cannot be inferred by `simp`.
theorem map_eq_zero_of_eq (v : ι → M) {i j : ι} (h : v i = v j) (hij : i ≠ j) : f v = 0 :=
  f.map_eq_zero_of_eq' v i j h hij

theorem map_coord_zero {m : ι → M} (i : ι) (h : m i = 0) : f m = 0 :=
  f.toMultilinearMap.map_coord_zero i h

@[simp]
theorem map_update_zero [DecidableEq ι] (m : ι → M) (i : ι) : f (update m i 0) = 0 :=
  f.toMultilinearMap.map_update_zero m i

@[simp]
theorem map_zero [Nonempty ι] : f 0 = 0 :=
  f.toMultilinearMap.map_zero

theorem map_eq_zero_of_not_injective (v : ι → M) (hv : ¬Function.Injective v) : f v = 0 := by
  rw [Function.Injective] at hv
  push Not at hv
  rcases hv with ⟨i₁, i₂, heq, hne⟩
  exact f.map_eq_zero_of_eq v heq hne

/-!
### Algebraic structure inherited from `MultilinearMap`

`AlternatingMap` carries the same `AddCommMonoid`, `AddCommGroup`, and `Module` structure
as `MultilinearMap`
-/


section SMul

variable {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]

instance instSMul : SMul S (M [⋀^ι]→ₗ[R] N) :=
  ⟨fun c f =>
    { c • (f : MultilinearMap R (fun _ : ι => M) N) with
      map_eq_zero_of_eq' := fun v i j h hij => by simp [f.map_eq_zero_of_eq v h hij] }⟩

@[simp]
theorem smul_apply (c : S) (m : ι → M) : (c • f) m = c • f m :=
  rfl

@[norm_cast]
theorem coe_smul (c : S) : ↑(c • f) = c • (f : MultilinearMap R (fun _ : ι => M) N) :=
  rfl

theorem coeFn_smul (c : S) (f : M [⋀^ι]→ₗ[R] N) : ⇑(c • f) = c • ⇑f :=
  rfl

instance instSMulCommClass {T : Type*} [Monoid T] [DistribMulAction T N] [SMulCommClass R T N]
    [SMulCommClass S T N] : SMulCommClass S T (M [⋀^ι]→ₗ[R] N) where
  smul_comm _ _ _ := ext fun _ ↦ smul_comm ..

instance instIsCentralScalar [DistribMulAction Sᵐᵒᵖ N] [IsCentralScalar S N] :
    IsCentralScalar S (M [⋀^ι]→ₗ[R] N) :=
  ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩

end SMul

/-- The Cartesian product of two alternating maps, as an alternating map. -/
@[simps!]
def prod (f : M [⋀^ι]→ₗ[R] N) (g : M [⋀^ι]→ₗ[R] P) : M [⋀^ι]→ₗ[R] (N × P) :=
  { f.toMultilinearMap.prod g.toMultilinearMap with
    map_eq_zero_of_eq' := fun _ _ _ h hne =>
      Prod.ext (f.map_eq_zero_of_eq _ h hne) (g.map_eq_zero_of_eq _ h hne) }

@[simp]
theorem coe_prod (f : M [⋀^ι]→ₗ[R] N) (g : M [⋀^ι]→ₗ[R] P) :
    (f.prod g : MultilinearMap R (fun _ : ι => M) (N × P)) = MultilinearMap.prod f g :=
  rfl

/-- Combine a family of alternating maps with the same domain and codomains `N i` into an
alternating map taking values in the space of functions `Π i, N i`. -/
@[simps!]
def pi {ι' : Type*} {N : ι' → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M [⋀^ι]→ₗ[R] N i) : M [⋀^ι]→ₗ[R] (∀ i, N i) :=
  { MultilinearMap.pi fun a => (f a).toMultilinearMap with
    map_eq_zero_of_eq' := fun _ _ _ h hne => funext fun a => (f a).map_eq_zero_of_eq _ h hne }

@[simp]
theorem coe_pi {ι' : Type*} {N : ι' → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M [⋀^ι]→ₗ[R] N i) :
    (pi f : MultilinearMap R (fun _ : ι => M) (∀ i, N i)) = MultilinearMap.pi fun a => f a :=
  rfl

/-- Given an alternating `R`-multilinear map `f` taking values in `R`, `f.smul_right z` is the map
sending `m` to `f m • z`. -/
@[simps!]
def smulRight {R M₁ M₂ ι : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module R M₁] [Module R M₂] (f : M₁ [⋀^ι]→ₗ[R] R) (z : M₂) : M₁ [⋀^ι]→ₗ[R] M₂ :=
  { f.toMultilinearMap.smulRight z with
    map_eq_zero_of_eq' := fun v i j h hne => by simp [f.map_eq_zero_of_eq v h hne] }

@[simp]
theorem coe_smulRight {R M₁ M₂ ι : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module R M₁] [Module R M₂] (f : M₁ [⋀^ι]→ₗ[R] R) (z : M₂) :
    (f.smulRight z : MultilinearMap R (fun _ : ι => M₁) M₂) = MultilinearMap.smulRight f z :=
  rfl

instance instAdd : Add (M [⋀^ι]→ₗ[R] N) where
  add a b :=
    { (a + b : MultilinearMap R (fun _ : ι => M) N) with
      map_eq_zero_of_eq' := fun v i j h hij => by
        simp [a.map_eq_zero_of_eq v h hij, b.map_eq_zero_of_eq v h hij] }

@[simp]
theorem add_apply : (f + f') v = f v + f' v :=
  rfl

@[norm_cast]
theorem coe_add : (↑(f + f') : MultilinearMap R (fun _ : ι => M) N) = f + f' :=
  rfl

instance instZero : Zero (M [⋀^ι]→ₗ[R] N) :=
  ⟨{ (0 : MultilinearMap R (fun _ : ι => M) N) with
      map_eq_zero_of_eq' := fun _ _ _ _ _ => by simp }⟩

@[simp]
theorem zero_apply : (0 : M [⋀^ι]→ₗ[R] N) v = 0 :=
  rfl

@[norm_cast]
theorem coe_zero : ((0 : M [⋀^ι]→ₗ[R] N) : MultilinearMap R (fun _ : ι => M) N) = 0 :=
  rfl

@[simp]
theorem mk_zero :
    mk (0 : MultilinearMap R (fun _ : ι ↦ M) N) (0 : M [⋀^ι]→ₗ[R] N).2 = 0 :=
  rfl

instance instInhabited : Inhabited (M [⋀^ι]→ₗ[R] N) :=
  ⟨0⟩

instance instAddCommMonoid : AddCommMonoid (M [⋀^ι]→ₗ[R] N) := fast_instance%
  coe_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => coeFn_smul _ _

instance instNeg : Neg (M [⋀^ι]→ₗ[R] N') :=
  ⟨fun f =>
    { -(f : MultilinearMap R (fun _ : ι => M) N') with
      map_eq_zero_of_eq' := fun v i j h hij => by simp [f.map_eq_zero_of_eq v h hij] }⟩

@[simp]
theorem neg_apply (m : ι → M) : (-g) m = -g m :=
  rfl

@[norm_cast]
theorem coe_neg : ((-g : M [⋀^ι]→ₗ[R] N') : MultilinearMap R (fun _ : ι => M) N') = -g :=
  rfl

instance instSub : Sub (M [⋀^ι]→ₗ[R] N') :=
  ⟨fun f g =>
    { (f - g : MultilinearMap R (fun _ : ι => M) N') with
      map_eq_zero_of_eq' := fun v i j h hij => by
        simp [f.map_eq_zero_of_eq v h hij, g.map_eq_zero_of_eq v h hij] }⟩

@[simp]
theorem sub_apply (m : ι → M) : (g - g₂) m = g m - g₂ m :=
  rfl

@[norm_cast]
theorem coe_sub : (↑(g - g₂) : MultilinearMap R (fun _ : ι => M) N') = g - g₂ :=
  rfl

instance instAddCommGroup : AddCommGroup (M [⋀^ι]→ₗ[R] N') := fast_instance%
  coe_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => coeFn_smul _ _) fun _ _ => coeFn_smul _ _

section DistribMulAction

variable {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]

instance instDistribMulAction : DistribMulAction S (M [⋀^ι]→ₗ[R] N) where
  one_smul _ := ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _
  smul_zero _ := ext fun _ => smul_zero _
  smul_add _ _ _ := ext fun _ => smul_add _ _ _

end DistribMulAction

section Module

variable {S : Type*} [Semiring S] [Module S N] [SMulCommClass R S N]

/-- The space of multilinear maps over an algebra over `R` is a module over `R`, for the pointwise
addition and scalar multiplication. -/
instance instModule : Module S (M [⋀^ι]→ₗ[R] N) where
  add_smul _ _ _ := ext fun _ => add_smul _ _ _
  zero_smul _ := ext fun _ => zero_smul _ _

instance instIsTorsionFree [IsTorsionFree S N] : IsTorsionFree S (M [⋀^ι]→ₗ[R] N) :=
  coe_injective.moduleIsTorsionFree _ coeFn_smul

/-- Embedding of alternating maps into multilinear maps as a linear map. -/
@[simps]
def toMultilinearMapLM : (M [⋀^ι]→ₗ[R] N) →ₗ[S] MultilinearMap R (fun _ : ι ↦ M) N where
  toFun := toMultilinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Module

section

variable (R M N)

/-- The natural equivalence between linear maps from `M` to `N`
and `1`-multilinear alternating maps from `M` to `N`. -/
@[simps!]
def ofSubsingleton [Subsingleton ι] (i : ι) : (M →ₗ[R] N) ≃ (M [⋀^ι]→ₗ[R] N) where
  toFun f := ⟨MultilinearMap.ofSubsingleton R M N i f, fun _ _ _ _ ↦ absurd (Subsingleton.elim _ _)⟩
  invFun f := (MultilinearMap.ofSubsingleton R M N i).symm f
  right_inv _ := coe_multilinearMap_injective <|
    (MultilinearMap.ofSubsingleton R M N i).apply_symm_apply _

variable (ι) {N}

/-- The constant map is alternating when `ι` is empty. -/
@[simps -fullyApplied]
def constOfIsEmpty [IsEmpty ι] (m : N) : M [⋀^ι]→ₗ[R] N :=
  { MultilinearMap.constOfIsEmpty R _ m with
    toFun := Function.const _ m
    map_eq_zero_of_eq' := fun _ => isEmptyElim }

end

/-- Restrict the codomain of an alternating map to a submodule. -/
@[simps]
def codRestrict (f : M [⋀^ι]→ₗ[R] N) (p : Submodule R N) (h : ∀ v, f v ∈ p) :
    M [⋀^ι]→ₗ[R] p :=
  { f.toMultilinearMap.codRestrict p h with
    toFun := fun v => ⟨f v, h v⟩
    map_eq_zero_of_eq' := fun _ _ _ hv hij => Subtype.ext <| map_eq_zero_of_eq _ _ hv hij }

end AlternatingMap

/-!
### Composition with linear maps
-/


namespace LinearMap

variable {S : Type*} {N₂ : Type*} [AddCommMonoid N₂] [Module R N₂]

/-- Composing an alternating map with a linear map on the left gives again an alternating map. -/
def compAlternatingMap (g : N →ₗ[R] N₂) (f : M [⋀^ι]→ₗ[R] N) : M [⋀^ι]→ₗ[R] N₂ where
  __ := g.compMultilinearMap (f : MultilinearMap R (fun _ : ι => M) N)
  map_eq_zero_of_eq' v i j h hij := by simp [f.map_eq_zero_of_eq v h hij]

@[simp]
theorem coe_compAlternatingMap (g : N →ₗ[R] N₂) (f : M [⋀^ι]→ₗ[R] N) :
    ⇑(g.compAlternatingMap f) = g ∘ f :=
  rfl

@[simp]
theorem compAlternatingMap_apply (g : N →ₗ[R] N₂) (f : M [⋀^ι]→ₗ[R] N) (m : ι → M) :
    g.compAlternatingMap f m = g (f m) :=
  rfl

@[simp]
theorem compAlternatingMap_zero (g : N →ₗ[R] N₂) :
    g.compAlternatingMap (0 : M [⋀^ι]→ₗ[R] N) = 0 :=
  AlternatingMap.ext fun _ => map_zero g

@[simp]
theorem zero_compAlternatingMap (f : M [⋀^ι]→ₗ[R] N) :
    (0 : N →ₗ[R] N₂).compAlternatingMap f = 0 := rfl

@[simp]
theorem compAlternatingMap_add (g : N →ₗ[R] N₂) (f₁ f₂ : M [⋀^ι]→ₗ[R] N) :
    g.compAlternatingMap (f₁ + f₂) = g.compAlternatingMap f₁ + g.compAlternatingMap f₂ :=
  AlternatingMap.ext fun _ => map_add g _ _

@[simp]
theorem add_compAlternatingMap (g₁ g₂ : N →ₗ[R] N₂) (f : M [⋀^ι]→ₗ[R] N) :
    (g₁ + g₂).compAlternatingMap f = g₁.compAlternatingMap f + g₂.compAlternatingMap f := rfl

@[simp]
theorem compAlternatingMap_smul [Monoid S] [DistribMulAction S N] [DistribMulAction S N₂]
    [SMulCommClass R S N] [SMulCommClass R S N₂] [CompatibleSMul N N₂ S R]
    (g : N →ₗ[R] N₂) (s : S) (f : M [⋀^ι]→ₗ[R] N) :
    g.compAlternatingMap (s • f) = s • g.compAlternatingMap f :=
  AlternatingMap.ext fun _ => g.map_smul_of_tower _ _

@[simp]
theorem smul_compAlternatingMap [Monoid S] [DistribMulAction S N₂] [SMulCommClass R S N₂]
    (g : N →ₗ[R] N₂) (s : S) (f : M [⋀^ι]→ₗ[R] N) :
    (s • g).compAlternatingMap f = s • g.compAlternatingMap f := rfl

variable (S) in
/-- `LinearMap.compAlternatingMap` as an `S`-linear map. -/
@[simps]
def compAlternatingMapₗ [Semiring S] [Module S N] [Module S N₂]
    [SMulCommClass R S N] [SMulCommClass R S N₂] [LinearMap.CompatibleSMul N N₂ S R]
    (g : N →ₗ[R] N₂) :
    (M [⋀^ι]→ₗ[R] N) →ₗ[S] (M [⋀^ι]→ₗ[R] N₂) where
  toFun := g.compAlternatingMap
  map_add' := g.compAlternatingMap_add
  map_smul' := g.compAlternatingMap_smul

theorem smulRight_eq_comp {R M₁ M₂ ι : Type*} [CommSemiring R] [AddCommMonoid M₁]
    [AddCommMonoid M₂] [Module R M₁] [Module R M₂] (f : M₁ [⋀^ι]→ₗ[R] R) (z : M₂) :
    f.smulRight z = (LinearMap.id.smulRight z).compAlternatingMap f :=
  rfl

@[simp]
theorem subtype_compAlternatingMap_codRestrict (f : M [⋀^ι]→ₗ[R] N) (p : Submodule R N)
    (h) : p.subtype.compAlternatingMap (f.codRestrict p h) = f :=
  AlternatingMap.ext fun _ => rfl

@[simp]
theorem compAlternatingMap_codRestrict (g : N →ₗ[R] N₂) (f : M [⋀^ι]→ₗ[R] N)
    (p : Submodule R N₂) (h) :
    (g.codRestrict p h).compAlternatingMap f =
      (g.compAlternatingMap f).codRestrict p fun v => h (f v) :=
  AlternatingMap.ext fun _ => rfl

end LinearMap

namespace AlternatingMap

variable {M₂ : Type*} [AddCommMonoid M₂] [Module R M₂]
variable {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃]

/-- Composing an alternating map with the same linear map on each argument gives again an
alternating map. -/
def compLinearMap (f : M [⋀^ι]→ₗ[R] N) (g : M₂ →ₗ[R] M) : M₂ [⋀^ι]→ₗ[R] N :=
  { (f : MultilinearMap R (fun _ : ι => M) N).compLinearMap fun _ => g with
    map_eq_zero_of_eq' := fun _ _ _ h hij => f.map_eq_zero_of_eq _ (LinearMap.congr_arg h) hij }

theorem coe_compLinearMap (f : M [⋀^ι]→ₗ[R] N) (g : M₂ →ₗ[R] M) :
    ⇑(f.compLinearMap g) = f ∘ (g ∘ ·) :=
  rfl

@[simp]
theorem compLinearMap_apply (f : M [⋀^ι]→ₗ[R] N) (g : M₂ →ₗ[R] M) (v : ι → M₂) :
    f.compLinearMap g v = f fun i => g (v i) :=
  rfl

/-- Composing an alternating map twice with the same linear map in each argument is
the same as composing with their composition. -/
theorem compLinearMap_assoc (f : M [⋀^ι]→ₗ[R] N) (g₁ : M₂ →ₗ[R] M) (g₂ : M₃ →ₗ[R] M₂) :
    (f.compLinearMap g₁).compLinearMap g₂ = f.compLinearMap (g₁ ∘ₗ g₂) :=
  rfl

@[simp]
theorem zero_compLinearMap (g : M₂ →ₗ[R] M) : (0 : M [⋀^ι]→ₗ[R] N).compLinearMap g = 0 := by
  ext
  simp only [compLinearMap_apply, zero_apply]

@[simp]
theorem add_compLinearMap (f₁ f₂ : M [⋀^ι]→ₗ[R] N) (g : M₂ →ₗ[R] M) :
    (f₁ + f₂).compLinearMap g = f₁.compLinearMap g + f₂.compLinearMap g := by
  ext
  simp only [compLinearMap_apply, add_apply]

@[simp]
theorem compLinearMap_zero [Nonempty ι] (f : M [⋀^ι]→ₗ[R] N) :
    f.compLinearMap (0 : M₂ →ₗ[R] M) = 0 := by
  ext
  simp_rw [compLinearMap_apply, LinearMap.zero_apply, ← Pi.zero_def, map_zero, zero_apply]

/-- Composing an alternating map with the identity linear map in each argument. -/
@[simp]
theorem compLinearMap_id (f : M [⋀^ι]→ₗ[R] N) : f.compLinearMap LinearMap.id = f :=
  ext fun _ => rfl

/-- Composing with a surjective linear map is injective. -/
theorem compLinearMap_injective (f : M₂ →ₗ[R] M) (hf : Function.Surjective f) :
    Function.Injective fun g : M [⋀^ι]→ₗ[R] N => g.compLinearMap f := fun g₁ g₂ h =>
  ext fun x => by
    simpa [Function.surjInv_eq hf] using AlternatingMap.ext_iff.mp h (Function.surjInv hf ∘ x)

theorem compLinearMap_inj (f : M₂ →ₗ[R] M) (hf : Function.Surjective f)
    (g₁ g₂ : M [⋀^ι]→ₗ[R] N) : g₁.compLinearMap f = g₂.compLinearMap f ↔ g₁ = g₂ :=
  (compLinearMap_injective _ hf).eq_iff

/-- If two `R`-alternating maps from `R` are equal on 1, then they are equal.

This is the alternating version of `LinearMap.ext_ring`. -/
@[ext]
theorem ext_ring {R} [CommSemiring R] [Module R N] [Finite ι] ⦃f g : R [⋀^ι]→ₗ[R] N⦄
    (h : f (fun _ ↦ 1) = g (fun _ ↦ 1)) : f = g :=
  coe_multilinearMap_injective <| MultilinearMap.ext_ring h

/-- The only `R`-alternating map from two or more copies of `R` is the zero map. -/
instance uniqueOfCommRing {R} [CommSemiring R] [Module R N] [Finite ι] [Nontrivial ι] :
    Unique (R [⋀^ι]→ₗ[R] N) where
  uniq f := let ⟨_, _, hij⟩ := exists_pair_ne ι; ext_ring <| f.map_eq_zero_of_eq _ rfl hij

section DomLcongr

variable (ι R N)
variable (S : Type*) [Semiring S] [Module S N] [SMulCommClass R S N]

/-- Construct a linear equivalence between maps from a linear equivalence between domains.

This is `AlternatingMap.compLinearMap` as an isomorphism,
and the alternating version of `LinearEquiv.multilinearMapCongrLeft`.
It could also have been called `LinearEquiv.alternatingMapCongrLeft`. -/
@[simps apply]
def domLCongr (e : M ≃ₗ[R] M₂) : M [⋀^ι]→ₗ[R] N ≃ₗ[S] (M₂ [⋀^ι]→ₗ[R] N) where
  toFun f := f.compLinearMap e.symm
  invFun g := g.compLinearMap e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := AlternatingMap.ext fun _ => f.congr_arg <| funext fun _ => e.symm_apply_apply _
  right_inv f := AlternatingMap.ext fun _ => f.congr_arg <| funext fun _ => e.apply_symm_apply _

@[simp]
theorem domLCongr_refl : domLCongr R N ι S (LinearEquiv.refl R M) = LinearEquiv.refl S _ :=
  LinearEquiv.ext fun _ => AlternatingMap.ext fun _ => rfl

@[simp]
theorem domLCongr_symm (e : M ≃ₗ[R] M₂) : (domLCongr R N ι S e).symm = domLCongr R N ι S e.symm :=
  rfl

theorem domLCongr_trans (e : M ≃ₗ[R] M₂) (f : M₂ ≃ₗ[R] M₃) :
    (domLCongr R N ι S e).trans (domLCongr R N ι S f) = domLCongr R N ι S (e.trans f) :=
  rfl

end DomLcongr

/-- Composing an alternating map with the same linear equiv on each argument gives the zero map
if and only if the alternating map is the zero map. -/
@[simp]
theorem compLinearEquiv_eq_zero_iff (f : M [⋀^ι]→ₗ[R] N) (g : M₂ ≃ₗ[R] M) :
    f.compLinearMap (g : M₂ →ₗ[R] M) = 0 ↔ f = 0 :=
  (domLCongr R N ι ℕ g.symm).map_eq_zero_iff

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

theorem map_add_univ [DecidableEq ι] [Fintype ι] (m m' : ι → M) :
    f (m + m') = ∑ s : Finset ι, f (s.piecewise m m') :=
  f.toMultilinearMap.map_add_univ m m'

theorem map_smul_univ {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M]
    [Module R M] {N : Type*} [AddCommMonoid N] [Module R N] [Fintype ι]
    (f : M [⋀^ι]→ₗ[R] N) (c : ι → R) (m : ι → M) :
    (f fun i => c i • m i) = (∏ i, c i) • f m :=
  f.toMultilinearMap.map_smul_univ c m

end

/-!
### Theorems specific to alternating maps

Various properties of reordered and repeated inputs which follow from
`AlternatingMap.map_eq_zero_of_eq`.
-/


theorem map_update_self [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    f (Function.update v i (v j)) = 0 :=
  f.map_eq_zero_of_eq _ (by rw [Function.update_self, Function.update_of_ne hij.symm]) hij

theorem map_update_update [DecidableEq ι] {i j : ι} (hij : i ≠ j) (m : M) :
    f (Function.update (Function.update v i m) j m) = 0 :=
  f.map_eq_zero_of_eq _
    (by rw [Function.update_self, Function.update_of_ne hij, Function.update_self]) hij

theorem map_swap_add [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    f (v ∘ Equiv.swap i j) + f v = 0 := by
  rw [Equiv.comp_swap_eq_update]
  convert f.map_update_update v hij (v i + v j)
  simp [f.map_update_self _ hij, f.map_update_self _ hij.symm,
    Function.update_comm hij (v i + v j) (v _) v, Function.update_comm hij.symm (v i) (v i) v]

theorem map_add_swap [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    f v + f (v ∘ Equiv.swap i j) = 0 := by
  rw [add_comm]
  exact f.map_swap_add v hij

theorem map_swap [DecidableEq ι] {i j : ι} (hij : i ≠ j) : g (v ∘ Equiv.swap i j) = -g v :=
  eq_neg_of_add_eq_zero_left <| g.map_swap_add v hij

theorem map_perm [DecidableEq ι] [Fintype ι] (v : ι → M) (σ : Equiv.Perm ι) :
    g (v ∘ σ) = Equiv.Perm.sign σ • g v := by
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => simp
  | mul_swap s x y hxy hI => simp_all [← Function.comp_assoc, g.map_swap]

theorem map_congr_perm [DecidableEq ι] [Fintype ι] (σ : Equiv.Perm ι) :
    g v = Equiv.Perm.sign σ • g (v ∘ σ) := by
  rw [g.map_perm, smul_smul]
  simp

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

@[simp]
theorem domDomCongr_refl (f : M [⋀^ι]→ₗ[R] N) : f.domDomCongr (Equiv.refl ι) = f := rfl

theorem domDomCongr_trans (σ₁ : ι ≃ ι') (σ₂ : ι' ≃ ι'') (f : M [⋀^ι]→ₗ[R] N) :
    f.domDomCongr (σ₁.trans σ₂) = (f.domDomCongr σ₁).domDomCongr σ₂ :=
  rfl

@[simp]
theorem domDomCongr_zero (σ : ι ≃ ι') : (0 : M [⋀^ι]→ₗ[R] N).domDomCongr σ = 0 :=
  rfl

@[simp]
theorem domDomCongr_add (σ : ι ≃ ι') (f g : M [⋀^ι]→ₗ[R] N) :
    (f + g).domDomCongr σ = f.domDomCongr σ + g.domDomCongr σ :=
  rfl

@[simp]
theorem domDomCongr_smul {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]
    (σ : ι ≃ ι') (c : S) (f : M [⋀^ι]→ₗ[R] N) :
    (c • f).domDomCongr σ = c • f.domDomCongr σ :=
  rfl

/-- `AlternatingMap.domDomCongr` as an equivalence.

This is declared separately because it does not work with dot notation. -/
@[simps apply symm_apply]
def domDomCongrEquiv (σ : ι ≃ ι') : M [⋀^ι]→ₗ[R] N ≃+ M [⋀^ι']→ₗ[R] N where
  toFun := domDomCongr σ
  invFun := domDomCongr σ.symm
  left_inv f := by
    ext
    simp [Function.comp_def]
  right_inv m := by
    ext
    simp [Function.comp_def]
  map_add' := domDomCongr_add σ

section DomDomLcongr

variable (S : Type*) [Semiring S] [Module S N] [SMulCommClass R S N]

/-- `AlternatingMap.domDomCongr` as a linear equivalence. -/
@[simps apply symm_apply]
def domDomCongrₗ (σ : ι ≃ ι') : M [⋀^ι]→ₗ[R] N ≃ₗ[S] M [⋀^ι']→ₗ[R] N where
  toFun := domDomCongr σ
  invFun := domDomCongr σ.symm
  left_inv f := by ext; simp [Function.comp_def]
  right_inv m := by ext; simp [Function.comp_def]
  map_add' := domDomCongr_add σ
  map_smul' := domDomCongr_smul σ

@[simp]
theorem domDomCongrₗ_refl :
    (domDomCongrₗ S (Equiv.refl ι) : M [⋀^ι]→ₗ[R] N ≃ₗ[S] M [⋀^ι]→ₗ[R] N) =
      LinearEquiv.refl _ _ :=
  rfl

@[simp]
theorem domDomCongrₗ_toAddEquiv (σ : ι ≃ ι') :
    (↑(domDomCongrₗ S σ : M [⋀^ι]→ₗ[R] N ≃ₗ[S] _) : M [⋀^ι]→ₗ[R] N ≃+ _) =
      domDomCongrEquiv σ :=
  rfl

end DomDomLcongr

/-- The results of applying `domDomCongr` to two maps are equal if and only if those maps are. -/
@[simp]
theorem domDomCongr_eq_iff (σ : ι ≃ ι') (f g : M [⋀^ι]→ₗ[R] N) :
    f.domDomCongr σ = g.domDomCongr σ ↔ f = g :=
  (domDomCongrEquiv σ : _ ≃+ M [⋀^ι']→ₗ[R] N).apply_eq_iff_eq

@[simp]
theorem domDomCongr_eq_zero_iff (σ : ι ≃ ι') (f : M [⋀^ι]→ₗ[R] N) :
    f.domDomCongr σ = 0 ↔ f = 0 :=
  (domDomCongrEquiv σ : M [⋀^ι]→ₗ[R] N ≃+ M [⋀^ι']→ₗ[R] N).map_eq_zero_iff

theorem domDomCongr_perm [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) :
    g.domDomCongr σ = Equiv.Perm.sign σ • g :=
  AlternatingMap.ext fun v => g.map_perm v σ

@[norm_cast]
theorem coe_domDomCongr (σ : ι ≃ ι') :
    ↑(f.domDomCongr σ) = (f : MultilinearMap R (fun _ : ι => M) N).domDomCongr σ :=
  MultilinearMap.ext fun _ => rfl

end DomDomCongr

/-- If the arguments are linearly dependent then the result is `0`. -/
theorem map_linearDependent {K M N : Type*} [Ring K] [IsDomain K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [IsTorsionFree K N] (f : M [⋀^ι]→ₗ[K] N)
    (v : ι → M) (h : ¬LinearIndependent K v) : f v = 0 := by
  obtain ⟨s, g, h, i, hi, hz⟩ := not_linearIndependent_iff.mp h
  letI := Classical.decEq ι
  suffices f (update v i (g i • v i)) = 0 by
    rw [f.map_update_smul, Function.update_eq_self, smul_eq_zero] at this
    exact Or.resolve_left this hz
  rw [← Finset.insert_erase hi, Finset.sum_insert (s.notMem_erase i), add_eq_zero_iff_eq_neg] at h
  rw [h, f.map_update_neg, f.map_update_sum, neg_eq_zero]
  apply Finset.sum_eq_zero
  intro j hj
  obtain ⟨hij, _⟩ := Finset.mem_erase.mp hj
  rw [f.map_update_smul, f.map_update_self _ hij.symm, smul_zero]

section Fin

open Fin

/-- A version of `MultilinearMap.cons_add` for `AlternatingMap`. -/
theorem map_vecCons_add {n : ℕ} (f : M [⋀^Fin n.succ]→ₗ[R] N) (m : Fin n → M) (x y : M) :
    f (Matrix.vecCons (x + y) m) = f (Matrix.vecCons x m) + f (Matrix.vecCons y m) :=
  f.toMultilinearMap.cons_add _ _ _

/-- A version of `MultilinearMap.cons_smul` for `AlternatingMap`. -/
theorem map_vecCons_smul {n : ℕ} (f : M [⋀^Fin n.succ]→ₗ[R] N) (m : Fin n → M) (c : R)
    (x : M) : f (Matrix.vecCons (c • x) m) = c • f (Matrix.vecCons x m) :=
  f.toMultilinearMap.cons_smul _ _ _

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
      (fun σ _ => by simp [Perm.sign_swap i_ne_j, apply_swap_eq_self hv])
      (fun σ _ _ => (not_congr swap_mul_eq_iff).mpr i_ne_j) (fun σ _ => Finset.mem_univ _)
      fun σ _ => swap_mul_involutive i j σ

/-- Produce an `AlternatingMap` out of a `MultilinearMap`, by summing over all argument
permutations. -/
def alternatization : MultilinearMap R (fun _ : ι => M) N' →+ M [⋀^ι]→ₗ[R] N' where
  toFun m :=
    { ∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ with
      toFun := ⇑(∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ)
      map_eq_zero_of_eq' := private fun v i j hvij hij =>
        alternization_map_eq_zero_of_eq_aux m v i j hij hvij }
  map_add' a b := by ext; simp [Finset.sum_add_distrib]
  map_zero' := by ext; simp

theorem alternatization_def (m : MultilinearMap R (fun _ : ι => M) N') :
    ⇑(alternatization m) = (∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ :) :=
  rfl

theorem alternatization_coe (m : MultilinearMap R (fun _ : ι => M) N') :
    ↑(alternatization m) = (∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ :) :=
  coe_injective rfl

theorem alternatization_apply (m : MultilinearMap R (fun _ : ι => M) N') (v : ι → M) :
    alternatization m v = ∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ v := by
  simp only [alternatization_def, smul_apply, sum_apply]

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

end LinearMap

section Basis

open AlternatingMap

variable {ι₁ : Type*} [Finite ι]
variable {R' : Type*} {N₁ N₂ : Type*} [CommSemiring R'] [AddCommMonoid N₁] [AddCommMonoid N₂]
variable [Module R' N₁] [Module R' N₂]

/-- Two alternating maps indexed by a `Fintype` are equal if they are equal when all arguments
are distinct basis vectors. -/
theorem Module.Basis.ext_alternating {f g : N₁ [⋀^ι]→ₗ[R'] N₂} (e : Basis ι₁ R' N₁)
    (h : ∀ v : ι → ι₁, Function.Injective v → (f fun i => e (v i)) = g fun i => e (v i)) :
    f = g := by
  refine AlternatingMap.coe_multilinearMap_injective (Basis.ext_multilinear (fun _ ↦ e) fun v => ?_)
  by_cases hi : Function.Injective v
  · exact h v hi
  · have : ¬Function.Injective fun i => e (v i) := hi.imp Function.Injective.of_comp
    rw [coe_multilinearMap, coe_multilinearMap, f.map_eq_zero_of_not_injective _ this,
      g.map_eq_zero_of_not_injective _ this]

end Basis

variable {R' : Type*} {M'' M₂'' N'' N₂'' : Type*} [CommSemiring R'] [AddCommMonoid M'']
  [AddCommMonoid M₂''] [AddCommMonoid N''] [AddCommMonoid N₂''] [Module R' M''] [Module R' M₂'']
  [Module R' N''] [Module R' N₂'']

/-- An isomorphism of multilinear maps given an isomorphism between their codomains.

This is `Linear.compAlternatingMap` as an isomorphism,
and the alternating version of `LinearEquiv.multilinearMapCongrRight`. -/
@[simps!]
def LinearEquiv.alternatingMapCongrRight (e : N'' ≃ₗ[R'] N₂'') :
    M'' [⋀^ι]→ₗ[R'] N'' ≃ₗ[R'] (M'' [⋀^ι]→ₗ[R'] N₂'') where
  toFun f := e.compAlternatingMap f
  invFun f := e.symm.compAlternatingMap f
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

/-- The space of constant maps is equivalent to the space of maps that are alternating with respect
to an empty family. -/
@[simps]
def AlternatingMap.constLinearEquivOfIsEmpty [IsEmpty ι] : N'' ≃ₗ[R'] (M'' [⋀^ι]→ₗ[R'] N'') where
  toFun := AlternatingMap.constOfIsEmpty R' M'' ι
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := f 0
  right_inv f := ext fun _ => AlternatingMap.congr_arg f <| Subsingleton.elim _ _
