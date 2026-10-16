/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basis

/-!
# Symmetric maps

We construct the bundled function `SymmetricMap`, which extends `MultilinearMap` with all the
arguments of the same type.

## Main definitions
* `SymmetricMap R M N ι` is the space of `R`-linear symmetric maps from `ι → M` to `N`.
* `f.map_swap` expresses that `f` is the same when two inputs are swapped.
* `f.map_perm` expresses that `f` is invariant under a permutation of its inputs.
* An `AddCommMonoid`, `AddCommGroup`, and `Module` structure over `SymmetricMap`s that
  matches the definitions over `MultilinearMap`s.
* `SymmetricMap.domDomCongr`, for permuting the elements within a family.
* `MultilinearMap.symmetrization`, which makes a symmetric map out of a non-symmetric one.
* `SymmetricMap.curryLeft`, for binding the leftmost argument of a symmetric map indexed
  by `Fin n.succ`.

## Implementation notes
Just like alternating maps, `SymmetricMap`s are provided with a coercion to `MultilinearMap`,
along with a set of `norm_cast` lemmas that act on the algebraic structure:

* `SymmetricMap.coe_add`
* `SymmetricMap.coe_zero`
* `SymmetricMap.coe_sub`
* `SymmetricMap.coe_neg`
* `SymmetricMap.coe_smul`
-/

@[expose] public section

open Module

-- semiring / add_comm_monoid
variable {R : Type*} [Semiring R]
  {M : Type*} [AddCommMonoid M] [Module R M]
  {N : Type*} [AddCommMonoid N] [Module R N]
  {P : Type*} [AddCommMonoid P] [Module R P]

-- semiring / add_comm_group
variable {M' : Type*} [AddCommGroup M'] [Module R M']
  {N' : Type*} [AddCommGroup N'] [Module R N']
  {ι ι' ι'' : Type*}

section

variable (R M N ι)

/-- A symmetric map from `ι → M` to `N`, denoted `M [Sym^ι]→ₗ[R] N`,
is a multilinear map that is invariant under swapping any two of its arguments. -/
structure SymmetricMap extends MultilinearMap R (fun _ : ι ↦ M) N where
  /-- The map is symmetric: swapping any two coordinates does not change `f` -/
  map_eq_map_of_swap' : ∀ (v : ι → M) (i j : ι), [DecidableEq ι] →
    toFun (v ∘ (Equiv.swap i j)) = toFun v

@[inherit_doc]
notation M " [Sym^" ι "]→ₗ[" R "] " N:100 => SymmetricMap R M N ι

end

/-- The multilinear map associated to a symmetric map -/
add_decl_doc SymmetricMap.toMultilinearMap

namespace SymmetricMap

variable (f f' : M [Sym^ι]→ₗ[R] N) (g g₂ : M [Sym^ι]→ₗ[R] N') (g' : M' [Sym^ι]→ₗ[R] N')
  (v : ι → M) (v' : ι → M')

open Function

/-! Basic coercion simp lemmas, largely copied from `RingHom` and `MultilinearMap` -/

section Coercions

instance instFunLike : FunLike (M [Sym^ι]→ₗ[R] N) (ι → M) N where
  coe f := f.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨_, _, _⟩, _⟩
    rcases g with ⟨⟨_, _, _⟩, _⟩
    congr

initialize_simps_projections SymmetricMap (toFun → apply)

@[simp]
theorem toFun_eq_coe : f.toFun = f :=
  rfl

@[simp]
theorem coe_mk (f : MultilinearMap R (fun _ : ι ↦ M) N) (h) :
    ⇑(⟨f, h⟩ : M [Sym^ι]→ₗ[R] N) = f :=
  rfl

protected theorem congr_fun {f g : M [Sym^ι]→ₗ[R] N} (h : f = g) (x : ι → M) : f x = g x :=
  congr_arg (fun h : M [Sym^ι]→ₗ[R] N ↦ h x) h

protected theorem congr_arg (f : M [Sym^ι]→ₗ[R] N) {x y : ι → M} (h : x = y) : f x = f y :=
  congr_arg (fun x : ι → M ↦ f x) h

theorem coe_injective : Injective ((↑) : M [Sym^ι]→ₗ[R] N → (ι → M) → N) :=
  DFunLike.coe_injective

@[norm_cast]
theorem coe_inj {f g : M [Sym^ι]→ₗ[R] N} : (f : (ι → M) → N) = g ↔ f = g :=
  coe_injective.eq_iff

@[ext]
theorem ext {f f' : M [Sym^ι]→ₗ[R] N} (H : ∀ x, f x = f' x) : f = f' :=
  DFunLike.ext _ _ H

attribute [coe] SymmetricMap.toMultilinearMap

instance instCoe : Coe (M [Sym^ι]→ₗ[R] N) (MultilinearMap R (fun _ : ι ↦ M) N) :=
  ⟨fun x ↦ x.toMultilinearMap⟩

@[simp, norm_cast]
theorem coe_multilinearMap : ⇑(f : MultilinearMap R (fun _ : ι ↦ M) N) = f :=
  rfl

theorem coe_multilinearMap_injective :
    Function.Injective ((↑) : M [Sym^ι]→ₗ[R] N → MultilinearMap R (fun _ : ι ↦ M) N) :=
  fun _ _ h ↦ ext <| MultilinearMap.congr_fun h

theorem coe_multilinearMap_mk (f : (ι → M) → N) (h₁ h₂ h₃) :
    ((⟨⟨f, h₁, h₂⟩, h₃⟩ : M [Sym^ι]→ₗ[R] N) : MultilinearMap R (fun _ : ι ↦ M) N) =
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

@[simp] -- TODO check carefully; is new for symmetric maps
theorem map_eq_map_of_swap [DecidableEq ι] (v : ι → M) {i j : ι} : f (v ∘ Equiv.swap i j) = f v :=
  f.map_eq_map_of_swap' v i j

theorem map_coord_zero {m : ι → M} (i : ι) (h : m i = 0) : f m = 0 :=
  f.toMultilinearMap.map_coord_zero i h

@[simp]
theorem map_update_zero [DecidableEq ι] (m : ι → M) (i : ι) : f (update m i 0) = 0 :=
  f.toMultilinearMap.map_update_zero m i

@[simp]
theorem map_zero [Nonempty ι] : f 0 = 0 :=
  f.toMultilinearMap.map_zero

/-!
### Algebraic structure inherited from `MultilinearMap`

`SymmetricMap` carries the same `AddCommMonoid`, `AddCommGroup`, and `Module` structure
as `MultilinearMap`
-/


section SMul

variable {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]

instance instSMul : SMul S (M [Sym^ι]→ₗ[R] N) where
  smul c f := {
    __ := c • (f : MultilinearMap R (fun _ : ι ↦ M) N)
    map_eq_map_of_swap' v i j := by simp }

@[simp]
theorem smul_apply (c : S) (m : ι → M) : (c • f) m = c • f m :=
  rfl

@[norm_cast]
theorem coe_smul (c : S) : ↑(c • f) = c • (f : MultilinearMap R (fun _ : ι ↦ M) N) :=
  rfl

theorem coeFn_smul (c : S) (f : M [Sym^ι]→ₗ[R] N) : ⇑(c • f) = c • ⇑f :=
  rfl

instance instSMulCommClass {T : Type*} [Monoid T] [DistribMulAction T N] [SMulCommClass R T N]
    [SMulCommClass S T N] : SMulCommClass S T (M [Sym^ι]→ₗ[R] N) where
  smul_comm _ _ _ := ext fun _ ↦ smul_comm ..

instance instIsCentralScalar [DistribMulAction Sᵐᵒᵖ N] [IsCentralScalar S N] :
    IsCentralScalar S (M [Sym^ι]→ₗ[R] N) :=
  ⟨fun _ _ ↦ ext fun _ ↦ op_smul_eq_smul _ _⟩

end SMul

/-- The Cartesian product of two symmetric maps, as a symmetric map. -/
@[simps!]
def prod (f : M [Sym^ι]→ₗ[R] N) (g : M [Sym^ι]→ₗ[R] P) : M [Sym^ι]→ₗ[R] (N × P) :=
  { f.toMultilinearMap.prod g.toMultilinearMap with
    map_eq_map_of_swap' v i j _ := by ext <;> simp }

@[simp]
theorem coe_prod (f : M [Sym^ι]→ₗ[R] N) (g : M [Sym^ι]→ₗ[R] P) :
    (f.prod g : MultilinearMap R (fun _ : ι ↦ M) (N × P)) = MultilinearMap.prod f g :=
  rfl

/-- Combine a family of symmetric maps with the same domain and codomains `N i` into a
symmetric map taking values in the space of functions `Π i, N i`. -/
@[simps!]
def pi {ι' : Type*} {N : ι' → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M [Sym^ι]→ₗ[R] N i) : M [Sym^ι]→ₗ[R] (∀ i, N i) :=
  { MultilinearMap.pi fun a ↦ (f a).toMultilinearMap with
    map_eq_map_of_swap' v i j _ := by ext; simp }

@[simp]
theorem coe_pi {ι' : Type*} {N : ι' → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M [Sym^ι]→ₗ[R] N i) :
    (pi f : MultilinearMap R (fun _ : ι ↦ M) (∀ i, N i)) = MultilinearMap.pi fun a ↦ f a :=
  rfl

/-- Given a symmetric `R`-multilinear map `f` taking values in `R`, `f.smul_right z` is the map
sending `m` to `f m • z`. -/
@[simps!]
def smulRight {R M₁ M₂ ι : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module R M₁] [Module R M₂] (f : M₁ [Sym^ι]→ₗ[R] R) (z : M₂) : M₁ [Sym^ι]→ₗ[R] M₂ :=
  { f.toMultilinearMap.smulRight z with
    map_eq_map_of_swap' v i j _ := by simp }

@[simp]
theorem coe_smulRight {R M₁ M₂ ι : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module R M₁] [Module R M₂] (f : M₁ [Sym^ι]→ₗ[R] R) (z : M₂) :
    (f.smulRight z : MultilinearMap R (fun _ : ι ↦ M₁) M₂) = MultilinearMap.smulRight f z :=
  rfl

instance instAdd : Add (M [Sym^ι]→ₗ[R] N) where
  add a b :=
    { (a + b : MultilinearMap R (fun _ : ι ↦ M) N) with
      map_eq_map_of_swap' v i j _ := by simp }

@[simp]
theorem add_apply : (f + f') v = f v + f' v :=
  rfl

@[norm_cast]
theorem coe_add : (↑(f + f') : MultilinearMap R (fun _ : ι ↦ M) N) = f + f' :=
  rfl

instance instZero : Zero (M [Sym^ι]→ₗ[R] N) :=
  ⟨{ (0 : MultilinearMap R (fun _ : ι ↦ M) N) with
      map_eq_map_of_swap' v i j _ := by simp }⟩

@[simp]
theorem zero_apply : (0 : M [Sym^ι]→ₗ[R] N) v = 0 :=
  rfl

@[norm_cast]
theorem coe_zero : ((0 : M [Sym^ι]→ₗ[R] N) : MultilinearMap R (fun _ : ι ↦ M) N) = 0 :=
  rfl

@[simp]
theorem mk_zero :
    mk (0 : MultilinearMap R (fun _ : ι ↦ M) N) (0 : M [Sym^ι]→ₗ[R] N).2 = 0 :=
  rfl

instance instInhabited : Inhabited (M [Sym^ι]→ₗ[R] N) :=
  ⟨0⟩

instance instAddCommMonoid : AddCommMonoid (M [Sym^ι]→ₗ[R] N) := fast_instance%
  coe_injective.addCommMonoid _ rfl (fun _ _ ↦ rfl) fun _ _ ↦ coeFn_smul _ _

instance instNeg : Neg (M [Sym^ι]→ₗ[R] N') :=
  ⟨fun f ↦
    { -(f : MultilinearMap R (fun _ : ι ↦ M) N') with
      map_eq_map_of_swap' v i j _ := by simp }⟩

@[simp]
theorem neg_apply (m : ι → M) : (-g) m = -g m :=
  rfl

@[norm_cast]
theorem coe_neg : ((-g : M [Sym^ι]→ₗ[R] N') : MultilinearMap R (fun _ : ι ↦ M) N') = -g :=
  rfl

instance instSub : Sub (M [Sym^ι]→ₗ[R] N') :=
  ⟨fun f g ↦
    { (f - g : MultilinearMap R (fun _ : ι ↦ M) N') with
      map_eq_map_of_swap' v i j _ := by simp }⟩

@[simp]
theorem sub_apply (m : ι → M) : (g - g₂) m = g m - g₂ m :=
  rfl

@[norm_cast]
theorem coe_sub : (↑(g - g₂) : MultilinearMap R (fun _ : ι ↦ M) N') = g - g₂ :=
  rfl

instance instAddCommGroup : AddCommGroup (M [Sym^ι]→ₗ[R] N') := fast_instance%
  coe_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ coeFn_smul _ _) fun _ _ ↦ coeFn_smul _ _

section DistribMulAction

variable {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]

instance instDistribMulAction : DistribMulAction S (M [Sym^ι]→ₗ[R] N) where
  one_smul _ := ext fun _ ↦ one_smul _ _
  mul_smul _ _ _ := ext fun _ ↦ mul_smul _ _ _
  smul_zero _ := ext fun _ ↦ smul_zero _
  smul_add _ _ _ := ext fun _ ↦ smul_add _ _ _

end DistribMulAction

section Module

variable {S : Type*} [Semiring S] [Module S N] [SMulCommClass R S N]

/-- The space of multilinear maps over an algebra over `R` is a module over `R`, for the pointwise
addition and scalar multiplication. -/
instance instModule : Module S (M [Sym^ι]→ₗ[R] N) where
  add_smul _ _ _ := ext fun _ ↦ add_smul _ _ _
  zero_smul _ := ext fun _ ↦ zero_smul _ _

instance instIsTorsionFree [IsTorsionFree S N] : IsTorsionFree S (M [Sym^ι]→ₗ[R] N) :=
  coe_injective.moduleIsTorsionFree _ coeFn_smul

/-- Embedding of symmetric maps into multilinear maps as a linear map. -/
@[simps]
def toMultilinearMapLM : (M [Sym^ι]→ₗ[R] N) →ₗ[S] MultilinearMap R (fun _ : ι ↦ M) N where
  toFun := toMultilinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Module

section

variable (R M N)

/-- The natural equivalence between linear maps from `M` to `N`
and `1`-multilinear symmetric maps from `M` to `N`. -/
@[simps!]
def ofSubsingleton [Subsingleton ι] (i : ι) : (M →ₗ[R] N) ≃ (M [Sym^ι]→ₗ[R] N) where
  toFun f := ⟨MultilinearMap.ofSubsingleton R M N i f, by
    intro v i' j' _
    congr 2
    apply Subsingleton.elim⟩
  invFun f := (MultilinearMap.ofSubsingleton R M N i).symm f
  right_inv _ := coe_multilinearMap_injective <|
    (MultilinearMap.ofSubsingleton R M N i).apply_symm_apply _

variable (ι) {N}

/-- The constant map is symmetric when `ι` is empty. -/
@[simps -fullyApplied]
def constOfIsEmpty [IsEmpty ι] (m : N) : M [Sym^ι]→ₗ[R] N :=
  { MultilinearMap.constOfIsEmpty R _ m with
    toFun := Function.const _ m
    map_eq_map_of_swap' v i j _ := by simp }

end

/-- Restrict the codomain of a symmetric map to a submodule. -/
@[simps]
def codRestrict (f : M [Sym^ι]→ₗ[R] N) (p : Submodule R N) (h : ∀ v, f v ∈ p) :
    M [Sym^ι]→ₗ[R] p :=
  { f.toMultilinearMap.codRestrict p h with
    toFun := fun v ↦ ⟨f v, h v⟩
    map_eq_map_of_swap' v i j _ := by simp }

end SymmetricMap

/-!
### Composition with linear maps
-/

namespace LinearMap

variable {S : Type*} {N₂ : Type*} [AddCommMonoid N₂] [Module R N₂]

/-- Composing a symmetric map with a linear map on the left gives again a symmetric map. -/
def compSymmetricMap (g : N →ₗ[R] N₂) (f : M [Sym^ι]→ₗ[R] N) : M [Sym^ι]→ₗ[R] N₂ where
  __ := g.compMultilinearMap (f : MultilinearMap R (fun _ : ι ↦ M) N)
  map_eq_map_of_swap' v i j _ := by simp

@[simp]
theorem coe_compSymmetricMap (g : N →ₗ[R] N₂) (f : M [Sym^ι]→ₗ[R] N) :
    ⇑(g.compSymmetricMap f) = g ∘ f :=
  rfl

@[simp]
theorem compSymmetricMap_apply (g : N →ₗ[R] N₂) (f : M [Sym^ι]→ₗ[R] N) (m : ι → M) :
    g.compSymmetricMap f m = g (f m) :=
  rfl

@[simp]
theorem compSymmetricMap_zero (g : N →ₗ[R] N₂) :
    g.compSymmetricMap (0 : M [Sym^ι]→ₗ[R] N) = 0 :=
  SymmetricMap.ext fun _ ↦ map_zero g

@[simp]
theorem zero_compSymmetricMap (f : M [Sym^ι]→ₗ[R] N) :
    (0 : N →ₗ[R] N₂).compSymmetricMap f = 0 := rfl

@[simp]
theorem compSymmetricMap_add (g : N →ₗ[R] N₂) (f₁ f₂ : M [Sym^ι]→ₗ[R] N) :
    g.compSymmetricMap (f₁ + f₂) = g.compSymmetricMap f₁ + g.compSymmetricMap f₂ :=
  SymmetricMap.ext fun _ ↦ map_add g _ _

@[simp]
theorem add_compSymmetricMap (g₁ g₂ : N →ₗ[R] N₂) (f : M [Sym^ι]→ₗ[R] N) :
    (g₁ + g₂).compSymmetricMap f = g₁.compSymmetricMap f + g₂.compSymmetricMap f := rfl

@[simp]
theorem compSymmetricMap_smul [Monoid S] [DistribMulAction S N] [DistribMulAction S N₂]
    [SMulCommClass R S N] [SMulCommClass R S N₂] [CompatibleSMul N N₂ S R]
    (g : N →ₗ[R] N₂) (s : S) (f : M [Sym^ι]→ₗ[R] N) :
    g.compSymmetricMap (s • f) = s • g.compSymmetricMap f :=
  SymmetricMap.ext fun _ ↦ g.map_smul_of_tower _ _

@[simp]
theorem smul_compSymmetricMap [Monoid S] [DistribMulAction S N₂] [SMulCommClass R S N₂]
    (g : N →ₗ[R] N₂) (s : S) (f : M [Sym^ι]→ₗ[R] N) :
    (s • g).compSymmetricMap f = s • g.compSymmetricMap f := rfl

variable (S) in
/-- `LinearMap.compSymmetricMap` as an `S`-linear map. -/
@[simps]
def compSymmetricMapₗ [Semiring S] [Module S N] [Module S N₂]
    [SMulCommClass R S N] [SMulCommClass R S N₂] [LinearMap.CompatibleSMul N N₂ S R]
    (g : N →ₗ[R] N₂) :
    (M [Sym^ι]→ₗ[R] N) →ₗ[S] (M [Sym^ι]→ₗ[R] N₂) where
  toFun := g.compSymmetricMap
  map_add' := g.compSymmetricMap_add
  map_smul' := g.compSymmetricMap_smul

theorem _root_.SymmetricMap.smulRight_eq_comp
    {R M₁ M₂ ι : Type*} [CommSemiring R] [AddCommMonoid M₁]
    [AddCommMonoid M₂] [Module R M₁] [Module R M₂] (f : M₁ [Sym^ι]→ₗ[R] R) (z : M₂) :
    f.smulRight z = (LinearMap.id.smulRight z).compSymmetricMap f :=
  rfl

@[simp]
theorem subtype_compSymmetricMap_codRestrict (f : M [Sym^ι]→ₗ[R] N) (p : Submodule R N)
    (h) : p.subtype.compSymmetricMap (f.codRestrict p h) = f :=
  SymmetricMap.ext fun _ ↦ rfl

@[simp]
theorem compSymmetricMap_codRestrict (g : N →ₗ[R] N₂) (f : M [Sym^ι]→ₗ[R] N)
    (p : Submodule R N₂) (h) :
    (g.codRestrict p h).compSymmetricMap f =
      (g.compSymmetricMap f).codRestrict p fun v ↦ h (f v) :=
  SymmetricMap.ext fun _ ↦ rfl

end LinearMap

namespace SymmetricMap

variable {M₂ : Type*} [AddCommMonoid M₂] [Module R M₂]
variable {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃]

/-- Composing a symmetric map with the same linear map on each argument gives again a symmetric
map. -/
def compLinearMap (f : M [Sym^ι]→ₗ[R] N) (g : M₂ →ₗ[R] M) : M₂ [Sym^ι]→ₗ[R] N :=
  { (f : MultilinearMap R (fun _ : ι ↦ M) N).compLinearMap fun _ ↦ g with
    map_eq_map_of_swap' v i j _ := by
      have aux := f.map_eq_map_of_swap' (g ∘ v) i j
      simpa }

theorem coe_compLinearMap (f : M [Sym^ι]→ₗ[R] N) (g : M₂ →ₗ[R] M) :
    ⇑(f.compLinearMap g) = f ∘ (g ∘ ·) :=
  rfl

@[simp]
theorem compLinearMap_apply (f : M [Sym^ι]→ₗ[R] N) (g : M₂ →ₗ[R] M) (v : ι → M₂) :
    f.compLinearMap g v = f fun i ↦ g (v i) :=
  rfl

/-- Composing a symmetric map twice with the same linear map in each argument is
the same as composing with their composition. -/
theorem compLinearMap_assoc (f : M [Sym^ι]→ₗ[R] N) (g₁ : M₂ →ₗ[R] M) (g₂ : M₃ →ₗ[R] M₂) :
    (f.compLinearMap g₁).compLinearMap g₂ = f.compLinearMap (g₁ ∘ₗ g₂) :=
  rfl

@[simp]
theorem zero_compLinearMap (g : M₂ →ₗ[R] M) : (0 : M [Sym^ι]→ₗ[R] N).compLinearMap g = 0 := by
  ext
  simp only [compLinearMap_apply, zero_apply]

@[simp]
theorem add_compLinearMap (f₁ f₂ : M [Sym^ι]→ₗ[R] N) (g : M₂ →ₗ[R] M) :
    (f₁ + f₂).compLinearMap g = f₁.compLinearMap g + f₂.compLinearMap g := by
  ext
  simp only [compLinearMap_apply, add_apply]

@[simp]
theorem compLinearMap_zero [Nonempty ι] (f : M [Sym^ι]→ₗ[R] N) :
    f.compLinearMap (0 : M₂ →ₗ[R] M) = 0 := by
  ext
  simp_rw [compLinearMap_apply, LinearMap.zero_apply, ← Pi.zero_def, map_zero, zero_apply]

/-- Composing a symmetric map with the identity linear map in each argument. -/
@[simp]
theorem compLinearMap_id (f : M [Sym^ι]→ₗ[R] N) : f.compLinearMap LinearMap.id = f :=
  ext fun _ ↦ rfl

/-- Composing with a surjective linear map is injective. -/
theorem compLinearMap_injective (f : M₂ →ₗ[R] M) (hf : Function.Surjective f) :
    Function.Injective fun g : M [Sym^ι]→ₗ[R] N ↦ g.compLinearMap f := fun g₁ g₂ h ↦
  ext fun x ↦ by
    simpa [Function.surjInv_eq hf] using SymmetricMap.ext_iff.mp h (Function.surjInv hf ∘ x)

theorem compLinearMap_inj (f : M₂ →ₗ[R] M) (hf : Function.Surjective f)
    (g₁ g₂ : M [Sym^ι]→ₗ[R] N) : g₁.compLinearMap f = g₂.compLinearMap f ↔ g₁ = g₂ :=
  (compLinearMap_injective _ hf).eq_iff

/-- If two `R`-symmetric maps from `R` are equal on 1, then they are equal.

This is the symmetric version of `LinearMap.ext_ring`. -/
@[ext]
theorem ext_ring {R} [CommSemiring R] [Module R N] [Finite ι] ⦃f g : R [Sym^ι]→ₗ[R] N⦄
    (h : f (fun _ ↦ 1) = g (fun _ ↦ 1)) : f = g :=
  coe_multilinearMap_injective <| MultilinearMap.ext_ring h

section DomLcongr

variable (ι R N)
variable (S : Type*) [Semiring S] [Module S N] [SMulCommClass R S N]

/-- Construct a linear equivalence between maps from a linear equivalence between domains.

This is `SymmetricMap.compLinearMap` as an isomorphism,
and the symmetric version of `LinearEquiv.multilinearMapCongrLeft`.
It could also have been called `LinearEquiv.symmetricMapCongrLeft`. -/
@[simps apply]
def domLCongr (e : M ≃ₗ[R] M₂) : M [Sym^ι]→ₗ[R] N ≃ₗ[S] (M₂ [Sym^ι]→ₗ[R] N) where
  toFun f := f.compLinearMap e.symm
  invFun g := g.compLinearMap e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := SymmetricMap.ext fun _ ↦ f.congr_arg <| funext fun _ ↦ e.symm_apply_apply _
  right_inv f := SymmetricMap.ext fun _ ↦ f.congr_arg <| funext fun _ ↦ e.apply_symm_apply _

@[simp]
theorem domLCongr_refl : domLCongr R N ι S (LinearEquiv.refl R M) = LinearEquiv.refl S _ :=
  LinearEquiv.ext fun _ ↦ SymmetricMap.ext fun _ ↦ rfl

@[simp]
theorem domLCongr_symm (e : M ≃ₗ[R] M₂) : (domLCongr R N ι S e).symm = domLCongr R N ι S e.symm :=
  rfl

theorem domLCongr_trans (e : M ≃ₗ[R] M₂) (f : M₂ ≃ₗ[R] M₃) :
    (domLCongr R N ι S e).trans (domLCongr R N ι S f) = domLCongr R N ι S (e.trans f) :=
  rfl

end DomLcongr

/-- Composing a symmetric map with the same linear equiv on each argument gives the zero map
if and only if the symmetric map is the zero map. -/
@[simp]
theorem compLinearEquiv_eq_zero_iff (f : M [Sym^ι]→ₗ[R] N) (g : M₂ ≃ₗ[R] M) :
    f.compLinearMap (g : M₂ →ₗ[R] M) = 0 ↔ f = 0 :=
  (domLCongr R N ι ℕ g.symm).map_eq_zero_iff

variable (f f' : M [Sym^ι]→ₗ[R] N)
variable (g g₂ : M [Sym^ι]→ₗ[R] N')
variable (g' : M' [Sym^ι]→ₗ[R] N')
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
    (f : M [Sym^ι]→ₗ[R] N) (c : ι → R) (m : ι → M) :
    (f fun i ↦ c i • m i) = (∏ i, c i) • f m :=
  f.toMultilinearMap.map_smul_univ c m

end

/-!
### Theorems specific to symmetric maps -/

-- TODO: necessary, or already implied by previous results?
theorem map_swap [DecidableEq ι] {i j : ι} : g (v ∘ Equiv.swap i j) = g v := by simp

@[simp]
theorem map_perm [Finite ι] (v : ι → M) (σ : Equiv.Perm ι) :
    g (v ∘ σ) = g v := by
  classical
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => simp
  | mul_swap s x y hxy hI =>
    simp_all [← Function.comp_assoc, g.map_swap]

theorem map_congr_perm [Finite ι] (σ : Equiv.Perm ι) : g v = g (v ∘ σ) := by simp

section DomDomCongr

/-- Transfer the arguments to a map along an equivalence between argument indices.

This is the symmetric version of `MultilinearMap.domDomCongr`. -/
@[simps]
def domDomCongr (σ : ι ≃ ι') (f : M [Sym^ι]→ₗ[R] N) : M [Sym^ι']→ₗ[R] N :=
  { f.toMultilinearMap.domDomCongr σ with
    toFun := fun v ↦ f (v ∘ σ)
    -- map_eq_zero_of_eq' := fun v i j hv hij ↦
    --   f.map_eq_zero_of_eq (v ∘ σ) (i := σ.symm i) (j := σ.symm j)
    --     (by simpa using hv) (σ.symm.injective.ne hij)
    map_eq_map_of_swap' v i j inst := by
      classical
      --rename_i f₀ v
      have aux := f.map_eq_map_of_swap' (v ∘ σ) (σ.symm i) (σ.symm j)
      simp only [MultilinearMap.toFun_eq_coe, coe_multilinearMap] at aux
      rw [← aux]
      simp only [map_eq_map_of_swap]
      --simp
      sorry--apply f.map_eq_map_of_swap' (v ∘ σ) (i := σ.symm i) (j := σ.symm j)
       }
#exit
@[simp]
theorem domDomCongr_refl (f : M [Sym^ι]→ₗ[R] N) : f.domDomCongr (Equiv.refl ι) = f := rfl

theorem domDomCongr_trans (σ₁ : ι ≃ ι') (σ₂ : ι' ≃ ι'') (f : M [Sym^ι]→ₗ[R] N) :
    f.domDomCongr (σ₁.trans σ₂) = (f.domDomCongr σ₁).domDomCongr σ₂ :=
  rfl

@[simp]
theorem domDomCongr_zero (σ : ι ≃ ι') : (0 : M [Sym^ι]→ₗ[R] N).domDomCongr σ = 0 :=
  rfl

@[simp]
theorem domDomCongr_add (σ : ι ≃ ι') (f g : M [Sym^ι]→ₗ[R] N) :
    (f + g).domDomCongr σ = f.domDomCongr σ + g.domDomCongr σ :=
  rfl

@[simp]
theorem domDomCongr_smul {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]
    (σ : ι ≃ ι') (c : S) (f : M [Sym^ι]→ₗ[R] N) :
    (c • f).domDomCongr σ = c • f.domDomCongr σ :=
  rfl

/-- `SymmetricMap.domDomCongr` as an equivalence.

This is declared separately because it does not work with dot notation. -/
@[simps apply symm_apply]
def domDomCongrEquiv (σ : ι ≃ ι') : M [Sym^ι]→ₗ[R] N ≃+ M [Sym^ι']→ₗ[R] N where
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

/-- `SymmetricMap.domDomCongr` as a linear equivalence. -/
@[simps apply symm_apply]
def domDomCongrₗ (σ : ι ≃ ι') : M [Sym^ι]→ₗ[R] N ≃ₗ[S] M [Sym^ι']→ₗ[R] N where
  toFun := domDomCongr σ
  invFun := domDomCongr σ.symm
  left_inv f := by ext; simp [Function.comp_def]
  right_inv m := by ext; simp [Function.comp_def]
  map_add' := domDomCongr_add σ
  map_smul' := domDomCongr_smul σ

@[simp]
theorem domDomCongrₗ_refl :
    (domDomCongrₗ S (Equiv.refl ι) : M [Sym^ι]→ₗ[R] N ≃ₗ[S] M [Sym^ι]→ₗ[R] N) =
      LinearEquiv.refl _ _ :=
  rfl

@[simp]
theorem domDomCongrₗ_toAddEquiv (σ : ι ≃ ι') :
    (↑(domDomCongrₗ S σ : M [Sym^ι]→ₗ[R] N ≃ₗ[S] _) : M [Sym^ι]→ₗ[R] N ≃+ _) =
      domDomCongrEquiv σ :=
  rfl

end DomDomLcongr

/-- The results of applying `domDomCongr` to two maps are equal if and only if those maps are. -/
@[simp]
theorem domDomCongr_eq_iff (σ : ι ≃ ι') (f g : M [Sym^ι]→ₗ[R] N) :
    f.domDomCongr σ = g.domDomCongr σ ↔ f = g :=
  (domDomCongrEquiv σ : _ ≃+ M [Sym^ι']→ₗ[R] N).apply_eq_iff_eq

@[simp]
theorem domDomCongr_eq_zero_iff (σ : ι ≃ ι') (f : M [Sym^ι]→ₗ[R] N) :
    f.domDomCongr σ = 0 ↔ f = 0 :=
  (domDomCongrEquiv σ : M [Sym^ι]→ₗ[R] N ≃+ M [Sym^ι']→ₗ[R] N).map_eq_zero_iff

theorem domDomCongr_perm [Finite ι] (σ : Equiv.Perm ι) : g.domDomCongr σ = g := by ext v; simp

@[norm_cast]
theorem coe_domDomCongr (σ : ι ≃ ι') :
    ↑(f.domDomCongr σ) = (f : MultilinearMap R (fun _ : ι ↦ M) N).domDomCongr σ :=
  MultilinearMap.ext fun _ ↦ rfl

end DomDomCongr

section Fin

open Fin

/-- A version of `MultilinearMap.cons_add` for `SymmetricMap`. -/
theorem map_vecCons_add {n : ℕ} (f : M [Sym^Fin n.succ]→ₗ[R] N) (m : Fin n → M) (x y : M) :
    f (Matrix.vecCons (x + y) m) = f (Matrix.vecCons x m) + f (Matrix.vecCons y m) :=
  f.toMultilinearMap.cons_add _ _ _

/-- A version of `MultilinearMap.cons_smul` for `SymmetricMap`. -/
theorem map_vecCons_smul {n : ℕ} (f : M [Sym^Fin n.succ]→ₗ[R] N) (m : Fin n → M) (c : R)
    (x : M) : f (Matrix.vecCons (c • x) m) = c • f (Matrix.vecCons x m) :=
  f.toMultilinearMap.cons_smul _ _ _

end Fin

end SymmetricMap

namespace MultilinearMap

open Equiv

variable [Fintype ι] [DecidableEq ι]

-- private theorem alternization_map_eq_zero_of_eq_aux (m : MultilinearMap R (fun _ : ι ↦ M) N')
--     (v : ι → M) (i j : ι) (i_ne_j : i ≠ j) (hv : v i = v j) :
--     (∑ σ : Perm ι, Equiv.Perm.sign σ • m.domDomCongr σ) v = 0 := by
--   rw [sum_apply]
--   exact
--     Finset.sum_involution (fun σ _ ↦ swap i j * σ)
--       (fun σ _ ↦ by simp [Perm.sign_swap i_ne_j, apply_swap_eq_self hv])
--       (fun σ _ _ ↦ (not_congr swap_mul_eq_iff).mpr i_ne_j) (fun σ _ ↦ Finset.mem_univ _)
--       fun σ _ ↦ swap_mul_involutive i j σ

/-- Produce a `SymmetricMap` out of a `MultilinearMap`, by summing over all argument
permutations. -/
def symmetrization : MultilinearMap R (fun _ : ι ↦ M) N' →+ M [Sym^ι]→ₗ[R] N' where
  toFun m :=
    { ∑ σ : Perm ι, m.domDomCongr σ with
      toFun := ⇑(∑ σ : Perm ι, m.domDomCongr σ)
      -- proof in the alternating case is essentially alternization_map_eq_zero_of_eq_aux
      -- TODO: think about this and fill it in!
      map_eq_map_of_swap' v i j _ := by sorry }
  map_add' a b := by ext; simp [Finset.sum_add_distrib]
  map_zero' := by ext; simp

theorem symmetrization_def (m : MultilinearMap R (fun _ : ι ↦ M) N') :
    ⇑(symmetrization m) = (∑ σ : Perm ι, m.domDomCongr σ :) :=
  rfl

theorem symmetrization_coe (m : MultilinearMap R (fun _ : ι ↦ M) N') :
    ↑(symmetrization m) = (∑ σ : Perm ι, m.domDomCongr σ :) :=
  coe_injective rfl

theorem symmetrization_apply (m : MultilinearMap R (fun _ : ι ↦ M) N') (v : ι → M) :
    symmetrization m v = ∑ σ : Perm ι, m.domDomCongr σ v := by
  simp only [symmetrization_def, sum_apply]

end MultilinearMap

namespace SymmetricMap

/-- Symmetrizing a multilinear map that is already symmetric results in a scale factor of `n!`,
where `n` is the number of inputs. -/
theorem coe_symmetrization [DecidableEq ι] [Fintype ι] (a : M [Sym^ι]→ₗ[R] N') :
    MultilinearMap.symmetrization (a : MultilinearMap R (fun _ ↦ M) N')
    = Nat.factorial (Fintype.card ι) • a := by
  apply SymmetricMap.coe_injective
  simp_rw [MultilinearMap.symmetrization_def, ← coe_domDomCongr, domDomCongr_perm,
    Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    ← coe_multilinearMap, coe_smul]

end SymmetricMap

namespace LinearMap

variable {N'₂ : Type*} [AddCommGroup N'₂] [Module R N'₂] [DecidableEq ι] [Fintype ι]

/-- Composition with a linear map before and after symmetrization are equivalent. -/
theorem compMultilinearMap_symmetrization (g : N' →ₗ[R] N'₂)
    (f : MultilinearMap R (fun _ : ι ↦ M) N') :
    MultilinearMap.symmetrization (g.compMultilinearMap f)
      = g.compSymmetricMap (MultilinearMap.symmetrization f) := by
  ext
  simp [MultilinearMap.symmetrization_def]

end LinearMap

section Basis

open SymmetricMap

variable {ι₁ : Type*} [Finite ι]
  {R' : Type*} {N₁ N₂ : Type*} [CommSemiring R'] [AddCommMonoid N₁] [AddCommMonoid N₂]
  [Module R' N₁] [Module R' N₂]

/-- Two symmetric maps indexed by a `Fintype` are equal if they are equal when all arguments
are distinct basis vectors. -/
-- TODO: is this actually true for symmetric maps?? if so, fix the proof!
theorem Module.Basis.ext_symmetric {f g : N₁ [Sym^ι]→ₗ[R'] N₂} (e : Basis ι₁ R' N₁)
    (h : ∀ v : ι → ι₁, Function.Injective v → (f fun i ↦ e (v i)) = g fun i ↦ e (v i)) :
    f = g := by
  refine SymmetricMap.coe_multilinearMap_injective (Basis.ext_multilinear (fun _ ↦ e) fun v ↦ ?_)
  by_cases hi : Function.Injective v
  · exact h v hi
  · have : ¬Function.Injective fun i ↦ e (v i) := hi.imp Function.Injective.of_comp
    sorry --rw [coe_multilinearMap, coe_multilinearMap, f.map_eq_zero_of_not_injective _ this,
    --  g.map_eq_zero_of_not_injective _ this]

end Basis

variable {R' : Type*} {M'' M₂'' N'' N₂'' : Type*} [CommSemiring R'] [AddCommMonoid M'']
  [AddCommMonoid M₂''] [AddCommMonoid N''] [AddCommMonoid N₂''] [Module R' M''] [Module R' M₂'']
  [Module R' N''] [Module R' N₂'']

/-- An isomorphism of multilinear maps given an isomorphism between their codomains.

This is `Linear.compSymmetricMap` as an isomorphism,
and the symmetric version of `LinearEquiv.multilinearMapCongrRight`. -/
@[simps!]
def LinearEquiv.symmetricMapCongrRight (e : N'' ≃ₗ[R'] N₂'') :
    M'' [Sym^ι]→ₗ[R'] N'' ≃ₗ[R'] (M'' [Sym^ι]→ₗ[R'] N₂'') where
  toFun f := e.compSymmetricMap f
  invFun f := e.symm.compSymmetricMap f
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

/-- The space of constant maps is equivalent to the space of maps that are symmetric with respect
to an empty family. -/
@[simps]
def Symmetric.constLinearEquivOfIsEmpty [IsEmpty ι] : N'' ≃ₗ[R'] (M'' [Sym^ι]→ₗ[R'] N'') where
  toFun := SymmetricMap.constOfIsEmpty R' M'' ι
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := f 0
  right_inv f := by--ext fun _ ↦ AlternatingMap.congr_arg f <| Subsingleton.elim _ _
    ext
    sorry
