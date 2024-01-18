/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
import Mathlib.Algebra.Module.Hom
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Data.Set.Finite
import Mathlib.Order.ConditionallyCompleteLattice.Basic

#align_import linear_algebra.basic from "leanprover-community/mathlib"@"9d684a893c52e1d6692a504a118bfccbae04feeb"

/-!
# Linear algebra

This file defines the basics of linear algebra. It sets up the "categorical/lattice structure" of
modules over a ring, submodules, and linear maps.

Many of the relevant definitions, including `Module`, `Submodule`, and `LinearMap`, are found in
`Algebra/Module`.

## Main definitions

* Many constructors for (semi)linear maps
* The kernel `ker` and range `range` of a linear map are submodules of the domain and codomain
  respectively.

See `LinearAlgebra.Span` for the span of a set (as a submodule),
and `LinearAlgebra.Quotient` for quotients by submodules.

## Main theorems

See `LinearAlgebra.Isomorphisms` for Noether's three isomorphism theorems for modules.

## Notations

* We continue to use the notations `M →ₛₗ[σ] M₂` and `M →ₗ[R] M₂` for the type of semilinear
  (resp. linear) maps from `M` to `M₂` over the ring homomorphism `σ` (resp. over the ring `R`).

## Implementation notes

We note that, when constructing linear maps, it is convenient to use operations defined on bundled
maps (`LinearMap.prod`, `LinearMap.coprod`, arithmetic operations like `+`) instead of defining a
function and proving it is linear.

## TODO

* Parts of this file have not yet been generalized to semilinear maps

## Tags
linear algebra, vector space, module

-/

open Function

open BigOperators Pointwise

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*} {R₄ : Type*}
variable {S : Type*}
variable {K : Type*} {K₂ : Type*}
variable {M : Type*} {M' : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*} {M₄ : Type*}
variable {N : Type*} {N₂ : Type*}
variable {ι : Type*}
variable {V : Type*} {V₂ : Type*}

/-! ### Properties of linear maps -/

/--
The `R`-linear equivalence between additive morphisms `A →+ B` and `ℕ`-linear morphisms `A →ₗ[ℕ] B`.
-/
@[simps]
def addMonoidHomLequivNat {A B : Type*} (R : Type*) [Semiring R] [AddCommMonoid A]
    [AddCommMonoid B] [Module R B] : (A →+ B) ≃ₗ[R] A →ₗ[ℕ] B
    where
  toFun := AddMonoidHom.toNatLinearMap
  invFun := LinearMap.toAddMonoidHom
  map_add' := by intros; ext; rfl
  map_smul' := by intros; ext; rfl
  left_inv := by intro f; ext; rfl
  right_inv := by intro f; ext; rfl
#align add_monoid_hom_lequiv_nat addMonoidHomLequivNat

/--
The `R`-linear equivalence between additive morphisms `A →+ B` and `ℤ`-linear morphisms `A →ₗ[ℤ] B`.
-/
@[simps]
def addMonoidHomLequivInt {A B : Type*} (R : Type*) [Semiring R] [AddCommGroup A] [AddCommGroup B]
    [Module R B] : (A →+ B) ≃ₗ[R] A →ₗ[ℤ] B
    where
  toFun := AddMonoidHom.toIntLinearMap
  invFun := LinearMap.toAddMonoidHom
  map_add' := by intros; ext; rfl
  map_smul' := by intros; ext; rfl
  left_inv := by intro f; ext; rfl
  right_inv := by intro f; ext; rfl
#align add_monoid_hom_lequiv_int addMonoidHomLequivInt

/-- Ring equivalence between additive group endomorphisms of an `AddCommGroup` `A` and
`ℤ`-module endomorphisms of `A.` -/
@[simps] def addMonoidEndRingEquivInt (A : Type*) [AddCommGroup A] :
    AddMonoid.End A ≃+* Module.End ℤ A :=
  { addMonoidHomLequivInt (B := A) ℤ with
    map_mul' := fun _ _ => rfl }

/-! ### Properties of linear maps -/


namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

open Submodule

variable {σ₂₁ : R₂ →+* R} {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}

variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

theorem map_codRestrict [RingHomSurjective σ₂₁] (p : Submodule R M) (f : M₂ →ₛₗ[σ₂₁] M) (h p') :
    Submodule.map (codRestrict p f h) p' = comap p.subtype (p'.map f) :=
  Submodule.ext fun ⟨x, hx⟩ => by simp [Subtype.ext_iff_val]
#align linear_map.map_cod_restrict LinearMap.map_codRestrict

theorem comap_codRestrict (p : Submodule R M) (f : M₂ →ₛₗ[σ₂₁] M) (hf p') :
    Submodule.comap (codRestrict p f hf) p' = Submodule.comap f (map p.subtype p') :=
  Submodule.ext fun x => ⟨fun h => ⟨⟨_, hf x⟩, h, rfl⟩, by rintro ⟨⟨_, _⟩, h, ⟨⟩⟩; exact h⟩
#align linear_map.comap_cod_restrict LinearMap.comap_codRestrict

section

variable {F : Type*} [sc : SemilinearMapClass F τ₁₂ M M₂]

/-- The range of a linear map `f : M → M₂` is a submodule of `M₂`.
See Note [range copy pattern]. -/
def range [RingHomSurjective τ₁₂] (f : F) : Submodule R₂ M₂ :=
  (map f ⊤).copy (Set.range f) Set.image_univ.symm
#align linear_map.range LinearMap.range

theorem range_coe [RingHomSurjective τ₁₂] (f : F) : (range f : Set M₂) = Set.range f :=
  rfl
#align linear_map.range_coe LinearMap.range_coe

theorem range_toAddSubmonoid [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) :
    f.range.toAddSubmonoid = AddMonoidHom.mrange f :=
  rfl
#align linear_map.range_to_add_submonoid LinearMap.range_toAddSubmonoid

@[simp]
theorem mem_range [RingHomSurjective τ₁₂] {f : F} {x} : x ∈ range f ↔ ∃ y, f y = x :=
  Iff.rfl
#align linear_map.mem_range LinearMap.mem_range

theorem range_eq_map [RingHomSurjective τ₁₂] (f : F) : range f = map f ⊤ := by
  ext
  simp
#align linear_map.range_eq_map LinearMap.range_eq_map

theorem mem_range_self [RingHomSurjective τ₁₂] (f : F) (x : M) : f x ∈ range f :=
  ⟨x, rfl⟩
#align linear_map.mem_range_self LinearMap.mem_range_self

@[simp]
theorem range_id : range (LinearMap.id : M →ₗ[R] M) = ⊤ :=
  SetLike.coe_injective Set.range_id
#align linear_map.range_id LinearMap.range_id

theorem range_comp [RingHomSurjective τ₁₂] [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃]
    (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃) : range (g.comp f : M →ₛₗ[τ₁₃] M₃) = map g (range f) :=
  SetLike.coe_injective (Set.range_comp g f)
#align linear_map.range_comp LinearMap.range_comp

theorem range_comp_le_range [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃] (f : M →ₛₗ[τ₁₂] M₂)
    (g : M₂ →ₛₗ[τ₂₃] M₃) : range (g.comp f : M →ₛₗ[τ₁₃] M₃) ≤ range g :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)
#align linear_map.range_comp_le_range LinearMap.range_comp_le_range

theorem range_eq_top [RingHomSurjective τ₁₂] {f : F} : range f = ⊤ ↔ Surjective f := by
  rw [SetLike.ext'_iff, range_coe, top_coe, Set.range_iff_surjective]
#align linear_map.range_eq_top LinearMap.range_eq_top

theorem range_le_iff_comap [RingHomSurjective τ₁₂] {f : F} {p : Submodule R₂ M₂} :
    range f ≤ p ↔ comap f p = ⊤ := by rw [range_eq_map, map_le_iff_le_comap, eq_top_iff]
#align linear_map.range_le_iff_comap LinearMap.range_le_iff_comap

theorem map_le_range [RingHomSurjective τ₁₂] {f : F} {p : Submodule R M} : map f p ≤ range f :=
  SetLike.coe_mono (Set.image_subset_range f p)
#align linear_map.map_le_range LinearMap.map_le_range

@[simp]
theorem range_neg {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*} [Semiring R] [Ring R₂]
    [AddCommMonoid M] [AddCommGroup M₂] [Module R M] [Module R₂ M₂] {τ₁₂ : R →+* R₂}
    [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : LinearMap.range (-f) = LinearMap.range f := by
  change range ((-LinearMap.id : M₂ →ₗ[R₂] M₂).comp f) = _
  rw [range_comp, Submodule.map_neg, Submodule.map_id]
#align linear_map.range_neg LinearMap.range_neg

lemma range_domRestrict_le_range [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) (S : Submodule R M) :
    LinearMap.range (f.domRestrict S) ≤ LinearMap.range f := by
  rintro x ⟨⟨y, hy⟩, rfl⟩
  exact LinearMap.mem_range_self f y

@[simp]
theorem _root_.AddMonoidHom.coe_toIntLinearMap_range {M M₂ : Type*} [AddCommGroup M]
    [AddCommGroup M₂] (f : M →+ M₂) :
    LinearMap.range f.toIntLinearMap = AddSubgroup.toIntSubmodule f.range := rfl

/-- A linear map version of `AddMonoidHom.eqLocusM` -/
def eqLocus (f g : F) : Submodule R M :=
  { (f : M →+ M₂).eqLocusM g with
    carrier := { x | f x = g x }
    smul_mem' := fun {r} {x} (hx : _ = _) => show _ = _ by
      simpa only [map_smulₛₗ] using congr_arg (τ₁₂ r • ·) hx }
#align linear_map.eq_locus LinearMap.eqLocus

@[simp]
theorem mem_eqLocus {x : M} {f g : F} : x ∈ eqLocus f g ↔ f x = g x :=
  Iff.rfl
#align linear_map.mem_eq_locus LinearMap.mem_eqLocus

theorem eqLocus_toAddSubmonoid (f g : F) :
    (eqLocus f g).toAddSubmonoid = (f : M →+ M₂).eqLocusM g :=
  rfl
#align linear_map.eq_locus_to_add_submonoid LinearMap.eqLocus_toAddSubmonoid

@[simp]
theorem eqLocus_eq_top {f g : F} : eqLocus f g = ⊤ ↔ f = g := by
  simp [SetLike.ext_iff, FunLike.ext_iff]

@[simp]
theorem eqLocus_same (f : F) : eqLocus f f = ⊤ := eqLocus_eq_top.2 rfl
#align linear_map.eq_locus_same LinearMap.eqLocus_same

theorem le_eqLocus {f g : F} {S : Submodule R M} : S ≤ eqLocus f g ↔ Set.EqOn f g S := Iff.rfl

theorem eqOn_sup {f g : F} {S T : Submodule R M} (hS : Set.EqOn f g S) (hT : Set.EqOn f g T) :
    Set.EqOn f g ↑(S ⊔ T) := by
  rw [← le_eqLocus] at hS hT ⊢
  exact sup_le hS hT

theorem ext_on_codisjoint {f g : F} {S T : Submodule R M} (hST : Codisjoint S T)
    (hS : Set.EqOn f g S) (hT : Set.EqOn f g T) : f = g :=
  FunLike.ext _ _ fun _ ↦ eqOn_sup hS hT <| hST.eq_top.symm ▸ trivial

end

/-- The decreasing sequence of submodules consisting of the ranges of the iterates of a linear map.
-/
@[simps]
def iterateRange (f : M →ₗ[R] M) : ℕ →o (Submodule R M)ᵒᵈ where
  toFun n := LinearMap.range (f ^ n)
  monotone' n m w x h := by
    obtain ⟨c, rfl⟩ := le_iff_exists_add.mp w
    rw [LinearMap.mem_range] at h
    obtain ⟨m, rfl⟩ := h
    rw [LinearMap.mem_range]
    use (f ^ c) m
    rw [pow_add, LinearMap.mul_apply]
#align linear_map.iterate_range LinearMap.iterateRange

/-- Restrict the codomain of a linear map `f` to `f.range`.

This is the bundled version of `Set.rangeFactorization`. -/
@[reducible]
def rangeRestrict [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : M →ₛₗ[τ₁₂] LinearMap.range f :=
  f.codRestrict (LinearMap.range f) (LinearMap.mem_range_self f)
#align linear_map.range_restrict LinearMap.rangeRestrict

/-- The range of a linear map is finite if the domain is finite.
Note: this instance can form a diamond with `Subtype.fintype` in the
  presence of `Fintype M₂`. -/
instance fintypeRange [Fintype M] [DecidableEq M₂] [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) :
    Fintype (range f) :=
  Set.fintypeRange f
#align linear_map.fintype_range LinearMap.fintypeRange

variable {F : Type*} [sc : SemilinearMapClass F τ₁₂ M M₂]

/-- The kernel of a linear map `f : M → M₂` is defined to be `comap f ⊥`. This is equivalent to the
set of `x : M` such that `f x = 0`. The kernel is a submodule of `M`. -/
def ker (f : F) : Submodule R M :=
  comap f ⊥
#align linear_map.ker LinearMap.ker

@[simp]
theorem mem_ker {f : F} {y} : y ∈ ker f ↔ f y = 0 :=
  mem_bot R₂
#align linear_map.mem_ker LinearMap.mem_ker

@[simp]
theorem ker_id : ker (LinearMap.id : M →ₗ[R] M) = ⊥ :=
  rfl
#align linear_map.ker_id LinearMap.ker_id

@[simp]
theorem map_coe_ker (f : F) (x : ker f) : f x = 0 :=
  mem_ker.1 x.2
#align linear_map.map_coe_ker LinearMap.map_coe_ker

theorem ker_toAddSubmonoid (f : M →ₛₗ[τ₁₂] M₂) : f.ker.toAddSubmonoid = (AddMonoidHom.mker f) :=
  rfl
#align linear_map.ker_to_add_submonoid LinearMap.ker_toAddSubmonoid

theorem comp_ker_subtype (f : M →ₛₗ[τ₁₂] M₂) : f.comp f.ker.subtype = 0 :=
  LinearMap.ext fun x => mem_ker.1 x.2
#align linear_map.comp_ker_subtype LinearMap.comp_ker_subtype

theorem ker_comp (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃) :
    ker (g.comp f : M →ₛₗ[τ₁₃] M₃) = comap f (ker g) :=
  rfl
#align linear_map.ker_comp LinearMap.ker_comp

theorem ker_le_ker_comp (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃) :
    ker f ≤ ker (g.comp f : M →ₛₗ[τ₁₃] M₃) := by rw [ker_comp]; exact comap_mono bot_le
#align linear_map.ker_le_ker_comp LinearMap.ker_le_ker_comp

theorem ker_sup_ker_le_ker_comp_of_commute {f g : M →ₗ[R] M} (h : Commute f g) :
    ker f ⊔ ker g ≤ ker (f ∘ₗ g) := by
  refine sup_le_iff.mpr ⟨?_, ker_le_ker_comp g f⟩
  rw [← mul_eq_comp, h.eq, mul_eq_comp]
  exact ker_le_ker_comp f g

@[simp]
theorem ker_le_comap {p : Submodule R₂ M₂} (f : M →ₛₗ[τ₁₂] M₂) :
    ker f ≤ p.comap f :=
  fun x hx ↦ by simp [mem_ker.mp hx]

theorem disjoint_ker {f : F} {p : Submodule R M} :
    Disjoint p (ker f) ↔ ∀ x ∈ p, f x = 0 → x = 0 := by
  simp [disjoint_def]
#align linear_map.disjoint_ker LinearMap.disjoint_ker

theorem ker_eq_bot' {f : F} : ker f = ⊥ ↔ ∀ m, f m = 0 → m = 0 := by
  simpa [disjoint_iff_inf_le] using disjoint_ker (f := f) (p := ⊤)
#align linear_map.ker_eq_bot' LinearMap.ker_eq_bot'

theorem ker_eq_bot_of_inverse {τ₂₁ : R₂ →+* R} [RingHomInvPair τ₁₂ τ₂₁] {f : M →ₛₗ[τ₁₂] M₂}
    {g : M₂ →ₛₗ[τ₂₁] M} (h : (g.comp f : M →ₗ[R] M) = id) : ker f = ⊥ :=
  ker_eq_bot'.2 fun m hm => by rw [← id_apply (R := R) m, ← h, comp_apply, hm, g.map_zero]
#align linear_map.ker_eq_bot_of_inverse LinearMap.ker_eq_bot_of_inverse

theorem le_ker_iff_map [RingHomSurjective τ₁₂] {f : F} {p : Submodule R M} :
    p ≤ ker f ↔ map f p = ⊥ := by rw [ker, eq_bot_iff, map_le_iff_le_comap]
#align linear_map.le_ker_iff_map LinearMap.le_ker_iff_map

theorem ker_codRestrict {τ₂₁ : R₂ →+* R} (p : Submodule R M) (f : M₂ →ₛₗ[τ₂₁] M) (hf) :
    ker (codRestrict p f hf) = ker f := by rw [ker, comap_codRestrict, Submodule.map_bot]; rfl
#align linear_map.ker_cod_restrict LinearMap.ker_codRestrict

theorem range_codRestrict {τ₂₁ : R₂ →+* R} [RingHomSurjective τ₂₁] (p : Submodule R M)
    (f : M₂ →ₛₗ[τ₂₁] M) (hf) :
    range (codRestrict p f hf) = comap p.subtype (LinearMap.range f) := by
  simpa only [range_eq_map] using map_codRestrict _ _ _ _
#align linear_map.range_cod_restrict LinearMap.range_codRestrict

theorem ker_restrict [AddCommMonoid M₁] [Module R M₁] {p : Submodule R M} {q : Submodule R M₁}
    {f : M →ₗ[R] M₁} (hf : ∀ x : M, x ∈ p → f x ∈ q) :
    ker (f.restrict hf) = LinearMap.ker (f.domRestrict p) := by
  rw [restrict_eq_codRestrict_domRestrict, ker_codRestrict]
#align linear_map.ker_restrict LinearMap.ker_restrict

theorem _root_.Submodule.map_comap_eq [RingHomSurjective τ₁₂] (f : F) (q : Submodule R₂ M₂) :
    map f (comap f q) = range f ⊓ q :=
  le_antisymm (le_inf map_le_range (map_comap_le _ _)) <| by
    rintro _ ⟨⟨x, _, rfl⟩, hx⟩; exact ⟨x, hx, rfl⟩
#align submodule.map_comap_eq Submodule.map_comap_eq

theorem _root_.Submodule.map_comap_eq_self [RingHomSurjective τ₁₂] {f : F} {q : Submodule R₂ M₂}
    (h : q ≤ range f) : map f (comap f q) = q := by rwa [Submodule.map_comap_eq, inf_eq_right]
#align submodule.map_comap_eq_self Submodule.map_comap_eq_self

@[simp]
theorem ker_zero : ker (0 : M →ₛₗ[τ₁₂] M₂) = ⊤ :=
  eq_top_iff'.2 fun x => by simp
#align linear_map.ker_zero LinearMap.ker_zero

@[simp]
theorem range_zero [RingHomSurjective τ₁₂] : range (0 : M →ₛₗ[τ₁₂] M₂) = ⊥ := by
  simpa only [range_eq_map] using Submodule.map_zero _
#align linear_map.range_zero LinearMap.range_zero

theorem ker_eq_top {f : M →ₛₗ[τ₁₂] M₂} : ker f = ⊤ ↔ f = 0 :=
  ⟨fun h => ext fun _ => mem_ker.1 <| h.symm ▸ trivial, fun h => h.symm ▸ ker_zero⟩
#align linear_map.ker_eq_top LinearMap.ker_eq_top

@[simp]
theorem _root_.AddMonoidHom.coe_toIntLinearMap_ker {M M₂ : Type*} [AddCommGroup M] [AddCommGroup M₂]
    (f : M →+ M₂) : LinearMap.ker f.toIntLinearMap = AddSubgroup.toIntSubmodule f.ker := rfl

section

variable [RingHomSurjective τ₁₂]

theorem range_le_bot_iff (f : M →ₛₗ[τ₁₂] M₂) : range f ≤ ⊥ ↔ f = 0 := by
  rw [range_le_iff_comap]; exact ker_eq_top
#align linear_map.range_le_bot_iff LinearMap.range_le_bot_iff

theorem range_eq_bot {f : M →ₛₗ[τ₁₂] M₂} : range f = ⊥ ↔ f = 0 := by
  rw [← range_le_bot_iff, le_bot_iff]
#align linear_map.range_eq_bot LinearMap.range_eq_bot

theorem range_le_ker_iff {f : M →ₛₗ[τ₁₂] M₂} {g : M₂ →ₛₗ[τ₂₃] M₃} :
    range f ≤ ker g ↔ (g.comp f : M →ₛₗ[τ₁₃] M₃) = 0 :=
  ⟨fun h => ker_eq_top.1 <| eq_top_iff'.2 fun x => h <| ⟨_, rfl⟩, fun h x hx =>
    mem_ker.2 <| Exists.elim hx fun y hy => by rw [← hy, ← comp_apply, h, zero_apply]⟩
#align linear_map.range_le_ker_iff LinearMap.range_le_ker_iff

theorem comap_le_comap_iff {f : F} (hf : range f = ⊤) {p p'} : comap f p ≤ comap f p' ↔ p ≤ p' :=
  ⟨fun H x hx => by rcases range_eq_top.1 hf x with ⟨y, hy, rfl⟩; exact H hx, comap_mono⟩
#align linear_map.comap_le_comap_iff LinearMap.comap_le_comap_iff

theorem comap_injective {f : F} (hf : range f = ⊤) : Injective (comap f) := fun _ _ h =>
  le_antisymm ((comap_le_comap_iff hf).1 (le_of_eq h)) ((comap_le_comap_iff hf).1 (ge_of_eq h))
#align linear_map.comap_injective LinearMap.comap_injective

end

theorem ker_eq_bot_of_injective {f : F} (hf : Injective f) : ker f = ⊥ := by
  have : Disjoint ⊤ (ker f) := by
    -- Porting note: `← map_zero f` should work here, but it needs to be directly applied to H.
    rw [disjoint_ker]
    intros _ _ H
    rw [← map_zero f] at H
    exact hf H
  simpa [disjoint_iff_inf_le]
#align linear_map.ker_eq_bot_of_injective LinearMap.ker_eq_bot_of_injective

/-- The increasing sequence of submodules consisting of the kernels of the iterates of a linear map.
-/
@[simps]
def iterateKer (f : M →ₗ[R] M) : ℕ →o Submodule R M where
  toFun n := ker (f ^ n)
  monotone' n m w x h := by
    obtain ⟨c, rfl⟩ := le_iff_exists_add.mp w
    rw [LinearMap.mem_ker] at h
    rw [LinearMap.mem_ker, add_comm, pow_add, LinearMap.mul_apply, h, LinearMap.map_zero]
#align linear_map.iterate_ker LinearMap.iterateKer

end AddCommMonoid

section Ring

variable [Ring R] [Ring R₂] [Ring R₃]
variable [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]
variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}
variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]
variable {F : Type*} [sc : SemilinearMapClass F τ₁₂ M M₂]
variable {f : F}

open Submodule

theorem range_toAddSubgroup [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) :
    (range f).toAddSubgroup = f.toAddMonoidHom.range :=
  rfl
#align linear_map.range_to_add_subgroup LinearMap.range_toAddSubgroup

theorem ker_toAddSubgroup (f : M →ₛₗ[τ₁₂] M₂) : (ker f).toAddSubgroup = f.toAddMonoidHom.ker :=
  rfl
#align linear_map.ker_to_add_subgroup LinearMap.ker_toAddSubgroup

theorem eqLocus_eq_ker_sub (f g : M →ₛₗ[τ₁₂] M₂) : eqLocus f g = ker (f - g) :=
  SetLike.ext fun _ => sub_eq_zero.symm
#align linear_map.eq_locus_eq_ker_sub LinearMap.eqLocus_eq_ker_sub

theorem sub_mem_ker_iff {x y} : x - y ∈ ker f ↔ f x = f y := by rw [mem_ker, map_sub, sub_eq_zero]
#align linear_map.sub_mem_ker_iff LinearMap.sub_mem_ker_iff

theorem disjoint_ker' {p : Submodule R M} :
    Disjoint p (ker f) ↔ ∀ x ∈ p, ∀ y ∈ p, f x = f y → x = y :=
  disjoint_ker.trans
    ⟨fun H x hx y hy h => eq_of_sub_eq_zero <| H _ (sub_mem hx hy) (by simp [h]),
     fun H x h₁ h₂ => H x h₁ 0 (zero_mem _) (by simpa using h₂)⟩
#align linear_map.disjoint_ker' LinearMap.disjoint_ker'

theorem injOn_of_disjoint_ker {p : Submodule R M} {s : Set M} (h : s ⊆ p)
    (hd : Disjoint p (ker f)) : Set.InjOn f s := fun _ hx _ hy =>
  disjoint_ker'.1 hd _ (h hx) _ (h hy)
#align linear_map.inj_on_of_disjoint_ker LinearMap.injOn_of_disjoint_ker

variable (F)

theorem _root_.LinearMapClass.ker_eq_bot : ker f = ⊥ ↔ Injective f := by
  simpa [disjoint_iff_inf_le] using disjoint_ker' (f := f) (p := ⊤)
#align linear_map_class.ker_eq_bot LinearMapClass.ker_eq_bot

variable {F}

theorem ker_eq_bot {f : M →ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Injective f :=
  LinearMapClass.ker_eq_bot _
#align linear_map.ker_eq_bot LinearMap.ker_eq_bot

theorem ker_le_iff [RingHomSurjective τ₁₂] {p : Submodule R M} :
    ker f ≤ p ↔ ∃ y ∈ range f, f ⁻¹' {y} ⊆ p := by
  constructor
  · intro h
    use 0
    rw [← SetLike.mem_coe, range_coe]
    exact ⟨⟨0, map_zero f⟩, h⟩
  · rintro ⟨y, h₁, h₂⟩
    rw [SetLike.le_def]
    intro z hz
    simp only [mem_ker, SetLike.mem_coe] at hz
    rw [← SetLike.mem_coe, range_coe, Set.mem_range] at h₁
    obtain ⟨x, hx⟩ := h₁
    have hx' : x ∈ p := h₂ hx
    have hxz : z + x ∈ p := by
      apply h₂
      simp [hx, hz]
    suffices z + x - x ∈ p by simpa only [this, add_sub_cancel]
    exact p.sub_mem hxz hx'
#align linear_map.ker_le_iff LinearMap.ker_le_iff

@[simp] lemma injective_domRestrict_iff {f : M →ₛₗ[τ₁₂] M₂} {S : Submodule R M} :
    Injective (f.domRestrict S) ↔ S ⊓ LinearMap.ker f = ⊥ := by
  rw [← LinearMap.ker_eq_bot]
  refine ⟨fun h ↦ le_bot_iff.1 ?_, fun h ↦ le_bot_iff.1 ?_⟩
  · intro x ⟨hx, h'x⟩
    have : ⟨x, hx⟩ ∈ LinearMap.ker (LinearMap.domRestrict f S) := by simpa using h'x
    rw [h] at this
    simpa using this
  · rintro ⟨x, hx⟩ h'x
    have : x ∈ S ⊓ LinearMap.ker f := ⟨hx, h'x⟩
    rw [h] at this
    simpa using this

@[simp] theorem injective_restrict_iff_disjoint {p : Submodule R M} {f : M →ₗ[R] M}
    (hf : ∀ x ∈ p, f x ∈ p) :
    Injective (f.restrict hf) ↔ Disjoint p (ker f) := by
  rw [← ker_eq_bot, ker_restrict hf, ker_eq_bot, injective_domRestrict_iff, disjoint_iff]

end Ring

section Semifield

variable [Semifield K] [Semifield K₂]
variable [AddCommMonoid V] [Module K V]
variable [AddCommMonoid V₂] [Module K V₂]

theorem ker_smul (f : V →ₗ[K] V₂) (a : K) (h : a ≠ 0) : ker (a • f) = ker f :=
  Submodule.comap_smul f _ a h
#align linear_map.ker_smul LinearMap.ker_smul

theorem ker_smul' (f : V →ₗ[K] V₂) (a : K) : ker (a • f) = ⨅ _ : a ≠ 0, ker f :=
  Submodule.comap_smul' f _ a
#align linear_map.ker_smul' LinearMap.ker_smul'

theorem range_smul (f : V →ₗ[K] V₂) (a : K) (h : a ≠ 0) : range (a • f) = range f := by
  simpa only [range_eq_map] using Submodule.map_smul f _ a h
#align linear_map.range_smul LinearMap.range_smul

theorem range_smul' (f : V →ₗ[K] V₂) (a : K) :
    range (a • f) = ⨆ _ : a ≠ 0, range f := by
  simpa only [range_eq_map] using Submodule.map_smul' f _ a
#align linear_map.range_smul' LinearMap.range_smul'

end Semifield

end LinearMap

namespace IsLinearMap

theorem isLinearMap_add [Semiring R] [AddCommMonoid M] [Module R M] :
    IsLinearMap R fun x : M × M => x.1 + x.2 := by
  apply IsLinearMap.mk
  · intro x y
    simp only [Prod.fst_add, Prod.snd_add]
    abel -- Porting Note: was cc
  · intro x y
    simp [smul_add]
#align is_linear_map.is_linear_map_add IsLinearMap.isLinearMap_add

theorem isLinearMap_sub {R M : Type*} [Semiring R] [AddCommGroup M] [Module R M] :
    IsLinearMap R fun x : M × M => x.1 - x.2 := by
  apply IsLinearMap.mk
  · intro x y
    -- Porting note: was `simp [add_comm, add_left_comm, sub_eq_add_neg]`
    rw [Prod.fst_add, Prod.snd_add]
    abel
  · intro x y
    simp [smul_sub]
#align is_linear_map.is_linear_map_sub IsLinearMap.isLinearMap_sub

end IsLinearMap

namespace Submodule

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]

variable [Module R M] [Module R₂ M₂]

variable (p p' : Submodule R M) (q : Submodule R₂ M₂)

variable {τ₁₂ : R →+* R₂}

variable {F : Type*} [sc : SemilinearMapClass F τ₁₂ M M₂]

open LinearMap

@[simp]
theorem map_top [RingHomSurjective τ₁₂] (f : F) : map f ⊤ = range f :=
  (range_eq_map f).symm
#align submodule.map_top Submodule.map_top

@[simp]
theorem comap_bot (f : F) : comap f ⊥ = ker f :=
  rfl
#align submodule.comap_bot Submodule.comap_bot

@[simp]
theorem ker_subtype : ker p.subtype = ⊥ :=
  ker_eq_bot_of_injective fun _ _ => Subtype.ext_val
#align submodule.ker_subtype Submodule.ker_subtype

@[simp]
theorem range_subtype : range p.subtype = p := by simpa using map_comap_subtype p ⊤
#align submodule.range_subtype Submodule.range_subtype

theorem map_subtype_le (p' : Submodule R p) : map p.subtype p' ≤ p := by
  simpa using (map_le_range : map p.subtype p' ≤ range p.subtype)
#align submodule.map_subtype_le Submodule.map_subtype_le

/-- Under the canonical linear map from a submodule `p` to the ambient space `M`, the image of the
maximal submodule of `p` is just `p`. -/
-- @[simp] -- Porting note: simp can prove this
theorem map_subtype_top : map p.subtype (⊤ : Submodule R p) = p := by simp
#align submodule.map_subtype_top Submodule.map_subtype_top

@[simp]
theorem comap_subtype_eq_top {p p' : Submodule R M} : comap p.subtype p' = ⊤ ↔ p ≤ p' :=
  eq_top_iff.trans <| map_le_iff_le_comap.symm.trans <| by rw [map_subtype_top]
#align submodule.comap_subtype_eq_top Submodule.comap_subtype_eq_top

@[simp]
theorem comap_subtype_self : comap p.subtype p = ⊤ :=
  comap_subtype_eq_top.2 le_rfl
#align submodule.comap_subtype_self Submodule.comap_subtype_self

@[simp]
theorem ker_inclusion (p p' : Submodule R M) (h : p ≤ p') : ker (inclusion h) = ⊥ := by
  rw [inclusion, ker_codRestrict, ker_subtype]
#align submodule.ker_of_le Submodule.ker_inclusion

theorem range_inclusion (p q : Submodule R M) (h : p ≤ q) :
    range (inclusion h) = comap q.subtype p := by
  rw [← map_top, inclusion, LinearMap.map_codRestrict, map_top, range_subtype]
#align submodule.range_of_le Submodule.range_inclusion

@[simp]
theorem map_subtype_range_inclusion {p p' : Submodule R M} (h : p ≤ p') :
    map p'.subtype (range <| inclusion h) = p := by simp [range_inclusion, map_comap_eq, h]
#align submodule.map_subtype_range_of_le Submodule.map_subtype_range_inclusion

theorem disjoint_iff_comap_eq_bot {p q : Submodule R M} : Disjoint p q ↔ comap p.subtype q = ⊥ := by
  rw [← (map_injective_of_injective (show Injective p.subtype from Subtype.coe_injective)).eq_iff,
    map_comap_subtype, map_bot, disjoint_iff]
#align submodule.disjoint_iff_comap_eq_bot Submodule.disjoint_iff_comap_eq_bot

/-- If `N ⊆ M` then submodules of `N` are the same as submodules of `M` contained in `N` -/
def MapSubtype.relIso : Submodule R p ≃o { p' : Submodule R M // p' ≤ p } where
  toFun p' := ⟨map p.subtype p', map_subtype_le p _⟩
  invFun q := comap p.subtype q
  left_inv p' := comap_map_eq_of_injective (by exact Subtype.val_injective) p'
  right_inv := fun ⟨q, hq⟩ => Subtype.ext_val <| by simp [map_comap_subtype p, inf_of_le_right hq]
  map_rel_iff' {p₁ p₂} := Subtype.coe_le_coe.symm.trans <| by
    dsimp
    rw [map_le_iff_le_comap,
      comap_map_eq_of_injective (show Injective p.subtype from Subtype.coe_injective) p₂]
#align submodule.map_subtype.rel_iso Submodule.MapSubtype.relIso

/-- If `p ⊆ M` is a submodule, the ordering of submodules of `p` is embedded in the ordering of
submodules of `M`. -/
def MapSubtype.orderEmbedding : Submodule R p ↪o Submodule R M :=
  (RelIso.toRelEmbedding <| MapSubtype.relIso p).trans <|
    Subtype.relEmbedding (X := Submodule R M) (fun p p' ↦ p ≤ p') _
#align submodule.map_subtype.order_embedding Submodule.MapSubtype.orderEmbedding

@[simp]
theorem map_subtype_embedding_eq (p' : Submodule R p) :
    MapSubtype.orderEmbedding p p' = map p.subtype p' :=
  rfl
#align submodule.map_subtype_embedding_eq Submodule.map_subtype_embedding_eq

end AddCommMonoid

end Submodule

namespace LinearMap

section Semiring

variable [Semiring R] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}

variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

/-- A monomorphism is injective. -/
theorem ker_eq_bot_of_cancel {f : M →ₛₗ[τ₁₂] M₂}
    (h : ∀ u v : ker f →ₗ[R] M, f.comp u = f.comp v → u = v) : ker f = ⊥ := by
  have h₁ : f.comp (0 : ker f →ₗ[R] M) = 0 := comp_zero _
  rw [← Submodule.range_subtype (ker f),
    ← h 0 f.ker.subtype (Eq.trans h₁ (comp_ker_subtype f).symm)]
  exact range_zero
#align linear_map.ker_eq_bot_of_cancel LinearMap.ker_eq_bot_of_cancel

theorem range_comp_of_range_eq_top [RingHomSurjective τ₁₂] [RingHomSurjective τ₂₃]
    [RingHomSurjective τ₁₃] {f : M →ₛₗ[τ₁₂] M₂} (g : M₂ →ₛₗ[τ₂₃] M₃) (hf : range f = ⊤) :
    range (g.comp f : M →ₛₗ[τ₁₃] M₃) = range g := by rw [range_comp, hf, Submodule.map_top]
#align linear_map.range_comp_of_range_eq_top LinearMap.range_comp_of_range_eq_top

theorem ker_comp_of_ker_eq_bot (f : M →ₛₗ[τ₁₂] M₂) {g : M₂ →ₛₗ[τ₂₃] M₃} (hg : ker g = ⊥) :
    ker (g.comp f : M →ₛₗ[τ₁₃] M₃) = ker f := by rw [ker_comp, hg, Submodule.comap_bot]
#align linear_map.ker_comp_of_ker_eq_bot LinearMap.ker_comp_of_ker_eq_bot

section Image

/-- If `O` is a submodule of `M`, and `Φ : O →ₗ M'` is a linear map,
then `(ϕ : O →ₗ M').submoduleImage N` is `ϕ(N)` as a submodule of `M'` -/
def submoduleImage {M' : Type*} [AddCommMonoid M'] [Module R M'] {O : Submodule R M}
    (ϕ : O →ₗ[R] M') (N : Submodule R M) : Submodule R M' :=
  (N.comap O.subtype).map ϕ
#align linear_map.submodule_image LinearMap.submoduleImage

@[simp]
theorem mem_submoduleImage {M' : Type*} [AddCommMonoid M'] [Module R M'] {O : Submodule R M}
    {ϕ : O →ₗ[R] M'} {N : Submodule R M} {x : M'} :
    x ∈ ϕ.submoduleImage N ↔ ∃ (y : _) (yO : y ∈ O), y ∈ N ∧ ϕ ⟨y, yO⟩ = x := by
  refine' Submodule.mem_map.trans ⟨_, _⟩ <;> simp_rw [Submodule.mem_comap]
  · rintro ⟨⟨y, yO⟩, yN : y ∈ N, h⟩
    exact ⟨y, yO, yN, h⟩
  · rintro ⟨y, yO, yN, h⟩
    exact ⟨⟨y, yO⟩, yN, h⟩
#align linear_map.mem_submodule_image LinearMap.mem_submoduleImage

theorem mem_submoduleImage_of_le {M' : Type*} [AddCommMonoid M'] [Module R M'] {O : Submodule R M}
    {ϕ : O →ₗ[R] M'} {N : Submodule R M} (hNO : N ≤ O) {x : M'} :
    x ∈ ϕ.submoduleImage N ↔ ∃ (y : _) (yN : y ∈ N), ϕ ⟨y, hNO yN⟩ = x := by
  refine' mem_submoduleImage.trans ⟨_, _⟩
  · rintro ⟨y, yO, yN, h⟩
    exact ⟨y, yN, h⟩
  · rintro ⟨y, yN, h⟩
    exact ⟨y, hNO yN, yN, h⟩
#align linear_map.mem_submodule_image_of_le LinearMap.mem_submoduleImage_of_le

theorem submoduleImage_apply_of_le {M' : Type*} [AddCommGroup M'] [Module R M']
    {O : Submodule R M} (ϕ : O →ₗ[R] M') (N : Submodule R M) (hNO : N ≤ O) :
    ϕ.submoduleImage N = range (ϕ.comp (Submodule.inclusion hNO)) := by
  rw [submoduleImage, range_comp, Submodule.range_inclusion]
#align linear_map.submodule_image_apply_of_le LinearMap.submoduleImage_apply_of_le

end Image

end Semiring

end LinearMap

@[simp]
theorem LinearMap.range_rangeRestrict [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [Module R M]
    [Module R M₂] (f : M →ₗ[R] M₂) : range f.rangeRestrict = ⊤ := by simp [f.range_codRestrict _]
#align linear_map.range_range_restrict LinearMap.range_rangeRestrict

@[simp]
theorem LinearMap.ker_rangeRestrict [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [Module R M]
    [Module R M₂] (f : M →ₗ[R] M₂) : ker f.rangeRestrict = ker f :=
  LinearMap.ker_codRestrict _ _ _
#align linear_map.ker_range_restrict LinearMap.ker_rangeRestrict

/-! ### Linear equivalences -/


namespace LinearEquiv

section AddCommMonoid

section Subsingleton

variable [Semiring R] [Semiring R₂]

variable [AddCommMonoid M] [AddCommMonoid M₂]

variable [Module R M] [Module R₂ M₂]

variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}

variable [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

section Module

variable [Subsingleton M] [Subsingleton M₂]

/-- Between two zero modules, the zero map is an equivalence. -/
instance : Zero (M ≃ₛₗ[σ₁₂] M₂) :=
  ⟨{ (0 : M →ₛₗ[σ₁₂] M₂) with
      toFun := 0
      invFun := 0
      right_inv := Subsingleton.elim _
      left_inv := Subsingleton.elim _ }⟩

-- Even though these are implied by `Subsingleton.elim` via the `Unique` instance below, they're
-- nice to have as `rfl`-lemmas for `dsimp`.
@[simp]
theorem zero_symm : (0 : M ≃ₛₗ[σ₁₂] M₂).symm = 0 :=
  rfl
#align linear_equiv.zero_symm LinearEquiv.zero_symm

@[simp]
theorem coe_zero : ⇑(0 : M ≃ₛₗ[σ₁₂] M₂) = 0 :=
  rfl
#align linear_equiv.coe_zero LinearEquiv.coe_zero

theorem zero_apply (x : M) : (0 : M ≃ₛₗ[σ₁₂] M₂) x = 0 :=
  rfl
#align linear_equiv.zero_apply LinearEquiv.zero_apply

/-- Between two zero modules, the zero map is the only equivalence. -/
instance : Unique (M ≃ₛₗ[σ₁₂] M₂) where
  uniq _ := toLinearMap_injective (Subsingleton.elim _ _)
  default := 0


end Module

instance uniqueOfSubsingleton [Subsingleton R] [Subsingleton R₂] : Unique (M ≃ₛₗ[σ₁₂] M₂) := by
  haveI := Module.subsingleton R M
  haveI := Module.subsingleton R₂ M₂
  infer_instance
#align linear_equiv.unique_of_subsingleton LinearEquiv.uniqueOfSubsingleton

end Subsingleton

section

variable [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring R₄]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]

variable {module_M : Module R M} {module_M₂ : Module R₂ M₂}

variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}

variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}

variable (e e' : M ≃ₛₗ[σ₁₂] M₂)

#align linear_equiv.map_sum map_sumₓ

theorem map_eq_comap {p : Submodule R M} :
    (p.map (e : M →ₛₗ[σ₁₂] M₂) : Submodule R₂ M₂) = p.comap (e.symm : M₂ →ₛₗ[σ₂₁] M) :=
  SetLike.coe_injective <| by simp [e.image_eq_preimage]
#align linear_equiv.map_eq_comap LinearEquiv.map_eq_comap

/-- A linear equivalence of two modules restricts to a linear equivalence from any submodule
`p` of the domain onto the image of that submodule.

This is the linear version of `AddEquiv.submonoidMap` and `AddEquiv.subgroupMap`.

This is `LinearEquiv.ofSubmodule'` but with `map` on the right instead of `comap` on the left. -/
def submoduleMap (p : Submodule R M) : p ≃ₛₗ[σ₁₂] ↥(p.map (e : M →ₛₗ[σ₁₂] M₂) : Submodule R₂ M₂) :=
  { ((e : M →ₛₗ[σ₁₂] M₂).domRestrict p).codRestrict (p.map (e : M →ₛₗ[σ₁₂] M₂)) fun x =>
      ⟨x, by
        simp only [LinearMap.domRestrict_apply, eq_self_iff_true, and_true_iff, SetLike.coe_mem,
          SetLike.mem_coe]⟩ with
    invFun := fun y =>
      ⟨(e.symm : M₂ →ₛₗ[σ₂₁] M) y, by
        rcases y with ⟨y', hy⟩
        rw [Submodule.mem_map] at hy
        rcases hy with ⟨x, hx, hxy⟩
        subst hxy
        simp only [symm_apply_apply, Submodule.coe_mk, coe_coe, hx]⟩
    left_inv := fun x => by
      simp only [LinearMap.domRestrict_apply, LinearMap.codRestrict_apply, LinearMap.toFun_eq_coe,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, SetLike.eta]
    right_inv := fun y => by
      apply SetCoe.ext
      simp only [LinearMap.domRestrict_apply, LinearMap.codRestrict_apply, LinearMap.toFun_eq_coe,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] }
#align linear_equiv.submodule_map LinearEquiv.submoduleMap


@[simp]
theorem submoduleMap_apply (p : Submodule R M) (x : p) : ↑(e.submoduleMap p x) = e x :=
  rfl
#align linear_equiv.submodule_map_apply LinearEquiv.submoduleMap_apply

@[simp]
theorem submoduleMap_symm_apply (p : Submodule R M)
    (x : (p.map (e : M →ₛₗ[σ₁₂] M₂) : Submodule R₂ M₂)) : ↑((e.submoduleMap p).symm x) = e.symm x :=
  rfl
#align linear_equiv.submodule_map_symm_apply LinearEquiv.submoduleMap_symm_apply


end

section Uncurry

variable [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring R₄]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]

variable (V V₂ R)

/-- Linear equivalence between a curried and uncurried function.
  Differs from `TensorProduct.curry`. -/
protected def curry : (V × V₂ → R) ≃ₗ[R] V → V₂ → R :=
  { Equiv.curry _ _ _ with
    map_add' := fun _ _ => by
      ext
      rfl
    map_smul' := fun _ _ => by
      ext
      rfl }
#align linear_equiv.curry LinearEquiv.curry

@[simp]
theorem coe_curry : ⇑(LinearEquiv.curry R V V₂) = curry :=
  rfl
#align linear_equiv.coe_curry LinearEquiv.coe_curry

@[simp]
theorem coe_curry_symm : ⇑(LinearEquiv.curry R V V₂).symm = uncurry :=
  rfl
#align linear_equiv.coe_curry_symm LinearEquiv.coe_curry_symm

end Uncurry

section

variable [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring R₄]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]

variable {module_M : Module R M} {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}

variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}

variable {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable {σ₃₂ : R₃ →+* R₂}

variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}

variable {re₂₃ : RingHomInvPair σ₂₃ σ₃₂} {re₃₂ : RingHomInvPair σ₃₂ σ₂₃}

variable (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₁] M) (e : M ≃ₛₗ[σ₁₂] M₂) (h : M₂ →ₛₗ[σ₂₃] M₃)

variable (e'' : M₂ ≃ₛₗ[σ₂₃] M₃)

variable (p q : Submodule R M)

/-- Linear equivalence between two equal submodules. -/
def ofEq (h : p = q) : p ≃ₗ[R] q :=
  { Equiv.Set.ofEq (congr_arg _ h) with
    map_smul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }
#align linear_equiv.of_eq LinearEquiv.ofEq

variable {p q}

@[simp]
theorem coe_ofEq_apply (h : p = q) (x : p) : (ofEq p q h x : M) = x :=
  rfl
#align linear_equiv.coe_of_eq_apply LinearEquiv.coe_ofEq_apply

@[simp]
theorem ofEq_symm (h : p = q) : (ofEq p q h).symm = ofEq q p h.symm :=
  rfl
#align linear_equiv.of_eq_symm LinearEquiv.ofEq_symm

@[simp]
theorem ofEq_rfl : ofEq p p rfl = LinearEquiv.refl R p := by ext; rfl
#align linear_equiv.of_eq_rfl LinearEquiv.ofEq_rfl

/-- A linear equivalence which maps a submodule of one module onto another, restricts to a linear
equivalence of the two submodules. -/
def ofSubmodules (p : Submodule R M) (q : Submodule R₂ M₂) (h : p.map (e : M →ₛₗ[σ₁₂] M₂) = q) :
    p ≃ₛₗ[σ₁₂] q :=
  (e.submoduleMap p).trans (LinearEquiv.ofEq _ _ h)
#align linear_equiv.of_submodules LinearEquiv.ofSubmodules

@[simp]
theorem ofSubmodules_apply {p : Submodule R M} {q : Submodule R₂ M₂} (h : p.map ↑e = q) (x : p) :
    ↑(e.ofSubmodules p q h x) = e x :=
  rfl
#align linear_equiv.of_submodules_apply LinearEquiv.ofSubmodules_apply

@[simp]
theorem ofSubmodules_symm_apply {p : Submodule R M} {q : Submodule R₂ M₂} (h : p.map ↑e = q)
    (x : q) : ↑((e.ofSubmodules p q h).symm x) = e.symm x :=
  rfl
#align linear_equiv.of_submodules_symm_apply LinearEquiv.ofSubmodules_symm_apply

/-- A linear equivalence of two modules restricts to a linear equivalence from the preimage of any
submodule to that submodule.

This is `LinearEquiv.ofSubmodule` but with `comap` on the left instead of `map` on the right. -/
def ofSubmodule' [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂) (U : Submodule R₂ M₂) :
    U.comap (f : M →ₛₗ[σ₁₂] M₂) ≃ₛₗ[σ₁₂] U :=
  (f.symm.ofSubmodules _ _ f.symm.map_eq_comap).symm
#align linear_equiv.of_submodule' LinearEquiv.ofSubmodule'

theorem ofSubmodule'_toLinearMap [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂)
    (U : Submodule R₂ M₂) :
    (f.ofSubmodule' U).toLinearMap = (f.toLinearMap.domRestrict _).codRestrict _ Subtype.prop := by
  ext
  rfl
#align linear_equiv.of_submodule'_to_linear_map LinearEquiv.ofSubmodule'_toLinearMap

@[simp]
theorem ofSubmodule'_apply [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂) (U : Submodule R₂ M₂)
    (x : U.comap (f : M →ₛₗ[σ₁₂] M₂)) : (f.ofSubmodule' U x : M₂) = f (x : M) :=
  rfl
#align linear_equiv.of_submodule'_apply LinearEquiv.ofSubmodule'_apply

@[simp]
theorem ofSubmodule'_symm_apply [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂)
    (U : Submodule R₂ M₂) (x : U) : ((f.ofSubmodule' U).symm x : M) = f.symm (x : M₂) :=
  rfl
#align linear_equiv.of_submodule'_symm_apply LinearEquiv.ofSubmodule'_symm_apply

variable (p)

/-- The top submodule of `M` is linearly equivalent to `M`. -/
def ofTop (h : p = ⊤) : p ≃ₗ[R] M :=
  { p.subtype with
    invFun := fun x => ⟨x, h.symm ▸ trivial⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
#align linear_equiv.of_top LinearEquiv.ofTop

@[simp]
theorem ofTop_apply {h} (x : p) : ofTop p h x = x :=
  rfl
#align linear_equiv.of_top_apply LinearEquiv.ofTop_apply

@[simp]
theorem coe_ofTop_symm_apply {h} (x : M) : ((ofTop p h).symm x : M) = x :=
  rfl
#align linear_equiv.coe_of_top_symm_apply LinearEquiv.coe_ofTop_symm_apply

theorem ofTop_symm_apply {h} (x : M) : (ofTop p h).symm x = ⟨x, h.symm ▸ trivial⟩ :=
  rfl
#align linear_equiv.of_top_symm_apply LinearEquiv.ofTop_symm_apply

/-- If a linear map has an inverse, it is a linear equivalence. -/
def ofLinear (h₁ : f.comp g = LinearMap.id) (h₂ : g.comp f = LinearMap.id) : M ≃ₛₗ[σ₁₂] M₂ :=
  { f with
    invFun := g
    left_inv := LinearMap.ext_iff.1 h₂
    right_inv := LinearMap.ext_iff.1 h₁ }
#align linear_equiv.of_linear LinearEquiv.ofLinear

@[simp]
theorem ofLinear_apply {h₁ h₂} (x : M) : (ofLinear f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂) x = f x :=
  rfl
#align linear_equiv.of_linear_apply LinearEquiv.ofLinear_apply

@[simp]
theorem ofLinear_symm_apply {h₁ h₂} (x : M₂) : (ofLinear f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂).symm x = g x :=
  rfl
#align linear_equiv.of_linear_symm_apply LinearEquiv.ofLinear_symm_apply

@[simp]
protected theorem range : LinearMap.range (e : M →ₛₗ[σ₁₂] M₂) = ⊤ :=
  LinearMap.range_eq_top.2 e.toEquiv.surjective
#align linear_equiv.range LinearEquiv.range

@[simp]
protected theorem _root_.LinearEquivClass.range [Module R M] [Module R₂ M₂] {F : Type*}
    [SemilinearEquivClass F σ₁₂ M M₂] (e : F) : LinearMap.range e = ⊤ :=
  LinearMap.range_eq_top.2 (EquivLike.surjective e)
#align linear_equiv_class.range LinearEquivClass.range

theorem eq_bot_of_equiv [Module R₂ M₂] (e : p ≃ₛₗ[σ₁₂] (⊥ : Submodule R₂ M₂)) : p = ⊥ := by
  refine' bot_unique (SetLike.le_def.2 fun b hb => (Submodule.mem_bot R).2 _)
  rw [← p.mk_eq_zero hb, ← e.map_eq_zero_iff]
  apply Submodule.eq_zero_of_bot_submodule
#align linear_equiv.eq_bot_of_equiv LinearEquiv.eq_bot_of_equiv

@[simp]
protected theorem ker : LinearMap.ker (e : M →ₛₗ[σ₁₂] M₂) = ⊥ :=
  LinearMap.ker_eq_bot_of_injective e.toEquiv.injective
#align linear_equiv.ker LinearEquiv.ker

-- Porting note: `RingHomSurjective σ₁₂` is an unused argument.
@[simp]
theorem range_comp [RingHomSurjective σ₂₃] [RingHomSurjective σ₁₃] :
    LinearMap.range (h.comp (e : M →ₛₗ[σ₁₂] M₂) : M →ₛₗ[σ₁₃] M₃) = LinearMap.range h :=
  LinearMap.range_comp_of_range_eq_top _ e.range
#align linear_equiv.range_comp LinearEquiv.range_comp

@[simp]
theorem ker_comp (l : M →ₛₗ[σ₁₂] M₂) :
    LinearMap.ker (((e'' : M₂ →ₛₗ[σ₂₃] M₃).comp l : M →ₛₗ[σ₁₃] M₃) : M →ₛₗ[σ₁₃] M₃) =
    LinearMap.ker l :=
  LinearMap.ker_comp_of_ker_eq_bot _ e''.ker
#align linear_equiv.ker_comp LinearEquiv.ker_comp

variable {f g}

/-- A linear map `f : M →ₗ[R] M₂` with a left-inverse `g : M₂ →ₗ[R] M` defines a linear
equivalence between `M` and `f.range`.

This is a computable alternative to `LinearEquiv.ofInjective`, and a bidirectional version of
`LinearMap.rangeRestrict`. -/
def ofLeftInverse [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {g : M₂ → M}
    (h : Function.LeftInverse g f) : M ≃ₛₗ[σ₁₂] (LinearMap.range f) :=
  { LinearMap.rangeRestrict f with
    toFun := LinearMap.rangeRestrict f
    invFun := g ∘ (LinearMap.range f).subtype
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := LinearMap.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }
#align linear_equiv.of_left_inverse LinearEquiv.ofLeftInverse

@[simp]
theorem ofLeftInverse_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    (h : Function.LeftInverse g f) (x : M) : ↑(ofLeftInverse h x) = f x :=
  rfl
#align linear_equiv.of_left_inverse_apply LinearEquiv.ofLeftInverse_apply

@[simp]
theorem ofLeftInverse_symm_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    (h : Function.LeftInverse g f) (x : LinearMap.range f) : (ofLeftInverse h).symm x = g x :=
  rfl
#align linear_equiv.of_left_inverse_symm_apply LinearEquiv.ofLeftInverse_symm_apply

variable (f)

/-- An `Injective` linear map `f : M →ₗ[R] M₂` defines a linear equivalence
between `M` and `f.range`. See also `LinearMap.ofLeftInverse`. -/
noncomputable def ofInjective [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (h : Injective f) :
    M ≃ₛₗ[σ₁₂] LinearMap.range f :=
  ofLeftInverse <| Classical.choose_spec h.hasLeftInverse
#align linear_equiv.of_injective LinearEquiv.ofInjective

@[simp]
theorem ofInjective_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h : Injective f}
    (x : M) : ↑(ofInjective f h x) = f x :=
  rfl
#align linear_equiv.of_injective_apply LinearEquiv.ofInjective_apply

/-- A bijective linear map is a linear equivalence. -/
noncomputable def ofBijective [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (hf : Bijective f) :
    M ≃ₛₗ[σ₁₂] M₂ :=
  (ofInjective f hf.injective).trans (ofTop _ <| LinearMap.range_eq_top.2 hf.surjective)
#align linear_equiv.of_bijective LinearEquiv.ofBijective

@[simp]
theorem ofBijective_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {hf} (x : M) :
    ofBijective f hf x = f x :=
  rfl
#align linear_equiv.of_bijective_apply LinearEquiv.ofBijective_apply

@[simp]
theorem ofBijective_symm_apply_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h} (x : M) :
    (ofBijective f h).symm (f x) = x := by
  simp [LinearEquiv.symm_apply_eq]

end

end AddCommMonoid

section AddCommGroup

variable [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring R₄]

variable [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup M₄]

variable {module_M : Module R M} {module_M₂ : Module R₂ M₂}

variable {module_M₃ : Module R₃ M₃} {module_M₄ : Module R₄ M₄}

variable {σ₁₂ : R →+* R₂} {σ₃₄ : R₃ →+* R₄}

variable {σ₂₁ : R₂ →+* R} {σ₄₃ : R₄ →+* R₃}

variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}

variable {re₃₄ : RingHomInvPair σ₃₄ σ₄₃} {re₄₃ : RingHomInvPair σ₄₃ σ₃₄}

variable (e e₁ : M ≃ₛₗ[σ₁₂] M₂) (e₂ : M₃ ≃ₛₗ[σ₃₄] M₄)

-- @[simp] -- Porting note: simp can prove this
theorem map_neg (a : M) : e (-a) = -e a :=
  e.toLinearMap.map_neg a
#align linear_equiv.map_neg LinearEquiv.map_neg

-- @[simp] -- Porting note: simp can prove this
theorem map_sub (a b : M) : e (a - b) = e a - e b :=
  e.toLinearMap.map_sub a b
#align linear_equiv.map_sub LinearEquiv.map_sub

end AddCommGroup

section Neg

variable (R) [Semiring R] [AddCommGroup M] [Module R M]

/-- `x ↦ -x` as a `LinearEquiv` -/
def neg : M ≃ₗ[R] M :=
  { Equiv.neg M, (-LinearMap.id : M →ₗ[R] M) with }
#align linear_equiv.neg LinearEquiv.neg

variable {R}

@[simp]
theorem coe_neg : ⇑(neg R : M ≃ₗ[R] M) = -id :=
  rfl
#align linear_equiv.coe_neg LinearEquiv.coe_neg

theorem neg_apply (x : M) : neg R x = -x := by simp
#align linear_equiv.neg_apply LinearEquiv.neg_apply

@[simp]
theorem symm_neg : (neg R : M ≃ₗ[R] M).symm = neg R :=
  rfl
#align linear_equiv.symm_neg LinearEquiv.symm_neg

end Neg

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₂] [Module R M₃]

open LinearMap

/-- Multiplying by a unit `a` of the ring `R` is a linear equivalence. -/
def smulOfUnit (a : Rˣ) : M ≃ₗ[R] M :=
  DistribMulAction.toLinearEquiv R M a
#align linear_equiv.smul_of_unit LinearEquiv.smulOfUnit

/-- A linear isomorphism between the domains and codomains of two spaces of linear maps gives a
linear isomorphism between the two function spaces. -/
def arrowCongr {R M₁ M₂ M₂₁ M₂₂ : Sort _} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
    [AddCommMonoid M₂₁] [AddCommMonoid M₂₂] [Module R M₁] [Module R M₂] [Module R M₂₁]
    [Module R M₂₂] (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : M₂₁ ≃ₗ[R] M₂₂) : (M₁ →ₗ[R] M₂₁) ≃ₗ[R] M₂ →ₗ[R] M₂₂
    where
  toFun := fun f : M₁ →ₗ[R] M₂₁ => (e₂ : M₂₁ →ₗ[R] M₂₂).comp <| f.comp (e₁.symm : M₂ →ₗ[R] M₁)
  invFun f := (e₂.symm : M₂₂ →ₗ[R] M₂₁).comp <| f.comp (e₁ : M₁ →ₗ[R] M₂)
  left_inv f := by
    ext x
    simp only [symm_apply_apply, Function.comp_apply, coe_comp, coe_coe]
  right_inv f := by
    ext x
    simp only [Function.comp_apply, apply_symm_apply, coe_comp, coe_coe]
  map_add' f g := by
    ext x
    simp only [map_add, add_apply, Function.comp_apply, coe_comp, coe_coe]
  map_smul' c f := by
    ext x
    simp only [smul_apply, Function.comp_apply, coe_comp, map_smulₛₗ e₂, coe_coe]
#align linear_equiv.arrow_congr LinearEquiv.arrowCongr

@[simp]
theorem arrowCongr_apply {R M₁ M₂ M₂₁ M₂₂ : Sort _} [CommSemiring R] [AddCommMonoid M₁]
    [AddCommMonoid M₂] [AddCommMonoid M₂₁] [AddCommMonoid M₂₂] [Module R M₁] [Module R M₂]
    [Module R M₂₁] [Module R M₂₂] (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : M₂₁ ≃ₗ[R] M₂₂) (f : M₁ →ₗ[R] M₂₁)
    (x : M₂) : arrowCongr e₁ e₂ f x = e₂ (f (e₁.symm x)) :=
  rfl
#align linear_equiv.arrow_congr_apply LinearEquiv.arrowCongr_apply

@[simp]
theorem arrowCongr_symm_apply {R M₁ M₂ M₂₁ M₂₂ : Sort _} [CommSemiring R] [AddCommMonoid M₁]
    [AddCommMonoid M₂] [AddCommMonoid M₂₁] [AddCommMonoid M₂₂] [Module R M₁] [Module R M₂]
    [Module R M₂₁] [Module R M₂₂] (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : M₂₁ ≃ₗ[R] M₂₂) (f : M₂ →ₗ[R] M₂₂)
    (x : M₁) : (arrowCongr e₁ e₂).symm f x = e₂.symm (f (e₁ x)) :=
  rfl
#align linear_equiv.arrow_congr_symm_apply LinearEquiv.arrowCongr_symm_apply

theorem arrowCongr_comp {N N₂ N₃ : Sort _} [AddCommMonoid N] [AddCommMonoid N₂] [AddCommMonoid N₃]
    [Module R N] [Module R N₂] [Module R N₃] (e₁ : M ≃ₗ[R] N) (e₂ : M₂ ≃ₗ[R] N₂) (e₃ : M₃ ≃ₗ[R] N₃)
    (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) :
    arrowCongr e₁ e₃ (g.comp f) = (arrowCongr e₂ e₃ g).comp (arrowCongr e₁ e₂ f) := by
  ext
  simp only [symm_apply_apply, arrowCongr_apply, LinearMap.comp_apply]
#align linear_equiv.arrow_congr_comp LinearEquiv.arrowCongr_comp

theorem arrowCongr_trans {M₁ M₂ M₃ N₁ N₂ N₃ : Sort _} [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid M₃] [Module R M₃] [AddCommMonoid N₁]
    [Module R N₁] [AddCommMonoid N₂] [Module R N₂] [AddCommMonoid N₃] [Module R N₃]
    (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : N₁ ≃ₗ[R] N₂) (e₃ : M₂ ≃ₗ[R] M₃) (e₄ : N₂ ≃ₗ[R] N₃) :
    (arrowCongr e₁ e₂).trans (arrowCongr e₃ e₄) = arrowCongr (e₁.trans e₃) (e₂.trans e₄) :=
  rfl
#align linear_equiv.arrow_congr_trans LinearEquiv.arrowCongr_trans

/-- If `M₂` and `M₃` are linearly isomorphic then the two spaces of linear maps from `M` into `M₂`
and `M` into `M₃` are linearly isomorphic. -/
def congrRight (f : M₂ ≃ₗ[R] M₃) : (M →ₗ[R] M₂) ≃ₗ[R] M →ₗ[R] M₃ :=
  arrowCongr (LinearEquiv.refl R M) f
#align linear_equiv.congr_right LinearEquiv.congrRight

/-- If `M` and `M₂` are linearly isomorphic then the two spaces of linear maps from `M` and `M₂` to
themselves are linearly isomorphic. -/
def conj (e : M ≃ₗ[R] M₂) : Module.End R M ≃ₗ[R] Module.End R M₂ :=
  arrowCongr e e
#align linear_equiv.conj LinearEquiv.conj

theorem conj_apply (e : M ≃ₗ[R] M₂) (f : Module.End R M) :
    e.conj f = ((↑e : M →ₗ[R] M₂).comp f).comp (e.symm : M₂ →ₗ[R] M) :=
  rfl
#align linear_equiv.conj_apply LinearEquiv.conj_apply

theorem conj_apply_apply (e : M ≃ₗ[R] M₂) (f : Module.End R M) (x : M₂) :
    e.conj f x = e (f (e.symm x)) :=
  rfl
#align linear_equiv.conj_apply_apply LinearEquiv.conj_apply_apply

theorem symm_conj_apply (e : M ≃ₗ[R] M₂) (f : Module.End R M₂) :
    e.symm.conj f = ((↑e.symm : M₂ →ₗ[R] M).comp f).comp (e : M →ₗ[R] M₂) :=
  rfl
#align linear_equiv.symm_conj_apply LinearEquiv.symm_conj_apply

theorem conj_comp (e : M ≃ₗ[R] M₂) (f g : Module.End R M) :
    e.conj (g.comp f) = (e.conj g).comp (e.conj f) :=
  arrowCongr_comp e e e f g
#align linear_equiv.conj_comp LinearEquiv.conj_comp

theorem conj_trans (e₁ : M ≃ₗ[R] M₂) (e₂ : M₂ ≃ₗ[R] M₃) :
    e₁.conj.trans e₂.conj = (e₁.trans e₂).conj := by
  ext f x
  rfl
#align linear_equiv.conj_trans LinearEquiv.conj_trans

@[simp]
theorem conj_id (e : M ≃ₗ[R] M₂) : e.conj LinearMap.id = LinearMap.id := by
  ext
  simp [conj_apply]
#align linear_equiv.conj_id LinearEquiv.conj_id

variable (M) in
/-- An `R`-linear isomorphism between two `R`-modules `M₂` and `M₃` induces an `S`-linear
isomorphism between `M₂ →ₗ[R] M` and `M₃ →ₗ[R] M`, if `M` is both an `R`-module and an
`S`-module and their actions commute. -/
def congrLeft {R} (S) [Semiring R] [Semiring S] [Module R M₂] [Module R M₃] [Module R M]
    [Module S M] [SMulCommClass R S M] (e : M₂ ≃ₗ[R] M₃) : (M₂ →ₗ[R] M) ≃ₗ[S] (M₃ →ₗ[R] M) where
  toFun f := f.comp e.symm.toLinearMap
  invFun f := f.comp e.toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by dsimp only; apply FunLike.ext; exact (congr_arg f <| e.left_inv ·)
  right_inv f := by dsimp only; apply FunLike.ext; exact (congr_arg f <| e.right_inv ·)

end CommSemiring

section Field

variable [Field K] [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃]

variable [Module K M] [Module K M₂] [Module K M₃]

variable (K) (M)

open LinearMap

/-- Multiplying by a nonzero element `a` of the field `K` is a linear equivalence. -/
@[simps!]
def smulOfNeZero (a : K) (ha : a ≠ 0) : M ≃ₗ[K] M :=
  smulOfUnit <| Units.mk0 a ha
#align linear_equiv.smul_of_ne_zero LinearEquiv.smulOfNeZero

end Field

end LinearEquiv

namespace Submodule

section Module

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- Given `p` a submodule of the module `M` and `q` a submodule of `p`, `p.equivSubtypeMap q`
is the natural `LinearEquiv` between `q` and `q.map p.subtype`. -/
def equivSubtypeMap (p : Submodule R M) (q : Submodule R p) : q ≃ₗ[R] q.map p.subtype :=
  { (p.subtype.domRestrict q).codRestrict _ (by rintro ⟨x, hx⟩; exact ⟨x, hx, rfl⟩) with
    invFun := by
      rintro ⟨x, hx⟩
      refine' ⟨⟨x, _⟩, _⟩ <;> rcases hx with ⟨⟨_, h⟩, _, rfl⟩ <;> assumption
    left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
    right_inv := fun ⟨x, ⟨_, h⟩, _, rfl⟩ => by ext; rfl }
#align submodule.equiv_subtype_map Submodule.equivSubtypeMap

@[simp]
theorem equivSubtypeMap_apply {p : Submodule R M} {q : Submodule R p} (x : q) :
    (p.equivSubtypeMap q x : M) = p.subtype.domRestrict q x :=
  rfl
#align submodule.equiv_subtype_map_apply Submodule.equivSubtypeMap_apply

@[simp]
theorem equivSubtypeMap_symm_apply {p : Submodule R M} {q : Submodule R p} (x : q.map p.subtype) :
    ((p.equivSubtypeMap q).symm x : M) = x := by
  cases x
  rfl
#align submodule.equiv_subtype_map_symm_apply Submodule.equivSubtypeMap_symm_apply

end Module

end Submodule


namespace Equiv

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂] [Module R M₂]

/-- An equivalence whose underlying function is linear is a linear equivalence. -/
def toLinearEquiv (e : M ≃ M₂) (h : IsLinearMap R (e : M → M₂)) : M ≃ₗ[R] M₂ :=
  { e, h.mk' e with }
#align equiv.to_linear_equiv Equiv.toLinearEquiv

end Equiv

section FunLeft

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]

variable {m n p : Type*}

namespace LinearMap

/-- Given an `R`-module `M` and a function `m → n` between arbitrary types,
construct a linear map `(n → M) →ₗ[R] (m → M)` -/
def funLeft (f : m → n) : (n → M) →ₗ[R] m → M where
  toFun := (· ∘ f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align linear_map.fun_left LinearMap.funLeft

@[simp]
theorem funLeft_apply (f : m → n) (g : n → M) (i : m) : funLeft R M f g i = g (f i) :=
  rfl
#align linear_map.fun_left_apply LinearMap.funLeft_apply

@[simp]
theorem funLeft_id (g : n → M) : funLeft R M _root_.id g = g :=
  rfl
#align linear_map.fun_left_id LinearMap.funLeft_id

theorem funLeft_comp (f₁ : n → p) (f₂ : m → n) :
    funLeft R M (f₁ ∘ f₂) = (funLeft R M f₂).comp (funLeft R M f₁) :=
  rfl
#align linear_map.fun_left_comp LinearMap.funLeft_comp

theorem funLeft_surjective_of_injective (f : m → n) (hf : Injective f) :
    Surjective (funLeft R M f) := by
  classical
    intro g
    refine' ⟨fun x => if h : ∃ y, f y = x then g h.choose else 0, _⟩
    · ext
      dsimp only [funLeft_apply]
      split_ifs with w
      · congr
        exact hf w.choose_spec
      · simp only [not_true, exists_apply_eq_apply] at w
#align linear_map.fun_left_surjective_of_injective LinearMap.funLeft_surjective_of_injective

theorem funLeft_injective_of_surjective (f : m → n) (hf : Surjective f) :
    Injective (funLeft R M f) := by
  obtain ⟨g, hg⟩ := hf.hasRightInverse
  suffices LeftInverse (funLeft R M g) (funLeft R M f) by exact this.injective
  intro x
  rw [← LinearMap.comp_apply, ← funLeft_comp, hg.id, funLeft_id]
#align linear_map.fun_left_injective_of_surjective LinearMap.funLeft_injective_of_surjective

end LinearMap

namespace LinearEquiv

open LinearMap

/-- Given an `R`-module `M` and an equivalence `m ≃ n` between arbitrary types,
construct a linear equivalence `(n → M) ≃ₗ[R] (m → M)` -/
def funCongrLeft (e : m ≃ n) : (n → M) ≃ₗ[R] m → M :=
  LinearEquiv.ofLinear (funLeft R M e) (funLeft R M e.symm)
    (LinearMap.ext fun x =>
      funext fun i => by rw [id_apply, ← funLeft_comp, Equiv.symm_comp_self, LinearMap.funLeft_id])
    (LinearMap.ext fun x =>
      funext fun i => by rw [id_apply, ← funLeft_comp, Equiv.self_comp_symm, LinearMap.funLeft_id])
#align linear_equiv.fun_congr_left LinearEquiv.funCongrLeft

@[simp]
theorem funCongrLeft_apply (e : m ≃ n) (x : n → M) : funCongrLeft R M e x = funLeft R M e x :=
  rfl
#align linear_equiv.fun_congr_left_apply LinearEquiv.funCongrLeft_apply

@[simp]
theorem funCongrLeft_id : funCongrLeft R M (Equiv.refl n) = LinearEquiv.refl R (n → M) :=
  rfl
#align linear_equiv.fun_congr_left_id LinearEquiv.funCongrLeft_id

@[simp]
theorem funCongrLeft_comp (e₁ : m ≃ n) (e₂ : n ≃ p) :
    funCongrLeft R M (Equiv.trans e₁ e₂) =
      LinearEquiv.trans (funCongrLeft R M e₂) (funCongrLeft R M e₁) :=
  rfl
#align linear_equiv.fun_congr_left_comp LinearEquiv.funCongrLeft_comp

@[simp]
theorem funCongrLeft_symm (e : m ≃ n) : (funCongrLeft R M e).symm = funCongrLeft R M e.symm :=
  rfl
#align linear_equiv.fun_congr_left_symm LinearEquiv.funCongrLeft_symm

end LinearEquiv

end FunLeft
