/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Module.Hom
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.LinearMap
import Mathlib.Data.DFinsupp.Basic
import Mathlib.Data.Finsupp.Basic

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

-- Porting note: TODO Erase this line.
attribute [-instance] Ring.toNonAssocRing

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*} {R₄ : Type*}
variable {S : Type*}
variable {K : Type*} {K₂ : Type*}
variable {M : Type*} {M' : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*} {M₄ : Type*}
variable {N : Type*} {N₂ : Type*}
variable {ι : Type*}
variable {V : Type*} {V₂ : Type*}

namespace Finsupp

theorem smul_sum {α : Type*} {β : Type*} {R : Type*} {M : Type*} [Zero β] [AddCommMonoid M]
    [DistribSMul R M] {v : α →₀ β} {c : R} {h : α → β → M} :
    c • v.sum h = v.sum fun a b => c • h a b :=
  Finset.smul_sum
#align finsupp.smul_sum Finsupp.smul_sum

@[simp]
theorem sum_smul_index_linearMap' {α : Type*} {R : Type*} {M : Type*} {M₂ : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid M₂] [Module R M₂] {v : α →₀ M} {c : R}
    {h : α → M →ₗ[R] M₂} : ((c • v).sum fun a => h a) = c • v.sum fun a => h a := by
  rw [Finsupp.sum_smul_index', Finsupp.smul_sum]
  -- ⊢ (sum v fun i c_1 => ↑(h i) (c • c_1)) = sum v fun a b => c • ↑(h a) b
  · simp only [map_smul]
    -- 🎉 no goals
  · intro i
    -- ⊢ ↑(h i) 0 = 0
    exact (h i).map_zero
    -- 🎉 no goals
#align finsupp.sum_smul_index_linear_map' Finsupp.sum_smul_index_linearMap'

variable (α : Type*) [Finite α]

variable (R M) [AddCommMonoid M] [Semiring R] [Module R M]

/-- Given `Finite α`, `linearEquivFunOnFinite R` is the natural `R`-linear equivalence between
`α →₀ β` and `α → β`. -/
@[simps apply]
noncomputable def linearEquivFunOnFinite : (α →₀ M) ≃ₗ[R] α → M :=
  { equivFunOnFinite with
    toFun := (⇑)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
#align finsupp.linear_equiv_fun_on_finite Finsupp.linearEquivFunOnFinite

@[simp]
theorem linearEquivFunOnFinite_single [DecidableEq α] (x : α) (m : M) :
    (linearEquivFunOnFinite R M α) (single x m) = Pi.single x m :=
  equivFunOnFinite_single x m
#align finsupp.linear_equiv_fun_on_finite_single Finsupp.linearEquivFunOnFinite_single

@[simp]
theorem linearEquivFunOnFinite_symm_single [DecidableEq α] (x : α) (m : M) :
    (linearEquivFunOnFinite R M α).symm (Pi.single x m) = single x m :=
  equivFunOnFinite_symm_single x m
#align finsupp.linear_equiv_fun_on_finite_symm_single Finsupp.linearEquivFunOnFinite_symm_single

@[simp]
theorem linearEquivFunOnFinite_symm_coe (f : α →₀ M) : (linearEquivFunOnFinite R M α).symm f = f :=
  (linearEquivFunOnFinite R M α).symm_apply_apply f
#align finsupp.linear_equiv_fun_on_finite_symm_coe Finsupp.linearEquivFunOnFinite_symm_coe

/-- If `α` has a unique term, then the type of finitely supported functions `α →₀ M` is
`R`-linearly equivalent to `M`. -/
noncomputable def LinearEquiv.finsuppUnique (α : Type*) [Unique α] : (α →₀ M) ≃ₗ[R] M :=
  { Finsupp.equivFunOnFinite.trans
      (Equiv.funUnique α M) with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
#align finsupp.linear_equiv.finsupp_unique Finsupp.LinearEquiv.finsuppUnique

variable {R M α}

@[simp]
theorem LinearEquiv.finsuppUnique_apply (α : Type*) [Unique α] (f : α →₀ M) :
    LinearEquiv.finsuppUnique R M α f = f default :=
  rfl
#align finsupp.linear_equiv.finsupp_unique_apply Finsupp.LinearEquiv.finsuppUnique_apply

@[simp]
theorem LinearEquiv.finsuppUnique_symm_apply {α : Type*} [Unique α] (m : M) :
    (LinearEquiv.finsuppUnique R M α).symm m = Finsupp.single default m := by
  ext; simp [LinearEquiv.finsuppUnique, Equiv.funUnique, single, Pi.single,
  -- ⊢ ↑(↑(LinearEquiv.symm (finsuppUnique R M α)) m) default = ↑(single default m) …
    equivFunOnFinite, Function.update]
#align finsupp.linear_equiv.finsupp_unique_symm_apply Finsupp.LinearEquiv.finsuppUnique_symm_apply

end Finsupp

/-- decomposing `x : ι → R` as a sum along the canonical basis -/
theorem pi_eq_sum_univ {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [Semiring R]
    (x : ι → R) : x = ∑ i, (x i) • fun j => if i = j then (1 : R) else 0 := by
  ext
  -- ⊢ x x✝ = Finset.sum Finset.univ (fun i => x i • fun j => if i = j then 1 else  …
  simp
  -- 🎉 no goals
#align pi_eq_sum_univ pi_eq_sum_univ

/-! ### Properties of linear maps -/


namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring R₄]
variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]
variable [AddCommMonoid M₃] [AddCommMonoid M₄]
variable [Module R M] [Module R M₁] [Module R₂ M₂] [Module R₃ M₃] [Module R₄ M₄]
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₃₄ : R₃ →+* R₄}
variable {σ₁₃ : R →+* R₃} {σ₂₄ : R₂ →+* R₄} {σ₁₄ : R →+* R₄}
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄]
variable [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄]
variable (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] M₃)

@[simp]
theorem map_sum {ι : Type*} {t : Finset ι} {g : ι → M} : f (∑ i in t, g i) = ∑ i in t, f (g i) :=
  f.toAddMonoidHom.map_sum _ _
#align linear_map.map_sum LinearMap.map_sum

theorem comp_assoc (h : M₃ →ₛₗ[σ₃₄] M₄) :
    ((h.comp g : M₂ →ₛₗ[σ₂₄] M₄).comp f : M →ₛₗ[σ₁₄] M₄) = h.comp (g.comp f : M →ₛₗ[σ₁₃] M₃) :=
  rfl
#align linear_map.comp_assoc LinearMap.comp_assoc


/-- The restriction of a linear map `f : M → M₂` to a submodule `p ⊆ M` gives a linear map
`p → M₂`. -/
def domRestrict (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) : p →ₛₗ[σ₁₂] M₂ :=
  f.comp p.subtype
#align linear_map.dom_restrict LinearMap.domRestrict

@[simp]
theorem domRestrict_apply (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) (x : p) :
    f.domRestrict p x = f x :=
  rfl
#align linear_map.dom_restrict_apply LinearMap.domRestrict_apply

/-- A linear map `f : M₂ → M` whose values lie in a submodule `p ⊆ M` can be restricted to a
linear map M₂ → p. -/
def codRestrict (p : Submodule R₂ M₂) (f : M →ₛₗ[σ₁₂] M₂) (h : ∀ c, f c ∈ p) : M →ₛₗ[σ₁₂] p := by
  refine' { toFun := fun c => ⟨f c, h c⟩.. } <;> intros <;> apply SetCoe.ext <;> simp
  -- ⊢ ∀ (x y : M), (fun c => { val := ↑f c, property := (_ : ↑f c ∈ p) }) (x + y)  …
                                                 -- ⊢ (fun c => { val := ↑f c, property := (_ : ↑f c ∈ p) }) (x✝ + y✝) = (fun c => …
                                                 -- ⊢ AddHom.toFun { toFun := fun c => { val := ↑f c, property := (_ : ↑f c ∈ p) } …
                                                            -- ⊢ ↑((fun c => { val := ↑f c, property := (_ : ↑f c ∈ p) }) (x✝ + y✝)) = ↑((fun …
                                                            -- ⊢ ↑(AddHom.toFun { toFun := fun c => { val := ↑f c, property := (_ : ↑f c ∈ p) …
                                                                                 -- 🎉 no goals
                                                                                 -- 🎉 no goals
#align linear_map.cod_restrict LinearMap.codRestrict

@[simp]
theorem codRestrict_apply (p : Submodule R₂ M₂) (f : M →ₛₗ[σ₁₂] M₂) {h} (x : M) :
    (codRestrict p f h x : M₂) = f x :=
  rfl
#align linear_map.cod_restrict_apply LinearMap.codRestrict_apply

@[simp]
theorem comp_codRestrict (p : Submodule R₃ M₃) (h : ∀ b, g b ∈ p) :
    ((codRestrict p g h).comp f : M →ₛₗ[σ₁₃] p) = codRestrict p (g.comp f) fun _ => h _ :=
  ext fun _ => rfl
#align linear_map.comp_cod_restrict LinearMap.comp_codRestrict

@[simp]
theorem subtype_comp_codRestrict (p : Submodule R₂ M₂) (h : ∀ b, f b ∈ p) :
    p.subtype.comp (codRestrict p f h) = f :=
  ext fun _ => rfl
#align linear_map.subtype_comp_cod_restrict LinearMap.subtype_comp_codRestrict

/-- Restrict domain and codomain of a linear map. -/
def restrict (f : M →ₗ[R] M₁) {p : Submodule R M} {q : Submodule R M₁} (hf : ∀ x ∈ p, f x ∈ q) :
    p →ₗ[R] q :=
  (f.domRestrict p).codRestrict q <| SetLike.forall.2 hf
#align linear_map.restrict LinearMap.restrict

@[simp]
theorem restrict_coe_apply (f : M →ₗ[R] M₁) {p : Submodule R M} {q : Submodule R M₁}
    (hf : ∀ x ∈ p, f x ∈ q) (x : p) : ↑(f.restrict hf x) = f x :=
  rfl
#align linear_map.restrict_coe_apply LinearMap.restrict_coe_apply

theorem restrict_apply {f : M →ₗ[R] M₁} {p : Submodule R M} {q : Submodule R M₁}
    (hf : ∀ x ∈ p, f x ∈ q) (x : p) : f.restrict hf x = ⟨f x, hf x.1 x.2⟩ :=
  rfl
#align linear_map.restrict_apply LinearMap.restrict_apply

theorem subtype_comp_restrict {f : M →ₗ[R] M₁} {p : Submodule R M} {q : Submodule R M₁}
    (hf : ∀ x ∈ p, f x ∈ q) : q.subtype.comp (f.restrict hf) = f.domRestrict p :=
  rfl
#align linear_map.subtype_comp_restrict LinearMap.subtype_comp_restrict

theorem restrict_eq_codRestrict_domRestrict {f : M →ₗ[R] M₁} {p : Submodule R M}
    {q : Submodule R M₁} (hf : ∀ x ∈ p, f x ∈ q) :
    f.restrict hf = (f.domRestrict p).codRestrict q fun x => hf x.1 x.2 :=
  rfl
#align linear_map.restrict_eq_cod_restrict_dom_restrict LinearMap.restrict_eq_codRestrict_domRestrict

theorem restrict_eq_domRestrict_codRestrict {f : M →ₗ[R] M₁} {p : Submodule R M}
    {q : Submodule R M₁} (hf : ∀ x, f x ∈ q) :
    (f.restrict fun x _ => hf x) = (f.codRestrict q hf).domRestrict p :=
  rfl
#align linear_map.restrict_eq_dom_restrict_cod_restrict LinearMap.restrict_eq_domRestrict_codRestrict

instance uniqueOfLeft [Subsingleton M] : Unique (M →ₛₗ[σ₁₂] M₂) :=
  { inferInstanceAs (Inhabited (M →ₛₗ[σ₁₂] M₂)) with
    uniq := fun f => ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero] }
                                     -- 🎉 no goals
#align linear_map.unique_of_left LinearMap.uniqueOfLeft

instance uniqueOfRight [Subsingleton M₂] : Unique (M →ₛₗ[σ₁₂] M₂) :=
  coe_injective.unique
#align linear_map.unique_of_right LinearMap.uniqueOfRight

/-- Evaluation of a `σ₁₂`-linear map at a fixed `a`, as an `addMonoidHom`. -/
def evalAddMonoidHom (a : M) : (M →ₛₗ[σ₁₂] M₂) →+ M₂
    where
  toFun f := f a
  map_add' f g := LinearMap.add_apply f g a
  map_zero' := rfl
#align linear_map.eval_add_monoid_hom LinearMap.evalAddMonoidHom

/-- `linear_map.toAddMonoidHom` promoted to a `toAddMonoidHom` -/
def toAddMonoidHom' : (M →ₛₗ[σ₁₂] M₂) →+ M →+ M₂
    where
  toFun := toAddMonoidHom
  map_zero' := by ext; rfl
                  -- ⊢ ↑(toAddMonoidHom 0) x✝ = ↑0 x✝
                       -- 🎉 no goals
  map_add' := by intros; ext; rfl
                 -- ⊢ ZeroHom.toFun { toFun := toAddMonoidHom, map_zero' := (_ : toAddMonoidHom 0  …
                         -- ⊢ ↑(ZeroHom.toFun { toFun := toAddMonoidHom, map_zero' := (_ : toAddMonoidHom  …
                              -- 🎉 no goals
#align linear_map.to_add_monoid_hom' LinearMap.toAddMonoidHom'

theorem sum_apply (t : Finset ι) (f : ι → M →ₛₗ[σ₁₂] M₂) (b : M) :
    (∑ d in t, f d) b = ∑ d in t, f d b :=
  _root_.map_sum ((AddMonoidHom.eval b).comp toAddMonoidHom') f _
#align linear_map.sum_apply LinearMap.sum_apply

section SmulRight

variable [Semiring S] [Module R S] [Module S M] [IsScalarTower R S M]

/-- When `f` is an `R`-linear map taking values in `S`, then `fun ↦ b, f b • x` is an `R`-linear
map. -/
def smulRight (f : M₁ →ₗ[R] S) (x : M) : M₁ →ₗ[R] M
    where
  toFun b := f b • x
  map_add' x y := by dsimp only; rw [f.map_add, add_smul]
                     -- ⊢ ↑f (x + y) • x✝ = ↑f x • x✝ + ↑f y • x✝
                                 -- 🎉 no goals
  map_smul' b y := by dsimp; rw [map_smul, smul_assoc]
                      -- ⊢ ↑f (b • y) • x = b • ↑f y • x
                             -- 🎉 no goals
#align linear_map.smul_right LinearMap.smulRight

@[simp]
theorem coe_smulRight (f : M₁ →ₗ[R] S) (x : M) : (smulRight f x : M₁ → M) = fun c => f c • x :=
  rfl
#align linear_map.coe_smul_right LinearMap.coe_smulRight

theorem smulRight_apply (f : M₁ →ₗ[R] S) (x : M) (c : M₁) : smulRight f x c = f c • x :=
  rfl
#align linear_map.smul_right_apply LinearMap.smulRight_apply

end SmulRight

instance [Nontrivial M] : Nontrivial (Module.End R M) := by
  obtain ⟨m, ne⟩ := (nontrivial_iff_exists_ne (0 : M)).mp inferInstance
  -- ⊢ Nontrivial (Module.End R M)
  exact nontrivial_of_ne 1 0 fun p => ne (LinearMap.congr_fun p m)
  -- 🎉 no goals

@[simp, norm_cast]
theorem coeFn_sum {ι : Type*} (t : Finset ι) (f : ι → M →ₛₗ[σ₁₂] M₂) :
    ⇑(∑ i in t, f i ) = ∑ i in t, (f i : M → M₂) :=
  _root_.map_sum
    (show AddMonoidHom (M →ₛₗ[σ₁₂] M₂) (M → M₂)
      from { toFun := FunLike.coe,
             map_zero' := rfl
             map_add' := fun _ _ => rfl }) _ _
#align linear_map.coe_fn_sum LinearMap.coeFn_sum

theorem coe_pow (f : M →ₗ[R] M) (n : ℕ) : ⇑(f ^ n) = f^[n] := hom_coe_pow _ rfl (fun _ _ ↦ rfl) _ _
#align linear_map.coe_pow LinearMap.coe_pow

theorem pow_apply (f : M →ₗ[R] M) (n : ℕ) (m : M) : (f ^ n) m = f^[n] m := congr_fun (coe_pow f n) m
#align linear_map.pow_apply LinearMap.pow_apply

theorem pow_map_zero_of_le {f : Module.End R M} {m : M} {k l : ℕ} (hk : k ≤ l)
    (hm : (f ^ k) m = 0) : (f ^ l) m = 0 := by
  rw [← tsub_add_cancel_of_le hk, pow_add, mul_apply, hm, map_zero]
  -- 🎉 no goals
#align linear_map.pow_map_zero_of_le LinearMap.pow_map_zero_of_le

theorem commute_pow_left_of_commute {f : M →ₛₗ[σ₁₂] M₂} {g : Module.End R M} {g₂ : Module.End R₂ M₂}
    (h : g₂.comp f = f.comp g) (k : ℕ) : (g₂ ^ k).comp f = f.comp (g ^ k) := by
  induction' k with k ih
  -- ⊢ comp (g₂ ^ Nat.zero) f = comp f (g ^ Nat.zero)
  · simp only [pow_zero, Nat.zero_eq]; rfl
    -- ⊢ comp 1 f = comp f 1
                                       -- 🎉 no goals
  · rw [pow_succ, pow_succ, LinearMap.mul_eq_comp, LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc,
      h, LinearMap.comp_assoc, LinearMap.mul_eq_comp]
#align linear_map.commute_pow_left_of_commute LinearMap.commute_pow_left_of_commute

theorem submodule_pow_eq_zero_of_pow_eq_zero {N : Submodule R M} {g : Module.End R N}
    {G : Module.End R M} (h : G.comp N.subtype = N.subtype.comp g) {k : ℕ} (hG : G ^ k = 0) :
    --Porting note: ugly `HPow.hPow` instead of `^` notation
    HPow.hPow g k = 0 := by
  ext m
  -- ⊢ ↑(↑(g ^ k) m) = ↑(↑0 m)
  have hg : N.subtype.comp (g ^ k) m = 0 := by
    rw [← commute_pow_left_of_commute h, hG, zero_comp, zero_apply]
  simpa using hg
  -- 🎉 no goals
#align linear_map.submodule_pow_eq_zero_of_pow_eq_zero LinearMap.submodule_pow_eq_zero_of_pow_eq_zero

@[simp]
theorem id_pow (n : ℕ) : (id : M →ₗ[R] M) ^ n = id :=
  one_pow n
#align linear_map.id_pow LinearMap.id_pow

section

variable {f' : M →ₗ[R] M}

theorem iterate_succ (n : ℕ) : f' ^ (n + 1) = comp (f' ^ n) f' := by rw [pow_succ', mul_eq_comp]
                                                                     -- 🎉 no goals
#align linear_map.iterate_succ LinearMap.iterate_succ

theorem iterate_surjective (h : Surjective f') : ∀ n : ℕ, Surjective (f' ^ n)
  | 0 => surjective_id
  | n + 1 => by
    rw [iterate_succ]
    -- ⊢ Surjective ↑(comp (f' ^ n) f')
    exact (iterate_surjective h n).comp h
    -- 🎉 no goals
#align linear_map.iterate_surjective LinearMap.iterate_surjective

theorem iterate_injective (h : Injective f') : ∀ n : ℕ, Injective (f' ^ n)
  | 0 => injective_id
  | n + 1 => by
    rw [iterate_succ]
    -- ⊢ Injective ↑(comp (f' ^ n) f')
    exact (iterate_injective h n).comp h
    -- 🎉 no goals
#align linear_map.iterate_injective LinearMap.iterate_injective

theorem iterate_bijective (h : Bijective f') : ∀ n : ℕ, Bijective (f' ^ n)
  | 0 => bijective_id
  | n + 1 => by
    rw [iterate_succ]
    -- ⊢ Bijective ↑(comp (f' ^ n) f')
    exact (iterate_bijective h n).comp h
    -- 🎉 no goals
#align linear_map.iterate_bijective LinearMap.iterate_bijective

theorem injective_of_iterate_injective {n : ℕ} (hn : n ≠ 0) (h : Injective (f' ^ n)) :
    Injective f' := by
  rw [← Nat.succ_pred_eq_of_pos (pos_iff_ne_zero.mpr hn), iterate_succ, coe_comp] at h
  -- ⊢ Injective ↑f'
  exact h.of_comp
  -- 🎉 no goals
#align linear_map.injective_of_iterate_injective LinearMap.injective_of_iterate_injective

theorem surjective_of_iterate_surjective {n : ℕ} (hn : n ≠ 0) (h : Surjective (f' ^ n)) :
    Surjective f' := by
  rw [← Nat.succ_pred_eq_of_pos (pos_iff_ne_zero.mpr hn),
    Nat.succ_eq_add_one, add_comm, pow_add] at h
  exact Surjective.of_comp h
  -- 🎉 no goals
#align linear_map.surjective_of_iterate_surjective LinearMap.surjective_of_iterate_surjective

theorem pow_apply_mem_of_forall_mem {p : Submodule R M} (n : ℕ) (h : ∀ x ∈ p, f' x ∈ p) (x : M)
    (hx : x ∈ p) : (f' ^ n) x ∈ p := by
  induction' n with n ih generalizing x; · simpa
  -- ⊢ ↑(f' ^ Nat.zero) x ∈ p
                                           -- 🎉 no goals
  simpa only [iterate_succ, coe_comp, Function.comp_apply, restrict_apply] using ih _ (h _ hx)
  -- 🎉 no goals
#align linear_map.pow_apply_mem_of_forall_mem LinearMap.pow_apply_mem_of_forall_mem

theorem pow_restrict {p : Submodule R M} (n : ℕ) (h : ∀ x ∈ p, f' x ∈ p)
    (h' := pow_apply_mem_of_forall_mem n h) :
    --Porting note: ugly `HPow.hPow` instead of `^` notation
    HPow.hPow (f'.restrict h) n = (HPow.hPow f' n).restrict h' := by
  ext x
  -- ⊢ ↑(↑(restrict f' h ^ n) x) = ↑(↑(restrict (f' ^ n) h') x)
  have : Semiconj (↑) (f'.restrict h) f' := fun _ ↦ rfl
  -- ⊢ ↑(↑(restrict f' h ^ n) x) = ↑(↑(restrict (f' ^ n) h') x)
  simp [coe_pow, this.iterate_right _ _]
  -- 🎉 no goals
#align linear_map.pow_restrict LinearMap.pow_restrict

end

/-- A linear map `f` applied to `x : ι → R` can be computed using the image under `f` of elements
of the canonical basis. -/
theorem pi_apply_eq_sum_univ [Fintype ι] [DecidableEq ι] (f : (ι → R) →ₗ[R] M) (x : ι → R) :
    f x = ∑ i, x i • f fun j => if i = j then 1 else 0 := by
  conv_lhs => rw [pi_eq_sum_univ x, f.map_sum]
  -- ⊢ ∑ i : ι, ↑f (x i • fun j => if i = j then 1 else 0) = ∑ i : ι, x i • ↑f fun  …
  refine Finset.sum_congr rfl (fun _ _ => ?_)
  -- ⊢ ↑f (x x✝¹ • fun j => if x✝¹ = j then 1 else 0) = x x✝¹ • ↑f fun j => if x✝¹  …
  rw [map_smul]
  -- 🎉 no goals
#align linear_map.pi_apply_eq_sum_univ LinearMap.pi_apply_eq_sum_univ

end AddCommMonoid

section Module

variable [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [Module R M] [Module R M₂] [Module R M₃] [Module S M₂] [Module S M₃] [SMulCommClass R S M₂]
  [SMulCommClass R S M₃] (f : M →ₗ[R] M₂)

variable (S)

/-- Applying a linear map at `v : M`, seen as `S`-linear map from `M →ₗ[R] M₂` to `M₂`.

 See `LinearMap.applyₗ` for a version where `S = R`. -/
@[simps]
def applyₗ' : M →+ (M →ₗ[R] M₂) →ₗ[S] M₂
    where
  toFun v :=
    { toFun := fun f => f v
      map_add' := fun f g => f.add_apply g v
      map_smul' := fun x f => f.smul_apply x v }
  map_zero' := LinearMap.ext fun f => f.map_zero
  map_add' _ _ := LinearMap.ext fun f => f.map_add _ _
#align linear_map.applyₗ' LinearMap.applyₗ'

section

variable (R M)

/-- The equivalence between R-linear maps from `R` to `M`, and points of `M` itself.
This says that the forgetful functor from `R`-modules to types is representable, by `R`.

This as an `S`-linear equivalence, under the assumption that `S` acts on `M` commuting with `R`.
When `R` is commutative, we can take this to be the usual action with `S = R`.
Otherwise, `S = ℕ` shows that the equivalence is additive.
See note [bundled maps over different rings].
-/
@[simps]
def ringLmapEquivSelf [Module S M] [SMulCommClass R S M] : (R →ₗ[R] M) ≃ₗ[S] M :=
  { applyₗ' S (1 : R) with
    toFun := fun f => f 1
    invFun := smulRight (1 : R →ₗ[R] R)
    left_inv := fun f => by
      ext
      -- ⊢ ↑(smulRight 1 (AddHom.toFun { toAddHom := { toFun := fun f => ↑f 1, map_add' …
      simp only [coe_smulRight, one_apply, smul_eq_mul, ← map_smul f, mul_one]
      -- 🎉 no goals
    right_inv := fun x => by simp }
                             -- 🎉 no goals
#align linear_map.ring_lmap_equiv_self LinearMap.ringLmapEquivSelf

end

end Module

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₂] [Module R M₃]

variable (f g : M →ₗ[R] M₂)

/-- Composition by `f : M₂ → M₃` is a linear map from the space of linear maps `M → M₂`
to the space of linear maps `M₂ → M₃`. -/
def compRight (f : M₂ →ₗ[R] M₃) : (M →ₗ[R] M₂) →ₗ[R] M →ₗ[R] M₃
    where
  toFun := f.comp
  map_add' _ _ := LinearMap.ext fun _ => map_add f _ _
  map_smul' _ _ := LinearMap.ext fun _ => map_smul f _ _
#align linear_map.comp_right LinearMap.compRight

@[simp]
theorem compRight_apply (f : M₂ →ₗ[R] M₃) (g : M →ₗ[R] M₂) : compRight f g = f.comp g :=
  rfl
#align linear_map.comp_right_apply LinearMap.compRight_apply

/-- Applying a linear map at `v : M`, seen as a linear map from `M →ₗ[R] M₂` to `M₂`.
See also `LinearMap.applyₗ'` for a version that works with two different semirings.

This is the `LinearMap` version of `toAddMonoidHom.eval`. -/
@[simps]
def applyₗ : M →ₗ[R] (M →ₗ[R] M₂) →ₗ[R] M₂ :=
  { applyₗ' R with
    toFun := fun v => { applyₗ' R v with toFun := fun f => f v }
    map_smul' := fun _ _ => LinearMap.ext fun f => map_smul f _ _ }
#align linear_map.applyₗ LinearMap.applyₗ

/-- Alternative version of `dom_restrict` as a linear map. -/
def domRestrict' (p : Submodule R M) : (M →ₗ[R] M₂) →ₗ[R] p →ₗ[R] M₂
    where
  toFun φ := φ.domRestrict p
  map_add' := by simp [LinearMap.ext_iff]
                 -- 🎉 no goals
  map_smul' := by simp [LinearMap.ext_iff]
                  -- 🎉 no goals
#align linear_map.dom_restrict' LinearMap.domRestrict'

@[simp]
theorem domRestrict'_apply (f : M →ₗ[R] M₂) (p : Submodule R M) (x : p) :
    domRestrict' p f x = f x :=
  rfl
#align linear_map.dom_restrict'_apply LinearMap.domRestrict'_apply

/--
The family of linear maps `M₂ → M` parameterised by `f ∈ M₂ → R`, `x ∈ M`, is linear in `f`, `x`.
-/
def smulRightₗ : (M₂ →ₗ[R] R) →ₗ[R] M →ₗ[R] M₂ →ₗ[R] M
    where
  toFun f :=
    { toFun := LinearMap.smulRight f
      map_add' := fun m m' => by
        ext
        -- ⊢ ↑(smulRight f (m + m')) x✝ = ↑(smulRight f m + smulRight f m') x✝
        apply smul_add
        -- 🎉 no goals
      map_smul' := fun c m => by
        ext
        -- ⊢ ↑(AddHom.toFun { toFun := smulRight f, map_add' := (_ : ∀ (m m' : M), smulRi …
        apply smul_comm }
        -- 🎉 no goals
  map_add' f f' := by
    ext
    -- ⊢ ↑(↑((fun f => { toAddHom := { toFun := smulRight f, map_add' := (_ : ∀ (m m' …
    apply add_smul
    -- 🎉 no goals
  map_smul' c f := by
    ext
    -- ⊢ ↑(↑(AddHom.toFun { toFun := fun f => { toAddHom := { toFun := smulRight f, m …
    apply mul_smul
    -- 🎉 no goals
#align linear_map.smul_rightₗ LinearMap.smulRightₗ

@[simp]
theorem smulRightₗ_apply (f : M₂ →ₗ[R] R) (x : M) (c : M₂) :
    (smulRightₗ : (M₂ →ₗ[R] R) →ₗ[R] M →ₗ[R] M₂ →ₗ[R] M) f x c = f c • x :=
  rfl
#align linear_map.smul_rightₗ_apply LinearMap.smulRightₗ_apply

end CommSemiring

end LinearMap

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
                 -- ⊢ AddMonoidHom.toNatLinearMap (x✝ + y✝) = AddMonoidHom.toNatLinearMap x✝ + Add …
                         -- ⊢ ↑(AddMonoidHom.toNatLinearMap (x✝¹ + y✝)) x✝ = ↑(AddMonoidHom.toNatLinearMap …
                              -- 🎉 no goals
  map_smul' := by intros; ext; rfl
                  -- ⊢ AddHom.toFun { toFun := AddMonoidHom.toNatLinearMap, map_add' := (_ : ∀ (x y …
                          -- ⊢ ↑(AddHom.toFun { toFun := AddMonoidHom.toNatLinearMap, map_add' := (_ : ∀ (x …
                               -- 🎉 no goals
  left_inv := by intro f; ext; rfl
                 -- ⊢ LinearMap.toAddMonoidHom (AddHom.toFun { toAddHom := { toFun := AddMonoidHom …
                          -- ⊢ ↑(LinearMap.toAddMonoidHom (AddHom.toFun { toAddHom := { toFun := AddMonoidH …
                               -- 🎉 no goals
  right_inv := by intro f; ext; rfl
                  -- ⊢ AddHom.toFun { toAddHom := { toFun := AddMonoidHom.toNatLinearMap, map_add'  …
                           -- ⊢ ↑(AddHom.toFun { toAddHom := { toFun := AddMonoidHom.toNatLinearMap, map_add …
                                -- 🎉 no goals
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
                 -- ⊢ AddMonoidHom.toIntLinearMap (x✝ + y✝) = AddMonoidHom.toIntLinearMap x✝ + Add …
                         -- ⊢ ↑(AddMonoidHom.toIntLinearMap (x✝¹ + y✝)) x✝ = ↑(AddMonoidHom.toIntLinearMap …
                              -- 🎉 no goals
  map_smul' := by intros; ext; rfl
                  -- ⊢ AddHom.toFun { toFun := AddMonoidHom.toIntLinearMap, map_add' := (_ : ∀ (x y …
                          -- ⊢ ↑(AddHom.toFun { toFun := AddMonoidHom.toIntLinearMap, map_add' := (_ : ∀ (x …
                               -- 🎉 no goals
  left_inv := by intro f; ext; rfl
                 -- ⊢ LinearMap.toAddMonoidHom (AddHom.toFun { toAddHom := { toFun := AddMonoidHom …
                          -- ⊢ ↑(LinearMap.toAddMonoidHom (AddHom.toFun { toAddHom := { toFun := AddMonoidH …
                               -- 🎉 no goals
  right_inv := by intro f; ext; rfl
                  -- ⊢ AddHom.toFun { toAddHom := { toFun := AddMonoidHom.toIntLinearMap, map_add'  …
                           -- ⊢ ↑(AddHom.toFun { toAddHom := { toFun := AddMonoidHom.toIntLinearMap, map_add …
                                -- 🎉 no goals
#align add_monoid_hom_lequiv_int addMonoidHomLequivInt

/-! ### Properties of submodules -/


namespace Submodule

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M']
variable [Module R M] [Module R M'] [Module R₂ M₂] [Module R₃ M₃]
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}
variable {σ₂₁ : R₂ →+* R}
variable [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable (p p' : Submodule R M) (q q' : Submodule R₂ M₂)
variable (q₁ q₁' : Submodule R M')
variable {r : R} {x y : M}

open Set

variable {p p'}

/-- If two submodules `p` and `p'` satisfy `p ⊆ p'`, then `ofLe p p'` is the linear map version of
this inclusion. -/
def ofLe (h : p ≤ p') : p →ₗ[R] p' :=
  p.subtype.codRestrict p' fun ⟨_, hx⟩ => h hx
#align submodule.of_le Submodule.ofLe

@[simp]
theorem coe_ofLe (h : p ≤ p') (x : p) : (ofLe h x : M) = x :=
  rfl
#align submodule.coe_of_le Submodule.coe_ofLe

theorem ofLe_apply (h : p ≤ p') (x : p) : ofLe h x = ⟨x, h x.2⟩ :=
  rfl
#align submodule.of_le_apply Submodule.ofLe_apply

theorem ofLe_injective (h : p ≤ p') : Function.Injective (ofLe h) := fun _ _ h =>
  Subtype.val_injective (Subtype.mk.inj h)
#align submodule.of_le_injective Submodule.ofLe_injective

variable (p p')

theorem subtype_comp_ofLe (p q : Submodule R M) (h : p ≤ q) :
    q.subtype.comp (ofLe h) = p.subtype := by
  ext ⟨b, hb⟩
  -- ⊢ ↑(LinearMap.comp (Submodule.subtype q) (ofLe h)) { val := b, property := hb  …
  rfl
  -- 🎉 no goals
#align submodule.subtype_comp_of_le Submodule.subtype_comp_ofLe

variable (R)

@[simp]
theorem subsingleton_iff : Subsingleton (Submodule R M) ↔ Subsingleton M :=
  have h : Subsingleton (Submodule R M) ↔ Subsingleton (AddSubmonoid M) := by
    rw [← subsingleton_iff_bot_eq_top, ← subsingleton_iff_bot_eq_top, ← toAddSubmonoid_eq]; rfl
    -- ⊢ ⊥.toAddSubmonoid = ⊤.toAddSubmonoid ↔ ⊥ = ⊤
                                                                                            -- 🎉 no goals
  h.trans AddSubmonoid.subsingleton_iff
#align submodule.subsingleton_iff Submodule.subsingleton_iff

@[simp]
theorem nontrivial_iff : Nontrivial (Submodule R M) ↔ Nontrivial M :=
  not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans <| subsingleton_iff R).trans
      not_nontrivial_iff_subsingleton.symm)
#align submodule.nontrivial_iff Submodule.nontrivial_iff

variable {R}

instance [Subsingleton M] : Unique (Submodule R M) :=
  ⟨⟨⊥⟩, fun a => @Subsingleton.elim _ ((subsingleton_iff R).mpr ‹_›) a _⟩

instance unique' [Subsingleton R] : Unique (Submodule R M) := by
  haveI := Module.subsingleton R M; infer_instance
  -- ⊢ Unique (Submodule R M)
                                    -- 🎉 no goals
#align submodule.unique' Submodule.unique'

instance [Nontrivial M] : Nontrivial (Submodule R M) :=
  (nontrivial_iff R).mpr ‹_›

theorem mem_right_iff_eq_zero_of_disjoint {p p' : Submodule R M} (h : Disjoint p p') {x : p} :
    (x : M) ∈ p' ↔ x = 0 :=
  ⟨fun hx => coe_eq_zero.1 <| disjoint_def.1 h x x.2 hx, fun h => h.symm ▸ p'.zero_mem⟩
#align submodule.mem_right_iff_eq_zero_of_disjoint Submodule.mem_right_iff_eq_zero_of_disjoint

theorem mem_left_iff_eq_zero_of_disjoint {p p' : Submodule R M} (h : Disjoint p p') {x : p'} :
    (x : M) ∈ p ↔ x = 0 :=
  ⟨fun hx => coe_eq_zero.1 <| disjoint_def.1 h x hx x.2, fun h => h.symm ▸ p.zero_mem⟩
#align submodule.mem_left_iff_eq_zero_of_disjoint Submodule.mem_left_iff_eq_zero_of_disjoint

section

variable [RingHomSurjective σ₁₂] {F : Type*} [sc : SemilinearMapClass F σ₁₂ M M₂]

/-- The pushforward of a submodule `p ⊆ M` by `f : M → M₂` -/
def map (f : F) (p : Submodule R M) : Submodule R₂ M₂ :=
  { p.toAddSubmonoid.map f with
    carrier := f '' p
    smul_mem' := by
      rintro c x ⟨y, hy, rfl⟩
      -- ⊢ c • ↑f y ∈ { toAddSubsemigroup := { carrier := ↑f '' ↑p, add_mem' := (_ : ∀  …
      obtain ⟨a, rfl⟩ := σ₁₂.surjective c
      -- ⊢ ↑σ₁₂ a • ↑f y ∈ { toAddSubsemigroup := { carrier := ↑f '' ↑p, add_mem' := (_ …
      exact ⟨_, p.smul_mem a hy, map_smulₛₗ f _ _⟩ }
      -- 🎉 no goals
#align submodule.map Submodule.map

@[simp]
theorem map_coe (f : F) (p : Submodule R M) : (map f p : Set M₂) = f '' p :=
  rfl
#align submodule.map_coe Submodule.map_coe

theorem map_toAddSubmonoid (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) :
    (p.map f).toAddSubmonoid = p.toAddSubmonoid.map (f : M →+ M₂) :=
  SetLike.coe_injective rfl
#align submodule.map_to_add_submonoid Submodule.map_toAddSubmonoid

theorem map_to_add_submonoid' (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) :
    (p.map f).toAddSubmonoid = p.toAddSubmonoid.map f :=
  SetLike.coe_injective rfl
#align submodule.map_to_add_submonoid' Submodule.map_to_add_submonoid'

@[simp]
theorem mem_map {f : F} {p : Submodule R M} {x : M₂} : x ∈ map f p ↔ ∃ y, y ∈ p ∧ f y = x :=
  Iff.rfl
#align submodule.mem_map Submodule.mem_map

theorem mem_map_of_mem {f : F} {p : Submodule R M} {r} (h : r ∈ p) : f r ∈ map f p :=
  Set.mem_image_of_mem _ h
#align submodule.mem_map_of_mem Submodule.mem_map_of_mem

theorem apply_coe_mem_map (f : F) {p : Submodule R M} (r : p) : f r ∈ map f p :=
  mem_map_of_mem r.prop
#align submodule.apply_coe_mem_map Submodule.apply_coe_mem_map

@[simp]
theorem map_id : map (LinearMap.id : M →ₗ[R] M) p = p :=
  Submodule.ext fun a => by simp
                            -- 🎉 no goals
#align submodule.map_id Submodule.map_id

theorem map_comp [RingHomSurjective σ₂₃] [RingHomSurjective σ₁₃] (f : M →ₛₗ[σ₁₂] M₂)
    (g : M₂ →ₛₗ[σ₂₃] M₃) (p : Submodule R M) : map (g.comp f : M →ₛₗ[σ₁₃] M₃) p = map g (map f p) :=
  SetLike.coe_injective <| by simp only [← image_comp, map_coe, LinearMap.coe_comp, comp_apply]
                              -- 🎉 no goals
#align submodule.map_comp Submodule.map_comp

theorem map_mono {f : F} {p p' : Submodule R M} : p ≤ p' → map f p ≤ map f p' :=
  image_subset _
#align submodule.map_mono Submodule.map_mono

@[simp]
theorem map_zero : map (0 : M →ₛₗ[σ₁₂] M₂) p = ⊥ :=
  have : ∃ x : M, x ∈ p := ⟨0, p.zero_mem⟩
  ext <| by simp [this, eq_comm]
            -- 🎉 no goals
#align submodule.map_zero Submodule.map_zero

theorem map_add_le (f g : M →ₛₗ[σ₁₂] M₂) : map (f + g) p ≤ map f p ⊔ map g p := by
  rintro x ⟨m, hm, rfl⟩
  -- ⊢ ↑(f + g) m ∈ map f p ⊔ map g p
  exact add_mem_sup (mem_map_of_mem hm) (mem_map_of_mem hm)
  -- 🎉 no goals
#align submodule.map_add_le Submodule.map_add_le

theorem range_map_nonempty (N : Submodule R M) :
    (Set.range (fun ϕ => Submodule.map ϕ N : (M →ₛₗ[σ₁₂] M₂) → Submodule R₂ M₂)).Nonempty :=
  ⟨_, Set.mem_range.mpr ⟨0, rfl⟩⟩
#align submodule.range_map_nonempty Submodule.range_map_nonempty

end

section SemilinearMap

variable {F : Type*} [sc : SemilinearMapClass F σ₁₂ M M₂]

/-- The pushforward of a submodule by an injective linear map is
linearly equivalent to the original submodule. See also `LinearEquiv.submoduleMap` for a
computable version when `f` has an explicit inverse. -/
noncomputable def equivMapOfInjective (f : F) (i : Injective f) (p : Submodule R M) :
    p ≃ₛₗ[σ₁₂] p.map f :=
  {
    Equiv.Set.image f p
      i with
    map_add' := by
      intros
      -- ⊢ Equiv.toFun src✝ (x✝ + y✝) = Equiv.toFun src✝ x✝ + Equiv.toFun src✝ y✝
      simp only [coe_add, map_add, Equiv.toFun_as_coe, Equiv.Set.image_apply]
      -- ⊢ { val := ↑f ↑x✝ + ↑f ↑y✝, property := (_ : (fun x => x ∈ ↑f '' ↑p) (↑f ↑x✝ + …
      rfl
      -- 🎉 no goals
    map_smul' := by
      intros
      -- ⊢ AddHom.toFun { toFun := src✝.toFun, map_add' := (_ : ∀ (x y : { x // x ∈ p } …
      simp only [coe_smul_of_tower, map_smulₛₗ, Equiv.toFun_as_coe, Equiv.Set.image_apply]
      -- ⊢ { val := ↑σ₁₂ r✝ • ↑f ↑x✝, property := (_ : (fun x => x ∈ ↑f '' ↑p) (↑σ₁₂ r✝ …
      rfl }
      -- 🎉 no goals
#align submodule.equiv_map_of_injective Submodule.equivMapOfInjective

@[simp]
theorem coe_equivMapOfInjective_apply (f : F) (i : Injective f) (p : Submodule R M) (x : p) :
    (equivMapOfInjective f i p x : M₂) = f x :=
  rfl
#align submodule.coe_equiv_map_of_injective_apply Submodule.coe_equivMapOfInjective_apply

/-- The pullback of a submodule `p ⊆ M₂` along `f : M → M₂` -/
def comap (f : F) (p : Submodule R₂ M₂) : Submodule R M :=
  { p.toAddSubmonoid.comap f with
    carrier := f ⁻¹' p
    smul_mem' := fun a x h => by simp [p.smul_mem (σ₁₂ a) h] }
                                 -- 🎉 no goals
#align submodule.comap Submodule.comap

@[simp]
theorem comap_coe (f : F) (p : Submodule R₂ M₂) : (comap f p : Set M) = f ⁻¹' p :=
  rfl
#align submodule.comap_coe Submodule.comap_coe

@[simp]
theorem mem_comap {f : F} {p : Submodule R₂ M₂} : x ∈ comap f p ↔ f x ∈ p :=
  Iff.rfl
#align submodule.mem_comap Submodule.mem_comap

@[simp]
theorem comap_id : comap (LinearMap.id : M →ₗ[R] M) p = p :=
  SetLike.coe_injective rfl
#align submodule.comap_id Submodule.comap_id

theorem comap_comp (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] M₃) (p : Submodule R₃ M₃) :
    comap (g.comp f : M →ₛₗ[σ₁₃] M₃) p = comap f (comap g p) :=
  rfl
#align submodule.comap_comp Submodule.comap_comp

theorem comap_mono {f : F} {q q' : Submodule R₂ M₂} : q ≤ q' → comap f q ≤ comap f q' :=
  preimage_mono
#align submodule.comap_mono Submodule.comap_mono

theorem le_comap_pow_of_le_comap (p : Submodule R M) {f : M →ₗ[R] M} (h : p ≤ p.comap f) (k : ℕ) :
    p ≤ p.comap (f ^ k) := by
  induction' k with k ih
  -- ⊢ p ≤ comap (f ^ Nat.zero) p
  · simp [LinearMap.one_eq_id]
    -- 🎉 no goals
  · simp [LinearMap.iterate_succ, comap_comp, h.trans (comap_mono ih)]
    -- 🎉 no goals
#align submodule.le_comap_pow_of_le_comap Submodule.le_comap_pow_of_le_comap

section

variable [RingHomSurjective σ₁₂]

theorem map_le_iff_le_comap {f : F} {p : Submodule R M} {q : Submodule R₂ M₂} :
    map f p ≤ q ↔ p ≤ comap f q :=
  image_subset_iff
#align submodule.map_le_iff_le_comap Submodule.map_le_iff_le_comap

theorem gc_map_comap (f : F) : GaloisConnection (map f) (comap f)
  | _, _ => map_le_iff_le_comap
#align submodule.gc_map_comap Submodule.gc_map_comap

@[simp]
theorem map_bot (f : F) : map f ⊥ = ⊥ :=
  (gc_map_comap f).l_bot
#align submodule.map_bot Submodule.map_bot

@[simp]
theorem map_sup (f : F) : map f (p ⊔ p') = map f p ⊔ map f p' :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sup
#align submodule.map_sup Submodule.map_sup

@[simp]
theorem map_iSup {ι : Sort*} (f : F) (p : ι → Submodule R M) :
    map f (⨆ i, p i) = ⨆ i, map f (p i) :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_iSup
#align submodule.map_supr Submodule.map_iSup

end

@[simp]
theorem comap_top (f : F) : comap f ⊤ = ⊤ :=
  rfl
#align submodule.comap_top Submodule.comap_top

@[simp]
theorem comap_inf (f : F) : comap f (q ⊓ q') = comap f q ⊓ comap f q' :=
  rfl
#align submodule.comap_inf Submodule.comap_inf

@[simp]
theorem comap_iInf [RingHomSurjective σ₁₂] {ι : Sort*} (f : F) (p : ι → Submodule R₂ M₂) :
    comap f (⨅ i, p i) = ⨅ i, comap f (p i) :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_iInf
#align submodule.comap_infi Submodule.comap_iInf

@[simp]
theorem comap_zero : comap (0 : M →ₛₗ[σ₁₂] M₂) q = ⊤ :=
  ext <| by simp
            -- 🎉 no goals
#align submodule.comap_zero Submodule.comap_zero

theorem map_comap_le [RingHomSurjective σ₁₂] (f : F) (q : Submodule R₂ M₂) :
    map f (comap f q) ≤ q :=
  (gc_map_comap f).l_u_le _
#align submodule.map_comap_le Submodule.map_comap_le

theorem le_comap_map [RingHomSurjective σ₁₂] (f : F) (p : Submodule R M) : p ≤ comap f (map f p) :=
  (gc_map_comap f).le_u_l _
#align submodule.le_comap_map Submodule.le_comap_map

section GaloisInsertion

variable {f : F} (hf : Surjective f)

variable [RingHomSurjective σ₁₂]

/-- `map f` and `comap f` form a `GaloisInsertion` when `f` is surjective. -/
def giMapComap : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x hx => by
    rcases hf x with ⟨y, rfl⟩
    -- ⊢ ↑f y ∈ map f (comap f S)
    simp only [mem_map, mem_comap]
    -- ⊢ ∃ y_1, ↑f y_1 ∈ S ∧ ↑f y_1 = ↑f y
    exact ⟨y, hx, rfl⟩
    -- 🎉 no goals
#align submodule.gi_map_comap Submodule.giMapComap

theorem map_comap_eq_of_surjective (p : Submodule R₂ M₂) : (p.comap f).map f = p :=
  (giMapComap hf).l_u_eq _
#align submodule.map_comap_eq_of_surjective Submodule.map_comap_eq_of_surjective

theorem map_surjective_of_surjective : Function.Surjective (map f) :=
  (giMapComap hf).l_surjective
#align submodule.map_surjective_of_surjective Submodule.map_surjective_of_surjective

theorem comap_injective_of_surjective : Function.Injective (comap f) :=
  (giMapComap hf).u_injective
#align submodule.comap_injective_of_surjective Submodule.comap_injective_of_surjective

theorem map_sup_comap_of_surjective (p q : Submodule R₂ M₂) :
    (p.comap f ⊔ q.comap f).map f = p ⊔ q :=
  (giMapComap hf).l_sup_u _ _
#align submodule.map_sup_comap_of_surjective Submodule.map_sup_comap_of_surjective

theorem map_iSup_comap_of_sujective {ι : Sort*} (S : ι → Submodule R₂ M₂) :
    (⨆ i, (S i).comap f).map f = iSup S :=
  (giMapComap hf).l_iSup_u _
#align submodule.map_supr_comap_of_sujective Submodule.map_iSup_comap_of_sujective

theorem map_inf_comap_of_surjective (p q : Submodule R₂ M₂) :
    (p.comap f ⊓ q.comap f).map f = p ⊓ q :=
  (giMapComap hf).l_inf_u _ _
#align submodule.map_inf_comap_of_surjective Submodule.map_inf_comap_of_surjective

theorem map_iInf_comap_of_surjective {ι : Sort*} (S : ι → Submodule R₂ M₂) :
    (⨅ i, (S i).comap f).map f = iInf S :=
  (giMapComap hf).l_iInf_u _
#align submodule.map_infi_comap_of_surjective Submodule.map_iInf_comap_of_surjective

theorem comap_le_comap_iff_of_surjective (p q : Submodule R₂ M₂) : p.comap f ≤ q.comap f ↔ p ≤ q :=
  (giMapComap hf).u_le_u_iff
#align submodule.comap_le_comap_iff_of_surjective Submodule.comap_le_comap_iff_of_surjective

theorem comap_strictMono_of_surjective : StrictMono (comap f) :=
  (giMapComap hf).strictMono_u
#align submodule.comap_strict_mono_of_surjective Submodule.comap_strictMono_of_surjective

end GaloisInsertion

section GaloisCoinsertion

variable [RingHomSurjective σ₁₂] {f : F} (hf : Injective f)

/-- `map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective. -/
def gciMapComap : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by
    simp [mem_comap, mem_map, forall_exists_index, and_imp]
    -- ⊢ ∀ (x_1 : M), x_1 ∈ S → ↑f x_1 = ↑f x → x ∈ S
    intro y hy hxy
    -- ⊢ x ∈ S
    rw [hf.eq_iff] at hxy
    -- ⊢ x ∈ S
    rwa [← hxy]
    -- 🎉 no goals
#align submodule.gci_map_comap Submodule.gciMapComap

theorem comap_map_eq_of_injective (p : Submodule R M) : (p.map f).comap f = p :=
  (gciMapComap hf).u_l_eq _
#align submodule.comap_map_eq_of_injective Submodule.comap_map_eq_of_injective

theorem comap_surjective_of_injective : Function.Surjective (comap f) :=
  (gciMapComap hf).u_surjective
#align submodule.comap_surjective_of_injective Submodule.comap_surjective_of_injective

theorem map_injective_of_injective : Function.Injective (map f) :=
  (gciMapComap hf).l_injective
#align submodule.map_injective_of_injective Submodule.map_injective_of_injective

theorem comap_inf_map_of_injective (p q : Submodule R M) : (p.map f ⊓ q.map f).comap f = p ⊓ q :=
  (gciMapComap hf).u_inf_l _ _
#align submodule.comap_inf_map_of_injective Submodule.comap_inf_map_of_injective

theorem comap_iInf_map_of_injective {ι : Sort*} (S : ι → Submodule R M) :
    (⨅ i, (S i).map f).comap f = iInf S :=
  (gciMapComap hf).u_iInf_l _
#align submodule.comap_infi_map_of_injective Submodule.comap_iInf_map_of_injective

theorem comap_sup_map_of_injective (p q : Submodule R M) : (p.map f ⊔ q.map f).comap f = p ⊔ q :=
  (gciMapComap hf).u_sup_l _ _
#align submodule.comap_sup_map_of_injective Submodule.comap_sup_map_of_injective

theorem comap_iSup_map_of_injective {ι : Sort*} (S : ι → Submodule R M) :
    (⨆ i, (S i).map f).comap f = iSup S :=
  (gciMapComap hf).u_iSup_l _
#align submodule.comap_supr_map_of_injective Submodule.comap_iSup_map_of_injective

theorem map_le_map_iff_of_injective (p q : Submodule R M) : p.map f ≤ q.map f ↔ p ≤ q :=
  (gciMapComap hf).l_le_l_iff
#align submodule.map_le_map_iff_of_injective Submodule.map_le_map_iff_of_injective

theorem map_strictMono_of_injective : StrictMono (map f) :=
  (gciMapComap hf).strictMono_l
#align submodule.map_strict_mono_of_injective Submodule.map_strictMono_of_injective

end GaloisCoinsertion

end SemilinearMap

section OrderIso

variable {F : Type*} [SemilinearEquivClass F σ₁₂ M M₂]

/-- A linear isomorphism induces an order isomorphism of submodules. -/
@[simps symm_apply apply]
def orderIsoMapComap (f : F) : Submodule R M ≃o Submodule R₂ M₂
    where
  toFun := map f
  invFun := comap f
  left_inv := comap_map_eq_of_injective (EquivLike.injective f)
  right_inv := map_comap_eq_of_surjective (EquivLike.surjective f)
  map_rel_iff' := map_le_map_iff_of_injective (EquivLike.injective f) _ _
#align submodule.order_iso_map_comap Submodule.orderIsoMapComap

end OrderIso

variable {F : Type*} [sc : SemilinearMapClass F σ₁₂ M M₂]

--TODO(Mario): is there a way to prove this from order properties?
theorem map_inf_eq_map_inf_comap [RingHomSurjective σ₁₂] {f : F} {p : Submodule R M}
    {p' : Submodule R₂ M₂} : map f p ⊓ p' = map f (p ⊓ comap f p') :=
  le_antisymm (by rintro _ ⟨⟨x, h₁, rfl⟩, h₂⟩; exact ⟨_, ⟨h₁, h₂⟩, rfl⟩)
                  -- ⊢ ↑f x ∈ map f (p ⊓ comap f p')
                                               -- 🎉 no goals
    (le_inf (map_mono inf_le_left) (map_le_iff_le_comap.2 inf_le_right))
#align submodule.map_inf_eq_map_inf_comap Submodule.map_inf_eq_map_inf_comap

theorem map_comap_subtype : map p.subtype (comap p.subtype p') = p ⊓ p' :=
  ext fun x => ⟨by rintro ⟨⟨_, h₁⟩, h₂, rfl⟩; exact ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨⟨_, h₁⟩, h₂, rfl⟩⟩
                   -- ⊢ ↑(Submodule.subtype p) { val := val✝, property := h₁ } ∈ p ⊓ p'
                                              -- 🎉 no goals
#align submodule.map_comap_subtype Submodule.map_comap_subtype

theorem eq_zero_of_bot_submodule : ∀ b : (⊥ : Submodule R M), b = 0
  | ⟨b', hb⟩ => Subtype.eq <| show b' = 0 from (mem_bot R).1 hb
#align submodule.eq_zero_of_bot_submodule Submodule.eq_zero_of_bot_submodule

/-- The infimum of a family of invariant submodule of an endomorphism is also an invariant
submodule. -/
theorem _root_.LinearMap.iInf_invariant {σ : R →+* R} [RingHomSurjective σ] {ι : Sort*}
    (f : M →ₛₗ[σ] M) {p : ι → Submodule R M} (hf : ∀ i, ∀ v ∈ p i, f v ∈ p i) :
    ∀ v ∈ iInf p, f v ∈ iInf p := by
  have : ∀ i, (p i).map f ≤ p i := by
    rintro i - ⟨v, hv, rfl⟩
    exact hf i v hv
  suffices (iInf p).map f ≤ iInf p by exact fun v hv => this ⟨v, hv, rfl⟩
  -- ⊢ map f (iInf p) ≤ iInf p
  exact le_iInf fun i => (Submodule.map_mono (iInf_le p i)).trans (this i)
  -- 🎉 no goals
#align linear_map.infi_invariant LinearMap.iInf_invariant

end AddCommMonoid
section AddCommGroup

variable [Ring R] [AddCommGroup M] [Module R M] (p : Submodule R M)

variable [AddCommGroup M₂] [Module R M₂]

-- Porting note: inferInstance works here only if one replaces [Ring R] with [Semiring R]. Why?
example : AddCommGroup (M →ₗ[R] M₂) := inferInstance

-- See `neg_coe_set`
theorem neg_coe : -(p : Set M) = p :=
  Set.ext fun _ => p.neg_mem_iff
#align submodule.neg_coe Submodule.neg_coe

@[simp]
protected theorem map_neg (f : M →ₗ[R] M₂) : map (-f) p = map f p :=
  ext fun _ =>
    ⟨fun ⟨x, hx, hy⟩ => hy ▸ ⟨-x, show -x ∈ p from neg_mem hx, map_neg f x⟩, fun ⟨x, hx, hy⟩ =>
      hy ▸ ⟨-x, show -x ∈ p from neg_mem hx, (map_neg (-f) _).trans (neg_neg (f x))⟩⟩
#align submodule.map_neg Submodule.map_neg

end AddCommGroup

end Submodule

namespace Submodule

variable [Semifield K]
variable [AddCommMonoid V] [Module K V]
variable [AddCommMonoid V₂] [Module K V₂]

theorem comap_smul (f : V →ₗ[K] V₂) (p : Submodule K V₂) (a : K) (h : a ≠ 0) :
    p.comap (a • f) = p.comap f := by
  ext b; simp only [Submodule.mem_comap, p.smul_mem_iff h, LinearMap.smul_apply]
  -- ⊢ b ∈ comap (a • f) p ↔ b ∈ comap f p
         -- 🎉 no goals
#align submodule.comap_smul Submodule.comap_smul

protected theorem map_smul (f : V →ₗ[K] V₂) (p : Submodule K V) (a : K) (h : a ≠ 0) :
    p.map (a • f) = p.map f :=
  le_antisymm (by rw [map_le_iff_le_comap, comap_smul f _ a h, ← map_le_iff_le_comap])
                  -- 🎉 no goals
    (by rw [map_le_iff_le_comap, ← comap_smul f _ a h, ← map_le_iff_le_comap])
        -- 🎉 no goals
#align submodule.map_smul Submodule.map_smul

-- Porting note: `⨅ h : a ≠ 0, p.comap f` gets an `unusedVariables` lint, but
-- `⨅ _ : a ≠ 0, p.comap f` is ill-formed. So, this is written `iInf (fun _ : a ≠ 0 => p.comap f)`.
theorem comap_smul' (f : V →ₗ[K] V₂) (p : Submodule K V₂) (a : K) :
    p.comap (a • f) = iInf (fun _ : a ≠ 0 => p.comap f) := by
  classical by_cases h : a = 0 <;> simp [h, comap_smul]
  -- 🎉 no goals
#align submodule.comap_smul' Submodule.comap_smul'

-- Porting note: Idem.
theorem map_smul' (f : V →ₗ[K] V₂) (p : Submodule K V) (a : K) :
    p.map (a • f) = iSup (fun _ : a ≠ 0 => p.map f) := by
  classical by_cases h : a = 0 <;> simp [h, Submodule.map_smul]
  -- 🎉 no goals
#align submodule.map_smul' Submodule.map_smul'

end Submodule

/-! ### Properties of linear maps -/


namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

open Submodule

section Finsupp

variable {γ : Type*} [Zero γ]

@[simp]
theorem map_finsupp_sum (f : M →ₛₗ[σ₁₂] M₂) {t : ι →₀ γ} {g : ι → γ → M} :
    f (t.sum g) = t.sum fun i d => f (g i d) :=
  f.map_sum
#align linear_map.map_finsupp_sum LinearMap.map_finsupp_sum

theorem coe_finsupp_sum (t : ι →₀ γ) (g : ι → γ → M →ₛₗ[σ₁₂] M₂) :
    ⇑(t.sum g) = t.sum fun i d => g i d := rfl
#align linear_map.coe_finsupp_sum LinearMap.coe_finsupp_sum

@[simp]
theorem finsupp_sum_apply (t : ι →₀ γ) (g : ι → γ → M →ₛₗ[σ₁₂] M₂) (b : M) :
    (t.sum g) b = t.sum fun i d => g i d b :=
  sum_apply _ _ _
#align linear_map.finsupp_sum_apply LinearMap.finsupp_sum_apply

end Finsupp

section DFinsupp

open DFinsupp

variable {γ : ι → Type*} [DecidableEq ι]

section Sum

variable [∀ i, Zero (γ i)] [∀ (i) (x : γ i), Decidable (x ≠ 0)]

@[simp]
theorem map_dfinsupp_sum (f : M →ₛₗ[σ₁₂] M₂) {t : Π₀ i, γ i} {g : ∀ i, γ i → M} :
    f (t.sum g) = t.sum fun i d => f (g i d) :=
  f.map_sum
#align linear_map.map_dfinsupp_sum LinearMap.map_dfinsupp_sum

theorem coe_dfinsupp_sum (t : Π₀ i, γ i) (g : ∀ i, γ i → M →ₛₗ[σ₁₂] M₂) :
    ⇑(t.sum g) = t.sum fun i d => g i d := rfl
#align linear_map.coe_dfinsupp_sum LinearMap.coe_dfinsupp_sum

@[simp]
theorem dfinsupp_sum_apply (t : Π₀ i, γ i) (g : ∀ i, γ i → M →ₛₗ[σ₁₂] M₂) (b : M) :
    (t.sum g) b = t.sum fun i d => g i d b :=
  sum_apply _ _ _
#align linear_map.dfinsupp_sum_apply LinearMap.dfinsupp_sum_apply

end Sum

section SumAddHom

variable [∀ i, AddZeroClass (γ i)]

@[simp]
theorem map_dfinsupp_sumAddHom (f : M →ₛₗ[σ₁₂] M₂) {t : Π₀ i, γ i} {g : ∀ i, γ i →+ M} :
    f (sumAddHom g t) = sumAddHom (fun i => f.toAddMonoidHom.comp (g i)) t :=
  f.toAddMonoidHom.map_dfinsupp_sumAddHom _ _
#align linear_map.map_dfinsupp_sum_add_hom LinearMap.map_dfinsupp_sumAddHom

end SumAddHom

end DFinsupp

variable {σ₂₁ : R₂ →+* R} {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}

variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

theorem map_codRestrict [RingHomSurjective σ₂₁] (p : Submodule R M) (f : M₂ →ₛₗ[σ₂₁] M) (h p') :
    Submodule.map (codRestrict p f h) p' = comap p.subtype (p'.map f) :=
  Submodule.ext fun ⟨x, hx⟩ => by simp [Subtype.ext_iff_val]
                                  -- 🎉 no goals
#align linear_map.map_cod_restrict LinearMap.map_codRestrict

theorem comap_codRestrict (p : Submodule R M) (f : M₂ →ₛₗ[σ₂₁] M) (hf p') :
    Submodule.comap (codRestrict p f hf) p' = Submodule.comap f (map p.subtype p') :=
  Submodule.ext fun x => ⟨fun h => ⟨⟨_, hf x⟩, h, rfl⟩, by rintro ⟨⟨_, _⟩, h, ⟨⟩⟩; exact h⟩
                                                           -- ⊢ x ∈ comap (codRestrict p f hf) p'
                                                                                   -- 🎉 no goals
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
  -- ⊢ x✝ ∈ range f ↔ x✝ ∈ map f ⊤
  simp
  -- 🎉 no goals
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
  -- 🎉 no goals
#align linear_map.range_eq_top LinearMap.range_eq_top

theorem range_le_iff_comap [RingHomSurjective τ₁₂] {f : F} {p : Submodule R₂ M₂} :
    range f ≤ p ↔ comap f p = ⊤ := by rw [range_eq_map, map_le_iff_le_comap, eq_top_iff]
                                      -- 🎉 no goals
#align linear_map.range_le_iff_comap LinearMap.range_le_iff_comap

theorem map_le_range [RingHomSurjective τ₁₂] {f : F} {p : Submodule R M} : map f p ≤ range f :=
  SetLike.coe_mono (Set.image_subset_range f p)
#align linear_map.map_le_range LinearMap.map_le_range

@[simp]
theorem range_neg {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*} [Semiring R] [Ring R₂]
    [AddCommMonoid M] [AddCommGroup M₂] [Module R M] [Module R₂ M₂] {τ₁₂ : R →+* R₂}
    [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : LinearMap.range (-f) = LinearMap.range f := by
  change range ((-LinearMap.id : M₂ →ₗ[R₂] M₂).comp f) = _
  -- ⊢ range (comp (-id) f) = range f
  rw [range_comp, Submodule.map_neg, Submodule.map_id]
  -- 🎉 no goals
#align linear_map.range_neg LinearMap.range_neg

/-- A linear map version of `toAddMonoidHom.eqLocus` -/
def eqLocus (f g : F) : Submodule R M :=
  { (f : M →+ M₂).eqLocusM g with
    carrier := { x | f x = g x }
    smul_mem' := fun {r} {x} (hx : _ = _) => show _ = _ by
      simpa only [map_smulₛₗ] using congr_arg ((· • ·) (τ₁₂ r)) hx }
      -- 🎉 no goals
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
    -- 🎉 no goals

@[simp]
theorem eqLocus_same (f : F) : eqLocus f f = ⊤ := eqLocus_eq_top.2 rfl
#align linear_map.eq_locus_same LinearMap.eqLocus_same

theorem le_eqLocus {f g : F} {S : Submodule R M} : S ≤ eqLocus f g ↔ Set.EqOn f g S := Iff.rfl

theorem eqOn_sup {f g : F} {S T : Submodule R M} (hS : Set.EqOn f g S) (hT : Set.EqOn f g T) :
    Set.EqOn f g ↑(S ⊔ T) := by
  rw [← le_eqLocus] at hS hT ⊢
  -- ⊢ S ⊔ T ≤ eqLocus f g
  exact sup_le hS hT
  -- 🎉 no goals

theorem ext_on_codisjoint {f g : F} {S T : Submodule R M} (hST : Codisjoint S T)
    (hS : Set.EqOn f g S) (hT : Set.EqOn f g T) : f = g :=
  FunLike.ext _ _ fun _ ↦ eqOn_sup hS hT <| hST.eq_top.symm ▸ trivial

end

/-- The decreasing sequence of submodules consisting of the ranges of the iterates of a linear map.
-/
@[simps]
def iterateRange (f : M →ₗ[R] M) : ℕ →o (Submodule R M)ᵒᵈ :=
  ⟨fun n => LinearMap.range (f ^ n), fun n m w x h => by
    obtain ⟨c, rfl⟩ := le_iff_exists_add.mp w
    -- ⊢ x ∈ (fun n => range (f ^ n)) n
    rw [LinearMap.mem_range] at h
    -- ⊢ x ∈ (fun n => range (f ^ n)) n
    obtain ⟨m, rfl⟩ := h
    -- ⊢ ↑(f ^ (n + c)) m ∈ (fun n => range (f ^ n)) n
    rw [LinearMap.mem_range]
    -- ⊢ ∃ y, ↑(f ^ n) y = ↑(f ^ (n + c)) m
    use (f ^ c) m
    -- ⊢ ↑(f ^ n) (↑(f ^ c) m) = ↑(f ^ (n + c)) m
    rw [pow_add, LinearMap.mul_apply]⟩
    -- 🎉 no goals
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
                                                 -- ⊢ ker f ≤ comap f (ker g)
                                                                -- 🎉 no goals
#align linear_map.ker_le_ker_comp LinearMap.ker_le_ker_comp

theorem disjoint_ker {f : F} {p : Submodule R M} : Disjoint p (ker f) ↔ ∀ x ∈ p, f x = 0 → x = 0 :=
  by simp [disjoint_def]
     -- 🎉 no goals
#align linear_map.disjoint_ker LinearMap.disjoint_ker

theorem ker_eq_bot' {f : F} : ker f = ⊥ ↔ ∀ m, f m = 0 → m = 0 := by
  simpa [disjoint_iff_inf_le] using @disjoint_ker _ _ _ _ _ _ _ _ _ _ _ _ _ f ⊤
  -- 🎉 no goals
#align linear_map.ker_eq_bot' LinearMap.ker_eq_bot'

theorem ker_eq_bot_of_inverse {τ₂₁ : R₂ →+* R} [RingHomInvPair τ₁₂ τ₂₁] {f : M →ₛₗ[τ₁₂] M₂}
    {g : M₂ →ₛₗ[τ₂₁] M} (h : (g.comp f : M →ₗ[R] M) = id) : ker f = ⊥ :=
  ker_eq_bot'.2 fun m hm => by rw [← id_apply (R := R) m, ← h, comp_apply, hm, g.map_zero]
                               -- 🎉 no goals
#align linear_map.ker_eq_bot_of_inverse LinearMap.ker_eq_bot_of_inverse

theorem le_ker_iff_map [RingHomSurjective τ₁₂] {f : F} {p : Submodule R M} :
    p ≤ ker f ↔ map f p = ⊥ := by rw [ker, eq_bot_iff, map_le_iff_le_comap]
                                  -- 🎉 no goals
#align linear_map.le_ker_iff_map LinearMap.le_ker_iff_map

theorem ker_codRestrict {τ₂₁ : R₂ →+* R} (p : Submodule R M) (f : M₂ →ₛₗ[τ₂₁] M) (hf) :
    ker (codRestrict p f hf) = ker f := by rw [ker, comap_codRestrict, Submodule.map_bot]; rfl
                                           -- ⊢ comap f ⊥ = ker f
                                                                                           -- 🎉 no goals
#align linear_map.ker_cod_restrict LinearMap.ker_codRestrict

theorem range_codRestrict {τ₂₁ : R₂ →+* R} [RingHomSurjective τ₂₁] (p : Submodule R M)
    (f : M₂ →ₛₗ[τ₂₁] M) (hf) :
    range (codRestrict p f hf) = comap p.subtype (LinearMap.range f) := by
  simpa only [range_eq_map] using map_codRestrict _ _ _ _
  -- 🎉 no goals
#align linear_map.range_cod_restrict LinearMap.range_codRestrict

theorem ker_restrict [AddCommMonoid M₁] [Module R M₁] {p : Submodule R M} {q : Submodule R M₁}
    {f : M →ₗ[R] M₁} (hf : ∀ x : M, x ∈ p → f x ∈ q) :
    ker (f.restrict hf) = LinearMap.ker (f.domRestrict p) := by
  rw [restrict_eq_codRestrict_domRestrict, ker_codRestrict]
  -- 🎉 no goals
#align linear_map.ker_restrict LinearMap.ker_restrict

theorem _root_.Submodule.map_comap_eq [RingHomSurjective τ₁₂] (f : F) (q : Submodule R₂ M₂) :
    map f (comap f q) = range f ⊓ q :=
  le_antisymm (le_inf map_le_range (map_comap_le _ _)) <| by
    rintro _ ⟨⟨x, _, rfl⟩, hx⟩; exact ⟨x, hx, rfl⟩
    -- ⊢ ↑f x ∈ map f (comap f q)
                                -- 🎉 no goals
#align submodule.map_comap_eq Submodule.map_comap_eq

theorem _root_.Submodule.map_comap_eq_self [RingHomSurjective τ₁₂] {f : F} {q : Submodule R₂ M₂}
    (h : q ≤ range f) : map f (comap f q) = q := by rwa [Submodule.map_comap_eq, inf_eq_right]
                                                    -- 🎉 no goals
#align submodule.map_comap_eq_self Submodule.map_comap_eq_self

@[simp]
theorem ker_zero : ker (0 : M →ₛₗ[τ₁₂] M₂) = ⊤ :=
  eq_top_iff'.2 fun x => by simp
                            -- 🎉 no goals
#align linear_map.ker_zero LinearMap.ker_zero

@[simp]
theorem range_zero [RingHomSurjective τ₁₂] : range (0 : M →ₛₗ[τ₁₂] M₂) = ⊥ := by
  simpa only [range_eq_map] using Submodule.map_zero _
  -- 🎉 no goals
#align linear_map.range_zero LinearMap.range_zero

theorem ker_eq_top {f : M →ₛₗ[τ₁₂] M₂} : ker f = ⊤ ↔ f = 0 :=
  ⟨fun h => ext fun _ => mem_ker.1 <| h.symm ▸ trivial, fun h => h.symm ▸ ker_zero⟩
#align linear_map.ker_eq_top LinearMap.ker_eq_top

section

variable [RingHomSurjective τ₁₂]

theorem range_le_bot_iff (f : M →ₛₗ[τ₁₂] M₂) : range f ≤ ⊥ ↔ f = 0 := by
  rw [range_le_iff_comap]; exact ker_eq_top
  -- ⊢ comap f ⊥ = ⊤ ↔ f = 0
                           -- 🎉 no goals
#align linear_map.range_le_bot_iff LinearMap.range_le_bot_iff

theorem range_eq_bot {f : M →ₛₗ[τ₁₂] M₂} : range f = ⊥ ↔ f = 0 := by
  rw [← range_le_bot_iff, le_bot_iff]
  -- 🎉 no goals
#align linear_map.range_eq_bot LinearMap.range_eq_bot

theorem range_le_ker_iff {f : M →ₛₗ[τ₁₂] M₂} {g : M₂ →ₛₗ[τ₂₃] M₃} :
    range f ≤ ker g ↔ (g.comp f : M →ₛₗ[τ₁₃] M₃) = 0 :=
  ⟨fun h => ker_eq_top.1 <| eq_top_iff'.2 fun x => h <| ⟨_, rfl⟩, fun h x hx =>
    mem_ker.2 <| Exists.elim hx fun y hy => by rw [← hy, ← comp_apply, h, zero_apply]⟩
                                               -- 🎉 no goals
#align linear_map.range_le_ker_iff LinearMap.range_le_ker_iff

theorem comap_le_comap_iff {f : F} (hf : range f = ⊤) {p p'} : comap f p ≤ comap f p' ↔ p ≤ p' :=
  ⟨fun H x hx => by rcases range_eq_top.1 hf x with ⟨y, hy, rfl⟩; exact H hx, comap_mono⟩
                    -- ⊢ ↑f y ∈ p'
                                                                  -- 🎉 no goals
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
  -- Porting note: was simpa? [disjoint_iff_inf_le]
  rw [disjoint_iff_inf_le, top_inf_eq, le_bot_iff] at this
  -- ⊢ ker f = ⊥
  assumption
  -- 🎉 no goals
#align linear_map.ker_eq_bot_of_injective LinearMap.ker_eq_bot_of_injective

/-- The increasing sequence of submodules consisting of the kernels of the iterates of a linear map.
-/
@[simps]
def iterateKer (f : M →ₗ[R] M) : ℕ →o Submodule R M :=
  ⟨fun n => ker (f ^ n), fun n m w x h => by
    obtain ⟨c, rfl⟩ := le_iff_exists_add.mp w
    -- ⊢ x ∈ (fun n => ker (f ^ n)) (n + c)
    rw [LinearMap.mem_ker] at h
    -- ⊢ x ∈ (fun n => ker (f ^ n)) (n + c)
    rw [LinearMap.mem_ker, add_comm, pow_add, LinearMap.mul_apply, h, LinearMap.map_zero]⟩
    -- 🎉 no goals
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
                                                                -- 🎉 no goals
#align linear_map.sub_mem_ker_iff LinearMap.sub_mem_ker_iff

theorem disjoint_ker' {p : Submodule R M} :
    Disjoint p (ker f) ↔ ∀ (x) (_ : x ∈ p) (y) (_ : y ∈ p), f x = f y → x = y :=
  disjoint_ker.trans
    ⟨fun H x hx y hy h => eq_of_sub_eq_zero <| H _ (sub_mem hx hy) (by simp [h]), fun H x h₁ h₂ =>
                                                                       -- 🎉 no goals
      H x h₁ 0 (zero_mem _) (by simpa using h₂)⟩
                                -- 🎉 no goals
#align linear_map.disjoint_ker' LinearMap.disjoint_ker'

theorem injOn_of_disjoint_ker {p : Submodule R M} {s : Set M} (h : s ⊆ p)
    (hd : Disjoint p (ker f)) : Set.InjOn f s := fun _ hx _ hy =>
  disjoint_ker'.1 hd _ (h hx) _ (h hy)
#align linear_map.inj_on_of_disjoint_ker LinearMap.injOn_of_disjoint_ker

variable (F)

theorem _root_.LinearMapClass.ker_eq_bot : ker f = ⊥ ↔ Injective f := by
  simpa [disjoint_iff_inf_le] using @disjoint_ker' _ _ _ _ _ _ _ _ _ _ _ _ _ f ⊤
  -- 🎉 no goals
#align linear_map_class.ker_eq_bot LinearMapClass.ker_eq_bot

variable {F}

theorem ker_eq_bot {f : M →ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Injective f :=
  LinearMapClass.ker_eq_bot _
#align linear_map.ker_eq_bot LinearMap.ker_eq_bot

theorem ker_le_iff [RingHomSurjective τ₁₂] {p : Submodule R M} :
    ker f ≤ p ↔ ∃ y ∈ range f, f ⁻¹' {y} ⊆ p := by
  constructor
  -- ⊢ ker f ≤ p → ∃ y, y ∈ range f ∧ ↑f ⁻¹' {y} ⊆ ↑p
  · intro h
    -- ⊢ ∃ y, y ∈ range f ∧ ↑f ⁻¹' {y} ⊆ ↑p
    use 0
    -- ⊢ 0 ∈ range f ∧ ↑f ⁻¹' {0} ⊆ ↑p
    rw [← SetLike.mem_coe, range_coe]
    -- ⊢ 0 ∈ Set.range ↑f ∧ ↑f ⁻¹' {0} ⊆ ↑p
    exact ⟨⟨0, map_zero f⟩, h⟩
    -- 🎉 no goals
  · rintro ⟨y, h₁, h₂⟩
    -- ⊢ ker f ≤ p
    rw [SetLike.le_def]
    -- ⊢ ∀ ⦃x : M⦄, x ∈ ker f → x ∈ p
    intro z hz
    -- ⊢ z ∈ p
    simp only [mem_ker, SetLike.mem_coe] at hz
    -- ⊢ z ∈ p
    rw [← SetLike.mem_coe, range_coe, Set.mem_range] at h₁
    -- ⊢ z ∈ p
    obtain ⟨x, hx⟩ := h₁
    -- ⊢ z ∈ p
    have hx' : x ∈ p := h₂ hx
    -- ⊢ z ∈ p
    have hxz : z + x ∈ p := by
      apply h₂
      simp [hx, hz]
    suffices z + x - x ∈ p by simpa only [this, add_sub_cancel]
    -- ⊢ z + x - x ∈ p
    exact p.sub_mem hxz hx'
    -- 🎉 no goals
#align linear_map.ker_le_iff LinearMap.ker_le_iff

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
  -- 🎉 no goals
#align linear_map.range_smul LinearMap.range_smul

theorem range_smul' (f : V →ₗ[K] V₂) (a : K) :
    range (a • f) = ⨆ _ : a ≠ 0, range f := by
  simpa only [range_eq_map] using Submodule.map_smul' f _ a
  -- 🎉 no goals
#align linear_map.range_smul' LinearMap.range_smul'

end Semifield

end LinearMap

namespace IsLinearMap

theorem isLinearMap_add [Semiring R] [AddCommMonoid M] [Module R M] :
    IsLinearMap R fun x : M × M => x.1 + x.2 := by
  apply IsLinearMap.mk
  -- ⊢ ∀ (x y : M × M), (x + y).fst + (x + y).snd = x.fst + x.snd + (y.fst + y.snd)
  · intro x y
    -- ⊢ (x + y).fst + (x + y).snd = x.fst + x.snd + (y.fst + y.snd)
    simp only [Prod.fst_add, Prod.snd_add]
    -- ⊢ x.fst + y.fst + (x.snd + y.snd) = x.fst + x.snd + (y.fst + y.snd)
    abel -- Porting Note: was cc
    -- 🎉 no goals
    -- 🎉 no goals
  · intro x y
    -- ⊢ (x • y).fst + (x • y).snd = x • (y.fst + y.snd)
    simp [smul_add]
    -- 🎉 no goals
#align is_linear_map.is_linear_map_add IsLinearMap.isLinearMap_add

theorem isLinearMap_sub {R M : Type*} [Semiring R] [AddCommGroup M] [Module R M] :
    IsLinearMap R fun x : M × M => x.1 - x.2 := by
  apply IsLinearMap.mk
  -- ⊢ ∀ (x y : M × M), (x + y).fst - (x + y).snd = x.fst - x.snd + (y.fst - y.snd)
  · intro x y
    -- ⊢ (x + y).fst - (x + y).snd = x.fst - x.snd + (y.fst - y.snd)
    -- Porting note: was `simp [add_comm, add_left_comm, sub_eq_add_neg]`
    rw [Prod.fst_add, Prod.snd_add]
    -- ⊢ x.fst + y.fst - (x.snd + y.snd) = x.fst - x.snd + (y.fst - y.snd)
    abel
    -- 🎉 no goals
    -- 🎉 no goals
  · intro x y
    -- ⊢ (x • y).fst - (x • y).snd = x • (y.fst - y.snd)
    simp [smul_sub]
    -- 🎉 no goals
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
                                                  -- 🎉 no goals
#align submodule.range_subtype Submodule.range_subtype

theorem map_subtype_le (p' : Submodule R p) : map p.subtype p' ≤ p := by
  simpa using (map_le_range : map p.subtype p' ≤ range p.subtype)
  -- 🎉 no goals
#align submodule.map_subtype_le Submodule.map_subtype_le

/-- Under the canonical linear map from a submodule `p` to the ambient space `M`, the image of the
maximal submodule of `p` is just `p `. -/
-- @[simp] -- Porting note: simp can prove this
theorem map_subtype_top : map p.subtype (⊤ : Submodule R p) = p := by simp
                                                                      -- 🎉 no goals
#align submodule.map_subtype_top Submodule.map_subtype_top

@[simp]
theorem comap_subtype_eq_top {p p' : Submodule R M} : comap p.subtype p' = ⊤ ↔ p ≤ p' :=
  eq_top_iff.trans <| map_le_iff_le_comap.symm.trans <| by rw [map_subtype_top]
                                                           -- 🎉 no goals
#align submodule.comap_subtype_eq_top Submodule.comap_subtype_eq_top

@[simp]
theorem comap_subtype_self : comap p.subtype p = ⊤ :=
  comap_subtype_eq_top.2 le_rfl
#align submodule.comap_subtype_self Submodule.comap_subtype_self

@[simp]
theorem ker_ofLe (p p' : Submodule R M) (h : p ≤ p') : ker (ofLe h) = ⊥ := by
  rw [ofLe, ker_codRestrict, ker_subtype]
  -- 🎉 no goals
#align submodule.ker_of_le Submodule.ker_ofLe

theorem range_ofLe (p q : Submodule R M) (h : p ≤ q) : range (ofLe h) = comap q.subtype p := by
  rw [← map_top, ofLe, LinearMap.map_codRestrict, map_top, range_subtype]
  -- 🎉 no goals
#align submodule.range_of_le Submodule.range_ofLe

@[simp]
theorem map_subtype_range_ofLe {p p' : Submodule R M} (h : p ≤ p') :
    map p'.subtype (range $ ofLe h) = p := by simp [range_ofLe, map_comap_eq, h]
                                              -- 🎉 no goals
#align submodule.map_subtype_range_of_le Submodule.map_subtype_range_ofLe

theorem disjoint_iff_comap_eq_bot {p q : Submodule R M} : Disjoint p q ↔ comap p.subtype q = ⊥ := by
  rw [← (map_injective_of_injective (show Injective p.subtype from Subtype.coe_injective)).eq_iff,
    map_comap_subtype, map_bot, disjoint_iff]
#align submodule.disjoint_iff_comap_eq_bot Submodule.disjoint_iff_comap_eq_bot

/-- If `N ⊆ M` then submodules of `N` are the same as submodules of `M` contained in `N` -/
def MapSubtype.relIso : Submodule R p ≃o { p' : Submodule R M // p' ≤ p } where
  toFun p' := ⟨map p.subtype p', map_subtype_le p _⟩
  invFun q := comap p.subtype q
  left_inv p' := comap_map_eq_of_injective (by exact Subtype.val_injective) p'
                                               -- 🎉 no goals
  right_inv := fun ⟨q, hq⟩ => Subtype.ext_val <| by simp [map_comap_subtype p, inf_of_le_right hq]
                                                    -- 🎉 no goals
  map_rel_iff' {p₁ p₂} := Subtype.coe_le_coe.symm.trans $ by
    dsimp
    -- ⊢ map (Submodule.subtype p) p₁ ≤ map (Submodule.subtype p) p₂ ↔ p₁ ≤ p₂
    rw [map_le_iff_le_comap,
      comap_map_eq_of_injective (show Injective p.subtype from Subtype.coe_injective) p₂]
#align submodule.map_subtype.rel_iso Submodule.MapSubtype.relIso

/-- If `p ⊆ M` is a submodule, the ordering of submodules of `p` is embedded in the ordering of
submodules of `M`. -/
def MapSubtype.orderEmbedding : Submodule R p ↪o Submodule R M :=
  (RelIso.toRelEmbedding <| MapSubtype.relIso p).trans $
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
  -- ⊢ ker f = ⊥
  rw [← Submodule.range_subtype (ker f),
    ← h 0 f.ker.subtype (Eq.trans h₁ (comp_ker_subtype f).symm)]
  exact range_zero
  -- 🎉 no goals
#align linear_map.ker_eq_bot_of_cancel LinearMap.ker_eq_bot_of_cancel

theorem range_comp_of_range_eq_top [RingHomSurjective τ₁₂] [RingHomSurjective τ₂₃]
    [RingHomSurjective τ₁₃] {f : M →ₛₗ[τ₁₂] M₂} (g : M₂ →ₛₗ[τ₂₃] M₃) (hf : range f = ⊤) :
    range (g.comp f : M →ₛₗ[τ₁₃] M₃) = range g := by rw [range_comp, hf, Submodule.map_top]
                                                     -- 🎉 no goals
#align linear_map.range_comp_of_range_eq_top LinearMap.range_comp_of_range_eq_top

theorem ker_comp_of_ker_eq_bot (f : M →ₛₗ[τ₁₂] M₂) {g : M₂ →ₛₗ[τ₂₃] M₃} (hg : ker g = ⊥) :
    ker (g.comp f : M →ₛₗ[τ₁₃] M₃) = ker f := by rw [ker_comp, hg, Submodule.comap_bot]
                                                 -- 🎉 no goals
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
    x ∈ ϕ.submoduleImage N ↔ ∃ (y : _) (yO : y ∈ O) (_ : y ∈ N), ϕ ⟨y, yO⟩ = x := by
  refine' Submodule.mem_map.trans ⟨_, _⟩ <;> simp_rw [Submodule.mem_comap]
  -- ⊢ (∃ y, y ∈ Submodule.comap (Submodule.subtype O) N ∧ ↑ϕ y = x) → ∃ y yO x_1,  …
                                             -- ⊢ (∃ y, ↑(Submodule.subtype O) y ∈ N ∧ ↑ϕ y = x) → ∃ y h h_1, ↑ϕ { val := y, p …
                                             -- ⊢ (∃ y h h_1, ↑ϕ { val := y, property := (_ : y ∈ O) } = x) → ∃ y, ↑(Submodule …
  · rintro ⟨⟨y, yO⟩, yN : y ∈ N, h⟩
    -- ⊢ ∃ y h h_1, ↑ϕ { val := y, property := (_ : y ∈ O) } = x
    exact ⟨y, yO, yN, h⟩
    -- 🎉 no goals
  · rintro ⟨y, yO, yN, h⟩
    -- ⊢ ∃ y, ↑(Submodule.subtype O) y ∈ N ∧ ↑ϕ y = x
    exact ⟨⟨y, yO⟩, yN, h⟩
    -- 🎉 no goals
#align linear_map.mem_submodule_image LinearMap.mem_submoduleImage

theorem mem_submoduleImage_of_le {M' : Type*} [AddCommMonoid M'] [Module R M'] {O : Submodule R M}
    {ϕ : O →ₗ[R] M'} {N : Submodule R M} (hNO : N ≤ O) {x : M'} :
    x ∈ ϕ.submoduleImage N ↔ ∃ (y : _) (yN : y ∈ N), ϕ ⟨y, hNO yN⟩ = x := by
  refine' mem_submoduleImage.trans ⟨_, _⟩
  -- ⊢ (∃ y yO x_1, ↑ϕ { val := y, property := yO } = x) → ∃ y yN, ↑ϕ { val := y, p …
  · rintro ⟨y, yO, yN, h⟩
    -- ⊢ ∃ y yN, ↑ϕ { val := y, property := (_ : y ∈ O) } = x
    exact ⟨y, yN, h⟩
    -- 🎉 no goals
  · rintro ⟨y, yN, h⟩
    -- ⊢ ∃ y yO x_1, ↑ϕ { val := y, property := yO } = x
    exact ⟨y, hNO yN, yN, h⟩
    -- 🎉 no goals
#align linear_map.mem_submodule_image_of_le LinearMap.mem_submoduleImage_of_le

theorem submoduleImage_apply_ofLe {M' : Type*} [AddCommGroup M'] [Module R M'] {O : Submodule R M}
    (ϕ : O →ₗ[R] M') (N : Submodule R M) (hNO : N ≤ O) :
    ϕ.submoduleImage N = range (ϕ.comp (Submodule.ofLe hNO)) := by
  rw [submoduleImage, range_comp, Submodule.range_ofLe]
  -- 🎉 no goals
#align linear_map.submodule_image_apply_of_le LinearMap.submoduleImage_apply_ofLe

end Image

end Semiring

end LinearMap

@[simp]
theorem LinearMap.range_rangeRestrict [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [Module R M]
    [Module R M₂] (f : M →ₗ[R] M₂) : range f.rangeRestrict = ⊤ := by simp [f.range_codRestrict _]
                                                                     -- 🎉 no goals
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
instance : Unique (M ≃ₛₗ[σ₁₂] M₂)
    where
  uniq _ := toLinearMap_injective (Subsingleton.elim _ _)
  default := 0


end Module

instance uniqueOfSubsingleton [Subsingleton R] [Subsingleton R₂] : Unique (M ≃ₛₗ[σ₁₂] M₂) := by
  haveI := Module.subsingleton R M
  -- ⊢ Unique (M ≃ₛₗ[σ₁₂] M₂)
  haveI := Module.subsingleton R₂ M₂
  -- ⊢ Unique (M ≃ₛₗ[σ₁₂] M₂)
  infer_instance
  -- 🎉 no goals
#align linear_equiv.unique_of_subsingleton LinearEquiv.uniqueOfSubsingleton

end Subsingleton

section

variable [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring R₄]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]

variable {module_M : Module R M} {module_M₂ : Module R₂ M₂}

variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}

variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}

variable (e e' : M ≃ₛₗ[σ₁₂] M₂)

@[simp]
theorem map_sum {s : Finset ι} (u : ι → M) : e (∑ i in s, u i) = ∑ i in s, e (u i) :=
  e.toLinearMap.map_sum
#align linear_equiv.map_sum LinearEquiv.map_sum

theorem map_eq_comap {p : Submodule R M} :
    (p.map (e : M →ₛₗ[σ₁₂] M₂) : Submodule R₂ M₂) = p.comap (e.symm : M₂ →ₛₗ[σ₂₁] M) :=
  SetLike.coe_injective <| by simp [e.image_eq_preimage]
                              -- 🎉 no goals
#align linear_equiv.map_eq_comap LinearEquiv.map_eq_comap

/-- A linear equivalence of two modules restricts to a linear equivalence from any submodule
`p` of the domain onto the image of that submodule.

This is the linear version of `AddEquiv.submonoidMap` and `AddEquiv.subgroupMap`.

This is `LinearEquiv.ofSubmodule'` but with `map` on the right instead of `comap` on the left. -/
def submoduleMap (p : Submodule R M) : p ≃ₛₗ[σ₁₂] ↥(p.map (e : M →ₛₗ[σ₁₂] M₂) : Submodule R₂ M₂) :=
  {
    ((e : M →ₛₗ[σ₁₂] M₂).domRestrict p).codRestrict (p.map (e : M →ₛₗ[σ₁₂] M₂)) fun x =>
      ⟨x, by
        simp only [LinearMap.domRestrict_apply, eq_self_iff_true, and_true_iff, SetLike.coe_mem,
          SetLike.mem_coe]⟩ with
    invFun := fun y =>
      ⟨(e.symm : M₂ →ₛₗ[σ₂₁] M) y, by
        rcases y with ⟨y', hy⟩
        -- ⊢ ↑↑(symm e) ↑{ val := y', property := hy } ∈ p
        rw [Submodule.mem_map] at hy
        -- ⊢ ↑↑(symm e) ↑{ val := y', property := hy✝ } ∈ p
        rcases hy with ⟨x, hx, hxy⟩
        -- ⊢ ↑↑(symm e) ↑{ val := y', property := hy } ∈ p
        subst hxy
        -- ⊢ ↑↑(symm e) ↑{ val := ↑↑e x, property := hy } ∈ p
        simp only [symm_apply_apply, Submodule.coe_mk, coe_coe, hx]⟩
        -- 🎉 no goals
    left_inv := fun x => by
      simp only [LinearMap.domRestrict_apply, LinearMap.codRestrict_apply, LinearMap.toFun_eq_coe,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, SetLike.eta]
    right_inv := fun y => by
      apply SetCoe.ext
      -- ⊢ ↑(AddHom.toFun { toAddHom := src✝.toAddHom, map_smul' := (_ : ∀ (r : R) (x : …
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

section Finsupp

variable {γ : Type*}

variable [Semiring R] [Semiring R₂]

variable [AddCommMonoid M] [AddCommMonoid M₂]

variable [Module R M] [Module R₂ M₂] [Zero γ]

variable {τ₁₂ : R →+* R₂} {τ₂₁ : R₂ →+* R}

variable [RingHomInvPair τ₁₂ τ₂₁] [RingHomInvPair τ₂₁ τ₁₂]

@[simp]
theorem map_finsupp_sum (f : M ≃ₛₗ[τ₁₂] M₂) {t : ι →₀ γ} {g : ι → γ → M} :
    f (t.sum g) = t.sum fun i d => f (g i d) :=
  f.map_sum _
#align linear_equiv.map_finsupp_sum LinearEquiv.map_finsupp_sum

end Finsupp

section DFinsupp

open DFinsupp

variable [Semiring R] [Semiring R₂]

variable [AddCommMonoid M] [AddCommMonoid M₂]

variable [Module R M] [Module R₂ M₂]

variable {τ₁₂ : R →+* R₂} {τ₂₁ : R₂ →+* R}

variable [RingHomInvPair τ₁₂ τ₂₁] [RingHomInvPair τ₂₁ τ₁₂]

variable {γ : ι → Type*} [DecidableEq ι]


@[simp]
theorem map_dfinsupp_sum [∀ i, Zero (γ i)] [∀ (i) (x : γ i), Decidable (x ≠ 0)] (f : M ≃ₛₗ[τ₁₂] M₂)
    (t : Π₀ i, γ i) (g : ∀ i, γ i → M) : f (t.sum g) = t.sum fun i d => f (g i d) :=
  f.map_sum _
#align linear_equiv.map_dfinsupp_sum LinearEquiv.map_dfinsupp_sum

@[simp]
theorem map_dfinsupp_sumAddHom [∀ i, AddZeroClass (γ i)] (f : M ≃ₛₗ[τ₁₂] M₂) (t : Π₀ i, γ i)
    (g : ∀ i, γ i →+ M) :
    f (sumAddHom g t) = sumAddHom (fun i => f.toAddEquiv.toAddMonoidHom.comp (g i)) t :=
  f.toAddEquiv.map_dfinsupp_sumAddHom _ _
#align linear_equiv.map_dfinsupp_sum_add_hom LinearEquiv.map_dfinsupp_sumAddHom

end DFinsupp

section Uncurry

variable [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring R₄]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]

variable (V V₂ R)

/-- Linear equivalence between a curried and uncurried function.
  Differs from `TensorProduct.curry`. -/
protected def curry : (V × V₂ → R) ≃ₗ[R] V → V₂ → R :=
  {
    Equiv.curry _ _
      _ with
    map_add' := fun _ _ => by
      ext
      -- ⊢ Equiv.toFun src✝ (x✝³ + x✝²) x✝¹ x✝ = (Equiv.toFun src✝ x✝³ + Equiv.toFun sr …
      rfl
      -- 🎉 no goals
    map_smul' := fun _ _ => by
      ext
      -- ⊢ AddHom.toFun { toFun := src✝.toFun, map_add' := (_ : ∀ (x x_1 : V × V₂ → R), …
      rfl }
      -- 🎉 no goals
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
                                                             -- ⊢ ↑(↑(ofEq p p (_ : p = p)) x✝) = ↑(↑(refl R { x // x ∈ p }) x✝)
                                                                  -- 🎉 no goals
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
  -- ⊢ ↑(↑↑(ofSubmodule' f U) x✝) = ↑(↑(LinearMap.codRestrict U (LinearMap.domRestr …
  rfl
  -- 🎉 no goals
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
  -- ⊢ b = 0
  rw [← p.mk_eq_zero hb, ← e.map_eq_zero_iff]
  -- ⊢ ↑e { val := b, property := hb } = 0
  apply Submodule.eq_zero_of_bot_submodule
  -- 🎉 no goals
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
                            -- 🎉 no goals
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
                                               -- 🎉 no goals
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
    -- ⊢ ↑((fun f => LinearMap.comp (↑(symm e₂)) (LinearMap.comp f ↑e₁)) (AddHom.toFu …
    simp only [symm_apply_apply, Function.comp_apply, coe_comp, coe_coe]
    -- 🎉 no goals
  right_inv f := by
    ext x
    -- ⊢ ↑(AddHom.toFun { toAddHom := { toFun := fun f => LinearMap.comp (↑e₂) (Linea …
    -- ⊢ ↑((fun f => LinearMap.comp (↑e₂) (LinearMap.comp f ↑(symm e₁))) (f + g)) x = …
    simp only [Function.comp_apply, apply_symm_apply, coe_comp, coe_coe]
    -- 🎉 no goals
    -- 🎉 no goals
  map_add' f g := by
    -- ⊢ ↑(AddHom.toFun { toFun := fun f => LinearMap.comp (↑e₂) (LinearMap.comp f ↑( …
    ext x
    -- 🎉 no goals
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
  -- ⊢ ↑(↑(arrowCongr e₁ e₃) (LinearMap.comp g f)) x✝ = ↑(LinearMap.comp (↑(arrowCo …
  simp only [symm_apply_apply, arrowCongr_apply, LinearMap.comp_apply]
  -- 🎉 no goals
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
  -- ⊢ ↑(↑(trans (conj e₁) (conj e₂)) f) x = ↑(↑(conj (trans e₁ e₂)) f) x
  rfl
  -- 🎉 no goals
#align linear_equiv.conj_trans LinearEquiv.conj_trans

@[simp]
theorem conj_id (e : M ≃ₗ[R] M₂) : e.conj LinearMap.id = LinearMap.id := by
  ext
  -- ⊢ ↑(↑(conj e) LinearMap.id) x✝ = ↑LinearMap.id x✝
  simp [conj_apply]
  -- 🎉 no goals
#align linear_equiv.conj_id LinearEquiv.conj_id

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
                                                -- ⊢ ↑(LinearMap.domRestrict (Submodule.subtype p) q) { val := x, property := hx  …
                                                                -- 🎉 no goals
    invFun := by
      rintro ⟨x, hx⟩
      -- ⊢ { x // x ∈ q }
      refine' ⟨⟨x, _⟩, _⟩ <;> rcases hx with ⟨⟨_, h⟩, _, rfl⟩ <;> assumption
      -- ⊢ x ∈ p
                              -- ⊢ ↑(Submodule.subtype p) { val := val✝, property := h } ∈ p
                              -- ⊢ { val := ↑(Submodule.subtype p) { val := val✝, property := h }, property :=  …
                                                                  -- 🎉 no goals
                                                                  -- 🎉 no goals
    left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
    right_inv := fun ⟨x, ⟨_, h⟩, _, rfl⟩ => by ext; rfl }
                                               -- ⊢ ↑(AddHom.toFun { toAddHom := src✝.toAddHom, map_smul' := (_ : ∀ (r : R) (x : …
                                                    -- 🎉 no goals
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
  -- ⊢ ↑↑(↑(LinearEquiv.symm (equivSubtypeMap p q)) { val := val✝, property := prop …
  rfl
  -- 🎉 no goals
#align submodule.equiv_subtype_map_symm_apply Submodule.equivSubtypeMap_symm_apply

/-- If `s ≤ t`, then we can view `s` as a submodule of `t` by taking the comap
of `t.subtype`. -/
@[simps symm_apply]
def comapSubtypeEquivOfLe {p q : Submodule R M} (hpq : p ≤ q) : comap q.subtype p ≃ₗ[R] p
    where
  toFun x := ⟨x, x.2⟩
  invFun x := ⟨⟨x, hpq x.2⟩, x.2⟩
  left_inv x := by simp only [coe_mk, SetLike.eta, LinearEquiv.coe_coe]
                   -- 🎉 no goals
  right_inv x := by simp only [Subtype.coe_mk, SetLike.eta, LinearEquiv.coe_coe]
                    -- 🎉 no goals
  map_add' x y := rfl
  map_smul' c x := rfl
#align submodule.comap_subtype_equiv_of_le Submodule.comapSubtypeEquivOfLe
#align submodule.comap_subtype_equiv_of_le_symm_apply_coe_coe Submodule.comapSubtypeEquivOfLe_symm_apply

-- Porting note: The original theorem generated by `simps` was using `LinearEquiv.toLinearMap`,
-- different from the theorem on Lean 3, and not simp-normal form.
@[simp]
theorem comapSubtypeEquivOfLe_apply_coe {p q : Submodule R M} (hpq : p ≤ q)
    (x : comap q.subtype p) :
    (comapSubtypeEquivOfLe hpq x : M) = (x : M) :=
  rfl
#align submodule.comap_subtype_equiv_of_le_apply_coe Submodule.comapSubtypeEquivOfLe_apply_coe

end Module

end Submodule

namespace Submodule

variable [CommSemiring R] [CommSemiring R₂]

variable [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂]

variable [AddCommMonoid N] [AddCommMonoid N₂] [Module R N] [Module R N₂]

variable {τ₁₂ : R →+* R₂} {τ₂₁ : R₂ →+* R}

variable [RingHomInvPair τ₁₂ τ₂₁] [RingHomInvPair τ₂₁ τ₁₂]

variable (p : Submodule R M) (q : Submodule R₂ M₂)

variable (pₗ : Submodule R N) (qₗ : Submodule R N₂)

-- Porting note: Was `@[simp]`.
@[simp high]
theorem mem_map_equiv {e : M ≃ₛₗ[τ₁₂] M₂} {x : M₂} :
    x ∈ p.map (e : M →ₛₗ[τ₁₂] M₂) ↔ e.symm x ∈ p := by
  rw [Submodule.mem_map]; constructor
  -- ⊢ (∃ y, y ∈ p ∧ ↑↑e y = x) ↔ ↑(LinearEquiv.symm e) x ∈ p
                          -- ⊢ (∃ y, y ∈ p ∧ ↑↑e y = x) → ↑(LinearEquiv.symm e) x ∈ p
  · rintro ⟨y, hy, hx⟩
    -- ⊢ ↑(LinearEquiv.symm e) x ∈ p
    simp [← hx, hy]
    -- 🎉 no goals
  · intro hx
    -- ⊢ ∃ y, y ∈ p ∧ ↑↑e y = x
    refine' ⟨e.symm x, hx, by simp⟩
    -- 🎉 no goals
#align submodule.mem_map_equiv Submodule.mem_map_equiv

theorem map_equiv_eq_comap_symm (e : M ≃ₛₗ[τ₁₂] M₂) (K : Submodule R M) :
    K.map (e : M →ₛₗ[τ₁₂] M₂) = K.comap (e.symm : M₂ →ₛₗ[τ₂₁] M) :=
  Submodule.ext fun _ => by rw [mem_map_equiv, mem_comap, LinearEquiv.coe_coe]
                            -- 🎉 no goals
#align submodule.map_equiv_eq_comap_symm Submodule.map_equiv_eq_comap_symm

theorem comap_equiv_eq_map_symm (e : M ≃ₛₗ[τ₁₂] M₂) (K : Submodule R₂ M₂) :
    K.comap (e : M →ₛₗ[τ₁₂] M₂) = K.map (e.symm : M₂ →ₛₗ[τ₂₁] M) :=
  (map_equiv_eq_comap_symm e.symm K).symm
#align submodule.comap_equiv_eq_map_symm Submodule.comap_equiv_eq_map_symm

variable {p}

theorem map_symm_eq_iff (e : M ≃ₛₗ[τ₁₂] M₂) {K : Submodule R₂ M₂} :
    K.map e.symm = p ↔ p.map e = K := by
  constructor <;> rintro rfl
  -- ⊢ map (LinearEquiv.symm e) K = p → map e p = K
                  -- ⊢ map e (map (LinearEquiv.symm e) K) = K
                  -- ⊢ map (LinearEquiv.symm e) (map e p) = p
  · calc
      map e (map e.symm K) = comap e.symm (map e.symm K) := map_equiv_eq_comap_symm _ _
      _ = K := comap_map_eq_of_injective e.symm.injective _
  · calc
      map e.symm (map e p) = comap e (map e p) := (comap_equiv_eq_map_symm _ _).symm
      _ = p := comap_map_eq_of_injective e.injective _
#align submodule.map_symm_eq_iff Submodule.map_symm_eq_iff

theorem orderIsoMapComap_apply' (e : M ≃ₛₗ[τ₁₂] M₂) (p : Submodule R M) :
    orderIsoMapComap e p = comap e.symm p :=
  p.map_equiv_eq_comap_symm _
#align submodule.order_iso_map_comap_apply' Submodule.orderIsoMapComap_apply'

theorem orderIsoMapComap_symm_apply' (e : M ≃ₛₗ[τ₁₂] M₂) (p : Submodule R₂ M₂) :
    (orderIsoMapComap e).symm p = map e.symm p :=
  p.comap_equiv_eq_map_symm _
#align submodule.order_iso_map_comap_symm_apply' Submodule.orderIsoMapComap_symm_apply'

theorem comap_le_comap_smul (fₗ : N →ₗ[R] N₂) (c : R) : comap fₗ qₗ ≤ comap (c • fₗ) qₗ := by
  rw [SetLike.le_def]
  -- ⊢ ∀ ⦃x : N⦄, x ∈ comap fₗ qₗ → x ∈ comap (c • fₗ) qₗ
  intro m h
  -- ⊢ m ∈ comap (c • fₗ) qₗ
  change c • fₗ m ∈ qₗ
  -- ⊢ c • ↑fₗ m ∈ qₗ
  replace h : fₗ m ∈ qₗ := h -- Porting note: was `change … at`
  -- ⊢ c • ↑fₗ m ∈ qₗ
  apply qₗ.smul_mem _ h
  -- 🎉 no goals
#align submodule.comap_le_comap_smul Submodule.comap_le_comap_smul

theorem inf_comap_le_comap_add (f₁ f₂ : M →ₛₗ[τ₁₂] M₂) :
    comap f₁ q ⊓ comap f₂ q ≤ comap (f₁ + f₂) q := by
  rw [SetLike.le_def]
  -- ⊢ ∀ ⦃x : M⦄, x ∈ comap f₁ q ⊓ comap f₂ q → x ∈ comap (f₁ + f₂) q
  intro m h
  -- ⊢ m ∈ comap (f₁ + f₂) q
  change f₁ m + f₂ m ∈ q
  -- ⊢ ↑f₁ m + ↑f₂ m ∈ q
  replace h : f₁ m ∈ q ∧ f₂ m ∈ q := h -- Porting note: was `change … at`
  -- ⊢ ↑f₁ m + ↑f₂ m ∈ q
  apply q.add_mem h.1 h.2
  -- 🎉 no goals
#align submodule.inf_comap_le_comap_add Submodule.inf_comap_le_comap_add

/-- Given modules `M`, `M₂` over a commutative ring, together with submodules `p ⊆ M`, `q ⊆ M₂`,
the set of maps $\{f ∈ Hom(M, M₂) | f(p) ⊆ q \}$ is a submodule of `Hom(M, M₂)`. -/
def compatibleMaps : Submodule R (N →ₗ[R] N₂)
    where
  carrier := { fₗ | pₗ ≤ comap fₗ qₗ }
  zero_mem' := by
    change pₗ ≤ comap (0 : N →ₗ[R] N₂) qₗ
    -- ⊢ pₗ ≤ comap 0 qₗ
    rw [comap_zero]
    -- ⊢ pₗ ≤ ⊤
    refine' le_top
    -- ⊢ pₗ ≤ comap f₁ qₗ ⊓ comap f₂ qₗ
    -- 🎉 no goals
    -- ⊢ pₗ ≤ comap f₁ qₗ ∧ pₗ ≤ comap f₂ qₗ
  add_mem' {f₁ f₂} h₁ h₂ := by
    -- 🎉 no goals
    apply le_trans _ (inf_comap_le_comap_add qₗ f₁ f₂)
    rw [le_inf_iff]
    exact ⟨h₁, h₂⟩
  smul_mem' c fₗ h := by
    dsimp at h
    -- ⊢ c • fₗ ∈ { toAddSubsemigroup := { carrier := {fₗ | pₗ ≤ comap fₗ qₗ}, add_me …
    exact le_trans h (comap_le_comap_smul qₗ fₗ c)
    -- 🎉 no goals
#align submodule.compatible_maps Submodule.compatibleMaps

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
def funLeft (f : m → n) : (n → M) →ₗ[R] m → M
    where
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
  -- ⊢ Injective ↑(funLeft R M f)
  suffices LeftInverse (funLeft R M g) (funLeft R M f) by exact this.injective
  -- ⊢ LeftInverse ↑(funLeft R M g) ↑(funLeft R M f)
  intro x
  -- ⊢ ↑(funLeft R M g) (↑(funLeft R M f) x) = x
  rw [← LinearMap.comp_apply, ← funLeft_comp, hg.id, funLeft_id]
  -- 🎉 no goals
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
                         -- 🎉 no goals
    (LinearMap.ext fun x =>
      funext fun i => by rw [id_apply, ← funLeft_comp, Equiv.self_comp_symm, LinearMap.funLeft_id])
                         -- 🎉 no goals
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
