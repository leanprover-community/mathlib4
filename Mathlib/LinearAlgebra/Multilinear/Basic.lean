/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.List.FinRange
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.Abel

#align_import linear_algebra.multilinear.basic from "leanprover-community/mathlib"@"78fdf68dcd2fdb3fe64c0dd6f88926a49418a6ea"

/-!
# Multilinear maps

We define multilinear maps as maps from `∀ (i : ι), M₁ i` to `M₂` which are linear in each
coordinate. Here, `M₁ i` and `M₂` are modules over a ring `R`, and `ι` is an arbitrary type
(although some statements will require it to be a fintype). This space, denoted by
`MultilinearMap R M₁ M₂`, inherits a module structure by pointwise addition and multiplication.

## Main definitions

* `MultilinearMap R M₁ M₂` is the space of multilinear maps from `∀ (i : ι), M₁ i` to `M₂`.
* `f.map_smul` is the multiplicativity of the multilinear map `f` along each coordinate.
* `f.map_add` is the additivity of the multilinear map `f` along each coordinate.
* `f.map_smul_univ` expresses the multiplicativity of `f` over all coordinates at the same time,
  writing `f (fun i => c i • m i)` as `(∏ i, c i) • f m`.
* `f.map_add_univ` expresses the additivity of `f` over all coordinates at the same time, writing

  `f (m + m')` as the sum over all subsets `s` of `ι` of `f (s.piecewise m m')`.
* `f.map_sum` expresses `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` as the sum of
  `f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all possible functions.

We also register isomorphisms corresponding to currying or uncurrying variables, transforming a
multilinear function `f` on `n+1` variables into a linear function taking values in multilinear
functions in `n` variables, and into a multilinear function in `n` variables taking values in linear
functions. These operations are called `f.curryLeft` and `f.curryRight` respectively
(with inverses `f.uncurryLeft` and `f.uncurryRight`). These operations induce linear equivalences
between spaces of multilinear functions in `n+1` variables and spaces of linear functions into
multilinear functions in `n` variables (resp. multilinear functions in `n` variables taking values
in linear functions), called respectively `multilinearCurryLeftEquiv` and
`multilinearCurryRightEquiv`.

## Implementation notes

Expressing that a map is linear along the `i`-th coordinate when all other coordinates are fixed
can be done in two (equivalent) different ways:

* fixing a vector `m : ∀ (j : ι - i), M₁ j.val`, and then choosing separately the `i`-th coordinate
* fixing a vector `m : ∀j, M₁ j`, and then modifying its `i`-th coordinate

The second way is more artificial as the value of `m` at `i` is not relevant, but it has the
advantage of avoiding subtype inclusion issues. This is the definition we use, based on
`Function.update` that allows to change the value of `m` at `i`.

Note that the use of `Function.update` requires a `DecidableEq ι` term to appear somewhere in the
statement of `MultilinearMap.map_add'` and `MultilinearMap.map_smul'`. Three possible choices
are:

1. Requiring `DecidableEq ι` as an argument to `MultilinearMap` (as we did originally).
2. Using `Classical.decEq ι` in the statement of `map_add'` and `map_smul'`.
3. Quantifying over all possible `DecidableEq ι` instances in the statement of `map_add'` and
   `map_smul'`.

Option 1 works fine, but puts unnecessary constraints on the user (the zero map certainly does not
need decidability). Option 2 looks great at first, but in the common case when `ι = Fin n` it
introduces non-defeq decidability instance diamonds within the context of proving `map_add'` and
`map_smul'`, of the form `Fin.decidableEq n = Classical.decEq (Fin n)`. Option 3 of course does
something similar, but of the form `Fin.decidableEq n = _inst`, which is much easier to clean up
since `_inst` is a free variable and so the equality can just be substituted.
-/


open Function Fin Set

universe uR uS uι v v' v₁ v₂ v₃

variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₂ : Type v₂} {M₃ : Type v₃} {M' : Type v'}

/-- Multilinear maps over the ring `R`, from `∀ i, M₁ i` to `M₂` where `M₁ i` and `M₂` are modules
over `R`. -/
structure MultilinearMap (R : Type uR) {ι : Type uι} (M₁ : ι → Type v₁) (M₂ : Type v₂) [Semiring R]
  [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [∀ i, Module R (M₁ i)] [Module R M₂] where
  /-- The underlying multivariate function of a multilinear map. -/
  toFun : (∀ i, M₁ i) → M₂
  /-- A multilinear map is additive in every argument. -/
  map_add' :
    ∀ [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i),
      toFun (update m i (x + y)) = toFun (update m i x) + toFun (update m i y)
  /-- A multilinear map is compatible with scalar multiplication in every argument. -/
  map_smul' :
    ∀ [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (c : R) (x : M₁ i),
      toFun (update m i (c • x)) = c • toFun (update m i x)
#align multilinear_map MultilinearMap

-- Porting note: added to avoid a linter timeout.
attribute [nolint simpNF] MultilinearMap.mk.injEq

namespace MultilinearMap

section Semiring

variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂]
  [AddCommMonoid M₃] [AddCommMonoid M'] [∀ i, Module R (M i)] [∀ i, Module R (M₁ i)] [Module R M₂]
  [Module R M₃] [Module R M'] (f f' : MultilinearMap R M₁ M₂)

-- Porting note: Replaced CoeFun with FunLike instance
instance : FunLike (MultilinearMap R M₁ M₂) (∀ i, M₁ i) M₂ where
  coe f := f.toFun
  coe_injective' := fun f g h ↦ by cases f; cases g; cases h; rfl

initialize_simps_projections MultilinearMap (toFun → apply)

@[simp]
theorem toFun_eq_coe : f.toFun = ⇑f :=
  rfl
#align multilinear_map.to_fun_eq_coe MultilinearMap.toFun_eq_coe

@[simp]
theorem coe_mk (f : (∀ i, M₁ i) → M₂) (h₁ h₂) : ⇑(⟨f, h₁, h₂⟩ : MultilinearMap R M₁ M₂) = f :=
  rfl
#align multilinear_map.coe_mk MultilinearMap.coe_mk

theorem congr_fun {f g : MultilinearMap R M₁ M₂} (h : f = g) (x : ∀ i, M₁ i) : f x = g x :=
  DFunLike.congr_fun h x
#align multilinear_map.congr_fun MultilinearMap.congr_fun

nonrec theorem congr_arg (f : MultilinearMap R M₁ M₂) {x y : ∀ i, M₁ i} (h : x = y) : f x = f y :=
  DFunLike.congr_arg f h
#align multilinear_map.congr_arg MultilinearMap.congr_arg

theorem coe_injective : Injective ((↑) : MultilinearMap R M₁ M₂ → (∀ i, M₁ i) → M₂) :=
  DFunLike.coe_injective
#align multilinear_map.coe_injective MultilinearMap.coe_injective

@[norm_cast] -- Porting note (#10618): Removed simp attribute, simp can prove this
theorem coe_inj {f g : MultilinearMap R M₁ M₂} : (f : (∀ i, M₁ i) → M₂) = g ↔ f = g :=
  DFunLike.coe_fn_eq
#align multilinear_map.coe_inj MultilinearMap.coe_inj

@[ext]
theorem ext {f f' : MultilinearMap R M₁ M₂} (H : ∀ x, f x = f' x) : f = f' :=
  DFunLike.ext _ _ H
#align multilinear_map.ext MultilinearMap.ext

theorem ext_iff {f g : MultilinearMap R M₁ M₂} : f = g ↔ ∀ x, f x = g x :=
  DFunLike.ext_iff
#align multilinear_map.ext_iff MultilinearMap.ext_iff

@[simp]
theorem mk_coe (f : MultilinearMap R M₁ M₂) (h₁ h₂) :
    (⟨f, h₁, h₂⟩ : MultilinearMap R M₁ M₂) = f := rfl
#align multilinear_map.mk_coe MultilinearMap.mk_coe

@[simp]
protected theorem map_add [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i) :
    f (update m i (x + y)) = f (update m i x) + f (update m i y) :=
  f.map_add' m i x y
#align multilinear_map.map_add MultilinearMap.map_add

@[simp]
protected theorem map_smul [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (c : R) (x : M₁ i) :
    f (update m i (c • x)) = c • f (update m i x) :=
  f.map_smul' m i c x
#align multilinear_map.map_smul MultilinearMap.map_smul

theorem map_coord_zero {m : ∀ i, M₁ i} (i : ι) (h : m i = 0) : f m = 0 := by
  classical
    have : (0 : R) • (0 : M₁ i) = 0 := by simp
    rw [← update_eq_self i m, h, ← this, f.map_smul, zero_smul R (M := M₂)]
#align multilinear_map.map_coord_zero MultilinearMap.map_coord_zero

@[simp]
theorem map_update_zero [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) : f (update m i 0) = 0 :=
  f.map_coord_zero i (update_same i 0 m)
#align multilinear_map.map_update_zero MultilinearMap.map_update_zero

@[simp]
theorem map_zero [Nonempty ι] : f 0 = 0 := by
  obtain ⟨i, _⟩ : ∃ i : ι, i ∈ Set.univ := Set.exists_mem_of_nonempty ι
  exact map_coord_zero f i rfl
#align multilinear_map.map_zero MultilinearMap.map_zero

instance : Add (MultilinearMap R M₁ M₂) :=
  ⟨fun f f' =>
    ⟨fun x => f x + f' x, fun m i x y => by simp [add_left_comm, add_assoc], fun m i c x => by
      simp [smul_add]⟩⟩

@[simp]
theorem add_apply (m : ∀ i, M₁ i) : (f + f') m = f m + f' m :=
  rfl
#align multilinear_map.add_apply MultilinearMap.add_apply

instance : Zero (MultilinearMap R M₁ M₂) :=
  ⟨⟨fun _ => 0, fun _ i _ _ => by simp, fun _ i c _ => by simp⟩⟩

instance : Inhabited (MultilinearMap R M₁ M₂) :=
  ⟨0⟩

@[simp]
theorem zero_apply (m : ∀ i, M₁ i) : (0 : MultilinearMap R M₁ M₂) m = 0 :=
  rfl
#align multilinear_map.zero_apply MultilinearMap.zero_apply

section SMul

variable {R' A : Type*} [Monoid R'] [Semiring A] [∀ i, Module A (M₁ i)] [DistribMulAction R' M₂]
  [Module A M₂] [SMulCommClass A R' M₂]

instance : SMul R' (MultilinearMap A M₁ M₂) :=
  ⟨fun c f =>
    ⟨fun m => c • f m, fun m i x y => by simp [smul_add], fun l i x d => by
      simp [← smul_comm x c (_ : M₂)]⟩⟩

@[simp]
theorem smul_apply (f : MultilinearMap A M₁ M₂) (c : R') (m : ∀ i, M₁ i) : (c • f) m = c • f m :=
  rfl
#align multilinear_map.smul_apply MultilinearMap.smul_apply

theorem coe_smul (c : R') (f : MultilinearMap A M₁ M₂) : ⇑(c • f) = c • (⇑ f) :=
  rfl
#align multilinear_map.coe_smul MultilinearMap.coe_smul

end SMul

instance addCommMonoid : AddCommMonoid (MultilinearMap R M₁ M₂) :=
  coe_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
#align multilinear_map.add_comm_monoid MultilinearMap.addCommMonoid

/-- Coercion of a multilinear map to a function as an additive monoid homomorphism. -/
@[simps] def coeAddMonoidHom : MultilinearMap R M₁ M₂ →+ (((i : ι) → M₁ i) → M₂) where
  toFun := DFunLike.coe; map_zero' := rfl; map_add' _ _ := rfl

@[simp]
theorem coe_sum {α : Type*} (f : α → MultilinearMap R M₁ M₂) (s : Finset α) :
    ⇑(∑ a ∈ s, f a) = ∑ a ∈ s, ⇑(f a) :=
  map_sum coeAddMonoidHom f s

theorem sum_apply {α : Type*} (f : α → MultilinearMap R M₁ M₂) (m : ∀ i, M₁ i) {s : Finset α} :
    (∑ a ∈ s, f a) m = ∑ a ∈ s, f a m := by simp
#align multilinear_map.sum_apply MultilinearMap.sum_apply

/-- If `f` is a multilinear map, then `f.toLinearMap m i` is the linear map obtained by fixing all
coordinates but `i` equal to those of `m`, and varying the `i`-th coordinate. -/
@[simps]
def toLinearMap [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) : M₁ i →ₗ[R] M₂ where
  toFun x := f (update m i x)
  map_add' x y := by simp
  map_smul' c x := by simp
#align multilinear_map.to_linear_map MultilinearMap.toLinearMap
#align multilinear_map.to_linear_map_to_add_hom_apply MultilinearMap.toLinearMap_apply

/-- The cartesian product of two multilinear maps, as a multilinear map. -/
@[simps]
def prod (f : MultilinearMap R M₁ M₂) (g : MultilinearMap R M₁ M₃) :
    MultilinearMap R M₁ (M₂ × M₃) where
  toFun m := (f m, g m)
  map_add' m i x y := by simp
  map_smul' m i c x := by simp
#align multilinear_map.prod MultilinearMap.prod
#align multilinear_map.prod_apply MultilinearMap.prod_apply

/-- Combine a family of multilinear maps with the same domain and codomains `M' i` into a
multilinear map taking values in the space of functions `∀ i, M' i`. -/
@[simps]
def pi {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)] [∀ i, Module R (M' i)]
    (f : ∀ i, MultilinearMap R M₁ (M' i)) : MultilinearMap R M₁ (∀ i, M' i) where
  toFun m i := f i m
  map_add' _ _ _ _ := funext fun j => (f j).map_add _ _ _ _
  map_smul' _ _ _ _ := funext fun j => (f j).map_smul _ _ _ _
#align multilinear_map.pi MultilinearMap.pi
#align multilinear_map.pi_apply MultilinearMap.pi_apply

section

variable (R M₂ M₃)

/-- Equivalence between linear maps `M₂ →ₗ[R] M₃` and one-multilinear maps. -/
@[simps]
def ofSubsingleton [Subsingleton ι] (i : ι) :
    (M₂ →ₗ[R] M₃) ≃ MultilinearMap R (fun _ : ι ↦ M₂) M₃ where
  toFun f :=
    { toFun := fun x ↦ f (x i)
      map_add' := by intros; simp [update_eq_const_of_subsingleton]
      map_smul' := by intros; simp [update_eq_const_of_subsingleton] }
  invFun f :=
    { toFun := fun x ↦ f fun _ ↦ x
      map_add' := fun x y ↦ by simpa [update_eq_const_of_subsingleton] using f.map_add 0 i x y
      map_smul' := fun c x ↦ by simpa [update_eq_const_of_subsingleton] using f.map_smul 0 i c x }
  left_inv f := rfl
  right_inv f := by ext x; refine congr_arg f ?_; exact (eq_const_of_subsingleton _ _).symm
#align multilinear_map.of_subsingleton MultilinearMap.ofSubsingletonₓ
#align multilinear_map.of_subsingleton_apply MultilinearMap.ofSubsingleton_apply_applyₓ

variable (M₁) {M₂}

/-- The constant map is multilinear when `ι` is empty. -/
-- Porting note: Removed [simps] & added simpNF-approved version of the generated lemma manually.
@[simps (config := .asFn)]
def constOfIsEmpty [IsEmpty ι] (m : M₂) : MultilinearMap R M₁ M₂ where
  toFun := Function.const _ m
  map_add' _ := isEmptyElim
  map_smul' _ := isEmptyElim
#align multilinear_map.const_of_is_empty MultilinearMap.constOfIsEmpty
#align multilinear_map.const_of_is_empty_apply MultilinearMap.constOfIsEmpty_apply

end

-- Porting note: Included `DFunLike.coe` to avoid strange CoeFun instance for Equiv
/-- Given a multilinear map `f` on `n` variables (parameterized by `Fin n`) and a subset `s` of `k`
of these variables, one gets a new multilinear map on `Fin k` by varying these variables, and fixing
the other ones equal to a given value `z`. It is denoted by `f.restr s hk z`, where `hk` is a
proof that the cardinality of `s` is `k`. The implicit identification between `Fin k` and `s` that
we use is the canonical (increasing) bijection. -/
def restr {k n : ℕ} (f : MultilinearMap R (fun _ : Fin n => M') M₂) (s : Finset (Fin n))
    (hk : s.card = k) (z : M') : MultilinearMap R (fun _ : Fin k => M') M₂ where
  toFun v := f fun j => if h : j ∈ s then v ((DFunLike.coe (s.orderIsoOfFin hk).symm) ⟨j, h⟩) else z
  /- Porting note: The proofs of the following two lemmas used to only use `erw` followed by `simp`,
  but it seems `erw` no longer unfolds or unifies well enough to work without more help. -/
  map_add' v i x y := by
    have : DFunLike.coe (s.orderIsoOfFin hk).symm = (s.orderIsoOfFin hk).toEquiv.symm := rfl
    simp only [this]
    erw [dite_comp_equiv_update (s.orderIsoOfFin hk).toEquiv,
      dite_comp_equiv_update (s.orderIsoOfFin hk).toEquiv,
      dite_comp_equiv_update (s.orderIsoOfFin hk).toEquiv]
    simp
  map_smul' v i c x := by
    have : DFunLike.coe (s.orderIsoOfFin hk).symm = (s.orderIsoOfFin hk).toEquiv.symm := rfl
    simp only [this]
    erw [dite_comp_equiv_update (s.orderIsoOfFin hk).toEquiv,
      dite_comp_equiv_update (s.orderIsoOfFin hk).toEquiv]
    simp
#align multilinear_map.restr MultilinearMap.restr

/-- In the specific case of multilinear maps on spaces indexed by `Fin (n+1)`, where one can build
an element of `∀ (i : Fin (n+1)), M i` using `cons`, one can express directly the additivity of a
multilinear map along the first variable. -/
theorem cons_add (f : MultilinearMap R M M₂) (m : ∀ i : Fin n, M i.succ) (x y : M 0) :
    f (cons (x + y) m) = f (cons x m) + f (cons y m) := by
  simp_rw [← update_cons_zero x m (x + y), f.map_add, update_cons_zero]
#align multilinear_map.cons_add MultilinearMap.cons_add

/-- In the specific case of multilinear maps on spaces indexed by `Fin (n+1)`, where one can build
an element of `∀ (i : Fin (n+1)), M i` using `cons`, one can express directly the multiplicativity
of a multilinear map along the first variable. -/
theorem cons_smul (f : MultilinearMap R M M₂) (m : ∀ i : Fin n, M i.succ) (c : R) (x : M 0) :
    f (cons (c • x) m) = c • f (cons x m) := by
  simp_rw [← update_cons_zero x m (c • x), f.map_smul, update_cons_zero]
#align multilinear_map.cons_smul MultilinearMap.cons_smul

/-- In the specific case of multilinear maps on spaces indexed by `Fin (n+1)`, where one can build
an element of `∀ (i : Fin (n+1)), M i` using `snoc`, one can express directly the additivity of a
multilinear map along the first variable. -/
theorem snoc_add (f : MultilinearMap R M M₂)
    (m : ∀ i : Fin n, M (castSucc i)) (x y : M (last n)) :
    f (snoc m (x + y)) = f (snoc m x) + f (snoc m y) := by
  simp_rw [← update_snoc_last x m (x + y), f.map_add, update_snoc_last]
#align multilinear_map.snoc_add MultilinearMap.snoc_add

/-- In the specific case of multilinear maps on spaces indexed by `Fin (n+1)`, where one can build
an element of `∀ (i : Fin (n+1)), M i` using `cons`, one can express directly the multiplicativity
of a multilinear map along the first variable. -/
theorem snoc_smul (f : MultilinearMap R M M₂) (m : ∀ i : Fin n, M (castSucc i)) (c : R)
    (x : M (last n)) : f (snoc m (c • x)) = c • f (snoc m x) := by
  simp_rw [← update_snoc_last x m (c • x), f.map_smul, update_snoc_last]
#align multilinear_map.snoc_smul MultilinearMap.snoc_smul

section

variable {M₁' : ι → Type*} [∀ i, AddCommMonoid (M₁' i)] [∀ i, Module R (M₁' i)]
variable {M₁'' : ι → Type*} [∀ i, AddCommMonoid (M₁'' i)] [∀ i, Module R (M₁'' i)]

/-- If `g` is a multilinear map and `f` is a collection of linear maps,
then `g (f₁ m₁, ..., fₙ mₙ)` is again a multilinear map, that we call
`g.compLinearMap f`. -/
def compLinearMap (g : MultilinearMap R M₁' M₂) (f : ∀ i, M₁ i →ₗ[R] M₁' i) :
    MultilinearMap R M₁ M₂ where
  toFun m := g fun i => f i (m i)
  map_add' m i x y := by
    have : ∀ j z, f j (update m i z j) = update (fun k => f k (m k)) i (f i z) j := fun j z =>
      Function.apply_update (fun k => f k) _ _ _ _
    simp [this]
  map_smul' m i c x := by
    have : ∀ j z, f j (update m i z j) = update (fun k => f k (m k)) i (f i z) j := fun j z =>
      Function.apply_update (fun k => f k) _ _ _ _
    simp [this]
#align multilinear_map.comp_linear_map MultilinearMap.compLinearMap

@[simp]
theorem compLinearMap_apply (g : MultilinearMap R M₁' M₂) (f : ∀ i, M₁ i →ₗ[R] M₁' i)
    (m : ∀ i, M₁ i) : g.compLinearMap f m = g fun i => f i (m i) :=
  rfl
#align multilinear_map.comp_linear_map_apply MultilinearMap.compLinearMap_apply

/-- Composing a multilinear map twice with a linear map in each argument is
the same as composing with their composition. -/
theorem compLinearMap_assoc (g : MultilinearMap R M₁'' M₂) (f₁ : ∀ i, M₁' i →ₗ[R] M₁'' i)
    (f₂ : ∀ i, M₁ i →ₗ[R] M₁' i) :
    (g.compLinearMap f₁).compLinearMap f₂ = g.compLinearMap fun i => f₁ i ∘ₗ f₂ i :=
  rfl
#align multilinear_map.comp_linear_map_assoc MultilinearMap.compLinearMap_assoc

/-- Composing the zero multilinear map with a linear map in each argument. -/
@[simp]
theorem zero_compLinearMap (f : ∀ i, M₁ i →ₗ[R] M₁' i) :
    (0 : MultilinearMap R M₁' M₂).compLinearMap f = 0 :=
  ext fun _ => rfl
#align multilinear_map.zero_comp_linear_map MultilinearMap.zero_compLinearMap

/-- Composing a multilinear map with the identity linear map in each argument. -/
@[simp]
theorem compLinearMap_id (g : MultilinearMap R M₁' M₂) :
    (g.compLinearMap fun _ => LinearMap.id) = g :=
  ext fun _ => rfl
#align multilinear_map.comp_linear_map_id MultilinearMap.compLinearMap_id

/-- Composing with a family of surjective linear maps is injective. -/
theorem compLinearMap_injective (f : ∀ i, M₁ i →ₗ[R] M₁' i) (hf : ∀ i, Surjective (f i)) :
    Injective fun g : MultilinearMap R M₁' M₂ => g.compLinearMap f := fun g₁ g₂ h =>
  ext fun x => by
    simpa [fun i => surjInv_eq (hf i)] using ext_iff.mp h fun i => surjInv (hf i) (x i)
#align multilinear_map.comp_linear_map_injective MultilinearMap.compLinearMap_injective

theorem compLinearMap_inj (f : ∀ i, M₁ i →ₗ[R] M₁' i) (hf : ∀ i, Surjective (f i))
    (g₁ g₂ : MultilinearMap R M₁' M₂) : g₁.compLinearMap f = g₂.compLinearMap f ↔ g₁ = g₂ :=
  (compLinearMap_injective _ hf).eq_iff
#align multilinear_map.comp_linear_map_inj MultilinearMap.compLinearMap_inj

/-- Composing a multilinear map with a linear equiv on each argument gives the zero map
if and only if the multilinear map is the zero map. -/
@[simp]
theorem comp_linearEquiv_eq_zero_iff (g : MultilinearMap R M₁' M₂) (f : ∀ i, M₁ i ≃ₗ[R] M₁' i) :
    (g.compLinearMap fun i => (f i : M₁ i →ₗ[R] M₁' i)) = 0 ↔ g = 0 := by
  set f' := fun i => (f i : M₁ i →ₗ[R] M₁' i)
  rw [← zero_compLinearMap f', compLinearMap_inj f' fun i => (f i).surjective]
#align multilinear_map.comp_linear_equiv_eq_zero_iff MultilinearMap.comp_linearEquiv_eq_zero_iff

end

/-- If one adds to a vector `m'` another vector `m`, but only for coordinates in a finset `t`, then
the image under a multilinear map `f` is the sum of `f (s.piecewise m m')` along all subsets `s` of
`t`. This is mainly an auxiliary statement to prove the result when `t = univ`, given in
`map_add_univ`, although it can be useful in its own right as it does not require the index set `ι`
to be finite. -/
theorem map_piecewise_add [DecidableEq ι] (m m' : ∀ i, M₁ i) (t : Finset ι) :
    f (t.piecewise (m + m') m') = ∑ s ∈ t.powerset, f (s.piecewise m m') := by
  revert m'
  refine Finset.induction_on t (by simp) ?_
  intro i t hit Hrec m'
  have A : (insert i t).piecewise (m + m') m' = update (t.piecewise (m + m') m') i (m i + m' i) :=
    t.piecewise_insert _ _ _
  have B : update (t.piecewise (m + m') m') i (m' i) = t.piecewise (m + m') m' := by
    ext j
    by_cases h : j = i
    · rw [h]
      simp [hit]
    · simp [h]
  let m'' := update m' i (m i)
  have C : update (t.piecewise (m + m') m') i (m i) = t.piecewise (m + m'') m'' := by
    ext j
    by_cases h : j = i
    · rw [h]
      simp [m'', hit]
    · by_cases h' : j ∈ t <;> simp [m'', h, hit, h']
  rw [A, f.map_add, B, C, Finset.sum_powerset_insert hit, Hrec, Hrec, add_comm (_ : M₂)]
  congr 1
  refine Finset.sum_congr rfl fun s hs => ?_
  have : (insert i s).piecewise m m' = s.piecewise m m'' := by
    ext j
    by_cases h : j = i
    · rw [h]
      simp [m'', Finset.not_mem_of_mem_powerset_of_not_mem hs hit]
    · by_cases h' : j ∈ s <;> simp [m'', h, h']
  rw [this]
#align multilinear_map.map_piecewise_add MultilinearMap.map_piecewise_add

/-- Additivity of a multilinear map along all coordinates at the same time,
writing `f (m + m')` as the sum of `f (s.piecewise m m')` over all sets `s`. -/
theorem map_add_univ [DecidableEq ι] [Fintype ι] (m m' : ∀ i, M₁ i) :
    f (m + m') = ∑ s : Finset ι, f (s.piecewise m m') := by
  simpa using f.map_piecewise_add m m' Finset.univ
#align multilinear_map.map_add_univ MultilinearMap.map_add_univ

section ApplySum

variable {α : ι → Type*} (g : ∀ i, α i → M₁ i) (A : ∀ i, Finset (α i))

open Fintype Finset

/-- If `f` is multilinear, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r 1 ∈ A₁`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with respect to each
coordinate. Here, we give an auxiliary statement tailored for an inductive proof. Use instead
`map_sum_finset`. -/
theorem map_sum_finset_aux [DecidableEq ι] [Fintype ι] {n : ℕ} (h : (∑ i, (A i).card) = n) :
    (f fun i => ∑ j ∈ A i, g i j) = ∑ r ∈ piFinset A, f fun i => g i (r i) := by
  letI := fun i => Classical.decEq (α i)
  induction' n using Nat.strong_induction_on with n IH generalizing A
  -- If one of the sets is empty, then all the sums are zero
  by_cases Ai_empty : ∃ i, A i = ∅
  · rcases Ai_empty with ⟨i, hi⟩
    have : ∑ j ∈ A i, g i j = 0 := by rw [hi, Finset.sum_empty]
    rw [f.map_coord_zero i this]
    have : piFinset A = ∅ := by
      refine Finset.eq_empty_of_forall_not_mem fun r hr => ?_
      have : r i ∈ A i := mem_piFinset.mp hr i
      simp [hi] at this
    rw [this, Finset.sum_empty]
  push_neg at Ai_empty
  -- Otherwise, if all sets are at most singletons, then they are exactly singletons and the result
  -- is again straightforward
  by_cases Ai_singleton : ∀ i, (A i).card ≤ 1
  · have Ai_card : ∀ i, (A i).card = 1 := by
      intro i
      have pos : Finset.card (A i) ≠ 0 := by simp [Finset.card_eq_zero, Ai_empty i]
      have : Finset.card (A i) ≤ 1 := Ai_singleton i
      exact le_antisymm this (Nat.succ_le_of_lt (_root_.pos_iff_ne_zero.mpr pos))
    have :
      ∀ r : ∀ i, α i, r ∈ piFinset A → (f fun i => g i (r i)) = f fun i => ∑ j ∈ A i, g i j := by
      intro r hr
      congr with i
      have : ∀ j ∈ A i, g i j = g i (r i) := by
        intro j hj
        congr
        apply Finset.card_le_one_iff.1 (Ai_singleton i) hj
        exact mem_piFinset.mp hr i
      simp only [Finset.sum_congr rfl this, Finset.mem_univ, Finset.sum_const, Ai_card i, one_nsmul]
    simp only [Finset.sum_congr rfl this, Ai_card, card_piFinset, prod_const_one, one_nsmul,
      Finset.sum_const]
  -- Remains the interesting case where one of the `A i`, say `A i₀`, has cardinality at least 2.
  -- We will split into two parts `B i₀` and `C i₀` of smaller cardinality, let `B i = C i = A i`
  -- for `i ≠ i₀`, apply the inductive assumption to `B` and `C`, and add up the corresponding
  -- parts to get the sum for `A`.
  push_neg at Ai_singleton
  obtain ⟨i₀, hi₀⟩ : ∃ i, 1 < (A i).card := Ai_singleton
  obtain ⟨j₁, j₂, _, hj₂, _⟩ : ∃ j₁ j₂, j₁ ∈ A i₀ ∧ j₂ ∈ A i₀ ∧ j₁ ≠ j₂ :=
    Finset.one_lt_card_iff.1 hi₀
  let B := Function.update A i₀ (A i₀ \ {j₂})
  let C := Function.update A i₀ {j₂}
  have B_subset_A : ∀ i, B i ⊆ A i := by
    intro i
    by_cases hi : i = i₀
    · rw [hi]
      simp only [B, sdiff_subset, update_same]
    · simp only [B, hi, update_noteq, Ne, not_false_iff, Finset.Subset.refl]
  have C_subset_A : ∀ i, C i ⊆ A i := by
    intro i
    by_cases hi : i = i₀
    · rw [hi]
      simp only [C, hj₂, Finset.singleton_subset_iff, update_same]
    · simp only [C, hi, update_noteq, Ne, not_false_iff, Finset.Subset.refl]
  -- split the sum at `i₀` as the sum over `B i₀` plus the sum over `C i₀`, to use additivity.
  have A_eq_BC :
    (fun i => ∑ j ∈ A i, g i j) =
      Function.update (fun i => ∑ j ∈ A i, g i j) i₀
        ((∑ j ∈ B i₀, g i₀ j) + ∑ j ∈ C i₀, g i₀ j) := by
    ext i
    by_cases hi : i = i₀
    · rw [hi, update_same]
      have : A i₀ = B i₀ ∪ C i₀ := by
        simp only [B, C, Function.update_same, Finset.sdiff_union_self_eq_union]
        symm
        simp only [hj₂, Finset.singleton_subset_iff, Finset.union_eq_left]
      rw [this]
      refine Finset.sum_union <| Finset.disjoint_right.2 fun j hj => ?_
      have : j = j₂ := by
        simpa [C] using hj
      rw [this]
      simp only [B, mem_sdiff, eq_self_iff_true, not_true, not_false_iff, Finset.mem_singleton,
        update_same, and_false_iff]
    · simp [hi]
  have Beq :
    Function.update (fun i => ∑ j ∈ A i, g i j) i₀ (∑ j ∈ B i₀, g i₀ j) = fun i =>
      ∑ j ∈ B i, g i j := by
    ext i
    by_cases hi : i = i₀
    · rw [hi]
      simp only [update_same]
    · simp only [B, hi, update_noteq, Ne, not_false_iff]
  have Ceq :
    Function.update (fun i => ∑ j ∈ A i, g i j) i₀ (∑ j ∈ C i₀, g i₀ j) = fun i =>
      ∑ j ∈ C i, g i j := by
    ext i
    by_cases hi : i = i₀
    · rw [hi]
      simp only [update_same]
    · simp only [C, hi, update_noteq, Ne, not_false_iff]
  -- Express the inductive assumption for `B`
  have Brec : (f fun i => ∑ j ∈ B i, g i j) = ∑ r ∈ piFinset B, f fun i => g i (r i) := by
    have : (∑ i, Finset.card (B i)) < ∑ i, Finset.card (A i) := by
      refine
        Finset.sum_lt_sum (fun i _ => Finset.card_le_card (B_subset_A i))
          ⟨i₀, Finset.mem_univ _, ?_⟩
      have : {j₂} ⊆ A i₀ := by simp [hj₂]
      simp only [B, Finset.card_sdiff this, Function.update_same, Finset.card_singleton]
      exact Nat.pred_lt (ne_of_gt (lt_trans Nat.zero_lt_one hi₀))
    rw [h] at this
    exact IH _ this B rfl
  -- Express the inductive assumption for `C`
  have Crec : (f fun i => ∑ j ∈ C i, g i j) = ∑ r ∈ piFinset C, f fun i => g i (r i) := by
    have : (∑ i, Finset.card (C i)) < ∑ i, Finset.card (A i) :=
      Finset.sum_lt_sum (fun i _ => Finset.card_le_card (C_subset_A i))
        ⟨i₀, Finset.mem_univ _, by simp [C, hi₀]⟩
    rw [h] at this
    exact IH _ this C rfl
  have D : Disjoint (piFinset B) (piFinset C) :=
    haveI : Disjoint (B i₀) (C i₀) := by simp [B, C]
    piFinset_disjoint_of_disjoint B C this
  have pi_BC : piFinset A = piFinset B ∪ piFinset C := by
    apply Finset.Subset.antisymm
    · intro r hr
      by_cases hri₀ : r i₀ = j₂
      · apply Finset.mem_union_right
        refine mem_piFinset.2 fun i => ?_
        by_cases hi : i = i₀
        · have : r i₀ ∈ C i₀ := by simp [C, hri₀]
          rwa [hi]
        · simp [C, hi, mem_piFinset.1 hr i]
      · apply Finset.mem_union_left
        refine mem_piFinset.2 fun i => ?_
        by_cases hi : i = i₀
        · have : r i₀ ∈ B i₀ := by simp [B, hri₀, mem_piFinset.1 hr i₀]
          rwa [hi]
        · simp [B, hi, mem_piFinset.1 hr i]
    · exact
        Finset.union_subset (piFinset_subset _ _ fun i => B_subset_A i)
          (piFinset_subset _ _ fun i => C_subset_A i)
  rw [A_eq_BC]
  simp only [MultilinearMap.map_add, Beq, Ceq, Brec, Crec, pi_BC]
  rw [← Finset.sum_union D]
#align multilinear_map.map_sum_finset_aux MultilinearMap.map_sum_finset_aux

/-- If `f` is multilinear, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r 1 ∈ A₁`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with respect to each
coordinate. -/
theorem map_sum_finset [DecidableEq ι] [Fintype ι] :
    (f fun i => ∑ j ∈ A i, g i j) = ∑ r ∈ piFinset A, f fun i => g i (r i) :=
  f.map_sum_finset_aux _ _ rfl
#align multilinear_map.map_sum_finset MultilinearMap.map_sum_finset

/-- If `f` is multilinear, then `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions `r`. This follows from
multilinearity by expanding successively with respect to each coordinate. -/
theorem map_sum [DecidableEq ι] [Fintype ι] [∀ i, Fintype (α i)] :
    (f fun i => ∑ j, g i j) = ∑ r : ∀ i, α i, f fun i => g i (r i) :=
  f.map_sum_finset g fun _ => Finset.univ
#align multilinear_map.map_sum MultilinearMap.map_sum

theorem map_update_sum {α : Type*} [DecidableEq ι] (t : Finset α) (i : ι) (g : α → M₁ i)
    (m : ∀ i, M₁ i) : f (update m i (∑ a ∈ t, g a)) = ∑ a ∈ t, f (update m i (g a)) := by
  classical
    induction' t using Finset.induction with a t has ih h
    · simp
    · simp [Finset.sum_insert has, ih]
#align multilinear_map.map_update_sum MultilinearMap.map_update_sum

end ApplySum

/-- Restrict the codomain of a multilinear map to a submodule.

This is the multilinear version of `LinearMap.codRestrict`. -/
@[simps]
def codRestrict (f : MultilinearMap R M₁ M₂) (p : Submodule R M₂) (h : ∀ v, f v ∈ p) :
    MultilinearMap R M₁ p where
  toFun v := ⟨f v, h v⟩
  map_add' _ _ _ _ := Subtype.ext <| MultilinearMap.map_add _ _ _ _ _
  map_smul' _ _ _ _ := Subtype.ext <| MultilinearMap.map_smul _ _ _ _ _
#align multilinear_map.cod_restrict MultilinearMap.codRestrict
#align multilinear_map.cod_restrict_apply_coe MultilinearMap.codRestrict_apply_coe

section RestrictScalar

variable (R)
variable {A : Type*} [Semiring A] [SMul R A] [∀ i : ι, Module A (M₁ i)] [Module A M₂]
  [∀ i, IsScalarTower R A (M₁ i)] [IsScalarTower R A M₂]

/-- Reinterpret an `A`-multilinear map as an `R`-multilinear map, if `A` is an algebra over `R`
and their actions on all involved modules agree with the action of `R` on `A`. -/
def restrictScalars (f : MultilinearMap A M₁ M₂) : MultilinearMap R M₁ M₂ where
  toFun := f
  map_add' := f.map_add
  map_smul' m i := (f.toLinearMap m i).map_smul_of_tower
#align multilinear_map.restrict_scalars MultilinearMap.restrictScalars

@[simp]
theorem coe_restrictScalars (f : MultilinearMap A M₁ M₂) : ⇑(f.restrictScalars R) = f :=
  rfl
#align multilinear_map.coe_restrict_scalars MultilinearMap.coe_restrictScalars

end RestrictScalar

section

variable {ι₁ ι₂ ι₃ : Type*}

/-- Transfer the arguments to a map along an equivalence between argument indices.

The naming is derived from `Finsupp.domCongr`, noting that here the permutation applies to the
domain of the domain. -/
@[simps apply]
def domDomCongr (σ : ι₁ ≃ ι₂) (m : MultilinearMap R (fun _ : ι₁ => M₂) M₃) :
    MultilinearMap R (fun _ : ι₂ => M₂) M₃ where
  toFun v := m fun i => v (σ i)
  map_add' v i a b := by
    letI := σ.injective.decidableEq
    simp_rw [Function.update_apply_equiv_apply v]
    rw [m.map_add]
  map_smul' v i a b := by
    letI := σ.injective.decidableEq
    simp_rw [Function.update_apply_equiv_apply v]
    rw [m.map_smul]
#align multilinear_map.dom_dom_congr MultilinearMap.domDomCongr
#align multilinear_map.dom_dom_congr_apply MultilinearMap.domDomCongr_apply

theorem domDomCongr_trans (σ₁ : ι₁ ≃ ι₂) (σ₂ : ι₂ ≃ ι₃)
    (m : MultilinearMap R (fun _ : ι₁ => M₂) M₃) :
    m.domDomCongr (σ₁.trans σ₂) = (m.domDomCongr σ₁).domDomCongr σ₂ :=
  rfl
#align multilinear_map.dom_dom_congr_trans MultilinearMap.domDomCongr_trans

theorem domDomCongr_mul (σ₁ : Equiv.Perm ι₁) (σ₂ : Equiv.Perm ι₁)
    (m : MultilinearMap R (fun _ : ι₁ => M₂) M₃) :
    m.domDomCongr (σ₂ * σ₁) = (m.domDomCongr σ₁).domDomCongr σ₂ :=
  rfl
#align multilinear_map.dom_dom_congr_mul MultilinearMap.domDomCongr_mul

/-- `MultilinearMap.domDomCongr` as an equivalence.

This is declared separately because it does not work with dot notation. -/
@[simps apply symm_apply]
def domDomCongrEquiv (σ : ι₁ ≃ ι₂) :
    MultilinearMap R (fun _ : ι₁ => M₂) M₃ ≃+ MultilinearMap R (fun _ : ι₂ => M₂) M₃ where
  toFun := domDomCongr σ
  invFun := domDomCongr σ.symm
  left_inv m := by
    ext
    simp [domDomCongr]
  right_inv m := by
    ext
    simp [domDomCongr]
  map_add' a b := by
    ext
    simp [domDomCongr]
#align multilinear_map.dom_dom_congr_equiv MultilinearMap.domDomCongrEquiv
#align multilinear_map.dom_dom_congr_equiv_apply MultilinearMap.domDomCongrEquiv_apply
#align multilinear_map.dom_dom_congr_equiv_symm_apply MultilinearMap.domDomCongrEquiv_symm_apply

/-- The results of applying `domDomCongr` to two maps are equal if
and only if those maps are. -/
@[simp]
theorem domDomCongr_eq_iff (σ : ι₁ ≃ ι₂) (f g : MultilinearMap R (fun _ : ι₁ => M₂) M₃) :
    f.domDomCongr σ = g.domDomCongr σ ↔ f = g :=
  (domDomCongrEquiv σ : _ ≃+ MultilinearMap R (fun _ => M₂) M₃).apply_eq_iff_eq
#align multilinear_map.dom_dom_congr_eq_iff MultilinearMap.domDomCongr_eq_iff

end

/-! If `{a // P a}` is a subtype of `ι` and if we fix an element `z` of `(i : {a // ¬ P a}) → M₁ i`,
then a multilinear map on `M₁` defines a multilinear map on the restriction of `M₁` to
`{a // P a}`, by fixing the arguments out of `{a // P a}` equal to the values of `z`. -/

lemma domDomRestrict_aux [DecidableEq ι] (P : ι → Prop) [DecidablePred P]
    [DecidableEq {a // P a}]
    (x : (i : {a // P a}) → M₁ i) (z : (i : {a // ¬ P a}) → M₁ i) (i : {a : ι // P a})
    (c : M₁ i) : (fun j ↦ if h : P j then Function.update x i c ⟨j, h⟩ else z ⟨j, h⟩) =
    Function.update (fun j => if h : P j then x ⟨j, h⟩ else z ⟨j, h⟩) i c := by
  ext j
  by_cases h : j = i
  · rw [h, Function.update_same]
    simp only [i.2, update_same, dite_true]
  · rw [Function.update_noteq h]
    by_cases h' : P j
    · simp only [h', ne_eq, Subtype.mk.injEq, dite_true]
      have h'' : ¬ ⟨j, h'⟩ = i :=
        fun he => by apply_fun (fun x => x.1) at he; exact h he
      rw [Function.update_noteq h'']
    · simp only [h', ne_eq, Subtype.mk.injEq, dite_false]

lemma domDomRestrict_aux_right [DecidableEq ι] (P : ι → Prop) [DecidablePred P]
    [DecidableEq {a // ¬ P a}]
    (x : (i : {a // P a}) → M₁ i) (z : (i : {a // ¬ P a}) → M₁ i) (i : {a : ι // ¬ P a})
    (c : M₁ i) : (fun j ↦ if h : P j then x ⟨j, h⟩ else Function.update z i c ⟨j, h⟩) =
    Function.update (fun j => if h : P j then x ⟨j, h⟩ else z ⟨j, h⟩) i c := by
  simpa only [dite_not] using domDomRestrict_aux _ z (fun j ↦ x ⟨j.1, not_not.mp j.2⟩) i c

/-- Given a multilinear map `f` on `(i : ι) → M i`, a (decidable) predicate `P` on `ι` and
an element `z` of `(i : {a // ¬ P a}) → M₁ i`, construct a multilinear map on
`(i : {a // P a}) → M₁ i)` whose value at `x` is `f` evaluated at the vector with `i`th coordinate
`x i` if `P i` and `z i` otherwise.

The naming is similar to `MultilinearMap.domDomCongr`: here we are applying the restriction to the
domain of the domain.

For a linear map version, see `MultilinearMap.domDomRestrictₗ`.
-/
def domDomRestrict (f : MultilinearMap R M₁ M₂) (P : ι → Prop) [DecidablePred P]
    (z : (i : {a : ι // ¬ P a}) → M₁ i) :
    MultilinearMap R (fun (i : {a : ι // P a}) => M₁ i) M₂ where
  toFun x := f (fun j ↦ if h : P j then x ⟨j, h⟩ else z ⟨j, h⟩)
  map_add' x i a b := by
    classical
    simp only
    repeat (rw [domDomRestrict_aux])
    simp only [MultilinearMap.map_add]
  map_smul' z i c a := by
    classical
    simp only
    repeat (rw [domDomRestrict_aux])
    simp only [MultilinearMap.map_smul]

@[simp]
lemma domDomRestrict_apply (f : MultilinearMap R M₁ M₂) (P : ι → Prop)
    [DecidablePred P] (x : (i : {a // P a}) → M₁ i) (z : (i : {a // ¬ P a}) → M₁ i) :
    f.domDomRestrict P z x = f (fun j => if h : P j then x ⟨j, h⟩ else z ⟨j, h⟩) := rfl

-- TODO: Should add a ref here when available.
/-- The "derivative" of a multilinear map, as a linear map from `(i : ι) → M₁ i` to `M₂`.
For continuous multilinear maps, this will indeed be the derivative. -/
def linearDeriv [DecidableEq ι] [Fintype ι] (f : MultilinearMap R M₁ M₂)
    (x : (i : ι) → M₁ i) : ((i : ι) → M₁ i) →ₗ[R] M₂ :=
  ∑ i : ι, (f.toLinearMap x i).comp (LinearMap.proj i)

@[simp]
lemma linearDeriv_apply [DecidableEq ι] [Fintype ι] (f : MultilinearMap R M₁ M₂)
    (x y : (i : ι) → M₁ i) :
    f.linearDeriv x y = ∑ i, f (update x i (y i)) := by
  unfold linearDeriv
  simp only [LinearMap.coeFn_sum, LinearMap.coe_comp, LinearMap.coe_proj, Finset.sum_apply,
    Function.comp_apply, Function.eval, toLinearMap_apply]

end Semiring

end MultilinearMap

namespace LinearMap

variable [Semiring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [AddCommMonoid M'] [∀ i, Module R (M₁ i)] [Module R M₂] [Module R M₃] [Module R M']

/-- Composing a multilinear map with a linear map gives again a multilinear map. -/
def compMultilinearMap (g : M₂ →ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) : MultilinearMap R M₁ M₃ where
  toFun := g ∘ f
  map_add' m i x y := by simp
  map_smul' m i c x := by simp
#align linear_map.comp_multilinear_map LinearMap.compMultilinearMap

@[simp]
theorem coe_compMultilinearMap (g : M₂ →ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) :
    ⇑(g.compMultilinearMap f) = g ∘ f :=
  rfl
#align linear_map.coe_comp_multilinear_map LinearMap.coe_compMultilinearMap

@[simp]
theorem compMultilinearMap_apply (g : M₂ →ₗ[R] M₃) (f : MultilinearMap R M₁ M₂) (m : ∀ i, M₁ i) :
    g.compMultilinearMap f m = g (f m) :=
  rfl
#align linear_map.comp_multilinear_map_apply LinearMap.compMultilinearMap_apply

/-- The multilinear version of `LinearMap.subtype_comp_codRestrict` -/
@[simp]
theorem subtype_compMultilinearMap_codRestrict (f : MultilinearMap R M₁ M₂) (p : Submodule R M₂)
    (h) : p.subtype.compMultilinearMap (f.codRestrict p h) = f :=
  MultilinearMap.ext fun _ => rfl
#align linear_map.subtype_comp_multilinear_map_cod_restrict LinearMap.subtype_compMultilinearMap_codRestrict

/-- The multilinear version of `LinearMap.comp_codRestrict` -/
@[simp]
theorem compMultilinearMap_codRestrict (g : M₂ →ₗ[R] M₃) (f : MultilinearMap R M₁ M₂)
    (p : Submodule R M₃) (h) :
    (g.codRestrict p h).compMultilinearMap f =
      (g.compMultilinearMap f).codRestrict p fun v => h (f v) :=
  MultilinearMap.ext fun _ => rfl
#align linear_map.comp_multilinear_map_cod_restrict LinearMap.compMultilinearMap_codRestrict

variable {ι₁ ι₂ : Type*}

@[simp]
theorem compMultilinearMap_domDomCongr (σ : ι₁ ≃ ι₂) (g : M₂ →ₗ[R] M₃)
    (f : MultilinearMap R (fun _ : ι₁ => M') M₂) :
    (g.compMultilinearMap f).domDomCongr σ = g.compMultilinearMap (f.domDomCongr σ) := by
  ext
  simp [MultilinearMap.domDomCongr]
#align linear_map.comp_multilinear_map_dom_dom_congr LinearMap.compMultilinearMap_domDomCongr

end LinearMap

namespace MultilinearMap

section Semiring

variable [Semiring R] [(i : ι) → AddCommMonoid (M₁ i)] [(i : ι) → Module R (M₁ i)]
  [AddCommMonoid M₂] [Module R M₂]

instance [Monoid S] [DistribMulAction S M₂] [Module R M₂] [SMulCommClass R S M₂] :
    DistribMulAction S (MultilinearMap R M₁ M₂) :=
  coe_injective.distribMulAction coeAddMonoidHom fun _ _ ↦ rfl

section Module

variable [Semiring S] [Module S M₂] [SMulCommClass R S M₂]

/-- The space of multilinear maps over an algebra over `R` is a module over `R`, for the pointwise
addition and scalar multiplication. -/
instance : Module S (MultilinearMap R M₁ M₂) :=
  coe_injective.module _ coeAddMonoidHom fun _ _ ↦ rfl

instance [NoZeroSMulDivisors S M₂] : NoZeroSMulDivisors S (MultilinearMap R M₁ M₂) :=
  coe_injective.noZeroSMulDivisors _ rfl coe_smul

variable (R S M₁ M₂ M₃)

section OfSubsingleton

variable [AddCommMonoid M₃] [Module S M₃] [Module R M₃] [SMulCommClass R S M₃]

/-- Linear equivalence between linear maps `M₂ →ₗ[R] M₃`
and one-multilinear maps `MultilinearMap R (fun _ : ι ↦ M₂) M₃`. -/
@[simps (config := { simpRhs := true })]
def ofSubsingletonₗ [Subsingleton ι] (i : ι) :
    (M₂ →ₗ[R] M₃) ≃ₗ[S] MultilinearMap R (fun _ : ι ↦ M₂) M₃ :=
  { ofSubsingleton R M₂ M₃ i with
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }

end OfSubsingleton

/-- The dependent version of `MultilinearMap.domDomCongrLinearEquiv`. -/
@[simps apply symm_apply]
def domDomCongrLinearEquiv' {ι' : Type*} (σ : ι ≃ ι') :
    MultilinearMap R M₁ M₂ ≃ₗ[S] MultilinearMap R (fun i => M₁ (σ.symm i)) M₂ where
  toFun f :=
    { toFun := f ∘ (σ.piCongrLeft' M₁).symm
      map_add' := fun m i => by
        letI := σ.decidableEq
        rw [← σ.apply_symm_apply i]
        intro x y
        simp only [comp_apply, piCongrLeft'_symm_update, f.map_add]
      map_smul' := fun m i c => by
        letI := σ.decidableEq
        rw [← σ.apply_symm_apply i]
        intro x
        simp only [Function.comp, piCongrLeft'_symm_update, f.map_smul] }
  invFun f :=
    { toFun := f ∘ σ.piCongrLeft' M₁
      map_add' := fun m i => by
        letI := σ.symm.decidableEq
        rw [← σ.symm_apply_apply i]
        intro x y
        simp only [comp_apply, piCongrLeft'_update, f.map_add]
      map_smul' := fun m i c => by
        letI := σ.symm.decidableEq
        rw [← σ.symm_apply_apply i]
        intro x
        simp only [Function.comp, piCongrLeft'_update, f.map_smul] }
  map_add' f₁ f₂ := by
    ext
    simp only [Function.comp, coe_mk, add_apply]
  map_smul' c f := by
    ext
    simp only [Function.comp, coe_mk, smul_apply, RingHom.id_apply]
  left_inv f := by
    ext
    simp only [coe_mk, comp_apply, Equiv.symm_apply_apply]
  right_inv f := by
    ext
    simp only [coe_mk, comp_apply, Equiv.apply_symm_apply]
#align multilinear_map.dom_dom_congr_linear_equiv' MultilinearMap.domDomCongrLinearEquiv'
#align multilinear_map.dom_dom_congr_linear_equiv'_apply MultilinearMap.domDomCongrLinearEquiv'_apply
#align multilinear_map.dom_dom_congr_linear_equiv'_symm_apply MultilinearMap.domDomCongrLinearEquiv'_symm_apply

/-- The space of constant maps is equivalent to the space of maps that are multilinear with respect
to an empty family. -/
@[simps]
def constLinearEquivOfIsEmpty [IsEmpty ι] : M₂ ≃ₗ[S] MultilinearMap R M₁ M₂ where
  toFun := MultilinearMap.constOfIsEmpty R _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := f 0
  left_inv _ := rfl
  right_inv f := ext fun _ => MultilinearMap.congr_arg f <| Subsingleton.elim _ _
#align multilinear_map.const_linear_equiv_of_is_empty MultilinearMap.constLinearEquivOfIsEmpty
#align multilinear_map.const_linear_equiv_of_is_empty_apply_to_add_hom_apply MultilinearMap.constLinearEquivOfIsEmpty_apply
#align multilinear_map.const_linear_equiv_of_is_empty_apply_to_add_hom_symm_apply MultilinearMap.constLinearEquivOfIsEmpty_symm_apply

variable [AddCommMonoid M₃] [Module R M₃] [Module S M₃] [SMulCommClass R S M₃]

/-- `MultilinearMap.domDomCongr` as a `LinearEquiv`. -/
@[simps apply symm_apply]
def domDomCongrLinearEquiv {ι₁ ι₂} (σ : ι₁ ≃ ι₂) :
    MultilinearMap R (fun _ : ι₁ => M₂) M₃ ≃ₗ[S] MultilinearMap R (fun _ : ι₂ => M₂) M₃ :=
  { (domDomCongrEquiv σ :
      MultilinearMap R (fun _ : ι₁ => M₂) M₃ ≃+ MultilinearMap R (fun _ : ι₂ => M₂) M₃) with
    map_smul' := fun c f => by
      ext
      simp [MultilinearMap.domDomCongr] }
#align multilinear_map.dom_dom_congr_linear_equiv MultilinearMap.domDomCongrLinearEquiv
#align multilinear_map.dom_dom_congr_linear_equiv_apply MultilinearMap.domDomCongrLinearEquiv_apply
#align multilinear_map.dom_dom_congr_linear_equiv_symm_apply MultilinearMap.domDomCongrLinearEquiv_symm_apply

end Module

end Semiring

section CommSemiring

variable [CommSemiring R] [∀ i, AddCommMonoid (M₁ i)] [∀ i, AddCommMonoid (M i)] [AddCommMonoid M₂]
  [∀ i, Module R (M i)] [∀ i, Module R (M₁ i)] [Module R M₂] (f f' : MultilinearMap R M₁ M₂)

section
variable {M₁' : ι → Type*} [Π i, AddCommMonoid (M₁' i)] [Π i, Module R (M₁' i)]

/-- Given a predicate `P`, one may associate to a multilinear map `f` a multilinear map
from the elements satisfying `P` to the multilinear maps on elements not satisfying `P`.
In other words, splitting the variables into two subsets one gets a multilinear map into
multilinear maps.
This is a linear map version of the function `MultilinearMap.domDomRestrict`. -/
def domDomRestrictₗ (f : MultilinearMap R M₁ M₂) (P : ι → Prop) [DecidablePred P] :
    MultilinearMap R (fun (i : {a : ι // ¬ P a}) => M₁ i)
      (MultilinearMap R (fun (i : {a : ι // P a}) => M₁ i) M₂) where
  toFun := fun z ↦ domDomRestrict f P z
  map_add' := by
    intro h m i x y
    classical
    ext v
    simp [domDomRestrict_aux_right]
  map_smul' := by
    intro h m i c x
    classical
    ext v
    simp [domDomRestrict_aux_right]

lemma iteratedFDeriv_aux {α : Type*} [DecidableEq α]
    (s : Set ι) [DecidableEq { x // x ∈ s }] (e : α ≃ s)
    (m : α → ((i : ι) → M₁ i)) (a : α) (z : (i : ι) → M₁ i) :
    (fun i ↦ update m a z (e.symm i) i) =
      (fun i ↦ update (fun j ↦ m (e.symm j) j) (e a) (z (e a)) i) := by
  ext i
  rcases eq_or_ne a (e.symm i) with rfl | hne
  · rw [Equiv.apply_symm_apply e i, update_same, update_same]
  · rw [update_noteq hne.symm, update_noteq fun h ↦ (Equiv.symm_apply_apply .. ▸ h ▸ hne) rfl]

/-- One of the components of the iterated derivative of a multilinear map. Given a bijection `e`
between a type `α` (typically `Fin k`) and a subset `s` of `ι`, this component is a multilinear map
of `k` vectors `v₁, ..., vₖ`, mapping them to `f (x₁, (v_{e.symm 2})₂, x₃, ...)`, where at
indices `i` in `s` one uses the `i`-th coordinate of the vector `v_{e.symm i}` and otherwise one
uses the `i`-th coordinate of a reference vector `x`.
This is multilinear in the components of `x` outside of `s`, and in the `v_j`. -/
noncomputable def iteratedFDerivComponent {α : Type*}
    (f : MultilinearMap R M₁ M₂) {s : Set ι} (e : α ≃ s) [DecidablePred (· ∈ s)] :
    MultilinearMap R (fun (i : {a : ι // a ∉ s}) ↦ M₁ i)
      (MultilinearMap R (fun (_ : α) ↦ (∀ i, M₁ i)) M₂) where
  toFun := fun z ↦
    { toFun := fun v ↦ domDomRestrictₗ f (fun i ↦ i ∈ s) z (fun i ↦ v (e.symm i) i)
      map_add' := by classical simp [iteratedFDeriv_aux]
      map_smul' := by classical simp [iteratedFDeriv_aux] }
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

open Classical in
/-- The `k`-th iterated derivative of a multilinear map `f` at the point `x`. It is a multilinear
map of `k` vectors `v₁, ..., vₖ` (with the same type as `x`), mapping them
to `∑ f (x₁, (v_{i₁})₂, x₃, ...)`, where at each index `j` one uses either `xⱼ` or one
of the `(vᵢ)ⱼ`, and each `vᵢ` has to be used exactly once.
The sum is parameterized by the embeddings of `Fin k` in the index type `ι` (or, equivalently,
by the subsets `s` of `ι` of cardinality `k` and then the bijections between `Fin k` and `s`).

For the continuous version, see `ContinuousMultilinearMap.iteratedFDeriv`. -/
protected noncomputable def iteratedFDeriv [Fintype ι]
    (f : MultilinearMap R M₁ M₂) (k : ℕ) (x : (i : ι) → M₁ i) :
    MultilinearMap R (fun (_ : Fin k) ↦ (∀ i, M₁ i)) M₂ :=
  ∑ e : Fin k ↪ ι, iteratedFDerivComponent f e.toEquivRange (fun i ↦ x i)

/-- If `f` is a collection of linear maps, then the construction `MultilinearMap.compLinearMap`
sending a multilinear map `g` to `g (f₁ ⬝ , ..., fₙ ⬝ )` is linear in `g`. -/
@[simps] def compLinearMapₗ (f : Π (i : ι), M₁ i →ₗ[R] M₁' i) :
    (MultilinearMap R M₁' M₂) →ₗ[R] MultilinearMap R M₁ M₂ where
  toFun := fun g ↦ g.compLinearMap f
  map_add' := fun _ _ ↦ rfl
  map_smul' := fun _ _ ↦ rfl

/-- If `f` is a collection of linear maps, then the construction `MultilinearMap.compLinearMap`
sending a multilinear map `g` to `g (f₁ ⬝ , ..., fₙ ⬝ )` is linear in `g` and multilinear in
`f₁, ..., fₙ`. -/
@[simps] def compLinearMapMultilinear :
  @MultilinearMap R ι (fun i ↦ M₁ i →ₗ[R] M₁' i)
    ((MultilinearMap R M₁' M₂) →ₗ[R] MultilinearMap R M₁ M₂) _ _ _
      (fun i ↦ LinearMap.module) _ where
  toFun := MultilinearMap.compLinearMapₗ
  map_add' := by
    intro _ f i f₁ f₂
    ext g x
    change (g fun j ↦ update f i (f₁ + f₂) j <| x j) =
        (g fun j ↦ update f i f₁ j <|x j) + g fun j ↦ update f i f₂ j (x j)
    let c : Π (i : ι), (M₁ i →ₗ[R] M₁' i) → M₁' i := fun i f ↦ f (x i)
    convert g.map_add (fun j ↦ f j (x j)) i (f₁ (x i)) (f₂ (x i)) with j j j
    · exact Function.apply_update c f i (f₁ + f₂) j
    · exact Function.apply_update c f i f₁ j
    · exact Function.apply_update c f i f₂ j
  map_smul' := by
    intro _ f i a f₀
    ext g x
    change (g fun j ↦ update f i (a • f₀) j <| x j) = a • g fun j ↦ update f i f₀ j (x j)
    let c : Π (i : ι), (M₁ i →ₗ[R] M₁' i) → M₁' i := fun i f ↦ f (x i)
    convert g.map_smul (fun j ↦ f j (x j)) i a (f₀ (x i)) with j j j
    · exact Function.apply_update c f i (a • f₀) j
    · exact Function.apply_update c f i f₀ j

/--
Let `M₁ᵢ` and `M₁ᵢ'` be two families of `R`-modules and `M₂` an `R`-module.
Let us denote `Π i, M₁ᵢ` and `Π i, M₁ᵢ'` by `M` and `M'` respectively.
If `g` is a multilinear map `M' → M₂`, then `g` can be reinterpreted as a multilinear
map from `Π i, M₁ᵢ ⟶ M₁ᵢ'` to `M ⟶ M₂` via `(fᵢ) ↦ v ↦ g(fᵢ vᵢ)`.
-/
@[simps!] def piLinearMap :
    MultilinearMap R M₁' M₂ →ₗ[R]
    MultilinearMap R (fun i ↦ M₁ i →ₗ[R] M₁' i) (MultilinearMap R M₁ M₂) where
  toFun g := (LinearMap.applyₗ g).compMultilinearMap compLinearMapMultilinear
  map_add' := by aesop
  map_smul' := by aesop

end

/-- If one multiplies by `c i` the coordinates in a finset `s`, then the image under a multilinear
map is multiplied by `∏ i ∈ s, c i`. This is mainly an auxiliary statement to prove the result when
`s = univ`, given in `map_smul_univ`, although it can be useful in its own right as it does not
require the index set `ι` to be finite. -/
theorem map_piecewise_smul [DecidableEq ι] (c : ι → R) (m : ∀ i, M₁ i) (s : Finset ι) :
    f (s.piecewise (fun i => c i • m i) m) = (∏ i ∈ s, c i) • f m := by
  refine s.induction_on (by simp) ?_
  intro j s j_not_mem_s Hrec
  have A :
    Function.update (s.piecewise (fun i => c i • m i) m) j (m j) =
      s.piecewise (fun i => c i • m i) m := by
    ext i
    by_cases h : i = j
    · rw [h]
      simp [j_not_mem_s]
    · simp [h]
  rw [s.piecewise_insert, f.map_smul, A, Hrec]
  simp [j_not_mem_s, mul_smul]
#align multilinear_map.map_piecewise_smul MultilinearMap.map_piecewise_smul

/-- Multiplicativity of a multilinear map along all coordinates at the same time,
writing `f (fun i => c i • m i)` as `(∏ i, c i) • f m`. -/
theorem map_smul_univ [Fintype ι] (c : ι → R) (m : ∀ i, M₁ i) :
    (f fun i => c i • m i) = (∏ i, c i) • f m := by
  classical simpa using map_piecewise_smul f c m Finset.univ
#align multilinear_map.map_smul_univ MultilinearMap.map_smul_univ

@[simp]
theorem map_update_smul [DecidableEq ι] [Fintype ι] (m : ∀ i, M₁ i) (i : ι) (c : R) (x : M₁ i) :
    f (update (c • m) i x) = c ^ (Fintype.card ι - 1) • f (update m i x) := by
  have :
    f ((Finset.univ.erase i).piecewise (c • update m i x) (update m i x)) =
      (∏ _i ∈ Finset.univ.erase i, c) • f (update m i x) :=
    map_piecewise_smul f _ _ _
  simpa [← Function.update_smul c m] using this
#align multilinear_map.map_update_smul MultilinearMap.map_update_smul

section

variable (R ι)
variable (A : Type*) [CommSemiring A] [Algebra R A] [Fintype ι]

/-- Given an `R`-algebra `A`, `mkPiAlgebra` is the multilinear map on `A^ι` associating
to `m` the product of all the `m i`.

See also `MultilinearMap.mkPiAlgebraFin` for a version that works with a non-commutative
algebra `A` but requires `ι = Fin n`. -/
protected def mkPiAlgebra : MultilinearMap R (fun _ : ι => A) A where
  toFun m := ∏ i, m i
  map_add' m i x y := by simp [Finset.prod_update_of_mem, add_mul]
  map_smul' m i c x := by simp [Finset.prod_update_of_mem]
#align multilinear_map.mk_pi_algebra MultilinearMap.mkPiAlgebra

variable {R A ι}

@[simp]
theorem mkPiAlgebra_apply (m : ι → A) : MultilinearMap.mkPiAlgebra R ι A m = ∏ i, m i :=
  rfl
#align multilinear_map.mk_pi_algebra_apply MultilinearMap.mkPiAlgebra_apply

end

section

variable (R n)
variable (A : Type*) [Semiring A] [Algebra R A]

/-- Given an `R`-algebra `A`, `mkPiAlgebraFin` is the multilinear map on `A^n` associating
to `m` the product of all the `m i`.

See also `MultilinearMap.mkPiAlgebra` for a version that assumes `[CommSemiring A]` but works
for `A^ι` with any finite type `ι`. -/
protected def mkPiAlgebraFin : MultilinearMap R (fun _ : Fin n => A) A where
  toFun m := (List.ofFn m).prod
  map_add' {dec} m i x y := by
    rw [Subsingleton.elim dec (by infer_instance)]
    have : (List.finRange n).indexOf i < n := by
      simpa using List.indexOf_lt_length.2 (List.mem_finRange i)
    simp [List.ofFn_eq_map, (List.nodup_finRange n).map_update, List.prod_set, add_mul, this,
      mul_add, add_mul]
  map_smul' {dec} m i c x := by
    rw [Subsingleton.elim dec (by infer_instance)]
    have : (List.finRange n).indexOf i < n := by
      simpa using List.indexOf_lt_length.2 (List.mem_finRange i)
    simp [List.ofFn_eq_map, (List.nodup_finRange n).map_update, List.prod_set, this]
#align multilinear_map.mk_pi_algebra_fin MultilinearMap.mkPiAlgebraFin

variable {R A n}

@[simp]
theorem mkPiAlgebraFin_apply (m : Fin n → A) :
    MultilinearMap.mkPiAlgebraFin R n A m = (List.ofFn m).prod :=
  rfl
#align multilinear_map.mk_pi_algebra_fin_apply MultilinearMap.mkPiAlgebraFin_apply

theorem mkPiAlgebraFin_apply_const (a : A) :
    (MultilinearMap.mkPiAlgebraFin R n A fun _ => a) = a ^ n := by simp
#align multilinear_map.mk_pi_algebra_fin_apply_const MultilinearMap.mkPiAlgebraFin_apply_const

end

/-- Given an `R`-multilinear map `f` taking values in `R`, `f.smulRight z` is the map
sending `m` to `f m • z`. -/
def smulRight (f : MultilinearMap R M₁ R) (z : M₂) : MultilinearMap R M₁ M₂ :=
  (LinearMap.smulRight LinearMap.id z).compMultilinearMap f
#align multilinear_map.smul_right MultilinearMap.smulRight

@[simp]
theorem smulRight_apply (f : MultilinearMap R M₁ R) (z : M₂) (m : ∀ i, M₁ i) :
    f.smulRight z m = f m • z :=
  rfl
#align multilinear_map.smul_right_apply MultilinearMap.smulRight_apply

variable (R ι)

/-- The canonical multilinear map on `R^ι` when `ι` is finite, associating to `m` the product of
all the `m i` (multiplied by a fixed reference element `z` in the target module). See also
`mkPiAlgebra` for a more general version. -/
protected def mkPiRing [Fintype ι] (z : M₂) : MultilinearMap R (fun _ : ι => R) M₂ :=
  (MultilinearMap.mkPiAlgebra R ι R).smulRight z
#align multilinear_map.mk_pi_ring MultilinearMap.mkPiRing

variable {R ι}

@[simp]
theorem mkPiRing_apply [Fintype ι] (z : M₂) (m : ι → R) :
    (MultilinearMap.mkPiRing R ι z : (ι → R) → M₂) m = (∏ i, m i) • z :=
  rfl
#align multilinear_map.mk_pi_ring_apply MultilinearMap.mkPiRing_apply

theorem mkPiRing_apply_one_eq_self [Fintype ι] (f : MultilinearMap R (fun _ : ι => R) M₂) :
    MultilinearMap.mkPiRing R ι (f fun _ => 1) = f := by
  ext m
  have : m = fun i => m i • (1 : R) := by
    ext j
    simp
  conv_rhs => rw [this, f.map_smul_univ]
  rfl
#align multilinear_map.mk_pi_ring_apply_one_eq_self MultilinearMap.mkPiRing_apply_one_eq_self

theorem mkPiRing_eq_iff [Fintype ι] {z₁ z₂ : M₂} :
    MultilinearMap.mkPiRing R ι z₁ = MultilinearMap.mkPiRing R ι z₂ ↔ z₁ = z₂ := by
  simp_rw [MultilinearMap.ext_iff, mkPiRing_apply]
  constructor <;> intro h
  · simpa using h fun _ => 1
  · intro x
    simp [h]
#align multilinear_map.mk_pi_ring_eq_iff MultilinearMap.mkPiRing_eq_iff

theorem mkPiRing_zero [Fintype ι] : MultilinearMap.mkPiRing R ι (0 : M₂) = 0 := by
  ext; rw [mkPiRing_apply, smul_zero, MultilinearMap.zero_apply]
#align multilinear_map.mk_pi_ring_zero MultilinearMap.mkPiRing_zero

theorem mkPiRing_eq_zero_iff [Fintype ι] (z : M₂) : MultilinearMap.mkPiRing R ι z = 0 ↔ z = 0 := by
  rw [← mkPiRing_zero, mkPiRing_eq_iff]
#align multilinear_map.mk_pi_ring_eq_zero_iff MultilinearMap.mkPiRing_eq_zero_iff

end CommSemiring

section RangeAddCommGroup

variable [Semiring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommGroup M₂] [∀ i, Module R (M₁ i)]
  [Module R M₂] (f g : MultilinearMap R M₁ M₂)

instance : Neg (MultilinearMap R M₁ M₂) :=
  ⟨fun f => ⟨fun m => -f m, fun m i x y => by simp [add_comm], fun m i c x => by simp⟩⟩

@[simp]
theorem neg_apply (m : ∀ i, M₁ i) : (-f) m = -f m :=
  rfl
#align multilinear_map.neg_apply MultilinearMap.neg_apply

instance : Sub (MultilinearMap R M₁ M₂) :=
  ⟨fun f g =>
    ⟨fun m => f m - g m, fun m i x y => by
      simp only [MultilinearMap.map_add, sub_eq_add_neg, neg_add]
      abel,
      fun m i c x => by simp only [MultilinearMap.map_smul, smul_sub]⟩⟩

@[simp]
theorem sub_apply (m : ∀ i, M₁ i) : (f - g) m = f m - g m :=
  rfl
#align multilinear_map.sub_apply MultilinearMap.sub_apply

instance : AddCommGroup (MultilinearMap R M₁ M₂) :=
  { MultilinearMap.addCommMonoid with
    add_left_neg := fun a => MultilinearMap.ext fun v => add_left_neg _
    sub_eq_add_neg := fun a b => MultilinearMap.ext fun v => sub_eq_add_neg _ _
    zsmul := fun n f =>
      { toFun := fun m => n • f m
        map_add' := fun m i x y => by simp [smul_add]
        map_smul' := fun l i x d => by simp [← smul_comm x n (_ : M₂)] }
    -- Porting note: changed from `AddCommGroup` to `SubNegMonoid`
    zsmul_zero' := fun a => MultilinearMap.ext fun v => SubNegMonoid.zsmul_zero' _
    zsmul_succ' := fun z a => MultilinearMap.ext fun v => SubNegMonoid.zsmul_succ' _ _
    zsmul_neg' := fun z a => MultilinearMap.ext fun v => SubNegMonoid.zsmul_neg' _ _ }

end RangeAddCommGroup

section AddCommGroup

variable [Semiring R] [∀ i, AddCommGroup (M₁ i)] [AddCommGroup M₂] [∀ i, Module R (M₁ i)]
  [Module R M₂] (f : MultilinearMap R M₁ M₂)

@[simp]
theorem map_neg [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (x : M₁ i) :
    f (update m i (-x)) = -f (update m i x) :=
  eq_neg_of_add_eq_zero_left <| by
    rw [← MultilinearMap.map_add, add_left_neg, f.map_coord_zero i (update_same i 0 m)]
#align multilinear_map.map_neg MultilinearMap.map_neg

@[simp]
theorem map_sub [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i) :
    f (update m i (x - y)) = f (update m i x) - f (update m i y) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, MultilinearMap.map_add, map_neg]
#align multilinear_map.map_sub MultilinearMap.map_sub

lemma map_update [DecidableEq ι] (x : (i : ι) → M₁ i) (i : ι) (v : M₁ i)  :
    f (update x i v) = f x - f (update x i (x i - v)) := by
  rw [map_sub, update_eq_self, sub_sub_cancel]

open Finset in
lemma map_sub_map_piecewise [LinearOrder ι] (a b : (i : ι) → M₁ i) (s : Finset ι) :
    f a - f (s.piecewise b a) =
    ∑ i ∈ s, f (fun j ↦ if j ∈ s → j < i then a j else if i = j then a j - b j else b j) := by
  refine s.induction_on_min ?_ fun k s hk ih ↦ ?_
  · rw [Finset.piecewise_empty, sum_empty, sub_self]
  rw [Finset.piecewise_insert, map_update, ← sub_add, ih,
      add_comm, sum_insert (lt_irrefl _ <| hk k ·)]
  simp_rw [s.mem_insert]
  congr 1
  · congr; ext i; split_ifs with h₁ h₂
    · rw [update_noteq, Finset.piecewise_eq_of_not_mem]
      · exact fun h ↦ (hk i h).not_lt (h₁ <| .inr h)
      · exact fun h ↦ (h₁ <| .inl h).ne h
    · cases h₂
      rw [update_same, s.piecewise_eq_of_not_mem _ _ (lt_irrefl _ <| hk k ·)]
    · push_neg at h₁
      rw [update_noteq (Ne.symm h₂), s.piecewise_eq_of_mem _ _ (h₁.1.resolve_left <| Ne.symm h₂)]
  · apply sum_congr rfl; intro i hi; congr; ext j; congr 1; apply propext
    simp_rw [imp_iff_not_or, not_or]; apply or_congr_left'
    intro h; rw [and_iff_right]; rintro rfl; exact h (hk i hi)

/-- This calculates the differences between the values of a multilinear map at
two arguments that differ on a finset `s` of `ι`. It requires a
linear order on `ι` in order to express the result. -/
lemma map_piecewise_sub_map_piecewise [LinearOrder ι] (a b v : (i : ι) → M₁ i) (s : Finset ι) :
    f (s.piecewise a v) - f (s.piecewise b v) = ∑ i ∈ s, f
      fun j ↦ if j ∈ s then if j < i then a j else if j = i then a j - b j else b j else v j := by
  rw [← s.piecewise_idem_right b a, map_sub_map_piecewise]
  refine Finset.sum_congr rfl fun i hi ↦ congr_arg f <| funext fun j ↦ ?_
  by_cases hjs : j ∈ s
  · rw [if_pos hjs]; by_cases hji : j < i
    · rw [if_pos fun _ ↦ hji, if_pos hji, s.piecewise_eq_of_mem _ _ hjs]
    rw [if_neg (Classical.not_imp.mpr ⟨hjs, hji⟩), if_neg hji]
    obtain rfl | hij := eq_or_ne i j
    · rw [if_pos rfl, if_pos rfl, s.piecewise_eq_of_mem _ _ hi]
    · rw [if_neg hij, if_neg hij.symm]
  · rw [if_neg hjs, if_pos fun h ↦ (hjs h).elim, s.piecewise_eq_of_not_mem _ _ hjs]

open Finset in
lemma map_add_eq_map_add_linearDeriv_add [DecidableEq ι] [Fintype ι] (x h : (i : ι) → M₁ i) :
    f (x + h) = f x + f.linearDeriv x h +
      ∑ s ∈ univ.powerset.filter (2 ≤ ·.card), f (s.piecewise h x) := by
  rw [add_comm, map_add_univ, ← Finset.powerset_univ,
      ← sum_filter_add_sum_filter_not _ (2 ≤ ·.card)]
  simp_rw [not_le, Nat.lt_succ, le_iff_lt_or_eq (b := 1), Nat.lt_one_iff, filter_or,
    ← powersetCard_eq_filter, sum_union (univ.pairwise_disjoint_powersetCard zero_ne_one),
    powersetCard_zero, powersetCard_one, sum_singleton, Finset.piecewise_empty, sum_map,
    Function.Embedding.coeFn_mk, Finset.piecewise_singleton, linearDeriv_apply, add_comm]

open Finset in
/-- This expresses the difference between the values of a multilinear map
at two points "close to `x`" in terms of the "derivative" of the multilinear map at `x`
and of "second-order" terms. -/
lemma map_add_sub_map_add_sub_linearDeriv [DecidableEq ι] [Fintype ι] (x h h' : (i : ι) → M₁ i) :
    f (x + h) - f (x + h') - f.linearDeriv x (h - h') =
    ∑ s ∈ univ.powerset.filter (2 ≤ ·.card), (f (s.piecewise h x) - f (s.piecewise h' x)) := by
  simp_rw [map_add_eq_map_add_linearDeriv_add, add_assoc, add_sub_add_comm, sub_self, zero_add,
    ← LinearMap.map_sub, add_sub_cancel_left, sum_sub_distrib]

end AddCommGroup

section CommSemiring

variable [CommSemiring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [∀ i, Module R (M₁ i)]
  [Module R M₂]

/-- When `ι` is finite, multilinear maps on `R^ι` with values in `M₂` are in bijection with `M₂`,
as such a multilinear map is completely determined by its value on the constant vector made of ones.
We register this bijection as a linear equivalence in `MultilinearMap.piRingEquiv`. -/
protected def piRingEquiv [Fintype ι] : M₂ ≃ₗ[R] MultilinearMap R (fun _ : ι => R) M₂ where
  toFun z := MultilinearMap.mkPiRing R ι z
  invFun f := f fun _ => 1
  map_add' z z' := by
    ext m
    simp [smul_add]
  map_smul' c z := by
    ext m
    simp [smul_smul, mul_comm]
  left_inv z := by simp
  right_inv f := f.mkPiRing_apply_one_eq_self
#align multilinear_map.pi_ring_equiv MultilinearMap.piRingEquiv

end CommSemiring

end MultilinearMap

section Currying

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
the variables, given by `m ↦ f (m 0) (tail m)`-/
def LinearMap.uncurryLeft (f : M 0 →ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂) :
    MultilinearMap R M M₂ where
  toFun m := f (m 0) (tail m)
  map_add' := @fun dec m i x y => by
    -- Porting note: `clear` not necessary in Lean 3 due to not being in the instance cache
    rw [Subsingleton.elim dec (by clear dec; infer_instance)]; clear dec
    by_cases h : i = 0
    · subst i
      simp only [update_same, map_add, tail_update_zero, MultilinearMap.add_apply]
    · simp_rw [update_noteq (Ne.symm h)]
      revert x y
      rw [← succ_pred i h]
      intro x y
      rw [tail_update_succ, MultilinearMap.map_add, tail_update_succ, tail_update_succ]
  map_smul' := @fun dec m i c x => by
    -- Porting note: `clear` not necessary in Lean 3 due to not being in the instance cache
    rw [Subsingleton.elim dec (by clear dec; infer_instance)]; clear dec
    by_cases h : i = 0
    · subst i
      simp only [update_same, map_smul, tail_update_zero, MultilinearMap.smul_apply]
    · simp_rw [update_noteq (Ne.symm h)]
      revert x
      rw [← succ_pred i h]
      intro x
      rw [tail_update_succ, tail_update_succ, MultilinearMap.map_smul]
#align linear_map.uncurry_left LinearMap.uncurryLeft

@[simp]
theorem LinearMap.uncurryLeft_apply (f : M 0 →ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂)
    (m : ∀ i, M i) : f.uncurryLeft m = f (m 0) (tail m) :=
  rfl
#align linear_map.uncurry_left_apply LinearMap.uncurryLeft_apply

/-- Given a multilinear map `f` in `n+1` variables, split the first variable to obtain
a linear map into multilinear maps in `n` variables, given by `x ↦ (m ↦ f (cons x m))`. -/
def MultilinearMap.curryLeft (f : MultilinearMap R M M₂) :
    M 0 →ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂ where
  toFun x :=
    { toFun := fun m => f (cons x m)
      map_add' := @fun dec m i y y' => by
        -- Porting note: `clear` not necessary in Lean 3 due to not being in the instance cache
        rw [Subsingleton.elim dec (by clear dec; infer_instance)]
        simp
      map_smul' := @fun dec m i y c => by
        -- Porting note: `clear` not necessary in Lean 3 due to not being in the instance cache
        rw [Subsingleton.elim dec (by clear dec; infer_instance)]
        simp }
  map_add' x y := by
    ext m
    exact cons_add f m x y
  map_smul' c x := by
    ext m
    exact cons_smul f m c x
#align multilinear_map.curry_left MultilinearMap.curryLeft

@[simp]
theorem MultilinearMap.curryLeft_apply (f : MultilinearMap R M M₂) (x : M 0)
    (m : ∀ i : Fin n, M i.succ) : f.curryLeft x m = f (cons x m) :=
  rfl
#align multilinear_map.curry_left_apply MultilinearMap.curryLeft_apply

@[simp]
theorem LinearMap.curry_uncurryLeft (f : M 0 →ₗ[R] MultilinearMap R (fun i :
    Fin n => M i.succ) M₂) : f.uncurryLeft.curryLeft = f := by
  ext m x
  simp only [tail_cons, LinearMap.uncurryLeft_apply, MultilinearMap.curryLeft_apply]
  rw [cons_zero]
#align linear_map.curry_uncurry_left LinearMap.curry_uncurryLeft

@[simp]
theorem MultilinearMap.uncurry_curryLeft (f : MultilinearMap R M M₂) :
    f.curryLeft.uncurryLeft = f := by
  ext m
  simp
#align multilinear_map.uncurry_curry_left MultilinearMap.uncurry_curryLeft

variable (R M M₂)

/-- The space of multilinear maps on `∀ (i : Fin (n+1)), M i` is canonically isomorphic to
the space of linear maps from `M 0` to the space of multilinear maps on
`∀ (i : Fin n), M i.succ`, by separating the first variable. We register this isomorphism as a
linear isomorphism in `multilinearCurryLeftEquiv R M M₂`.

The direct and inverse maps are given by `f.uncurryLeft` and `f.curryLeft`. Use these
unless you need the full framework of linear equivs. -/
def multilinearCurryLeftEquiv :
    (M 0 →ₗ[R] MultilinearMap R (fun i : Fin n => M i.succ) M₂) ≃ₗ[R] MultilinearMap R M M₂ where
  toFun := LinearMap.uncurryLeft
  map_add' f₁ f₂ := by
    ext m
    rfl
  map_smul' c f := by
    ext m
    rfl
  invFun := MultilinearMap.curryLeft
  left_inv := LinearMap.curry_uncurryLeft
  right_inv := MultilinearMap.uncurry_curryLeft
#align multilinear_curry_left_equiv multilinearCurryLeftEquiv

variable {R M M₂}

/-! #### Right currying -/


/-- Given a multilinear map `f` in `n` variables to the space of linear maps from `M (last n)` to
`M₂`, construct the corresponding multilinear map on `n+1` variables obtained by concatenating
the variables, given by `m ↦ f (init m) (m (last n))`-/
def MultilinearMap.uncurryRight
    (f : MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) →ₗ[R] M₂)) :
    MultilinearMap R M M₂ where
  toFun m := f (init m) (m (last n))
  map_add' {dec} m i x y := by
    -- Porting note: `clear` not necessary in Lean 3 due to not being in the instance cache
    rw [Subsingleton.elim dec (by clear dec; infer_instance)]; clear dec
    by_cases h : i.val < n
    · have : last n ≠ i := Ne.symm (ne_of_lt h)
      simp_rw [update_noteq this]
      revert x y
      rw [(castSucc_castLT i h).symm]
      intro x y
      rw [init_update_castSucc, MultilinearMap.map_add, init_update_castSucc,
        init_update_castSucc, LinearMap.add_apply]
    · revert x y
      rw [eq_last_of_not_lt h]
      intro x y
      simp_rw [init_update_last, update_same, LinearMap.map_add]
  map_smul' {dec} m i c x := by
    -- Porting note: `clear` not necessary in Lean 3 due to not being in the instance cache
    rw [Subsingleton.elim dec (by clear dec; infer_instance)]; clear dec
    by_cases h : i.val < n
    · have : last n ≠ i := Ne.symm (ne_of_lt h)
      simp_rw [update_noteq this]
      revert x
      rw [(castSucc_castLT i h).symm]
      intro x
      rw [init_update_castSucc, init_update_castSucc, MultilinearMap.map_smul,
        LinearMap.smul_apply]
    · revert x
      rw [eq_last_of_not_lt h]
      intro x
      simp_rw [update_same, init_update_last, map_smul]
#align multilinear_map.uncurry_right MultilinearMap.uncurryRight

@[simp]
theorem MultilinearMap.uncurryRight_apply
    (f : MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) →ₗ[R] M₂))
    (m : ∀ i, M i) : f.uncurryRight m = f (init m) (m (last n)) :=
  rfl
#align multilinear_map.uncurry_right_apply MultilinearMap.uncurryRight_apply

/-- Given a multilinear map `f` in `n+1` variables, split the last variable to obtain
a multilinear map in `n` variables taking values in linear maps from `M (last n)` to `M₂`, given by
`m ↦ (x ↦ f (snoc m x))`. -/
def MultilinearMap.curryRight (f : MultilinearMap R M M₂) :
    MultilinearMap R (fun i : Fin n => M (Fin.castSucc i)) (M (last n) →ₗ[R] M₂) where
  toFun m :=
    { toFun := fun x => f (snoc m x)
      map_add' := fun x y => by simp_rw [f.snoc_add]
      map_smul' := fun c x => by simp only [f.snoc_smul, RingHom.id_apply] }
  map_add' := @fun dec m i x y => by
    rw [Subsingleton.elim dec (by clear dec; infer_instance)]; clear dec
    ext z
    change f (snoc (update m i (x + y)) z) = f (snoc (update m i x) z) + f (snoc (update m i y) z)
    rw [snoc_update, snoc_update, snoc_update, f.map_add]
  map_smul' := @fun dec m i c x => by
    rw [Subsingleton.elim dec (by clear dec; infer_instance)]; clear dec
    ext z
    change f (snoc (update m i (c • x)) z) = c • f (snoc (update m i x) z)
    rw [snoc_update, snoc_update, f.map_smul]
#align multilinear_map.curry_right MultilinearMap.curryRight

@[simp]
theorem MultilinearMap.curryRight_apply (f : MultilinearMap R M M₂)
    (m : ∀ i : Fin n, M (castSucc i)) (x : M (last n)) : f.curryRight m x = f (snoc m x) :=
  rfl
#align multilinear_map.curry_right_apply MultilinearMap.curryRight_apply

@[simp]
theorem MultilinearMap.curry_uncurryRight
    (f : MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) →ₗ[R] M₂)) :
    f.uncurryRight.curryRight = f := by
  ext m x
  simp only [snoc_last, MultilinearMap.curryRight_apply, MultilinearMap.uncurryRight_apply]
  rw [init_snoc]
#align multilinear_map.curry_uncurry_right MultilinearMap.curry_uncurryRight

@[simp]
theorem MultilinearMap.uncurry_curryRight (f : MultilinearMap R M M₂) :
    f.curryRight.uncurryRight = f := by
  ext m
  simp
#align multilinear_map.uncurry_curry_right MultilinearMap.uncurry_curryRight

variable (R M M₂)

/-- The space of multilinear maps on `∀ (i : Fin (n+1)), M i` is canonically isomorphic to
the space of linear maps from the space of multilinear maps on `∀ (i : Fin n), M (castSucc i)` to
the space of linear maps on `M (last n)`, by separating the last variable. We register this
isomorphism as a linear isomorphism in `multilinearCurryRightEquiv R M M₂`.

The direct and inverse maps are given by `f.uncurryRight` and `f.curryRight`. Use these
unless you need the full framework of linear equivs. -/
def multilinearCurryRightEquiv :
    MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) →ₗ[R] M₂) ≃ₗ[R]
      MultilinearMap R M M₂ where
  toFun := MultilinearMap.uncurryRight
  map_add' f₁ f₂ := by
    ext m
    rfl
  map_smul' c f := by
    ext m
    rw [smul_apply]
    rfl
  invFun := MultilinearMap.curryRight
  left_inv := MultilinearMap.curry_uncurryRight
  right_inv := MultilinearMap.uncurry_curryRight
#align multilinear_curry_right_equiv multilinearCurryRightEquiv

namespace MultilinearMap

variable {ι' : Type*} {R M₂}

/-- A multilinear map on `∀ i : ι ⊕ ι', M'` defines a multilinear map on `∀ i : ι, M'`
taking values in the space of multilinear maps on `∀ i : ι', M'`. -/
def currySum (f : MultilinearMap R (fun _ : Sum ι ι' => M') M₂) :
    MultilinearMap R (fun _ : ι => M') (MultilinearMap R (fun _ : ι' => M') M₂) where
  toFun u :=
    { toFun := fun v => f (Sum.elim u v)
      map_add' := fun v i x y => by
        letI := Classical.decEq ι
        simp only [← Sum.update_elim_inr, f.map_add]
      map_smul' := fun v i c x => by
        letI := Classical.decEq ι
        simp only [← Sum.update_elim_inr, f.map_smul] }
  map_add' u i x y :=
    ext fun v => by
      letI := Classical.decEq ι'
      simp only [MultilinearMap.coe_mk, add_apply, ← Sum.update_elim_inl, f.map_add]
  map_smul' u i c x :=
    ext fun v => by
      letI := Classical.decEq ι'
      simp only [MultilinearMap.coe_mk, smul_apply, ← Sum.update_elim_inl, f.map_smul]
#align multilinear_map.curry_sum MultilinearMap.currySum

@[simp]
theorem currySum_apply (f : MultilinearMap R (fun _ : Sum ι ι' => M') M₂) (u : ι → M')
    (v : ι' → M') : f.currySum u v = f (Sum.elim u v) :=
  rfl
#align multilinear_map.curry_sum_apply MultilinearMap.currySum_apply

/-- A multilinear map on `∀ i : ι, M'` taking values in the space of multilinear maps
on `∀ i : ι', M'` defines a multilinear map on `∀ i : ι ⊕ ι', M'`. -/
def uncurrySum (f : MultilinearMap R (fun _ : ι => M') (MultilinearMap R (fun _ : ι' => M') M₂)) :
    MultilinearMap R (fun _ : Sum ι ι' => M') M₂ where
  toFun u := f (u ∘ Sum.inl) (u ∘ Sum.inr)
  map_add' u i x y := by
    letI := (@Sum.inl_injective ι ι').decidableEq
    letI := (@Sum.inr_injective ι ι').decidableEq
    cases i <;>
      simp only [MultilinearMap.map_add, add_apply, Sum.update_inl_comp_inl,
        Sum.update_inl_comp_inr, Sum.update_inr_comp_inl, Sum.update_inr_comp_inr]
  map_smul' u i c x := by
    letI := (@Sum.inl_injective ι ι').decidableEq
    letI := (@Sum.inr_injective ι ι').decidableEq
    cases i <;>
      simp only [MultilinearMap.map_smul, smul_apply, Sum.update_inl_comp_inl,
        Sum.update_inl_comp_inr, Sum.update_inr_comp_inl, Sum.update_inr_comp_inr]
#align multilinear_map.uncurry_sum MultilinearMap.uncurrySum

@[simp]
theorem uncurrySum_aux_apply
    (f : MultilinearMap R (fun _ : ι => M') (MultilinearMap R (fun _ : ι' => M') M₂))
    (u : Sum ι ι' → M') : f.uncurrySum u = f (u ∘ Sum.inl) (u ∘ Sum.inr) :=
  rfl
#align multilinear_map.uncurry_sum_aux_apply MultilinearMap.uncurrySum_aux_apply

variable (ι ι' R M₂ M')

/-- Linear equivalence between the space of multilinear maps on `∀ i : ι ⊕ ι', M'` and the space
of multilinear maps on `∀ i : ι, M'` taking values in the space of multilinear maps
on `∀ i : ι', M'`. -/
def currySumEquiv :
    MultilinearMap R (fun _ : Sum ι ι' => M') M₂ ≃ₗ[R]
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
#align multilinear_map.curry_sum_equiv MultilinearMap.currySumEquiv

variable {ι ι' R M₂ M'}

@[simp]
theorem coe_currySumEquiv : ⇑(currySumEquiv R ι M₂ M' ι') = currySum :=
  rfl
#align multilinear_map.coe_curry_sum_equiv MultilinearMap.coe_currySumEquiv

-- Porting note: fixed missing letter `y` in name
@[simp]
theorem coe_currySumEquiv_symm : ⇑(currySumEquiv R ι M₂ M' ι').symm = uncurrySum :=
  rfl
#align multilinear_map.coe_curr_sum_equiv_symm MultilinearMap.coe_currySumEquiv_symm

variable (R M₂ M')

/-- If `s : Finset (Fin n)` is a finite set of cardinality `k` and its complement has cardinality
`l`, then the space of multilinear maps on `fun i : Fin n => M'` is isomorphic to the space of
multilinear maps on `fun i : Fin k => M'` taking values in the space of multilinear maps
on `fun i : Fin l => M'`. -/
def curryFinFinset {k l n : ℕ} {s : Finset (Fin n)} (hk : s.card = k) (hl : sᶜ.card = l) :
    MultilinearMap R (fun _ : Fin n => M') M₂ ≃ₗ[R]
      MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂) :=
  (domDomCongrLinearEquiv R R M' M₂ (finSumEquivOfFinset hk hl).symm).trans
    (currySumEquiv R (Fin k) M₂ M' (Fin l))
#align multilinear_map.curry_fin_finset MultilinearMap.curryFinFinset

variable {R M₂ M'}

@[simp]
theorem curryFinFinset_apply {k l n : ℕ} {s : Finset (Fin n)} (hk : s.card = k) (hl : sᶜ.card = l)
    (f : MultilinearMap R (fun _ : Fin n => M') M₂) (mk : Fin k → M') (ml : Fin l → M') :
    curryFinFinset R M₂ M' hk hl f mk ml =
      f fun i => Sum.elim mk ml ((finSumEquivOfFinset hk hl).symm i) :=
  rfl
#align multilinear_map.curry_fin_finset_apply MultilinearMap.curryFinFinset_apply

@[simp]
theorem curryFinFinset_symm_apply {k l n : ℕ} {s : Finset (Fin n)} (hk : s.card = k)
    (hl : sᶜ.card = l)
    (f : MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂))
    (m : Fin n → M') :
    (curryFinFinset R M₂ M' hk hl).symm f m =
      f (fun i => m <| finSumEquivOfFinset hk hl (Sum.inl i)) fun i =>
        m <| finSumEquivOfFinset hk hl (Sum.inr i) :=
  rfl
#align multilinear_map.curry_fin_finset_symm_apply MultilinearMap.curryFinFinset_symm_apply

-- @[simp] -- Porting note: simpNF linter, lhs simplifies, added aux version below
theorem curryFinFinset_symm_apply_piecewise_const {k l n : ℕ} {s : Finset (Fin n)} (hk : s.card = k)
    (hl : sᶜ.card = l)
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
#align multilinear_map.curry_fin_finset_symm_apply_piecewise_const MultilinearMap.curryFinFinset_symm_apply_piecewise_const

@[simp]
theorem curryFinFinset_symm_apply_piecewise_const_aux {k l n : ℕ} {s : Finset (Fin n)}
    (hk : s.card = k) (hl : sᶜ.card = l)
    (f : MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂))
    (x y : M') :
      ((⇑f fun _ => x) (fun i => (Finset.piecewise s (fun _ => x) (fun _ => y)
          ((sᶜ.orderEmbOfFin hl) i))) = f (fun _ => x) fun _ => y) := by
  have := curryFinFinset_symm_apply_piecewise_const hk hl f x y
  simp only [curryFinFinset_symm_apply, finSumEquivOfFinset_inl, Finset.orderEmbOfFin_mem,
  Finset.piecewise_eq_of_mem, finSumEquivOfFinset_inr] at this
  exact this

@[simp]
theorem curryFinFinset_symm_apply_const {k l n : ℕ} {s : Finset (Fin n)} (hk : s.card = k)
    (hl : sᶜ.card = l)
    (f : MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂))
    (x : M') : ((curryFinFinset R M₂ M' hk hl).symm f fun _ => x) = f (fun _ => x) fun _ => x :=
  rfl
#align multilinear_map.curry_fin_finset_symm_apply_const MultilinearMap.curryFinFinset_symm_apply_const

-- @[simp] -- Porting note: simpNF, lhs simplifies, added aux version below
theorem curryFinFinset_apply_const {k l n : ℕ} {s : Finset (Fin n)} (hk : s.card = k)
    (hl : sᶜ.card = l) (f : MultilinearMap R (fun _ : Fin n => M') M₂) (x y : M') :
    (curryFinFinset R M₂ M' hk hl f (fun _ => x) fun _ => y) =
      f (s.piecewise (fun _ => x) fun _ => y) := by
  refine (curryFinFinset_symm_apply_piecewise_const hk hl _ _ _).symm.trans ?_
  -- `rw` fails
  rw [LinearEquiv.symm_apply_apply]
#align multilinear_map.curry_fin_finset_apply_const MultilinearMap.curryFinFinset_apply_const

@[simp]
theorem curryFinFinset_apply_const_aux {k l n : ℕ} {s : Finset (Fin n)} (hk : s.card = k)
    (hl : sᶜ.card = l) (f : MultilinearMap R (fun _ : Fin n => M') M₂) (x y : M') :
    (f fun i => Sum.elim (fun _ => x) (fun _ => y) ((⇑ (Equiv.symm (finSumEquivOfFinset hk hl))) i))
      = f (s.piecewise (fun _ => x) fun _ => y) := by
  rw [← curryFinFinset_apply]
  apply curryFinFinset_apply_const

end MultilinearMap

end Currying

namespace MultilinearMap

section Submodule

variable [Ring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M'] [AddCommMonoid M₂]
  [∀ i, Module R (M₁ i)] [Module R M'] [Module R M₂]

/-- The pushforward of an indexed collection of submodule `p i ⊆ M₁ i` by `f : M₁ → M₂`.

Note that this is not a submodule - it is not closed under addition. -/
def map [Nonempty ι] (f : MultilinearMap R M₁ M₂) (p : ∀ i, Submodule R (M₁ i)) :
    SubMulAction R M₂ where
  carrier := f '' { v | ∀ i, v i ∈ p i }
  smul_mem' := fun c _ ⟨x, hx, hf⟩ => by
    let ⟨i⟩ := ‹Nonempty ι›
    letI := Classical.decEq ι
    refine ⟨update x i (c • x i), fun j => if hij : j = i then ?_ else ?_, hf ▸ ?_⟩
    · rw [hij, update_same]
      exact (p i).smul_mem _ (hx i)
    · rw [update_noteq hij]
      exact hx j
    · rw [f.map_smul, update_eq_self]
#align multilinear_map.map MultilinearMap.map

/-- The map is always nonempty. This lemma is needed to apply `SubMulAction.zero_mem`. -/
theorem map_nonempty [Nonempty ι] (f : MultilinearMap R M₁ M₂) (p : ∀ i, Submodule R (M₁ i)) :
    (map f p : Set M₂).Nonempty :=
  ⟨f 0, 0, fun i => (p i).zero_mem, rfl⟩
#align multilinear_map.map_nonempty MultilinearMap.map_nonempty

/-- The range of a multilinear map, closed under scalar multiplication. -/
def range [Nonempty ι] (f : MultilinearMap R M₁ M₂) : SubMulAction R M₂ :=
  f.map fun _ => ⊤
#align multilinear_map.range MultilinearMap.range

end Submodule

end MultilinearMap
