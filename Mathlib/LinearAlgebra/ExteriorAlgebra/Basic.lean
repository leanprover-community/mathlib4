/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhangir Azerbayev, Adam Topaz, Eric Wieser
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.Alternating.Basic

#align_import linear_algebra.exterior_algebra.basic from "leanprover-community/mathlib"@"b8d2eaa69d69ce8f03179a5cda774fc0cde984e4"

/-!
# Exterior Algebras

We construct the exterior algebra of a module `M` over a commutative semiring `R`.

## Notation

The exterior algebra of the `R`-module `M` is denoted as `ExteriorAlgebra R M`.
It is endowed with the structure of an `R`-algebra.

The `n`th exterior power of the `R`-module `M` is denoted by `exteriorPower R n M`;
it is of type `Submodule R (ExteriorAlgebra R M)` and defined as
`LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ n`.
We also introduce the notation `⋀[R]^n M` for `exteriorPower R n M`.

Given a linear morphism `f : M → A` from a module `M` to another `R`-algebra `A`, such that
`cond : ∀ m : M, f m * f m = 0`, there is a (unique) lift of `f` to an `R`-algebra morphism,
which is denoted `ExteriorAlgebra.lift R f cond`.

The canonical linear map `M → ExteriorAlgebra R M` is denoted `ExteriorAlgebra.ι R`.

## Theorems

The main theorems proved ensure that `ExteriorAlgebra R M` satisfies the universal property
of the exterior algebra.
1. `ι_comp_lift` is the fact that the composition of `ι R` with `lift R f cond` agrees with `f`.
2. `lift_unique` ensures the uniqueness of `lift R f cond` with respect to 1.

## Definitions

* `ιMulti` is the `AlternatingMap` corresponding to the wedge product of `ι R m` terms.

## Implementation details

The exterior algebra of `M` is constructed as simply `CliffordAlgebra (0 : QuadraticForm R M)`,
as this avoids us having to duplicate API.
-/


universe u1 u2 u3 u4 u5

variable (R : Type u1) [CommRing R]
variable (M : Type u2) [AddCommGroup M] [Module R M]

/-- The exterior algebra of an `R`-module `M`.
-/
abbrev ExteriorAlgebra :=
  CliffordAlgebra (0 : QuadraticForm R M)
#align exterior_algebra ExteriorAlgebra

namespace ExteriorAlgebra

variable {M}

/-- The canonical linear map `M →ₗ[R] ExteriorAlgebra R M`.
-/
abbrev ι : M →ₗ[R] ExteriorAlgebra R M :=
  CliffordAlgebra.ι _
#align exterior_algebra.ι ExteriorAlgebra.ι

section exteriorPower

-- New variables `n` and `M`, to get the correct order of variables in the notation.
variable (n : ℕ) (M : Type u2) [AddCommGroup M] [Module R M]

/-- Definition of the `n`th exterior power of a `R`-module `N`. We introduce the notation
`⋀[R]^n M` for `exteriorPower R n M`. -/
abbrev exteriorPower : Submodule R (ExteriorAlgebra R M) :=
  LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M) ^ n

@[inherit_doc exteriorPower]
notation:max "⋀[" R "]^" n:arg => exteriorPower R n

end exteriorPower

variable {R}

/-- As well as being linear, `ι m` squares to zero. -/
-- @[simp] -- Porting note (#10618): simp can prove this
theorem ι_sq_zero (m : M) : ι R m * ι R m = 0 :=
  (CliffordAlgebra.ι_sq_scalar _ m).trans <| map_zero _
#align exterior_algebra.ι_sq_zero ExteriorAlgebra.ι_sq_zero

variable {A : Type*} [Semiring A] [Algebra R A]

-- @[simp] -- Porting note (#10618): simp can prove this
theorem comp_ι_sq_zero (g : ExteriorAlgebra R M →ₐ[R] A) (m : M) : g (ι R m) * g (ι R m) = 0 := by
  rw [← AlgHom.map_mul, ι_sq_zero, AlgHom.map_zero]
#align exterior_algebra.comp_ι_sq_zero ExteriorAlgebra.comp_ι_sq_zero

variable (R)

/-- Given a linear map `f : M →ₗ[R] A` into an `R`-algebra `A`, which satisfies the condition:
`cond : ∀ m : M, f m * f m = 0`, this is the canonical lift of `f` to a morphism of `R`-algebras
from `ExteriorAlgebra R M` to `A`.
-/
@[simps! symm_apply]
def lift : { f : M →ₗ[R] A // ∀ m, f m * f m = 0 } ≃ (ExteriorAlgebra R M →ₐ[R] A) :=
  Equiv.trans (Equiv.subtypeEquiv (Equiv.refl _) <| by simp) <| CliffordAlgebra.lift _
#align exterior_algebra.lift ExteriorAlgebra.lift

@[simp]
theorem ι_comp_lift (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0) :
    (lift R ⟨f, cond⟩).toLinearMap.comp (ι R) = f :=
  CliffordAlgebra.ι_comp_lift f _
#align exterior_algebra.ι_comp_lift ExteriorAlgebra.ι_comp_lift

@[simp]
theorem lift_ι_apply (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0) (x) :
    lift R ⟨f, cond⟩ (ι R x) = f x :=
  CliffordAlgebra.lift_ι_apply f _ x
#align exterior_algebra.lift_ι_apply ExteriorAlgebra.lift_ι_apply

@[simp]
theorem lift_unique (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0) (g : ExteriorAlgebra R M →ₐ[R] A) :
    g.toLinearMap.comp (ι R) = f ↔ g = lift R ⟨f, cond⟩ :=
  CliffordAlgebra.lift_unique f _ _
#align exterior_algebra.lift_unique ExteriorAlgebra.lift_unique

variable {R}

@[simp]
theorem lift_comp_ι (g : ExteriorAlgebra R M →ₐ[R] A) :
    lift R ⟨g.toLinearMap.comp (ι R), comp_ι_sq_zero _⟩ = g :=
  CliffordAlgebra.lift_comp_ι g
#align exterior_algebra.lift_comp_ι ExteriorAlgebra.lift_comp_ι

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem hom_ext {f g : ExteriorAlgebra R M →ₐ[R] A}
    (h : f.toLinearMap.comp (ι R) = g.toLinearMap.comp (ι R)) : f = g :=
  CliffordAlgebra.hom_ext h
#align exterior_algebra.hom_ext ExteriorAlgebra.hom_ext

/-- If `C` holds for the `algebraMap` of `r : R` into `ExteriorAlgebra R M`, the `ι` of `x : M`,
and is preserved under addition and muliplication, then it holds for all of `ExteriorAlgebra R M`.
-/
@[elab_as_elim]
theorem induction {C : ExteriorAlgebra R M → Prop}
    (algebraMap : ∀ r, C (algebraMap R (ExteriorAlgebra R M) r)) (ι : ∀ x, C (ι R x))
    (mul : ∀ a b, C a → C b → C (a * b)) (add : ∀ a b, C a → C b → C (a + b))
    (a : ExteriorAlgebra R M) : C a :=
  CliffordAlgebra.induction algebraMap ι mul add a
#align exterior_algebra.induction ExteriorAlgebra.induction

/-- The left-inverse of `algebraMap`. -/
def algebraMapInv : ExteriorAlgebra R M →ₐ[R] R :=
  ExteriorAlgebra.lift R ⟨(0 : M →ₗ[R] R), fun _ => by simp⟩
#align exterior_algebra.algebra_map_inv ExteriorAlgebra.algebraMapInv

variable (M)

theorem algebraMap_leftInverse :
    Function.LeftInverse algebraMapInv (algebraMap R <| ExteriorAlgebra R M) := fun x => by
  simp [algebraMapInv]
#align exterior_algebra.algebra_map_left_inverse ExteriorAlgebra.algebraMap_leftInverse

@[simp]
theorem algebraMap_inj (x y : R) :
    algebraMap R (ExteriorAlgebra R M) x = algebraMap R (ExteriorAlgebra R M) y ↔ x = y :=
  (algebraMap_leftInverse M).injective.eq_iff
#align exterior_algebra.algebra_map_inj ExteriorAlgebra.algebraMap_inj

@[simp]
theorem algebraMap_eq_zero_iff (x : R) : algebraMap R (ExteriorAlgebra R M) x = 0 ↔ x = 0 :=
  map_eq_zero_iff (algebraMap _ _) (algebraMap_leftInverse _).injective
#align exterior_algebra.algebra_map_eq_zero_iff ExteriorAlgebra.algebraMap_eq_zero_iff

@[simp]
theorem algebraMap_eq_one_iff (x : R) : algebraMap R (ExteriorAlgebra R M) x = 1 ↔ x = 1 :=
  map_eq_one_iff (algebraMap _ _) (algebraMap_leftInverse _).injective
#align exterior_algebra.algebra_map_eq_one_iff ExteriorAlgebra.algebraMap_eq_one_iff

theorem isUnit_algebraMap (r : R) : IsUnit (algebraMap R (ExteriorAlgebra R M) r) ↔ IsUnit r :=
  isUnit_map_of_leftInverse _ (algebraMap_leftInverse M)
#align exterior_algebra.is_unit_algebra_map ExteriorAlgebra.isUnit_algebraMap

/-- Invertibility in the exterior algebra is the same as invertibility of the base ring. -/
@[simps!]
def invertibleAlgebraMapEquiv (r : R) :
    Invertible (algebraMap R (ExteriorAlgebra R M) r) ≃ Invertible r :=
  invertibleEquivOfLeftInverse _ _ _ (algebraMap_leftInverse M)
#align exterior_algebra.invertible_algebra_map_equiv ExteriorAlgebra.invertibleAlgebraMapEquiv

variable {M}

/-- The canonical map from `ExteriorAlgebra R M` into `TrivSqZeroExt R M` that sends
`ExteriorAlgebra.ι` to `TrivSqZeroExt.inr`. -/
def toTrivSqZeroExt [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    ExteriorAlgebra R M →ₐ[R] TrivSqZeroExt R M :=
  lift R ⟨TrivSqZeroExt.inrHom R M, fun m => TrivSqZeroExt.inr_mul_inr R m m⟩
#align exterior_algebra.to_triv_sq_zero_ext ExteriorAlgebra.toTrivSqZeroExt

@[simp]
theorem toTrivSqZeroExt_ι [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (x : M) :
    toTrivSqZeroExt (ι R x) = TrivSqZeroExt.inr x :=
  lift_ι_apply _ _ _ _
#align exterior_algebra.to_triv_sq_zero_ext_ι ExteriorAlgebra.toTrivSqZeroExt_ι

/-- The left-inverse of `ι`.

As an implementation detail, we implement this using `TrivSqZeroExt` which has a suitable
algebra structure. -/
def ιInv : ExteriorAlgebra R M →ₗ[R] M := by
  letI : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  haveI : IsCentralScalar R M := ⟨fun r m => rfl⟩
  exact (TrivSqZeroExt.sndHom R M).comp toTrivSqZeroExt.toLinearMap
#align exterior_algebra.ι_inv ExteriorAlgebra.ιInv

theorem ι_leftInverse : Function.LeftInverse ιInv (ι R : M → ExteriorAlgebra R M) := fun x => by
  -- Porting note: Original proof didn't have `letI` and `haveI`
  letI : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  haveI : IsCentralScalar R M := ⟨fun r m => rfl⟩
  simp [ιInv]
#align exterior_algebra.ι_left_inverse ExteriorAlgebra.ι_leftInverse

variable (R)

@[simp]
theorem ι_inj (x y : M) : ι R x = ι R y ↔ x = y :=
  ι_leftInverse.injective.eq_iff
#align exterior_algebra.ι_inj ExteriorAlgebra.ι_inj

variable {R}

@[simp]
theorem ι_eq_zero_iff (x : M) : ι R x = 0 ↔ x = 0 := by rw [← ι_inj R x 0, LinearMap.map_zero]
#align exterior_algebra.ι_eq_zero_iff ExteriorAlgebra.ι_eq_zero_iff

@[simp]
theorem ι_eq_algebraMap_iff (x : M) (r : R) : ι R x = algebraMap R _ r ↔ x = 0 ∧ r = 0 := by
  refine ⟨fun h => ?_, ?_⟩
  · letI : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
    haveI : IsCentralScalar R M := ⟨fun r m => rfl⟩
    have hf0 : toTrivSqZeroExt (ι R x) = (0, x) := toTrivSqZeroExt_ι _
    rw [h, AlgHom.commutes] at hf0
    have : r = 0 ∧ 0 = x := Prod.ext_iff.1 hf0
    exact this.symm.imp_left Eq.symm
  · rintro ⟨rfl, rfl⟩
    rw [LinearMap.map_zero, RingHom.map_zero]
#align exterior_algebra.ι_eq_algebra_map_iff ExteriorAlgebra.ι_eq_algebraMap_iff

@[simp]
theorem ι_ne_one [Nontrivial R] (x : M) : ι R x ≠ 1 := by
  rw [← (algebraMap R (ExteriorAlgebra R M)).map_one, Ne, ι_eq_algebraMap_iff]
  exact one_ne_zero ∘ And.right
#align exterior_algebra.ι_ne_one ExteriorAlgebra.ι_ne_one

/-- The generators of the exterior algebra are disjoint from its scalars. -/
theorem ι_range_disjoint_one :
    Disjoint (LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M))
      (1 : Submodule R (ExteriorAlgebra R M)) := by
  rw [Submodule.disjoint_def]
  rintro _ ⟨x, hx⟩ ⟨r, rfl : algebraMap R (ExteriorAlgebra R M) r = _⟩
  rw [ι_eq_algebraMap_iff x] at hx
  rw [hx.2, RingHom.map_zero]
#align exterior_algebra.ι_range_disjoint_one ExteriorAlgebra.ι_range_disjoint_one

@[simp]
theorem ι_add_mul_swap (x y : M) : ι R x * ι R y + ι R y * ι R x = 0 :=
  CliffordAlgebra.ι_mul_ι_add_swap_of_isOrtho <| .all _ _
#align exterior_algebra.ι_add_mul_swap ExteriorAlgebra.ι_add_mul_swap

theorem ι_mul_prod_list {n : ℕ} (f : Fin n → M) (i : Fin n) :
    (ι R <| f i) * (List.ofFn fun i => ι R <| f i).prod = 0 := by
  induction' n with n hn
  · exact i.elim0
  · rw [List.ofFn_succ, List.prod_cons, ← mul_assoc]
    by_cases h : i = 0
    · rw [h, ι_sq_zero, zero_mul]
    · replace hn :=
        congr_arg (ι R (f 0) * ·) <| hn (fun i => f <| Fin.succ i) (i.pred h)
      simp only at hn
      rw [Fin.succ_pred, ← mul_assoc, mul_zero] at hn
      refine (eq_zero_iff_eq_zero_of_add_eq_zero ?_).mp hn
      rw [← add_mul, ι_add_mul_swap, zero_mul]
#align exterior_algebra.ι_mul_prod_list ExteriorAlgebra.ι_mul_prod_list

variable (R)

/-- The product of `n` terms of the form `ι R m` is an alternating map.

This is a special case of `MultilinearMap.mkPiAlgebraFin`, and the exterior algebra version of
`TensorAlgebra.tprod`. -/
def ιMulti (n : ℕ) : M [⋀^Fin n]→ₗ[R] ExteriorAlgebra R M :=
  let F := (MultilinearMap.mkPiAlgebraFin R n (ExteriorAlgebra R M)).compLinearMap fun _ => ι R
  { F with
    map_eq_zero_of_eq' := fun f x y hfxy hxy => by
      dsimp [F]
      clear F
      wlog h : x < y
      · exact this R (A := A) n f y x hfxy.symm hxy.symm (hxy.lt_or_lt.resolve_left h)
      clear hxy
      induction' n with n hn
      · exact x.elim0
      · rw [List.ofFn_succ, List.prod_cons]
        by_cases hx : x = 0
        -- one of the repeated terms is on the left
        · rw [hx] at hfxy h
          rw [hfxy, ← Fin.succ_pred y (ne_of_lt h).symm]
          exact ι_mul_prod_list (f ∘ Fin.succ) _
        -- ignore the left-most term and induct on the remaining ones, decrementing indices
        · convert mul_zero (ι R (f 0))
          refine
            hn
              (fun i => f <| Fin.succ i) (x.pred hx)
              (y.pred (ne_of_lt <| lt_of_le_of_lt x.zero_le h).symm) ?_
              (Fin.pred_lt_pred_iff.mpr h)
          simp only [Fin.succ_pred]
          exact hfxy
    toFun := F }
#align exterior_algebra.ι_multi ExteriorAlgebra.ιMulti

variable {R}

theorem ιMulti_apply {n : ℕ} (v : Fin n → M) : ιMulti R n v = (List.ofFn fun i => ι R (v i)).prod :=
  rfl
#align exterior_algebra.ι_multi_apply ExteriorAlgebra.ιMulti_apply

@[simp]
theorem ιMulti_zero_apply (v : Fin 0 → M) : ιMulti R 0 v = 1 :=
  rfl
#align exterior_algebra.ι_multi_zero_apply ExteriorAlgebra.ιMulti_zero_apply

@[simp]
theorem ιMulti_succ_apply {n : ℕ} (v : Fin n.succ → M) :
    ιMulti R _ v = ι R (v 0) * ιMulti R _ (Matrix.vecTail v) := by
  simp [ιMulti, Matrix.vecTail]
#align exterior_algebra.ι_multi_succ_apply ExteriorAlgebra.ιMulti_succ_apply

theorem ιMulti_succ_curryLeft {n : ℕ} (m : M) :
    (ιMulti R n.succ).curryLeft m = (LinearMap.mulLeft R (ι R m)).compAlternatingMap (ιMulti R n) :=
  AlternatingMap.ext fun v =>
    (ιMulti_succ_apply _).trans <| by
      simp_rw [Matrix.tail_cons]
      rfl
#align exterior_algebra.ι_multi_succ_curry_left ExteriorAlgebra.ιMulti_succ_curryLeft

variable (R)

/-- The image of `ExteriorAlgebra.ιMulti R n` is contained in the `n`th exterior power. -/
lemma ιMulti_range (n : ℕ) :
    Set.range (ιMulti R n (M := M)) ⊆ ↑(⋀[R]^n M) := by
  rw [Set.range_subset_iff]
  intro v
  rw [ιMulti_apply]
  apply Submodule.pow_subset_pow
  rw [Set.mem_pow]
  exact ⟨fun i => ⟨ι R (v i), LinearMap.mem_range_self _ _⟩, rfl⟩

/-- The image of `ExteriorAlgebra.ιMulti R n` spans the `n`th exterior power, as a submodule
of the exterior algebra. -/
lemma ιMulti_span_fixedDegree (n : ℕ) :
    Submodule.span R (Set.range (ιMulti R n)) = ⋀[R]^n M := by
  refine le_antisymm (Submodule.span_le.2 (ιMulti_range R n)) ?_
  rw [exteriorPower, Submodule.pow_eq_span_pow_set, Submodule.span_le]
  refine fun u hu ↦ Submodule.subset_span ?_
  obtain ⟨f, rfl⟩ := Set.mem_pow.mp hu
  refine ⟨fun i => ιInv (f i).1, ?_⟩
  rw [ιMulti_apply]
  congr with i
  obtain ⟨v, hv⟩ := (f i).prop
  rw [← hv, ι_leftInverse]

/-- Given a linearly ordered family `v` of vectors of `M` and a natural number `n`, produce the
family of `n`fold exterior products of elements of `v`, seen as members of the exterior algebra. -/
abbrev ιMulti_family (n : ℕ) {I : Type*} [LinearOrder I] (v : I → M)
    (s : {s : Finset I // Finset.card s = n}) : ExteriorAlgebra R M :=
  ιMulti R n fun i => v (Finset.orderIsoOfFin _ s.prop i)

variable {R}

/-- An `ExteriorAlgebra` over a nontrivial ring is nontrivial. -/
instance [Nontrivial R] : Nontrivial (ExteriorAlgebra R M) :=
  (algebraMap_leftInverse M).injective.nontrivial

/-! Functoriality of the exterior algebra. -/

variable {N : Type u4} {N' : Type u5} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']

/-- The morphism of exterior algebras induced by a linear map. -/
def map (f : M →ₗ[R] N) : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R N :=
  CliffordAlgebra.map { f with map_app' := fun _ => rfl }

@[simp]
theorem map_comp_ι (f : M →ₗ[R] N) : (map f).toLinearMap ∘ₗ ι R = ι R ∘ₗ f :=
  CliffordAlgebra.map_comp_ι _

@[simp]
theorem map_apply_ι (f : M →ₗ[R] N) (m : M) : map f (ι R m) = ι R (f m) :=
  CliffordAlgebra.map_apply_ι _ m

@[simp]
theorem map_apply_ιMulti {n : ℕ} (f : M →ₗ[R] N) (m : Fin n → M) :
    map f (ιMulti R n m) = ιMulti R n (f ∘ m) := by
  rw [ιMulti_apply, ιMulti_apply, map_list_prod]
  simp only [List.map_ofFn, Function.comp, map_apply_ι]

@[simp]
theorem map_comp_ιMulti {n : ℕ} (f : M →ₗ[R] N) :
    (map f).toLinearMap.compAlternatingMap (ιMulti R n (M := M)) =
    (ιMulti R n (M := N)).compLinearMap f := by
  ext m
  exact map_apply_ιMulti _ _

@[simp]
theorem map_id :
    map LinearMap.id = AlgHom.id R (ExteriorAlgebra R M) :=
  CliffordAlgebra.map_id 0

@[simp]
theorem map_comp_map (f : M →ₗ[R] N) (g : N →ₗ[R] N') :
    AlgHom.comp (map g) (map f) = map (LinearMap.comp g f) :=
  CliffordAlgebra.map_comp_map _ _

@[simp]
theorem ι_range_map_map (f : M →ₗ[R] N) :
    Submodule.map (AlgHom.toLinearMap (map f)) (LinearMap.range (ι R (M := M))) =
    Submodule.map (ι R) (LinearMap.range f) :=
  CliffordAlgebra.ι_range_map_map _

theorem toTrivSqZeroExt_comp_map [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [Module Rᵐᵒᵖ N]
    [IsCentralScalar R N] (f : M →ₗ[R] N) :
    toTrivSqZeroExt.comp (map f) = (TrivSqZeroExt.map f).comp toTrivSqZeroExt := by
  apply hom_ext
  apply LinearMap.ext
  simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, map_apply_ι, toTrivSqZeroExt_ι, TrivSqZeroExt.map_inr, forall_const]

theorem ιInv_comp_map (f : M →ₗ[R] N) :
    ιInv.comp (map f).toLinearMap = f.comp ιInv := by
  letI : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  haveI : IsCentralScalar R M := ⟨fun r m => rfl⟩
  letI : Module Rᵐᵒᵖ N := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  haveI : IsCentralScalar R N := ⟨fun r m => rfl⟩
  unfold ιInv
  conv_lhs => rw [LinearMap.comp_assoc, ← AlgHom.comp_toLinearMap, toTrivSqZeroExt_comp_map,
                AlgHom.comp_toLinearMap, ← LinearMap.comp_assoc, TrivSqZeroExt.sndHom_comp_map]
  rfl

open Function in
/-- For a linear map `f` from `M` to `N`,
`ExteriorAlgebra.map g` is a retraction of `ExteriorAlgebra.map f` iff
`g` is a retraction of `f`. -/
@[simp]
lemma leftInverse_map_iff {f : M →ₗ[R] N} {g : N →ₗ[R] M} :
    LeftInverse (map g) (map f) ↔ LeftInverse g f := by
  refine ⟨fun h x => ?_, fun h => CliffordAlgebra.leftInverse_map_of_leftInverse _ _ h⟩
  simpa using h (ι _ x)

/-- A morphism of modules that admits a linear retraction induces an injective morphism of
exterior algebras. -/
lemma map_injective {f : M →ₗ[R] N} (hf : ∃ (g : N →ₗ[R] M), g.comp f = LinearMap.id) :
    Function.Injective (map f) :=
  let ⟨_, hgf⟩ := hf; (leftInverse_map_iff.mpr (DFunLike.congr_fun hgf)).injective

/-- A morphism of modules is surjective if and only the morphism of exterior algebras that it
induces is surjective. -/
@[simp]
lemma map_surjective_iff {f : M →ₗ[R] N} :
    Function.Surjective (map f) ↔ Function.Surjective f := by
  refine ⟨fun h y ↦ ?_, fun h ↦ CliffordAlgebra.map_surjective _ h⟩
  obtain ⟨x, hx⟩ := h (ι R y)
  existsi ιInv x
  rw [← LinearMap.comp_apply, ← ιInv_comp_map, LinearMap.comp_apply]
  erw [hx, ExteriorAlgebra.ι_leftInverse]

variable {K E F : Type*} [Field K] [AddCommGroup E]
  [Module K E] [AddCommGroup F] [Module K F]

/-- An injective morphism of vector spaces induces an injective morphism of exterior algebras. -/
lemma map_injective_field {f : E →ₗ[K] F} (hf : LinearMap.ker f = ⊥) :
    Function.Injective (map f) :=
  map_injective (LinearMap.exists_leftInverse_of_injective f hf)

end ExteriorAlgebra

namespace TensorAlgebra

variable {R M}

/-- The canonical image of the `TensorAlgebra` in the `ExteriorAlgebra`, which maps
`TensorAlgebra.ι R x` to `ExteriorAlgebra.ι R x`. -/
def toExterior : TensorAlgebra R M →ₐ[R] ExteriorAlgebra R M :=
  TensorAlgebra.lift R (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M)
#align tensor_algebra.to_exterior TensorAlgebra.toExterior

@[simp]
theorem toExterior_ι (m : M) :
    TensorAlgebra.toExterior (TensorAlgebra.ι R m) = ExteriorAlgebra.ι R m := by
  simp [toExterior]
#align tensor_algebra.to_exterior_ι TensorAlgebra.toExterior_ι

end TensorAlgebra
