/-

Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.PowerBasis

#align_import ring_theory.is_adjoin_root from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# A predicate on adjoining roots of polynomial

This file defines a predicate `IsAdjoinRoot S f`, which states that the ring `S` can be
constructed by adjoining a specified root of the polynomial `f : R[X]` to `R`.
This predicate is useful when the same ring can be generated by adjoining the root of different
polynomials, and you want to vary which polynomial you're considering.

The results in this file are intended to mirror those in `RingTheory.AdjoinRoot`,
in order to provide an easier way to translate results from one to the other.

## Motivation

`AdjoinRoot` presents one construction of a ring `R[α]`. However, it is possible to obtain
rings of this form in many ways, such as `NumberField.ringOfIntegers ℚ(√-5)`,
or `Algebra.adjoin R {α, α^2}`, or `IntermediateField.adjoin R {α, 2 - α}`,
or even if we want to view `ℂ` as adjoining a root of `X^2 + 1` to `ℝ`.

## Main definitions

The two main predicates in this file are:

 * `IsAdjoinRoot S f`: `S` is generated by adjoining a specified root of `f : R[X]` to `R`
 * `IsAdjoinRootMonic S f`: `S` is generated by adjoining a root of the monic polynomial
   `f : R[X]` to `R`

Using `IsAdjoinRoot` to map into `S`:

 * `IsAdjoinRoot.map`: inclusion from `R[X]` to `S`
 * `IsAdjoinRoot.root`: the specific root adjoined to `R` to give `S`

Using `IsAdjoinRoot` to map out of `S`:

 * `IsAdjoinRoot.repr`: choose a non-unique representative in `R[X]`
 * `IsAdjoinRoot.lift`, `IsAdjoinRoot.liftHom`: lift a morphism `R →+* T` to `S →+* T`
 * `IsAdjoinRootMonic.modByMonicHom`: a unique representative in `R[X]` if `f` is monic

## Main results

 * `AdjoinRoot.isAdjoinRoot` and `AdjoinRoot.isAdjoinRootMonic`:
   `AdjoinRoot` satisfies the conditions on `IsAdjoinRoot`(`_monic`)
 * `IsAdjoinRootMonic.powerBasis`: the `root` generates a power basis on `S` over `R`
 * `IsAdjoinRoot.aequiv`: algebra isomorphism showing adjoining a root gives a unique ring
   up to isomorphism
 * `IsAdjoinRoot.ofEquiv`: transfer `IsAdjoinRoot` across an algebra isomorphism
 * `IsAdjoinRootMonic.minpoly_eq`: the minimal polynomial of the adjoined root of `f` is equal to
   `f`, if `f` is irreducible and monic, and `R` is a GCD domain
-/


open scoped Polynomial

open Polynomial

noncomputable section

universe u v

-- Porting note: this looks like something that should not be here
-- section MoveMe
--
-- end MoveMe

-- This class doesn't really make sense on a predicate
/-- `IsAdjoinRoot S f` states that the ring `S` can be constructed by adjoining a specified root
of the polynomial `f : R[X]` to `R`.

Compare `PowerBasis R S`, which does not explicitly specify which polynomial we adjoin a root of
(in particular `f` does not need to be the minimal polynomial of the root we adjoin),
and `AdjoinRoot` which constructs a new type.

This is not a typeclass because the choice of root given `S` and `f` is not unique.
-/
-- Porting note(#5171): this linter isn't ported yet.
-- @[nolint has_nonempty_instance]
structure IsAdjoinRoot {R : Type u} (S : Type v) [CommSemiring R] [Semiring S] [Algebra R S]
    (f : R[X]) : Type max u v where
  map : R[X] →+* S
  map_surjective : Function.Surjective map
  ker_map : RingHom.ker map = Ideal.span {f}
  algebraMap_eq : algebraMap R S = map.comp Polynomial.C
#align is_adjoin_root IsAdjoinRoot

-- This class doesn't really make sense on a predicate
/-- `IsAdjoinRootMonic S f` states that the ring `S` can be constructed by adjoining a specified
root of the monic polynomial `f : R[X]` to `R`.

As long as `f` is monic, there is a well-defined representation of elements of `S` as polynomials
in `R[X]` of degree lower than `deg f` (see `modByMonicHom` and `coeff`). In particular,
we have `IsAdjoinRootMonic.powerBasis`.

Bundling `Monic` into this structure is very useful when working with explicit `f`s such as
`X^2 - C a * X - C b` since it saves you carrying around the proofs of monicity.
-/
-- @[nolint has_nonempty_instance] -- Porting note: This linter does not exist yet.
structure IsAdjoinRootMonic {R : Type u} (S : Type v) [CommSemiring R] [Semiring S] [Algebra R S]
    (f : R[X]) extends IsAdjoinRoot S f where
  Monic : Monic f
#align is_adjoin_root_monic IsAdjoinRootMonic

section Ring

variable {R : Type u} {S : Type v} [CommRing R] [Ring S] {f : R[X]} [Algebra R S]

namespace IsAdjoinRoot

/-- `(h : IsAdjoinRoot S f).root` is the root of `f` that can be adjoined to generate `S`. -/
def root (h : IsAdjoinRoot S f) : S :=
  h.map X
#align is_adjoin_root.root IsAdjoinRoot.root

theorem subsingleton (h : IsAdjoinRoot S f) [Subsingleton R] : Subsingleton S :=
  h.map_surjective.subsingleton
#align is_adjoin_root.subsingleton IsAdjoinRoot.subsingleton

theorem algebraMap_apply (h : IsAdjoinRoot S f) (x : R) :
    algebraMap R S x = h.map (Polynomial.C x) := by rw [h.algebraMap_eq, RingHom.comp_apply]
#align is_adjoin_root.algebra_map_apply IsAdjoinRoot.algebraMap_apply

@[simp]
theorem mem_ker_map (h : IsAdjoinRoot S f) {p} : p ∈ RingHom.ker h.map ↔ f ∣ p := by
  rw [h.ker_map, Ideal.mem_span_singleton]
#align is_adjoin_root.mem_ker_map IsAdjoinRoot.mem_ker_map

theorem map_eq_zero_iff (h : IsAdjoinRoot S f) {p} : h.map p = 0 ↔ f ∣ p := by
  rw [← h.mem_ker_map, RingHom.mem_ker]
#align is_adjoin_root.map_eq_zero_iff IsAdjoinRoot.map_eq_zero_iff

@[simp]
theorem map_X (h : IsAdjoinRoot S f) : h.map X = h.root := rfl
set_option linter.uppercaseLean3 false in
#align is_adjoin_root.map_X IsAdjoinRoot.map_X

@[simp]
theorem map_self (h : IsAdjoinRoot S f) : h.map f = 0 := h.map_eq_zero_iff.mpr dvd_rfl
#align is_adjoin_root.map_self IsAdjoinRoot.map_self

@[simp]
theorem aeval_eq (h : IsAdjoinRoot S f) (p : R[X]) : aeval h.root p = h.map p :=
  Polynomial.induction_on p (fun x => by rw [aeval_C, h.algebraMap_apply])
    (fun p q ihp ihq => by rw [AlgHom.map_add, RingHom.map_add, ihp, ihq]) fun n x _ => by
    rw [AlgHom.map_mul, aeval_C, AlgHom.map_pow, aeval_X, RingHom.map_mul, ← h.algebraMap_apply,
      RingHom.map_pow, map_X]
#align is_adjoin_root.aeval_eq IsAdjoinRoot.aeval_eq

-- @[simp] -- Porting note (#10618): simp can prove this
theorem aeval_root (h : IsAdjoinRoot S f) : aeval h.root f = 0 := by rw [aeval_eq, map_self]
#align is_adjoin_root.aeval_root IsAdjoinRoot.aeval_root

/-- Choose an arbitrary representative so that `h.map (h.repr x) = x`.

If `f` is monic, use `IsAdjoinRootMonic.modByMonicHom` for a unique choice of representative.
-/
def repr (h : IsAdjoinRoot S f) (x : S) : R[X] :=
  (h.map_surjective x).choose
#align is_adjoin_root.repr IsAdjoinRoot.repr

theorem map_repr (h : IsAdjoinRoot S f) (x : S) : h.map (h.repr x) = x :=
  (h.map_surjective x).choose_spec
#align is_adjoin_root.map_repr IsAdjoinRoot.map_repr

/-- `repr` preserves zero, up to multiples of `f` -/
theorem repr_zero_mem_span (h : IsAdjoinRoot S f) : h.repr 0 ∈ Ideal.span ({f} : Set R[X]) := by
  rw [← h.ker_map, RingHom.mem_ker, h.map_repr]
#align is_adjoin_root.repr_zero_mem_span IsAdjoinRoot.repr_zero_mem_span

/-- `repr` preserves addition, up to multiples of `f` -/
theorem repr_add_sub_repr_add_repr_mem_span (h : IsAdjoinRoot S f) (x y : S) :
    h.repr (x + y) - (h.repr x + h.repr y) ∈ Ideal.span ({f} : Set R[X]) := by
  rw [← h.ker_map, RingHom.mem_ker, map_sub, h.map_repr, map_add, h.map_repr, h.map_repr, sub_self]
#align is_adjoin_root.repr_add_sub_repr_add_repr_mem_span IsAdjoinRoot.repr_add_sub_repr_add_repr_mem_span

/-- Extensionality of the `IsAdjoinRoot` structure itself. See `IsAdjoinRootMonic.ext_elem`
for extensionality of the ring elements. -/
theorem ext_map (h h' : IsAdjoinRoot S f) (eq : ∀ x, h.map x = h'.map x) : h = h' := by
  cases h; cases h'; congr
  exact RingHom.ext eq
#align is_adjoin_root.ext_map IsAdjoinRoot.ext_map

/-- Extensionality of the `IsAdjoinRoot` structure itself. See `IsAdjoinRootMonic.ext_elem`
for extensionality of the ring elements. -/
@[ext]
theorem ext (h h' : IsAdjoinRoot S f) (eq : h.root = h'.root) : h = h' :=
  h.ext_map h' fun x => by rw [← h.aeval_eq, ← h'.aeval_eq, eq]
#align is_adjoin_root.ext IsAdjoinRoot.ext

section lift

variable {T : Type*} [CommRing T] {i : R →+* T} {x : T} (hx : f.eval₂ i x = 0)

/-- Auxiliary lemma for `IsAdjoinRoot.lift` -/
theorem eval₂_repr_eq_eval₂_of_map_eq (h : IsAdjoinRoot S f) (z : S) (w : R[X])
    (hzw : h.map w = z) : (h.repr z).eval₂ i x = w.eval₂ i x := by
  rw [eq_comm, ← sub_eq_zero, ← h.map_repr z, ← map_sub, h.map_eq_zero_iff] at hzw
  obtain ⟨y, hy⟩ := hzw
  rw [← sub_eq_zero, ← eval₂_sub, hy, eval₂_mul, hx, zero_mul]
#align is_adjoin_root.eval₂_repr_eq_eval₂_of_map_eq IsAdjoinRoot.eval₂_repr_eq_eval₂_of_map_eq

variable (i x)

-- To match `AdjoinRoot.lift`
/-- Lift a ring homomorphism `R →+* T` to `S →+* T` by specifying a root `x` of `f` in `T`,
where `S` is given by adjoining a root of `f` to `R`. -/
def lift (h : IsAdjoinRoot S f) : S →+* T where
  toFun z := (h.repr z).eval₂ i x
  map_zero' := by
    dsimp only -- Porting note (#10752): added `dsimp only`
    rw [h.eval₂_repr_eq_eval₂_of_map_eq hx _ _ (map_zero _), eval₂_zero]
  map_add' z w := by
    dsimp only -- Porting note (#10752): added `dsimp only`
    rw [h.eval₂_repr_eq_eval₂_of_map_eq hx _ (h.repr z + h.repr w), eval₂_add]
    · rw [map_add, map_repr, map_repr]
  map_one' := by
    dsimp only -- Porting note (#10752): added `dsimp only`
    rw [h.eval₂_repr_eq_eval₂_of_map_eq hx _ _ (map_one _), eval₂_one]
  map_mul' z w := by
    dsimp only -- Porting note (#10752): added `dsimp only`
    rw [h.eval₂_repr_eq_eval₂_of_map_eq hx _ (h.repr z * h.repr w), eval₂_mul]
    · rw [map_mul, map_repr, map_repr]
#align is_adjoin_root.lift IsAdjoinRoot.lift

variable {i x}

@[simp]
theorem lift_map (h : IsAdjoinRoot S f) (z : R[X]) : h.lift i x hx (h.map z) = z.eval₂ i x := by
  rw [lift, RingHom.coe_mk]
  dsimp -- Porting note (#11227):added a `dsimp`
  rw [h.eval₂_repr_eq_eval₂_of_map_eq hx _ _ rfl]
#align is_adjoin_root.lift_map IsAdjoinRoot.lift_map

@[simp]
theorem lift_root (h : IsAdjoinRoot S f) : h.lift i x hx h.root = x := by
  rw [← h.map_X, lift_map, eval₂_X]
#align is_adjoin_root.lift_root IsAdjoinRoot.lift_root

@[simp]
theorem lift_algebraMap (h : IsAdjoinRoot S f) (a : R) : h.lift i x hx (algebraMap R S a) = i a :=
  by rw [h.algebraMap_apply, lift_map, eval₂_C]
#align is_adjoin_root.lift_algebra_map IsAdjoinRoot.lift_algebraMap

/-- Auxiliary lemma for `apply_eq_lift` -/
theorem apply_eq_lift (h : IsAdjoinRoot S f) (g : S →+* T) (hmap : ∀ a, g (algebraMap R S a) = i a)
    (hroot : g h.root = x) (a : S) : g a = h.lift i x hx a := by
  rw [← h.map_repr a, Polynomial.as_sum_range_C_mul_X_pow (h.repr a)]
  simp only [map_sum, map_mul, map_pow, h.map_X, hroot, ← h.algebraMap_apply, hmap, lift_root,
    lift_algebraMap]
#align is_adjoin_root.apply_eq_lift IsAdjoinRoot.apply_eq_lift

/-- Unicity of `lift`: a map that agrees on `R` and `h.root` agrees with `lift` everywhere. -/
theorem eq_lift (h : IsAdjoinRoot S f) (g : S →+* T) (hmap : ∀ a, g (algebraMap R S a) = i a)
    (hroot : g h.root = x) : g = h.lift i x hx :=
  RingHom.ext (h.apply_eq_lift hx g hmap hroot)
#align is_adjoin_root.eq_lift IsAdjoinRoot.eq_lift

variable [Algebra R T] (hx' : aeval x f = 0)
variable (x)

-- To match `AdjoinRoot.liftHom`
/-- Lift the algebra map `R → T` to `S →ₐ[R] T` by specifying a root `x` of `f` in `T`,
where `S` is given by adjoining a root of `f` to `R`. -/
def liftHom (h : IsAdjoinRoot S f) : S →ₐ[R] T :=
  { h.lift (algebraMap R T) x hx' with commutes' := fun a => h.lift_algebraMap hx' a }
#align is_adjoin_root.lift_hom IsAdjoinRoot.liftHom

variable {x}

@[simp]
theorem coe_liftHom (h : IsAdjoinRoot S f) :
    (h.liftHom x hx' : S →+* T) = h.lift (algebraMap R T) x hx' := rfl
#align is_adjoin_root.coe_lift_hom IsAdjoinRoot.coe_liftHom

theorem lift_algebraMap_apply (h : IsAdjoinRoot S f) (z : S) :
    h.lift (algebraMap R T) x hx' z = h.liftHom x hx' z := rfl
#align is_adjoin_root.lift_algebra_map_apply IsAdjoinRoot.lift_algebraMap_apply

@[simp]
theorem liftHom_map (h : IsAdjoinRoot S f) (z : R[X]) : h.liftHom x hx' (h.map z) = aeval x z := by
  rw [← lift_algebraMap_apply, lift_map, aeval_def]
#align is_adjoin_root.lift_hom_map IsAdjoinRoot.liftHom_map

@[simp]
theorem liftHom_root (h : IsAdjoinRoot S f) : h.liftHom x hx' h.root = x := by
  rw [← lift_algebraMap_apply, lift_root]
#align is_adjoin_root.lift_hom_root IsAdjoinRoot.liftHom_root

/-- Unicity of `liftHom`: a map that agrees on `h.root` agrees with `liftHom` everywhere. -/
theorem eq_liftHom (h : IsAdjoinRoot S f) (g : S →ₐ[R] T) (hroot : g h.root = x) :
    g = h.liftHom x hx' :=
  AlgHom.ext (h.apply_eq_lift hx' g g.commutes hroot)
#align is_adjoin_root.eq_lift_hom IsAdjoinRoot.eq_liftHom

end lift

end IsAdjoinRoot

namespace AdjoinRoot

variable (f)

/-- `AdjoinRoot f` is indeed given by adjoining a root of `f`. -/
protected def isAdjoinRoot : IsAdjoinRoot (AdjoinRoot f) f where
  map := AdjoinRoot.mk f
  map_surjective := Ideal.Quotient.mk_surjective
  ker_map := by
    ext
    rw [RingHom.mem_ker, ← @AdjoinRoot.mk_self _ _ f, AdjoinRoot.mk_eq_mk, Ideal.mem_span_singleton,
      ← dvd_add_left (dvd_refl f), sub_add_cancel]
  algebraMap_eq := AdjoinRoot.algebraMap_eq f
#align adjoin_root.is_adjoin_root AdjoinRoot.isAdjoinRoot

/-- `AdjoinRoot f` is indeed given by adjoining a root of `f`. If `f` is monic this is more
powerful than `AdjoinRoot.isAdjoinRoot`. -/
protected def isAdjoinRootMonic (hf : Monic f) : IsAdjoinRootMonic (AdjoinRoot f) f :=
  { AdjoinRoot.isAdjoinRoot f with Monic := hf }
#align adjoin_root.is_adjoin_root_monic AdjoinRoot.isAdjoinRootMonic

@[simp]
theorem isAdjoinRoot_map_eq_mk : (AdjoinRoot.isAdjoinRoot f).map = AdjoinRoot.mk f :=
  rfl
#align adjoin_root.is_adjoin_root_map_eq_mk AdjoinRoot.isAdjoinRoot_map_eq_mk

@[simp]
theorem isAdjoinRootMonic_map_eq_mk (hf : f.Monic) :
    (AdjoinRoot.isAdjoinRootMonic f hf).map = AdjoinRoot.mk f :=
  rfl
#align adjoin_root.is_adjoin_root_monic_map_eq_mk AdjoinRoot.isAdjoinRootMonic_map_eq_mk

@[simp]
theorem isAdjoinRoot_root_eq_root : (AdjoinRoot.isAdjoinRoot f).root = AdjoinRoot.root f := by
  simp only [IsAdjoinRoot.root, AdjoinRoot.root, AdjoinRoot.isAdjoinRoot_map_eq_mk]
#align adjoin_root.is_adjoin_root_root_eq_root AdjoinRoot.isAdjoinRoot_root_eq_root

@[simp]
theorem isAdjoinRootMonic_root_eq_root (hf : Monic f) :
    (AdjoinRoot.isAdjoinRootMonic f hf).root = AdjoinRoot.root f := by
  simp only [IsAdjoinRoot.root, AdjoinRoot.root, AdjoinRoot.isAdjoinRootMonic_map_eq_mk]
#align adjoin_root.is_adjoin_root_monic_root_eq_root AdjoinRoot.isAdjoinRootMonic_root_eq_root

end AdjoinRoot

namespace IsAdjoinRootMonic

open IsAdjoinRoot

theorem map_modByMonic (h : IsAdjoinRootMonic S f) (g : R[X]) : h.map (g %ₘ f) = h.map g := by
  rw [← RingHom.sub_mem_ker_iff, mem_ker_map, modByMonic_eq_sub_mul_div _ h.Monic, sub_right_comm,
    sub_self, zero_sub, dvd_neg]
  exact ⟨_, rfl⟩
#align is_adjoin_root_monic.map_mod_by_monic IsAdjoinRootMonic.map_modByMonic

theorem modByMonic_repr_map (h : IsAdjoinRootMonic S f) (g : R[X]) :
    h.repr (h.map g) %ₘ f = g %ₘ f :=
  modByMonic_eq_of_dvd_sub h.Monic <| by rw [← h.mem_ker_map, RingHom.sub_mem_ker_iff, map_repr]
#align is_adjoin_root_monic.mod_by_monic_repr_map IsAdjoinRootMonic.modByMonic_repr_map

/-- `IsAdjoinRoot.modByMonicHom` sends the equivalence class of `f` mod `g` to `f %ₘ g`. -/
def modByMonicHom (h : IsAdjoinRootMonic S f) : S →ₗ[R] R[X] where
  toFun x := h.repr x %ₘ f
  map_add' x y := by
    conv_lhs =>
      rw [← h.map_repr x, ← h.map_repr y, ← map_add]
      dsimp only -- Porting note (#10752): added `dsimp only`
      rw [h.modByMonic_repr_map, add_modByMonic]
  map_smul' c x := by
    rw [RingHom.id_apply, ← h.map_repr x, Algebra.smul_def, h.algebraMap_apply, ← map_mul]
    dsimp only -- Porting note (#10752): added `dsimp only`
    rw [h.modByMonic_repr_map, ← smul_eq_C_mul, smul_modByMonic, h.map_repr]
#align is_adjoin_root_monic.mod_by_monic_hom IsAdjoinRootMonic.modByMonicHom

@[simp]
theorem modByMonicHom_map (h : IsAdjoinRootMonic S f) (g : R[X]) :
    h.modByMonicHom (h.map g) = g %ₘ f := h.modByMonic_repr_map g
#align is_adjoin_root_monic.mod_by_monic_hom_map IsAdjoinRootMonic.modByMonicHom_map

@[simp]
theorem map_modByMonicHom (h : IsAdjoinRootMonic S f) (x : S) : h.map (h.modByMonicHom x) = x := by
  rw [modByMonicHom, LinearMap.coe_mk]
  dsimp -- Porting note (#11227):added a `dsimp`
  rw [map_modByMonic, map_repr]
#align is_adjoin_root_monic.map_mod_by_monic_hom IsAdjoinRootMonic.map_modByMonicHom

@[simp]
theorem modByMonicHom_root_pow (h : IsAdjoinRootMonic S f) {n : ℕ} (hdeg : n < natDegree f) :
    h.modByMonicHom (h.root ^ n) = X ^ n := by
  nontriviality R
  rw [← h.map_X, ← map_pow, modByMonicHom_map, modByMonic_eq_self_iff h.Monic, degree_X_pow]
  contrapose! hdeg
  simpa [natDegree_le_iff_degree_le] using hdeg
#align is_adjoin_root_monic.mod_by_monic_hom_root_pow IsAdjoinRootMonic.modByMonicHom_root_pow

@[simp]
theorem modByMonicHom_root (h : IsAdjoinRootMonic S f) (hdeg : 1 < natDegree f) :
    h.modByMonicHom h.root = X := by simpa using modByMonicHom_root_pow h hdeg
#align is_adjoin_root_monic.mod_by_monic_hom_root IsAdjoinRootMonic.modByMonicHom_root

/-- The basis on `S` generated by powers of `h.root`.

Auxiliary definition for `IsAdjoinRootMonic.powerBasis`. -/
def basis (h : IsAdjoinRootMonic S f) : Basis (Fin (natDegree f)) R S :=
  Basis.ofRepr
    { toFun := fun x => (h.modByMonicHom x).toFinsupp.comapDomain _ (Fin.val_injective.injOn _)
      invFun := fun g => h.map (ofFinsupp (g.mapDomain _))
      left_inv := fun x => by
        cases subsingleton_or_nontrivial R
        · haveI := h.subsingleton
          exact Subsingleton.elim _ _
        simp only
        rw [Finsupp.mapDomain_comapDomain, Polynomial.eta, h.map_modByMonicHom x]
        · exact Fin.val_injective
        intro i hi
        refine Set.mem_range.mpr ⟨⟨i, ?_⟩, rfl⟩
        contrapose! hi
        simp only [Polynomial.toFinsupp_apply, Classical.not_not, Finsupp.mem_support_iff, Ne,
          modByMonicHom, LinearMap.coe_mk, Finset.mem_coe]
        by_cases hx : h.toIsAdjoinRoot.repr x %ₘ f = 0
        · simp [hx]
        refine coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le ?_ hi)
        dsimp -- Porting note (#11227):added a `dsimp`
        rw [natDegree_lt_natDegree_iff hx]
        · exact degree_modByMonic_lt _ h.Monic
      right_inv := fun g => by
        nontriviality R
        ext i
        simp only [h.modByMonicHom_map, Finsupp.comapDomain_apply, Polynomial.toFinsupp_apply]
        rw [(Polynomial.modByMonic_eq_self_iff h.Monic).mpr, Polynomial.coeff]
        dsimp only -- Porting note (#10752): added `dsimp only`
        rw [Finsupp.mapDomain_apply Fin.val_injective]
        rw [degree_eq_natDegree h.Monic.ne_zero, degree_lt_iff_coeff_zero]
        intro m hm
        rw [Polynomial.coeff]
        dsimp only -- Porting note (#10752): added `dsimp only`
        rw [Finsupp.mapDomain_notin_range]
        rw [Set.mem_range, not_exists]
        rintro i rfl
        exact i.prop.not_le hm
      map_add' := fun x y => by
        dsimp only -- Porting note (#10752): added `dsimp only`
        rw [map_add, toFinsupp_add, Finsupp.comapDomain_add_of_injective Fin.val_injective]
      -- Porting note: the original simp proof with the same lemmas does not work
      -- See https://github.com/leanprover-community/mathlib4/issues/5026
      -- simp only [map_add, Finsupp.comapDomain_add_of_injective Fin.val_injective, toFinsupp_add]
      map_smul' := fun c x => by
        dsimp only -- Porting note (#10752): added `dsimp only`
        rw [map_smul, toFinsupp_smul, Finsupp.comapDomain_smul_of_injective Fin.val_injective,
          RingHom.id_apply] }
      -- Porting note: the original simp proof with the same lemmas does not work
      -- See https://github.com/leanprover-community/mathlib4/issues/5026
      -- simp only [map_smul, Finsupp.comapDomain_smul_of_injective Fin.val_injective,
      --   RingHom.id_apply, toFinsupp_smul] }
#align is_adjoin_root_monic.basis IsAdjoinRootMonic.basis

@[simp]
theorem basis_apply (h : IsAdjoinRootMonic S f) (i) : h.basis i = h.root ^ (i : ℕ) :=
  Basis.apply_eq_iff.mpr <|
    show (h.modByMonicHom (h.toIsAdjoinRoot.root ^ (i : ℕ))).toFinsupp.comapDomain _
          (Fin.val_injective.injOn _) = Finsupp.single _ _ by
      ext j
      rw [Finsupp.comapDomain_apply, modByMonicHom_root_pow]
      · rw [X_pow_eq_monomial, toFinsupp_monomial, Finsupp.single_apply_left Fin.val_injective]
      · exact i.is_lt
#align is_adjoin_root_monic.basis_apply IsAdjoinRootMonic.basis_apply

theorem deg_pos [Nontrivial S] (h : IsAdjoinRootMonic S f) : 0 < natDegree f := by
  rcases h.basis.index_nonempty with ⟨⟨i, hi⟩⟩
  exact (Nat.zero_le _).trans_lt hi
#align is_adjoin_root_monic.deg_pos IsAdjoinRootMonic.deg_pos

theorem deg_ne_zero [Nontrivial S] (h : IsAdjoinRootMonic S f) : natDegree f ≠ 0 :=
  h.deg_pos.ne'
#align is_adjoin_root_monic.deg_ne_zero IsAdjoinRootMonic.deg_ne_zero

/-- If `f` is monic, the powers of `h.root` form a basis. -/
@[simps! gen dim basis]
def powerBasis (h : IsAdjoinRootMonic S f) : PowerBasis R S where
  gen := h.root
  dim := natDegree f
  basis := h.basis
  basis_eq_pow := h.basis_apply
#align is_adjoin_root_monic.power_basis IsAdjoinRootMonic.powerBasis

@[simp]
theorem basis_repr (h : IsAdjoinRootMonic S f) (x : S) (i : Fin (natDegree f)) :
    h.basis.repr x i = (h.modByMonicHom x).coeff (i : ℕ) := by
  change (h.modByMonicHom x).toFinsupp.comapDomain _ ( Fin.val_injective.injOn _) i = _
  rw [Finsupp.comapDomain_apply, Polynomial.toFinsupp_apply]
#align is_adjoin_root_monic.basis_repr IsAdjoinRootMonic.basis_repr

theorem basis_one (h : IsAdjoinRootMonic S f) (hdeg : 1 < natDegree f) :
    h.basis ⟨1, hdeg⟩ = h.root := by rw [h.basis_apply, Fin.val_mk, pow_one]
#align is_adjoin_root_monic.basis_one IsAdjoinRootMonic.basis_one

/-- `IsAdjoinRootMonic.liftPolyₗ` lifts a linear map on polynomials to a linear map on `S`. -/
@[simps!]
def liftPolyₗ {T : Type*} [AddCommGroup T] [Module R T] (h : IsAdjoinRootMonic S f)
    (g : R[X] →ₗ[R] T) : S →ₗ[R] T :=
  g.comp h.modByMonicHom
#align is_adjoin_root_monic.lift_polyₗ IsAdjoinRootMonic.liftPolyₗ

/-- `IsAdjoinRootMonic.coeff h x i` is the `i`th coefficient of the representative of `x : S`.
-/
def coeff (h : IsAdjoinRootMonic S f) : S →ₗ[R] ℕ → R :=
  h.liftPolyₗ
    { toFun := Polynomial.coeff
      map_add' := fun p q => funext (Polynomial.coeff_add p q)
      map_smul' := fun c p => funext (Polynomial.coeff_smul c p) }
#align is_adjoin_root_monic.coeff IsAdjoinRootMonic.coeff

theorem coeff_apply_lt (h : IsAdjoinRootMonic S f) (z : S) (i : ℕ) (hi : i < natDegree f) :
    h.coeff z i = h.basis.repr z ⟨i, hi⟩ := by
  simp only [coeff, LinearMap.comp_apply, Finsupp.lcoeFun_apply, Finsupp.lmapDomain_apply,
    LinearEquiv.coe_coe, liftPolyₗ_apply, LinearMap.coe_mk, h.basis_repr]
  rfl
#align is_adjoin_root_monic.coeff_apply_lt IsAdjoinRootMonic.coeff_apply_lt

theorem coeff_apply_coe (h : IsAdjoinRootMonic S f) (z : S) (i : Fin (natDegree f)) :
    h.coeff z i = h.basis.repr z i := h.coeff_apply_lt z i i.prop
#align is_adjoin_root_monic.coeff_apply_coe IsAdjoinRootMonic.coeff_apply_coe

theorem coeff_apply_le (h : IsAdjoinRootMonic S f) (z : S) (i : ℕ) (hi : natDegree f ≤ i) :
    h.coeff z i = 0 := by
  simp only [coeff, LinearMap.comp_apply, Finsupp.lcoeFun_apply, Finsupp.lmapDomain_apply,
    LinearEquiv.coe_coe, liftPolyₗ_apply, LinearMap.coe_mk, h.basis_repr]
  nontriviality R
  exact
    Polynomial.coeff_eq_zero_of_degree_lt
      ((degree_modByMonic_lt _ h.Monic).trans_le (Polynomial.degree_le_of_natDegree_le hi))
#align is_adjoin_root_monic.coeff_apply_le IsAdjoinRootMonic.coeff_apply_le

theorem coeff_apply (h : IsAdjoinRootMonic S f) (z : S) (i : ℕ) :
    h.coeff z i = if hi : i < natDegree f then h.basis.repr z ⟨i, hi⟩ else 0 := by
  split_ifs with hi
  · exact h.coeff_apply_lt z i hi
  · exact h.coeff_apply_le z i (le_of_not_lt hi)
#align is_adjoin_root_monic.coeff_apply IsAdjoinRootMonic.coeff_apply

theorem coeff_root_pow (h : IsAdjoinRootMonic S f) {n} (hn : n < natDegree f) :
    h.coeff (h.root ^ n) = Pi.single n 1 := by
  ext i
  rw [coeff_apply]
  split_ifs with hi
  · calc
      h.basis.repr (h.root ^ n) ⟨i, _⟩ = h.basis.repr (h.basis ⟨n, hn⟩) ⟨i, hi⟩ := by
        rw [h.basis_apply, Fin.val_mk]
      _ = Pi.single (f := fun _ => R) ((⟨n, hn⟩ : Fin _) : ℕ) (1 : (fun _ => R) n)
        ↑(⟨i, _⟩ : Fin _) := by
        rw [h.basis.repr_self, ← Finsupp.single_eq_pi_single,
          Finsupp.single_apply_left Fin.val_injective]
      _ = Pi.single (f := fun _ => R) n 1 i := by rw [Fin.val_mk, Fin.val_mk]
  · refine (Pi.single_eq_of_ne (f := fun _ => R) ?_ (1 : (fun _ => R) n)).symm
    rintro rfl
    simp [hi] at hn
#align is_adjoin_root_monic.coeff_root_pow IsAdjoinRootMonic.coeff_root_pow

theorem coeff_one [Nontrivial S] (h : IsAdjoinRootMonic S f) : h.coeff 1 = Pi.single 0 1 := by
  rw [← h.coeff_root_pow h.deg_pos, pow_zero]
#align is_adjoin_root_monic.coeff_one IsAdjoinRootMonic.coeff_one

theorem coeff_root (h : IsAdjoinRootMonic S f) (hdeg : 1 < natDegree f) :
    h.coeff h.root = Pi.single 1 1 := by rw [← h.coeff_root_pow hdeg, pow_one]
#align is_adjoin_root_monic.coeff_root IsAdjoinRootMonic.coeff_root

theorem coeff_algebraMap [Nontrivial S] (h : IsAdjoinRootMonic S f) (x : R) :
    h.coeff (algebraMap R S x) = Pi.single 0 x := by
  ext i
  rw [Algebra.algebraMap_eq_smul_one, map_smul, coeff_one, Pi.smul_apply, smul_eq_mul]
  refine' (Pi.apply_single (fun _ y => x * y) _ 0 1 i).trans (by simp)
  intros
  simp
#align is_adjoin_root_monic.coeff_algebra_map IsAdjoinRootMonic.coeff_algebraMap

theorem ext_elem (h : IsAdjoinRootMonic S f) ⦃x y : S⦄
    (hxy : ∀ i < natDegree f, h.coeff x i = h.coeff y i) : x = y :=
  EquivLike.injective h.basis.equivFun <|
    funext fun i => by
      rw [Basis.equivFun_apply, ← h.coeff_apply_coe, Basis.equivFun_apply, ← h.coeff_apply_coe,
        hxy i i.prop]
#align is_adjoin_root_monic.ext_elem IsAdjoinRootMonic.ext_elem

theorem ext_elem_iff (h : IsAdjoinRootMonic S f) {x y : S} :
    x = y ↔ ∀ i < natDegree f, h.coeff x i = h.coeff y i :=
  ⟨fun hxy _ _=> hxy ▸ rfl, fun hxy => h.ext_elem hxy⟩
#align is_adjoin_root_monic.ext_elem_iff IsAdjoinRootMonic.ext_elem_iff

theorem coeff_injective (h : IsAdjoinRootMonic S f) : Function.Injective h.coeff := fun _ _ hxy =>
  h.ext_elem fun _ _ => hxy ▸ rfl
#align is_adjoin_root_monic.coeff_injective IsAdjoinRootMonic.coeff_injective

theorem isIntegral_root (h : IsAdjoinRootMonic S f) : IsIntegral R h.root :=
  ⟨f, h.Monic, h.aeval_root⟩
#align is_adjoin_root_monic.is_integral_root IsAdjoinRootMonic.isIntegral_root

end IsAdjoinRootMonic

end Ring

section CommRing

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] {f : R[X]}

namespace IsAdjoinRoot

section lift

@[simp]
theorem lift_self_apply (h : IsAdjoinRoot S f) (x : S) :
    h.lift (algebraMap R S) h.root h.aeval_root x = x := by
  rw [← h.map_repr x, lift_map, ← aeval_def, h.aeval_eq]
#align is_adjoin_root.lift_self_apply IsAdjoinRoot.lift_self_apply

theorem lift_self (h : IsAdjoinRoot S f) :
    h.lift (algebraMap R S) h.root h.aeval_root = RingHom.id S :=
  RingHom.ext h.lift_self_apply
#align is_adjoin_root.lift_self IsAdjoinRoot.lift_self

end lift

section Equiv

variable {T : Type*} [CommRing T] [Algebra R T]

/-- Adjoining a root gives a unique ring up to algebra isomorphism.

This is the converse of `IsAdjoinRoot.ofEquiv`: this turns an `IsAdjoinRoot` into an
`AlgEquiv`, and `IsAdjoinRoot.ofEquiv` turns an `AlgEquiv` into an `IsAdjoinRoot`.
-/
def aequiv (h : IsAdjoinRoot S f) (h' : IsAdjoinRoot T f) : S ≃ₐ[R] T :=
  { h.liftHom h'.root h'.aeval_root with
    toFun := h.liftHom h'.root h'.aeval_root
    invFun := h'.liftHom h.root h.aeval_root
    left_inv := fun x => by rw [← h.map_repr x, liftHom_map, aeval_eq, liftHom_map, aeval_eq]
    right_inv := fun x => by rw [← h'.map_repr x, liftHom_map, aeval_eq, liftHom_map, aeval_eq] }
#align is_adjoin_root.aequiv IsAdjoinRoot.aequiv

@[simp]
theorem aequiv_map (h : IsAdjoinRoot S f) (h' : IsAdjoinRoot T f) (z : R[X]) :
    h.aequiv h' (h.map z) = h'.map z := by rw [aequiv, AlgEquiv.coe_mk, liftHom_map, aeval_eq]
#align is_adjoin_root.aequiv_map IsAdjoinRoot.aequiv_map

@[simp]
theorem aequiv_root (h : IsAdjoinRoot S f) (h' : IsAdjoinRoot T f) : h.aequiv h' h.root = h'.root :=
  by rw [aequiv, AlgEquiv.coe_mk, liftHom_root]
#align is_adjoin_root.aequiv_root IsAdjoinRoot.aequiv_root

@[simp]
theorem aequiv_self (h : IsAdjoinRoot S f) : h.aequiv h = AlgEquiv.refl := by
  ext a; exact h.lift_self_apply a
#align is_adjoin_root.aequiv_self IsAdjoinRoot.aequiv_self

@[simp]
theorem aequiv_symm (h : IsAdjoinRoot S f) (h' : IsAdjoinRoot T f) :
    (h.aequiv h').symm = h'.aequiv h := by ext; rfl
#align is_adjoin_root.aequiv_symm IsAdjoinRoot.aequiv_symm

@[simp]
theorem lift_aequiv {U : Type*} [CommRing U] (h : IsAdjoinRoot S f) (h' : IsAdjoinRoot T f)
    (i : R →+* U) (x hx z) : h'.lift i x hx (h.aequiv h' z) = h.lift i x hx z := by
  rw [← h.map_repr z, aequiv_map, lift_map, lift_map]
#align is_adjoin_root.lift_aequiv IsAdjoinRoot.lift_aequiv

@[simp]
theorem liftHom_aequiv {U : Type*} [CommRing U] [Algebra R U] (h : IsAdjoinRoot S f)
    (h' : IsAdjoinRoot T f) (x : U) (hx z) : h'.liftHom x hx (h.aequiv h' z) = h.liftHom x hx z :=
  h.lift_aequiv h' _ _ hx _
#align is_adjoin_root.lift_hom_aequiv IsAdjoinRoot.liftHom_aequiv

@[simp]
theorem aequiv_aequiv {U : Type*} [CommRing U] [Algebra R U] (h : IsAdjoinRoot S f)
    (h' : IsAdjoinRoot T f) (h'' : IsAdjoinRoot U f) (x) :
    (h'.aequiv h'') (h.aequiv h' x) = h.aequiv h'' x :=
  h.liftHom_aequiv _ _ h''.aeval_root _
#align is_adjoin_root.aequiv_aequiv IsAdjoinRoot.aequiv_aequiv

@[simp]
theorem aequiv_trans {U : Type*} [CommRing U] [Algebra R U] (h : IsAdjoinRoot S f)
    (h' : IsAdjoinRoot T f) (h'' : IsAdjoinRoot U f) :
    (h.aequiv h').trans (h'.aequiv h'') = h.aequiv h'' := by ext z; exact h.aequiv_aequiv h' h'' z
#align is_adjoin_root.aequiv_trans IsAdjoinRoot.aequiv_trans

/-- Transfer `IsAdjoinRoot` across an algebra isomorphism.

This is the converse of `IsAdjoinRoot.aequiv`: this turns an `AlgEquiv` into an `IsAdjoinRoot`,
and `IsAdjoinRoot.aequiv` turns an `IsAdjoinRoot` into an `AlgEquiv`.
-/
@[simps! map_apply]
def ofEquiv (h : IsAdjoinRoot S f) (e : S ≃ₐ[R] T) : IsAdjoinRoot T f where
  map := ((e : S ≃+* T) : S →+* T).comp h.map
  map_surjective := e.surjective.comp h.map_surjective
  ker_map := by
    rw [← RingHom.comap_ker, RingHom.ker_coe_equiv, ← RingHom.ker_eq_comap_bot, h.ker_map]
  algebraMap_eq := by
    ext
    simp only [AlgEquiv.commutes, RingHom.comp_apply, AlgEquiv.coe_ringEquiv,
      RingEquiv.coe_toRingHom, ← h.algebraMap_apply]
#align is_adjoin_root.of_equiv IsAdjoinRoot.ofEquiv

@[simp]
theorem ofEquiv_root (h : IsAdjoinRoot S f) (e : S ≃ₐ[R] T) : (h.ofEquiv e).root = e h.root := rfl
#align is_adjoin_root.of_equiv_root IsAdjoinRoot.ofEquiv_root

@[simp]
theorem aequiv_ofEquiv {U : Type*} [CommRing U] [Algebra R U] (h : IsAdjoinRoot S f)
    (h' : IsAdjoinRoot T f) (e : T ≃ₐ[R] U) : h.aequiv (h'.ofEquiv e) = (h.aequiv h').trans e := by
  ext a; rw [← h.map_repr a, aequiv_map, AlgEquiv.trans_apply, aequiv_map, ofEquiv_map_apply]
#align is_adjoin_root.aequiv_of_equiv IsAdjoinRoot.aequiv_ofEquiv

@[simp]
theorem ofEquiv_aequiv {U : Type*} [CommRing U] [Algebra R U] (h : IsAdjoinRoot S f)
    (h' : IsAdjoinRoot U f) (e : S ≃ₐ[R] T) :
    (h.ofEquiv e).aequiv h' = e.symm.trans (h.aequiv h') := by
  ext a
  rw [← (h.ofEquiv e).map_repr a, aequiv_map, AlgEquiv.trans_apply, ofEquiv_map_apply,
    e.symm_apply_apply, aequiv_map]
#align is_adjoin_root.of_equiv_aequiv IsAdjoinRoot.ofEquiv_aequiv

end Equiv

end IsAdjoinRoot

namespace IsAdjoinRootMonic

theorem minpoly_eq [IsDomain R] [IsDomain S] [NoZeroSMulDivisors R S] [IsIntegrallyClosed R]
    (h : IsAdjoinRootMonic S f) (hirr : Irreducible f) : minpoly R h.root = f :=
  let ⟨q, hq⟩ := minpoly.isIntegrallyClosed_dvd h.isIntegral_root h.aeval_root
  symm <|
    eq_of_monic_of_associated h.Monic (minpoly.monic h.isIntegral_root) <| by
      convert
        Associated.mul_left (minpoly R h.root) <|
          associated_one_iff_isUnit.2 <|
            (hirr.isUnit_or_isUnit hq).resolve_left <| minpoly.not_isUnit R h.root
      rw [mul_one]
#align is_adjoin_root_monic.minpoly_eq IsAdjoinRootMonic.minpoly_eq

end IsAdjoinRootMonic

section Algebra

open AdjoinRoot IsAdjoinRoot minpoly PowerBasis IsAdjoinRootMonic Algebra

theorem Algebra.adjoin.powerBasis'_minpoly_gen [IsDomain R] [IsDomain S] [NoZeroSMulDivisors R S]
    [IsIntegrallyClosed R] {x : S} (hx' : IsIntegral R x) :
    minpoly R x = minpoly R (Algebra.adjoin.powerBasis' hx').gen := by
  haveI := isDomain_of_prime (prime_of_isIntegrallyClosed hx')
  haveI :=
    noZeroSMulDivisors_of_prime_of_degree_ne_zero (prime_of_isIntegrallyClosed hx')
      (ne_of_lt (degree_pos hx')).symm
  rw [← minpolyGen_eq, adjoin.powerBasis', minpolyGen_map, minpolyGen_eq,
    AdjoinRoot.powerBasis'_gen, ← isAdjoinRootMonic_root_eq_root _ (monic hx'), minpoly_eq]
  exact irreducible hx'
#align algebra.adjoin.power_basis'_minpoly_gen Algebra.adjoin.powerBasis'_minpoly_gen

end Algebra

end CommRing
