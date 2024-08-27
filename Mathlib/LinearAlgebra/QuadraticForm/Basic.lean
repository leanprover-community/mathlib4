/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Eric Wieser
-/
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Finset.Sym
import Mathlib.LinearAlgebra.BilinearMap

/-!
# Quadratic maps

This file defines quadratic maps on an `R`-module `M`, taking values in an `R`-module `N`.
An `N`-valued quadratic map on a module `M` over a commutative ring `R` is a map `Q : M → N` such
that:

* `QuadraticMap.map_smul`: `Q (a • x) = (a * a) • Q x`
* `QuadraticMap.polar_add_left`, `QuadraticMap.polar_add_right`,
  `QuadraticMap.polar_smul_left`, `QuadraticMap.polar_smul_right`:
  the map `QuadraticMap.polar Q := fun x y ↦ Q (x + y) - Q x - Q y` is bilinear.

This notion generalizes to commutative semirings using the approach in [izhakian2016][] which
requires that there be a (possibly non-unique) companion bilinear map `B` such that
`∀ x y, Q (x + y) = Q x + Q y + B x y`. Over a ring, this `B` is precisely `QuadraticMap.polar Q`.

To build a `QuadraticMap` from the `polar` axioms, use `QuadraticMap.ofPolar`.

Quadratic maps come with a scalar multiplication, `(a • Q) x = a • Q x`,
and composition with linear maps `f`, `Q.comp f x = Q (f x)`.

## Main definitions

 * `QuadraticMap.ofPolar`: a more familiar constructor that works on rings
 * `QuadraticMap.associated`: associated bilinear map
 * `QuadraticMap.PosDef`: positive definite quadratic maps
 * `QuadraticMap.Anisotropic`: anisotropic quadratic maps
 * `QuadraticMap.discr`: discriminant of a quadratic map
 * `QuadraticMap.IsOrtho`: orthogonality of vectors with respect to a quadratic map.

## Main statements

 * `QuadraticMap.associated_left_inverse`,
 * `QuadraticMap.associated_rightInverse`: in a commutative ring where 2 has
  an inverse, there is a correspondence between quadratic maps and symmetric
  bilinear forms
 * `LinearMap.BilinForm.exists_orthogonal_basis`: There exists an orthogonal basis with
  respect to any nondegenerate, symmetric bilinear map `B`.

## Notation

In this file, the variable `R` is used when a `CommSemiring` structure is available.

The variable `S` is used when `R` itself has a `•` action.

## Implementation notes

While the definition and many results make sense if we drop commutativity assumptions,
the correct definition of a quadratic maps in the noncommutative setting would require
substantial refactors from the current version, such that $Q(rm) = rQ(m)r^*$ for some
suitable conjugation $r^*$.

The [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Quadratic.20Maps/near/395529867)
has some further discussion.

## References

 * https://en.wikipedia.org/wiki/Quadratic_form
 * https://en.wikipedia.org/wiki/Discriminant#Quadratic_forms

## Tags

quadratic map, homogeneous polynomial, quadratic polynomial
-/

universe u v w

variable {S T : Type*}
variable {R : Type*} {M N P A : Type*}

open LinearMap (BilinMap BilinForm)

section Polar

variable [CommRing R] [AddCommGroup M] [AddCommGroup N]

namespace QuadraticMap

/-- Up to a factor 2, `Q.polar` is the associated bilinear map for a quadratic map `Q`.

Source of this name: https://en.wikipedia.org/wiki/Quadratic_form#Generalization
-/
def polar (f : M → N) (x y : M) :=
  f (x + y) - f x - f y

protected theorem map_add (f : M → N) (x y : M) :
    f (x + y) = f x + f y + polar f x y := by
  rw [polar]
  abel

theorem polar_add (f g : M → N) (x y : M) : polar (f + g) x y = polar f x y + polar g x y := by
  simp only [polar, Pi.add_apply]
  abel

theorem polar_neg (f : M → N) (x y : M) : polar (-f) x y = -polar f x y := by
  simp only [polar, Pi.neg_apply, sub_eq_add_neg, neg_add]

theorem polar_smul [Monoid S] [DistribMulAction S N] (f : M → N) (s : S) (x y : M) :
    polar (s • f) x y = s • polar f x y := by simp only [polar, Pi.smul_apply, smul_sub]

theorem polar_comm (f : M → N) (x y : M) : polar f x y = polar f y x := by
  rw [polar, polar, add_comm, sub_sub, sub_sub, add_comm (f x) (f y)]

/-- Auxiliary lemma to express bilinearity of `QuadraticMap.polar` without subtraction. -/
theorem polar_add_left_iff {f : M → N} {x x' y : M} :
    polar f (x + x') y = polar f x y + polar f x' y ↔
      f (x + x' + y) + (f x + f x' + f y) = f (x + x') + f (x' + y) + f (y + x) := by
  simp only [← add_assoc]
  simp only [polar, sub_eq_iff_eq_add, eq_sub_iff_add_eq, sub_add_eq_add_sub, add_sub]
  simp only [add_right_comm _ (f y) _, add_right_comm _ (f x') (f x)]
  rw [add_comm y x, add_right_comm _ _ (f (x + y)), add_comm _ (f (x + y)),
    add_right_comm (f (x + y)), add_left_inj]

theorem polar_comp {F : Type*} [CommRing S] [FunLike F N S] [AddMonoidHomClass F N S]
    (f : M → N) (g : F) (x y : M) :
    polar (g ∘ f) x y = g (polar f x y) := by
  simp only [polar, Pi.smul_apply, Function.comp_apply, map_sub]

end QuadraticMap

end Polar

/-- A quadratic map on a module.

For a more familiar constructor when `R` is a ring, see `QuadraticMap.ofPolar`. -/
structure QuadraticMap (R : Type u) (M : Type v) (N : Type w) [CommSemiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] where
  toFun : M → N
  toFun_smul : ∀ (a : R) (x : M), toFun (a • x) = (a * a) • toFun x
  exists_companion' : ∃ B : BilinMap R M N, ∀ x y, toFun (x + y) = toFun x + toFun y + B x y

section QuadraticForm

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

variable (R M) in
/-- A quadratic form on a module. -/
abbrev QuadraticForm : Type _ := QuadraticMap R M R

end QuadraticForm

namespace QuadraticMap

section DFunLike

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable {Q Q' : QuadraticMap R M N}

instance instFunLike : FunLike (QuadraticMap R M N) M N where
  coe := toFun
  coe_injective' x y h := by cases x; cases y; congr

/-- Helper instance for when there's too many metavariables to apply
`DFunLike.hasCoeToFun` directly. -/
instance : CoeFun (QuadraticMap R M N) fun _ => M → N :=
  ⟨DFunLike.coe⟩

variable (Q)

/-- The `simp` normal form for a quadratic map is `DFunLike.coe`, not `toFun`. -/
@[simp]
theorem toFun_eq_coe : Q.toFun = ⇑Q :=
  rfl

-- this must come after the coe_to_fun definition
initialize_simps_projections QuadraticMap (toFun → apply)

variable {Q}

@[ext]
theorem ext (H : ∀ x : M, Q x = Q' x) : Q = Q' :=
  DFunLike.ext _ _ H

theorem congr_fun (h : Q = Q') (x : M) : Q x = Q' x :=
  DFunLike.congr_fun h _

/-- Copy of a `QuadraticMap` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (Q : QuadraticMap R M N) (Q' : M → N) (h : Q' = ⇑Q) : QuadraticMap R M N where
  toFun := Q'
  toFun_smul := h.symm ▸ Q.toFun_smul
  exists_companion' := h.symm ▸ Q.exists_companion'

@[simp]
theorem coe_copy (Q : QuadraticMap R M N) (Q' : M → N) (h : Q' = ⇑Q) : ⇑(Q.copy Q' h) = Q' :=
  rfl

theorem copy_eq (Q : QuadraticMap R M N) (Q' : M → N) (h : Q' = ⇑Q) : Q.copy Q' h = Q :=
  DFunLike.ext' h

end DFunLike

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable (Q : QuadraticMap R M N)

theorem map_smul (a : R) (x : M) : Q (a • x) = (a * a) • Q x :=
  Q.toFun_smul a x

theorem exists_companion : ∃ B : BilinMap R M N, ∀ x y, Q (x + y) = Q x + Q y + B x y :=
  Q.exists_companion'

theorem map_add_add_add_map (x y z : M) :
    Q (x + y + z) + (Q x + Q y + Q z) = Q (x + y) + Q (y + z) + Q (z + x) := by
  obtain ⟨B, h⟩ := Q.exists_companion
  rw [add_comm z x]
  simp only [h, LinearMap.map_add₂]
  abel

theorem map_add_self (x : M) : Q (x + x) = 4 • Q x := by
  rw [← two_smul R x, map_smul, ← Nat.cast_smul_eq_nsmul R]
  norm_num

-- not @[simp] because it is superseded by `ZeroHomClass.map_zero`
protected theorem map_zero : Q 0 = 0 := by
  rw [← @zero_smul R _ _ _ _ (0 : M), map_smul, zero_mul, zero_smul]

instance zeroHomClass : ZeroHomClass (QuadraticMap R M N) M N :=
  { QuadraticMap.instFunLike (R := R) (M := M) (N := N) with map_zero := QuadraticMap.map_zero }

theorem map_smul_of_tower [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]
    [Module S N] [IsScalarTower S R N] (a : S)
    (x : M) : Q (a • x) = (a * a) • Q x := by
  rw [← IsScalarTower.algebraMap_smul R a x, map_smul, ← RingHom.map_mul, algebraMap_smul]

end CommSemiring

section CommRing

variable [CommRing R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] (Q : QuadraticMap R M N)

@[simp]
theorem map_neg (x : M) : Q (-x) = Q x := by
  rw [← @neg_one_smul R _ _ _ _ x, map_smul, neg_one_mul, neg_neg, one_smul]

theorem map_sub (x y : M) : Q (x - y) = Q (y - x) := by rw [← neg_sub, map_neg]

@[simp]
theorem polar_zero_left (y : M) : polar Q 0 y = 0 := by
  simp only [polar, zero_add, QuadraticMap.map_zero, sub_zero, sub_self]

@[simp]
theorem polar_add_left (x x' y : M) : polar Q (x + x') y = polar Q x y + polar Q x' y :=
  polar_add_left_iff.mpr <| Q.map_add_add_add_map x x' y

@[simp]
theorem polar_smul_left (a : R) (x y : M) : polar Q (a • x) y = a • polar Q x y := by
  obtain ⟨B, h⟩ := Q.exists_companion
  simp_rw [polar, h, Q.map_smul, LinearMap.map_smul₂, sub_sub, add_sub_cancel_left]

@[simp]
theorem polar_neg_left (x y : M) : polar Q (-x) y = -polar Q x y := by
  rw [← neg_one_smul R x, polar_smul_left, neg_one_smul]

@[simp]
theorem polar_sub_left (x x' y : M) : polar Q (x - x') y = polar Q x y - polar Q x' y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, polar_add_left, polar_neg_left]

@[simp]
theorem polar_zero_right (y : M) : polar Q y 0 = 0 := by
  simp only [add_zero, polar, QuadraticMap.map_zero, sub_self]

@[simp]
theorem polar_add_right (x y y' : M) : polar Q x (y + y') = polar Q x y + polar Q x y' := by
  rw [polar_comm Q x, polar_comm Q x, polar_comm Q x, polar_add_left]

@[simp]
theorem polar_smul_right (a : R) (x y : M) : polar Q x (a • y) = a • polar Q x y := by
  rw [polar_comm Q x, polar_comm Q x, polar_smul_left]

@[simp]
theorem polar_neg_right (x y : M) : polar Q x (-y) = -polar Q x y := by
  rw [← neg_one_smul R y, polar_smul_right, neg_one_smul]

@[simp]
theorem polar_sub_right (x y y' : M) : polar Q x (y - y') = polar Q x y - polar Q x y' := by
  rw [sub_eq_add_neg, sub_eq_add_neg, polar_add_right, polar_neg_right]

@[simp]
theorem polar_self (x : M) : polar Q x x = 2 • Q x := by
  rw [polar, map_add_self, sub_sub, sub_eq_iff_eq_add, ← two_smul ℕ, ← two_smul ℕ, ← mul_smul]
  norm_num

/-- `QuadraticMap.polar` as a bilinear map -/
@[simps!]
def polarBilin : BilinMap R M N :=
  LinearMap.mk₂ R (polar Q) (polar_add_left Q) (polar_smul_left Q) (polar_add_right Q)
  (polar_smul_right Q)

variable [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M] [Module S N]
    [IsScalarTower S R N]

@[simp]
theorem polar_smul_left_of_tower (a : S) (x y : M) : polar Q (a • x) y = a • polar Q x y := by
  rw [← IsScalarTower.algebraMap_smul R a x, polar_smul_left, algebraMap_smul]

@[simp]
theorem polar_smul_right_of_tower (a : S) (x y : M) : polar Q x (a • y) = a • polar Q x y := by
  rw [← IsScalarTower.algebraMap_smul R a y, polar_smul_right, algebraMap_smul]

/-- An alternative constructor to `QuadraticMap.mk`, for rings where `polar` can be used. -/
@[simps]
def ofPolar (toFun : M → N) (toFun_smul : ∀ (a : R) (x : M), toFun (a • x) = (a * a) • toFun x)
    (polar_add_left : ∀ x x' y : M, polar toFun (x + x') y = polar toFun x y + polar toFun x' y)
    (polar_smul_left : ∀ (a : R) (x y : M), polar toFun (a • x) y = a • polar toFun x y) :
    QuadraticMap R M N :=
  { toFun
    toFun_smul
    exists_companion' := ⟨LinearMap.mk₂ R (polar toFun) (polar_add_left) (polar_smul_left)
      (fun x _ _ ↦ by simp_rw [polar_comm _ x, polar_add_left])
      (fun _ _ _ ↦ by rw [polar_comm, polar_smul_left, polar_comm]),
      fun _ _ ↦ by
        simp only [LinearMap.mk₂_apply]
        rw [polar, sub_sub, add_sub_cancel]⟩ }

/-- In a ring the companion bilinear form is unique and equal to `QuadraticMap.polar`. -/
theorem choose_exists_companion : Q.exists_companion.choose = polarBilin Q :=
  LinearMap.ext₂ fun x y => by
    rw [polarBilin_apply_apply, polar, Q.exists_companion.choose_spec, sub_sub,
      add_sub_cancel_left]

protected theorem map_sum {ι} [DecidableEq ι] (Q : QuadraticMap R M N) (s : Finset ι) (f : ι → M) :
    Q (∑ i ∈ s, f i) = ∑ i ∈ s, Q (f i) +
      ∑ ij in s.sym2.filter (¬ ·.IsDiag),
        Sym2.lift ⟨fun i j => polar Q (f i) (f j), fun _ _ => polar_comm _ _ _⟩ ij := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    simp_rw [Finset.sum_cons, QuadraticMap.map_add, ih, add_assoc, Finset.sym2_cons,
      Finset.sum_filter, Finset.sum_disjUnion, Finset.sum_map, Finset.sum_cons,
      Sym2.mkEmbedding_apply, Sym2.isDiag_iff_proj_eq, not_true, if_false, zero_add, Sym2.lift_mk,
      ← polarBilin_apply_apply, _root_.map_sum, polarBilin_apply_apply]
    congr 2
    rw [add_comm]
    congr! with i hi
    rw [if_pos (ne_of_mem_of_not_mem hi ha).symm]

protected theorem map_sum' {ι} (Q : QuadraticMap R M N) (s : Finset ι) (f : ι → M) :
    Q (∑ i ∈ s, f i) =
      ∑ ij in s.sym2,
        Sym2.lift ⟨fun i j => polar Q (f i) (f j), fun _ _ => polar_comm _ _ _⟩ ij
      - ∑ i ∈ s, Q (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    simp_rw [Finset.sum_cons, QuadraticMap.map_add Q, ih, add_assoc, Finset.sym2_cons,
      Finset.sum_disjUnion, Finset.sum_map, Finset.sum_cons, Sym2.mkEmbedding_apply, Sym2.lift_mk,
      ← polarBilin_apply_apply, _root_.map_sum, polarBilin_apply_apply, polar_self]
    abel_nf

end CommRing

section SemiringOperators

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

section SMul

variable [Monoid S] [Monoid T] [DistribMulAction S N] [DistribMulAction T N]
variable [SMulCommClass S R N] [SMulCommClass T R N]

/-- `QuadraticMap R M N` inherits the scalar action from any algebra over `R`.

This provides an `R`-action via `Algebra.id`. -/
instance : SMul S (QuadraticMap R M N) :=
  ⟨fun a Q =>
    { toFun := a • ⇑Q
      toFun_smul := fun b x => by
        rw [Pi.smul_apply, map_smul, Pi.smul_apply, smul_comm]
      exists_companion' :=
        let ⟨B, h⟩ := Q.exists_companion
        letI := SMulCommClass.symm S R N
        ⟨a • B, by simp [h]⟩ }⟩

@[simp]
theorem coeFn_smul (a : S) (Q : QuadraticMap R M N) : ⇑(a • Q) = a • ⇑Q :=
  rfl

@[simp]
theorem smul_apply (a : S) (Q : QuadraticMap R M N) (x : M) : (a • Q) x = a • Q x :=
  rfl

instance [SMulCommClass S T N] : SMulCommClass S T (QuadraticMap R M N) where
  smul_comm _s _t _q := ext fun _ => smul_comm _ _ _

instance [SMul S T] [IsScalarTower S T N] : IsScalarTower S T (QuadraticMap R M N) where
  smul_assoc _s _t _q := ext fun _ => smul_assoc _ _ _

end SMul

instance : Zero (QuadraticMap R M N) :=
  ⟨{  toFun := fun _ => 0
      toFun_smul := fun a _ => by simp only [smul_zero]
      exists_companion' := ⟨0, fun _ _ => by simp only [add_zero, LinearMap.zero_apply]⟩ }⟩

@[simp]
theorem coeFn_zero : ⇑(0 : QuadraticMap R M N) = 0 :=
  rfl

@[simp]
theorem zero_apply (x : M) : (0 : QuadraticMap R M N) x = 0 :=
  rfl

instance : Inhabited (QuadraticMap R M N) :=
  ⟨0⟩

instance : Add (QuadraticMap R M N) :=
  ⟨fun Q Q' =>
    { toFun := Q + Q'
      toFun_smul := fun a x => by simp only [Pi.add_apply, smul_add, map_smul]
      exists_companion' :=
        let ⟨B, h⟩ := Q.exists_companion
        let ⟨B', h'⟩ := Q'.exists_companion
        ⟨B + B', fun x y => by
          simp_rw [Pi.add_apply, h, h', LinearMap.add_apply, add_add_add_comm]⟩ }⟩

@[simp]
theorem coeFn_add (Q Q' : QuadraticMap R M N) : ⇑(Q + Q') = Q + Q' :=
  rfl

@[simp]
theorem add_apply (Q Q' : QuadraticMap R M N) (x : M) : (Q + Q') x = Q x + Q' x :=
  rfl

instance : AddCommMonoid (QuadraticMap R M N) :=
  DFunLike.coe_injective.addCommMonoid _ coeFn_zero coeFn_add fun _ _ => coeFn_smul _ _

/-- `@CoeFn (QuadraticMap R M)` as an `AddMonoidHom`.

This API mirrors `AddMonoidHom.coeFn`. -/
@[simps apply]
def coeFnAddMonoidHom : QuadraticMap R M N →+ M → N where
  toFun := DFunLike.coe
  map_zero' := coeFn_zero
  map_add' := coeFn_add

/-- Evaluation on a particular element of the module `M` is an additive map on quadratic maps. -/
@[simps! apply]
def evalAddMonoidHom (m : M) : QuadraticMap R M N →+ N :=
  (Pi.evalAddMonoidHom _ m).comp coeFnAddMonoidHom

section Sum

@[simp]
theorem coeFn_sum {ι : Type*} (Q : ι → QuadraticMap R M N) (s : Finset ι) :
    ⇑(∑ i ∈ s, Q i) = ∑ i ∈ s, ⇑(Q i) :=
  map_sum coeFnAddMonoidHom Q s

@[simp]
theorem sum_apply {ι : Type*} (Q : ι → QuadraticMap R M N) (s : Finset ι) (x : M) :
    (∑ i ∈ s, Q i) x = ∑ i ∈ s, Q i x :=
  map_sum (evalAddMonoidHom x : _ →+ N) Q s

end Sum

instance [Monoid S] [DistribMulAction S N] [SMulCommClass S R N] :
    DistribMulAction S (QuadraticMap R M N) where
  mul_smul a b Q := ext fun x => by simp only [smul_apply, mul_smul]
  one_smul Q := ext fun x => by simp only [QuadraticMap.smul_apply, one_smul]
  smul_add a Q Q' := by
    ext
    simp only [add_apply, smul_apply, smul_add]
  smul_zero a := by
    ext
    simp only [zero_apply, smul_apply, smul_zero]

instance [Semiring S] [Module S N] [SMulCommClass S R N] :
    Module S (QuadraticMap R M N) where
  zero_smul Q := by
    ext
    simp only [zero_apply, smul_apply, zero_smul]
  add_smul a b Q := by
    ext
    simp only [add_apply, smul_apply, add_smul]

end SemiringOperators

section RingOperators

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

instance : Neg (QuadraticMap R M N) :=
  ⟨fun Q =>
    { toFun := -Q
      toFun_smul := fun a x => by simp only [Pi.neg_apply, map_smul, smul_neg]
      exists_companion' :=
        let ⟨B, h⟩ := Q.exists_companion
        ⟨-B, fun x y => by simp_rw [Pi.neg_apply, h, LinearMap.neg_apply, neg_add]⟩ }⟩

@[simp]
theorem coeFn_neg (Q : QuadraticMap R M N) : ⇑(-Q) = -Q :=
  rfl

@[simp]
theorem neg_apply (Q : QuadraticMap R M N) (x : M) : (-Q) x = -Q x :=
  rfl

instance : Sub (QuadraticMap R M N) :=
  ⟨fun Q Q' => (Q + -Q').copy (Q - Q') (sub_eq_add_neg _ _)⟩

@[simp]
theorem coeFn_sub (Q Q' : QuadraticMap R M N) : ⇑(Q - Q') = Q - Q' :=
  rfl

@[simp]
theorem sub_apply (Q Q' : QuadraticMap R M N) (x : M) : (Q - Q') x = Q x - Q' x :=
  rfl

instance : AddCommGroup (QuadraticMap R M N) :=
  DFunLike.coe_injective.addCommGroup _ coeFn_zero coeFn_add coeFn_neg coeFn_sub
    (fun _ _ => coeFn_smul _ _) fun _ _ => coeFn_smul _ _

end RingOperators

section restrictScalars

variable [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] [Module S M] [Module S N] [Algebra S R]
variable [IsScalarTower S R M] [IsScalarTower S R N]

/-- If `B : M → N → Pₗ` is `R`-`S` bilinear and `R'` and `S'` are compatible scalar multiplications,
then the restriction of scalars is a `R'`-`S'` bilinear map. -/
@[simps!]
def restrictScalars (Q : QuadraticMap R M N) : QuadraticMap S M N where
  toFun x := Q x
  toFun_smul a x := by
    simp [map_smul_of_tower]
  exists_companion' :=
    let ⟨B, h⟩ := Q.exists_companion
    ⟨B.restrictScalars₁₂ (S := R) (R' := S) (S' := S), fun x y => by
      simp only [LinearMap.restrictScalars₁₂_apply_apply, h]⟩

end restrictScalars

section Comp

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

/-- Compose the quadratic map with a linear function on the right. -/
def comp (Q : QuadraticMap R N P) (f : M →ₗ[R] N) : QuadraticMap R M P where
  toFun x := Q (f x)
  toFun_smul a x := by simp only [map_smul, f.map_smul]
  exists_companion' :=
    let ⟨B, h⟩ := Q.exists_companion
    ⟨B.compl₁₂ f f, fun x y => by simp_rw [f.map_add]; exact h (f x) (f y)⟩

@[simp]
theorem comp_apply (Q : QuadraticMap R N P) (f : M →ₗ[R] N) (x : M) : (Q.comp f) x = Q (f x) :=
  rfl

/-- Compose a quadratic map with a linear function on the left. -/
@[simps (config := { simpRhs := true })]
def _root_.LinearMap.compQuadraticMap (f : N →ₗ[R] P) (Q : QuadraticMap R M N) :
    QuadraticMap R M P where
  toFun x := f (Q x)
  toFun_smul b x := by simp only [map_smul, f.map_smul]
  exists_companion' :=
    let ⟨B, h⟩ := Q.exists_companion
    ⟨B.compr₂ f, fun x y => by simp only [h, map_add, LinearMap.compr₂_apply]⟩

/-- Compose a quadratic map with a linear function on the left. -/
@[simps! (config := { simpRhs := true })]
def _root_.LinearMap.compQuadraticMap' [CommSemiring S] [Algebra S R] [Module S N] [Module S M]
    [IsScalarTower S R N] [IsScalarTower S R M] [Module S P]
    (f : N →ₗ[S] P) (Q : QuadraticMap R M N) : QuadraticMap S M P :=
  _root_.LinearMap.compQuadraticMap f Q.restrictScalars

end Comp
section NonUnitalNonAssocSemiring

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [AddCommMonoid M] [Module R M]
variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

/-- The product of linear forms is a quadratic form. -/
def linMulLin (f g : M →ₗ[R] A) : QuadraticMap R M A where
  toFun := f * g
  toFun_smul a x := by
    rw [Pi.mul_apply, Pi.mul_apply, LinearMap.map_smulₛₗ, RingHom.id_apply, LinearMap.map_smulₛₗ,
      RingHom.id_apply, smul_mul_assoc, mul_smul_comm, ← smul_assoc, (smul_eq_mul R)]
  exists_companion' :=
    ⟨(LinearMap.mul R A).compl₁₂ f g + (LinearMap.mul R A).flip.compl₁₂ g f, fun x y => by
      simp only [Pi.mul_apply, map_add, left_distrib, right_distrib, LinearMap.add_apply,
        LinearMap.compl₁₂_apply, LinearMap.mul_apply', LinearMap.flip_apply]
      abel_nf⟩

@[simp]
theorem linMulLin_apply (f g : M →ₗ[R] A) (x) : linMulLin f g x = f x * g x :=
  rfl

@[simp]
theorem add_linMulLin (f g h : M →ₗ[R] A) : linMulLin (f + g) h = linMulLin f h + linMulLin g h :=
  ext fun _ => add_mul _ _ _

@[simp]
theorem linMulLin_add (f g h : M →ₗ[R] A) : linMulLin f (g + h) = linMulLin f g + linMulLin f h :=
  ext fun _ => mul_add _ _ _

variable {N' : Type*} [AddCommMonoid N'] [Module R N']

@[simp]
theorem linMulLin_comp (f g : M →ₗ[R] A) (h : N' →ₗ[R] M) :
    (linMulLin f g).comp h = linMulLin (f.comp h) (g.comp h) :=
  rfl

variable {n : Type*}

/-- `sq` is the quadratic form mapping the vector `x : A` to `x * x` -/
@[simps!]
def sq : QuadraticMap R A A :=
  linMulLin LinearMap.id LinearMap.id

/-- `proj i j` is the quadratic form mapping the vector `x : n → R` to `x i * x j` -/
def proj (i j : n) : QuadraticMap R (n → A) A :=
  linMulLin (@LinearMap.proj _ _ _ (fun _ => A) _ _ i) (@LinearMap.proj _ _ _ (fun _ => A) _ _ j)

@[simp]
theorem proj_apply (i j : n) (x : n → A) : proj (R := R) i j x = x i * x j :=
  rfl

end NonUnitalNonAssocSemiring

end QuadraticMap

/-!
### Associated bilinear maps

Over a commutative ring with an inverse of 2, the theory of quadratic maps is
basically identical to that of symmetric bilinear maps. The map from quadratic
maps to bilinear maps giving this identification is called the `QuadraticMap.associated`
quadratic map.
-/

namespace LinearMap

namespace BilinMap

open QuadraticMap
open LinearMap (BilinMap)

section Semiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable {N' : Type*}  [AddCommMonoid N'] [Module R N']

/-- A bilinear map gives a quadratic map by applying the argument twice. -/
def toQuadraticMap (B : BilinMap R M N) : QuadraticMap R M N where
  toFun x := B x x
  toFun_smul a x := by simp only [_root_.map_smul, LinearMap.smul_apply, smul_smul]
  exists_companion' := ⟨B + LinearMap.flip B, fun x y => by simp [add_add_add_comm, add_comm]⟩

@[simp]
theorem toQuadraticMap_apply (B : BilinMap R M N) (x : M) : B.toQuadraticMap x = B x x :=
  rfl

theorem toQuadraticMap_comp_same (B : BilinMap R M N) (f : N' →ₗ[R] M) :
    BilinMap.toQuadraticMap (B.compl₁₂ f f) = B.toQuadraticMap.comp f := rfl

section

variable (R M)

@[simp]
theorem toQuadraticMap_zero : (0 : BilinMap R M N).toQuadraticMap = 0 :=
  rfl

end

@[simp]
theorem toQuadraticMap_add (B₁ B₂ : BilinMap R M N) :
    (B₁ + B₂).toQuadraticMap = B₁.toQuadraticMap + B₂.toQuadraticMap :=
  rfl

@[simp]
theorem toQuadraticMap_smul [Monoid S] [DistribMulAction S N] [SMulCommClass S R N]
    [SMulCommClass R S N] (a : S)
    (B : BilinMap R M N) : (a • B).toQuadraticMap = a • B.toQuadraticMap :=
  rfl

section

variable (S R M)

/-- `LinearMap.BilinForm.toQuadraticMap` as an additive homomorphism -/
@[simps]
def toQuadraticMapAddMonoidHom : (BilinMap R M N) →+ QuadraticMap R M N where
  toFun := toQuadraticMap
  map_zero' := toQuadraticMap_zero _ _
  map_add' := toQuadraticMap_add

/-- `LinearMap.BilinForm.toQuadraticMap` as a linear map -/
@[simps!]
def toQuadraticMapLinearMap [Semiring S] [Module S N] [SMulCommClass S R N] [SMulCommClass R S N] :
    (BilinMap R M N) →ₗ[S] QuadraticMap R M N where
  toFun := toQuadraticMap
  map_smul' := toQuadraticMap_smul
  map_add' := toQuadraticMap_add

end

@[simp]
theorem toQuadraticMap_list_sum (B : List (BilinMap R M N)) :
    B.sum.toQuadraticMap = (B.map toQuadraticMap).sum :=
  map_list_sum (toQuadraticMapAddMonoidHom R M) B

@[simp]
theorem toQuadraticMap_multiset_sum (B : Multiset (BilinMap R M N)) :
    B.sum.toQuadraticMap = (B.map toQuadraticMap).sum :=
  map_multiset_sum (toQuadraticMapAddMonoidHom R M) B

@[simp]
theorem toQuadraticMap_sum {ι : Type*} (s : Finset ι) (B : ι → (BilinMap R M N)) :
    (∑ i ∈ s, B i).toQuadraticMap = ∑ i ∈ s, (B i).toQuadraticMap :=
  map_sum (toQuadraticMapAddMonoidHom R M) B s

@[simp]
theorem toQuadraticMap_eq_zero {B : BilinMap R M N} :
    B.toQuadraticMap = 0 ↔ B.IsAlt :=
  QuadraticMap.ext_iff

end Semiring

section Ring

variable [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
variable {B : BilinMap R M N}

@[simp]
theorem toQuadraticMap_neg (B : BilinMap R M N) : (-B).toQuadraticMap = -B.toQuadraticMap :=
  rfl

@[simp]
theorem toQuadraticMap_sub (B₁ B₂ : BilinMap R M N) :
    (B₁ - B₂).toQuadraticMap = B₁.toQuadraticMap - B₂.toQuadraticMap :=
  rfl

theorem polar_toQuadraticMap (x y : M) : polar (toQuadraticMap B) x y = B x y + B y x := by
  simp only [polar, toQuadraticMap_apply, map_add, add_apply, add_assoc, add_comm (B y x) _,
    add_sub_cancel_left, sub_eq_add_neg _ (B y y), add_neg_cancel_left]

theorem polarBilin_toQuadraticMap : polarBilin (toQuadraticMap B) = B + flip B :=
  LinearMap.ext₂ polar_toQuadraticMap

@[simp] theorem _root_.QuadraticMap.toQuadraticMap_polarBilin (Q : QuadraticMap R M N) :
    toQuadraticMap (polarBilin Q) = 2 • Q :=
  QuadraticMap.ext fun x => (polar_self _ x).trans <| by simp

theorem _root_.QuadraticMap.polarBilin_injective (h : IsUnit (2 : R)) :
    Function.Injective (polarBilin : QuadraticMap R M N → _) := by
  intro Q₁ Q₂ h₁₂
  apply h.smul_left_cancel.mp
  rw [show (2 : R) = (2 : ℕ) by rfl]
  simp_rw [Nat.cast_smul_eq_nsmul R, ← QuadraticMap.toQuadraticMap_polarBilin]
  exact congrArg toQuadraticMap h₁₂

section

variable {N' : Type*} [AddCommGroup N'] [Module R N']
variable [CommRing S] [Algebra S R] [Module S M] [IsScalarTower S R M]

theorem _root_.QuadraticMap.polarBilin_comp (Q : QuadraticMap R N' N) (f : M →ₗ[R] N') :
    polarBilin (Q.comp f) = LinearMap.compl₁₂ (polarBilin Q) f f :=
  LinearMap.ext₂ <| fun x y => by simp [polar]

end

variable {N' : Type*} [AddCommGroup N']

theorem _root_.LinearMap.compQuadraticMap_polar [CommSemiring S] [Algebra S R] [Module S N]
    [Module S N'] [IsScalarTower S R N] [Module S M] [IsScalarTower S R M] (f : N →ₗ[S] N')
    (Q : QuadraticMap R M N) (x y : M) : polar (f.compQuadraticMap' Q) x y = f (polar Q x y) := by
  simp [polar]

variable [Module R N']

theorem _root_.LinearMap.compQuadraticMap_polarBilin (f : N →ₗ[R] N') (Q : QuadraticMap R M N) :
    (f.compQuadraticMap' Q).polarBilin = Q.polarBilin.compr₂ f := by
  ext
  rw [polarBilin_apply_apply, compr₂_apply, polarBilin_apply_apply,
    LinearMap.compQuadraticMap_polar]

end Ring

end BilinMap

end LinearMap

namespace QuadraticMap

open LinearMap (BilinMap)

section AssociatedHom

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (S) [CommSemiring S] [Algebra S R]
variable [Module S N] [IsScalarTower S R N]
variable [Invertible (2 : R)] {B₁ : BilinMap R M R}

/-- `associatedHom` is the map that sends a quadratic map on a module `M` over `R` to its
associated symmetric bilinear map.  As provided here, this has the structure of an `S`-linear map
where `S` is a commutative subring of `R`.

Over a commutative ring, use `QuadraticMap.associated`, which gives an `R`-linear map.  Over a
general ring with no nontrivial distinguished commutative subring, use `QuadraticMap.associated'`,
which gives an additive homomorphism (or more precisely a `ℤ`-linear map.) -/
def associatedHom : QuadraticMap R M N →ₗ[S] (BilinMap R M N) :=
  -- TODO: this `center` stuff is vertigial from an incorrect non-commutative version, but we leave
  -- it behind to make a future refactor to a *correct* non-commutative version easier in future.
  (⟨⅟2, Set.invOf_mem_center (Set.ofNat_mem_center _ _)⟩ : Submonoid.center R) •
    { toFun := polarBilin
      map_add' := fun _x _y => LinearMap.ext₂ <| polar_add _ _
      map_smul' := fun _c _x => LinearMap.ext₂ <| polar_smul _ _ }

variable (Q : QuadraticMap R M N)

@[simp]
theorem associated_apply (x y : M) : associatedHom S Q x y = ⅟ (2 : R) • (Q (x + y) - Q x - Q y) :=
  rfl

@[simp] theorem two_nsmul_associated : 2 • associatedHom S Q = Q.polarBilin := by
  ext
  dsimp
  rw [← smul_assoc, two_nsmul, invOf_two_add_invOf_two, one_smul, polar]

theorem associated_isSymm (Q : QuadraticMap R M R) : (associatedHom S Q).IsSymm := fun x y => by
  simp only [associated_apply, sub_eq_add_neg, add_assoc, map_mul, RingHom.id_apply, map_add,
    _root_.map_neg, add_comm, add_left_comm]


@[simp]
theorem associated_comp {N' : Type*} [AddCommGroup N'] [Module R N'] (f : N' →ₗ[R] M) :
    associatedHom S (Q.comp f) = (associatedHom S Q).compl₁₂ f f := by
  ext
  simp only [associated_apply, comp_apply, map_add, LinearMap.compl₁₂_apply]

theorem associated_toQuadraticMap (B : BilinMap R M R) (x y : M) :
    associatedHom S B.toQuadraticMap x y = ⅟ (2 : R) • (B x y + B y x) := by
  simp only [associated_apply, LinearMap.BilinMap.toQuadraticMap_apply, map_add,
    LinearMap.add_apply, smul_eq_mul]
  abel_nf

theorem associated_left_inverse (h : B₁.IsSymm) : associatedHom S B₁.toQuadraticMap = B₁ :=
  LinearMap.ext₂ fun x y => by
    rw [associated_toQuadraticMap, ← h.eq x y, RingHom.id_apply, ← two_mul, ← smul_mul_assoc,
      smul_eq_mul, invOf_mul_self, one_mul]

-- Porting note: moved from below to golf the next theorem
theorem associated_eq_self_apply (x : M) : associatedHom S Q x x = Q x := by
  rw [associated_apply, map_add_self, ← three_add_one_eq_four, ← two_add_one_eq_three, add_smul,
    add_smul, one_smul, add_sub_cancel_right, add_sub_cancel_right, two_smul, ← two_smul R,
    ← smul_assoc]
  simp only [smul_eq_mul, invOf_mul_self', one_smul]

theorem toQuadraticMap_associated : (associatedHom S Q).toQuadraticMap = Q :=
  QuadraticMap.ext <| associated_eq_self_apply S Q

-- note: usually `rightInverse` lemmas are named the other way around, but this is consistent
-- with historical naming in this file.
theorem associated_rightInverse :
    Function.RightInverse (associatedHom S) (BilinMap.toQuadraticMap : _ → QuadraticMap R M R) :=
  fun Q => toQuadraticMap_associated S Q

/-- `associated'` is the `ℤ`-linear map that sends a quadratic form on a module `M` over `R` to its
associated symmetric bilinear form. -/
abbrev associated' : QuadraticMap R M R →ₗ[ℤ] BilinMap R M R :=
  associatedHom ℤ

/-- Symmetric bilinear forms can be lifted to quadratic forms -/
instance canLift :
    CanLift (BilinMap R M R) (QuadraticForm R M) (associatedHom ℕ) LinearMap.IsSymm where
  prf B hB := ⟨B.toQuadraticMap, associated_left_inverse _ hB⟩

/-- There exists a non-null vector with respect to any quadratic form `Q` whose associated
bilinear form is non-zero, i.e. there exists `x` such that `Q x ≠ 0`. -/
theorem exists_quadraticForm_ne_zero {Q : QuadraticForm R M}
    -- Porting note: added implicit argument
    (hB₁ : associated' (R := R) Q ≠ 0) :
    ∃ x, Q x ≠ 0 := by
  rw [← not_forall]
  intro h
  apply hB₁
  rw [(QuadraticMap.ext h : Q = 0), LinearMap.map_zero]

end AssociatedHom

section Associated

variable [CommSemiring S] [CommRing R] [AddCommGroup M] [Algebra S R] [Module R M]
variable [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower S R N]
variable [Invertible (2 : R)]

-- Note:  When possible, rather than writing lemmas about `associated`, write a lemma applying to
-- the more general `associatedHom` and place it in the previous section.
/-- `associated` is the linear map that sends a quadratic map over a commutative ring to its
associated symmetric bilinear map. -/
abbrev associated : QuadraticMap R M N →ₗ[R] BilinMap R M N :=
  associatedHom R

variable (S) in
theorem coe_associatedHom :
    ⇑(associatedHom S : QuadraticMap R M N →ₗ[S] BilinMap R M N) = associated :=
  rfl

open LinearMap in
@[simp]
theorem associated_linMulLin (f g : M →ₗ[R] R) :
    associated (R := R) (linMulLin f g) =
      ⅟ (2 : R) • ((mul R R).compl₁₂ f g + (mul R R).compl₁₂ g f) := by
  ext
  simp only [associated_apply, linMulLin_apply, map_add, smul_add, LinearMap.add_apply,
    LinearMap.smul_apply, compl₁₂_apply, mul_apply', smul_eq_mul]
  ring_nf

open LinearMap in
@[simp]
lemma associated_sq : associated (R := R) sq = mul R R :=
  (associated_linMulLin (id) (id)).trans <|
    by simp only [smul_add, invOf_two_smul_add_invOf_two_smul]; rfl

end Associated

section IsOrtho

/-! ### Orthogonality -/

section CommSemiring
variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  {Q : QuadraticMap R M N}

/-- The proposition that two elements of a quadratic map space are orthogonal. -/
def IsOrtho (Q : QuadraticMap R M N) (x y : M) : Prop :=
  Q (x + y) = Q x + Q y

theorem isOrtho_def {Q : QuadraticMap R M N} {x y : M} : Q.IsOrtho x y ↔ Q (x + y) = Q x + Q y :=
  Iff.rfl

theorem IsOrtho.all (x y : M) : IsOrtho (0 : QuadraticMap R M N) x y := (zero_add _).symm

theorem IsOrtho.zero_left (x : M) : IsOrtho Q (0 : M) x := by simp [isOrtho_def]

theorem IsOrtho.zero_right (x : M) : IsOrtho Q x (0 : M) := by simp [isOrtho_def]

theorem ne_zero_of_not_isOrtho_self {Q : QuadraticMap R M N} (x : M) (hx₁ : ¬Q.IsOrtho x x) :
    x ≠ 0 :=
  fun hx₂ => hx₁ (hx₂.symm ▸ .zero_left _)

theorem isOrtho_comm {x y : M} : IsOrtho Q x y ↔ IsOrtho Q y x := by simp_rw [isOrtho_def, add_comm]

alias ⟨IsOrtho.symm, _⟩ := isOrtho_comm

theorem _root_.LinearMap.BilinForm.toQuadraticMap_isOrtho [IsCancelAdd R]
    [NoZeroDivisors R] [CharZero R] {B : BilinMap R M R} {x y : M} (h : B.IsSymm) :
    B.toQuadraticMap.IsOrtho x y ↔ B.IsOrtho x y := by
  letI : AddCancelMonoid R := { ‹IsCancelAdd R›, (inferInstanceAs <| AddCommMonoid R) with }
  simp_rw [isOrtho_def, LinearMap.isOrtho_def, B.toQuadraticMap_apply, map_add,
    LinearMap.add_apply, add_comm _ (B y y), add_add_add_comm _ _ (B y y), add_comm (B y y)]
  rw [add_right_eq_self (a := B x x + B y y), ← h, RingHom.id_apply, add_self_eq_zero]

end CommSemiring

section CommRing
variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {Q : QuadraticMap R M N}

@[simp]
theorem isOrtho_polarBilin {x y : M} : Q.polarBilin.IsOrtho x y ↔ IsOrtho Q x y := by
  simp_rw [isOrtho_def, LinearMap.isOrtho_def, polarBilin_apply_apply, polar, sub_sub, sub_eq_zero]

theorem IsOrtho.polar_eq_zero {x y : M} (h : IsOrtho Q x y) : polar Q x y = 0 :=
  isOrtho_polarBilin.mpr h

@[simp]
theorem associated_isOrtho [Invertible (2 : R)] {x y : M} :
    Q.associated.IsOrtho x y ↔ Q.IsOrtho x y := by
  simp_rw [isOrtho_def, LinearMap.isOrtho_def, associated_apply, invOf_smul_eq_iff,
    smul_zero, sub_sub, sub_eq_zero]

end CommRing

end IsOrtho

section Anisotropic

section Semiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- An anisotropic quadratic map is zero only on zero vectors. -/
def Anisotropic (Q : QuadraticMap R M N) : Prop :=
  ∀ x, Q x = 0 → x = 0

theorem not_anisotropic_iff_exists (Q : QuadraticMap R M N) :
    ¬Anisotropic Q ↔ ∃ x, x ≠ 0 ∧ Q x = 0 := by
  simp only [Anisotropic, not_forall, exists_prop, and_comm]

theorem Anisotropic.eq_zero_iff {Q : QuadraticMap R M N} (h : Anisotropic Q) {x : M} :
    Q x = 0 ↔ x = 0 :=
  ⟨h x, fun h => h.symm ▸ map_zero Q⟩

end Semiring

section Ring

variable [CommRing R] [AddCommGroup M] [Module R M]

/-- The associated bilinear form of an anisotropic quadratic form is nondegenerate. -/
theorem separatingLeft_of_anisotropic [Invertible (2 : R)] (Q : QuadraticMap R M R)
    (hB : Q.Anisotropic) :
    -- Porting note: added implicit argument
    (QuadraticMap.associated' (R := R) Q).SeparatingLeft := fun x hx ↦ hB _ <| by
  rw [← hx x]
  exact (associated_eq_self_apply _ _ x).symm

end Ring

end Anisotropic

section PosDef

variable {R₂ : Type u} [CommSemiring R₂] [AddCommMonoid M] [Module R₂ M]
variable [PartialOrder N] [AddCommMonoid N] [Module R₂ N]
variable {Q₂ : QuadraticMap R₂ M N}

/-- A positive definite quadratic form is positive on nonzero vectors. -/
def PosDef (Q₂ : QuadraticMap R₂ M N) : Prop :=
  ∀ x, x ≠ 0 → 0 < Q₂ x


theorem PosDef.smul {R} [LinearOrderedCommRing R] [Module R M] [Module R N] [PosSMulStrictMono R N]
    {Q : QuadraticMap R M N} (h : PosDef Q) {a : R} (a_pos : 0 < a) : PosDef (a • Q) :=
  fun x hx => smul_pos a_pos (h x hx)

variable {n : Type*}

theorem PosDef.nonneg {Q : QuadraticMap R₂ M N} (hQ : PosDef Q) (x : M) : 0 ≤ Q x :=
  (eq_or_ne x 0).elim (fun h => h.symm ▸ (map_zero Q).symm.le) fun h => (hQ _ h).le

theorem PosDef.anisotropic {Q : QuadraticMap R₂ M N} (hQ : Q.PosDef) : Q.Anisotropic :=
  fun x hQx => by_contradiction fun hx =>
    lt_irrefl (0 : N) <| by
      have := hQ _ hx
      rw [hQx] at this
      exact this

theorem posDef_of_nonneg {Q : QuadraticMap R₂ M N} (h : ∀ x, 0 ≤ Q x) (h0 : Q.Anisotropic) :
    PosDef Q :=
  fun x hx => lt_of_le_of_ne (h x) (Ne.symm fun hQx => hx <| h0 _ hQx)

theorem posDef_iff_nonneg {Q : QuadraticMap R₂ M N} : PosDef Q ↔ (∀ x, 0 ≤ Q x) ∧ Q.Anisotropic :=
  ⟨fun h => ⟨h.nonneg, h.anisotropic⟩, fun ⟨n, a⟩ => posDef_of_nonneg n a⟩

theorem PosDef.add [CovariantClass N N (· + ·) (· < ·)]
    (Q Q' : QuadraticMap R₂ M N) (hQ : PosDef Q) (hQ' : PosDef Q') :
    PosDef (Q + Q') :=
  fun x hx => add_pos (hQ x hx) (hQ' x hx)

theorem linMulLinSelfPosDef {R} [LinearOrderedCommRing R] [Module R M] [LinearOrderedSemiring A]
    [ExistsAddOfLE A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] (f : M →ₗ[R] A)
    (hf : LinearMap.ker f = ⊥) : PosDef (linMulLin (A := A) f f) :=
  fun _x hx => mul_self_pos.2 fun h => hx <| LinearMap.ker_eq_bot'.mp hf _ h

end PosDef

end QuadraticMap

section

/-!
### Quadratic forms and matrices

Connect quadratic forms and matrices, in order to explicitly compute with them.
The convention is twos out, so there might be a factor 2⁻¹ in the entries of the
matrix.
The determinant of the matrix is the discriminant of the quadratic form.
-/

variable {n : Type w} [Fintype n] [DecidableEq n]
variable [CommRing R] [AddCommMonoid M] [Module R M]

/-- `M.toQuadraticMap'` is the map `fun x ↦ row x * M * col x` as a quadratic form. -/
def Matrix.toQuadraticMap' (M : Matrix n n R) : QuadraticMap R (n → R) R :=
  LinearMap.BilinMap.toQuadraticMap (Matrix.toLinearMap₂' R M)

variable [Invertible (2 : R)]

/-- A matrix representation of the quadratic form. -/
def QuadraticMap.toMatrix' (Q : QuadraticMap R (n → R) R) : Matrix n n R :=
  LinearMap.toMatrix₂' R (associated Q)

open QuadraticMap

theorem QuadraticMap.toMatrix'_smul (a : R) (Q : QuadraticMap R (n → R) R) :
    (a • Q).toMatrix' = a • Q.toMatrix' := by
  simp only [toMatrix', LinearEquiv.map_smul, LinearMap.map_smul]

theorem QuadraticMap.isSymm_toMatrix' (Q : QuadraticMap R (n → R) R) : Q.toMatrix'.IsSymm := by
  ext i j
  rw [toMatrix', Matrix.transpose_apply, LinearMap.toMatrix₂'_apply, LinearMap.toMatrix₂'_apply,
    ← associated_isSymm, RingHom.id_apply, associated_apply]

end

namespace QuadraticMap

variable {n : Type w} [Fintype n]
variable [CommRing R] [DecidableEq n] [Invertible (2 : R)]
variable {m : Type w} [DecidableEq m] [Fintype m]

open Matrix

@[simp]
theorem toMatrix'_comp (Q : QuadraticMap R (m → R) R) (f : (n → R) →ₗ[R] m → R) :
    (Q.comp f).toMatrix' = (LinearMap.toMatrix' f)ᵀ * Q.toMatrix' * (LinearMap.toMatrix' f) := by
  ext
  simp only [QuadraticMap.associated_comp, LinearMap.toMatrix₂'_compl₁₂, toMatrix']

section Discriminant

variable {Q : QuadraticMap R (n → R) R}

/-- The discriminant of a quadratic form generalizes the discriminant of a quadratic polynomial. -/
def discr (Q : QuadraticMap R (n → R) R) : R :=
  Q.toMatrix'.det

theorem discr_smul (a : R) : (a • Q).discr = a ^ Fintype.card n * Q.discr := by
  simp only [discr, toMatrix'_smul, Matrix.det_smul]

theorem discr_comp (f : (n → R) →ₗ[R] n → R) :
    (Q.comp f).discr = f.toMatrix'.det * f.toMatrix'.det * Q.discr := by
  simp only [Matrix.det_transpose, mul_left_comm, QuadraticMap.toMatrix'_comp, mul_comm,
    Matrix.det_mul, discr]

end Discriminant

end QuadraticMap

namespace QuadraticMap

end QuadraticMap

namespace LinearMap

namespace BilinForm

open LinearMap (BilinMap)

section Semiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/--
A bilinear form is separating left if the quadratic form it is associated with is anisotropic.
-/
theorem separatingLeft_of_anisotropic {B : BilinForm R M} (hB : B.toQuadraticMap.Anisotropic) :
    B.SeparatingLeft := fun x hx => hB _ (hx x)

end Semiring

variable [CommRing R] [AddCommGroup M] [Module R M]

/-- There exists a non-null vector with respect to any symmetric, nonzero bilinear form `B`
on a module `M` over a ring `R` with invertible `2`, i.e. there exists some
`x : M` such that `B x x ≠ 0`. -/
theorem exists_bilinForm_self_ne_zero [htwo : Invertible (2 : R)] {B : BilinForm R M}
    (hB₁ : B ≠ 0) (hB₂ : B.IsSymm) : ∃ x, ¬B.IsOrtho x x := by
  lift B to QuadraticForm R M using hB₂ with Q
  obtain ⟨x, hx⟩ := QuadraticMap.exists_quadraticForm_ne_zero hB₁
  exact ⟨x, fun h => hx (Q.associated_eq_self_apply ℕ x ▸ h)⟩

open FiniteDimensional

variable {V : Type u} {K : Type v} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

/-- Given a symmetric bilinear form `B` on some vector space `V` over a field `K`
in which `2` is invertible, there exists an orthogonal basis with respect to `B`. -/
theorem exists_orthogonal_basis [hK : Invertible (2 : K)] {B : LinearMap.BilinForm K V}
    (hB₂ : B.IsSymm) : ∃ v : Basis (Fin (finrank K V)) K V, B.IsOrthoᵢ v := by
  induction' hd : finrank K V with d ih generalizing V
  · exact ⟨basisOfFinrankZero hd, fun _ _ _ => map_zero _⟩
  haveI := finrank_pos_iff.1 (hd.symm ▸ Nat.succ_pos d : 0 < finrank K V)
  -- either the bilinear form is trivial or we can pick a non-null `x`
  obtain rfl | hB₁ := eq_or_ne B 0
  · let b := FiniteDimensional.finBasis K V
    rw [hd] at b
    exact ⟨b, fun i j _ => rfl⟩
  obtain ⟨x, hx⟩ := exists_bilinForm_self_ne_zero hB₁ hB₂
  rw [← Submodule.finrank_add_eq_of_isCompl (isCompl_span_singleton_orthogonal hx).symm,
    finrank_span_singleton (ne_zero_of_map hx)] at hd
  let B' :=  B.domRestrict₁₂ (Submodule.orthogonalBilin (K ∙ x) B )
    (Submodule.orthogonalBilin (K ∙ x) B )
  obtain ⟨v', hv₁⟩ := ih (hB₂.domRestrict _ : B'.IsSymm) (Nat.succ.inj hd)
  -- concatenate `x` with the basis obtained by induction
  let b :=
    Basis.mkFinCons x v'
      (by
        rintro c y hy hc
        rw [add_eq_zero_iff_neg_eq] at hc
        rw [← hc, Submodule.neg_mem_iff] at hy
        have := (isCompl_span_singleton_orthogonal hx).disjoint
        rw [Submodule.disjoint_def] at this
        have := this (c • x) (Submodule.smul_mem _ _ <| Submodule.mem_span_singleton_self _) hy
        exact (smul_eq_zero.1 this).resolve_right fun h => hx <| h.symm ▸ map_zero _)
      (by
        intro y
        refine ⟨-B x y / B x x, fun z hz => ?_⟩
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
        rw [IsOrtho, map_smul, smul_apply, map_add, map_smul, smul_eq_mul, smul_eq_mul,
          div_mul_cancel₀ _ hx, add_neg_cancel, mul_zero])
  refine ⟨b, ?_⟩
  rw [Basis.coe_mkFinCons]
  intro j i
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro hij <;>
    simp only [Function.onFun, Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
  · exact (hij rfl).elim
  · rw [IsOrtho, ← hB₂]
    exact (v' j).prop _ (Submodule.mem_span_singleton_self x)
  · exact (v' i).prop _ (Submodule.mem_span_singleton_self x)
  · exact hv₁ (ne_of_apply_ne _ hij)

end BilinForm

end LinearMap

namespace QuadraticMap

open Finset

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable {ι : Type*}

/-- Given a quadratic map `Q` and a basis, `basisRepr` is the basis representation of `Q`. -/
noncomputable def basisRepr [Finite ι] (Q : QuadraticMap R M N) (v : Basis ι R M) :
    QuadraticMap R (ι → R) N :=
  Q.comp v.equivFun.symm

@[simp]
theorem basisRepr_apply [Fintype ι] {v : Basis ι R M} (Q : QuadraticMap R M N) (w : ι → R) :
    Q.basisRepr v w = Q (∑ i : ι, w i • v i) := by
  rw [← v.equivFun_symm_apply]
  rfl

variable [Fintype ι] {v : Basis ι R M}

section

variable (R)

/-- The weighted sum of squares with respect to some weight as a quadratic form.

The weights are applied using `•`; typically this definition is used either with `S = R` or
`[Algebra S R]`, although this is stated more generally. -/
def weightedSumSquares [Monoid S] [DistribMulAction S R] [SMulCommClass S R R] (w : ι → S) :
    QuadraticMap R (ι → R) R :=
  ∑ i : ι, w i • (proj (R := R) (n := ι) i i)

end

@[simp]
theorem weightedSumSquares_apply [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]
    (w : ι → S) (v : ι → R) :
    weightedSumSquares R w v = ∑ i : ι, w i • (v i * v i) :=
  QuadraticMap.sum_apply _ _ _

/-- On an orthogonal basis, the basis representation of `Q` is just a sum of squares. -/
theorem basisRepr_eq_of_iIsOrtho {R M} [CommRing R] [AddCommGroup M] [Module R M]
    [Invertible (2 : R)] (Q : QuadraticMap R M R) (v : Basis ι R M)
    (hv₂ : (associated (R := R) Q).IsOrthoᵢ v) :
    Q.basisRepr v = weightedSumSquares _ fun i => Q (v i) := by
  ext w
  rw [basisRepr_apply, ← @associated_eq_self_apply R, map_sum, weightedSumSquares_apply]
  refine sum_congr rfl fun j hj => ?_
  rw [← @associated_eq_self_apply R, LinearMap.map_sum₂, sum_eq_single_of_mem j hj]
  · rw [LinearMap.map_smul, LinearMap.map_smul₂, smul_eq_mul, associated_apply, smul_eq_mul,
      smul_eq_mul, smul_eq_mul]
    ring_nf
  · intro i _ hij
    rw [LinearMap.map_smul, LinearMap.map_smul₂,
      show associatedHom R Q (v i) (v j) = 0 from hv₂ hij, smul_eq_mul, smul_eq_mul,
      mul_zero, mul_zero]

end QuadraticMap
