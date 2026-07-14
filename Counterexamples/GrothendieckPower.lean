/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
import Mathlib.Algebra.Category.CommHopfAlgCat
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.FunLike.Fintype
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.BigOperators

/-!
# A finite free group scheme of rank four that is not killed by four

Grothendieck asked whether a finite locally free group scheme of order `n` is killed by `n`;
Deligne proved that this holds for commutative group schemes.  This file formalizes a
counterexample in the non-commutative case: an affine group scheme, finite free of rank four
over the base ring `R = ℤ[a, b] / (a³, b³, a²b + 2)`, whose fourth power map is not trivial.

The coordinate Hopf algebra is `A = R[U, V] / (U² - abU + b²V, V² - a²V)`, built as two
nested `QuadraticAlgebra`s; it is finite free of rank four over `R`.  With
`lambda = (1 + aU)(1 + bV)`, the comultiplication is determined by

* `Δ(U) = U ⊗ 1 + lambda ⊗ U`,
* `Δ(V) = V ⊗ lambda + 1 ⊗ V`,

and `lambda` is group-like.  The `n`-th convolution power of the identity — the coordinate
map of the pointwise `n`-th power `x ↦ xⁿ` of the group scheme — sends `U` to
`(1 + lambda + ⋯ + lambdaⁿ⁻¹) · U`.  For `n = 4` this is `2bUV ≠ 0`, while the eighth
convolution power is the convolution unit (the composite of the counit with the unit map of
`A`).  In particular the seventh convolution power supplies an antipode, so `A` is a Hopf
algebra, and the associated group scheme has order four but is not killed by four.

## Main definitions

* `Counterexample.GrothendieckPower.R`: the base ring `ℤ[a, b] / (a³, b³, a²b + 2)`.
* `Counterexample.GrothendieckPower.A`: the coordinate algebra, finite free of rank four
  over `R`.
* `Counterexample.GrothendieckPower.instHopfAlgebra`: the Hopf algebra structure on `A`.
* `Counterexample.GrothendieckPower.powerMap`: the `n`-th convolution power of the identity
  of `A`, i.e. the coordinate map of the pointwise `n`-th power of the group scheme.
* `Counterexample.GrothendieckPower.affineGroupScheme`: the counterexample as a group object
  in the opposite of the category of commutative `R`-algebras, through Mathlib's
  antiequivalence with commutative Hopf algebras.

## Main results

* `Counterexample.GrothendieckPower.finrank_A`: `A` is free of rank four over `R`.
* `Counterexample.GrothendieckPower.powerMap_four_U_ne_zero`: the fourth power map is not
  the convolution unit, since it sends `U` to `2bUV ≠ 0`.
* `Counterexample.GrothendieckPower.powerMap_eight`: the eighth power map is the convolution
  unit.
* `Counterexample.GrothendieckPower.counterexample`: the combined statement: over the
  nontrivial ring `R`, the algebra `A` is finite free of rank four and its fourth power map
  is not the convolution unit.
* `Counterexample.GrothendieckPower.orderOf_universalPoint`: the universal `A`-valued point
  of the group scheme has order exactly eight.
* `Counterexample.GrothendieckPower.not_isCocomm`: `A` is not cocommutative, i.e. the group
  scheme is noncommutative, as forced by Deligne's theorem for commutative group schemes.
* `Counterexample.GrothendieckPower.monPowMap_affineGroupScheme_four_ne`: the group-scheme
  formulation, through Mathlib's antiequivalence between commutative Hopf algebras and
  affine group schemes: the pointwise fourth power map of the corresponding group object in
  `(CommAlgCat R)ᵒᵖ` is not the constant-unit endomorphism.

## Implementation notes

Nontriviality of the base ring (concretely, `2b ≠ 0` in `R`) is certified by an explicit
model: the regular representation of `R` on `M = ℤ/4 × ℤ/4 × (ℤ/2)⁵`, with the actions of
`a` and `b` given by explicit additive endomorphisms and all relations checked by `decide`.

The polynomial identities underlying the comultiplication and the power-map computations are
proved once in an arbitrary commutative ring satisfying the relations of `R`
(`law_relations_generic`, `law_lambda_generic`, `theta_identities_generic`) using
`linear_combination`, and then transported along algebra maps.

The generators are given short names in each successive algebra (`aB`, `bB`, `aA`, `bA`) and
in the tensor square (`aaT`, `bbT`, `u₁`, `v₁`, `u₂`, `v₂`, `l₁`, `l₂`).  These are `abbrev`s,
so that they unfold definitionally; their only purpose is to keep the statements of the
polynomial certificates and of the coproduct construction readable.

The construction of this group scheme as well as its formalization were carried out by the
AI assistants Codex (OpenAI) and Claude (Anthropic).

## References

* [F. Oort, J. Tate, *Group schemes of prime order*][oorttate1970]: Deligne's proof that a
  commutative finite locally free group scheme is killed by its order is reproduced in §1,
  and the question for possibly non-commutative group schemes is raised on p. 5.
* [J. Tate, *Finite flat group schemes*][tate1997]: records the question as open in §3.8.

## Tags

group scheme, Hopf algebra, counterexample
-/

namespace Counterexample.GrothendieckPower

private theorem quadratic_lift_omega {C S : Type*} [CommSemiring C] [Ring S]
    {c l : C} [Algebra C S] (x : S) (hx : x * x = c • 1 + l • x) :
    QuadraticAlgebra.lift (R := C) ⟨x, hx⟩ QuadraticAlgebra.omega = x :=
  congr_arg Subtype.val
    ((QuadraticAlgebra.lift (R := C) (A := S)).symm_apply_apply ⟨x, hx⟩)

/-!
### An explicit faithful model of the base ring

The base ring `R = ℤ[a, b] / (a³, b³, a²b + 2)` is nontrivial, but this is not syntactically
obvious from its presentation.  We certify it by exhibiting an explicit `R`-module: the
regular representation of `R` on `ℤ/4 × ℤ/4 × (ℤ/2)⁵`, with `a` and `b` acting through
explicit commuting additive endomorphisms.  All required relations are closed under `decide`.
-/

/-- Reduction modulo `2`, as an additive map `ℤ/4 → ℤ/2`. -/
def reduce : ZMod 4 →+ ZMod 2 :=
  (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)).toAddMonoidHom

/-- The additive map `ℤ/2 → ℤ/4` sending `1` to `2`. -/
def double : ZMod 2 →+ ZMod 4 :=
  ZMod.lift 2 ⟨2 • Int.castAddHom (ZMod 4), by change (4 : ZMod 4) = 0; decide⟩

@[simp] theorem reduce_double (x : ZMod 2) : reduce (double x) = 0 := by
  fin_cases x <;> decide

@[simp] theorem double_reduce (x : ZMod 4) : double (reduce x) = 2 * x := by
  fin_cases x <;> decide

/-- The additive group `ℤ/4 × ℤ/4 × (ℤ/2)⁵`, carrier of the regular representation of the
base ring `ℤ[a, b] / (a³, b³, a²b + 2)`. -/
abbrev M := ZMod 4 × ZMod 4 × (Fin 5 → ZMod 2)

/-- The additive endomorphism of `M` realizing multiplication by `a` in the regular
representation of the base ring. -/
def aEnd : AddMonoid.End M where
  toFun x :=
    (double (x.2.2 2), double (x.2.2 4),
      ![reduce x.1, x.2.2 0, reduce x.2.1, 0, x.2.2 3])
  map_zero' := by
    apply Prod.ext
    · simp
    · apply Prod.ext
      · simp
      · funext i; fin_cases i <;> simp
  map_add' x y := by
    apply Prod.ext
    · simp
    · apply Prod.ext
      · simp
      · funext i; fin_cases i <;> simp

/-- The additive endomorphism of `M` realizing multiplication by `b` in the regular
representation of the base ring. -/
def bEnd : AddMonoid.End M where
  toFun x :=
    (double (x.2.2 1), x.1,
      ![0, 0, x.2.2 0, reduce x.2.1, x.2.2 2])
  map_zero' := by
    apply Prod.ext
    · simp
    · apply Prod.ext
      · simp
      · funext i; fin_cases i <;> simp
  map_add' x y := by
    apply Prod.ext
    · simp
    · apply Prod.ext
      · simp
      · funext i; fin_cases i <;> simp

theorem aEnd_bEnd_comm : aEnd * bEnd = bEnd * aEnd := by decide +kernel

theorem aEnd_cube : aEnd ^ 3 = 0 := by decide +kernel

theorem bEnd_cube : bEnd ^ 3 = 0 := by decide +kernel

theorem aEnd_sq_mul_bEnd : aEnd ^ 2 * bEnd + 2 = 0 := by decide +kernel

theorem two_mul_bEnd_ne_zero : 2 * bEnd ≠ 0 := by decide +kernel

private theorem generators_commute :
    ∀ x ∈ ({aEnd, bEnd} : Set (AddMonoid.End M)),
      ∀ y ∈ ({aEnd, bEnd} : Set (AddMonoid.End M)), x * y = y * x := by
  intro x hx y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · exact aEnd_bEnd_comm
  · exact aEnd_bEnd_comm.symm
  · rfl

/-- The commutative subring of `AddMonoid.End M` generated by `aEnd` and `bEnd`.  It receives
a ring map from the base ring, certifying that `2 * b ≠ 0` there. -/
def WitnessRing := Subring.closure ({aEnd, bEnd} : Set (AddMonoid.End M))

open scoped IsMulCommutative

noncomputable instance : IsMulCommutative WitnessRing :=
  Subring.isMulCommutative_closure generators_commute

/-- The element `aEnd`, as an element of `WitnessRing`. -/
def aw : WitnessRing := ⟨aEnd, Subring.subset_closure (Set.mem_insert _ _)⟩

/-- The element `bEnd`, as an element of `WitnessRing`. -/
def bw : WitnessRing :=
  ⟨bEnd, Subring.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩

@[simp] theorem aw_cube : aw ^ 3 = 0 :=
  Subtype.ext aEnd_cube

@[simp] theorem bw_cube : bw ^ 3 = 0 :=
  Subtype.ext bEnd_cube

@[simp] theorem witness_relation : aw ^ 2 * bw + 2 = 0 :=
  Subtype.ext aEnd_sq_mul_bEnd

theorem two_bw_ne_zero : (2 : WitnessRing) * bw ≠ 0 := fun h ↦
  two_mul_bEnd_ne_zero (congr_arg Subtype.val h)

instance : Nontrivial WitnessRing := ⟨⟨(2 : WitnessRing) * bw, 0, two_bw_ne_zero⟩⟩

/-!
### The base ring `R = ℤ[a, b] / (a³, b³, a²b + 2)`
-/

noncomputable section

open MvPolynomial

/-- The polynomial ring `ℤ[a, b]`. -/
abbrev P := MvPolynomial (Fin 2) ℤ

/-- The polynomial variable `a`. -/
def ap : P := X 0

/-- The polynomial variable `b`. -/
def bp : P := X 1

/-- The ideal `(a³, b³, a²b + 2)` of `ℤ[a, b]`. -/
def baseIdeal : Ideal P :=
  Ideal.span ({ap ^ 3, bp ^ 3, ap ^ 2 * bp + C 2} : Set P)

/-- The base ring `R = ℤ[a, b] / (a³, b³, a²b + 2)`. -/
abbrev R := P ⧸ baseIdeal

/-- The class of the variable `a` in the base ring `R`. -/
def a : R := Ideal.Quotient.mk baseIdeal ap

/-- The class of the variable `b` in the base ring `R`. -/
def b : R := Ideal.Quotient.mk baseIdeal bp

@[simp] theorem a_cube : a ^ 3 = 0 := by
  rw [show a ^ 3 = Ideal.Quotient.mk baseIdeal (ap ^ 3) by rfl,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)

@[simp] theorem b_cube : b ^ 3 = 0 := by
  rw [show b ^ 3 = Ideal.Quotient.mk baseIdeal (bp ^ 3) by rfl,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)

@[simp] theorem base_relation : a ^ 2 * b + 2 = 0 := by
  rw [show a ^ 2 * b + 2 =
      Ideal.Quotient.mk baseIdeal (ap ^ 2 * bp + C 2) by rfl,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)

/-- Evaluation of integer polynomials at `(aw, bw)` in `WitnessRing`. -/
def evalWitness : P →+* WitnessRing :=
  eval₂Hom (Int.castRingHom WitnessRing) ![aw, bw]

theorem baseIdeal_le_ker_evalWitness : baseIdeal ≤ RingHom.ker evalWitness := by
  apply Ideal.span_le.2
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · apply (RingHom.mem_ker).2
    simpa only [evalWitness, ap, map_pow, eval₂Hom_X', Matrix.cons_val_zero] using aw_cube
  · apply (RingHom.mem_ker).2
    simpa only [evalWitness, bp, map_pow, eval₂Hom_X', Matrix.cons_val_one,
      Matrix.cons_val_zero] using bw_cube
  · apply (RingHom.mem_ker).2
    simpa only [evalWitness, ap, bp, map_add, map_mul, map_pow, map_ofNat,
      eval₂Hom_X', eval₂Hom_C, Matrix.cons_val_zero, Matrix.cons_val_one] using witness_relation

/-- The ring map `R → WitnessRing`, witnessing that relations not in `baseIdeal` do not hold
in `R`. -/
def witnessHom : R →+* WitnessRing :=
  Ideal.Quotient.lift baseIdeal evalWitness baseIdeal_le_ker_evalWitness

@[simp] theorem witnessHom_b : witnessHom b = bw := by
  rw [witnessHom, b, Ideal.Quotient.lift_mk]
  simp only [evalWitness, bp, eval₂Hom_X', Matrix.cons_val_one, Matrix.cons_val_zero]

theorem two_b_ne_zero : (2 : R) * b ≠ 0 := by
  intro h
  apply two_bw_ne_zero
  have := congr_arg witnessHom h
  rw [map_mul, map_ofNat, map_zero] at this
  simpa only [witnessHom_b] using this

instance : Nontrivial R := ⟨⟨(2 : R) * b, 0, two_b_ne_zero⟩⟩

/-!
### The coordinate algebra `A = R[U, V] / (U² - abU + b²V, V² - a²V)`

The algebra `A` is realized as two nested `QuadraticAlgebra`s, so that its finite freeness of
rank four over `R` follows from the corresponding facts for each step of the tower.
-/

open scoped QuadraticAlgebra

/-- The intermediate quadratic algebra `B = R[V] / (V² - a²V)`. -/
abbrev B := QuadraticAlgebra R 0 (a ^ 2)

/-- The generator `V` of `B`, satisfying `V² = a²V`. -/
def V : B := QuadraticAlgebra.omega

@[simp] theorem V_relation : V ^ 2 = algebraMap R B (a ^ 2) * V := by
  unfold V
  rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_mk]
  ext <;> simp [pow_two]

/-- The image of `a` in `B`. -/
abbrev aB : B := algebraMap R B a

/-- The image of `b` in `B`. -/
abbrev bB : B := algebraMap R B b

/-- The coordinate algebra `A = B[U] / (U² - abU + b²V)`, finite free of rank four over the
base ring `R`. -/
abbrev A := QuadraticAlgebra B (-(bB ^ 2) * V) (aB * bB)

private theorem r_smul_mul (r : R) (x y : A) : r • x * y = r • (x * y) := by
  ext <;> simp [V, aB, bB, pow_two]

noncomputable instance : Algebra R A :=
  Algebra.ofModule r_smul_mul fun r x y ↦ by
    rw [mul_comm x (r • y), mul_comm x y]
    exact r_smul_mul r y x

/-- The generator `U` of `A`, satisfying `U² = abU - b²V`. -/
def U : A := QuadraticAlgebra.omega

/-- The image of `V` in `A`. -/
def v : A := algebraMap B A V

@[simp] theorem U_relation :
    U ^ 2 = algebraMap R A (a * b) * U - algebraMap R A (b ^ 2) * v := by
  rw [pow_two]
  unfold U v
  rw [QuadraticAlgebra.omega_mul_omega_eq_mk]
  ext <;> simp [V, aB, bB, pow_two, IsScalarTower.algebraMap_apply R B A]

@[simp] theorem v_relation : v ^ 2 = algebraMap R A (a ^ 2) * v := by
  change (algebraMap B A V) ^ 2 = algebraMap R A (a ^ 2) * algebraMap B A V
  rw [← map_pow, V_relation, map_mul, IsScalarTower.algebraMap_apply R B A]

instance : Nontrivial B :=
  Function.Injective.nontrivial QuadraticAlgebra.algebraMap_injective

instance : Nontrivial A :=
  Function.Injective.nontrivial QuadraticAlgebra.algebraMap_injective

noncomputable instance : Module.Free R A :=
  Module.Free.trans (R := R) (S := B) (M := A)
noncomputable instance : Module.Finite R A :=
  Module.Finite.trans (R := R) (A := B) (M := A)

theorem finrank_B : Module.finrank R B = 2 :=
  QuadraticAlgebra.finrank_eq_two (0 : R) (a ^ 2)

theorem finrank_A_over_B : Module.finrank B A = 2 :=
  QuadraticAlgebra.finrank_eq_two (-(bB ^ 2) * V) (aB * bB)

theorem finrank_A : Module.finrank R A = 4 := by
  calc
    Module.finrank R A = Module.finrank R B * Module.finrank B A :=
      (Module.finrank_mul_finrank R B A).symm
    _ = 4 := by rw [finrank_B, finrank_A_over_B]

/-!
### The comultiplication

The polynomial identities behind the coproduct are proved once, in an arbitrary commutative
ring whose distinguished elements satisfy the relations of `R`, by `linear_combination`
certificates; they are then transported to the tensor square along the two inclusions.
-/

private theorem law_relations_generic {S : Type*} [CommRing S]
    (a b u₁ v₁ u₂ v₂ : S)
    (ha : a ^ 3 = 0) (hb : b ^ 3 = 0) (hab : a ^ 2 * b + 2 = 0)
    (hv₁ : v₁ ^ 2 = a ^ 2 * v₁) (hu₁ : u₁ ^ 2 = a * b * u₁ - b ^ 2 * v₁)
    (hv₂ : v₂ ^ 2 = a ^ 2 * v₂) (hu₂ : u₂ ^ 2 = a * b * u₂ - b ^ 2 * v₂) :
    let l₁ := (1 + a * u₁) * (1 + b * v₁)
    let l₂ := (1 + a * u₂) * (1 + b * v₂)
    let dv := v₁ * l₂ + v₂
    let du := u₁ + l₁ * u₂
    dv ^ 2 = a ^ 2 * dv ∧ du ^ 2 = a * b * du - b ^ 2 * dv := by
  dsimp
  have hab' : a ^ 2 * b = -2 := eq_neg_of_add_eq_zero_left hab
  have h2a : 2 * a = 0 := by
    linear_combination a * hab - b * ha
  have h2a2 : 2 * a ^ 2 = 0 := by
    linear_combination a * h2a
  have h2b2 : 2 * b ^ 2 = 0 := by
    linear_combination b ^ 2 * hab - a ^ 2 * hb
  have h4 : (4 : S) = 0 := by
    linear_combination -(a ^ 2 * b - 2) * hab + a * b ^ 2 * ha
  constructor
  · ring_nf
    simp only [hu₂, hv₁, hv₂, ha, h4]
    ring_nf
    simp only [hv₂, ha, hb, h4]
    linear_combination
      (v₁ * u₂ * v₂) * h2a +
      (a ^ 2 * b * v₁ * u₂) * ha -
      (a ^ 5 * b ^ 4 * v₁ * v₂) * ha -
      (v₁ * v₂) * hab +
      (v₁ * v₂) * h4
  · ring_nf
    simp only [hu₁, hu₂, hv₁, hb, h4]
    ring_nf
    simp only [hv₁, ha, hb, h4]
    linear_combination
      -(u₁ * b ^ 2 * v₂) * h2a +
      (u₁ * b * u₂ * v₁) * hab -
      (u₁ * u₂) * hab +
      (u₁ * u₂) * h4 +
      (u₁ * a * b ^ 2 * u₂) * ha -
      (u₁ * a ^ 2 * b ^ 5 * v₂ * v₁) * ha +
      (u₁ * a ^ 3 * b ^ 4 * u₂ * v₁) * ha +
      (2 * a * b ^ 5 * v₂ * v₁) * ha +
      (a ^ 3 * b ^ 6 * v₂ * v₁) * ha -
      (a ^ 4 * b ^ 5 * u₂ * v₁) * ha

private theorem law_lambda_generic {S : Type*} [CommRing S]
    (a b u₁ v₁ u₂ v₂ : S)
    (ha : a ^ 3 = 0) (hb : b ^ 3 = 0) (hab : a ^ 2 * b + 2 = 0)
    (hv₁ : v₁ ^ 2 = a ^ 2 * v₁)
    (hv₂ : v₂ ^ 2 = a ^ 2 * v₂) (hu₂ : u₂ ^ 2 = a * b * u₂ - b ^ 2 * v₂) :
    let l₁ := (1 + a * u₁) * (1 + b * v₁)
    let l₂ := (1 + a * u₂) * (1 + b * v₂)
    let dv := v₁ * l₂ + v₂
    let du := u₁ + l₁ * u₂
    (1 + a * du) * (1 + b * dv) = l₁ * l₂ := by
  dsimp
  have hab' : a ^ 2 * b = -2 := eq_neg_of_add_eq_zero_left hab
  have h2a : 2 * a = 0 := by
    linear_combination a * hab - b * ha
  have h2a2 : 2 * a ^ 2 = 0 := by
    linear_combination a * h2a
  have h2b2 : 2 * b ^ 2 = 0 := by
    linear_combination b ^ 2 * hab - a ^ 2 * hb
  have h4 : (4 : S) = 0 := by
    linear_combination -(a ^ 2 * b - 2) * hab + a * b ^ 2 * ha
  ring_nf
  simp only [hu₂, hv₁, ha, hb, hab']
  ring_nf
  simp only [hv₂, ha, hb]
  linear_combination
    (b ^ 2 * v₁ * v₂ * u₂) * h2a +
    (u₁ * b * v₁ * u₂) * h2a2 +
    (u₁ * b ^ 2 * v₁ * v₂ * u₂) * h2a2 +
    (v₁ * v₂) * h2b2 +
    (a * u₁ * b ^ 2 * v₁ * u₂) * ha -
    (2 * a * b ^ 4 * v₁ * v₂) * ha

/-- The image of `a` in `A`. -/
abbrev aA : A := algebraMap R A a

/-- The image of `b` in `A`. -/
abbrev bA : A := algebraMap R A b

/-- The group-like unit controlling the semidirect-product law. -/
def lambda : A := (1 + aA * U) * (1 + bA * v)

private theorem mapped_relations {S : Type*} [CommRing S] [Algebra R S]
    (f : A →ₐ[R] S) :
    let aa := f aA
    let bb := f bA
    let uu := f U
    let vv := f v
    aa ^ 3 = 0 ∧ bb ^ 3 = 0 ∧ aa ^ 2 * bb + 2 = 0 ∧
      vv ^ 2 = aa ^ 2 * vv ∧ uu ^ 2 = aa * bb * uu - bb ^ 2 * vv := by
  dsimp
  constructor
  · rw [← map_pow]
    simp [aA, ← map_pow, a_cube]
  constructor
  · rw [← map_pow]
    simp [bA, ← map_pow, b_cube]
  constructor
  · have h : aA ^ 2 * bA + 2 = 0 := by
      unfold aA bA
      calc
        (algebraMap R A a) ^ 2 * algebraMap R A b + 2 =
            algebraMap R A (a ^ 2 * b + 2) := by
              rw [map_add, map_mul, map_pow, map_ofNat]
        _ = algebraMap R A 0 := congr_arg (algebraMap R A) base_relation
        _ = 0 := map_zero _
    simpa only [map_add, map_mul, map_pow, map_ofNat, map_zero] using congr_arg f h
  constructor
  · rw [← map_pow, v_relation, map_mul]
    simp [aA, ← map_pow]
  · have h : U ^ 2 = aA * bA * U - bA ^ 2 * v := by
      simp [aA, bA, map_pow, map_mul]
    simpa only [map_pow, map_sub, map_mul] using congr_arg f h

open scoped TensorProduct

/-- The `R`-module structure on `A` bundled with the algebra structure.  Fixing this instance
from this point on keeps iterated tensor products definitionally aligned with Mathlib's
bialgebra API. -/
local instance canonicalModuleRA : Module R A := Algebra.toModule

/-- The canonical semiring structure on the tensor square `A ⊗[R] A`.  See
`canonicalModuleRA`. -/
local instance canonicalSemiringT : Semiring (A ⊗[R] A) :=
  Algebra.TensorProduct.instSemiring

/-- The canonical algebra structure on the tensor square `A ⊗[R] A`.  See
`canonicalModuleRA`. -/
local instance canonicalAlgebraRT : Algebra R (A ⊗[R] A) :=
  Algebra.TensorProduct.instAlgebra

/-- The inclusion of the left tensor factor `A → A ⊗[R] A`. -/
abbrev left : A →ₐ[R] A ⊗[R] A :=
  Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A) (B := A)

/-- The inclusion of the right tensor factor `A → A ⊗[R] A`. -/
abbrev right : A →ₐ[R] A ⊗[R] A :=
  Algebra.TensorProduct.includeRight (R := R) (A := A) (B := A)

/-- The image of `a` in `A ⊗[R] A`. -/
abbrev aaT : A ⊗[R] A := left aA

/-- The image of `b` in `A ⊗[R] A`. -/
abbrev bbT : A ⊗[R] A := left bA

private theorem right_aA : right aA = aaT := by
  change (1 : A) ⊗ₜ[R] aA = aA ⊗ₜ[R] (1 : A)
  rw [show aA = a • (1 : A) from Algebra.algebraMap_eq_smul_one a]
  exact (TensorProduct.tmul_smul a 1 1).trans (TensorProduct.smul_tmul' a 1 1).symm

private theorem right_bA : right bA = bbT := by
  change (1 : A) ⊗ₜ[R] bA = bA ⊗ₜ[R] (1 : A)
  rw [show bA = b • (1 : A) from Algebra.algebraMap_eq_smul_one b]
  exact (TensorProduct.tmul_smul b 1 1).trans (TensorProduct.smul_tmul' b 1 1).symm

/-- The image of `U` in the left tensor factor. -/
abbrev u₁ : A ⊗[R] A := left U

/-- The image of `v` in the left tensor factor. -/
abbrev v₁ : A ⊗[R] A := left v

/-- The image of `U` in the right tensor factor. -/
abbrev u₂ : A ⊗[R] A := right U

/-- The image of `v` in the right tensor factor. -/
abbrev v₂ : A ⊗[R] A := right v

/-- The image of `lambda` in the left tensor factor. -/
abbrev l₁ : A ⊗[R] A := (1 + aaT * u₁) * (1 + bbT * v₁)

/-- The image of `lambda` in the right tensor factor. -/
abbrev l₂ : A ⊗[R] A := (1 + aaT * u₂) * (1 + bbT * v₂)

/-- The proposed coproduct of `V`. -/
def deltaV : A ⊗[R] A := v₁ * l₂ + v₂

/-- The proposed coproduct of `U`. -/
def deltaU : A ⊗[R] A := u₁ + l₁ * u₂

private theorem delta_relations :
    deltaV ^ 2 = aaT ^ 2 * deltaV ∧
      deltaU ^ 2 = aaT * bbT * deltaU - bbT ^ 2 * deltaV := by
  obtain ⟨ha₁, hb₁, hab₁, hv₁', hu₁'⟩ := mapped_relations (S := A ⊗[R] A) left
  obtain ⟨_, _, _, hv₂', hu₂'⟩ := mapped_relations (S := A ⊗[R] A) right
  simp only [right_aA, right_bA] at hv₂' hu₂'
  exact law_relations_generic _ _ _ _ _ _ ha₁ hb₁ hab₁ hv₁' hu₁' hv₂' hu₂'

private theorem delta_lambda :
    (1 + aaT * deltaU) * (1 + bbT * deltaV) = l₁ * l₂ := by
  obtain ⟨ha₁, hb₁, hab₁, hv₁', -⟩ := mapped_relations (S := A ⊗[R] A) left
  obtain ⟨-, -, -, hv₂', hu₂'⟩ := mapped_relations (S := A ⊗[R] A) right
  simp only [right_aA, right_bA] at hv₂' hu₂'
  exact law_lambda_generic _ _ _ _ _ _ ha₁ hb₁ hab₁ hv₁' hv₂' hu₂'

private theorem aaT_smul : aaT = a • (1 : A ⊗[R] A) := by
  change (aA ⊗ₜ[R] (1 : A)) = a • (1 : A ⊗[R] A)
  rw [show aA = a • (1 : A) from Algebra.algebraMap_eq_smul_one a]
  exact TensorProduct.smul_tmul' a 1 1

private theorem bbT_smul : bbT = b • (1 : A ⊗[R] A) := by
  change (bA ⊗ₜ[R] (1 : A)) = b • (1 : A ⊗[R] A)
  rw [show bA = b • (1 : A) from Algebra.algebraMap_eq_smul_one b]
  exact TensorProduct.smul_tmul' b 1 1

private theorem zero_smul_A (x : A) : (0 : R) • x = 0 := by
  ext <;> simp

private theorem zero_smul_T (x : A ⊗[R] A) : (0 : R) • x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul x y =>
      change ((0 : R) • x) ⊗ₜ[R] y = 0
      rw [zero_smul_A, TensorProduct.zero_tmul]
  | add x y hx hy =>
      rw [TensorProduct.smul_add, hx, hy, add_zero]

/-- First lift of the coproduct, sending `V` to `deltaV`. -/
noncomputable def comulB : B →ₐ[R] A ⊗[R] A :=
  QuadraticAlgebra.lift ⟨deltaV, by
    have hsquare : (a • (1 : A ⊗[R] A)) ^ 2 = (a ^ 2 : R) • (1 : A ⊗[R] A) := by
      calc
        (a • (1 : A ⊗[R] A)) ^ 2 = (a * a) • ((1 : A ⊗[R] A) * (1 : A ⊗[R] A)) :=
          (pow_two _).trans (smul_mul_smul_comm a (1 : A ⊗[R] A) a (1 : A ⊗[R] A))
        _ = (a * a) • (1 : A ⊗[R] A) :=
          congr_arg ((a * a) • ·) (mul_one (1 : A ⊗[R] A))
        _ = (a ^ 2 : R) • (1 : A ⊗[R] A) :=
          congr_arg (fun r : R ↦ r • (1 : A ⊗[R] A)) (pow_two a).symm
    calc
      deltaV * deltaV = aaT ^ 2 * deltaV := by simpa only [pow_two] using delta_relations.1
      _ = (0 : R) • (1 : A ⊗[R] A) + (a ^ 2 : R) • deltaV := by
        calc
          aaT ^ 2 * deltaV = ((a ^ 2 : R) • (1 : A ⊗[R] A)) * deltaV := by rw [aaT_smul, hsquare]
          _ = (a ^ 2 : R) • ((1 : A ⊗[R] A) * deltaV) := smul_mul_assoc _ _ _
          _ = (a ^ 2 : R) • deltaV := congr_arg ((a ^ 2 : R) • ·) (one_mul deltaV)
          _ = (0 : R) • (1 : A ⊗[R] A) + (a ^ 2 : R) • deltaV := by
            rw [zero_smul_T, zero_add]⟩

@[simp] theorem comulB_V : comulB V = deltaV :=
  quadratic_lift_omega deltaV _

theorem comulB_aB : comulB aB = aaT := by
  calc
    comulB aB = algebraMap R (A ⊗[R] A) a := comulB.commutes a
    _ = a • (1 : A ⊗[R] A) := Algebra.algebraMap_eq_smul_one a
    _ = aaT := aaT_smul.symm

theorem comulB_bB : comulB bB = bbT := by
  calc
    comulB bB = algebraMap R (A ⊗[R] A) b := comulB.commutes b
    _ = b • (1 : A ⊗[R] A) := Algebra.algebraMap_eq_smul_one b
    _ = bbT := bbT_smul.symm

private theorem comulB_neg (x : B) : comulB (-x) = -comulB x :=
  map_neg comulB x

private theorem comulB_bB_sq : comulB (bB ^ 2) = comulB bB ^ 2 := by
  calc
    comulB (bB ^ 2) = comulB (bB * bB) := congr_arg comulB (pow_two bB)
    _ = comulB bB * comulB bB := comulB.map_mul bB bB
    _ = comulB bB ^ 2 := (pow_two (comulB bB)).symm

noncomputable instance instAlgebraBT : Algebra B (A ⊗[R] A) :=
  comulB.toRingHom.toAlgebra' fun (c : B) (x : A ⊗[R] A) ↦ mul_comm (comulB c) x

private theorem deltaU_root_mul :
    deltaU * deltaU = comulB (-(bB ^ 2) * V) * 1 +
      comulB (aB * bB) * deltaU := by
  have hc : comulB (-(bB ^ 2) * V) = -(bbT ^ 2) * deltaV := by
    have hn : comulB (-(bB ^ 2)) = -(comulB bB ^ 2) := by
      calc
        comulB (-(bB ^ 2)) = -comulB (bB ^ 2) := comulB_neg _
        _ = -(comulB bB ^ 2) := congr_arg Neg.neg comulB_bB_sq
    calc
      comulB (-(bB ^ 2) * V) = comulB (-(bB ^ 2)) * comulB V := comulB.map_mul _ _
      _ = -(comulB bB ^ 2) * comulB V := by rw [hn]
      _ = -(bbT ^ 2) * deltaV := by rw [comulB_bB, comulB_V]
  have hl : comulB (aB * bB) = aaT * bbT := by
    calc
      comulB (aB * bB) = comulB aB * comulB bB := comulB.map_mul _ _
      _ = aaT * bbT := by rw [comulB_aB, comulB_bB]
  rw [hc, hl]
  calc
    deltaU * deltaU = aaT * bbT * deltaU - bbT ^ 2 * deltaV := by
      simpa only [pow_two] using delta_relations.2
    _ = -(bbT ^ 2) * deltaV * 1 + aaT * bbT * deltaU := by ring

/-- The outer quadratic lift defining the coproduct. -/
noncomputable def comulOuter : A →ₐ[B] A ⊗[R] A :=
  QuadraticAlgebra.lift ⟨deltaU, by
    change deltaU * deltaU = comulB (-(bB ^ 2) * V) * 1 +
      comulB (aB * bB) * deltaU
    exact deltaU_root_mul⟩

/-- The coproduct algebra homomorphism. -/
noncomputable def comul : A →ₐ[R] A ⊗[R] A :=
  { comulOuter.toRingHom with
    commutes' := fun r ↦ by
      change comulOuter (algebraMap R A r) = algebraMap R (A ⊗[R] A) r
      calc
        comulOuter (algebraMap R A r) =
            comulOuter (algebraMap B A (algebraMap R B r)) := by
              rw [IsScalarTower.algebraMap_apply R B A]
        _ = algebraMap B (A ⊗[R] A) (algebraMap R B r) := comulOuter.commutes _
        _ = comulB (algebraMap R B r) := rfl
        _ = algebraMap R (A ⊗[R] A) r := comulB.commutes r }

theorem comul_v : comul v = deltaV := by
  calc
    comul v = comulOuter (algebraMap B A V) := rfl
    _ = algebraMap B (A ⊗[R] A) V := comulOuter.commutes V
    _ = comulB V := rfl
    _ = deltaV := comulB_V

theorem comul_U : comul U = deltaU := by
  apply quadratic_lift_omega

theorem comul_aA : comul aA = aaT := by
  calc
    comul aA = algebraMap R (A ⊗[R] A) a := comul.commutes a
    _ = a • (1 : A ⊗[R] A) := Algebra.algebraMap_eq_smul_one a
    _ = aaT := aaT_smul.symm

theorem comul_bA : comul bA = bbT := by
  calc
    comul bA = algebraMap R (A ⊗[R] A) b := comul.commutes b
    _ = b • (1 : A ⊗[R] A) := Algebra.algebraMap_eq_smul_one b
    _ = bbT := bbT_smul.symm

theorem left_lambda : left lambda = l₁ := by
  have hone : left (1 : A) = 1 := left.map_one
  unfold lambda l₁
  simp only [map_mul, map_add]
  rw [hone]

theorem right_lambda : right lambda = l₂ := by
  have hone : right (1 : A) = 1 := right.map_one
  unfold lambda l₂
  simp only [map_mul, map_add]
  rw [hone, right_aA, right_bA]

@[simp] theorem comul_lambda : comul lambda = left lambda * right lambda := by
  rw [left_lambda, right_lambda]
  have hone : comul (1 : A) = 1 := comul.map_one
  unfold lambda
  simp only [map_mul, map_add]
  rw [hone, comul_aA, comul_bA, comul_U, comul_v]
  exact delta_lambda

@[simp] theorem comul_U_formula :
    comul U = left U + left lambda * right U := by
  rw [comul_U, left_lambda]
  rfl

@[simp] theorem comul_v_formula :
    comul v = left v * right lambda + right v := by
  rw [comul_v, right_lambda]
  rfl

/-- Two `R`-algebra maps out of `A` agree if they agree on `U` and `V`. -/
theorem algHom_ext {S : Type*} [Semiring S] [Algebra R S]
    {f g : A →ₐ[R] S} (hU : f U = g U) (hv : f v = g v) : f = g := by
  apply DFunLike.ext _ _
  intro x
  have h_embed (z : B) :
      algebraMap B A z = algebraMap R A z.re + algebraMap R A z.im * v := by
    have hz : z = algebraMap R B z.re + algebraMap R B z.im * V := by
      calc
        z = ⟨z.re, z.im⟩ := rfl
        _ = algebraMap R B z.re + z.im • V :=
          QuadraticAlgebra.mk_eq_add_smul_omega z.re z.im
        _ = algebraMap R B z.re + algebraMap R B z.im * V := by
          apply QuadraticAlgebra.ext <;> simp [V]
    calc
      algebraMap B A z = algebraMap B A
          (algebraMap R B z.re + algebraMap R B z.im * V) := congr_arg _ hz
      _ = algebraMap R A z.re + algebraMap R A z.im * v := by
        rw [map_add, map_mul, ← IsScalarTower.algebraMap_apply R B A,
          ← IsScalarTower.algebraMap_apply R B A]
        rfl
  have hB (z : B) : f (algebraMap B A z) = g (algebraMap B A z) := by
    rw [h_embed]
    simp only [map_add, map_mul]
    rw [f.commutes, f.commutes, g.commutes, g.commutes, hv]
  have hx : x = algebraMap B A x.re + algebraMap B A x.im * U := by
    apply QuadraticAlgebra.ext <;> simp [U]
  rw [hx, map_add, map_mul, map_add, map_mul, hB x.re, hB x.im, hU]

/-!
### The counit and the bialgebra structure
-/

/-- The inner counit, sending `V` to zero. -/
noncomputable def counitB : B →ₐ[R] R :=
  QuadraticAlgebra.lift ⟨0, by simp⟩

@[simp] theorem counitB_V : counitB V = 0 :=
  quadratic_lift_omega 0 _

noncomputable instance instAlgebraBR : Algebra B R :=
  counitB.toRingHom.toAlgebra' fun (c : B) (r : R) ↦ mul_comm (counitB c) r

/-- The outer counit, sending `U` to zero. -/
noncomputable def counitOuter : A →ₐ[B] R :=
  QuadraticAlgebra.lift ⟨0, by
    change (0 : R) * 0 = counitB (-(bB ^ 2) * V) * 1 +
      counitB (aB * bB) * 0
    simp⟩

/-- The counit algebra homomorphism. -/
noncomputable def counit : A →ₐ[R] R :=
  { counitOuter.toRingHom with
    commutes' := fun r ↦ by
      change counitOuter (algebraMap R A r) = r
      calc
        counitOuter (algebraMap R A r) =
            counitOuter (algebraMap B A (algebraMap R B r)) := by
              rw [IsScalarTower.algebraMap_apply R B A]
        _ = algebraMap B R (algebraMap R B r) := counitOuter.commutes _
        _ = counitB (algebraMap R B r) := rfl
        _ = r := counitB.commutes r }

@[simp] theorem counit_v : counit v = 0 := by
  calc
    counit v = counitOuter (algebraMap B A V) := rfl
    _ = algebraMap B R V := counitOuter.commutes V
    _ = counitB V := rfl
    _ = 0 := counitB_V

@[simp] theorem counit_U : counit U = 0 := by
  apply quadratic_lift_omega

@[simp] theorem counit_lambda : counit lambda = 1 := by
  simp [lambda]

private theorem comul_coassoc :
    (Algebra.TensorProduct.assoc R R R A A A).toAlgHom.comp
        ((Algebra.TensorProduct.map comul (.id R A)).comp comul) =
      (Algebra.TensorProduct.map (.id R A) comul).comp comul := by
  apply algHom_ext (S := TensorProduct R A (TensorProduct R A A))
  · simp [comul_U_formula, comul_lambda, Algebra.TensorProduct.one_def,
      TensorProduct.add_tmul, TensorProduct.tmul_add, add_assoc]
  · simp [comul_v_formula, comul_lambda, Algebra.TensorProduct.one_def,
      TensorProduct.add_tmul, TensorProduct.tmul_add, add_assoc]

private theorem counit_left :
    (Algebra.TensorProduct.map counit (.id R A)).comp comul =
      (Algebra.TensorProduct.lid R A).symm := by
  apply algHom_ext (S := TensorProduct R R A)
  · simp [counit_lambda]
  · simp

private theorem counit_right :
    (Algebra.TensorProduct.map (.id R A) counit).comp comul =
      (Algebra.TensorProduct.rid R R A).symm := by
  apply algHom_ext (S := TensorProduct R A R)
  · simp
  · simp [counit_lambda]

/-- The bialgebra structure underlying the counterexample. -/
noncomputable instance instBialgebra : Bialgebra R A :=
  Bialgebra.ofAlgHom comul counit comul_coassoc counit_left counit_right

private theorem bialgebra_comulAlgHom : Bialgebra.comulAlgHom R A = comul := rfl
private theorem bialgebra_counitAlgHom : Bialgebra.counitAlgHom R A = counit := rfl

/-- The coordinate `lambda` is a group-like element of `A`. -/
theorem isGroupLikeElem_lambda : IsGroupLikeElem R lambda where
  counit_eq_one := by
    rw [← Bialgebra.counitAlgHom_apply (R := R), bialgebra_counitAlgHom]
    exact counit_lambda
  comul_eq_tmul_self := by
    rw [← Bialgebra.comulAlgHom_apply (R := R), bialgebra_comulAlgHom, comul_lambda]
    simp

/-!
### The convolution power maps

The `n`-th power map of the group scheme (pointwise `x ↦ xⁿ`) corresponds, on coordinate
rings, to the `n`-th convolution power of the identity of `A`.  On the skew-primitive
coordinates it is controlled by the geometric sum
`1 + lambda + ⋯ + lambdaⁿ⁻¹`, which we compute from the square-zero element
`theta = lambda - 1`.
-/

/-- The square-zero part of the group-like coordinate. -/
def theta : A := lambda - 1

private theorem theta_identities_generic {S : Type*} [CommRing S]
    (aa bb uu vv : S)
    (ha : aa ^ 3 = 0) (hb : bb ^ 3 = 0) (hab : aa ^ 2 * bb + 2 = 0)
    (hv : vv ^ 2 = aa ^ 2 * vv)
    (hu : uu ^ 2 = aa * bb * uu - bb ^ 2 * vv) :
    let th := (1 + aa * uu) * (1 + bb * vv) - 1
    th ^ 2 = 0 ∧ 2 * th = 2 * bb * vv := by
  dsimp
  have hab' : aa ^ 2 * bb = -2 := eq_neg_of_add_eq_zero_left hab
  have h2a : 2 * aa = 0 := by
    linear_combination aa * hab - bb * ha
  have h2a2 : 2 * aa ^ 2 = 0 := by
    linear_combination aa * h2a
  have h2b2 : 2 * bb ^ 2 = 0 := by
    linear_combination bb ^ 2 * hab - aa ^ 2 * hb
  have h4 : (4 : S) = 0 := by
    linear_combination -(aa ^ 2 * bb - 2) * hab + aa * bb ^ 2 * ha
  constructor
  · ring_nf
    simp only [hu, hv]
    ring_nf
    linear_combination
      (uu * bb * vv) * h2a -
      (2 * aa ^ 2 * vv ^ 2) * hb +
      (uu * bb) * ha +
      (4 * uu * bb ^ 2 * vv) * ha -
      (aa * bb ^ 4 * vv ^ 2) * ha +
      (aa ^ 2 * uu * bb ^ 3 * vv) * ha
  · ring_nf
    linear_combination uu * (1 + bb * vv) * h2a

theorem theta_sq : theta ^ 2 = 0 := by
  obtain ⟨ha, hb, hab, hv, hu⟩ := mapped_relations (AlgHom.id R A)
  exact (theta_identities_generic _ _ _ _ ha hb hab hv hu).1

theorem two_theta : 2 * theta = 2 * bA * v := by
  obtain ⟨ha, hb, hab, hv, hu⟩ := mapped_relations (AlgHom.id R A)
  exact (theta_identities_generic _ _ _ _ ha hb hab hv hu).2

open WithConv

/-- The universal point, in the convolution monoid of `R`-algebra endomorphisms. -/
noncomputable def universalPoint : WithConv (A →ₐ[R] A) :=
  toConv (AlgHom.id R A)

/-- The `n`-th convolution power of the identity of `A`: the coordinate-ring map of the
pointwise `n`-th power map of the group scheme. -/
noncomputable def powerMap (n : ℕ) : A →ₐ[R] A :=
  (universalPoint ^ n).ofConv

@[simp] theorem powerMap_zero_apply (x : A) : powerMap 0 x = algebraMap R A (counit x) := by
  rfl

@[simp] theorem powerMap_one_apply (x : A) : powerMap 1 x = x := by
  calc
    powerMap 1 x = universalPoint.ofConv x :=
      congr_arg (fun f : WithConv (A →ₐ[R] A) ↦ f.ofConv x) (pow_one universalPoint)
    _ = x := rfl

theorem powerMap_succ_U (n : ℕ) :
    powerMap (n + 1) U = powerMap n U + powerMap n lambda * U := by
  calc
    powerMap (n + 1) U = (universalPoint ^ n * universalPoint).ofConv U :=
      congr_arg (fun f : WithConv (A →ₐ[R] A) ↦ f.ofConv U)
        (pow_succ universalPoint n)
    _ = powerMap n U + powerMap n lambda * U := by
      rw [AlgHom.convMul_apply]
      rw [← Bialgebra.comulAlgHom_apply, bialgebra_comulAlgHom, comul_U_formula]
      simp [universalPoint, powerMap]

theorem powerMap_succ_v (n : ℕ) :
    powerMap (n + 1) v = powerMap n v * lambda + v := by
  calc
    powerMap (n + 1) v = (universalPoint ^ n * universalPoint).ofConv v :=
      congr_arg (fun f : WithConv (A →ₐ[R] A) ↦ f.ofConv v)
        (pow_succ universalPoint n)
    _ = powerMap n v * lambda + v := by
      rw [AlgHom.convMul_apply]
      rw [← Bialgebra.comulAlgHom_apply, bialgebra_comulAlgHom, comul_v_formula]
      simp [universalPoint, powerMap]

theorem powerMap_succ_lambda (n : ℕ) :
    powerMap (n + 1) lambda = powerMap n lambda * lambda := by
  calc
    powerMap (n + 1) lambda = (universalPoint ^ n * universalPoint).ofConv lambda :=
      congr_arg (fun f : WithConv (A →ₐ[R] A) ↦ f.ofConv lambda)
        (pow_succ universalPoint n)
    _ = powerMap n lambda * lambda := by
      rw [AlgHom.convMul_apply]
      rw [← Bialgebra.comulAlgHom_apply, bialgebra_comulAlgHom, comul_lambda]
      simp [universalPoint, powerMap]

theorem four_eq_zero : (4 : A) = 0 := by
  obtain ⟨ha, _, hab, _, _⟩ := mapped_relations (AlgHom.id R A)
  change aA ^ 3 = 0 at ha
  change aA ^ 2 * bA + 2 = 0 at hab
  linear_combination -(aA ^ 2 * bA - 2) * hab + aA * bA ^ 2 * ha

theorem lambda_eq_one_add_theta : lambda = 1 + theta := by
  unfold theta
  ring

theorem lambda_pow_four : lambda ^ 4 = 1 := by
  rw [lambda_eq_one_add_theta]
  ring_nf
  have ht3 : theta ^ 3 = 0 := by
    calc
      theta ^ 3 = theta ^ 2 * theta := by ring
      _ = 0 := by rw [theta_sq, zero_mul]
  have ht4 : theta ^ 4 = 0 := by
    calc
      theta ^ 4 = (theta ^ 2) ^ 2 := by ring
      _ = 0 := by rw [theta_sq, zero_pow]; norm_num
  linear_combination theta * four_eq_zero + 6 * theta_sq + 4 * ht3 + ht4

/-- The geometric sum controlling powers in both skew-primitive coordinates. -/
def geomSum (n : ℕ) : A := ∑ i ∈ Finset.range n, lambda ^ i

@[simp] theorem geomSum_zero : geomSum 0 = 0 := by
  simp [geomSum]

theorem geomSum_succ (n : ℕ) : geomSum (n + 1) = geomSum n + lambda ^ n := by
  simpa [geomSum] using Finset.sum_range_succ (fun i ↦ lambda ^ i) n

theorem geomSum_mul_lambda_add_one (n : ℕ) :
    geomSum n * lambda + 1 = geomSum (n + 1) := by
  induction n with
  | zero => norm_num [geomSum, Finset.sum_range_succ]
  | succ n ih =>
      calc
        geomSum (n + 1) * lambda + 1 =
            (geomSum n + lambda ^ n) * lambda + 1 :=
          congr_arg (fun x : A ↦ x * lambda + 1) (geomSum_succ n)
        _ = (geomSum n * lambda + 1) + lambda ^ n * lambda := by ring
        _ = geomSum (n + 1) + lambda ^ n * lambda :=
          congr_arg (fun x : A ↦ x + lambda ^ n * lambda) ih
        _ = geomSum (n + 1) + lambda ^ (n + 1) :=
          congr_arg (fun x : A ↦ geomSum (n + 1) + x) (pow_succ lambda n).symm
        _ = geomSum (n + 1 + 1) := (geomSum_succ (n + 1)).symm

theorem powerMap_lambda (n : ℕ) : powerMap n lambda = lambda ^ n := by
  induction n with
  | zero => simp [powerMap_zero_apply, counit_lambda]
  | succ n ih =>
      calc
        powerMap (n + 1) lambda = powerMap n lambda * lambda := powerMap_succ_lambda n
        _ = lambda ^ n * lambda := congr_arg (fun x : A ↦ x * lambda) ih
        _ = lambda ^ (n + 1) := (pow_succ lambda n).symm

theorem powerMap_U (n : ℕ) : powerMap n U = geomSum n * U := by
  induction n with
  | zero => simp [powerMap_zero_apply, counit_U]
  | succ n ih =>
      calc
        powerMap (n + 1) U = powerMap n U + powerMap n lambda * U := powerMap_succ_U n
        _ = geomSum n * U + lambda ^ n * U := by rw [ih, powerMap_lambda]
        _ = geomSum (n + 1) * U := by rw [geomSum_succ, add_mul]

theorem powerMap_v (n : ℕ) : powerMap n v = v * geomSum n := by
  induction n with
  | zero => simp [powerMap_zero_apply, counit_v]
  | succ n ih =>
      calc
        powerMap (n + 1) v = powerMap n v * lambda + v := powerMap_succ_v n
        _ = v * geomSum n * lambda + v := by rw [ih]
        _ = v * (geomSum n * lambda + 1) := by ring
        _ = v * geomSum (n + 1) := by rw [geomSum_mul_lambda_add_one]

theorem geomSum_four : geomSum 4 = 2 * bA * v := by
  norm_num [geomSum, Finset.sum_range_succ]
  rw [lambda_eq_one_add_theta]
  ring_nf
  have ht3 : theta ^ 3 = 0 := by
    calc
      theta ^ 3 = theta ^ 2 * theta := by ring
      _ = 0 := by rw [theta_sq, zero_mul]
  rw [theta_sq, ht3, four_eq_zero]
  ring_nf
  linear_combination two_theta + theta * four_eq_zero

theorem powerMap_four_U : powerMap 4 U = 2 * bA * U * v := by
  rw [powerMap_U, geomSum_four]
  ring

theorem two_b_U_v_ne_zero : 2 * bA * U * v ≠ 0 := by
  intro h
  have hOuter := congr_arg (fun x : A ↦ x.im) h
  have hInner := congr_arg (fun x : B ↦ x.im) hOuter
  apply two_b_ne_zero
  simpa [bA, U, v, V, IsScalarTower.algebraMap_apply R B A] using hInner

theorem powerMap_four_U_ne_zero : powerMap 4 U ≠ 0 := by
  rw [powerMap_four_U]
  exact two_b_U_v_ne_zero

theorem powerMap_four_v : powerMap 4 v = 0 := by
  rw [powerMap_v, geomSum_four]
  have hv : v ^ 2 = aA ^ 2 * v := by
    simp [aA, map_pow]
  have hab : aA ^ 2 * bA + 2 = 0 := by
    obtain ⟨_, _, hab, _, _⟩ := mapped_relations (AlgHom.id R A)
    exact hab
  rw [show v * (2 * bA * v) = 2 * bA * v ^ 2 by ring, hv]
  linear_combination 2 * v * hab - v * four_eq_zero

theorem geomSum_eight : geomSum 8 = 0 := by
  norm_num [geomSum, Finset.sum_range_succ]
  rw [lambda_eq_one_add_theta]
  ring_nf
  have ht3 : theta ^ 3 = 0 := by
    calc theta ^ 3 = theta ^ 2 * theta := by ring
         _ = 0 := by rw [theta_sq, zero_mul]
  have ht4 : theta ^ 4 = 0 := by
    calc theta ^ 4 = theta ^ 2 * theta ^ 2 := by ring
         _ = 0 := by rw [theta_sq, zero_mul]
  have ht5 : theta ^ 5 = 0 := by
    calc theta ^ 5 = theta ^ 4 * theta := by ring
         _ = 0 := by rw [ht4, zero_mul]
  have ht6 : theta ^ 6 = 0 := by
    calc theta ^ 6 = theta ^ 4 * theta ^ 2 := by ring
         _ = 0 := by rw [ht4, zero_mul]
  have ht7 : theta ^ 7 = 0 := by
    calc theta ^ 7 = theta ^ 6 * theta := by ring
         _ = 0 := by rw [ht6, zero_mul]
  rw [theta_sq, ht3, ht4, ht5, ht6, ht7]
  ring_nf
  linear_combination 2 * four_eq_zero + 7 * theta * four_eq_zero

theorem powerMap_eight_U : powerMap 8 U = 0 := by
  rw [powerMap_U, geomSum_eight, zero_mul]

theorem powerMap_eight_v : powerMap 8 v = 0 := by
  rw [powerMap_v, geomSum_eight, mul_zero]

theorem powerMap_eight : powerMap 8 = (Algebra.ofId R A).comp counit := by
  apply algHom_ext
  · simp [powerMap_eight_U]
  · simp [powerMap_eight_v]

theorem universalPoint_pow_eight : universalPoint ^ 8 = 1 := by
  apply WithConv.ext
  change powerMap 8 = (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A)
  rw [bialgebra_counitAlgHom]
  exact powerMap_eight

theorem universalPoint_pow_four_ne_one : universalPoint ^ 4 ≠ 1 := by
  intro h
  have h' : powerMap 4 = powerMap 0 := congr_arg WithConv.ofConv h
  exact powerMap_four_U_ne_zero (by simpa using DFunLike.congr_fun h' U)

/-- In the group of `A`-valued points of the group scheme, the universal point has order
exactly eight: an element of order eight on a group scheme of order four. -/
theorem orderOf_universalPoint : orderOf universalPoint = 8 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 2) universalPoint_pow_four_ne_one
    universalPoint_pow_eight
  norm_num at h
  exact h

/-!
### The Hopf algebra structure and the main statement

Since the eighth convolution power of the identity is the convolution unit, the seventh
convolution power is a two-sided convolution inverse of the identity, that is, an antipode.
-/

private theorem powerMap_seven_mul_universalPoint :
    toConv (powerMap 7) * universalPoint = 1 := by
  calc
    toConv (powerMap 7) * universalPoint = universalPoint ^ 7 * universalPoint := by
      simp [powerMap]
    _ = universalPoint ^ 8 := (pow_succ universalPoint 7).symm
    _ = 1 := universalPoint_pow_eight

private theorem universalPoint_mul_powerMap_seven :
    universalPoint * toConv (powerMap 7) = 1 := by
  calc
    universalPoint * toConv (powerMap 7) = universalPoint * universalPoint ^ 7 := by
      simp [powerMap]
    _ = universalPoint ^ 8 := (pow_succ' universalPoint 7).symm
    _ = 1 := universalPoint_pow_eight

private theorem antipode_right_identity :
    ((Algebra.TensorProduct.lift (powerMap 7) (.id R A) fun _ ↦ Commute.all _).comp
      (Bialgebra.comulAlgHom R A)) =
        (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A) := by
  have h := congr_arg WithConv.ofConv powerMap_seven_mul_universalPoint
  change
    (Algebra.TensorProduct.lmul' R).comp
        ((Algebra.TensorProduct.map (powerMap 7) (.id R A)).comp
          (Bialgebra.comulAlgHom R A)) =
      (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A) at h
  rw [← AlgHom.comp_assoc, Algebra.TensorProduct.lmul'_comp_map] at h
  exact h

private theorem antipode_left_identity :
    ((Algebra.TensorProduct.lift (.id R A) (powerMap 7) fun _ _ ↦ Commute.all _ _).comp
      (Bialgebra.comulAlgHom R A)) =
        (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A) := by
  have h := congr_arg WithConv.ofConv universalPoint_mul_powerMap_seven
  change
    (Algebra.TensorProduct.lmul' R).comp
        ((Algebra.TensorProduct.map (.id R A) (powerMap 7)).comp
          (Bialgebra.comulAlgHom R A)) =
      (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A) at h
  rw [← AlgHom.comp_assoc, Algebra.TensorProduct.lmul'_comp_map] at h
  exact h

/-- The Hopf algebra structure; its antipode is the seventh convolution power of the
identity. -/
noncomputable instance instHopfAlgebra : HopfAlgebra R A :=
  HopfAlgebra.ofAlgHom (powerMap 7) antipode_right_identity antipode_left_identity

/-- The bundled commutative Hopf algebra representing the affine group scheme. -/
noncomputable def coordinateHopfAlgebra : CommHopfAlgCat R :=
  CommHopfAlgCat.of R A

/-- The formal counterexample: over the nontrivial base ring `R`, the commutative Hopf
algebra `A` is finite free of rank four, and its fourth power map is not the convolution
unit.

The freeness and finiteness conjuncts guarantee that the `Module.finrank` conjunct expresses
the honest rank of `A` over `R`. -/
theorem counterexample :
    Nontrivial R ∧ Module.Free R A ∧ Module.Finite R A ∧ Module.finrank R A = 4 ∧
      powerMap 4 ≠ (Algebra.ofId R A).comp counit := by
  refine ⟨inferInstance, inferInstance, inferInstance, finrank_A, ?_⟩
  intro h
  apply powerMap_four_U_ne_zero
  have hU := DFunLike.congr_fun h U
  simpa using hU

/-!
### Non-cocommutativity

By Deligne's theorem, a commutative finite locally free group scheme is killed by its order,
so the group scheme represented by `A` is necessarily noncommutative; equivalently, `A` is
not cocommutative.  We verify this directly: the coefficient functional of `U` distinguishes
`Δ(U)` from its swap.
-/

/-- The `R`-linear coefficient functional of `U` in the basis `1, v, U, U * v` of `A`. -/
private def coeffU : A →ₗ[R] R where
  toFun x := x.im.re
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The `R`-linear coefficient functional of `v` in the basis `1, v, U, U * v` of `A`. -/
private def coeffV : A →ₗ[R] R where
  toFun x := x.re.im
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The Hopf algebra `A` is not cocommutative; equivalently, the affine group scheme it
represents is noncommutative.  This is forced by Deligne's theorem, which affirms
Grothendieck's question for commutative group schemes. -/
theorem not_isCocomm : ¬Coalgebra.IsCocomm R A := by
  intro h
  have hU := DFunLike.congr_fun h.comm_comp_comul U
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    ← Bialgebra.comulAlgHom_apply (R := R), bialgebra_comulAlgHom] at hU
  rw [comul_U_formula] at hU
  simp only [map_add, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    mul_one, TensorProduct.comm_tmul] at hU
  have h2 := congr_arg (fun z ↦ TensorProduct.lid R R (TensorProduct.map coeffU coeffV z)) hU
  have hV1 : coeffV 1 = 0 := rfl
  have hVU : coeffV U = 0 := rfl
  have hU1 : coeffU 1 = 0 := rfl
  have hUU : coeffU U = 1 := rfl
  have hVlam : coeffV lambda = b := by
    change lambda.re.im = b
    simp [lambda, aA, bA, U, v, V, IsScalarTower.algebraMap_apply R B A]
  simp only [map_add, TensorProduct.map_tmul, TensorProduct.lid_tmul, hV1, hVU, hVlam, hU1,
    hUU, smul_eq_mul, one_mul, mul_zero, add_zero, zero_add] at h2
  exact two_b_ne_zero (by rw [h2, mul_zero])

/-!
### The group-scheme formulation

Mathlib's antiequivalence `commHopfAlgCatEquivCogrpCommAlgCat` identifies commutative Hopf
algebras over `R` with group objects in `(CommAlgCat R)ᵒᵖ`, the opposite of the category of
commutative `R`-algebras.  This opposite category is the category of affine schemes over `R`
(via the `Spec` antiequivalence), so these group objects are exactly the affine group schemes
over `R`; here the group object is `op A`, the algebraic incarnation of `Spec A`.  We work
entirely on the algebra side and do not use `AlgebraicGeometry.Spec`, as Mathlib does not yet
connect commutative Hopf algebras to group objects in `AlgebraicGeometry.Scheme`.  This
section transports the counterexample across that equivalence: the pointwise fourth power map
of the resulting group object is not the constant-unit endomorphism.
-/

open CategoryTheory CartesianMonoidalCategory MonObj Opposite

/-- The pointwise `n`-th power map of a monoid object in a cartesian monoidal category.  For
a group scheme, this is the morphism `x ↦ xⁿ`, which is not in general a homomorphism. -/
def monPowMap {C : Type*} [Category C] [CartesianMonoidalCategory C] (M : C) [MonObj M] :
    ℕ → (M ⟶ M)
  | 0 => toUnit M ≫ η[M]
  | n + 1 => lift (monPowMap M n) (𝟙 M) ≫ μ[M]

/-- On the group object `op A` in `(CommAlgCat R)ᵒᵖ` — the affine group scheme corresponding
to `A` — the pointwise `n`-th power map corresponds to the `n`-th convolution power of the
identity of `A`. -/
theorem monPowMap_op_unop_hom (n : ℕ) :
    (monPowMap (op (CommAlgCat.of R A)) n).unop.hom = powerMap n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h : (monPowMap (op (CommAlgCat.of R A)) (n + 1)).unop.hom =
          (Algebra.TensorProduct.lift (powerMap n) (AlgHom.id R A)
              fun _ _ ↦ Commute.all _ _).comp
            (Bialgebra.comulAlgHom R A) := by
        simp only [monPowMap, unop_comp, CommAlgCat.hom_comp, CommAlgCat.mul_op_of_unop_hom,
          CommAlgCat.lift_unop_hom, unop_id, CommAlgCat.hom_id, ih]
      rw [h, ← Algebra.TensorProduct.lmul'_comp_map, AlgHom.comp_assoc]
      rfl

/-- The pointwise fourth power map of the group object `op A` in `(CommAlgCat R)ᵒᵖ` — the
affine group scheme corresponding to `A` — is not the constant-unit endomorphism. -/
theorem monPowMap_op_four_ne :
    monPowMap (op (CommAlgCat.of R A)) 4 ≠
      toUnit (op (CommAlgCat.of R A)) ≫ η[op (CommAlgCat.of R A)] := by
  intro h
  replace h : monPowMap (op (CommAlgCat.of R A)) 4 = monPowMap (op (CommAlgCat.of R A)) 0 := h
  have h' : powerMap 4 = powerMap 0 := by
    rw [← monPowMap_op_unop_hom, ← monPowMap_op_unop_hom, h]
  exact powerMap_four_U_ne_zero (by simpa using DFunLike.congr_fun h' U)

/-- The rank-four counterexample as an affine group scheme: the group object in the opposite
of the category of commutative `R`-algebras corresponding to `coordinateHopfAlgebra` under
Mathlib's antiequivalence `commHopfAlgCatEquivCogrpCommAlgCat`. -/
noncomputable def affineGroupScheme : Grp (CommAlgCat R)ᵒᵖ :=
  ((commHopfAlgCatEquivCogrpCommAlgCat R).functor.obj coordinateHopfAlgebra).unop

theorem affineGroupScheme_X : affineGroupScheme.X = op (CommAlgCat.of R A) := rfl

/-- The order-four affine group scheme corresponding to `A` (the group object in
`(CommAlgCat R)ᵒᵖ`) is not killed by four: its pointwise fourth power map is not the
constant-unit endomorphism. -/
theorem monPowMap_affineGroupScheme_four_ne :
    monPowMap affineGroupScheme.X 4 ≠
      toUnit affineGroupScheme.X ≫ η[affineGroupScheme.X] :=
  monPowMap_op_four_ne

end

end Counterexample.GrothendieckPower
