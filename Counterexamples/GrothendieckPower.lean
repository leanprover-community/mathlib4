/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
import Mathlib.Algebra.Category.CommHopfAlgCat
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.GeomSum
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
Note that `R` is a finite ring of size `2^{10}` satisfying `4 = 0` but `2 ≠ 0`.

The coordinate Hopf algebra of the counterexample is `A = R[U, V] / (U² - abU + b²V, V² - a²V)`,
built as a `QuadraticAlgebra` over the `QuadraticAlgebra` `B := R[V] / (V² - a²V)`.
It is finite free of rank four over `R`.  With
`lambda = (1 + aU) * (1 + bV)`, the comultiplication is determined by

* `Δ(U) = U ⊗ 1 + lambda ⊗ U`,
* `Δ(V) = V ⊗ lambda + 1 ⊗ V`,

and `lambda` is group-like (that is, `Δ(lambda) = lambda ⊗ lambda`).
The counit sends both `U` and `V` to zero. The `n`th convolution power of
the identity — the coordinate map of the pointwise `n`th power `x ↦ xⁿ` of the
group scheme — sends `U` to `(1 + lambda + ⋯ + lambdaⁿ⁻¹) · U`.  For `n = 4` this
is `2bUV ≠ 0`, while the eighth convolution power is the convolution unit
(the composite of the counit with the unit map of `A`) and in particular sends `U` to `0`.
In particular the seventh convolution power supplies an antipode, so `A` is a Hopf
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

* `Counterexample.GrothendieckPower.finrank_A`: `A` has rank four over `R`. Note that
  `A` is also finite and free over `R`, so `A ≅ R⁴` as an `R`-module.
* `Counterexample.GrothendieckPower.powerMap_four_U_ne_zero`: the fourth power map is not
  the convolution unit, since it sends `U` to `2bUV ≠ 0`.
* `Counterexample.GrothendieckPower.powerMap_eight`: the eighth power map is the convolution
  unit.
* `Counterexample.GrothendieckPower.counterexample`: the combined statement: over the
  nontrivial ring `R`, the algebra `A` is finite free of rank four and its fourth power map
  is not the convolution unit.
* `Counterexample.GrothendieckPower.exists_hopfAlgebra_not_killed_by_finrank`: the negative
  answer to Grothendieck's question, spelled out as an existence statement: there is a
  nontrivial commutative ring and a commutative Hopf algebra, free of finite rank over it,
  whose convolution power map at the exponent equal to its rank is not the convolution unit.
* `Counterexample.GrothendieckPower.orderOf_universalPoint`: the universal `A`-valued point
  of the group scheme has order exactly eight.
* `Counterexample.GrothendieckPower.not_isCocomm`: `A` is not cocommutative, i.e. the group
  scheme is noncommutative, as forced by Deligne's theorem for commutative group schemes.
* `Counterexample.GrothendieckPower.id_pow_affineGroupScheme_four_ne_one`: the group-scheme
  formulation, through Mathlib's antiequivalence between commutative Hopf algebras and
  affine group schemes: on the corresponding group object in `(CommAlgCat R)ᵒᵖ`, the
  pointwise fourth power map — the fourth power `𝟙 _ ^ 4` of the identity in the convolution
  monoid of endomorphisms — is not the constant-unit endomorphism.

## Implementation notes

Nontriviality of the base ring (concretely, `2b ≠ 0` in `R`) is certified by an explicit
model: the regular representation of `R` on `M = ℤ/4 × ℤ/4 × (ℤ/2)⁵`, with the actions of
`a` and `b` given by explicit additive endomorphisms and all relations checked
by `decide +kernel`.

The polynomial identities underlying the comultiplication and the power-map computations are
proved once in an arbitrary commutative ring satisfying the relations of `R`
(`law_relations_generic`, `law_lambda_generic`, `theta_identities_generic`) using
`linear_combination`, and then transported along algebra maps.

The generators are given short names in each successive algebra (`aB`, `bB`, `aA`, `bA`) and
in the tensor square (`a₁`, `b₁`, `u₁`, `v₁`, `u₂`, `v₂`, `l₁`, `l₂`).  These are `abbrev`s,
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
    (QuadraticAlgebra.lift.symm_apply_apply ⟨x, hx⟩)

/-!
### An explicit faithful model of the base ring

The base ring `R = ℤ[a, b] / (a³, b³, a²b + 2)` is nontrivial, but this is not syntactically
obvious from its presentation.  We certify it by exhibiting an explicit `R`-module: the
regular representation of `R` on `ℤ/4 × ℤ/4 × (ℤ/2)⁵`, with `a` and `b` acting through
explicit commuting additive endomorphisms.  All required relations are closed under `decide`.
-/

/-- Reduction modulo `2`, as a ring homomorphism `ℤ/4 → ℤ/2`. -/
def reduce : ZMod 4 →+* ZMod 2 := ZMod.castHom (by norm_num : 2 ∣ 4) _

/-- The additive map `ℤ/2 → ℤ/4` sending `1` to `2`. -/
def double : ZMod 2 →+ ZMod 4 := ZMod.lift 2 ⟨2 • Int.castAddHom (ZMod 4), by decide⟩

@[simp] theorem reduce_double (x : ZMod 2) : reduce (double x) = 0 := by
  fin_cases x <;> decide

@[simp] theorem double_reduce (x : ZMod 4) : double (reduce x) = 2 * x := by
  fin_cases x <;> decide

/-- The additive group `ℤ/4 × ℤ/4 × (ℤ/2)⁵`, carrier of the regular representation of the
base ring `R := ℤ[a, b] / (a³, b³, a²b + 2)` (and in particular isomorphic to `R`
as an additive group). -/
abbrev M := ZMod 4 × ZMod 4 × (Fin 5 → ZMod 2)

/-- The additive endomorphism of `M` realizing multiplication by the generator `a` (the class
of the first variable) of the base ring `R = ℤ[a, b] / (a³, b³, a²b + 2)`, in its regular
representation. -/
def aEnd : AddMonoid.End M where
  toFun x :=
    (double (x.2.2 2), double (x.2.2 4),
      ![reduce x.1, x.2.2 0, reduce x.2.1, 0, x.2.2 3])
  map_zero' := by simp
  map_add' x y := by simp

/-- The additive endomorphism of `M` realizing multiplication by the generator `b` (the class
of the second variable) of the base ring `R = ℤ[a, b] / (a³, b³, a²b + 2)`, in its regular
representation. -/
def bEnd : AddMonoid.End M where
  toFun x :=
    (double (x.2.2 1), x.1,
      ![0, 0, x.2.2 0, reduce x.2.1, x.2.2 2])
  map_zero' := by simp
  map_add' x y := by simp

theorem aEnd_bEnd_comm : aEnd * bEnd = bEnd * aEnd := by decide +kernel

theorem aEnd_cube : aEnd ^ 3 = 0 := by decide +kernel

theorem bEnd_cube : bEnd ^ 3 = 0 := by decide +kernel

theorem aEnd_sq_mul_bEnd : aEnd ^ 2 * bEnd + 2 = 0 := by decide +kernel

theorem two_mul_bEnd_ne_zero : 2 * bEnd ≠ 0 := by decide +kernel

private theorem generators_commute {x y : AddMonoid.End M}
    (hx : x ∈ ({aEnd, bEnd} : Set (AddMonoid.End M)))
    (hy : y ∈ ({aEnd, bEnd} : Set (AddMonoid.End M))) : x * y = y * x := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [aEnd_bEnd_comm]

/-- The commutative subring of `AddMonoid.End M` generated by `aEnd` and `bEnd`. -/
def WitnessRing := Subring.closure ({aEnd, bEnd} : Set (AddMonoid.End M))

open scoped IsMulCommutative

noncomputable instance : IsMulCommutative WitnessRing :=
  Subring.isMulCommutative_closure fun _ hx _ hy ↦ generators_commute hx hy

/-- The element `aEnd`, as an element of `WitnessRing`. -/
def aw : WitnessRing := ⟨aEnd, Subring.subset_closure (Set.mem_insert _ _)⟩

/-- The element `bEnd`, as an element of `WitnessRing`. -/
def bw : WitnessRing :=
  ⟨bEnd, Subring.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩

@[simp] theorem aw_cube : aw ^ 3 = 0 := Subtype.ext aEnd_cube

@[simp] theorem bw_cube : bw ^ 3 = 0 := Subtype.ext bEnd_cube

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
abbrev ap : P := X 0

/-- The polynomial variable `b`. -/
abbrev bp : P := X 1

/-- The ideal `(a³, b³, a²b + 2)` of `ℤ[a, b]`. -/
def baseIdeal : Ideal P :=
  Ideal.span ({ap ^ 3, bp ^ 3, ap ^ 2 * bp + C 2} : Set P)

/-- The base ring `R = ℤ[a, b] / (a³, b³, a²b + 2)`. -/
abbrev R := P ⧸ baseIdeal

/-- The class of the variable `a` in the base ring `R`. -/
def a : R := Ideal.Quotient.mk baseIdeal ap

/-- The class of the variable `b` in the base ring `R`. -/
def b : R := Ideal.Quotient.mk baseIdeal bp

@[simp] theorem a_cube : a ^ 3 = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 <| Ideal.subset_span (by simp)

@[simp] theorem b_cube : b ^ 3 = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 <| Ideal.subset_span (by simp)

@[simp] theorem base_relation : a ^ 2 * b + 2 = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 <| Ideal.subset_span (by simp)

/-- Evaluation of integer polynomials at `(aw, bw)` in `WitnessRing`. -/
def evalWitness : P →+* WitnessRing :=
  eval₂Hom (Int.castRingHom WitnessRing) ![aw, bw]

theorem baseIdeal_le_ker_evalWitness : baseIdeal ≤ RingHom.ker evalWitness := by
  rw [baseIdeal, Ideal.span_le]
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl <;> simp [evalWitness, ap, bp]

/-- The ring map `R → WitnessRing`, giving an action of `R` on `M`. -/
def witnessHom : R →+* WitnessRing :=
  Ideal.Quotient.lift baseIdeal evalWitness baseIdeal_le_ker_evalWitness

@[simp] theorem witnessHom_b : witnessHom b = bw := by
  simp [witnessHom, b, evalWitness, bp]

theorem two_b_ne_zero : (2 : R) * b ≠ 0 := by
  intro h
  apply two_bw_ne_zero
  simpa [map_ofNat] using congr_arg witnessHom h

instance : Nontrivial R := ⟨⟨(2 : R) * b, 0, two_b_ne_zero⟩⟩

/-!
### The coordinate algebra `A = R[U, V] / (U² - abU + b²V, V² - a²V)`

The algebra `A` is realized as two nested `QuadraticAlgebra`s, so that its finite freeness of
rank four over `R` follows from the corresponding facts for each step of the tower.
-/

open scoped QuadraticAlgebra

/-- The intermediate quadratic algebra `B = R[V] / (V² - a²V)`. -/
abbrev B := QuadraticAlgebra R 0 (a ^ 2)

/-- The generator `VB` of `B`, satisfying `VB² = a²·VB`. -/
abbrev VB : B := ω

@[simp] theorem VB_relation : VB ^ 2 = algebraMap R B (a ^ 2) * VB := by
  simp [pow_two, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]

/-- The image of `a` in `B`. -/
abbrev aB : B := algebraMap R B a

/-- The image of `b` in `B`. -/
abbrev bB : B := algebraMap R B b

/-- The coordinate algebra `A = B[U] / (U² - abU + b²V) = R[U, V] / (U² - abU + b²V, V² - a²V)`,
finite free of rank four over the base ring `R`. -/
abbrev A := QuadraticAlgebra B (-(bB ^ 2) * VB) (aB * bB)

/-- The generator `U` of `A`, satisfying `U² = abU - b²V`. -/
abbrev U : A := ω

/-- The image `V` of `VB` in `A`. -/
abbrev V : A := algebraMap B A VB

/-- The image `aA` of `a` in `A`. -/
abbrev aA : A := algebraMap R A a

/-- The image `bA` of `b` in `A`. -/
abbrev bA : A := algebraMap R A b

@[simp] theorem U_relation :
    U ^ 2 = algebraMap R A (a * b) * U - algebraMap R A (b ^ 2) * V := by
  rw [pow_two]
  unfold U V
  rw [QuadraticAlgebra.omega_mul_omega_eq_mk]
  ext <;> simp [VB, aB, bB, pow_two, IsScalarTower.algebraMap_apply R B A]

@[simp] theorem V_relation : V ^ 2 = algebraMap R A (a ^ 2) * V := by
  change (algebraMap B A VB) ^ 2 = algebraMap R A (a ^ 2) * algebraMap B A VB
  rw [← map_pow, VB_relation, map_mul, IsScalarTower.algebraMap_apply R B A]

noncomputable instance : Module.Free R A :=
  Module.Free.trans (S := B)

noncomputable instance : Module.Finite R A :=
  Module.Finite.trans B A

theorem finrank_B : Module.finrank R B = 2 :=
  QuadraticAlgebra.finrank_eq_two _ _

theorem finrank_A_over_B : Module.finrank B A = 2 :=
  QuadraticAlgebra.finrank_eq_two _ _

theorem finrank_A : Module.finrank R A = 4 := by
  rw [← Module.finrank_mul_finrank R B A, finrank_B, finrank_A_over_B]

/-!
### The universal property of `A`

An `R`-algebra map out of `A = R[U, V] / (U² - abU + b²V, V² - a²V)` amounts to a pair of
elements of the target satisfying the two defining relations.  The construction goes through
the tower `R → B → A`: the image of `V` determines an `R`-algebra map out of
`B = R[V] / (V² - a²V)`, which makes the target a `B`-algebra, and the image of `U` then
determines a quadratic lift out of `A`.  The `B`-algebra structure depends on the chosen
image of `V`, so it is kept local to the construction and never becomes an instance: the
coproduct below, for example, uses a `B`-algebra structure on `A ⊗[R] A` different from the
canonical one through the left tensor factor.
-/

section UniversalProperty

variable {S : Type*} [CommRing S] [Algebra R S]

/-- The `R`-algebra map `B →ₐ[R] S` sending `VB` to a root of `X² - a²X`. -/
private noncomputable def mkAlgHomB (v : S) (hv : v ^ 2 = algebraMap R S (a ^ 2) * v) :
    B →ₐ[R] S :=
  QuadraticAlgebra.lift ⟨v, by rw [zero_smul, zero_add, Algebra.smul_def, ← pow_two, hv]⟩

private theorem mkAlgHomB_VB (v : S) (hv : v ^ 2 = algebraMap R S (a ^ 2) * v) :
    mkAlgHomB v hv VB = v :=
  quadratic_lift_omega v _

/-- The `R`-algebra map `A →ₐ[R] S` sending `U` and `V` to a pair of elements satisfying the
defining relations of `A`. -/
noncomputable def mkAlgHom (u v : S) (hv : v ^ 2 = algebraMap R S (a ^ 2) * v)
    (hu : u ^ 2 = algebraMap R S (a * b) * u - algebraMap R S (b ^ 2) * v) :
    A →ₐ[R] S :=
  let : Algebra B S := (mkAlgHomB v hv).toRingHom.toAlgebra
  have : IsScalarTower R B S :=
    .of_algebraMap_eq fun r ↦ ((mkAlgHomB v hv).commutes r).symm
  AlgHom.restrictScalars R (QuadraticAlgebra.lift
    ⟨u, show u * u = mkAlgHomB v hv (-(bB ^ 2) * VB) * 1 + mkAlgHomB v hv (aB * bB) * u by
      rw [mul_one, map_mul, map_mul, map_neg, map_pow, mkAlgHomB_VB,
        (mkAlgHomB v hv).commutes, (mkAlgHomB v hv).commutes]
      linear_combination hu + u * map_mul (algebraMap R S) a b -
        v * map_pow (algebraMap R S) b 2⟩ : A →ₐ[B] S)

theorem mkAlgHom_U {u v : S} (hv : v ^ 2 = algebraMap R S (a ^ 2) * v)
    (hu : u ^ 2 = algebraMap R S (a * b) * u - algebraMap R S (b ^ 2) * v) :
    mkAlgHom u v hv hu U = u := by
  let : Algebra B S := (mkAlgHomB v hv).toRingHom.toAlgebra
  exact quadratic_lift_omega u _

theorem mkAlgHom_V {u v : S} (hv : v ^ 2 = algebraMap R S (a ^ 2) * v)
    (hu : u ^ 2 = algebraMap R S (a * b) * u - algebraMap R S (b ^ 2) * v) :
    mkAlgHom u v hv hu V = v := by
  let : Algebra B S := (mkAlgHomB v hv).toRingHom.toAlgebra
  exact ((QuadraticAlgebra.lift _ : A →ₐ[B] S).commutes VB).trans (mkAlgHomB_VB v hv)

end UniversalProperty

/-!
### The comultiplication

The polynomial identities behind the coproduct are proved once, in an arbitrary commutative
ring whose distinguished elements satisfy the relations of `R`, by `linear_combination`
certificates; they are then transported to the tensor square along the two inclusions.
-/

private theorem law_relations_generic {S : Type*} [CommRing S]
    {a b u₁ v₁ u₂ v₂ : S}
    (ha : a ^ 3 = 0) (hb : b ^ 3 = 0) (hab : a ^ 2 * b + 2 = 0)
    (hv₁ : v₁ ^ 2 = a ^ 2 * v₁) (hu₁ : u₁ ^ 2 = a * b * u₁ - b ^ 2 * v₁)
    (hv₂ : v₂ ^ 2 = a ^ 2 * v₂) (hu₂ : u₂ ^ 2 = a * b * u₂ - b ^ 2 * v₂) :
    let l₁ := (1 + a * u₁) * (1 + b * v₁)
    let l₂ := (1 + a * u₂) * (1 + b * v₂)
    let dv := v₁ * l₂ + v₂
    let du := u₁ + l₁ * u₂
    dv ^ 2 = a ^ 2 * dv ∧ du ^ 2 = a * b * du - b ^ 2 * dv := by
  dsimp only
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
    {a b u₁ v₁ u₂ v₂ : S}
    (ha : a ^ 3 = 0) (hb : b ^ 3 = 0) (hab : a ^ 2 * b + 2 = 0)
    (hv₁ : v₁ ^ 2 = a ^ 2 * v₁)
    (hv₂ : v₂ ^ 2 = a ^ 2 * v₂) (hu₂ : u₂ ^ 2 = a * b * u₂ - b ^ 2 * v₂) :
    letI l₁ := (1 + a * u₁) * (1 + b * v₁)
    letI l₂ := (1 + a * u₂) * (1 + b * v₂)
    letI dv := v₁ * l₂ + v₂
    letI du := u₁ + l₁ * u₂
    (1 + a * du) * (1 + b * dv) = l₁ * l₂ := by
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

/-- The group-like unit controlling the semidirect-product law. -/
def lambda : A := (1 + aA * U) * (1 + bA * V)

private theorem mapped_relations {S : Type*} [CommRing S] [Algebra R S]
    (f : A →ₐ[R] S) :
    letI aa := f aA
    letI bb := f bA
    letI uu := f U
    letI vv := f V
    aa ^ 3 = 0 ∧ bb ^ 3 = 0 ∧ aa ^ 2 * bb + 2 = 0 ∧
      vv ^ 2 = aa ^ 2 * vv ∧ uu ^ 2 = aa * bb * uu - bb ^ 2 * vv := by
  split_ands
  · simp [aA, ← map_pow, a_cube]
  · simp [bA, ← map_pow, b_cube]
  · have h : aA ^ 2 * bA + 2 = 0 := by
      unfold aA bA
      calc
        (algebraMap R A a) ^ 2 * algebraMap R A b + 2 =
            algebraMap R A (a ^ 2 * b + 2) := by
              rw [map_add, map_mul, map_pow, map_ofNat]
        _ = algebraMap R A 0 := congr_arg (algebraMap R A) base_relation
        _ = 0 := map_zero _
    simpa only [map_add, map_mul, map_pow, map_ofNat, map_zero] using congr_arg f h
  · rw [← map_pow, V_relation, map_mul]
    simp [aA, ← map_pow]
  · have h : U ^ 2 = aA * bA * U - bA ^ 2 * V := by
      simp [aA, bA, map_pow, map_mul]
    simpa only [map_pow, map_sub, map_mul] using congr_arg f h

open scoped TensorProduct

/-- The inclusion of the left tensor factor `A → A ⊗[R] A`. -/
abbrev left : A →ₐ[R] A ⊗[R] A := Algebra.TensorProduct.includeLeft

/-- The inclusion of the right tensor factor `A → A ⊗[R] A`. -/
abbrev right : A →ₐ[R] A ⊗[R] A := Algebra.TensorProduct.includeRight

/-- The image of `a` in `A ⊗[R] A`. -/
abbrev a₁ : A ⊗[R] A := left aA

/-- The image of `b` in `A ⊗[R] A`. -/
abbrev b₁ : A ⊗[R] A := left bA

private theorem right_aA : right aA = a₁ := by
  change (1 : A) ⊗ₜ[R] aA = aA ⊗ₜ[R] (1 : A)
  rw [show aA = a • (1 : A) from Algebra.algebraMap_eq_smul_one a]
  exact (TensorProduct.tmul_smul a 1 1).trans (TensorProduct.smul_tmul' a 1 1).symm

private theorem right_bA : right bA = b₁ := by
  change (1 : A) ⊗ₜ[R] bA = bA ⊗ₜ[R] (1 : A)
  rw [show bA = b • (1 : A) from Algebra.algebraMap_eq_smul_one b]
  exact (TensorProduct.tmul_smul b 1 1).trans (TensorProduct.smul_tmul' b 1 1).symm

/-- The image of `U` in the left tensor factor. -/
abbrev u₁ : A ⊗[R] A := left U

/-- The image of `V` in the left tensor factor. -/
abbrev v₁ : A ⊗[R] A := left V

/-- The image of `U` in the right tensor factor. -/
abbrev u₂ : A ⊗[R] A := right U

/-- The image of `V` in the right tensor factor. -/
abbrev v₂ : A ⊗[R] A := right V

/-- The image of `lambda` in the left tensor factor. -/
abbrev l₁ : A ⊗[R] A := (1 + a₁ * u₁) * (1 + b₁ * v₁)

/-- The image of `lambda` in the right tensor factor. -/
abbrev l₂ : A ⊗[R] A := (1 + a₁ * u₂) * (1 + b₁ * v₂)

/-- The proposed coproduct of `V`. -/
def deltaV : A ⊗[R] A := v₁ * l₂ + v₂

/-- The proposed coproduct of `U`. -/
def deltaU : A ⊗[R] A := u₁ + l₁ * u₂

private theorem delta_relations :
    deltaV ^ 2 = a₁ ^ 2 * deltaV ∧
      deltaU ^ 2 = a₁ * b₁ * deltaU - b₁ ^ 2 * deltaV := by
  obtain ⟨ha₁, hb₁, hab₁, hv₁', hu₁'⟩ := mapped_relations (S := A ⊗[R] A) left
  obtain ⟨_, _, _, hv₂', hu₂'⟩ := mapped_relations (S := A ⊗[R] A) right
  simp only [right_aA, right_bA] at hv₂' hu₂'
  exact law_relations_generic ha₁ hb₁ hab₁ hv₁' hu₁' hv₂' hu₂'

private theorem delta_lambda :
    (1 + a₁ * deltaU) * (1 + b₁ * deltaV) = l₁ * l₂ := by
  obtain ⟨ha₁, hb₁, hab₁, hv₁', -⟩ := mapped_relations (S := A ⊗[R] A) left
  obtain ⟨-, -, -, hv₂', hu₂'⟩ := mapped_relations (S := A ⊗[R] A) right
  simp only [right_aA, right_bA] at hv₂' hu₂'
  exact law_lambda_generic ha₁ hb₁ hab₁ hv₁' hv₂' hu₂'

private theorem a₁_smul : a₁ = a • 1 := by
  change (aA ⊗ₜ[R] (1 : A)) = a • 1
  rw [show aA = a • (1 : A) from Algebra.algebraMap_eq_smul_one a]
  exact TensorProduct.smul_tmul' a 1 1

private theorem b₁_smul : b₁ = b • 1 := by
  change (bA ⊗ₜ[R] (1 : A)) = b • 1
  rw [show bA = b • (1 : A) from Algebra.algebraMap_eq_smul_one b]
  exact TensorProduct.smul_tmul' b 1 1

/-- The coproduct algebra homomorphism, sending `U` to `deltaU` and `V` to `deltaV`. -/
noncomputable def comul : A →ₐ[R] A ⊗[R] A :=
  mkAlgHom deltaU deltaV
    (by rw [← left.commutes (a ^ 2), map_pow, map_pow]; exact delta_relations.1)
    (by rw [← left.commutes (a * b), ← left.commutes (b ^ 2), map_mul, map_mul, map_pow,
      map_pow]; exact delta_relations.2)

theorem comul_U : comul U = deltaU := mkAlgHom_U _ _

theorem comul_V : comul V = deltaV := mkAlgHom_V _ _

theorem comul_aA : comul aA = a₁ := by
  rw [comul.commutes, Algebra.algebraMap_eq_smul_one, ← a₁_smul]

theorem comul_bA : comul bA = b₁ := by
  rw [comul.commutes, Algebra.algebraMap_eq_smul_one, ← b₁_smul]

theorem left_lambda : left lambda = l₁ := by
  simp only [lambda, map_mul, map_add, map_one]

theorem right_lambda : right lambda = l₂ := by
  simp only [lambda, map_mul, map_add, map_one, right_aA, right_bA]

@[simp] theorem comul_lambda : comul lambda = left lambda * right lambda := by
  rw [left_lambda, right_lambda]
  simpa [lambda, map_mul, map_add, comul_aA, comul_bA, comul_U, comul_V] using delta_lambda

@[simp] theorem comul_U_formula :
    comul U = left U + left lambda * right U := by
  rw [comul_U, left_lambda]
  rfl

@[simp] theorem comul_V_formula :
    comul V = left V * right lambda + right V := by
  rw [comul_V, right_lambda]
  rfl

/-- Two `R`-algebra maps out of `A` agree if they agree on `U` and `V`. -/
theorem algHom_ext {S : Type*} [Semiring S] [Algebra R S]
    {f g : A →ₐ[R] S} (hU : f U = g U) (hv : f V = g V) : f = g := by
  ext x
  have h_embed (z : B) :
      algebraMap B A z = algebraMap R A z.re + algebraMap R A z.im * V := by
    have hz : z = algebraMap R B z.re + algebraMap R B z.im * VB := by
      calc
        z = ⟨z.re, z.im⟩ := rfl
        _ = algebraMap R B z.re + z.im • VB :=
          QuadraticAlgebra.mk_eq_add_smul_omega z.re z.im
        _ = algebraMap R B z.re + algebraMap R B z.im * VB := by
          apply QuadraticAlgebra.ext <;> simp [VB]
    calc
      algebraMap B A z = algebraMap B A
          (algebraMap R B z.re + algebraMap R B z.im * VB) := congr_arg _ hz
      _ = algebraMap R A z.re + algebraMap R A z.im * V := by
        rw [map_add, map_mul, ← IsScalarTower.algebraMap_apply R B A,
          ← IsScalarTower.algebraMap_apply R B A]
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

/-- The counit algebra homomorphism, sending `U` and `V` to zero. -/
noncomputable def counit : A →ₐ[R] R :=
  mkAlgHom 0 0 (by simp) (by simp)

@[simp] theorem counit_V : counit V = 0 := mkAlgHom_V _ _

@[simp] theorem counit_U : counit U = 0 := mkAlgHom_U _ _

@[simp] theorem counit_lambda : counit lambda = 1 := by
  simp [lambda]

private theorem comul_coassoc :
    (Algebra.TensorProduct.assoc R R R A A A).toAlgHom.comp
        ((Algebra.TensorProduct.map comul (.id R A)).comp comul) =
      (Algebra.TensorProduct.map (.id R A) comul).comp comul := by
  apply algHom_ext
  · simp [comul_U_formula, comul_lambda, Algebra.TensorProduct.one_def,
      TensorProduct.add_tmul, TensorProduct.tmul_add, add_assoc]
  · simp [comul_V_formula, comul_lambda, Algebra.TensorProduct.one_def,
      TensorProduct.add_tmul, TensorProduct.tmul_add, add_assoc]

private theorem counit_left :
    (Algebra.TensorProduct.map counit (.id R A)).comp comul =
      (Algebra.TensorProduct.lid R A).symm := by
  apply algHom_ext
  · simp [counit_lambda]
  · simp

private theorem counit_right :
    (Algebra.TensorProduct.map (.id R A) counit).comp comul =
      (Algebra.TensorProduct.rid R R A).symm := by
  apply algHom_ext
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
rings, to the `n`th convolution power of the identity of `A`.  On the skew-primitive
coordinates it is controlled by the geometric sum
`1 + lambda + ⋯ + lambdaⁿ⁻¹`, which we compute from the square-zero element
`theta = lambda - 1`.
-/

/-- The square-zero part of the group-like coordinate. -/
def theta : A := lambda - 1

private theorem theta_identities_generic {S : Type*} [CommRing S]
    {aa bb uu vv : S}
    (ha : aa ^ 3 = 0) (hb : bb ^ 3 = 0) (hab : aa ^ 2 * bb + 2 = 0)
    (hv : vv ^ 2 = aa ^ 2 * vv)
    (hu : uu ^ 2 = aa * bb * uu - bb ^ 2 * vv) :
    letI th := (1 + aa * uu) * (1 + bb * vv) - 1
    th ^ 2 = 0 ∧ 2 * th = 2 * bb * vv := by
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
  exact (theta_identities_generic ha hb hab hv hu).1

theorem two_theta : 2 * theta = 2 * bA * V := by
  obtain ⟨ha, hb, hab, hv, hu⟩ := mapped_relations (AlgHom.id R A)
  exact (theta_identities_generic ha hb hab hv hu).2

open WithConv

/-- The universal point, in the convolution monoid of `R`-algebra endomorphisms. -/
noncomputable def universalPoint : WithConv (A →ₐ[R] A) :=
  toConv (AlgHom.id R A)

/-- The `n`th convolution power of the identity of `A`: the coordinate ring map of the
pointwise `n`th power map of the group scheme. -/
noncomputable def powerMap (n : ℕ) : A →ₐ[R] A :=
  (universalPoint ^ n).ofConv

@[simp] theorem powerMap_zero_apply (x : A) : powerMap 0 x = algebraMap R A (counit x) := by
  rfl

@[simp] theorem powerMap_one_apply (x : A) : powerMap 1 x = x :=
  congr_arg (fun f : WithConv (A →ₐ[R] A) ↦ f.ofConv x) (pow_one universalPoint)

theorem powerMap_succ_U (n : ℕ) :
    powerMap (n + 1) U = powerMap n U + powerMap n lambda * U := by
  change (universalPoint ^ (n + 1)).ofConv U = _
  rw [pow_succ universalPoint n, AlgHom.convMul_apply, ← Bialgebra.comulAlgHom_apply,
    bialgebra_comulAlgHom, comul_U_formula]
  simp [universalPoint, powerMap]

theorem powerMap_succ_V (n : ℕ) :
    powerMap (n + 1) V = powerMap n V * lambda + V := by
  change (universalPoint ^ (n + 1)).ofConv V = _
  rw [pow_succ universalPoint n, AlgHom.convMul_apply, ← Bialgebra.comulAlgHom_apply,
    bialgebra_comulAlgHom, comul_V_formula]
  simp [universalPoint, powerMap]

theorem powerMap_succ_lambda (n : ℕ) :
    powerMap (n + 1) lambda = powerMap n lambda * lambda := by
  change (universalPoint ^ (n + 1)).ofConv lambda = _
  rw [pow_succ universalPoint n, AlgHom.convMul_apply, ← Bialgebra.comulAlgHom_apply,
    bialgebra_comulAlgHom, comul_lambda]
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
  have ht (k : ℕ) (hk : 2 ≤ k) : theta ^ k = 0 := pow_eq_zero_of_le hk theta_sq
  rw [lambda_eq_one_add_theta]
  linear_combination theta * four_eq_zero + 6 * theta_sq + 4 * ht 3 (by norm_num) +
    ht 4 (by norm_num)

theorem powerMap_lambda (n : ℕ) : powerMap n lambda = lambda ^ n := by
  induction n with
  | zero => simp [powerMap_zero_apply, counit_lambda]
  | succ n ih => rw [powerMap_succ_lambda, ih, pow_succ lambda n]

theorem powerMap_U (n : ℕ) : powerMap n U = (∑ i ∈ Finset.range n, lambda ^ i) * U := by
  induction n with
  | zero => simp [powerMap_zero_apply, counit_U]
  | succ n ih => rw [powerMap_succ_U, ih, powerMap_lambda, geom_sum_succ']; ring

theorem powerMap_V (n : ℕ) : powerMap n V = V * ∑ i ∈ Finset.range n, lambda ^ i := by
  induction n with
  | zero => simp [powerMap_zero_apply, counit_V]
  | succ n ih => rw [powerMap_succ_V, ih, geom_sum_succ]; ring

theorem geom_sum_four : ∑ i ∈ Finset.range 4, lambda ^ i = 2 * bA * V := by
  have ht (k : ℕ) (hk : 2 ≤ k) : theta ^ k = 0 := pow_eq_zero_of_le hk theta_sq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, lambda_eq_one_add_theta]
  linear_combination two_theta + (1 + theta) * four_eq_zero + 4 * theta_sq + ht 3 (by norm_num)

theorem powerMap_four_U : powerMap 4 U = 2 * bA * U * V := by
  rw [powerMap_U, geom_sum_four]
  ring

theorem two_b_U_V_ne_zero : 2 * bA * U * V ≠ 0 := by
  intro h
  have hOuter := congr_arg (fun x : A ↦ x.im) h
  have hInner := congr_arg (fun x : B ↦ x.im) hOuter
  apply two_b_ne_zero
  simpa [bA, U, V, VB, IsScalarTower.algebraMap_apply R B A] using hInner

theorem powerMap_four_U_ne_zero : powerMap 4 U ≠ 0 := by
  rw [powerMap_four_U]
  exact two_b_U_V_ne_zero

theorem powerMap_four_V : powerMap 4 V = 0 := by
  rw [powerMap_V, geom_sum_four]
  have hv : V ^ 2 = aA ^ 2 * V := by
    simp [aA, map_pow]
  have hab : aA ^ 2 * bA + 2 = 0 := by
    obtain ⟨_, _, hab, _, _⟩ := mapped_relations (AlgHom.id R A)
    simpa using hab
  rw [show V * (2 * bA * V) = 2 * bA * V ^ 2 by ring, hv]
  linear_combination 2 * V * hab - V * four_eq_zero

theorem geom_sum_eight : ∑ i ∈ Finset.range 8, lambda ^ i = 0 := by
  have ht (k : ℕ) (hk : 2 ≤ k) : theta ^ k = 0 := pow_eq_zero_of_le hk theta_sq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, lambda_eq_one_add_theta]
  linear_combination (2 + 7 * theta) * four_eq_zero + 56 * theta_sq +
    70 * ht 3 (by norm_num) + 56 * ht 4 (by norm_num) + 28 * ht 5 (by norm_num) +
    8 * ht 6 (by norm_num) + ht 7 (by norm_num)

theorem powerMap_eight_U : powerMap 8 U = 0 := by
  rw [powerMap_U, geom_sum_eight, zero_mul]

theorem powerMap_eight_V : powerMap 8 V = 0 := by
  rw [powerMap_V, geom_sum_eight, mul_zero]

theorem powerMap_eight : powerMap 8 = (Algebra.ofId R A).comp counit := by
  apply algHom_ext
  · simp [powerMap_eight_U]
  · simp [powerMap_eight_V]

theorem universalPoint_pow_eight : universalPoint ^ 8 = 1 :=
  WithConv.ext powerMap_eight

theorem universalPoint_pow_four_ne_one : universalPoint ^ 4 ≠ 1 := by
  intro h
  have h' : powerMap 4 = powerMap 0 := congr_arg WithConv.ofConv h
  exact powerMap_four_U_ne_zero (by simpa using DFunLike.congr_fun h' U)

/-- In the group of `A`-valued points of the group scheme, the universal point has order
exactly eight: an element of order eight on a group scheme of order four. -/
theorem orderOf_universalPoint : orderOf universalPoint = 8 := by
  simpa using orderOf_eq_prime_pow (p := 2) (n := 2) universalPoint_pow_four_ne_one
    universalPoint_pow_eight

/-!
### The Hopf algebra structure and the main statement

Since the eighth convolution power of the identity is the convolution unit, the seventh
convolution power is a two-sided convolution inverse of the identity, that is, an antipode.
-/

private theorem powerMap_seven_mul_universalPoint :
    toConv (powerMap 7) * universalPoint = 1 := by
  simpa [powerMap, ← pow_succ] using universalPoint_pow_eight

private theorem universalPoint_mul_powerMap_seven :
    universalPoint * toConv (powerMap 7) = 1 := by
  simpa [powerMap, ← pow_succ'] using universalPoint_pow_eight

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

/-- The Hopf `R`-algebra structure on `A`. -/
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
  simp [h]

/-- **Grothendieck's question has a negative answer.**  Grothendieck asked whether every finite
locally free group scheme of order `n` is killed by `n` — equivalently, whether the `n`-th
convolution power of the identity of a commutative Hopf algebra that is free of rank `n` over
the base ring is always the convolution unit `1` (the composite of the counit with the unit).
This is false: there is a nontrivial commutative ring `S` and a commutative `S`-Hopf algebra
`H`, free of finite rank over `S`, whose `(Module.finrank S H)`-th convolution power of the
identity is not the convolution unit.  The witness is the rank-four Hopf algebra `A` over `R`;
see `counterexample`. -/
theorem exists_hopfAlgebra_not_killed_by_finrank :
    ∃ (S : Type) (_ : CommRing S) (_ : Nontrivial S) (H : Type) (_ : CommRing H)
      (_ : HopfAlgebra S H) (_ : Module.Free S H) (_ : Module.Finite S H),
        0 < Module.finrank S H ∧
          WithConv.toConv (AlgHom.id S H) ^ Module.finrank S H ≠ 1 := by
  refine ⟨R, inferInstance, inferInstance, A, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_, ?_⟩
  · rw [finrank_A]; norm_num
  · rw [finrank_A]
    have h8 : orderOf (WithConv.toConv (AlgHom.id R A)) = 8 := orderOf_universalPoint
    exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [h8]; norm_num)

/-!
### Non-cocommutativity

By Deligne's theorem, a commutative finite locally free group scheme is killed by its order,
so the group scheme represented by `A` is necessarily noncommutative; equivalently, `A` is
not cocommutative.  We verify this directly: the coefficient functional of `U` distinguishes
`Δ(U)` from its swap.
-/

/-- The `R`-linear coefficient functional of `U` in the basis `1, V, U, U * V` of `A`. -/
private def coeffU : A →ₗ[R] R where
  toFun x := x.im.re
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The `R`-linear coefficient functional of `V` in the basis `1, V, U, U * V` of `A`. -/
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
    simp [lambda, aA, bA, U, V, VB, IsScalarTower.algebraMap_apply R B A]
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

open CategoryTheory MonObj Opposite

/-- On the group object `op A` in `(CommAlgCat R)ᵒᵖ` — the affine group scheme corresponding
to `A` — the pointwise `n`-th power map `𝟙 _ ^ n` (the `n`-th power of the identity in the
convolution monoid `CategoryTheory.Hom.monoid` of endomorphisms; for a group scheme, the
morphism `x ↦ xⁿ`, which is not in general a homomorphism) corresponds to the `n`-th
convolution power of the identity of `A`. -/
theorem id_pow_op_unop_hom (n : ℕ) :
    (𝟙 (op (CommAlgCat.of R A)) ^ n).unop.hom = powerMap n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h : (𝟙 (op (CommAlgCat.of R A)) ^ (n + 1)).unop.hom =
          (Algebra.TensorProduct.lift (powerMap n) (AlgHom.id R A)
              fun _ _ ↦ Commute.all _ _).comp
            (Bialgebra.comulAlgHom R A) := by
        simp only [pow_succ, Hom.mul_def, unop_comp, CommAlgCat.hom_comp,
          CommAlgCat.mul_op_of_unop_hom, CommAlgCat.lift_unop_hom, unop_id, CommAlgCat.hom_id,
          ih]
      rw [h, ← Algebra.TensorProduct.lmul'_comp_map, AlgHom.comp_assoc]
      rfl

/-- The pointwise fourth power map of the group object `op A` in `(CommAlgCat R)ᵒᵖ` — the
affine group scheme corresponding to `A` — is not the constant-unit endomorphism `1`. -/
theorem id_pow_op_four_ne_one : 𝟙 (op (CommAlgCat.of R A)) ^ 4 ≠ 1 := by
  intro h
  have h' : powerMap 4 = powerMap 0 := by
    rw [← id_pow_op_unop_hom, ← id_pow_op_unop_hom, pow_zero, h]
  exact powerMap_four_U_ne_zero (by simpa using DFunLike.congr_fun h' U)

/-- The rank-four counterexample as an affine group scheme: the group object in the opposite
of the category of commutative `R`-algebras corresponding to `coordinateHopfAlgebra` under
Mathlib's antiequivalence `commHopfAlgCatEquivCogrpCommAlgCat`. -/
noncomputable def affineGroupScheme : Grp (CommAlgCat R)ᵒᵖ :=
  ((commHopfAlgCatEquivCogrpCommAlgCat R).functor.obj coordinateHopfAlgebra).unop

theorem affineGroupScheme_X : affineGroupScheme.X = op (CommAlgCat.of R A) := rfl

/-- The order-four affine group scheme corresponding to `A` (the group object in
`(CommAlgCat R)ᵒᵖ`) is not killed by four: its pointwise fourth power map — the fourth power
of the identity in the convolution monoid of endomorphisms — is not the constant-unit
endomorphism `1`. -/
theorem id_pow_affineGroupScheme_four_ne_one : 𝟙 affineGroupScheme.X ^ 4 ≠ 1 :=
  id_pow_op_four_ne_one

end

end Counterexample.GrothendieckPower
