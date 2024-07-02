/-
Copyright (c) 2024 Jou Glasheen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jou Glasheen, Amelia Livingston, Jujian Zhang, Kevin Buzzard
-/
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.Algebra.Polynomial.GroupRingAction
import Mathlib.FieldTheory.Finite.Basic

/-!

# Frobenius elements

Frobenius elements in Galois groups.

## Statement of the theorem

Say `L/K` is a finite Galois extension of number fields, with integer rings `B/A`,
and say `Q` is a maximal ideal of `B` dividing `P` of `A`. This file contains the
construction of an element `Frob Q` in `Gal(L/K)`, and a proof that
modulo `Q` it raises elements to the power `q := |A/P|`.

In fact we work in more generality, with a construction which also applies in the function
field setting.

We start with `A ⊆ B` an extension of integral domains, let `G` be `B ≃ₐ[A] B`,
and assume that `A` equals the `G`-invariants of `B` (this assumption is true in the applications
to number fields and function fields). Given `Q/P` a compatible pair of maximal ideals, under the
assumption that `A/P` is a finite field of size `q` and `B/Q` is also finite,
we construct an element `Frob_Q` in `G` and prove:

1) `Frob_Q • Q = Q`;
2) `x ^ q ≡ Frob_Q x (mod Q)`.

Note that if `Q` is ramified, there is more than one choice of `Frob_Q` satisfying the defining
equations; for example if `B=ℤ[i]` and `A=ℤ` then both the identity and complex conjugation
work for `Frob Q` if `Q=(1+i)`. In this situation `Frob` returns a random one (i.e. it's opaque;
all we know is that it satisfies the two properties).

In the applications, `galRestrict` will provide us with the isomorphism `L ≃ₐ[K] L ≃* B ≃ₐ[A] B`
which we need to construct the actual Frobenius elements in Galois groups.

## The construction

We follow a proof in footnote 2 on p141 of [J. S. Milne,  *Algebraic Number Theory*][milne-ANT]

The Galois orbit of `Q` consists of `Q` and possibly some other primes `Q'`. The unit group
`(B/Q)ˣ` is finite and hence cyclic; so by the Chinese Remainder Theorem we may choose `y ∈ B`
which reduces to a generator mod `Q` and to 0 modulo all other `Q'` in the Galois orbit of `Q`.

The polynomial `F = ∏ (X - σ y)`, the product running over `σ` in the Galois group, is in `B[X]`
and is Galois-stable so is in fact in `A[X]`. Hence if `Fbar` is `F mod Q`
then `Fbar` has coefficients in `A/P=𝔽_q` and thus `Fbar(y^q)=Fbar(y)^q=0`, meaning that `y^q`
is a root of `F` mod `Q` and thus congruent mod `Q` to `σ y` for some `σ`. We define `Frob Q` to
be this `σ` (more precisely, any such `σ`).

## The proof

We know `σ y ≡ y ^ q ≠ 0 mod Q`. Hence `σ y ∉ Q`, and thus `y ∉ σ⁻¹ Q`. But `y ∈ Q'` for all
nontrivial conjugates `Q'` of `Q`, hence `σ⁻¹ Q = Q` and thus `Q` is `σ`-stable.

Hence `σ` induces a field automorphism of `B/Q` and we know it's `x ↦ x^q` on a generator,
so it's `x ↦ x^q` on everything.

## Note

This work started its life as Jou Glasheen's final project for Kevin Buzzard's
Formalising Mathematics 2024 course.

## TODO

Check that the hypotheses are satisfied in the two main applications:

1) Finite Galois extensions of number fields and their integers or `S`-integers;
2) Finite Galois extensions of function fields over finite fields, and their `S`-integers for
   `S` a nonempty set of places;

Note that the theorem could also be used to construct the Frobenius element in the
case where `A` and `B` are finite fields, and `Q/P=0/0` (recovering the
classical theory of Frobenius elements).

-/

variable (A : Type*) [CommRing A] {B : Type*} [CommRing B] [Algebra A B]

open scoped Pointwise -- to get Galois action on ideals

namespace ArithmeticFrobenius -- So it will be absolutely clear which Frob we're talking about
-- some authors like to use "Geometric Frobenius", which is the the inverse of this one

namespace Abstract -- stuff in here is auxiliary variables etc, general stuff which will
-- work in number field and function field settings. This namespace is full of junk
-- like `y_spec` and `F_spec` which are auxiliary constructions needed for `Frob` and
-- which we will never need again.

/-

## Auxiliary variables

The noncomputable variables `g : (B ⧸ Q)ˣ` (a generator),
`y : B` (congruent to `g` mod `Q` and to `0` mod all Galois conjugates of `Q`,
`F : B[X]` (the product of `X - σ y` as `σ` runs through the Galois group), and
`m : A[X]`, the descent of `F` to `A[X]` (it's Galois-stable).
-/

variable (Q : Ideal B) [Q.IsMaximal]

variable [Fintype (B ⧸ Q)]

/-- An auxiliary definition needed in the definition of Frobenius elements;
`g` is a generator of the units of the finite field `B ⧸ Q`.-/
noncomputable abbrev g : (B ⧸ Q)ˣ := (IsCyclic.exists_monoid_generator (α := (B ⧸ Q)ˣ)).choose

lemma g_spec : ∀ (z : (B ⧸ Q)ˣ), z ∈ Submonoid.powers (g Q) :=
  (IsCyclic.exists_monoid_generator (α := (B ⧸ Q)ˣ)).choose_spec

variable [Fintype (B ≃ₐ[A] B)] [DecidableEq (Ideal B)]

/-- An element `y` of `B` exists, which is congruent to `b` mod `Q`
and to `0` mod all other Galois conjugates of `Q` (if any).-/
lemma exists_y :
    ∃ y : B, (y : B ⧸ Q) = g Q ∧ ∀ Q' :
    Ideal B, Q' ∈ MulAction.orbit (B ≃ₐ[A] B) Q → Q' ≠ Q → y ∈ Q' := by
  let O : Set (Ideal B) := MulAction.orbit (B ≃ₐ[A] B) Q
  have hO' : Finite (O : Type _) := Set.finite_range _
  have hmax (I : O) : Ideal.IsMaximal (I : Ideal B) := by
    rcases I with ⟨_, σ, rfl⟩
    convert Ideal.comap_isMaximal_of_surjective (K := Q) _ (AlgEquiv.surjective σ.symm)
    apply Ideal.pointwise_smul_eq_comap
  have hPairwise : Pairwise fun (I : O) (J : O) ↦ IsCoprime (I : Ideal B) J := fun x y h ↦ ⟨1, 1, by
    simp only [Ideal.one_eq_top, Ideal.top_mul]
    exact Ideal.IsMaximal.coprime_of_ne (hmax x) (hmax y) <| mt Subtype.ext h⟩
  obtain ⟨y, hy⟩ := Ideal.exists_forall_sub_mem_ideal (ι := O) hPairwise
    (fun J ↦ if J = ⟨Q, 1, by simp⟩ then (Ideal.Quotient.mk_surjective (g Q : B ⧸ Q)).choose else 0)
  refine ⟨y, ?_, ?_⟩
  · specialize hy ⟨Q, 1, by simp⟩
    simp at hy
    rw [← (Ideal.Quotient.mk_surjective (g Q : B ⧸ Q)).choose_spec]
    exact
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem y
        (Ideal.Quotient.mk_surjective (I := Q) (g Q)).choose).mpr hy
  · rintro Q' ⟨σ, rfl⟩ hQ'
    specialize hy ⟨σ • Q, σ, rfl⟩
    simp_all

/-- An auxiliary definition needed for the definition of an abstract Frobenius
element; `y ∈ B` reduces mod `Q` to a generator of the unit group,
and reduces mod `Q'` to `0` for any other maximal ideal Galois-conjugate to `Q`.
Its existence is trivial from the Chinese Remainder Theorem but we need an
explicit name for it. -/
noncomputable abbrev y : B :=
  (exists_y A Q).choose

lemma y_spec : ((y A Q : B) : B ⧸ Q) = g Q ∧
    ∀ Q' : Ideal B, Q' ∈ MulAction.orbit (B ≃ₐ[A] B) Q → Q' ≠ Q → (y A Q) ∈ Q' :=
  (exists_y A Q).choose_spec

lemma y_mod_Q : Ideal.Quotient.mk Q (y A Q) = g Q := (y_spec A Q).1

open scoped algebraMap

lemma y_mod_Q' : (((y A Q) : B) : B ⧸ Q) = (g Q : B ⧸ Q) := y_mod_Q A Q

lemma y_not_in_Q : (y A Q) ∉ Q :=
  mt Ideal.Quotient.eq_zero_iff_mem.mpr <| y_mod_Q A Q ▸ (g Q).ne_zero

open Polynomial BigOperators

/-- `F : B[X]` is defined to be a product of linear factors `(X - τ • y)`; where
`τ` runs over `B ≃ₐ[A] B`, and `y : B` is an element which generates `(B ⧸ Q)ˣ`
and lies in `τ • Q` for all `τ • Q ≠ Q`.-/
noncomputable abbrev F : B[X] := ∏ τ : B ≃ₐ[A] B, (X - C (τ • (y A Q)))

lemma F_spec : F A Q = ∏ τ : B ≃ₐ[A] B, (X - C (τ • (y A Q))) := rfl

variable {A Q} in
open Finset in
lemma F.smul_eq_self (σ :  B ≃ₐ[A] B)  : σ • (F A Q) = F A Q := calc
  σ • F A Q = σ • ∏ τ : B ≃ₐ[A] B, (X - C (τ • (y A Q))) := by rw [F_spec]
  _         = ∏ τ : B ≃ₐ[A] B, σ • (X - C (τ • (y A Q))) := smul_prod
  _         = ∏ τ : B ≃ₐ[A] B, (X - C ((σ * τ) • (y A Q))) := by simp [smul_sub]
  _         = ∏ τ' : B ≃ₐ[A] B, (X - C (τ' • (y A Q))) := Fintype.prod_bijective (fun τ ↦ σ * τ)
                                                      (Group.mulLeft_bijective σ) _ _ (fun _ ↦ rfl)
  _         = F A Q := by rw [F_spec]

lemma F.y_eq_zero : (F A Q).eval (y A Q) = 0 := by
  simp [F_spec, eval_prod, Finset.prod_eq_zero (Finset.mem_univ (1 : B ≃ₐ[A] B))]

open scoped algebraMap

-- This trick enables us to use `norm_cast` to make some proofs less painful.
/-- An auxiliary local instance, enabling us to coerce polynomials
cheaply from `A[X]` to `B[X]` given that `B` is an `A`-algebra.  -/
noncomputable local instance : Algebra A[X] B[X] :=
  RingHom.toAlgebra (Polynomial.mapRingHom (Algebra.toRingHom))

@[simp, norm_cast]
lemma _root_.Polynomial.coe_monomial' (n : ℕ) (a : A) :
    ((monomial n a : A[X]) : B[X]) = monomial n (a : B) :=
  map_monomial _

lemma F.descent (h : ∀ b : B, (∀ σ : B ≃ₐ[A] B, σ • b = b) → ∃ a : A, b = a) :
    ∃ m : A[X], (m : B[X]) = F A Q := by
  choose f hf using h
  classical
  let f' : B → A := fun b ↦ if h : ∀ σ : B ≃ₐ[A] B, σ b = b then f b h else 37
  use (∑ x ∈ (F A Q).support, (monomial x) (f' ((F A Q).coeff x)))
  ext N
  push_cast
  simp_rw [finset_sum_coeff, ← lcoeff_apply, lcoeff_apply, coeff_monomial,
    Finset.sum_ite_eq', mem_support_iff, ne_eq, ite_not, f']
  split
  · next h => exact h.symm
  · next h1 =>
    rw [dif_pos <| fun σ ↦ ?_]
    · refine (hf ?_ ?_).symm
    · nth_rw 2 [← F.smul_eq_self σ]
      rfl

-- This will be true in applications to number fields etc. A Galois-invariant element
-- of `B` is in `A`.
variable (isGalois : ∀ b : B, (∀ σ : B ≃ₐ[A] B, σ • b = b) → ∃ a : A, b = a)

/-- An auxiliary polynomial, needed in the definition of Frobenius elements.
It's the descent to `A[X]` of a certain auxiliary Galois-invariant polynomial in `B[X]`. -/
noncomputable abbrev m := (F.descent A Q isGalois).choose

lemma m_spec : ((m A Q isGalois) : B[X]) = F A Q := (F.descent A Q isGalois).choose_spec

lemma m_spec' : (m A Q isGalois).map (algebraMap A B) = F A Q := by
  rw [← m_spec A Q isGalois]
  rfl

-- Amelia's trick to insert "let P be the ideal under Q" into the typeclass system
variable (P : Ideal A) [P.IsMaximal] [Algebra (A ⧸ P) (B ⧸ Q)] [IsScalarTower A (A⧸P) (B⧸Q)]
variable {A} -- now can be implicit because `P`

lemma m.y_mod_P_eq_zero : Polynomial.aeval (↑(y A Q) : B ⧸ Q) (m A Q isGalois) = 0 := by
  rw [← aeval_map_algebraMap B, m_spec', algebraMap.coe_def, aeval_algebraMap_apply,
    coe_aeval_eq_eval, F.y_eq_zero A Q, map_zero]

open scoped Polynomial

variable [Fintype (A⧸P)]

lemma m.mod_P_y_pow_q_eq_zero' :
    aeval ((algebraMap B (B⧸Q) (y A Q)) ^ (Fintype.card (A⧸P)))  (m A Q isGalois) = 0 := by
  let foobar : Field (A⧸P) := ((Ideal.Quotient.maximal_ideal_iff_isField_quotient P).mp ‹_›).toField
  rw [← aeval_map_algebraMap (A⧸P), FiniteField.aeval_pow_card, ← algebraMap.coe_def,
    aeval_map_algebraMap, m.y_mod_P_eq_zero, zero_pow Fintype.card_ne_zero]

lemma F.mod_Q_y_pow_q_eq_zero' :
    aeval ((algebraMap B (B⧸Q) (y A Q)) ^ (Fintype.card (A⧸P))) (F A Q) = 0 := by
  rw [← m_spec' A Q isGalois, aeval_map_algebraMap, m.mod_P_y_pow_q_eq_zero']

lemma _root_.Polynomial.aeval_finset_prod.{u, v, y} {R : Type u} {S : Type v} {ι : Type y}
    [CommSemiring R] [CommSemiring S] [Algebra R S] (s : Finset ι) (g : ι → R[X]) (x : S) :
  aeval x (∏ i ∈ s, g i) = (∏ i ∈ s, aeval x (g i)) := eval₂_finset_prod (algebraMap R S) s g x

lemma exists_Frob : ∃ σ : B ≃ₐ[A] B, σ (y A Q) - (y A Q) ^ (Fintype.card (A⧸P)) ∈ Q := by
  have := F.mod_Q_y_pow_q_eq_zero' Q isGalois P
  rw [F_spec, aeval_finset_prod, Finset.prod_eq_zero_iff] at this
  obtain ⟨σ, -, hσ⟩ := this
  use σ
  simp only [Ideal.Quotient.algebraMap_eq, AlgEquiv.smul_def, map_sub, aeval_X, aeval_C,
    sub_eq_zero] at hσ
  exact (Submodule.Quotient.eq Q).mp (hσ.symm)

/-- An auxiliary arithmetic Frobenius element, in the automorphism group of the integer ring
rather than the global field itself. -/
noncomputable abbrev Frob := (exists_Frob Q isGalois P).choose

lemma Frob_spec : (Frob Q isGalois P) • (y A Q) - (y A Q) ^ (Fintype.card (A⧸P)) ∈ Q :=
  (exists_Frob Q isGalois P).choose_spec

lemma Frob_Q : Frob Q isGalois P • Q = Q := by
  rw [smul_eq_iff_eq_inv_smul]
  by_contra h
  have hy : y A Q ∈ (Frob Q isGalois P)⁻¹ • Q := (y_spec A Q).2 _ ⟨_, rfl⟩ (Ne.symm h)
  have hy2 : (Frob Q isGalois P) • (y A Q) ∈ Q := by
    rwa [Ideal.pointwise_smul_eq_comap] at hy
  have this := Q.sub_mem hy2 <| Frob_spec Q isGalois P
  simp only [sub_sub_cancel] at this
  apply y_not_in_Q A Q <| Ideal.IsPrime.mem_of_pow_mem (show Q.IsPrime by infer_instance) _ this

lemma Frob_Q_eq_pow_card (x : B) : Frob Q isGalois P x - x ^ (Fintype.card (A⧸P)) ∈ Q := by
  by_cases hx : x ∈ Q
  · refine Q.sub_mem ?_ (Q.pow_mem_of_mem hx _ Fintype.card_pos)
    nth_rw 2 [← Frob_Q Q isGalois P]
    change (Frob Q isGalois P) • x ∈ _
    rw [Ideal.pointwise_smul_eq_comap, Ideal.mem_comap]
    convert hx
    exact inv_smul_smul (Frob Q isGalois P) _
  · letI : Field (B ⧸ Q) := ((Ideal.Quotient.maximal_ideal_iff_isField_quotient Q).mp ‹_›).toField
    let xbar : (B ⧸ Q)ˣ := Units.mk0 (x : B ⧸ Q) <|
      mt (fun h ↦ (Submodule.Quotient.mk_eq_zero Q).mp h) hx
    obtain ⟨n, (hn : g Q ^ n = xbar)⟩ := g_spec Q xbar
    have hn2 : (g Q : B ⧸ Q) ^ n = xbar := by exact_mod_cast hn
    change _ = (x : B ⧸ Q) at hn2
    rw [← Ideal.Quotient.cast_eq_cast_iff_sub_mem]
    push_cast
    rw [← hn2]
    have := Frob_spec Q isGalois P
    rw [← Ideal.Quotient.cast_eq_cast_iff_sub_mem] at this
    push_cast at this
    rw [← y_mod_Q' A Q, pow_right_comm, ← this]
    norm_cast
    rw [Ideal.Quotient.cast_eq_cast_iff_sub_mem, ← smul_pow']
    change (Frob Q isGalois P) • x - _ ∈ _
    rw [← smul_sub]
    nth_rw 3 [ ← Frob_Q Q isGalois P]
    rw [Ideal.smul_mem_pointwise_smul_iff, ← Ideal.Quotient.cast_eq_cast_iff_sub_mem,
      ← hn2, ← y_mod_Q A Q]
    norm_cast
