/-
Copyright (c) 2024 Jou Glasheen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jou Glasheen, Amelia Livingston, Jujian Zhang, Kevin Buzzard
-/
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.IntegralRestrict
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.FieldTheory.Cardinality

/-

# Frobenius elements

Frobenius elements in Galois groups.

## Statement of the theorem

Say `L/K` is a finite Galois extension of number fields, with integer rings `B/A`,
and say `Q` is a maximal ideal of `B` dividing `P` of `A`. This file contains the
construction of an element `Frob Q` in `Gal(L/K)`, and a proof that
modulo `Q` it raises elements to the power `q := |A/P|`.

More generally, our theory works in the "ABKL" setting, with `B/A` a finite extension of
Dedekind domains, and the corresponding extension `L/K` of fields of fractions is
assumed finite and Galois. Given `Q/P` a compatible pair of maximal ideals, under the
assumption that `A/P` is a finite field of size `q`, we construct an element `Frob_Q`
in `Gal(L/K)` and prove:

1) `Frob_Q • Q = Q`;
2) `x ^ q ≡ Frob_Q x (mod Q)`.

Examples where these hypotheses hold are:

1) Finite Galois extensions of number fields and their integers or `S`-integers;
2) Finite Galois extensions of function fields over finite fields, and their `S`-integers for
   `S` a nonempty set of places;
3) Finite Galois extensions of finite fields L/K where B/A=L/K and Q/P=0/0 (recovering the
classical theory of Frobenius elements)

Note that if `Q` is ramified, there is more than one choice of `Frob_Q` which works;
for example if `L=ℚ(i)` and `K=ℚ` then both the identity and complex conjugation
work for `Frob Q` if `Q=(1+i)`, and `Frob` returns a random one (i.e. it's opaque; all we know
is that it satisfies the two properties).

## The construction

We follow a proof in a footnote of a book by Milne. **TODO** which book

The Galois orbit of `Q` consists of `Q` and possibly some other primes `Q'`. The unit group
`(B/Q)ˣ` is finite and hence cyclic; so by the Chinese Remainder Theorem we may choose y ∈ B
which reduces to a generator mod Q and to 0 modulo all other Q' in the Galois orbit of Q.

The polynomial `F = ∏ (X - σ y)`, the product running over `σ` in the Galois group, is in `B[X]`
and is Galois-stable so is in fact in `A[X]`. Hence if `Fbar` is `F mod Q`
then `Fbar` has coefficients in `A/P=𝔽_q` and thus `Fbar(y^q)=Fbar(y)^q=0`, meaning that `y^q`
is a root of `F` mod `Q` and thus congruent to `σ y mod Q` for some `σ`. We define `Frob Q` to
be this `σ`.

## The proof

We know `σ y ≡ y ^ q ≠ 0 mod Q`. Hence `σ y ∉ Q`, and thus `y ∉ σ⁻¹ Q`. But `y ∈ Q'` for all nontrivial
conjugates `Q'` of `Q`, hence `σ⁻¹ Q = Q` and thus `Q` is `σ`-stable.

Hence `σ` induces a field automorphism of `B/Q` and we know it's `x ↦ x^q` on a generator,
so it's `x ↦ x^q` on everything.

## Note

This work started its life as Jou Glasheen's final project for Kevin Buzzard's
Formalising Mathematics 2024 course.

## TODO

Show that this applies to number fields and their rings of integers,
i.e. supply the finiteness typeclasses and descent hypothesis in this case.

-/

variable (A : Type*) [CommRing A] {B : Type*} [CommRing B] [Algebra A B]

-- PR #13294
variable {α : Type*} in
instance Ideal.pointwiseMulSemiringAction
    [Monoid α] [MulSemiringAction α B] : MulSemiringAction α (Ideal B) where
  smul a I := Ideal.map (MulSemiringAction.toRingHom _ _ a) I
  one_smul I :=
    congr_arg (I.map ·) (RingHom.ext <| one_smul α) |>.trans I.map_id
  mul_smul _a₁ _a₂ I :=
    congr_arg (I.map ·) (RingHom.ext <| mul_smul _ _) |>.trans (I.map_map _ _).symm
  smul_one a := by simp only [Ideal.one_eq_top]; exact Ideal.map_top _
  smul_mul a I J := Ideal.map_mul _ I J
  smul_add a I J := Ideal.map_sup _ I J
  smul_zero a := Ideal.map_bot

-- should be in #13294?
variable {α : Type*} in
lemma Ideal.map_eq_comap_symm [Group α] [MulSemiringAction α B] (J : Ideal B) (σ : α) :
    σ • J = J.comap (MulSemiringAction.toRingHom _ _ σ⁻¹) :=
  J.map_comap_of_equiv (MulSemiringAction.toRingEquiv α B σ)

namespace ArithmeticFrobenius
/-

## Auxiliary variables

The noncomputable variables `g : (B ⧸ Q)ˣ` (a generator),
`y : B` (congruent to `g` mod `Q` and to `0` mod all Galois conjugates of `Q`,
`F : B[X]` (the product of `X - σ y` as `σ` runs through the Galois group), and
`m : A[X]`, the descent of `F` to `A[X]` (it's Galois-stable).
-/

variable (Q : Ideal B) [Q.IsMaximal]

variable [Fintype (B ⧸ Q)]

noncomputable abbrev g : (B ⧸ Q)ˣ := (IsCyclic.exists_monoid_generator (α := (B ⧸ Q)ˣ)).choose

lemma g_spec : ∀ (z : (B ⧸ Q)ˣ), z ∈ Submonoid.powers (g Q) :=
  (IsCyclic.exists_monoid_generator (α := (B ⧸ Q)ˣ)).choose_spec

variable [Fintype (B ≃ₐ[A] B)] [DecidableEq (Ideal B)]

/-- An element `y` of `B` exists, which is congruent to `b` mod `Q`
and to 0 mod all Galois conjugates of `Q` (if any).-/
lemma exists_y :
    ∃ y : B, (y : B ⧸ Q) = g Q ∧ ∀ Q' : Ideal B, Q' ∈ MulAction.orbit (B ≃ₐ[A] B) Q → Q' ≠ Q → y ∈ Q' := by
  let O : Set (Ideal B) := MulAction.orbit (B ≃ₐ[A] B) Q
  have hO' : Finite (O : Type _) := Set.finite_range _
  have hmax (I : O) : Ideal.IsMaximal (I : Ideal B) := by
    rcases I with ⟨_, σ, rfl⟩
    convert Ideal.comap_isMaximal_of_surjective (K := Q) _ (AlgEquiv.surjective σ.symm)
    apply Ideal.map_eq_comap_symm
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

noncomputable abbrev y : B :=
  (exists_y A Q).choose

lemma y_spec : ((y A Q : B) : B ⧸ Q) = g Q ∧
    ∀ Q' : Ideal B, Q' ∈ MulAction.orbit (B ≃ₐ[A] B) Q → Q' ≠ Q → (y A Q) ∈ Q' :=
  (exists_y A Q).choose_spec

lemma y_mod_Q : Ideal.Quotient.mk Q (y A Q) = g Q := (y_spec A Q).1

lemma y_not_in_Q : (y A Q) ∉ Q :=
  mt Ideal.Quotient.eq_zero_iff_mem.mpr <| y_mod_Q A Q ▸ (g Q).ne_zero

open Polynomial BigOperators

/-- `F : B[X]` defined to be a product of linear factors `(X - τ • α)`; where
`τ` runs over `L ≃ₐ[K] L`, and `α : B` is an element which generates `(B ⧸ Q)ˣ`
and lies in `τ • Q` for all `τ ∉ (decomposition_subgroup_Ideal'  A K L B Q)`.-/
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

noncomputable local instance : Algebra A[X] B[X] :=
  RingHom.toAlgebra (Polynomial.mapRingHom (Algebra.toRingHom))

@[simp, norm_cast]
lemma coe_monomial (n : ℕ) (a : A) : ((monomial n a : A[X]) : B[X]) = monomial n (a : B) :=
  map_monomial _

lemma F.descent (h : ∀ b : B, (∀ σ : B ≃ₐ[A] B, σ • b = b) → ∃ a : A, b = a) :
    ∃ m : A[X], (m : B[X]) = F A Q := by
  choose f hf using h
  classical
  let f' : B → A := fun b ↦ if h : ∀ σ : B ≃ₐ[A] B, σ b = b then f b h else 37
  use (∑ x ∈ (F A Q).support, (monomial x) (f' ((F A Q).coeff x)))
  ext N
  push_cast
  simp_rw [finset_sum_coeff, ← lcoeff_apply, lcoeff_apply, coeff_monomial]
  simp only [Finset.sum_ite_eq', mem_support_iff, ne_eq, ite_not, f']
  symm
  split
  · next h => exact h
  · next h1 =>
    rw [dif_pos <| fun σ ↦ ?_]
    · refine hf ?_ ?_
    · nth_rw 2 [← F.smul_eq_self σ]
      rfl

-- This will be true in applications to number fields etc.
variable (isGalois : ∀ b : B, (∀ σ : B ≃ₐ[A] B, σ • b = b) → ∃ a : A, b = a)

noncomputable abbrev m := (F.descent A Q isGalois).choose

lemma m_spec : ((m A Q isGalois) : B[X]) = F A Q := (F.descent A Q isGalois).choose_spec

lemma m_spec' : (m A Q isGalois).map (algebraMap A B) = F A Q := by
  rw [← m_spec A Q isGalois]
  rfl

-- Amelia's trick to insert "let P be the ideal under Q" into the typeclass system
variable (P : Ideal A) [P.IsMaximal] [Algebra (A ⧸ P) (B ⧸ Q)] [IsScalarTower A (A⧸P) (B⧸Q)]

-- want to move from eval₂?
lemma m.mod_P_y_eq_zero : (m A Q isGalois).eval₂ (algebraMap A (B⧸Q)) (algebraMap B (B⧸Q) (y A Q)) = 0 := by
  rw [show algebraMap A (B⧸Q) = (algebraMap B (B⧸Q)).comp (algebraMap A B) from IsScalarTower.algebraMap_eq A B (B ⧸ Q)]
  rw [←eval₂_map]
  change eval₂ _ _ (m A Q isGalois : B[X]) = _
  simp [m_spec A Q isGalois, eval_map, F.y_eq_zero]

lemma m.y_mod_P_eq_zero : Polynomial.aeval (↑(y A Q) : B ⧸ Q) (m A Q isGalois) = 0 := by
  rw [← aeval_map_algebraMap B, m_spec']
  -- why can't I do this with a `rw`?
  change aeval (algebraMap B (B⧸Q) (y A Q)) _ = _
  rw [aeval_algebraMap_apply, coe_aeval_eq_eval, F.y_eq_zero A Q, map_zero]


noncomputable abbrev mmodP := (m A Q isGalois).map (algebraMap A (A⧸P))

open scoped Polynomial

-- lemma barg (K : Type*) [Field K] [Fintype K] : ∃ p n : ℕ, p.Prime ∧ Fintype.card K = p ^ n ∧ CharP K p := by
--   obtain ⟨p, n, h₁, h₂⟩ := FiniteField.card' K
--   refine ⟨p, n.val, h₁, h₂, ?_⟩
--   have : (p ^ n.val : K) = 0 := mod_cast h₂ ▸ Nat.cast_card_eq_zero K
--   rw [CharP.charP_iff_prime_eq_zero h₁]
--   simpa only [ne_eq, PNat.ne_zero, not_false_eq_true, pow_eq_zero_iff] using this

-- mathlib
lemma _root_.Polynomial.eval₂_pow_card (k : Type*) [Field k] [Fintype k] (f : k[X])
    (L : Type*) [CommRing L] [Algebra k L]
    (t : L) : f.eval₂ (algebraMap k L) (t^(Fintype.card k)) =
              (f.eval₂ (algebraMap k L) t)^(Fintype.card k) := by
  simp_rw [← Polynomial.aeval_def] -- `eval₂ (algebraMap k L)` is just `aeval`
  rw [← map_pow, ← FiniteField.expand_card, Polynomial.expand_aeval]

variable [Fintype (A⧸P)]
-- (m-bar)(y^q)=0 in B/Q
lemma m.mod_P_y_pow_q_eq_zero :
    (m A Q isGalois).eval₂ (algebraMap A (B⧸Q)) ((algebraMap B (B⧸Q) (y A Q)) ^ (Fintype.card (A⧸P)))
    = 0 := by
  suffices ((m A Q isGalois).map (algebraMap A (A⧸P))).eval₂ (algebraMap (A⧸P) (B⧸Q))
    ((algebraMap B (B⧸Q) (y A Q)) ^ (Fintype.card (A⧸P))) = 0 by
    rwa [eval₂_map, ← IsScalarTower.algebraMap_eq A (A ⧸ P) (B ⧸ Q)] at this
  let foobar : Field (A⧸P) := ((Ideal.Quotient.maximal_ideal_iff_isField_quotient P).mp ‹_›).toField
  rw [eval₂_pow_card, eval₂_map, ← IsScalarTower.algebraMap_eq A (A ⧸ P) (B ⧸ Q), m.mod_P_y_eq_zero, zero_pow]
  exact Fintype.card_ne_zero

lemma F.mod_Q_y_pow_q_eq_zero : (F A Q).eval₂ (algebraMap B (B⧸Q)) ((algebraMap B (B⧸Q) (y A Q)) ^ (Fintype.card (A⧸P))) = 0 := by
  rw [← m_spec' A Q isGalois, eval₂_map]--, m.mod_P_y_pow_q_eq_zero]
  rw [← IsScalarTower.algebraMap_eq A B (B ⧸ Q), m.mod_P_y_pow_q_eq_zero]

lemma exists_Frob : ∃ σ : B ≃ₐ[A] B, σ (y A Q) - (y A Q) ^ (Fintype.card (A⧸P)) ∈ Q := by
  have := F.mod_Q_y_pow_q_eq_zero A Q isGalois P
  rw [F_spec] at this
  rw [eval₂_finset_prod] at this
  rw [Finset.prod_eq_zero_iff] at this
  obtain ⟨σ, -, hσ⟩ := this
  use σ
  simp only [Ideal.Quotient.algebraMap_eq, AlgEquiv.smul_def, eval₂_sub, eval₂_X, eval₂_C,
    sub_eq_zero] at hσ
  exact (Submodule.Quotient.eq Q).mp (hσ.symm)

noncomputable abbrev Frob := (exists_Frob A Q isGalois P).choose

lemma Frob_spec : (Frob A Q isGalois P) • (y A Q) - (y A Q) ^ (Fintype.card (A⧸P)) ∈ Q :=
  (exists_Frob A Q isGalois P).choose_spec

lemma Frob_Q : Frob A Q isGalois P • Q = Q := by
  rw [smul_eq_iff_eq_inv_smul]
  by_contra h
  have hy : y A Q ∈ (Frob A Q isGalois P)⁻¹ • Q := (y_spec A Q).2 _ ⟨_, rfl⟩ (Ne.symm h)
  have hy2 : (Frob A Q isGalois P) • (y A Q) ∈ Q := by
    rwa [Ideal.map_eq_comap_symm] at hy
  have this := Q.sub_mem hy2 <| Frob_spec A Q isGalois P
  simp only [sub_sub_cancel] at this
  apply y_not_in_Q A Q <| Ideal.IsPrime.mem_of_pow_mem (show Q.IsPrime by infer_instance) _ this

lemma _root_.Ideal.Quotient.coe_eq_coe_iff_sub_mem {R : Type*} [CommRing R] {I : Ideal R} (x y : R) :
  (x : R ⧸ I) = y ↔ x - y ∈ I := Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _

lemma coething (A B : Type*) [CommSemiring A] [Ring B] [Algebra A B] (a : A) (n : ℕ) :
    (a ^ n : A) = (a : B) ^ n := by
  --change algebraMap A B a ^ n = algebraMap A B (a ^ n)
  --symm
  exact map_pow _ _ _
--  simp only [map_pow]

--attribute [norm_cast] map_pow

lemma Frob_Q_eq_pow_card (x : B) : Frob A Q isGalois P x - x^(Fintype.card (A⧸P)) ∈ Q := by
  by_cases hx : x ∈ Q
  · refine Q.sub_mem ?_ (Q.pow_mem_of_mem hx _ Fintype.card_pos)
    nth_rw 2 [← Frob_Q A Q isGalois P]
    change (Frob A Q isGalois P) • x ∈ _
    rw [Ideal.map_eq_comap_symm, Ideal.mem_comap]
    convert hx
    exact inv_smul_smul _ _
  ·
    have foo : (x : B ⧸ Q) ≠ 0 :=
      mt (fun h ↦ (Submodule.Quotient.mk_eq_zero Q).mp h) hx
    let foobar : Field (B⧸Q) := ((Ideal.Quotient.maximal_ideal_iff_isField_quotient Q).mp ‹_›).toField
    let xbar : (B ⧸ Q)ˣ := Units.mk0 (x : B ⧸ Q) foo
    obtain ⟨n, (hn : g Q ^ n = xbar)⟩ := g_spec Q xbar
    have hn2 : (g Q : B ⧸ Q) ^ n = xbar := by exact_mod_cast hn
    change _ = (x : B ⧸ Q) at hn2
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    change ((Frob A Q isGalois P) x : B ⧸ Q) = x ^ Fintype.card (A ⧸ P)
    rw [← hn2]
    push_cast
    have fact1 := Frob_spec A Q isGalois P
    have fact2 : y A Q = (g Q : B⧸Q) := y_mod_Q A Q
    rw [← fact2]
    rw [← Ideal.Quotient.coe_eq_coe_iff_sub_mem] at fact1
    push_cast at fact1
    rw [pow_right_comm]
    rw [← fact1]
    norm_cast
    rw [Ideal.Quotient.coe_eq_coe_iff_sub_mem]
    have fact3 := Frob_Q A Q isGalois P
    rw [← smul_pow']
    change (Frob A Q isGalois P) • x - _ ∈ _
    rw [← smul_sub]
    nth_rw 3 [ ← fact3]
    suffices (x - y A Q ^ n) ∈ Q by
      exact?
    rw [smul_mem_smul]
    simp
    skip
    sorry

/- maths proof:

2) σ is x ^ #A/P mod Q
3) Application to number fields
-/
