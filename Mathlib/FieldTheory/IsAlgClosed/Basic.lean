/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.FieldTheory.Normal
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Localization.Integral

#align_import field_theory.is_alg_closed.basic from "leanprover-community/mathlib"@"00f91228655eecdcd3ac97a7fd8dbcb139fe990a"

/-!
# Algebraically Closed Field

In this file we define the typeclass for algebraically closed fields and algebraic closures,
and prove some of their properties.

## Main Definitions

- `IsAlgClosed k` is the typeclass saying `k` is an algebraically closed field, i.e. every
polynomial in `k` splits.

- `IsAlgClosure R K` is the typeclass saying `K` is an algebraic closure of `R`, where `R` is a
  commutative ring. This means that the map from `R` to `K` is injective, and `K` is
  algebraically closed and algebraic over `R`

- `IsAlgClosed.lift` is a map from an algebraic extension `L` of `R`, into any algebraically
  closed extension of `R`.

- `IsAlgClosure.equiv` is a proof that any two algebraic closures of the
  same field are isomorphic.

## Tags

algebraic closure, algebraically closed

## TODO

- Prove that if `K / k` is algebraic, and any monic irreducible polynomial over `k` has a root
  in `K`, then `K` is algebraically closed (in fact an algebraic closure of `k`).

  Reference: <https://kconrad.math.uconn.edu/blurbs/galoistheory/algclosure.pdf>, Theorem 2

-/


universe u v w

open scoped Classical Polynomial

open Polynomial

variable (k : Type u) [Field k]

/-- Typeclass for algebraically closed fields.

To show `Polynomial.Splits p f` for an arbitrary ring homomorphism `f`,
see `IsAlgClosed.splits_codomain` and `IsAlgClosed.splits_domain`.
-/
class IsAlgClosed : Prop where
  splits : ∀ p : k[X], p.Splits <| RingHom.id k
#align is_alg_closed IsAlgClosed

/-- Every polynomial splits in the field extension `f : K →+* k` if `k` is algebraically closed.

See also `IsAlgClosed.splits_domain` for the case where `K` is algebraically closed.
-/
theorem IsAlgClosed.splits_codomain {k K : Type*} [Field k] [IsAlgClosed k] [Field K] {f : K →+* k}
    (p : K[X]) : p.Splits f := by convert IsAlgClosed.splits (p.map f); simp [splits_map_iff]
#align is_alg_closed.splits_codomain IsAlgClosed.splits_codomain

/-- Every polynomial splits in the field extension `f : K →+* k` if `K` is algebraically closed.

See also `IsAlgClosed.splits_codomain` for the case where `k` is algebraically closed.
-/
theorem IsAlgClosed.splits_domain {k K : Type*} [Field k] [IsAlgClosed k] [Field K] {f : k →+* K}
    (p : k[X]) : p.Splits f :=
  Polynomial.splits_of_splits_id _ <| IsAlgClosed.splits _
#align is_alg_closed.splits_domain IsAlgClosed.splits_domain

namespace IsAlgClosed

variable {k}

theorem exists_root [IsAlgClosed k] (p : k[X]) (hp : p.degree ≠ 0) : ∃ x, IsRoot p x :=
  exists_root_of_splits _ (IsAlgClosed.splits p) hp
#align is_alg_closed.exists_root IsAlgClosed.exists_root

theorem exists_pow_nat_eq [IsAlgClosed k] (x : k) {n : ℕ} (hn : 0 < n) : ∃ z, z ^ n = x := by
  have : degree (X ^ n - C x) ≠ 0 := by
    rw [degree_X_pow_sub_C hn x]
    exact ne_of_gt (WithBot.coe_lt_coe.2 hn)
  obtain ⟨z, hz⟩ := exists_root (X ^ n - C x) this
  use z
  simp only [eval_C, eval_X, eval_pow, eval_sub, IsRoot.def] at hz
  exact sub_eq_zero.1 hz
#align is_alg_closed.exists_pow_nat_eq IsAlgClosed.exists_pow_nat_eq

theorem exists_eq_mul_self [IsAlgClosed k] (x : k) : ∃ z, x = z * z := by
  rcases exists_pow_nat_eq x zero_lt_two with ⟨z, rfl⟩
  exact ⟨z, sq z⟩
#align is_alg_closed.exists_eq_mul_self IsAlgClosed.exists_eq_mul_self

theorem roots_eq_zero_iff [IsAlgClosed k] {p : k[X]} :
    p.roots = 0 ↔ p = Polynomial.C (p.coeff 0) := by
  refine ⟨fun h => ?_, fun hp => by rw [hp, roots_C]⟩
  rcases le_or_lt (degree p) 0 with hd | hd
  · exact eq_C_of_degree_le_zero hd
  · obtain ⟨z, hz⟩ := IsAlgClosed.exists_root p hd.ne'
    rw [← mem_roots (ne_zero_of_degree_gt hd), h] at hz
    simp at hz
#align is_alg_closed.roots_eq_zero_iff IsAlgClosed.roots_eq_zero_iff

theorem exists_eval₂_eq_zero_of_injective {R : Type*} [Ring R] [IsAlgClosed k] (f : R →+* k)
    (hf : Function.Injective f) (p : R[X]) (hp : p.degree ≠ 0) : ∃ x, p.eval₂ f x = 0 :=
  let ⟨x, hx⟩ := exists_root (p.map f) (by rwa [degree_map_eq_of_injective hf])
  ⟨x, by rwa [eval₂_eq_eval_map, ← IsRoot]⟩
#align is_alg_closed.exists_eval₂_eq_zero_of_injective IsAlgClosed.exists_eval₂_eq_zero_of_injective

theorem exists_eval₂_eq_zero {R : Type*} [Field R] [IsAlgClosed k] (f : R →+* k) (p : R[X])
    (hp : p.degree ≠ 0) : ∃ x, p.eval₂ f x = 0 :=
  exists_eval₂_eq_zero_of_injective f f.injective p hp
#align is_alg_closed.exists_eval₂_eq_zero IsAlgClosed.exists_eval₂_eq_zero

variable (k)

theorem exists_aeval_eq_zero_of_injective {R : Type*} [CommRing R] [IsAlgClosed k] [Algebra R k]
    (hinj : Function.Injective (algebraMap R k)) (p : R[X]) (hp : p.degree ≠ 0) :
    ∃ x : k, aeval x p = 0 :=
  exists_eval₂_eq_zero_of_injective (algebraMap R k) hinj p hp
#align is_alg_closed.exists_aeval_eq_zero_of_injective IsAlgClosed.exists_aeval_eq_zero_of_injective

theorem exists_aeval_eq_zero {R : Type*} [Field R] [IsAlgClosed k] [Algebra R k] (p : R[X])
    (hp : p.degree ≠ 0) : ∃ x : k, aeval x p = 0 :=
  exists_eval₂_eq_zero (algebraMap R k) p hp
#align is_alg_closed.exists_aeval_eq_zero IsAlgClosed.exists_aeval_eq_zero

theorem of_exists_root (H : ∀ p : k[X], p.Monic → Irreducible p → ∃ x, p.eval x = 0) :
    IsAlgClosed k := by
  refine ⟨fun p ↦ Or.inr ?_⟩
  intro q hq _
  have : Irreducible (q * C (leadingCoeff q)⁻¹) := by
    rw [← coe_normUnit_of_ne_zero hq.ne_zero]
    exact (associated_normalize _).irreducible hq
  obtain ⟨x, hx⟩ := H (q * C (leadingCoeff q)⁻¹) (monic_mul_leadingCoeff_inv hq.ne_zero) this
  exact degree_mul_leadingCoeff_inv q hq.ne_zero ▸ degree_eq_one_of_irreducible_of_root this hx
#align is_alg_closed.of_exists_root IsAlgClosed.of_exists_root

theorem of_ringEquiv (k' : Type u) [Field k'] (e : k ≃+* k')
    [IsAlgClosed k] : IsAlgClosed k' := by
  apply IsAlgClosed.of_exists_root
  intro p hmp hp
  have hpe : degree (p.map e.symm.toRingHom) ≠ 0 := by
    rw [degree_map]
    exact ne_of_gt (degree_pos_of_irreducible hp)
  rcases IsAlgClosed.exists_root (k := k) (p.map e.symm) hpe with ⟨x, hx⟩
  use e x
  rw [IsRoot] at hx
  apply e.symm.injective
  rw [map_zero, ← hx]
  clear hx hpe hp hmp
  induction p using Polynomial.induction_on <;> simp_all

theorem degree_eq_one_of_irreducible [IsAlgClosed k] {p : k[X]} (hp : Irreducible p) :
    p.degree = 1 :=
  degree_eq_one_of_irreducible_of_splits hp (IsAlgClosed.splits_codomain _)
#align is_alg_closed.degree_eq_one_of_irreducible IsAlgClosed.degree_eq_one_of_irreducible

theorem algebraMap_surjective_of_isIntegral {k K : Type*} [Field k] [Ring K] [IsDomain K]
    [hk : IsAlgClosed k] [Algebra k K] [Algebra.IsIntegral k K] :
    Function.Surjective (algebraMap k K) := by
  refine fun x => ⟨-(minpoly k x).coeff 0, ?_⟩
  have hq : (minpoly k x).leadingCoeff = 1 := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have h : (minpoly k x).degree = 1 := degree_eq_one_of_irreducible k (minpoly.irreducible
    (Algebra.IsIntegral.isIntegral x))
  have : aeval x (minpoly k x) = 0 := minpoly.aeval k x
  rw [eq_X_add_C_of_degree_eq_one h, hq, C_1, one_mul, aeval_add, aeval_X, aeval_C,
    add_eq_zero_iff_eq_neg] at this
  exact (RingHom.map_neg (algebraMap k K) ((minpoly k x).coeff 0)).symm ▸ this.symm
#align is_alg_closed.algebra_map_surjective_of_is_integral IsAlgClosed.algebraMap_surjective_of_isIntegral

theorem algebraMap_surjective_of_isIntegral' {k K : Type*} [Field k] [CommRing K] [IsDomain K]
    [IsAlgClosed k] (f : k →+* K) (hf : f.IsIntegral) : Function.Surjective f :=
  let _ : Algebra k K := f.toAlgebra
  have : Algebra.IsIntegral k K := ⟨hf⟩
  algebraMap_surjective_of_isIntegral
#align is_alg_closed.algebra_map_surjective_of_is_integral' IsAlgClosed.algebraMap_surjective_of_isIntegral'

/--
Deprecated: `algebraMap_surjective_of_isIntegral` is identical apart from the `IsIntegral` argument,
which can be found by instance synthesis
-/
@[deprecated algebraMap_surjective_of_isIntegral (since := "2024-05-08")]
theorem algebraMap_surjective_of_isAlgebraic {k K : Type*} [Field k] [Ring K] [IsDomain K]
    [IsAlgClosed k] [Algebra k K] [Algebra.IsAlgebraic k K] :
    Function.Surjective (algebraMap k K) :=
  algebraMap_surjective_of_isIntegral
#align is_alg_closed.algebra_map_surjective_of_is_algebraic IsAlgClosed.algebraMap_surjective_of_isAlgebraic

end IsAlgClosed

/-- If `k` is algebraically closed, `K / k` is a field extension, `L / k` is an intermediate field
which is algebraic, then `L` is equal to `k`. A corollary of
`IsAlgClosed.algebraMap_surjective_of_isAlgebraic`. -/
theorem IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic {k K : Type*} [Field k] [Field K]
    [IsAlgClosed k] [Algebra k K] (L : IntermediateField k K) [Algebra.IsAlgebraic k L] :
    L = ⊥ := bot_unique fun x hx ↦ by
  obtain ⟨y, hy⟩ := IsAlgClosed.algebraMap_surjective_of_isIntegral (k := k) (⟨x, hx⟩ : L)
  exact ⟨y, congr_arg (algebraMap L K) hy⟩

/-- Typeclass for an extension being an algebraic closure. -/
class IsAlgClosure (R : Type u) (K : Type v) [CommRing R] [Field K] [Algebra R K]
    [NoZeroSMulDivisors R K] : Prop where
  alg_closed : IsAlgClosed K
  algebraic : Algebra.IsAlgebraic R K
#align is_alg_closure IsAlgClosure

attribute [instance] IsAlgClosure.algebraic

theorem isAlgClosure_iff (K : Type v) [Field K] [Algebra k K] :
    IsAlgClosure k K ↔ IsAlgClosed K ∧ Algebra.IsAlgebraic k K :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
#align is_alg_closure_iff isAlgClosure_iff

instance (priority := 100) IsAlgClosure.normal (R K : Type*) [Field R] [Field K] [Algebra R K]
    [IsAlgClosure R K] : Normal R K where
  toIsAlgebraic := IsAlgClosure.algebraic
  splits' _ := @IsAlgClosed.splits_codomain _ _ _ (IsAlgClosure.alg_closed R) _ _ _
#align is_alg_closure.normal IsAlgClosure.normal

instance (priority := 100) IsAlgClosure.separable (R K : Type*) [Field R] [Field K] [Algebra R K]
    [IsAlgClosure R K] [CharZero R] : IsSeparable R K :=
  ⟨fun _ => (minpoly.irreducible (Algebra.IsIntegral.isIntegral _)).separable⟩
#align is_alg_closure.separable IsAlgClosure.separable

namespace IsAlgClosed

variable {K : Type u} [Field K] {L : Type v} {M : Type w} [Field L] [Algebra K L] [Field M]
  [Algebra K M] [IsAlgClosed M]

/-- If E/L/K is a tower of field extensions with E/L algebraic, and if M is an algebraically
  closed extension of K, then any embedding of L/K into M/K extends to an embedding of E/K.
  Known as the extension lemma in https://math.stackexchange.com/a/687914. -/
theorem surjective_comp_algebraMap_of_isAlgebraic {E : Type*}
    [Field E] [Algebra K E] [Algebra L E] [IsScalarTower K L E] [Algebra.IsAlgebraic L E] :
    Function.Surjective fun φ : E →ₐ[K] M ↦ φ.comp (IsScalarTower.toAlgHom K L E) :=
  fun f ↦ IntermediateField.exists_algHom_of_splits'
    (E := E) f fun s ↦ ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits_codomain _⟩

variable [Algebra.IsAlgebraic K L] (K L M)

/-- Less general version of `lift`. -/
private noncomputable irreducible_def lift_aux : L →ₐ[K] M :=
  Classical.choice <| IntermediateField.nonempty_algHom_of_adjoin_splits
    (fun x _ ↦ ⟨Algebra.IsIntegral.isIntegral x, splits_codomain (minpoly K x)⟩)
    (IntermediateField.adjoin_univ K L)

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [IsDomain S] [Algebra R S] [Algebra R M] [NoZeroSMulDivisors R S]
  [NoZeroSMulDivisors R M] [Algebra.IsAlgebraic R S]

variable {M}

private instance FractionRing.isAlgebraic :
    letI : IsDomain R := (NoZeroSMulDivisors.algebraMap_injective R S).isDomain _
    letI : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R _
    Algebra.IsAlgebraic (FractionRing R) (FractionRing S) := by
  letI : IsDomain R := (NoZeroSMulDivisors.algebraMap_injective R S).isDomain _
  letI : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R _
  have := FractionRing.isScalarTower_liftAlgebra R (FractionRing S)
  have := (IsFractionRing.isAlgebraic_iff' R S (FractionRing S)).1 inferInstance
  constructor
  intro
  exact (IsFractionRing.isAlgebraic_iff R (FractionRing R) (FractionRing S)).1
      (Algebra.IsAlgebraic.isAlgebraic _)

/-- A (random) homomorphism from an algebraic extension of R into an algebraically
  closed extension of R. -/
noncomputable irreducible_def lift : S →ₐ[R] M := by
  letI : IsDomain R := (NoZeroSMulDivisors.algebraMap_injective R S).isDomain _
  letI := FractionRing.liftAlgebra R M
  letI := FractionRing.liftAlgebra R (FractionRing S)
  have := FractionRing.isScalarTower_liftAlgebra R M
  have := FractionRing.isScalarTower_liftAlgebra R (FractionRing S)
  let f : FractionRing S →ₐ[FractionRing R] M := lift_aux (FractionRing R) (FractionRing S) M
  exact (f.restrictScalars R).comp ((Algebra.ofId S (FractionRing S)).restrictScalars R)
#align is_alg_closed.lift IsAlgClosed.lift

noncomputable instance (priority := 100) perfectRing (p : ℕ) [Fact p.Prime] [CharP k p]
    [IsAlgClosed k] : PerfectRing k p :=
  PerfectRing.ofSurjective k p fun _ => IsAlgClosed.exists_pow_nat_eq _ <| NeZero.pos p
#align is_alg_closed.perfect_ring IsAlgClosed.perfectRing

noncomputable instance (priority := 100) perfectField [IsAlgClosed k] : PerfectField k := by
  obtain _ | ⟨p, _, _⟩ := CharP.exists' k
  exacts [.ofCharZero, PerfectRing.toPerfectField k p]

/-- Algebraically closed fields are infinite since `Xⁿ⁺¹ - 1` is separable when `#K = n` -/
instance (priority := 500) {K : Type*} [Field K] [IsAlgClosed K] : Infinite K := by
  apply Infinite.of_not_fintype
  intro hfin
  set n := Fintype.card K
  set f := (X : K[X]) ^ (n + 1) - 1
  have hfsep : Separable f := separable_X_pow_sub_C 1 (by simp [n]) one_ne_zero
  apply Nat.not_succ_le_self (Fintype.card K)
  have hroot : n.succ = Fintype.card (f.rootSet K) := by
    erw [card_rootSet_eq_natDegree hfsep (IsAlgClosed.splits_domain _), natDegree_X_pow_sub_C]
  rw [hroot]
  exact Fintype.card_le_of_injective _ Subtype.coe_injective

end IsAlgClosed

namespace IsAlgClosure

-- Porting note: errors with
-- > cannot find synthesization order for instance alg_closed with type
-- > all remaining arguments have metavariables
-- attribute [local instance] IsAlgClosure.alg_closed

section

variable (R : Type u) [CommRing R] (L : Type v) (M : Type w) [Field L] [Field M]
variable [Algebra R M] [NoZeroSMulDivisors R M] [IsAlgClosure R M]
variable [Algebra R L] [NoZeroSMulDivisors R L] [IsAlgClosure R L]

/-- A (random) isomorphism between two algebraic closures of `R`. -/
noncomputable def equiv : L ≃ₐ[R] M :=
  -- Porting note (#10754): added to replace local instance above
  haveI : IsAlgClosed L := IsAlgClosure.alg_closed R
  haveI : IsAlgClosed M := IsAlgClosure.alg_closed R
  AlgEquiv.ofBijective _ (IsAlgClosure.algebraic.algHom_bijective₂
    (IsAlgClosed.lift : L →ₐ[R] M)
    (IsAlgClosed.lift : M →ₐ[R] L)).1
#align is_alg_closure.equiv IsAlgClosure.equiv

end

variable (K : Type*) (J : Type*) (R : Type u) (S : Type*) (L : Type v) (M : Type w)
  [Field K] [Field J] [CommRing R] [CommRing S] [Field L] [Field M]
  [Algebra R M] [NoZeroSMulDivisors R M] [IsAlgClosure R M] [Algebra K M] [IsAlgClosure K M]
  [Algebra S L] [NoZeroSMulDivisors S L] [IsAlgClosure S L]

section EquivOfAlgebraic

variable [Algebra R S] [Algebra R L] [IsScalarTower R S L]
variable [Algebra K J] [Algebra J L] [IsAlgClosure J L] [Algebra K L] [IsScalarTower K J L]

/-- If `J` is an algebraic extension of `K` and `L` is an algebraic closure of `J`, then it is
  also an algebraic closure of `K`. -/
theorem ofAlgebraic [hKJ : Algebra.IsAlgebraic K J] : IsAlgClosure K L :=
  ⟨IsAlgClosure.alg_closed J, hKJ.trans⟩
#align is_alg_closure.of_algebraic IsAlgClosure.ofAlgebraic

/-- A (random) isomorphism between an algebraic closure of `R` and an algebraic closure of
  an algebraic extension of `R` -/
noncomputable def equivOfAlgebraic' [Nontrivial S] [NoZeroSMulDivisors R S]
    [Algebra.IsAlgebraic R L] : L ≃ₐ[R] M := by
  letI : NoZeroSMulDivisors R L := NoZeroSMulDivisors.of_algebraMap_injective <| by
    rw [IsScalarTower.algebraMap_eq R S L]
    exact (Function.Injective.comp (NoZeroSMulDivisors.algebraMap_injective S L)
            (NoZeroSMulDivisors.algebraMap_injective R S) : _)
  letI : IsAlgClosure R L :=
    { alg_closed := IsAlgClosure.alg_closed S
      algebraic := ‹_› }
  exact IsAlgClosure.equiv _ _ _
#align is_alg_closure.equiv_of_algebraic' IsAlgClosure.equivOfAlgebraic'

/-- A (random) isomorphism between an algebraic closure of `K` and an algebraic closure
  of an algebraic extension of `K` -/
noncomputable def equivOfAlgebraic [hKJ : Algebra.IsAlgebraic K J] : L ≃ₐ[K] M :=
  have : Algebra.IsAlgebraic K L := hKJ.trans
  equivOfAlgebraic' K J _ _
#align is_alg_closure.equiv_of_algebraic IsAlgClosure.equivOfAlgebraic

end EquivOfAlgebraic

section EquivOfEquiv

variable {R S}

/-- Used in the definition of `equivOfEquiv` -/
noncomputable def equivOfEquivAux (hSR : S ≃+* R) :
    { e : L ≃+* M // e.toRingHom.comp (algebraMap S L) = (algebraMap R M).comp hSR.toRingHom } := by
  letI : Algebra R S := RingHom.toAlgebra hSR.symm.toRingHom
  letI : Algebra S R := RingHom.toAlgebra hSR.toRingHom
  letI : IsDomain R := (NoZeroSMulDivisors.algebraMap_injective R M).isDomain _
  letI : IsDomain S := (NoZeroSMulDivisors.algebraMap_injective S L).isDomain _
  letI : Algebra R L := RingHom.toAlgebra ((algebraMap S L).comp (algebraMap R S))
  haveI : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower S R L :=
    IsScalarTower.of_algebraMap_eq (by simp [RingHom.algebraMap_toAlgebra])
  haveI : NoZeroSMulDivisors R S := NoZeroSMulDivisors.of_algebraMap_injective hSR.symm.injective
  have : Algebra.IsAlgebraic R L := (IsAlgClosure.algebraic.tower_top_of_injective
    (show Function.Injective (algebraMap S R) from hSR.injective))
  refine
    ⟨equivOfAlgebraic' R S L M, ?_⟩
  ext x
  simp only [RingEquiv.toRingHom_eq_coe, Function.comp_apply, RingHom.coe_comp,
    AlgEquiv.coe_ringEquiv, RingEquiv.coe_toRingHom]
  conv_lhs => rw [← hSR.symm_apply_apply x]
  show equivOfAlgebraic' R S L M (algebraMap R L (hSR x)) = _
  rw [AlgEquiv.commutes]
#align is_alg_closure.equiv_of_equiv_aux IsAlgClosure.equivOfEquivAux

/-- Algebraic closure of isomorphic fields are isomorphic -/
noncomputable def equivOfEquiv (hSR : S ≃+* R) : L ≃+* M :=
  equivOfEquivAux L M hSR
#align is_alg_closure.equiv_of_equiv IsAlgClosure.equivOfEquiv

@[simp]
theorem equivOfEquiv_comp_algebraMap (hSR : S ≃+* R) :
    (↑(equivOfEquiv L M hSR) : L →+* M).comp (algebraMap S L) = (algebraMap R M).comp hSR :=
  (equivOfEquivAux L M hSR).2
#align is_alg_closure.equiv_of_equiv_comp_algebra_map IsAlgClosure.equivOfEquiv_comp_algebraMap

@[simp]
theorem equivOfEquiv_algebraMap (hSR : S ≃+* R) (s : S) :
    equivOfEquiv L M hSR (algebraMap S L s) = algebraMap R M (hSR s) :=
  RingHom.ext_iff.1 (equivOfEquiv_comp_algebraMap L M hSR) s
#align is_alg_closure.equiv_of_equiv_algebra_map IsAlgClosure.equivOfEquiv_algebraMap

@[simp]
theorem equivOfEquiv_symm_algebraMap (hSR : S ≃+* R) (r : R) :
    (equivOfEquiv L M hSR).symm (algebraMap R M r) = algebraMap S L (hSR.symm r) :=
  (equivOfEquiv L M hSR).injective (by simp)
#align is_alg_closure.equiv_of_equiv_symm_algebra_map IsAlgClosure.equivOfEquiv_symm_algebraMap

@[simp]
theorem equivOfEquiv_symm_comp_algebraMap (hSR : S ≃+* R) :
    ((equivOfEquiv L M hSR).symm : M →+* L).comp (algebraMap R M) =
      (algebraMap S L).comp hSR.symm :=
  RingHom.ext_iff.2 (equivOfEquiv_symm_algebraMap L M hSR)
#align is_alg_closure.equiv_of_equiv_symm_comp_algebra_map IsAlgClosure.equivOfEquiv_symm_comp_algebraMap

end EquivOfEquiv

end IsAlgClosure

section Algebra.IsAlgebraic

variable {F K : Type*} (A : Type*) [Field F] [Field K] [Field A] [Algebra F K] [Algebra F A]
  [Algebra.IsAlgebraic F K]

/-- Let `A` be an algebraically closed field and let `x ∈ K`, with `K/F` an algebraic extension
  of fields. Then the images of `x` by the `F`-algebra morphisms from `K` to `A` are exactly
  the roots in `A` of the minimal polynomial of `x` over `F`. -/
theorem Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly [IsAlgClosed A] (x : K) :
    (Set.range fun ψ : K →ₐ[F] A ↦ ψ x) = (minpoly F x).rootSet A :=
  range_eval_eq_rootSet_minpoly_of_splits A (fun _ ↦ IsAlgClosed.splits_codomain _) x
#align algebra.is_algebraic.range_eval_eq_root_set_minpoly Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly

/-- All `F`-embeddings of a field `K` into another field `A` factor through any intermediate
field of `A/F` in which the minimal polynomial of elements of `K` splits. -/
@[simps]
def IntermediateField.algHomEquivAlgHomOfSplits (L : IntermediateField F A)
    (hL : ∀ x : K, (minpoly F x).Splits (algebraMap F L)) :
    (K →ₐ[F] L) ≃ (K →ₐ[F] A) where
  toFun := L.val.comp
  invFun f := f.codRestrict _ fun x ↦
    ((Algebra.IsIntegral.isIntegral x).map f).mem_intermediateField_of_minpoly_splits <| by
      rw [minpoly.algHom_eq f f.injective]; exact hL x
  left_inv _ := rfl
  right_inv _ := by rfl

theorem IntermediateField.algHomEquivAlgHomOfSplits_apply_apply (L : IntermediateField F A)
    (hL : ∀ x : K, (minpoly F x).Splits (algebraMap F L)) (f : K →ₐ[F] L) (x : K) :
    algHomEquivAlgHomOfSplits A L hL f x = algebraMap L A (f x) := rfl

/-- All `F`-embeddings of a field `K` into another field `A` factor through any subextension
of `A/F` in which the minimal polynomial of elements of `K` splits. -/
noncomputable def Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits (L : Type*) [Field L]
    [Algebra F L] [Algebra L A] [IsScalarTower F L A]
    (hL : ∀ x : K, (minpoly F x).Splits (algebraMap F L)) :
    (K →ₐ[F] L) ≃ (K →ₐ[F] A) :=
  (AlgEquiv.refl.arrowCongr (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L A))).trans <|
    IntermediateField.algHomEquivAlgHomOfSplits A (IsScalarTower.toAlgHom F L A).fieldRange
    fun x ↦ splits_of_algHom (hL x) (AlgHom.rangeRestrict _)

theorem Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits_apply_apply (L : Type*) [Field L]
    [Algebra F L] [Algebra L A] [IsScalarTower F L A]
    (hL : ∀ x : K, (minpoly F x).Splits (algebraMap F L)) (f : K →ₐ[F] L) (x : K) :
    Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits A L hL f x = algebraMap L A (f x) := rfl

end Algebra.IsAlgebraic
