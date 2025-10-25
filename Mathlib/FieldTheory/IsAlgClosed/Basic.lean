/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.FieldTheory.Extension
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Localization.Integral

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

## Main results

- `IsAlgClosure.of_splits`: if `K / k` is algebraic, and every monic irreducible polynomial over
  `k` splits in `K`, then `K` is algebraically closed (in fact an algebraic closure of `k`).
  For the stronger fact that only requires every such polynomial has a root in `K`,
  see `IsAlgClosure.of_exist_roots`.

  Reference: <https://kconrad.math.uconn.edu/blurbs/galoistheory/algclosure.pdf>, Theorem 2

-/

universe u v w

open Polynomial

variable (k : Type u) [Field k]

/-- Typeclass for algebraically closed fields.

To show `Polynomial.Splits p f` for an arbitrary ring homomorphism `f`,
see `IsAlgClosed.splits_codomain` and `IsAlgClosed.splits_domain`.
-/
@[stacks 09GR "The definition of `IsAlgClosed` in mathlib is 09GR (4)"]
class IsAlgClosed : Prop where
  splits : ∀ p : k[X], p.Splits <| RingHom.id k

/-- Every polynomial splits in the field extension `f : K →+* k` if `k` is algebraically closed.

See also `IsAlgClosed.splits_domain` for the case where `K` is algebraically closed.
-/
theorem IsAlgClosed.splits_codomain {k K : Type*} [Field k] [IsAlgClosed k] [CommRing K]
    {f : K →+* k} (p : K[X]) : p.Splits f := by
  convert IsAlgClosed.splits (p.map f); simp [splits_map_iff]

/-- Every polynomial splits in the field extension `f : K →+* k` if `K` is algebraically closed.

See also `IsAlgClosed.splits_codomain` for the case where `k` is algebraically closed.
-/
theorem IsAlgClosed.splits_domain {k K : Type*} [Field k] [IsAlgClosed k] [Field K] {f : k →+* K}
    (p : k[X]) : p.Splits f :=
  Polynomial.splits_of_splits_id _ <| IsAlgClosed.splits _

namespace IsAlgClosed

variable {k}

/--
If `k` is algebraically closed, then every nonconstant polynomial has a root.
-/
@[stacks 09GR "(4) ⟹ (3)"]
theorem exists_root [IsAlgClosed k] (p : k[X]) (hp : p.degree ≠ 0) : ∃ x, IsRoot p x :=
  exists_root_of_splits _ (IsAlgClosed.splits p) hp

theorem exists_pow_nat_eq [IsAlgClosed k] (x : k) {n : ℕ} (hn : 0 < n) : ∃ z, z ^ n = x := by
  have : degree (X ^ n - C x) ≠ 0 := by
    rw [degree_X_pow_sub_C hn x]
    exact ne_of_gt (WithBot.coe_lt_coe.2 hn)
  obtain ⟨z, hz⟩ := exists_root (X ^ n - C x) this
  use z
  simp only [eval_C, eval_X, eval_pow, eval_sub, IsRoot.def] at hz
  exact sub_eq_zero.1 hz

theorem exists_eq_mul_self [IsAlgClosed k] (x : k) : ∃ z, x = z * z := by
  rcases exists_pow_nat_eq x zero_lt_two with ⟨z, rfl⟩
  exact ⟨z, sq z⟩

theorem roots_eq_zero_iff [IsAlgClosed k] {p : k[X]} :
    p.roots = 0 ↔ p = Polynomial.C (p.coeff 0) := by
  refine ⟨fun h => ?_, fun hp => by rw [hp, roots_C]⟩
  rcases le_or_gt (degree p) 0 with hd | hd
  · exact eq_C_of_degree_le_zero hd
  · obtain ⟨z, hz⟩ := IsAlgClosed.exists_root p hd.ne'
    rw [← mem_roots (ne_zero_of_degree_gt hd), h] at hz
    simp at hz

theorem exists_eval₂_eq_zero_of_injective {R : Type*} [Semiring R] [IsAlgClosed k] (f : R →+* k)
    (hf : Function.Injective f) (p : R[X]) (hp : p.degree ≠ 0) : ∃ x, p.eval₂ f x = 0 :=
  let ⟨x, hx⟩ := exists_root (p.map f) (by rwa [degree_map_eq_of_injective hf])
  ⟨x, by rwa [eval₂_eq_eval_map, ← IsRoot]⟩

theorem exists_eval₂_eq_zero {R : Type*} [DivisionRing R] [IsAlgClosed k] (f : R →+* k) (p : R[X])
    (hp : p.degree ≠ 0) : ∃ x, p.eval₂ f x = 0 :=
  exists_eval₂_eq_zero_of_injective f f.injective p hp

variable (k)

theorem exists_aeval_eq_zero_of_injective {R : Type*} [CommSemiring R] [IsAlgClosed k] [Algebra R k]
    (hinj : Function.Injective (algebraMap R k)) (p : R[X]) (hp : p.degree ≠ 0) :
    ∃ x : k, aeval x p = 0 :=
  exists_eval₂_eq_zero_of_injective (algebraMap R k) hinj p hp

theorem exists_aeval_eq_zero {R : Type*} [Field R] [IsAlgClosed k] [Algebra R k] (p : R[X])
    (hp : p.degree ≠ 0) : ∃ x : k, aeval x p = 0 :=
  exists_eval₂_eq_zero (algebraMap R k) p hp


/--
If every nonconstant polynomial over `k` has a root, then `k` is algebraically closed.
-/
@[stacks 09GR "(3) ⟹ (4)"]
theorem of_exists_root (H : ∀ p : k[X], p.Monic → Irreducible p → ∃ x, p.eval x = 0) :
    IsAlgClosed k := by
  refine ⟨fun p ↦ factors_iff_splits.mpr <| Or.inr ?_⟩
  intro q hq _
  have : Irreducible (q * C (leadingCoeff q)⁻¹) := by
    classical
    rw [← coe_normUnit_of_ne_zero hq.ne_zero]
    exact (associated_normalize _).irreducible hq
  obtain ⟨x, hx⟩ := H (q * C (leadingCoeff q)⁻¹) (monic_mul_leadingCoeff_inv hq.ne_zero) this
  exact degree_mul_leadingCoeff_inv q hq.ne_zero ▸ degree_eq_one_of_irreducible_of_root this hx

theorem of_ringEquiv (k' : Type u) [Field k'] (e : k ≃+* k')
    [IsAlgClosed k] : IsAlgClosed k' := by
  apply IsAlgClosed.of_exists_root
  intro p hmp hp
  have hpe : degree (p.map e.symm.toRingHom) ≠ 0 := by
    rw [degree_map]
    exact ne_of_gt (degree_pos_of_irreducible hp)
  rcases IsAlgClosed.exists_root (k := k) (p.map e.symm.toRingHom) hpe with ⟨x, hx⟩
  use e x
  rw [IsRoot] at hx
  apply e.symm.injective
  rw [map_zero, ← hx]
  clear hx hpe hp hmp
  induction p using Polynomial.induction_on <;> simp_all

/--
If `k` is algebraically closed, then every irreducible polynomial over `k` is linear.
-/
@[stacks 09GR "(4) ⟹ (2)"]
theorem degree_eq_one_of_irreducible [IsAlgClosed k] {p : k[X]} (hp : Irreducible p) :
    p.degree = 1 :=
  degree_eq_one_of_irreducible_of_splits hp (IsAlgClosed.splits_codomain _)

theorem algebraMap_bijective_of_isIntegral {k K : Type*} [Field k] [Ring K] [IsDomain K]
    [hk : IsAlgClosed k] [Algebra k K] [Algebra.IsIntegral k K] :
    Function.Bijective (algebraMap k K) := by
  refine ⟨RingHom.injective _, fun x ↦ ⟨-(minpoly k x).coeff 0, ?_⟩⟩
  have hq : (minpoly k x).leadingCoeff = 1 := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have h : (minpoly k x).degree = 1 := degree_eq_one_of_irreducible k (minpoly.irreducible
    (Algebra.IsIntegral.isIntegral x))
  have : aeval x (minpoly k x) = 0 := minpoly.aeval k x
  rw [eq_X_add_C_of_degree_eq_one h, hq, C_1, one_mul, aeval_add, aeval_X, aeval_C,
    add_eq_zero_iff_eq_neg] at this
  exact (RingHom.map_neg (algebraMap k K) ((minpoly k x).coeff 0)).symm ▸ this.symm

theorem ringHom_bijective_of_isIntegral {k K : Type*} [Field k] [CommRing K] [IsDomain K]
    [IsAlgClosed k] (f : k →+* K) (hf : f.IsIntegral) : Function.Bijective f :=
  let _ : Algebra k K := f.toAlgebra
  have : Algebra.IsIntegral k K := ⟨hf⟩
  algebraMap_bijective_of_isIntegral

end IsAlgClosed

/-- If `k` is algebraically closed, `K / k` is a field extension, `L / k` is an intermediate field
which is algebraic, then `L` is equal to `k`. A corollary of
`IsAlgClosed.algebraMap_surjective_of_isAlgebraic`. -/
@[stacks 09GQ "The result is the definition of algebraically closedness in Stacks Project. \
This statement is 09GR (4) ⟹ (1)."]
theorem IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic {k K : Type*} [Field k] [Field K]
    [IsAlgClosed k] [Algebra k K] (L : IntermediateField k K) [Algebra.IsAlgebraic k L] :
    L = ⊥ := bot_unique fun x hx ↦ by
  obtain ⟨y, hy⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2 (⟨x, hx⟩ : L)
  exact ⟨y, congr_arg (algebraMap L K) hy⟩

lemma Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (K : Type v) [Field K] [IsAlgClosed K]
    [Algebra k K] (p q : k[X]) : IsCoprime p q ↔ ∀ a : K, aeval a p ≠ 0 ∨ aeval a q ≠ 0 := by
  refine ⟨fun h => aeval_ne_zero_of_isCoprime h, fun h => isCoprime_of_dvd _ _ ?_ fun x hu h0 => ?_⟩
  · replace h := h 0
    contrapose! h
    rw [h.left, h.right, map_zero, and_self]
  · rintro ⟨_, rfl⟩ ⟨_, rfl⟩
    obtain ⟨a, ha : _ = _⟩ := IsAlgClosed.exists_root (x.map <| algebraMap k K) <| by
      simpa only [degree_map] using (ne_of_lt <| degree_pos_of_ne_zero_of_nonunit h0 hu).symm
    exact not_and_or.mpr (h a) (by simp_rw [map_mul, ← eval_map_algebraMap, ha, zero_mul, true_and])

/-- Typeclass for an extension being an algebraic closure. -/
@[stacks 09GS]
class IsAlgClosure (R : Type u) (K : Type v) [CommRing R] [Field K] [Algebra R K]
    [NoZeroSMulDivisors R K] : Prop where
  isAlgClosed : IsAlgClosed K
  isAlgebraic : Algebra.IsAlgebraic R K

attribute [instance] IsAlgClosure.isAlgebraic

theorem isAlgClosure_iff (K : Type v) [Field K] [Algebra k K] :
    IsAlgClosure k K ↔ IsAlgClosed K ∧ Algebra.IsAlgebraic k K :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

instance (priority := 100) IsAlgClosure.normal (R K : Type*) [Field R] [Field K] [Algebra R K]
    [IsAlgClosure R K] : Normal R K where
  toIsAlgebraic := IsAlgClosure.isAlgebraic
  splits' _ := @IsAlgClosed.splits_codomain _ _ _ (IsAlgClosure.isAlgClosed R) _ _ _

instance (priority := 100) IsAlgClosure.separable (R K : Type*) [Field R] [Field K] [Algebra R K]
    [IsAlgClosure R K] [CharZero R] : Algebra.IsSeparable R K :=
  ⟨fun _ => (minpoly.irreducible (Algebra.IsIntegral.isIntegral _)).separable⟩

instance IsAlgClosed.instIsAlgClosure (F : Type*) [Field F] [IsAlgClosed F] : IsAlgClosure F F where
  isAlgClosed := ‹_›
  isAlgebraic := .of_finite F F

theorem IsAlgClosure.of_splits {R K} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [Algebra.IsIntegral R K] [NoZeroSMulDivisors R K]
    (h : ∀ p : R[X], p.Monic → Irreducible p → p.Splits (algebraMap R K)) : IsAlgClosure R K where
  isAlgebraic := inferInstance
  isAlgClosed := .of_exists_root _ fun _p _ p_irred ↦
    have ⟨g, monic, irred, dvd⟩ := p_irred.exists_dvd_monic_irreducible_of_isIntegral (K := R)
    exists_root_of_splits _ (splits_of_splits_of_dvd _ (map_monic_ne_zero monic)
      ((splits_id_iff_splits _).mpr <| h g monic irred) dvd) <|
        degree_ne_of_natDegree_ne p_irred.natDegree_pos.ne'

namespace IsAlgClosed

variable {K : Type u} [Field K] {L : Type v} {M : Type w} [Field L] [Algebra K L] [Field M]
  [Algebra K M] [IsAlgClosed M]

/-- If E/L/K is a tower of field extensions with E/L algebraic, and if M is an algebraically
  closed extension of K, then any embedding of L/K into M/K extends to an embedding of E/K.
  Known as the extension lemma in https://math.stackexchange.com/a/687914. -/
theorem surjective_restrictDomain_of_isAlgebraic {E : Type*}
    [Field E] [Algebra K E] [Algebra L E] [IsScalarTower K L E] [Algebra.IsAlgebraic L E] :
    Function.Surjective fun φ : E →ₐ[K] M ↦ φ.restrictDomain L :=
  fun f ↦ IntermediateField.exists_algHom_of_splits'
    (E := E) f fun s ↦ ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits_codomain _⟩

variable [Algebra.IsAlgebraic K L] (K L M)

/-- Less general version of `lift`. -/
private noncomputable irreducible_def liftAux : L →ₐ[K] M :=
  Classical.choice <| IntermediateField.nonempty_algHom_of_adjoin_splits
    (fun x _ ↦ ⟨Algebra.IsIntegral.isIntegral x, splits_codomain (minpoly K x)⟩)
    (IntermediateField.adjoin_univ K L)

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [IsDomain S] [Algebra R S] [Algebra R M] [NoZeroSMulDivisors R S]
  [NoZeroSMulDivisors R M] [Algebra.IsAlgebraic R S]

variable {M}

private instance FractionRing.isAlgebraic :
    letI : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain _
    letI : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R _
    Algebra.IsAlgebraic (FractionRing R) (FractionRing S) := by
  letI : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain _
  letI : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R _
  have := FractionRing.isScalarTower_liftAlgebra R (FractionRing S)
  have := (IsFractionRing.isAlgebraic_iff' R S (FractionRing S)).1 inferInstance
  constructor
  intro
  exact (IsFractionRing.isAlgebraic_iff R (FractionRing R) (FractionRing S)).1
      (Algebra.IsAlgebraic.isAlgebraic _)

/-- A (random) homomorphism from an algebraic extension of R into an algebraically
  closed extension of R. -/
@[stacks 09GU]
noncomputable irreducible_def lift : S →ₐ[R] M := by
  letI : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain _
  letI := FractionRing.liftAlgebra R M
  letI := FractionRing.liftAlgebra R (FractionRing S)
  have := FractionRing.isScalarTower_liftAlgebra R M
  have := FractionRing.isScalarTower_liftAlgebra R (FractionRing S)
  let f : FractionRing S →ₐ[FractionRing R] M := liftAux (FractionRing R) (FractionRing S) M
  exact (f.restrictScalars R).comp ((Algebra.ofId S (FractionRing S)).restrictScalars R)

theorem nonempty_algEquiv_or_of_finrank_eq_two {F F' : Type*} (E : Type*)
    [Field F] [Field F'] [Field E] [Algebra F F'] [Algebra F E]
    [Algebra.IsAlgebraic F E] [IsAlgClosed F'] (h : Module.finrank F F' = 2) :
    Nonempty (E ≃ₐ[F] F) ∨ Nonempty (E ≃ₐ[F] F') := by
  have emb : E →ₐ[F] F' := lift
  have e := AlgEquiv.ofInjectiveField emb
  have := Subalgebra.isSimpleOrder_of_finrank h
  obtain h | h := IsSimpleOrder.eq_bot_or_eq_top emb.range <;> rw [h] at e
  exacts [.inl ⟨e.trans <| Algebra.botEquiv ..⟩, .inr ⟨e.trans Subalgebra.topEquiv⟩]

noncomputable instance (priority := 100) perfectRing (p : ℕ) [Fact p.Prime] [CharP k p]
    [IsAlgClosed k] : PerfectRing k p :=
  PerfectRing.ofSurjective k p fun _ => IsAlgClosed.exists_pow_nat_eq _ <| NeZero.pos p

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
    rw [card_rootSet_eq_natDegree hfsep (IsAlgClosed.splits_domain _)]
    unfold f
    rw [← C_1, natDegree_X_pow_sub_C]
  rw [hroot]
  exact Fintype.card_le_of_injective _ Subtype.coe_injective

end IsAlgClosed

namespace IsAlgClosure

section

variable (R : Type u) [CommRing R] (L : Type v) (M : Type w) [Field L] [Field M]
variable [Algebra R M] [NoZeroSMulDivisors R M] [IsAlgClosure R M]
variable [Algebra R L] [NoZeroSMulDivisors R L] [IsAlgClosure R L]

attribute [local instance] IsAlgClosure.isAlgClosed in
/-- A (random) isomorphism between two algebraic closures of `R`. -/
@[stacks 09GV]
noncomputable def equiv : L ≃ₐ[R] M :=
  AlgEquiv.ofBijective _ (IsAlgClosure.isAlgebraic.algHom_bijective₂
    (IsAlgClosed.lift : L →ₐ[R] M)
    (IsAlgClosed.lift : M →ₐ[R] L)).1

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
theorem ofAlgebraic [Algebra.IsAlgebraic K J] : IsAlgClosure K L :=
  ⟨IsAlgClosure.isAlgClosed J, .trans K J L⟩

/-- A (random) isomorphism between an algebraic closure of `R` and an algebraic closure of
  an algebraic extension of `R` -/
noncomputable def equivOfAlgebraic' [Nontrivial S] [NoZeroSMulDivisors R S]
    [Algebra.IsAlgebraic R L] : L ≃ₐ[R] M := by
  have : NoZeroSMulDivisors R L := NoZeroSMulDivisors.trans_faithfulSMul R S L
  have : IsAlgClosure R L :=
    { isAlgClosed := IsAlgClosure.isAlgClosed S
      isAlgebraic := ‹_› }
  exact IsAlgClosure.equiv _ _ _

/-- A (random) isomorphism between an algebraic closure of `K` and an algebraic closure
  of an algebraic extension of `K` -/
noncomputable def equivOfAlgebraic [Algebra.IsAlgebraic K J] : L ≃ₐ[K] M :=
  have := Algebra.IsAlgebraic.trans K J L
  equivOfAlgebraic' K J _ _

end EquivOfAlgebraic

section EquivOfEquiv

variable {R S}

/-- Used in the definition of `equivOfEquiv` -/
noncomputable def equivOfEquivAux (hSR : S ≃+* R) :
    { e : L ≃+* M // e.toRingHom.comp (algebraMap S L) = (algebraMap R M).comp hSR.toRingHom } := by
  letI : Algebra R S := RingHom.toAlgebra hSR.symm.toRingHom
  letI : Algebra S R := RingHom.toAlgebra hSR.toRingHom
  have : IsDomain S := (FaithfulSMul.algebraMap_injective S L).isDomain _
  letI : Algebra R L := RingHom.toAlgebra ((algebraMap S L).comp (algebraMap R S))
  haveI : IsScalarTower R S L := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower S R L := .of_algebraMap_eq (by simp [RingHom.algebraMap_toAlgebra])
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hSR.symm.injective
  have : Algebra.IsAlgebraic R L := (IsAlgClosure.isAlgebraic.extendScalars
    (show Function.Injective (algebraMap S R) from hSR.injective))
  refine ⟨equivOfAlgebraic' R S L M, ?_⟩
  ext x
  simp only [RingEquiv.toRingHom_eq_coe, Function.comp_apply, RingHom.coe_comp,
    AlgEquiv.coe_ringEquiv, RingEquiv.coe_toRingHom]
  conv_lhs => rw [← hSR.symm_apply_apply x]
  change equivOfAlgebraic' R S L M (algebraMap R L (hSR x)) = _
  rw [AlgEquiv.commutes]

/-- Algebraic closure of isomorphic fields are isomorphic -/
noncomputable def equivOfEquiv (hSR : S ≃+* R) : L ≃+* M :=
  equivOfEquivAux L M hSR

@[simp]
theorem equivOfEquiv_comp_algebraMap (hSR : S ≃+* R) :
    (↑(equivOfEquiv L M hSR) : L →+* M).comp (algebraMap S L) = (algebraMap R M).comp hSR :=
  (equivOfEquivAux L M hSR).2

@[simp]
theorem equivOfEquiv_algebraMap (hSR : S ≃+* R) (s : S) :
    equivOfEquiv L M hSR (algebraMap S L s) = algebraMap R M (hSR s) :=
  RingHom.ext_iff.1 (equivOfEquiv_comp_algebraMap L M hSR) s

@[simp]
theorem equivOfEquiv_symm_algebraMap (hSR : S ≃+* R) (r : R) :
    (equivOfEquiv L M hSR).symm (algebraMap R M r) = algebraMap S L (hSR.symm r) :=
  (equivOfEquiv L M hSR).injective (by simp)

@[simp]
theorem equivOfEquiv_symm_comp_algebraMap (hSR : S ≃+* R) :
    ((equivOfEquiv L M hSR).symm : M →+* L).comp (algebraMap R M) =
      (algebraMap S L).comp hSR.symm :=
  RingHom.ext_iff.2 (equivOfEquiv_symm_algebraMap L M hSR)

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

/-- Over an algebraically closed field of characteristic zero a necessary and sufficient condition
for the set of roots of a nonzero polynomial `f` to be a subset of the set of roots of `g` is that
`f` divides `f.derivative * g`. Over an integral domain, this is a sufficient but not necessary
condition. See `isRoot_of_isRoot_of_dvd_derivative_mul` -/
theorem Polynomial.isRoot_of_isRoot_iff_dvd_derivative_mul {K : Type*} [Field K]
    [IsAlgClosed K] [CharZero K] {f g : K[X]} (hf0 : f ≠ 0) :
    (∀ x, IsRoot f x → IsRoot g x) ↔ f ∣ f.derivative * g := by
  refine ⟨?_, isRoot_of_isRoot_of_dvd_derivative_mul hf0⟩
  by_cases hg0 : g = 0
  · simp [hg0]
  by_cases hdf0 : derivative f = 0
  · rw [eq_C_of_derivative_eq_zero hdf0]
    simp only [derivative_C, zero_mul, dvd_zero, implies_true]
  have hdg :  f.derivative * g ≠ 0 := mul_ne_zero hdf0 hg0
  classical rw [Splits.dvd_iff_roots_le_roots (IsAlgClosed.splits f) hf0 hdg, Multiset.le_iff_count]
  simp only [count_roots, rootMultiplicity_mul hdg]
  refine forall_imp fun a => ?_
  by_cases haf : f.eval a = 0
  · have h0 : 0 < f.rootMultiplicity a := (rootMultiplicity_pos hf0).2 haf
    rw [derivative_rootMultiplicity_of_root haf]
    intro h
    calc rootMultiplicity a f
        = rootMultiplicity a f - 1 + 1 := (Nat.sub_add_cancel (Nat.succ_le_iff.1 h0)).symm
      _ ≤ rootMultiplicity a f - 1 + rootMultiplicity a g := add_le_add le_rfl (Nat.succ_le_iff.1
        ((rootMultiplicity_pos hg0).2 (h haf)))
  · simp [haf, rootMultiplicity_eq_zero haf]
