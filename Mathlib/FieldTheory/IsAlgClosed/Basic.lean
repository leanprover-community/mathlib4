/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module field_theory.is_alg_closed.basic
! leanprover-community/mathlib commit 00f91228655eecdcd3ac97a7fd8dbcb139fe990a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.FieldTheory.Normal
import Mathbin.FieldTheory.PerfectClosure
import Mathbin.RingTheory.Localization.Integral

/-!
# Algebraically Closed Field

In this file we define the typeclass for algebraically closed fields and algebraic closures,
and prove some of their properties.

## Main Definitions

- `is_alg_closed k` is the typeclass saying `k` is an algebraically closed field, i.e. every
polynomial in `k` splits.

- `is_alg_closure R K` is the typeclass saying `K` is an algebraic closure of `R`, where `R` is a
  commutative ring. This means that the map from `R` to `K` is injective, and `K` is
  algebraically closed and algebraic over `R`

- `is_alg_closed.lift` is a map from an algebraic extension `L` of `R`, into any algebraically
  closed extension of `R`.

- `is_alg_closure.equiv` is a proof that any two algebraic closures of the
  same field are isomorphic.

## Tags

algebraic closure, algebraically closed

-/


universe u v w

open scoped Classical BigOperators Polynomial

open Polynomial

variable (k : Type u) [Field k]

/-- Typeclass for algebraically closed fields.

To show `polynomial.splits p f` for an arbitrary ring homomorphism `f`,
see `is_alg_closed.splits_codomain` and `is_alg_closed.splits_domain`.
-/
class IsAlgClosed : Prop where
  Splits : ∀ p : k[X], p.Splits <| RingHom.id k
#align is_alg_closed IsAlgClosed

/-- Every polynomial splits in the field extension `f : K →+* k` if `k` is algebraically closed.

See also `is_alg_closed.splits_domain` for the case where `K` is algebraically closed.
-/
theorem IsAlgClosed.splits_codomain {k K : Type _} [Field k] [IsAlgClosed k] [Field K] {f : K →+* k}
    (p : K[X]) : p.Splits f := by convert IsAlgClosed.splits (p.map f); simp [splits_map_iff]
#align is_alg_closed.splits_codomain IsAlgClosed.splits_codomain

/-- Every polynomial splits in the field extension `f : K →+* k` if `K` is algebraically closed.

See also `is_alg_closed.splits_codomain` for the case where `k` is algebraically closed.
-/
theorem IsAlgClosed.splits_domain {k K : Type _} [Field k] [IsAlgClosed k] [Field K] {f : k →+* K}
    (p : k[X]) : p.Splits f :=
  Polynomial.splits_of_splits_id _ <| IsAlgClosed.splits _
#align is_alg_closed.splits_domain IsAlgClosed.splits_domain

namespace IsAlgClosed

variable {k}

theorem exists_root [IsAlgClosed k] (p : k[X]) (hp : p.degree ≠ 0) : ∃ x, IsRoot p x :=
  exists_root_of_splits _ (IsAlgClosed.splits p) hp
#align is_alg_closed.exists_root IsAlgClosed.exists_root

theorem exists_pow_nat_eq [IsAlgClosed k] (x : k) {n : ℕ} (hn : 0 < n) : ∃ z, z ^ n = x :=
  by
  rcases exists_root (X ^ n - C x) _ with ⟨z, hz⟩; swap
  · rw [degree_X_pow_sub_C hn x]
    exact ne_of_gt (WithBot.coe_lt_coe.2 hn)
  use z
  simp only [eval_C, eval_X, eval_pow, eval_sub, is_root.def] at hz 
  exact sub_eq_zero.1 hz
#align is_alg_closed.exists_pow_nat_eq IsAlgClosed.exists_pow_nat_eq

theorem exists_eq_mul_self [IsAlgClosed k] (x : k) : ∃ z, x = z * z :=
  by
  rcases exists_pow_nat_eq x zero_lt_two with ⟨z, rfl⟩
  exact ⟨z, sq z⟩
#align is_alg_closed.exists_eq_mul_self IsAlgClosed.exists_eq_mul_self

theorem roots_eq_zero_iff [IsAlgClosed k] {p : k[X]} : p.roots = 0 ↔ p = Polynomial.C (p.coeff 0) :=
  by
  refine' ⟨fun h => _, fun hp => by rw [hp, roots_C]⟩
  cases' le_or_lt (degree p) 0 with hd hd
  · exact eq_C_of_degree_le_zero hd
  · obtain ⟨z, hz⟩ := IsAlgClosed.exists_root p hd.ne'
    rw [← mem_roots (ne_zero_of_degree_gt hd), h] at hz 
    simpa using hz
#align is_alg_closed.roots_eq_zero_iff IsAlgClosed.roots_eq_zero_iff

theorem exists_eval₂_eq_zero_of_injective {R : Type _} [Ring R] [IsAlgClosed k] (f : R →+* k)
    (hf : Function.Injective f) (p : R[X]) (hp : p.degree ≠ 0) : ∃ x, p.eval₂ f x = 0 :=
  let ⟨x, hx⟩ := exists_root (p.map f) (by rwa [degree_map_eq_of_injective hf])
  ⟨x, by rwa [eval₂_eq_eval_map, ← is_root]⟩
#align is_alg_closed.exists_eval₂_eq_zero_of_injective IsAlgClosed.exists_eval₂_eq_zero_of_injective

theorem exists_eval₂_eq_zero {R : Type _} [Field R] [IsAlgClosed k] (f : R →+* k) (p : R[X])
    (hp : p.degree ≠ 0) : ∃ x, p.eval₂ f x = 0 :=
  exists_eval₂_eq_zero_of_injective f f.Injective p hp
#align is_alg_closed.exists_eval₂_eq_zero IsAlgClosed.exists_eval₂_eq_zero

variable (k)

theorem exists_aeval_eq_zero_of_injective {R : Type _} [CommRing R] [IsAlgClosed k] [Algebra R k]
    (hinj : Function.Injective (algebraMap R k)) (p : R[X]) (hp : p.degree ≠ 0) :
    ∃ x : k, aeval x p = 0 :=
  exists_eval₂_eq_zero_of_injective (algebraMap R k) hinj p hp
#align is_alg_closed.exists_aeval_eq_zero_of_injective IsAlgClosed.exists_aeval_eq_zero_of_injective

theorem exists_aeval_eq_zero {R : Type _} [Field R] [IsAlgClosed k] [Algebra R k] (p : R[X])
    (hp : p.degree ≠ 0) : ∃ x : k, aeval x p = 0 :=
  exists_eval₂_eq_zero (algebraMap R k) p hp
#align is_alg_closed.exists_aeval_eq_zero IsAlgClosed.exists_aeval_eq_zero

theorem of_exists_root (H : ∀ p : k[X], p.Monic → Irreducible p → ∃ x, p.eval x = 0) :
    IsAlgClosed k :=
  ⟨fun p =>
    Or.inr fun q hq hqp =>
      have : Irreducible (q * C (leadingCoeff q)⁻¹) :=
        by
        rw [← coe_norm_unit_of_ne_zero hq.ne_zero]
        exact (associated_normalize _).Irreducible hq
      let ⟨x, hx⟩ := H (q * C (leadingCoeff q)⁻¹) (monic_mul_leadingCoeff_inv hq.NeZero) this
      degree_mul_leadingCoeff_inv q hq.NeZero ▸ degree_eq_one_of_irreducible_of_root this hx⟩
#align is_alg_closed.of_exists_root IsAlgClosed.of_exists_root

theorem degree_eq_one_of_irreducible [IsAlgClosed k] {p : k[X]} (hp : Irreducible p) :
    p.degree = 1 :=
  degree_eq_one_of_irreducible_of_splits hp (IsAlgClosed.splits_codomain _)
#align is_alg_closed.degree_eq_one_of_irreducible IsAlgClosed.degree_eq_one_of_irreducible

theorem algebraMap_surjective_of_isIntegral {k K : Type _} [Field k] [Ring K] [IsDomain K]
    [hk : IsAlgClosed k] [Algebra k K] (hf : Algebra.IsIntegral k K) :
    Function.Surjective (algebraMap k K) :=
  by
  refine' fun x => ⟨-(minpoly k x).coeff 0, _⟩
  have hq : (minpoly k x).leadingCoeff = 1 := minpoly.monic (hf x)
  have h : (minpoly k x).degree = 1 := degree_eq_one_of_irreducible k (minpoly.irreducible (hf x))
  have : aeval x (minpoly k x) = 0 := minpoly.aeval k x
  rw [eq_X_add_C_of_degree_eq_one h, hq, C_1, one_mul, aeval_add, aeval_X, aeval_C,
    add_eq_zero_iff_eq_neg] at this 
  exact (RingHom.map_neg (algebraMap k K) ((minpoly k x).coeff 0)).symm ▸ this.symm
#align is_alg_closed.algebra_map_surjective_of_is_integral IsAlgClosed.algebraMap_surjective_of_isIntegral

theorem algebra_map_surjective_of_is_integral' {k K : Type _} [Field k] [CommRing K] [IsDomain K]
    [hk : IsAlgClosed k] (f : k →+* K) (hf : f.IsIntegral) : Function.Surjective f :=
  @algebraMap_surjective_of_isIntegral k K _ _ _ _ f.toAlgebra hf
#align is_alg_closed.algebra_map_surjective_of_is_integral' IsAlgClosed.algebra_map_surjective_of_is_integral'

theorem algebraMap_surjective_of_isAlgebraic {k K : Type _} [Field k] [Ring K] [IsDomain K]
    [hk : IsAlgClosed k] [Algebra k K] (hf : Algebra.IsAlgebraic k K) :
    Function.Surjective (algebraMap k K) :=
  algebraMap_surjective_of_isIntegral (Algebra.isAlgebraic_iff_isIntegral.mp hf)
#align is_alg_closed.algebra_map_surjective_of_is_algebraic IsAlgClosed.algebraMap_surjective_of_isAlgebraic

end IsAlgClosed

/-- Typeclass for an extension being an algebraic closure. -/
class IsAlgClosure (R : Type u) (K : Type v) [CommRing R] [Field K] [Algebra R K]
    [NoZeroSMulDivisors R K] : Prop where
  alg_closed : IsAlgClosed K
  algebraic : Algebra.IsAlgebraic R K
#align is_alg_closure IsAlgClosure

theorem isAlgClosure_iff (K : Type v) [Field K] [Algebra k K] :
    IsAlgClosure k K ↔ IsAlgClosed K ∧ Algebra.IsAlgebraic k K :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
#align is_alg_closure_iff isAlgClosure_iff

instance (priority := 100) IsAlgClosure.normal (R K : Type _) [Field R] [Field K] [Algebra R K]
    [IsAlgClosure R K] : Normal R K :=
  ⟨IsAlgClosure.algebraic, fun _ =>
    @IsAlgClosed.splits_codomain _ _ _ (IsAlgClosure.alg_closed R) _ _ _⟩
#align is_alg_closure.normal IsAlgClosure.normal

instance (priority := 100) IsAlgClosure.separable (R K : Type _) [Field R] [Field K] [Algebra R K]
    [IsAlgClosure R K] [CharZero R] : IsSeparable R K :=
  ⟨fun _ => isAlgebraic_iff_isIntegral.mp (IsAlgClosure.algebraic _), fun _ =>
    (minpoly.irreducible (isAlgebraic_iff_isIntegral.mp (IsAlgClosure.algebraic _))).Separable⟩
#align is_alg_closure.separable IsAlgClosure.separable

namespace lift

/- In this section, the homomorphism from any algebraic extension into an algebraically
  closed extension is proven to exist. The assumption that M is algebraically closed could probably
  easily be switched to an assumption that M contains all the roots of polynomials in K -/
variable {K : Type u} {L : Type v} {M : Type w} [Field K] [Field L] [Algebra K L] [Field M]
  [Algebra K M] [IsAlgClosed M] (hL : Algebra.IsAlgebraic K L)

variable (K L M)

include hL

open Subalgebra AlgHom Function

/-- This structure is used to prove the existence of a homomorphism from any algebraic extension
into an algebraic closure -/
structure SubfieldWithHom where
  carrier : Subalgebra K L
  emb : carrier →ₐ[K] M
#align lift.subfield_with_hom lift.SubfieldWithHom

variable {K L M hL}

namespace SubfieldWithHom

variable {E₁ E₂ E₃ : SubfieldWithHom K L M hL}

instance : LE (SubfieldWithHom K L M hL)
    where le E₁ E₂ := ∃ h : E₁.carrier ≤ E₂.carrier, ∀ x, E₂.emb (inclusion h x) = E₁.emb x

noncomputable instance : Inhabited (SubfieldWithHom K L M hL) :=
  ⟨{  carrier := ⊥
      emb := (Algebra.ofId K M).comp (Algebra.botEquiv K L).toAlgHom }⟩

theorem le_def : E₁ ≤ E₂ ↔ ∃ h : E₁.carrier ≤ E₂.carrier, ∀ x, E₂.emb (inclusion h x) = E₁.emb x :=
  Iff.rfl
#align lift.subfield_with_hom.le_def lift.SubfieldWithHom.le_def

theorem compat (h : E₁ ≤ E₂) : ∀ x, E₂.emb (inclusion h.fst x) = E₁.emb x := by rw [le_def] at h ;
  cases h; assumption
#align lift.subfield_with_hom.compat lift.SubfieldWithHom.compat

instance : Preorder (SubfieldWithHom K L M hL)
    where
  le := (· ≤ ·)
  le_refl E := ⟨le_rfl, by simp⟩
  le_trans E₁ E₂ E₃ h₁₂ h₂₃ :=
    ⟨le_trans h₁₂.fst h₂₃.fst, fun _ => by
      erw [← inclusion_inclusion h₁₂.fst h₂₃.fst, compat, compat]⟩

open Lattice

theorem maximal_subfieldWithHom_chain_bounded (c : Set (SubfieldWithHom K L M hL))
    (hc : IsChain (· ≤ ·) c) : ∃ ub : SubfieldWithHom K L M hL, ∀ N, N ∈ c → N ≤ ub :=
  if hcn : c.Nonempty then
    let ub : SubfieldWithHom K L M hL :=
      haveI : Nonempty c := Set.Nonempty.to_subtype hcn
      { carrier := ⨆ i : c, (i : subfield_with_hom K L M hL).carrier
        emb :=
          Subalgebra.iSupLift (fun i : c => (i : subfield_with_hom K L M hL).carrier)
            (fun i j =>
              let ⟨k, hik, hjk⟩ := directedOn_iff_directed.1 hc.directed_on i j
              ⟨k, hik.fst, hjk.fst⟩)
            (fun i => (i : subfield_with_hom K L M hL).emb)
            (by
              intro i j h
              ext x
              cases' hc.total i.prop j.prop with hij hji
              · simp [← hij.snd x]
              ·
                erw [AlgHom.comp_apply, ← hji.snd (inclusion h x), inclusion_inclusion,
                  inclusion_self, AlgHom.id_apply x])
            _ rfl }
    ⟨ub, fun N hN =>
      ⟨(le_iSup (fun i : c => (i : SubfieldWithHom K L M hL).carrier) ⟨N, hN⟩ : _),
        by
        intro x
        simp [ub]
        rfl⟩⟩
  else by rw [Set.not_nonempty_iff_eq_empty] at hcn ; simp [hcn]
#align lift.subfield_with_hom.maximal_subfield_with_hom_chain_bounded lift.SubfieldWithHom.maximal_subfieldWithHom_chain_bounded

variable (hL M)

theorem exists_maximal_subfieldWithHom : ∃ E : SubfieldWithHom K L M hL, ∀ N, E ≤ N → N ≤ E :=
  exists_maximal_of_chains_bounded maximal_subfieldWithHom_chain_bounded fun _ _ _ => le_trans
#align lift.subfield_with_hom.exists_maximal_subfield_with_hom lift.SubfieldWithHom.exists_maximal_subfieldWithHom

/-- The maximal `subfield_with_hom`. We later prove that this is equal to `⊤`. -/
noncomputable def maximalSubfieldWithHom : SubfieldWithHom K L M hL :=
  Classical.choose (exists_maximal_subfieldWithHom M hL)
#align lift.subfield_with_hom.maximal_subfield_with_hom lift.SubfieldWithHom.maximalSubfieldWithHom

theorem maximalSubfieldWithHom_is_maximal :
    ∀ N : SubfieldWithHom K L M hL,
      maximalSubfieldWithHom M hL ≤ N → N ≤ maximalSubfieldWithHom M hL :=
  Classical.choose_spec (exists_maximal_subfieldWithHom M hL)
#align lift.subfield_with_hom.maximal_subfield_with_hom_is_maximal lift.SubfieldWithHom.maximalSubfieldWithHom_is_maximal

theorem maximalSubfieldWithHom_eq_top : (maximalSubfieldWithHom M hL).carrier = ⊤ :=
  by
  rw [eq_top_iff]
  intro x _
  let p := minpoly K x
  let N : Subalgebra K L := (maximal_subfield_with_hom M hL).carrier
  letI : Field N := (Subalgebra.isField_of_algebraic N hL).toField
  letI : Algebra N M := (maximal_subfield_with_hom M hL).emb.toRingHom.toAlgebra
  cases'
    IsAlgClosed.exists_aeval_eq_zero M (minpoly N x)
      (ne_of_gt
        (minpoly.degree_pos
          (isAlgebraic_iff_isIntegral.1 (Algebra.isAlgebraic_of_larger_base _ _ hL x)))) with
    y hy
  let O : Subalgebra N L := Algebra.adjoin N {(x : L)}
  let larger_emb :=
    (AdjoinRoot.liftHom (minpoly N x) y hy).comp
      (AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly N x).toAlgHom
  have hNO : N ≤ O.restrict_scalars K := by
    intro z hz
    show algebraMap N L ⟨z, hz⟩ ∈ O
    exact O.algebra_map_mem _
  let O' : subfield_with_hom K L M hL :=
    { carrier := O.restrict_scalars K
      emb := larger_emb.restrict_scalars K }
  have hO' : maximal_subfield_with_hom M hL ≤ O' :=
    by
    refine' ⟨hNO, _⟩
    intro z
    show O'.emb (algebraMap N O z) = algebraMap N M z
    simp only [O', restrict_scalars_apply, AlgHom.commutes]
  refine' (maximal_subfield_with_hom_is_maximal M hL O' hO').fst _
  exact Algebra.subset_adjoin (Set.mem_singleton x)
#align lift.subfield_with_hom.maximal_subfield_with_hom_eq_top lift.SubfieldWithHom.maximalSubfieldWithHom_eq_top

end SubfieldWithHom

end lift

namespace IsAlgClosed

variable {K : Type u} [Field K] {L : Type v} {M : Type w} [Field L] [Algebra K L] [Field M]
  [Algebra K M] [IsAlgClosed M] (hL : Algebra.IsAlgebraic K L)

variable (K L M)

include hL

/-- Less general version of `lift`. -/
private noncomputable irreducible_def lift_aux : L →ₐ[K] M :=
  (lift.SubfieldWithHom.maximalSubfieldWithHom M hL).emb.comp <|
    Eq.recOn (lift.SubfieldWithHom.maximalSubfieldWithHom_eq_top M hL).symm Algebra.toTop

omit hL

variable {R : Type u} [CommRing R]

variable {S : Type v} [CommRing S] [IsDomain S] [Algebra R S] [Algebra R M] [NoZeroSMulDivisors R S]
  [NoZeroSMulDivisors R M] (hS : Algebra.IsAlgebraic R S)

variable {M}

include hS

private theorem fraction_ring.is_algebraic :
    letI : IsDomain R := (NoZeroSMulDivisors.algebraMap_injective R S).IsDomain _
    Algebra.IsAlgebraic (FractionRing R) (FractionRing S) :=
  by
  intro inst x
  exact
    (IsFractionRing.isAlgebraic_iff R (FractionRing R) (FractionRing S)).1
      ((IsFractionRing.isAlgebraic_iff' R S (FractionRing S)).1 hS x)

/-- A (random) homomorphism from an algebraic extension of R into an algebraically
  closed extension of R. -/
noncomputable irreducible_def lift : S →ₐ[R] M :=
  by
  letI : IsDomain R := (NoZeroSMulDivisors.algebraMap_injective R S).IsDomain _
  have hfRfS : Algebra.IsAlgebraic (FractionRing R) (FractionRing S) :=
    fraction_ring.is_algebraic hS
  let f : FractionRing S →ₐ[FractionRing R] M := lift_aux (FractionRing R) (FractionRing S) M hfRfS
  exact (f.restrict_scalars R).comp ((Algebra.ofId S (FractionRing S)).restrictScalars R)
#align is_alg_closed.lift IsAlgClosed.lift

omit hS

noncomputable instance (priority := 100) perfectRing (p : ℕ) [Fact p.Prime] [CharP k p]
    [IsAlgClosed k] : PerfectRing k p :=
  PerfectRing.ofSurjective k p fun x => IsAlgClosed.exists_pow_nat_eq _ <| NeZero.pos p
#align is_alg_closed.perfect_ring IsAlgClosed.perfectRing

/-- Algebraically closed fields are infinite since `Xⁿ⁺¹ - 1` is separable when `#K = n` -/
instance (priority := 500) {K : Type _} [Field K] [IsAlgClosed K] : Infinite K :=
  by
  apply Infinite.of_not_fintype
  intro hfin
  set n := Fintype.card K with hn
  set f := (X : K[X]) ^ (n + 1) - 1 with hf
  have hfsep : separable f := separable_X_pow_sub_C 1 (by simp) one_ne_zero
  apply Nat.not_succ_le_self (Fintype.card K)
  have hroot : n.succ = Fintype.card (f.root_set K) := by
    erw [card_root_set_eq_nat_degree hfsep (IsAlgClosed.splits_domain _), nat_degree_X_pow_sub_C]
  rw [hroot]
  exact Fintype.card_le_of_injective coe Subtype.coe_injective

end IsAlgClosed

namespace IsAlgClosure

variable (K : Type _) (J : Type _) (R : Type u) (S : Type _) [Field K] [Field J] [CommRing R]
  (L : Type v) (M : Type w) [Field L] [Field M] [Algebra R M] [NoZeroSMulDivisors R M]
  [IsAlgClosure R M] [Algebra K M] [IsAlgClosure K M] [CommRing S] [Algebra S L]
  [NoZeroSMulDivisors S L] [IsAlgClosure S L]

attribute [local instance] IsAlgClosure.alg_closed

section

variable [Algebra R L] [NoZeroSMulDivisors R L] [IsAlgClosure R L]

/-- A (random) isomorphism between two algebraic closures of `R`. -/
noncomputable def equiv : L ≃ₐ[R] M :=
  let f : L →ₐ[R] M := IsAlgClosed.lift IsAlgClosure.algebraic
  AlgEquiv.ofBijective f
    ⟨RingHom.injective f.toRingHom,
      by
      letI : Algebra L M := RingHom.toAlgebra f
      letI : IsScalarTower R L M :=
        IsScalarTower.of_algebraMap_eq (by simp [RingHom.algebraMap_toAlgebra])
      show Function.Surjective (algebraMap L M)
      exact
        IsAlgClosed.algebraMap_surjective_of_isAlgebraic
          (Algebra.isAlgebraic_of_larger_base_of_injective
            (NoZeroSMulDivisors.algebraMap_injective R _) IsAlgClosure.algebraic)⟩
#align is_alg_closure.equiv IsAlgClosure.equiv

end

section EquivOfAlgebraic

variable [Algebra R S] [Algebra R L] [IsScalarTower R S L]

variable [Algebra K J] [Algebra J L] [IsAlgClosure J L] [Algebra K L] [IsScalarTower K J L]

/-- If `J` is an algebraic extension of `K` and `L` is an algebraic closure of `J`, then it is
  also an algebraic closure of `K`. -/
theorem ofAlgebraic (hKJ : Algebra.IsAlgebraic K J) : IsAlgClosure K L :=
  ⟨IsAlgClosure.alg_closed J, Algebra.isAlgebraic_trans hKJ IsAlgClosure.algebraic⟩
#align is_alg_closure.of_algebraic IsAlgClosure.ofAlgebraic

/-- A (random) isomorphism between an algebraic closure of `R` and an algebraic closure of
  an algebraic extension of `R` -/
noncomputable def equivOfAlgebraic' [Nontrivial S] [NoZeroSMulDivisors R S]
    (hRL : Algebra.IsAlgebraic R L) : L ≃ₐ[R] M :=
  by
  letI : NoZeroSMulDivisors R L :=
    NoZeroSMulDivisors.of_algebraMap_injective
      (by
        rw [IsScalarTower.algebraMap_eq R S L]
        exact
          Function.Injective.comp (NoZeroSMulDivisors.algebraMap_injective _ _)
            (NoZeroSMulDivisors.algebraMap_injective _ _))
  letI : IsAlgClosure R L :=
    { alg_closed := by infer_instance
      algebraic := hRL }
  exact IsAlgClosure.equiv _ _ _
#align is_alg_closure.equiv_of_algebraic' IsAlgClosure.equivOfAlgebraic'

/-- A (random) isomorphism between an algebraic closure of `K` and an algebraic closure
  of an algebraic extension of `K` -/
noncomputable def equivOfAlgebraic (hKJ : Algebra.IsAlgebraic K J) : L ≃ₐ[K] M :=
  equivOfAlgebraic' K J _ _ (Algebra.isAlgebraic_trans hKJ IsAlgClosure.algebraic)
#align is_alg_closure.equiv_of_algebraic IsAlgClosure.equivOfAlgebraic

end EquivOfAlgebraic

section EquivOfEquiv

variable {R S}

/-- Used in the definition of `equiv_of_equiv` -/
noncomputable def equivOfEquivAux (hSR : S ≃+* R) :
    { e : L ≃+* M // e.toRingHom.comp (algebraMap S L) = (algebraMap R M).comp hSR.toRingHom } :=
  by
  letI : Algebra R S := RingHom.toAlgebra hSR.symm.to_ring_hom
  letI : Algebra S R := RingHom.toAlgebra hSR.to_ring_hom
  letI : IsDomain R := (NoZeroSMulDivisors.algebraMap_injective R M).IsDomain _
  letI : IsDomain S := (NoZeroSMulDivisors.algebraMap_injective S L).IsDomain _
  have : Algebra.IsAlgebraic R S := fun x =>
    by
    rw [← RingEquiv.symm_apply_apply hSR x]
    exact isAlgebraic_algebraMap _
  letI : Algebra R L := RingHom.toAlgebra ((algebraMap S L).comp (algebraMap R S))
  haveI : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower S R L :=
    IsScalarTower.of_algebraMap_eq (by simp [RingHom.algebraMap_toAlgebra])
  haveI : NoZeroSMulDivisors R S := NoZeroSMulDivisors.of_algebraMap_injective hSR.symm.injective
  refine'
    ⟨equiv_of_algebraic' R S L M
        (Algebra.isAlgebraic_of_larger_base_of_injective
          (show Function.Injective (algebraMap S R) from hSR.injective) IsAlgClosure.algebraic),
      _⟩
  ext
  simp only [RingEquiv.toRingHom_eq_coe, Function.comp_apply, RingHom.coe_comp,
    AlgEquiv.coe_ringEquiv, RingEquiv.coe_toRingHom]
  conv_lhs => rw [← hSR.symm_apply_apply x]
  show equiv_of_algebraic' R S L M _ (algebraMap R L (hSR x)) = _
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
  (equivOfEquiv L M hSR).Injective (by simp)
#align is_alg_closure.equiv_of_equiv_symm_algebra_map IsAlgClosure.equivOfEquiv_symm_algebraMap

@[simp]
theorem equivOfEquiv_symm_comp_algebraMap (hSR : S ≃+* R) :
    ((equivOfEquiv L M hSR).symm : M →+* L).comp (algebraMap R M) =
      (algebraMap S L).comp hSR.symm :=
  RingHom.ext_iff.2 (equivOfEquiv_symm_algebraMap L M hSR)
#align is_alg_closure.equiv_of_equiv_symm_comp_algebra_map IsAlgClosure.equivOfEquiv_symm_comp_algebraMap

end EquivOfEquiv

end IsAlgClosure

/-- Let `A` be an algebraically closed field and let `x ∈ K`, with `K/F` an algebraic extension
  of fields. Then the images of `x` by the `F`-algebra morphisms from `K` to `A` are exactly
  the roots in `A` of the minimal polynomial of `x` over `F`. -/
theorem Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly {F K} (A) [Field F] [Field K] [Field A]
    [IsAlgClosed A] [Algebra F K] (hK : Algebra.IsAlgebraic F K) [Algebra F A] (x : K) :
    (Set.range fun ψ : K →ₐ[F] A => ψ x) = (minpoly F x).rootSet A :=
  by
  have := Algebra.isAlgebraic_iff_isIntegral.1 hK
  ext a; rw [mem_root_set_of_ne (minpoly.ne_zero (this x))] <;> [skip; infer_instance]
  refine' ⟨_, fun ha => _⟩
  · rintro ⟨ψ, rfl⟩; rw [aeval_alg_hom_apply ψ x, minpoly.aeval, map_zero]
  let Fx := AdjoinRoot (minpoly F x)
  have hx : aeval x (minpoly F x) = 0 := minpoly.aeval F x
  letI : Algebra Fx A := (AdjoinRoot.lift (algebraMap F A) a ha).toAlgebra
  letI : Algebra Fx K := (AdjoinRoot.lift (algebraMap F K) x hx).toAlgebra
  haveI : IsScalarTower F Fx A := IsScalarTower.of_ring_hom (AdjoinRoot.liftHom _ a ha)
  haveI : IsScalarTower F Fx K := IsScalarTower.of_ring_hom (AdjoinRoot.liftHom _ x hx)
  haveI : Fact (Irreducible <| minpoly F x) := ⟨minpoly.irreducible <| this x⟩
  let ψ₀ : K →ₐ[Fx] A := IsAlgClosed.lift (Algebra.isAlgebraic_of_larger_base F Fx hK)
  exact
    ⟨ψ₀.restrict_scalars F,
      (congr_arg ψ₀ (AdjoinRoot.lift_root hx).symm).trans <|
        (ψ₀.commutes _).trans <| AdjoinRoot.lift_root ha⟩
#align algebra.is_algebraic.range_eval_eq_root_set_minpoly Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly

