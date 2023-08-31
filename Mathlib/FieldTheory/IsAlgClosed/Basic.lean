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

-/


universe u v w

open scoped Classical BigOperators Polynomial

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
  · use z
    simp only [eval_C, eval_X, eval_pow, eval_sub, IsRoot.def] at hz
    exact sub_eq_zero.1 hz
#align is_alg_closed.exists_pow_nat_eq IsAlgClosed.exists_pow_nat_eq

theorem exists_eq_mul_self [IsAlgClosed k] (x : k) : ∃ z, x = z * z := by
  rcases exists_pow_nat_eq x zero_lt_two with ⟨z, rfl⟩
  exact ⟨z, sq z⟩
#align is_alg_closed.exists_eq_mul_self IsAlgClosed.exists_eq_mul_self

theorem roots_eq_zero_iff [IsAlgClosed k] {p : k[X]} :
    p.roots = 0 ↔ p = Polynomial.C (p.coeff 0) := by
  refine' ⟨fun h => _, fun hp => by rw [hp, roots_C]⟩
  cases' le_or_lt (degree p) 0 with hd hd
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

theorem degree_eq_one_of_irreducible [IsAlgClosed k] {p : k[X]} (hp : Irreducible p) :
    p.degree = 1 :=
  degree_eq_one_of_irreducible_of_splits hp (IsAlgClosed.splits_codomain _)
#align is_alg_closed.degree_eq_one_of_irreducible IsAlgClosed.degree_eq_one_of_irreducible

theorem algebraMap_surjective_of_isIntegral {k K : Type*} [Field k] [Ring K] [IsDomain K]
    [hk : IsAlgClosed k] [Algebra k K] (hf : Algebra.IsIntegral k K) :
    Function.Surjective (algebraMap k K) := by
  refine' fun x => ⟨-(minpoly k x).coeff 0, _⟩
  have hq : (minpoly k x).leadingCoeff = 1 := minpoly.monic (hf x)
  have h : (minpoly k x).degree = 1 := degree_eq_one_of_irreducible k (minpoly.irreducible (hf x))
  have : aeval x (minpoly k x) = 0 := minpoly.aeval k x
  rw [eq_X_add_C_of_degree_eq_one h, hq, C_1, one_mul, aeval_add, aeval_X, aeval_C,
    add_eq_zero_iff_eq_neg] at this
  exact (RingHom.map_neg (algebraMap k K) ((minpoly k x).coeff 0)).symm ▸ this.symm
#align is_alg_closed.algebra_map_surjective_of_is_integral IsAlgClosed.algebraMap_surjective_of_isIntegral

theorem algebraMap_surjective_of_isIntegral' {k K : Type*} [Field k] [CommRing K] [IsDomain K]
    [IsAlgClosed k] (f : k →+* K) (hf : f.IsIntegral) : Function.Surjective f :=
  @algebraMap_surjective_of_isIntegral k K _ _ _ _ f.toAlgebra hf
#align is_alg_closed.algebra_map_surjective_of_is_integral' IsAlgClosed.algebraMap_surjective_of_isIntegral'

theorem algebraMap_surjective_of_isAlgebraic {k K : Type*} [Field k] [Ring K] [IsDomain K]
    [IsAlgClosed k] [Algebra k K] (hf : Algebra.IsAlgebraic k K) :
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

instance (priority := 100) IsAlgClosure.normal (R K : Type*) [Field R] [Field K] [Algebra R K]
    [IsAlgClosure R K] : Normal R K :=
  ⟨IsAlgClosure.algebraic, fun _ =>
    @IsAlgClosed.splits_codomain _ _ _ (IsAlgClosure.alg_closed R) _ _ _⟩
#align is_alg_closure.normal IsAlgClosure.normal

instance (priority := 100) IsAlgClosure.separable (R K : Type*) [Field R] [Field K] [Algebra R K]
    [IsAlgClosure R K] [CharZero R] : IsSeparable R K :=
  ⟨fun _ => isAlgebraic_iff_isIntegral.mp (IsAlgClosure.algebraic _), fun _ =>
    (minpoly.irreducible (isAlgebraic_iff_isIntegral.mp (IsAlgClosure.algebraic _))).separable⟩
#align is_alg_closure.separable IsAlgClosure.separable

namespace IsAlgClosed

namespace lift

/- In this section, the homomorphism from any algebraic extension into an algebraically
  closed extension is proven to exist. The assumption that M is algebraically closed could probably
  easily be switched to an assumption that M contains all the roots of polynomials in K -/
variable {K : Type u} {L : Type v} {M : Type w} [Field K] [Field L] [Algebra K L] [Field M]
  [Algebra K M] [IsAlgClosed M] (hL : Algebra.IsAlgebraic K L)

variable (K L M)

open Subalgebra AlgHom Function

/-- This structure is used to prove the existence of a homomorphism from any algebraic extension
into an algebraic closure -/
structure SubfieldWithHom where
  /-- The corresponding `Subalgebra` -/
  carrier : Subalgebra K L
  /-- The embedding into the algebraically closed field -/
  emb : carrier →ₐ[K] M
#align lift.subfield_with_hom IsAlgClosed.lift.SubfieldWithHom

variable {K L M hL}

namespace SubfieldWithHom

variable {E₁ E₂ E₃ : SubfieldWithHom K L M}

instance : LE (SubfieldWithHom K L M) where
  le E₁ E₂ := ∃ h : E₁.carrier ≤ E₂.carrier, ∀ x, E₂.emb (inclusion h x) = E₁.emb x

noncomputable instance : Inhabited (SubfieldWithHom K L M) :=
  ⟨{  carrier := ⊥
      emb := (Algebra.ofId K M).comp (Algebra.botEquiv K L).toAlgHom }⟩

theorem le_def : E₁ ≤ E₂ ↔ ∃ h : E₁.carrier ≤ E₂.carrier, ∀ x, E₂.emb (inclusion h x) = E₁.emb x :=
  Iff.rfl
#align lift.subfield_with_hom.le_def IsAlgClosed.lift.SubfieldWithHom.le_def

theorem compat (h : E₁ ≤ E₂) : ∀ x, E₂.emb (inclusion h.fst x) = E₁.emb x := by
  rw [le_def] at h; cases h; assumption
#align lift.subfield_with_hom.compat IsAlgClosed.lift.SubfieldWithHom.compat

instance : Preorder (SubfieldWithHom K L M) where
  le := (· ≤ ·)
  le_refl E := ⟨le_rfl, by simp⟩
  le_trans E₁ E₂ E₃ h₁₂ h₂₃ := by
    refine ⟨h₁₂.1.trans h₂₃.1, fun _ ↦ ?_⟩
    erw [← inclusion_inclusion h₁₂.fst h₂₃.fst, compat h₂₃, compat h₁₂]

open Lattice

theorem maximal_subfieldWithHom_chain_bounded (c : Set (SubfieldWithHom K L M))
    (hc : IsChain (· ≤ ·) c) : ∃ ub : SubfieldWithHom K L M, ∀ N, N ∈ c → N ≤ ub := by
  by_cases hcn : c.Nonempty
  case neg => rw [Set.not_nonempty_iff_eq_empty] at hcn; simp [hcn]
  case pos =>
    have : Nonempty c := Set.Nonempty.to_subtype hcn
    let ub : SubfieldWithHom K L M :=
      ⟨⨆ i : c, (i : SubfieldWithHom K L M).carrier,
        @Subalgebra.iSupLift _ _ _ _ _ _ _ _ _ this
            (fun i : c => (i : SubfieldWithHom K L M).carrier)
            (fun i j =>
              let ⟨k, hik, hjk⟩ := directedOn_iff_directed.1 hc.directedOn i j
              ⟨k, hik.fst, hjk.fst⟩)
            (fun i => (i : SubfieldWithHom K L M).emb)
            (by
              intro i j h
              ext x
              cases' hc.total i.prop j.prop with hij hji
              · simp [← hij.snd x]
              · erw [AlgHom.comp_apply, ← hji.snd (inclusion h x), inclusion_inclusion,
                  inclusion_self, AlgHom.id_apply x])
            _ rfl⟩
    exact ⟨ub, fun N hN =>
         ⟨(le_iSup (fun i : c => (i : SubfieldWithHom K L M).carrier) ⟨N, hN⟩ : _), by
           intro x
           simp⟩⟩
#align lift.subfield_with_hom.maximal_subfield_with_hom_chain_bounded IsAlgClosed.lift.SubfieldWithHom.maximal_subfieldWithHom_chain_bounded

variable (K L M)

theorem exists_maximal_subfieldWithHom : ∃ E : SubfieldWithHom K L M, ∀ N, E ≤ N → N ≤ E :=
  exists_maximal_of_chains_bounded maximal_subfieldWithHom_chain_bounded le_trans
#align lift.subfield_with_hom.exists_maximal_subfield_with_hom IsAlgClosed.lift.SubfieldWithHom.exists_maximal_subfieldWithHom

/-- The maximal `SubfieldWithHom`. We later prove that this is equal to `⊤`. -/
noncomputable def maximalSubfieldWithHom : SubfieldWithHom K L M :=
  Classical.choose (exists_maximal_subfieldWithHom K L M)
#align lift.subfield_with_hom.maximal_subfield_with_hom IsAlgClosed.lift.SubfieldWithHom.maximalSubfieldWithHom

theorem maximalSubfieldWithHom_is_maximal :
    ∀ N : SubfieldWithHom K L M,
      maximalSubfieldWithHom K L M ≤ N → N ≤ maximalSubfieldWithHom K L M :=
  Classical.choose_spec (exists_maximal_subfieldWithHom K L M)
#align lift.subfield_with_hom.maximal_subfield_with_hom_is_maximal IsAlgClosed.lift.SubfieldWithHom.maximalSubfieldWithHom_is_maximal

-- Porting note: split out this definition from `maximalSubfieldWithHom_eq_top`
/-- Produce an algebra homomorphism `Adjoin R {x} →ₐ[R] T` sending `x` to
a root of `x`'s minimal polynomial in `T`. -/
noncomputable def _root_.Algebra.adjoin.liftSingleton (R : Type*) [Field R] {S T : Type*}
  [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  (x : S) (y : T) (h : aeval y (minpoly R x) = 0) :
  Algebra.adjoin R {x} →ₐ[R] T :=
AlgHom.comp
  (AdjoinRoot.liftHom _ y h)
  (AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly R x).toAlgHom

-- porting note: this was much faster in lean 3
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem maximalSubfieldWithHom_eq_top : (maximalSubfieldWithHom K L M).carrier = ⊤ := by
  rw [eq_top_iff]
  intro x _
  let N : Subalgebra K L := (maximalSubfieldWithHom K L M).carrier
  letI : Field N := (Subalgebra.isField_of_algebraic N hL).toField
  letI : Algebra N M := (maximalSubfieldWithHom K L M).emb.toRingHom.toAlgebra
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_aeval_eq_zero M (minpoly N x) <|
    (minpoly.degree_pos
      (isAlgebraic_iff_isIntegral.1 (Algebra.isAlgebraic_of_larger_base _ hL x))).ne'
  let O : Subalgebra N L := Algebra.adjoin N {(x : L)}
  letI : Algebra N O := Subalgebra.algebra O
  -- Porting note: there are some tricky unfolds going on here:
  -- (O.restrictScalars K : Type*) is identified with (O : Type*) in a few places
  let larger_emb : O →ₐ[N] M := Algebra.adjoin.liftSingleton N x y hy
  let larger_emb' : O →ₐ[K] M := AlgHom.restrictScalars K (S := N) (A := O) (B := M) larger_emb
  have hNO : N ≤ O.restrictScalars K := by
    intro z hz
    show algebraMap N L ⟨z, hz⟩ ∈ O
    exact O.algebraMap_mem _
  let O' : SubfieldWithHom K L M :=
    ⟨O.restrictScalars K, larger_emb'⟩
  have hO' : maximalSubfieldWithHom K L M ≤ O' := by
    refine' ⟨hNO, _⟩
    intro z
    -- Porting note: have to help Lean unfold even more here
    show Algebra.adjoin.liftSingleton N x y hy (@algebraMap N O _ _ (Subalgebra.algebra O) z) =
        algebraMap N M z
    exact AlgHom.commutes _ _
  refine' (maximalSubfieldWithHom_is_maximal K L M O' hO').fst _
  show x ∈ Algebra.adjoin N {(x : L)}
  exact Algebra.subset_adjoin (Set.mem_singleton x)
#align lift.subfield_with_hom.maximal_subfield_with_hom_eq_top IsAlgClosed.lift.SubfieldWithHom.maximalSubfieldWithHom_eq_top

end SubfieldWithHom

end lift

variable {K : Type u} [Field K] {L : Type v} {M : Type w} [Field L] [Algebra K L] [Field M]
  [Algebra K M] [IsAlgClosed M] (hL : Algebra.IsAlgebraic K L)

variable (K L M)

/-- Less general version of `lift`. -/
private noncomputable irreducible_def lift_aux : L →ₐ[K] M :=
  (lift.SubfieldWithHom.maximalSubfieldWithHom K L M).emb.comp <|
    (lift.SubfieldWithHom.maximalSubfieldWithHom_eq_top (K := K) (L := L) (M := M) (hL := hL)).symm
      ▸ Algebra.toTop

variable {R : Type u} [CommRing R]

variable {S : Type v} [CommRing S] [IsDomain S] [Algebra R S] [Algebra R M] [NoZeroSMulDivisors R S]
  [NoZeroSMulDivisors R M] (hS : Algebra.IsAlgebraic R S)

variable {M}

private theorem FractionRing.isAlgebraic :
    letI : IsDomain R := (NoZeroSMulDivisors.algebraMap_injective R S).isDomain _
    Algebra.IsAlgebraic (FractionRing R) (FractionRing S) := by
  letI : IsDomain R := (NoZeroSMulDivisors.algebraMap_injective R S).isDomain _
  intro
  exact
    (IsFractionRing.isAlgebraic_iff R (FractionRing R) (FractionRing S)).1
      ((IsFractionRing.isAlgebraic_iff' R S (FractionRing S)).1 hS _)

/-- A (random) homomorphism from an algebraic extension of R into an algebraically
  closed extension of R. -/
noncomputable irreducible_def lift : S →ₐ[R] M := by
  letI : IsDomain R := (NoZeroSMulDivisors.algebraMap_injective R S).isDomain _
  have : Algebra.IsAlgebraic (FractionRing R) (FractionRing S) :=
    FractionRing.isAlgebraic hS
  let f : FractionRing S →ₐ[FractionRing R] M := lift_aux (FractionRing R) (FractionRing S) M this
  exact (f.restrictScalars R).comp ((Algebra.ofId S (FractionRing S)).restrictScalars R)
#align is_alg_closed.lift IsAlgClosed.lift

noncomputable instance (priority := 100) perfectRing (p : ℕ) [Fact p.Prime] [CharP k p]
    [IsAlgClosed k] : PerfectRing k p :=
  PerfectRing.ofSurjective k p fun _ => IsAlgClosed.exists_pow_nat_eq _ <| NeZero.pos p
#align is_alg_closed.perfect_ring IsAlgClosed.perfectRing

/-- Algebraically closed fields are infinite since `Xⁿ⁺¹ - 1` is separable when `#K = n` -/
instance (priority := 500) {K : Type*} [Field K] [IsAlgClosed K] : Infinite K := by
  apply Infinite.of_not_fintype
  intro hfin
  set n := Fintype.card K
  set f := (X : K[X]) ^ (n + 1) - 1
  have hfsep : Separable f := separable_X_pow_sub_C 1 (by simp) one_ne_zero
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
  -- Porting note: added to replace local instance above
  haveI : IsAlgClosed M := IsAlgClosure.alg_closed R
  let f : L →ₐ[R] M := IsAlgClosed.lift IsAlgClosure.algebraic
  AlgEquiv.ofBijective f
    ⟨RingHom.injective f.toRingHom, by
      letI : Algebra L M := RingHom.toAlgebra f
      letI : IsScalarTower R L M := IsScalarTower.of_algebraMap_eq <| by
        simp only [RingHom.algebraMap_toAlgebra, RingHom.coe_coe, AlgHom.commutes, forall_const]
      letI : IsAlgClosed L := IsAlgClosure.alg_closed R
      show Function.Surjective (algebraMap L M)
      exact
        IsAlgClosed.algebraMap_surjective_of_isAlgebraic
          (Algebra.isAlgebraic_of_larger_base_of_injective
            (NoZeroSMulDivisors.algebraMap_injective R _) IsAlgClosure.algebraic)⟩
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
theorem ofAlgebraic (hKJ : Algebra.IsAlgebraic K J) : IsAlgClosure K L :=
  ⟨IsAlgClosure.alg_closed J, Algebra.isAlgebraic_trans hKJ IsAlgClosure.algebraic⟩
#align is_alg_closure.of_algebraic IsAlgClosure.ofAlgebraic

/-- A (random) isomorphism between an algebraic closure of `R` and an algebraic closure of
  an algebraic extension of `R` -/
noncomputable def equivOfAlgebraic' [Nontrivial S] [NoZeroSMulDivisors R S]
    (hRL : Algebra.IsAlgebraic R L) : L ≃ₐ[R] M := by
  letI : NoZeroSMulDivisors R L := NoZeroSMulDivisors.of_algebraMap_injective <| by
    rw [IsScalarTower.algebraMap_eq R S L]
    exact (Function.Injective.comp (NoZeroSMulDivisors.algebraMap_injective S L)
            (NoZeroSMulDivisors.algebraMap_injective R S) : _)
  letI : IsAlgClosure R L :=
    { alg_closed := IsAlgClosure.alg_closed S
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
  refine'
    ⟨equivOfAlgebraic' R S L M
        (Algebra.isAlgebraic_of_larger_base_of_injective
          (show Function.Injective (algebraMap S R) from hSR.injective) IsAlgClosure.algebraic),
      _⟩
  ext x
  simp only [RingEquiv.toRingHom_eq_coe, Function.comp_apply, RingHom.coe_comp,
    AlgEquiv.coe_ringEquiv, RingEquiv.coe_toRingHom]
  conv_lhs => rw [← hSR.symm_apply_apply x]
  show equivOfAlgebraic' R S L M _ (algebraMap R L (hSR x)) = _
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

/-- Let `A` be an algebraically closed field and let `x ∈ K`, with `K/F` an algebraic extension
  of fields. Then the images of `x` by the `F`-algebra morphisms from `K` to `A` are exactly
  the roots in `A` of the minimal polynomial of `x` over `F`. -/
theorem Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly {F K} (A) [Field F] [Field K] [Field A]
    [IsAlgClosed A] [Algebra F K] (hK : Algebra.IsAlgebraic F K) [Algebra F A] (x : K) :
    (Set.range fun ψ : K →ₐ[F] A => ψ x) = (minpoly F x).rootSet A := by
  have hFK := Algebra.isAlgebraic_iff_isIntegral.1 hK
  ext a
  rw [mem_rootSet_of_ne (minpoly.ne_zero (hFK x))]
  refine' ⟨_, fun ha => _⟩
  · rintro ⟨ψ, rfl⟩; rw [aeval_algHom_apply ψ x, minpoly.aeval, map_zero]
  let Fx := AdjoinRoot (minpoly F x)
  have hx : aeval x (minpoly F x) = 0 := minpoly.aeval F x
  letI : Algebra Fx A := (AdjoinRoot.lift (algebraMap F A) a ha).toAlgebra
  letI : Algebra Fx K := (AdjoinRoot.lift (algebraMap F K) x hx).toAlgebra
  haveI : IsScalarTower F Fx A := IsScalarTower.of_ring_hom (AdjoinRoot.liftHom _ a ha)
  haveI : IsScalarTower F Fx K := IsScalarTower.of_ring_hom (AdjoinRoot.liftHom _ x hx)
  haveI : Fact (Irreducible <| minpoly F x) := ⟨minpoly.irreducible <| hFK x⟩
  let ψ₀ : K →ₐ[Fx] A := IsAlgClosed.lift (Algebra.isAlgebraic_of_larger_base Fx hK)
  exact
    ⟨ψ₀.restrictScalars F,
      (congr_arg ψ₀ (AdjoinRoot.lift_root hx).symm).trans <|
        (ψ₀.commutes _).trans <| AdjoinRoot.lift_root ha⟩
#align algebra.is_algebraic.range_eval_eq_root_set_minpoly Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly
