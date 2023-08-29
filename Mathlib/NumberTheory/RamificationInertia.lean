/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.LinearAlgebra.FreeModule.Finite.Rank
import Mathlib.RingTheory.DedekindDomain.Ideal

#align_import number_theory.ramification_inertia from "leanprover-community/mathlib"@"039a089d2a4b93c761b234f3e5f5aeb752bac60f"

/-!
# Ramification index and inertia degree

Given `P : Ideal S` lying over `p : Ideal R` for the ring extension `f : R →+* S`
(assuming `P` and `p` are prime or maximal where needed),
the **ramification index** `Ideal.ramificationIdx f p P` is the multiplicity of `P` in `map f p`,
and the **inertia degree** `Ideal.inertiaDeg f p P` is the degree of the field extension
`(S / P) : (R / p)`.

## Main results

The main theorem `Ideal.sum_ramification_inertia` states that for all coprime `P` lying over `p`,
`Σ P, ramification_idx f p P * inertia_deg f p P` equals the degree of the field extension
`Frac(S) : Frac(R)`.

## Implementation notes

Often the above theory is set up in the case where:
 * `R` is the ring of integers of a number field `K`,
 * `L` is a finite separable extension of `K`,
 * `S` is the integral closure of `R` in `L`,
 * `p` and `P` are maximal ideals,
 * `P` is an ideal lying over `p`
We will try to relax the above hypotheses as much as possible.

## Notation

In this file, `e` stands for the ramification index and `f` for the inertia degree of `P` over `p`,
leaving `p` and `P` implicit.

-/


namespace Ideal

universe u v

variable {R : Type u} [CommRing R]

variable {S : Type v} [CommRing S] (f : R →+* S)

variable (p : Ideal R) (P : Ideal S)

open FiniteDimensional

open UniqueFactorizationMonoid

section DecEq

open scoped Classical

/-- The ramification index of `P` over `p` is the largest exponent `n` such that
`p` is contained in `P^n`.

In particular, if `p` is not contained in `P^n`, then the ramification index is 0.

If there is no largest such `n` (e.g. because `p = ⊥`), then `ramificationIdx` is
defined to be 0.
-/
noncomputable def ramificationIdx : ℕ := sSup {n | map f p ≤ P ^ n}
#align ideal.ramification_idx Ideal.ramificationIdx

variable {f p P}

theorem ramificationIdx_eq_find (h : ∃ n, ∀ k, map f p ≤ P ^ k → k ≤ n) :
    ramificationIdx f p P = Nat.find h :=
  Nat.sSup_def h
#align ideal.ramification_idx_eq_find Ideal.ramificationIdx_eq_find

theorem ramificationIdx_eq_zero (h : ∀ n : ℕ, ∃ k, map f p ≤ P ^ k ∧ n < k) :
    ramificationIdx f p P = 0 :=
  dif_neg (by push_neg; exact h)
              -- ⊢ ∀ (n : ℕ), ∃ a, a ∈ {n | map f p ≤ P ^ n} ∧ n < a
                        -- 🎉 no goals
#align ideal.ramification_idx_eq_zero Ideal.ramificationIdx_eq_zero

theorem ramificationIdx_spec {n : ℕ} (hle : map f p ≤ P ^ n) (hgt : ¬map f p ≤ P ^ (n + 1)) :
    ramificationIdx f p P = n := by
  let Q : ℕ → Prop := fun m => ∀ k : ℕ, map f p ≤ P ^ k → k ≤ m
  -- ⊢ ramificationIdx f p P = n
  have : Q n := by
    intro k hk
    refine le_of_not_lt fun hnk => ?_
    exact hgt (hk.trans (Ideal.pow_le_pow hnk))
  rw [ramificationIdx_eq_find ⟨n, this⟩]
  -- ⊢ Nat.find (_ : ∃ n, ∀ (k : ℕ), map f p ≤ P ^ k → k ≤ n) = n
  refine le_antisymm (Nat.find_min' _ this) (le_of_not_gt fun h : Nat.find _ < n => ?_)
  -- ⊢ False
  obtain this' := Nat.find_spec ⟨n, this⟩
  -- ⊢ False
  exact h.not_le (this' _ hle)
  -- 🎉 no goals
#align ideal.ramification_idx_spec Ideal.ramificationIdx_spec

theorem ramificationIdx_lt {n : ℕ} (hgt : ¬map f p ≤ P ^ n) : ramificationIdx f p P < n := by
  cases' n with n n
  -- ⊢ ramificationIdx f p P < Nat.zero
  · simp at hgt
    -- 🎉 no goals
  · rw [Nat.lt_succ_iff]
    -- ⊢ ramificationIdx f p P ≤ n
    have : ∀ k, map f p ≤ P ^ k → k ≤ n := by
      refine fun k hk => le_of_not_lt fun hnk => ?_
      exact hgt (hk.trans (Ideal.pow_le_pow hnk))
    rw [ramificationIdx_eq_find ⟨n, this⟩]
    -- ⊢ Nat.find (_ : ∃ n, ∀ (k : ℕ), map f p ≤ P ^ k → k ≤ n) ≤ n
    exact Nat.find_min' ⟨n, this⟩ this
    -- 🎉 no goals
#align ideal.ramification_idx_lt Ideal.ramificationIdx_lt

@[simp]
theorem ramificationIdx_bot : ramificationIdx f ⊥ P = 0 :=
  dif_neg <| not_exists.mpr fun n hn => n.lt_succ_self.not_le (hn _ (by simp))
                                                                        -- 🎉 no goals
#align ideal.ramification_idx_bot Ideal.ramificationIdx_bot

@[simp]
theorem ramificationIdx_of_not_le (h : ¬map f p ≤ P) : ramificationIdx f p P = 0 :=
  ramificationIdx_spec (by simp) (by simpa using h)
                           -- 🎉 no goals
                                     -- 🎉 no goals
#align ideal.ramification_idx_of_not_le Ideal.ramificationIdx_of_not_le

theorem ramificationIdx_ne_zero {e : ℕ} (he : e ≠ 0) (hle : map f p ≤ P ^ e)
    (hnle : ¬map f p ≤ P ^ (e + 1)) : ramificationIdx f p P ≠ 0 := by
  rwa [ramificationIdx_spec hle hnle]
  -- 🎉 no goals
#align ideal.ramification_idx_ne_zero Ideal.ramificationIdx_ne_zero

theorem le_pow_of_le_ramificationIdx {n : ℕ} (hn : n ≤ ramificationIdx f p P) :
    map f p ≤ P ^ n := by
  contrapose! hn
  -- ⊢ ramificationIdx f p P < n
  exact ramificationIdx_lt hn
  -- 🎉 no goals
#align ideal.le_pow_of_le_ramification_idx Ideal.le_pow_of_le_ramificationIdx

theorem le_pow_ramificationIdx : map f p ≤ P ^ ramificationIdx f p P :=
  le_pow_of_le_ramificationIdx (le_refl _)
#align ideal.le_pow_ramification_idx Ideal.le_pow_ramificationIdx

theorem le_comap_pow_ramificationIdx : p ≤ comap f (P ^ ramificationIdx f p P) :=
  map_le_iff_le_comap.mp le_pow_ramificationIdx
#align ideal.le_comap_pow_ramification_idx Ideal.le_comap_pow_ramificationIdx

theorem le_comap_of_ramificationIdx_ne_zero (h : ramificationIdx f p P ≠ 0) : p ≤ comap f P :=
  Ideal.map_le_iff_le_comap.mp <| le_pow_ramificationIdx.trans <| Ideal.pow_le_self <| h
#align ideal.le_comap_of_ramification_idx_ne_zero Ideal.le_comap_of_ramificationIdx_ne_zero

namespace IsDedekindDomain

variable [IsDomain S] [IsDedekindDomain S]

theorem ramificationIdx_eq_normalizedFactors_count (hp0 : map f p ≠ ⊥) (hP : P.IsPrime)
    (hP0 : P ≠ ⊥) : ramificationIdx f p P = (normalizedFactors (map f p)).count P := by
  have hPirr := (Ideal.prime_of_isPrime hP0 hP).irreducible
  -- ⊢ ramificationIdx f p P = Multiset.count P (normalizedFactors (map f p))
  refine ramificationIdx_spec (Ideal.le_of_dvd ?_) (mt Ideal.dvd_iff_le.mpr ?_) <;>
  -- ⊢ P ^ Multiset.count P (normalizedFactors (map f p)) ∣ map f p
    rw [dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hP0) hp0,
      normalizedFactors_pow, normalizedFactors_irreducible hPirr, normalize_eq,
      Multiset.nsmul_singleton, ← Multiset.le_count_iff_replicate_le]
  · exact (Nat.lt_succ_self _).not_le
    -- 🎉 no goals
#align ideal.is_dedekind_domain.ramification_idx_eq_normalized_factors_count Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count

theorem ramificationIdx_eq_factors_count (hp0 : map f p ≠ ⊥) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    ramificationIdx f p P = (factors (map f p)).count P := by
  rw [IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hp0 hP hP0,
    factors_eq_normalizedFactors]
#align ideal.is_dedekind_domain.ramification_idx_eq_factors_count Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count

theorem ramificationIdx_ne_zero (hp0 : map f p ≠ ⊥) (hP : P.IsPrime) (le : map f p ≤ P) :
    ramificationIdx f p P ≠ 0 := by
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    have := le_bot_iff.mp le
    contradiction
  have hPirr := (Ideal.prime_of_isPrime hP0 hP).irreducible
  -- ⊢ ramificationIdx f p P ≠ 0
  rw [IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hp0 hP hP0]
  -- ⊢ Multiset.count P (normalizedFactors (map f p)) ≠ 0
  obtain ⟨P', hP', P'_eq⟩ :=
    exists_mem_normalizedFactors_of_dvd hp0 hPirr (Ideal.dvd_iff_le.mpr le)
  rwa [Multiset.count_ne_zero, associated_iff_eq.mp P'_eq]
  -- 🎉 no goals
#align ideal.is_dedekind_domain.ramification_idx_ne_zero Ideal.IsDedekindDomain.ramificationIdx_ne_zero

end IsDedekindDomain

variable (f p P)

attribute [local instance] Ideal.Quotient.field

/-- The inertia degree of `P : Ideal S` lying over `p : Ideal R` is the degree of the
extension `(S / P) : (R / p)`.

We do not assume `P` lies over `p` in the definition; we return `0` instead.

See `inertiaDeg_algebraMap` for the common case where `f = algebraMap R S`
and there is an algebra structure `R / p → S / P`.
-/
noncomputable def inertiaDeg [p.IsMaximal] : ℕ :=
  if hPp : comap f P = p then
    @finrank (R ⧸ p) (S ⧸ P) _ _ <|
      @Algebra.toModule _ _ _ _ <|
        RingHom.toAlgebra <|
          Ideal.Quotient.lift p ((Ideal.Quotient.mk P).comp f) fun _ ha =>
            Quotient.eq_zero_iff_mem.mpr <| mem_comap.mp <| hPp.symm ▸ ha
  else 0
#align ideal.inertia_deg Ideal.inertiaDeg

-- Useful for the `nontriviality` tactic using `comap_eq_of_scalar_tower_quotient`.
@[simp]
theorem inertiaDeg_of_subsingleton [hp : p.IsMaximal] [hQ : Subsingleton (S ⧸ P)] :
    inertiaDeg f p P = 0 := by
  have := Ideal.Quotient.subsingleton_iff.mp hQ
  -- ⊢ inertiaDeg f p P = 0
  subst this
  -- ⊢ inertiaDeg f p ⊤ = 0
  exact dif_neg fun h => hp.ne_top <| h.symm.trans comap_top
  -- 🎉 no goals
#align ideal.inertia_deg_of_subsingleton Ideal.inertiaDeg_of_subsingleton

@[simp]
theorem inertiaDeg_algebraMap [Algebra R S] [Algebra (R ⧸ p) (S ⧸ P)]
    [IsScalarTower R (R ⧸ p) (S ⧸ P)] [hp : p.IsMaximal] :
    inertiaDeg (algebraMap R S) p P = finrank (R ⧸ p) (S ⧸ P) := by
  nontriviality S ⧸ P using inertiaDeg_of_subsingleton, finrank_zero_of_subsingleton
  -- ⊢ inertiaDeg (algebraMap R S) p P = finrank (R ⧸ p) (S ⧸ P)
  have := comap_eq_of_scalar_tower_quotient (algebraMap (R ⧸ p) (S ⧸ P)).injective
  -- ⊢ inertiaDeg (algebraMap R S) p P = finrank (R ⧸ p) (S ⧸ P)
  rw [inertiaDeg, dif_pos this]
  -- ⊢ finrank (R ⧸ p) (S ⧸ P) = finrank (R ⧸ p) (S ⧸ P)
  congr
  -- ⊢ RingHom.toAlgebra (Quotient.lift p (RingHom.comp (Quotient.mk P) (algebraMap …
  refine' Algebra.algebra_ext _ _ fun x' => Quotient.inductionOn' x' fun x => _
  -- ⊢ ↑(algebraMap (R ⧸ p) (S ⧸ P)) (Quotient.mk'' x) = ↑(algebraMap (R ⧸ p) (S ⧸  …
  change Ideal.Quotient.lift p _ _ (Ideal.Quotient.mk p x) = algebraMap _ _ (Ideal.Quotient.mk p x)
  -- ⊢ ↑(Quotient.lift p (RingHom.comp (Quotient.mk P) (algebraMap R S)) (_ : ∀ (x  …
  rw [Ideal.Quotient.lift_mk, ← Ideal.Quotient.algebraMap_eq P, ← IsScalarTower.algebraMap_eq,
    ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
#align ideal.inertia_deg_algebra_map Ideal.inertiaDeg_algebraMap

end DecEq

section FinrankQuotientMap

open scoped BigOperators

open scoped nonZeroDivisors

variable [Algebra R S]

variable {K : Type*} [Field K] [Algebra R K] [hRK : IsFractionRing R K]

variable {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L]

variable {V V' V'' : Type*}

variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

variable [AddCommGroup V'] [Module R V'] [Module S V'] [IsScalarTower R S V']

variable [AddCommGroup V''] [Module R V'']

variable (K)

/-- Let `V` be a vector space over `K = Frac(R)`, `S / R` a ring extension
and `V'` a module over `S`. If `b`, in the intersection `V''` of `V` and `V'`,
is linear independent over `S` in `V'`, then it is linear independent over `R` in `V`.

The statement we prove is actually slightly more general:
 * it suffices that the inclusion `algebraMap R S : R → S` is nontrivial
 * the function `f' : V'' → V'` doesn't need to be injective
-/
theorem FinrankQuotientMap.linearIndependent_of_nontrivial [IsDomain R] [IsDedekindDomain R]
    (hRS : RingHom.ker (algebraMap R S) ≠ ⊤) (f : V'' →ₗ[R] V) (hf : Function.Injective f)
    (f' : V'' →ₗ[R] V') {ι : Type*} {b : ι → V''} (hb' : LinearIndependent S (f' ∘ b)) :
    LinearIndependent K (f ∘ b) := by
  contrapose! hb' with hb
  -- ⊢ ¬LinearIndependent S (↑f' ∘ b)
  -- Informally, if we have a nontrivial linear dependence with coefficients `g` in `K`,
  -- then we can find a linear dependence with coefficients `I.Quotient.mk g'` in `R/I`,
  -- where `I = ker (algebraMap R S)`.
  -- We make use of the same principle but stay in `R` everywhere.
  simp only [linearIndependent_iff', not_forall] at hb ⊢
  -- ⊢ ∃ x x_1 h x_2 x, ¬x_1 x_2 = 0
  obtain ⟨s, g, eq, j', hj's, hj'g⟩ := hb
  -- ⊢ ∃ x x_1 h x_2 x, ¬x_1 x_2 = 0
  use s
  -- ⊢ ∃ x h x_1 x_2, ¬x x_1 = 0
  obtain ⟨a, hag, j, hjs, hgI⟩ := Ideal.exist_integer_multiples_not_mem hRS s g hj's hj'g
  -- ⊢ ∃ x h x_1 x_2, ¬x x_1 = 0
  choose g'' hg'' using hag
  -- ⊢ ∃ x h x_1 x_2, ¬x x_1 = 0
  letI := Classical.propDecidable
  -- ⊢ ∃ x h x_1 x_2, ¬x x_1 = 0
  let g' i := if h : i ∈ s then g'' i h else 0
  -- ⊢ ∃ x h x_1 x_2, ¬x x_1 = 0
  have hg' : ∀ i ∈ s, algebraMap _ _ (g' i) = a * g i := by
    intro i hi; exact (congr_arg _ (dif_pos hi)).trans (hg'' i hi)
  -- Because `R/I` is nontrivial, we can lift `g` to a nontrivial linear dependence in `S`.
  have hgI : algebraMap R S (g' j) ≠ 0 := by
    simp only [FractionalIdeal.mem_coeIdeal, not_exists, not_and'] at hgI
    exact hgI _ (hg' j hjs)
  refine ⟨fun i => algebraMap R S (g' i), ?_, j, hjs, hgI⟩
  -- ⊢ ∑ i in s, (fun i => ↑(algebraMap R S) (g' i)) i • (↑f' ∘ b) i = 0
  have eq : f (∑ i in s, g' i • b i) = 0 := by
    rw [LinearMap.map_sum, ← smul_zero a, ← eq, Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [LinearMap.map_smul, ← IsScalarTower.algebraMap_smul K, hg' i hi, ← smul_assoc,
      smul_eq_mul, Function.comp_apply]
  simp only [IsScalarTower.algebraMap_smul, ← LinearMap.map_smul, ← LinearMap.map_sum,
    (f.map_eq_zero_iff hf).mp eq, LinearMap.map_zero, (· ∘ ·)]
#align ideal.finrank_quotient_map.linear_independent_of_nontrivial Ideal.FinrankQuotientMap.linearIndependent_of_nontrivial

open scoped Matrix

variable {K}

/-- If `b` mod `p` spans `S/p` as `R/p`-space, then `b` itself spans `Frac(S)` as `K`-space.

Here,
 * `p` is an ideal of `R` such that `R / p` is nontrivial
 * `K` is a field that has an embedding of `R` (in particular we can take `K = Frac(R)`)
 * `L` is a field extension of `K`
 * `S` is the integral closure of `R` in `L`

More precisely, we avoid quotients in this statement and instead require that `b ∪ pS` spans `S`.
-/
theorem FinrankQuotientMap.span_eq_top [IsDomain R] [IsDomain S] [Algebra K L] [IsNoetherian R S]
    [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L] [IsIntegralClosure S R L]
    [NoZeroSMulDivisors R K] (hp : p ≠ ⊤) (b : Set S)
    (hb' : Submodule.span R b ⊔ (p.map (algebraMap R S)).restrictScalars R = ⊤) :
    Submodule.span K (algebraMap S L '' b) = ⊤ := by
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (NoZeroSMulDivisors.algebraMap_injective R K)
  -- Let `M` be the `R`-module spanned by the proposed basis elements.
  let M : Submodule R S := Submodule.span R b
  -- ⊢ Submodule.span K (↑(algebraMap S L) '' b) = ⊤
  -- Then `S / M` is generated by some finite set of `n` vectors `a`.
  letI h : Module.Finite R (S ⧸ M) :=
    Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.Quotient.mk_surjective _)
  obtain ⟨n, a, ha⟩ := @Module.Finite.exists_fin _ _ _ _ _ h
  -- ⊢ Submodule.span K (↑(algebraMap S L) '' b) = ⊤
  -- Because the image of `p` in `S / M` is `⊤`,
  have smul_top_eq : p • (⊤ : Submodule R (S ⧸ M)) = ⊤ := by
    calc
      p • ⊤ = Submodule.map M.mkQ (p • ⊤) := by
        rw [Submodule.map_smul'', Submodule.map_top, M.range_mkQ]
      _ = ⊤ := by rw [Ideal.smul_top_eq_map, (Submodule.map_mkQ_eq_top M _).mpr hb']
  -- we can write the elements of `a` as `p`-linear combinations of other elements of `a`.
  have exists_sum : ∀ x : S ⧸ M, ∃ a' : Fin n → R, (∀ i, a' i ∈ p) ∧ ∑ i, a' i • a i = x := by
    intro x
    obtain ⟨a'', ha'', hx⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum p a x).1
      (by { rw [ha, smul_top_eq]; exact Submodule.mem_top } :
        x ∈ p • Submodule.span R (Set.range a))
    · refine ⟨fun i => a'' i, fun i => ha'' _, ?_⟩
      rw [← hx, Finsupp.sum_fintype]
      exact fun _ => zero_smul _ _
  choose A' hA'p hA' using fun i => exists_sum (a i)
  -- ⊢ Submodule.span K (↑(algebraMap S L) '' b) = ⊤
  -- This gives us a(n invertible) matrix `A` such that `det A ∈ (M = span R b)`,
  let A : Matrix (Fin n) (Fin n) R := Matrix.of A' - 1
  -- ⊢ Submodule.span K (↑(algebraMap S L) '' b) = ⊤
  let B := A.adjugate
  -- ⊢ Submodule.span K (↑(algebraMap S L) '' b) = ⊤
  have A_smul : ∀ i, ∑ j, A i j • a j = 0 := by
    intros
    simp only [Matrix.sub_apply, Matrix.of_apply, ne_eq, Matrix.one_apply, sub_smul,
      Finset.sum_sub_distrib, hA', Finset.sum_univ_ite, sub_self]
  -- since `span S {det A} / M = 0`.
  have d_smul : ∀ i, A.det • a i = 0 := by
    intro i
    calc
      A.det • a i = ∑ j, (B * A) i j • a j := ?_
      _ = ∑ k, B i k • ∑ j, A k j • a j := ?_
      _ = 0 := Finset.sum_eq_zero fun k _ => ?_
    · simp only [Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, ite_true,
        mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ]
    · simp only [Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
      rw [Finset.sum_comm]
    · rw [A_smul, smul_zero]
  -- In the rings of integers we have the desired inclusion.
  have span_d : (Submodule.span S ({algebraMap R S A.det} : Set S)).restrictScalars R ≤ M := by
    intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    obtain ⟨x', rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [smul_eq_mul, mul_comm, ← Algebra.smul_def] at hx ⊢
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    obtain ⟨a', _, quot_x_eq⟩ := exists_sum (Submodule.Quotient.mk x')
    rw [← quot_x_eq, Finset.smul_sum]
    conv =>
      lhs; congr; next => skip
      intro x; rw [smul_comm A.det, d_smul, smul_zero]
    exact Finset.sum_const_zero
  refine top_le_iff.mp
      (calc
        ⊤ = (Ideal.span {algebraMap R L A.det}).restrictScalars K := ?_
        _ ≤ Submodule.span K (algebraMap S L '' b) := ?_)
  -- Because `det A ≠ 0`, we have `span L {det A} = ⊤`.
  · rw [eq_comm, Submodule.restrictScalars_eq_top_iff, Ideal.span_singleton_eq_top]
    -- ⊢ IsUnit (↑(algebraMap R L) (Matrix.det A))
    refine IsUnit.mk0 _ ((map_ne_zero_iff (algebraMap R L) hRL).mpr ?_)
    -- ⊢ Matrix.det A ≠ 0
    refine @ne_zero_of_map _ _ _ _ _ _ (Ideal.Quotient.mk p) _ ?_
    -- ⊢ ↑(Quotient.mk p) (Matrix.det A) ≠ 0
    haveI := Ideal.Quotient.nontrivial hp
    -- ⊢ ↑(Quotient.mk p) (Matrix.det A) ≠ 0
    calc
      Ideal.Quotient.mk p A.det = Matrix.det ((Ideal.Quotient.mk p).mapMatrix A) := by
        rw [RingHom.map_det, RingHom.mapMatrix_apply]
      _ = Matrix.det ((Ideal.Quotient.mk p).mapMatrix (Matrix.of A' - 1)) := rfl
      _ = Matrix.det fun i j =>
          (Ideal.Quotient.mk p) (A' i j) - (1 : Matrix (Fin n) (Fin n) (R ⧸ p)) i j := ?_
      _ = Matrix.det (-1 : Matrix (Fin n) (Fin n) (R ⧸ p)) := ?_
      _ = (-1 : R ⧸ p) ^ n := by rw [Matrix.det_neg, Fintype.card_fin, Matrix.det_one, mul_one]
      _ ≠ 0 := IsUnit.ne_zero (isUnit_one.neg.pow _)
    · refine congr_arg Matrix.det (Matrix.ext fun i j => ?_)
      -- ⊢ ↑(RingHom.mapMatrix (Quotient.mk p)) (↑Matrix.of A' - 1) i j = ↑(Quotient.mk …
      rw [map_sub, RingHom.mapMatrix_apply, map_one]
      -- ⊢ (Matrix.map (↑Matrix.of A') ↑(Quotient.mk p) - 1) i j = ↑(Quotient.mk p) (A' …
      rfl
      -- 🎉 no goals
    · refine congr_arg Matrix.det (Matrix.ext fun i j => ?_)
      -- ⊢ ↑(Quotient.mk p) (A' i j) - OfNat.ofNat 1 i j = (-1) i j
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hA'p i j), zero_sub]
      -- ⊢ -OfNat.ofNat 1 i j = (-1) i j
      rfl
      -- 🎉 no goals
  -- And we conclude `L = span L {det A} ≤ span K b`, so `span K b` spans everything.
  · intro x hx
    -- ⊢ x ∈ Submodule.span K (↑(algebraMap S L) '' b)
    rw [Submodule.restrictScalars_mem, IsScalarTower.algebraMap_apply R S L] at hx
    -- ⊢ x ∈ Submodule.span K (↑(algebraMap S L) '' b)
    refine' IsFractionRing.ideal_span_singleton_map_subset R _ hRL span_d hx
    -- ⊢ Algebra.IsAlgebraic R L
    haveI : NoZeroSMulDivisors R L := NoZeroSMulDivisors.of_algebraMap_injective hRL
    -- ⊢ Algebra.IsAlgebraic R L
    rw [← IsFractionRing.isAlgebraic_iff' R S]
    -- ⊢ Algebra.IsAlgebraic R S
    intro x
    -- ⊢ IsAlgebraic R x
    exact IsIntegral.isAlgebraic _ (isIntegral_of_noetherian inferInstance _)
    -- 🎉 no goals
#align ideal.finrank_quotient_map.span_eq_top Ideal.FinrankQuotientMap.span_eq_top

variable (K L)

/-- If `p` is a maximal ideal of `R`, and `S` is the integral closure of `R` in `L`,
then the dimension `[S/pS : R/p]` is equal to `[Frac(S) : Frac(R)]`. -/
theorem finrank_quotient_map [IsDomain R] [IsDomain S] [IsDedekindDomain R] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] [IsIntegralClosure S R L]
    [hp : p.IsMaximal] [IsNoetherian R S] :
    finrank (R ⧸ p) (S ⧸ map (algebraMap R S) p) = finrank K L := by
  -- Choose an arbitrary basis `b` for `[S/pS : R/p]`.
  -- We'll use the previous results to turn it into a basis on `[Frac(S) : Frac(R)]`.
  letI : Field (R ⧸ p) := Ideal.Quotient.field _
  -- ⊢ finrank (R ⧸ p) (S ⧸ map (algebraMap R S) p) = finrank K L
  let ι := Module.Free.ChooseBasisIndex (R ⧸ p) (S ⧸ map (algebraMap R S) p)
  -- ⊢ finrank (R ⧸ p) (S ⧸ map (algebraMap R S) p) = finrank K L
  let b : Basis ι (R ⧸ p) (S ⧸ map (algebraMap R S) p) := Module.Free.chooseBasis _ _
  -- ⊢ finrank (R ⧸ p) (S ⧸ map (algebraMap R S) p) = finrank K L
  -- Namely, choose a representative `b' i : S` for each `b i : S / pS`.
  let b' : ι → S := fun i => (Ideal.Quotient.mk_surjective (b i)).choose
  -- ⊢ finrank (R ⧸ p) (S ⧸ map (algebraMap R S) p) = finrank K L
  have b_eq_b' : ⇑b = (Submodule.mkQ (map (algebraMap R S) p)).restrictScalars R ∘ b' :=
    funext fun i => (Ideal.Quotient.mk_surjective (b i)).choose_spec.symm
  -- We claim `b'` is a basis for `Frac(S)` over `Frac(R)` because it is linear independent
  -- and spans the whole of `Frac(S)`.
  let b'' : ι → L := algebraMap S L ∘ b'
  -- ⊢ finrank (R ⧸ p) (S ⧸ map (algebraMap R S) p) = finrank K L
  have b''_li : LinearIndependent K b'' := ?_
  -- ⊢ finrank (R ⧸ p) (S ⧸ map (algebraMap R S) p) = finrank K L
  have b''_sp : Submodule.span K (Set.range b'') = ⊤ := ?_
  -- Since the two bases have the same index set, the spaces have the same dimension.
  let c : Basis ι K L := Basis.mk b''_li b''_sp.ge
  rw [finrank_eq_card_basis b, finrank_eq_card_basis c]
  -- ⊢ Submodule.span K (Set.range b'') = ⊤
  -- It remains to show that the basis is indeed linear independent and spans the whole space.
  · rw [Set.range_comp]
    -- ⊢ Submodule.span K (↑(algebraMap S L) '' Set.range b') = ⊤
    refine FinrankQuotientMap.span_eq_top p hp.ne_top _ (top_le_iff.mp ?_)
    -- ⊢ ⊤ ≤ Submodule.span R (Set.range b') ⊔ Submodule.restrictScalars R (map (alge …
    -- The nicest way to show `S ≤ span b' ⊔ pS` is by reducing both sides modulo pS.
    -- However, this would imply distinguishing between `pS` as `S`-ideal,
    -- and `pS` as `R`-submodule, since they have different (non-defeq) quotients.
    -- Instead we'll lift `x mod pS ∈ span b` to `y ∈ span b'` for some `y - x ∈ pS`.
    intro x _
    -- ⊢ x ∈ Submodule.span R (Set.range b') ⊔ Submodule.restrictScalars R (map (alge …
    have mem_span_b : ((Submodule.mkQ (map (algebraMap R S) p)) x : S ⧸ map (algebraMap R S) p) ∈
        Submodule.span (R ⧸ p) (Set.range b) := b.mem_span _
    rw [← @Submodule.restrictScalars_mem R,
      Submodule.restrictScalars_span R (R ⧸ p) Ideal.Quotient.mk_surjective, b_eq_b',
      Set.range_comp, ← Submodule.map_span] at mem_span_b
    obtain ⟨y, y_mem, y_eq⟩ := Submodule.mem_map.mp mem_span_b
    -- ⊢ x ∈ Submodule.span R (Set.range b') ⊔ Submodule.restrictScalars R (map (alge …
    suffices y + -(y - x) ∈ _ by simpa
    -- ⊢ y + -(y - x) ∈ Submodule.span R (Set.range fun i => Exists.choose (_ : ∃ a,  …
    rw [LinearMap.restrictScalars_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq] at y_eq
    exact add_mem (Submodule.mem_sup_left y_mem) (neg_mem <| Submodule.mem_sup_right y_eq)
    -- 🎉 no goals
  · have := b.linearIndependent; rw [b_eq_b'] at this
    -- ⊢ LinearIndependent K b''
                                 -- ⊢ LinearIndependent K b''
    convert FinrankQuotientMap.linearIndependent_of_nontrivial K _
        ((Algebra.linearMap S L).restrictScalars R) _ ((Submodule.mkQ _).restrictScalars R) this
    · rw [Quotient.algebraMap_eq, Ideal.mk_ker]
      -- ⊢ p ≠ ⊤
      exact hp.ne_top
      -- 🎉 no goals
    · exact IsFractionRing.injective S L
      -- 🎉 no goals
#align ideal.finrank_quotient_map Ideal.finrank_quotient_map

end FinrankQuotientMap

section FactLeComap

local notation "e" => ramificationIdx f p P

/-- `R / p` has a canonical map to `S / (P ^ e)`, where `e` is the ramification index
of `P` over `p`. -/
noncomputable instance Quotient.algebraQuotientPowRamificationIdx : Algebra (R ⧸ p) (S ⧸ P ^ e) :=
  Quotient.algebraQuotientOfLeComap (Ideal.map_le_iff_le_comap.mp le_pow_ramificationIdx)
#align ideal.quotient.algebra_quotient_pow_ramification_idx Ideal.Quotient.algebraQuotientPowRamificationIdx

@[simp]
theorem Quotient.algebraMap_quotient_pow_ramificationIdx (x : R) :
    algebraMap (R ⧸ p) (S ⧸ P ^ e) (Ideal.Quotient.mk p x) = Ideal.Quotient.mk _ (f x) := rfl
#align ideal.quotient.algebra_map_quotient_pow_ramification_idx Ideal.Quotient.algebraMap_quotient_pow_ramificationIdx

variable [hfp : NeZero (ramificationIdx f p P)]

/-- If `P` lies over `p`, then `R / p` has a canonical map to `S / P`.

This can't be an instance since the map `f : R → S` is generally not inferrable.
-/
def Quotient.algebraQuotientOfRamificationIdxNeZero : Algebra (R ⧸ p) (S ⧸ P) :=
  Quotient.algebraQuotientOfLeComap (le_comap_of_ramificationIdx_ne_zero hfp.out)
#align ideal.quotient.algebra_quotient_of_ramification_idx_ne_zero Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero

set_option synthInstance.checkSynthOrder false -- Porting note: this is okay by the remark below
-- In this file, the value for `f` can be inferred.
attribute [local instance] Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero

@[simp]
theorem Quotient.algebraMap_quotient_of_ramificationIdx_neZero (x : R) :
    algebraMap (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk p x) = Ideal.Quotient.mk _ (f x) := rfl
#align ideal.quotient.algebra_map_quotient_of_ramification_idx_ne_zero Ideal.Quotient.algebraMap_quotient_of_ramificationIdx_neZero

/-- The inclusion `(P^(i + 1) / P^e) ⊂ (P^i / P^e)`. -/
@[simps]
def powQuotSuccInclusion (i : ℕ) :
    Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (i + 1)) →ₗ[R ⧸ p]
    Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ i) where
  toFun x := ⟨x, Ideal.map_mono (Ideal.pow_le_pow i.le_succ) x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align ideal.pow_quot_succ_inclusion Ideal.powQuotSuccInclusion

theorem powQuotSuccInclusion_injective (i : ℕ) :
    Function.Injective (powQuotSuccInclusion f p P i) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  -- ⊢ ∀ (m : { x // x ∈ map (Quotient.mk (P ^ e)) (P ^ (i + 1)) }), ↑(powQuotSuccI …
  rintro ⟨x, hx⟩ hx0
  -- ⊢ { val := x, property := hx } = 0
  rw [Subtype.ext_iff] at hx0 ⊢
  -- ⊢ ↑{ val := x, property := hx } = ↑0
  rwa [powQuotSuccInclusion_apply_coe] at hx0
  -- 🎉 no goals
#align ideal.pow_quot_succ_inclusion_injective Ideal.powQuotSuccInclusion_injective

/-- `S ⧸ P` embeds into the quotient by `P^(i+1) ⧸ P^e` as a subspace of `P^i ⧸ P^e`.
See `quotientToQuotientRangePowQuotSucc` for this as a linear map,
and `quotientRangePowQuotSuccInclusionEquiv` for this as a linear equivalence.
-/
noncomputable def quotientToQuotientRangePowQuotSuccAux {i : ℕ} {a : S} (a_mem : a ∈ P ^ i) :
    S ⧸ P →
      (P ^ i).map (Ideal.Quotient.mk (P ^ e)) ⧸ LinearMap.range (powQuotSuccInclusion f p P i) :=
  Quotient.map' (fun x : S => ⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ x a_mem)⟩)
    fun x y h => by
    rw [Submodule.quotientRel_r_def] at h ⊢
    -- ⊢ (fun x => { val := ↑(Quotient.mk (P ^ e)) (x * a), property := (_ : ↑(Quotie …
    simp only [_root_.map_mul, LinearMap.mem_range]
    -- ⊢ ∃ y_1, ↑(powQuotSuccInclusion f p P i) y_1 = { val := ↑(Quotient.mk (P ^ e)) …
    refine' ⟨⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_mul h a_mem)⟩, _⟩
    -- ⊢ ↑(powQuotSuccInclusion f p P i) { val := ↑(Quotient.mk (P ^ e)) ((x - y) * a …
    ext
    -- ⊢ ↑(↑(powQuotSuccInclusion f p P i) { val := ↑(Quotient.mk (P ^ e)) ((x - y) * …
    rw [powQuotSuccInclusion_apply_coe, Subtype.coe_mk, Submodule.coe_sub, Subtype.coe_mk,
      Subtype.coe_mk, _root_.map_mul, map_sub, sub_mul]
#align ideal.quotient_to_quotient_range_pow_quot_succ_aux Ideal.quotientToQuotientRangePowQuotSuccAux

theorem quotientToQuotientRangePowQuotSuccAux_mk {i : ℕ} {a : S} (a_mem : a ∈ P ^ i) (x : S) :
    quotientToQuotientRangePowQuotSuccAux f p P a_mem (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ x a_mem)⟩ :=
  by apply Quotient.map'_mk''
     -- 🎉 no goals
#align ideal.quotient_to_quotient_range_pow_quot_succ_aux_mk Ideal.quotientToQuotientRangePowQuotSuccAux_mk

/-- `S ⧸ P` embeds into the quotient by `P^(i+1) ⧸ P^e` as a subspace of `P^i ⧸ P^e`. -/
noncomputable def quotientToQuotientRangePowQuotSucc {i : ℕ} {a : S} (a_mem : a ∈ P ^ i) :
    S ⧸ P →ₗ[R ⧸ p]
      (P ^ i).map (Ideal.Quotient.mk (P ^ e)) ⧸ LinearMap.range (powQuotSuccInclusion f p P i) where
  toFun := quotientToQuotientRangePowQuotSuccAux f p P a_mem
  map_add' := by
    intro x y; refine' Quotient.inductionOn' x fun x => Quotient.inductionOn' y fun y => _
    -- ⊢ quotientToQuotientRangePowQuotSuccAux f p P a_mem (x + y) = quotientToQuotie …
               -- ⊢ quotientToQuotientRangePowQuotSuccAux f p P a_mem (Quotient.mk'' x + Quotien …
    simp only [Submodule.Quotient.mk''_eq_mk, ← Submodule.Quotient.mk_add,
      quotientToQuotientRangePowQuotSuccAux_mk, add_mul]
    exact congr_arg Submodule.Quotient.mk rfl
    -- 🎉 no goals
  map_smul' := by
    intro x y; refine' Quotient.inductionOn' x fun x => Quotient.inductionOn' y fun y => _
    -- ⊢ AddHom.toFun { toFun := quotientToQuotientRangePowQuotSuccAux f p P a_mem, m …
               -- ⊢ AddHom.toFun { toFun := quotientToQuotientRangePowQuotSuccAux f p P a_mem, m …
    simp only [Submodule.Quotient.mk''_eq_mk, RingHom.id_apply,
      quotientToQuotientRangePowQuotSuccAux_mk]
    refine congr_arg Submodule.Quotient.mk ?_
    -- ⊢ (fun x => { val := ↑(Quotient.mk (P ^ e)) (x * a), property := (_ : ↑(Quotie …
    ext
    -- ⊢ ↑((fun x => { val := ↑(Quotient.mk (P ^ e)) (x * a), property := (_ : ↑(Quot …
    simp only [mul_assoc, _root_.map_mul, Quotient.mk_eq_mk, Submodule.coe_smul_of_tower,
      Algebra.smul_def, Quotient.algebraMap_quotient_pow_ramificationIdx]
#align ideal.quotient_to_quotient_range_pow_quot_succ Ideal.quotientToQuotientRangePowQuotSucc

theorem quotientToQuotientRangePowQuotSucc_mk {i : ℕ} {a : S} (a_mem : a ∈ P ^ i) (x : S) :
    quotientToQuotientRangePowQuotSucc f p P a_mem (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ x a_mem)⟩ :=
  quotientToQuotientRangePowQuotSuccAux_mk f p P a_mem x
#align ideal.quotient_to_quotient_range_pow_quot_succ_mk Ideal.quotientToQuotientRangePowQuotSucc_mk

theorem quotientToQuotientRangePowQuotSucc_injective [IsDomain S] [IsDedekindDomain S] [P.IsPrime]
    {i : ℕ} (hi : i < e) {a : S} (a_mem : a ∈ P ^ i) (a_not_mem : a ∉ P ^ (i + 1)) :
    Function.Injective (quotientToQuotientRangePowQuotSucc f p P a_mem) := fun x =>
  Quotient.inductionOn' x fun x y =>
    Quotient.inductionOn' y fun y h => by
      have Pe_le_Pi1 : P ^ e ≤ P ^ (i + 1) := Ideal.pow_le_pow hi
      -- ⊢ Quotient.mk'' x = Quotient.mk'' y
      simp only [Submodule.Quotient.mk''_eq_mk, quotientToQuotientRangePowQuotSucc_mk,
        Submodule.Quotient.eq, LinearMap.mem_range, Subtype.ext_iff, Subtype.coe_mk,
        Submodule.coe_sub] at h ⊢
      rcases h with ⟨⟨⟨z⟩, hz⟩, h⟩
      -- ⊢ x - y ∈ P
      rw [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk, Ideal.mem_quotient_iff_mem_sup,
        sup_eq_left.mpr Pe_le_Pi1] at hz
      rw [powQuotSuccInclusion_apply_coe, Subtype.coe_mk, Submodule.Quotient.quot_mk_eq_mk,
        Ideal.Quotient.mk_eq_mk, ← map_sub, Ideal.Quotient.eq, ← sub_mul] at h
      exact
        (Ideal.IsPrime.mul_mem_pow _
              ((Submodule.sub_mem_iff_right _ hz).mp (Pe_le_Pi1 h))).resolve_right
          a_not_mem
#align ideal.quotient_to_quotient_range_pow_quot_succ_injective Ideal.quotientToQuotientRangePowQuotSucc_injective

theorem quotientToQuotientRangePowQuotSucc_surjective [IsDomain S] [IsDedekindDomain S]
    (hP0 : P ≠ ⊥) [hP : P.IsPrime] {i : ℕ} (hi : i < e) {a : S} (a_mem : a ∈ P ^ i)
    (a_not_mem : a ∉ P ^ (i + 1)) :
    Function.Surjective (quotientToQuotientRangePowQuotSucc f p P a_mem) := by
  rintro ⟨⟨⟨x⟩, hx⟩⟩
  -- ⊢ ∃ a_1, ↑(quotientToQuotientRangePowQuotSucc f p P a_mem) a_1 = Quot.mk Setoi …
  have Pe_le_Pi : P ^ e ≤ P ^ i := Ideal.pow_le_pow hi.le
  -- ⊢ ∃ a_1, ↑(quotientToQuotientRangePowQuotSucc f p P a_mem) a_1 = Quot.mk Setoi …
  rw [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk, Ideal.mem_quotient_iff_mem_sup,
    sup_eq_left.mpr Pe_le_Pi] at hx
  suffices hx' : x ∈ Ideal.span {a} ⊔ P ^ (i + 1)
  -- ⊢ ∃ a_1, ↑(quotientToQuotientRangePowQuotSucc f p P a_mem) a_1 = Quot.mk Setoi …
  · obtain ⟨y', hy', z, hz, rfl⟩ := Submodule.mem_sup.mp hx'
    -- ⊢ ∃ a_1, ↑(quotientToQuotientRangePowQuotSucc f p P a_mem) a_1 = Quot.mk Setoi …
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hy'
    -- ⊢ ∃ a_1, ↑(quotientToQuotientRangePowQuotSucc f p P a_mem) a_1 = Quot.mk Setoi …
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    -- ⊢ ↑(quotientToQuotientRangePowQuotSucc f p P a_mem) (Submodule.Quotient.mk y)  …
    simp only [Submodule.Quotient.quot_mk_eq_mk, quotientToQuotientRangePowQuotSucc_mk,
      Submodule.Quotient.eq, LinearMap.mem_range, Subtype.ext_iff, Subtype.coe_mk,
      Submodule.coe_sub]
    refine ⟨⟨_, Ideal.mem_map_of_mem _ (Submodule.neg_mem _ hz)⟩, ?_⟩
    -- ⊢ ↑(↑(powQuotSuccInclusion f p P i) { val := ↑(Quotient.mk (P ^ e)) (-z), prop …
    rw [powQuotSuccInclusion_apply_coe, Subtype.coe_mk, Ideal.Quotient.mk_eq_mk, map_add,
      mul_comm y a, sub_add_cancel', map_neg]
  letI := Classical.decEq (Ideal S)
  -- ⊢ x ∈ span {a} ⊔ P ^ (i + 1)
  rw [sup_eq_prod_inf_factors _ (pow_ne_zero _ hP0), normalizedFactors_pow,
    normalizedFactors_irreducible ((Ideal.prime_iff_isPrime hP0).mpr hP).irreducible, normalize_eq,
    Multiset.nsmul_singleton, Multiset.inter_replicate, Multiset.prod_replicate]
  rw [← Submodule.span_singleton_le_iff_mem, Ideal.submodule_span_eq] at a_mem a_not_mem
  -- ⊢ x ∈ P ^ min (Multiset.count P (normalizedFactors (span {a}))) (i + 1)
  rwa [Ideal.count_normalizedFactors_eq a_mem a_not_mem, min_eq_left i.le_succ]
  -- ⊢ span {a} ≠ ⊥
  · intro ha
    -- ⊢ False
    rw [Ideal.span_singleton_eq_bot.mp ha] at a_not_mem
    -- ⊢ False
    have := (P ^ (i + 1)).zero_mem
    -- ⊢ False
    contradiction
    -- 🎉 no goals
#align ideal.quotient_to_quotient_range_pow_quot_succ_surjective Ideal.quotientToQuotientRangePowQuotSucc_surjective

/-- Quotienting `P^i / P^e` by its subspace `P^(i+1) ⧸ P^e` is
`R ⧸ p`-linearly isomorphic to `S ⧸ P`. -/
noncomputable def quotientRangePowQuotSuccInclusionEquiv [IsDomain S] [IsDedekindDomain S]
    [P.IsPrime] (hP : P ≠ ⊥) {i : ℕ} (hi : i < e) :
    ((P ^ i).map (Ideal.Quotient.mk (P ^ e)) ⧸ LinearMap.range (powQuotSuccInclusion f p P i))
      ≃ₗ[R ⧸ p] S ⧸ P := by
  choose a a_mem a_not_mem using
    SetLike.exists_of_lt
      (Ideal.strictAnti_pow P hP (Ideal.IsPrime.ne_top inferInstance) (le_refl i.succ))
  refine' (LinearEquiv.ofBijective _ ⟨_, _⟩).symm
  · exact quotientToQuotientRangePowQuotSucc f p P a_mem
    -- 🎉 no goals
  · exact quotientToQuotientRangePowQuotSucc_injective f p P hi a_mem a_not_mem
    -- 🎉 no goals
  · exact quotientToQuotientRangePowQuotSucc_surjective f p P hP hi a_mem a_not_mem
    -- 🎉 no goals
#align ideal.quotient_range_pow_quot_succ_inclusion_equiv Ideal.quotientRangePowQuotSuccInclusionEquiv

/-- Since the inclusion `(P^(i + 1) / P^e) ⊂ (P^i / P^e)` has a kernel isomorphic to `P / S`,
`[P^i / P^e : R / p] = [P^(i+1) / P^e : R / p] + [P / S : R / p]` -/
theorem rank_pow_quot_aux [IsDomain S] [IsDedekindDomain S] [p.IsMaximal] [P.IsPrime] (hP0 : P ≠ ⊥)
    {i : ℕ} (hi : i < e) :
    Module.rank (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ i)) =
      Module.rank (R ⧸ p) (S ⧸ P) +
        Module.rank (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (i + 1))) := by
  letI : Field (R ⧸ p) := Ideal.Quotient.field _
  -- ⊢ Module.rank (R ⧸ p) { x // x ∈ map (Quotient.mk (P ^ e)) (P ^ i) } = Module. …
  rw [← rank_range_of_injective _ (powQuotSuccInclusion_injective f p P i),
    (quotientRangePowQuotSuccInclusionEquiv f p P hP0 hi).symm.rank_eq]
  exact (rank_quotient_add_rank (LinearMap.range (powQuotSuccInclusion f p P i))).symm
  -- 🎉 no goals
#align ideal.rank_pow_quot_aux Ideal.rank_pow_quot_aux

theorem rank_pow_quot [IsDomain S] [IsDedekindDomain S] [p.IsMaximal] [P.IsPrime] (hP0 : P ≠ ⊥)
    (i : ℕ) (hi : i ≤ e) :
    Module.rank (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ i)) =
      (e - i) • Module.rank (R ⧸ p) (S ⧸ P) := by
-- Porting note: Lean cannot figure out what to prove by itself
  let Q : ℕ → Prop :=
    fun i => Module.rank (R ⧸ p) { x // x ∈ map (Quotient.mk (P ^ e)) (P ^ i) }
      = (e - i) • Module.rank (R ⧸ p) (S ⧸ P)
  refine @Nat.decreasingInduction' Q i e (fun j lt_e _le_j ih => ?_) hi ?_
  -- ⊢ Q j
  · dsimp only
    -- ⊢ Module.rank (R ⧸ p) { x // x ∈ map (Quotient.mk (P ^ e)) (P ^ j) } = (e - j) …
    rw [rank_pow_quot_aux f p P _ lt_e, ih, ← succ_nsmul, Nat.sub_succ, ← Nat.succ_eq_add_one,
      Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt lt_e)]
    assumption
    -- 🎉 no goals
  · dsimp only
    -- ⊢ Module.rank (R ⧸ p) { x // x ∈ map (Quotient.mk (P ^ e)) (P ^ e) } = (e - e) …
    rw [Nat.sub_self, zero_nsmul, map_quotient_self]
    -- ⊢ Module.rank (R ⧸ p) { x // x ∈ ⊥ } = 0
    exact rank_bot (R ⧸ p) (S ⧸ P ^ e)
    -- 🎉 no goals
#align ideal.rank_pow_quot Ideal.rank_pow_quot

/-- If `p` is a maximal ideal of `R`, `S` extends `R` and `P^e` lies over `p`,
then the dimension `[S/(P^e) : R/p]` is equal to `e * [S/P : R/p]`. -/
theorem rank_prime_pow_ramificationIdx [IsDomain S] [IsDedekindDomain S] [p.IsMaximal] [P.IsPrime]
    (hP0 : P ≠ ⊥) (he : e ≠ 0) :
    Module.rank (R ⧸ p) (S ⧸ P ^ e) =
      e •
        @Module.rank (R ⧸ p) (S ⧸ P) _ _
          (@Algebra.toModule _ _ _ _ <|
            @Quotient.algebraQuotientOfRamificationIdxNeZero _ _ _ _ _ _ _ ⟨he⟩) := by
  letI : NeZero e := ⟨he⟩
  -- ⊢ Module.rank (R ⧸ p) (S ⧸ P ^ e) = e • Module.rank (R ⧸ p) (S ⧸ P)
  have := rank_pow_quot f p P hP0 0 (Nat.zero_le e)
  -- ⊢ Module.rank (R ⧸ p) (S ⧸ P ^ e) = e • Module.rank (R ⧸ p) (S ⧸ P)
  rw [pow_zero, Nat.sub_zero, Ideal.one_eq_top, Ideal.map_top] at this
  -- ⊢ Module.rank (R ⧸ p) (S ⧸ P ^ e) = e • Module.rank (R ⧸ p) (S ⧸ P)
  exact (rank_top (R ⧸ p) _).symm.trans this
  -- 🎉 no goals
#align ideal.rank_prime_pow_ramification_idx Ideal.rank_prime_pow_ramificationIdx

/-- If `p` is a maximal ideal of `R`, `S` extends `R` and `P^e` lies over `p`,
then the dimension `[S/(P^e) : R/p]`, as a natural number, is equal to `e * [S/P : R/p]`. -/
theorem finrank_prime_pow_ramificationIdx [IsDomain S] [IsDedekindDomain S] (hP0 : P ≠ ⊥)
    [p.IsMaximal] [P.IsPrime] (he : e ≠ 0) :
    finrank (R ⧸ p) (S ⧸ P ^ e) =
      e *
        @finrank (R ⧸ p) (S ⧸ P) _ _
          (@Algebra.toModule _ _ _ _ <|
            @Quotient.algebraQuotientOfRamificationIdxNeZero _ _ _ _ _ _ _ ⟨he⟩) := by
  letI : NeZero e := ⟨he⟩
  -- ⊢ finrank (R ⧸ p) (S ⧸ P ^ e) = e * finrank (R ⧸ p) (S ⧸ P)
  letI : Algebra (R ⧸ p) (S ⧸ P) := Quotient.algebraQuotientOfRamificationIdxNeZero f p P
  -- ⊢ finrank (R ⧸ p) (S ⧸ P ^ e) = e * finrank (R ⧸ p) (S ⧸ P)
  letI := Ideal.Quotient.field p
  -- ⊢ finrank (R ⧸ p) (S ⧸ P ^ e) = e * finrank (R ⧸ p) (S ⧸ P)
  have hdim := rank_prime_pow_ramificationIdx _ _ _ hP0 he
  -- ⊢ finrank (R ⧸ p) (S ⧸ P ^ e) = e * finrank (R ⧸ p) (S ⧸ P)
  by_cases hP : FiniteDimensional (R ⧸ p) (S ⧸ P)
  -- ⊢ finrank (R ⧸ p) (S ⧸ P ^ e) = e * finrank (R ⧸ p) (S ⧸ P)
  · haveI := hP
    -- ⊢ finrank (R ⧸ p) (S ⧸ P ^ e) = e * finrank (R ⧸ p) (S ⧸ P)
    haveI := (finiteDimensional_iff_of_rank_eq_nsmul he hdim).mpr hP
    -- ⊢ finrank (R ⧸ p) (S ⧸ P ^ e) = e * finrank (R ⧸ p) (S ⧸ P)
    refine' Cardinal.natCast_injective _
    -- ⊢ ↑(finrank (R ⧸ p) (S ⧸ P ^ e)) = ↑(e * finrank (R ⧸ p) (S ⧸ P))
    rw [finrank_eq_rank', Nat.cast_mul, finrank_eq_rank', hdim, nsmul_eq_mul]
    -- 🎉 no goals
  have hPe := mt (finiteDimensional_iff_of_rank_eq_nsmul he hdim).mp hP
  -- ⊢ finrank (R ⧸ p) (S ⧸ P ^ e) = e * finrank (R ⧸ p) (S ⧸ P)
  simp only [finrank_of_infinite_dimensional hP, finrank_of_infinite_dimensional hPe,
    mul_zero]
#align ideal.finrank_prime_pow_ramification_idx Ideal.finrank_prime_pow_ramificationIdx

end FactLeComap

section FactorsMap

open scoped Classical

/-! ## Properties of the factors of `p.map (algebraMap R S)` -/


variable [IsDomain S] [IsDedekindDomain S] [Algebra R S]

theorem Factors.ne_bot (P : (factors (map (algebraMap R S) p)).toFinset) : (P : Ideal S) ≠ ⊥ :=
  (prime_of_factor _ (Multiset.mem_toFinset.mp P.2)).ne_zero
#align ideal.factors.ne_bot Ideal.Factors.ne_bot

instance Factors.isPrime (P : (factors (map (algebraMap R S) p)).toFinset) :
    IsPrime (P : Ideal S) :=
  Ideal.isPrime_of_prime (prime_of_factor _ (Multiset.mem_toFinset.mp P.2))
#align ideal.factors.is_prime Ideal.Factors.isPrime

theorem Factors.ramificationIdx_ne_zero (P : (factors (map (algebraMap R S) p)).toFinset) :
    ramificationIdx (algebraMap R S) p P ≠ 0 :=
  IsDedekindDomain.ramificationIdx_ne_zero (ne_zero_of_mem_factors (Multiset.mem_toFinset.mp P.2))
    (Factors.isPrime p P) (Ideal.le_of_dvd (dvd_of_mem_factors (Multiset.mem_toFinset.mp P.2)))
#align ideal.factors.ramification_idx_ne_zero Ideal.Factors.ramificationIdx_ne_zero

instance Factors.fact_ramificationIdx_neZero (P : (factors (map (algebraMap R S) p)).toFinset) :
    NeZero (ramificationIdx (algebraMap R S) p P) :=
  ⟨Factors.ramificationIdx_ne_zero p P⟩
#align ideal.factors.fact_ramification_idx_ne_zero Ideal.Factors.fact_ramificationIdx_neZero

set_option synthInstance.checkSynthOrder false
-- Porting note: this is okay since, as noted above, in this file the value of `f` can be inferred
attribute [local instance] Quotient.algebraQuotientOfRamificationIdxNeZero

instance Factors.isScalarTower (P : (factors (map (algebraMap R S) p)).toFinset) :
    IsScalarTower R (R ⧸ p) (S ⧸ (P : Ideal S)) :=
  IsScalarTower.of_algebraMap_eq fun x => by simp
                                             -- 🎉 no goals
#align ideal.factors.is_scalar_tower Ideal.Factors.isScalarTower

attribute [local instance] Ideal.Quotient.field

theorem Factors.finrank_pow_ramificationIdx [p.IsMaximal]
    (P : (factors (map (algebraMap R S) p)).toFinset) :
    finrank (R ⧸ p) (S ⧸ (P : Ideal S) ^ ramificationIdx (algebraMap R S) p P) =
      ramificationIdx (algebraMap R S) p P * inertiaDeg (algebraMap R S) p P := by
  rw [finrank_prime_pow_ramificationIdx, inertiaDeg_algebraMap]
  exacts [NeZero.ne _, Factors.ne_bot p P]
  -- 🎉 no goals
#align ideal.factors.finrank_pow_ramification_idx Ideal.Factors.finrank_pow_ramificationIdx

instance Factors.finiteDimensional_quotient [IsNoetherian R S] [p.IsMaximal]
    (P : (factors (map (algebraMap R S) p)).toFinset) :
    FiniteDimensional (R ⧸ p) (S ⧸ (P : Ideal S)) :=
  IsNoetherian.iff_fg.mp <|
    isNoetherian_of_tower R <|
      isNoetherian_of_surjective S (Ideal.Quotient.mkₐ _ _).toLinearMap <|
        LinearMap.range_eq_top.mpr Ideal.Quotient.mk_surjective
#align ideal.factors.finite_dimensional_quotient Ideal.Factors.finiteDimensional_quotient

theorem Factors.inertiaDeg_ne_zero [IsNoetherian R S] [p.IsMaximal]
    (P : (factors (map (algebraMap R S) p)).toFinset) : inertiaDeg (algebraMap R S) p P ≠ 0 := by
  rw [inertiaDeg_algebraMap]; exact (FiniteDimensional.finrank_pos_iff.mpr inferInstance).ne'
  -- ⊢ finrank (R ⧸ p) (S ⧸ ↑P) ≠ 0
                              -- 🎉 no goals
#align ideal.factors.inertia_deg_ne_zero Ideal.Factors.inertiaDeg_ne_zero

instance Factors.finiteDimensional_quotient_pow [IsNoetherian R S] [p.IsMaximal]
    (P : (factors (map (algebraMap R S) p)).toFinset) :
    FiniteDimensional (R ⧸ p) (S ⧸ (P : Ideal S) ^ ramificationIdx (algebraMap R S) p P) := by
  refine FiniteDimensional.finiteDimensional_of_finrank ?_
  -- ⊢ 0 < finrank (R ⧸ p) (S ⧸ ↑P ^ ramificationIdx (algebraMap R S) p ↑P)
  rw [pos_iff_ne_zero, Factors.finrank_pow_ramificationIdx]
  -- ⊢ ramificationIdx (algebraMap R S) p ↑P * inertiaDeg (algebraMap R S) p ↑P ≠ 0
  exact mul_ne_zero (Factors.ramificationIdx_ne_zero p P) (Factors.inertiaDeg_ne_zero p P)
  -- 🎉 no goals
#align ideal.factors.finite_dimensional_quotient_pow Ideal.Factors.finiteDimensional_quotient_pow

universe w

/-- **Chinese remainder theorem** for a ring of integers: if the prime ideal `p : Ideal R`
factors in `S` as `∏ i, P i ^ e i`, then `S ⧸ I` factors as `Π i, R ⧸ (P i ^ e i)`. -/
noncomputable def Factors.piQuotientEquiv (p : Ideal R) (hp : map (algebraMap R S) p ≠ ⊥) :
    S ⧸ map (algebraMap R S) p ≃+*
      ∀ P : (factors (map (algebraMap R S) p)).toFinset,
        S ⧸ (P : Ideal S) ^ ramificationIdx (algebraMap R S) p P :=
  (IsDedekindDomain.quotientEquivPiFactors hp).trans <|
    @RingEquiv.piCongrRight (factors (map (algebraMap R S) p)).toFinset
      (fun P => S ⧸ (P : Ideal S) ^ (factors (map (algebraMap R S) p)).count (P : Ideal S))
      (fun P => S ⧸ (P : Ideal S) ^ ramificationIdx (algebraMap R S) p P) _ _
      fun P : (factors (map (algebraMap R S) p)).toFinset =>
      Ideal.quotEquivOfEq <| by
        rw [IsDedekindDomain.ramificationIdx_eq_factors_count hp (Factors.isPrime p P)
            (Factors.ne_bot p P)]
#align ideal.factors.pi_quotient_equiv Ideal.Factors.piQuotientEquiv

@[simp]
theorem Factors.piQuotientEquiv_mk (p : Ideal R) (hp : map (algebraMap R S) p ≠ ⊥) (x : S) :
    Factors.piQuotientEquiv p hp (Ideal.Quotient.mk _ x) = fun _ => Ideal.Quotient.mk _ x := rfl
#align ideal.factors.pi_quotient_equiv_mk Ideal.Factors.piQuotientEquiv_mk

@[simp]
theorem Factors.piQuotientEquiv_map (p : Ideal R) (hp : map (algebraMap R S) p ≠ ⊥) (x : R) :
    Factors.piQuotientEquiv p hp (algebraMap _ _ x) = fun _ =>
      Ideal.Quotient.mk _ (algebraMap _ _ x) := rfl
#align ideal.factors.pi_quotient_equiv_map Ideal.Factors.piQuotientEquiv_map

variable (S)

/-- **Chinese remainder theorem** for a ring of integers: if the prime ideal `p : Ideal R`
factors in `S` as `∏ i, P i ^ e i`,
then `S ⧸ I` factors `R ⧸ I`-linearly as `Π i, R ⧸ (P i ^ e i)`. -/
noncomputable def Factors.piQuotientLinearEquiv (p : Ideal R) (hp : map (algebraMap R S) p ≠ ⊥) :
    (S ⧸ map (algebraMap R S) p) ≃ₗ[R ⧸ p]
      ∀ P : (factors (map (algebraMap R S) p)).toFinset,
        S ⧸ (P : Ideal S) ^ ramificationIdx (algebraMap R S) p P :=
  { Factors.piQuotientEquiv p hp with
    map_smul' := by
      rintro ⟨c⟩ ⟨x⟩; ext P
      -- ⊢ AddHom.toFun { toFun := src✝.toFun, map_add' := (_ : ∀ (x y : S ⧸ map (algeb …
                      -- ⊢ AddHom.toFun { toFun := src✝.toFun, map_add' := (_ : ∀ (x y : S ⧸ map (algeb …
      simp only [Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk, Algebra.smul_def,
        Quotient.algebraMap_quotient_map_quotient, Quotient.mk_algebraMap,
        RingHomCompTriple.comp_apply, Pi.mul_apply, Pi.algebraMap_apply]
      congr }
      -- 🎉 no goals
#align ideal.factors.pi_quotient_linear_equiv Ideal.Factors.piQuotientLinearEquiv

variable {S}

open scoped BigOperators

/-- The **fundamental identity** of ramification index `e` and inertia degree `f`:
for `P` ranging over the primes lying over `p`, `∑ P, e P * f P = [Frac(S) : Frac(R)]`;
here `S` is a finite `R`-module (and thus `Frac(S) : Frac(R)` is a finite extension) and `p`
is maximal.
-/
theorem sum_ramification_inertia (K L : Type*) [Field K] [Field L] [IsDomain R]
    [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L] [IsNoetherian R S]
    [IsIntegralClosure S R L] [p.IsMaximal] (hp0 : p ≠ ⊥) :
    (∑ P in (factors (map (algebraMap R S) p)).toFinset,
        ramificationIdx (algebraMap R S) p P * inertiaDeg (algebraMap R S) p P) =
      finrank K L := by
  set e := ramificationIdx (algebraMap R S) p
  -- ⊢ ∑ P in Multiset.toFinset (factors (map (algebraMap R S) p)), e P * inertiaDe …
  set f := inertiaDeg (algebraMap R S) p
  -- ⊢ ∑ P in Multiset.toFinset (factors (map (algebraMap R S) p)), e P * f P = fin …
  have inj_RL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L, RingHom.coe_comp]
    exact (RingHom.injective _).comp (IsFractionRing.injective R K)
  have inj_RS : Function.Injective (algebraMap R S) := by
    refine Function.Injective.of_comp (show Function.Injective (algebraMap S L ∘ _) from ?_)
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
    exact inj_RL
  calc
    (∑ P in (factors (map (algebraMap R S) p)).toFinset, e P * f P) =
        ∑ P in (factors (map (algebraMap R S) p)).toFinset.attach,
          finrank (R ⧸ p) (S ⧸ (P : Ideal S) ^ e P) := ?_
    _ = finrank (R ⧸ p)
          (∀ P : (factors (map (algebraMap R S) p)).toFinset, S ⧸ (P : Ideal S) ^ e P) :=
      (finrank_pi_fintype (R ⧸ p)).symm
    _ = finrank (R ⧸ p) (S ⧸ map (algebraMap R S) p) := ?_
    _ = finrank K L := ?_
  · rw [← Finset.sum_attach]
    -- ⊢ ∑ x in Finset.attach (Multiset.toFinset (factors (map (algebraMap R S) p))), …
    refine Finset.sum_congr rfl fun P _ => ?_
    -- ⊢ e ↑P * f ↑P = finrank (R ⧸ p) (S ⧸ ↑P ^ e ↑P)
    rw [Factors.finrank_pow_ramificationIdx]
    -- 🎉 no goals
  · refine LinearEquiv.finrank_eq (Factors.piQuotientLinearEquiv S p ?_).symm
    -- ⊢ map (algebraMap R S) p ≠ ⊥
    rwa [Ne.def, Ideal.map_eq_bot_iff_le_ker, (RingHom.injective_iff_ker_eq_bot _).mp inj_RS,
      le_bot_iff]
  · exact finrank_quotient_map p K L
    -- 🎉 no goals
#align ideal.sum_ramification_inertia Ideal.sum_ramification_inertia

end FactorsMap

end Ideal
