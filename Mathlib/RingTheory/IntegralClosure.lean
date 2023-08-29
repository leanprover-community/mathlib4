/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Data.Polynomial.Expand
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.RingTheory.Polynomial.Tower
import Mathlib.RingTheory.TensorProduct

#align_import ring_theory.integral_closure from "leanprover-community/mathlib"@"641b6a82006416ec431b2987b354af9311fed4f2"

/-!
# Integral closure of a subring.

If A is an R-algebra then `a : A` is integral over R if it is a root of a monic polynomial
with coefficients in R. Enough theory is developed to prove that integral elements
form a sub-R-algebra of A.

## Main definitions

Let `R` be a `CommRing` and let `A` be an R-algebra.

* `RingHom.IsIntegralElem (f : R →+* A) (x : A)` : `x` is integral with respect to the map `f`,

* `IsIntegral (x : A)`  : `x` is integral over `R`, i.e., is a root of a monic polynomial with
                          coefficients in `R`.
* `integralClosure R A` : the integral closure of `R` in `A`, regarded as a sub-`R`-algebra of `A`.
-/


open Classical BigOperators Polynomial Submodule

section Ring

variable {R S A : Type*}

variable [CommRing R] [Ring A] [Ring S] (f : R →+* S)

/-- An element `x` of `A` is said to be integral over `R` with respect to `f`
if it is a root of a monic polynomial `p : R[X]` evaluated under `f` -/
def RingHom.IsIntegralElem (f : R →+* A) (x : A) :=
  ∃ p : R[X], Monic p ∧ eval₂ f x p = 0
#align ring_hom.is_integral_elem RingHom.IsIntegralElem

/-- A ring homomorphism `f : R →+* A` is said to be integral
if every element `A` is integral with respect to the map `f` -/
def RingHom.IsIntegral (f : R →+* A) :=
  ∀ x : A, f.IsIntegralElem x
#align ring_hom.is_integral RingHom.IsIntegral

variable [Algebra R A] (R)

/-- An element `x` of an algebra `A` over a commutative ring `R` is said to be *integral*,
if it is a root of some monic polynomial `p : R[X]`.
Equivalently, the element is integral over `R` with respect to the induced `algebraMap` -/
def IsIntegral (x : A) : Prop :=
  (algebraMap R A).IsIntegralElem x
#align is_integral IsIntegral

variable (A)

/-- An algebra is integral if every element of the extension is integral over the base ring -/
protected def Algebra.IsIntegral : Prop :=
  (algebraMap R A).IsIntegral
#align algebra.is_integral Algebra.IsIntegral

variable {R A}

theorem RingHom.is_integral_map {x : R} : f.IsIntegralElem (f x) :=
  ⟨X - C x, monic_X_sub_C _, by simp⟩
                                -- 🎉 no goals
#align ring_hom.is_integral_map RingHom.is_integral_map

theorem isIntegral_algebraMap {x : R} : IsIntegral R (algebraMap R A x) :=
  (algebraMap R A).is_integral_map
#align is_integral_algebra_map isIntegral_algebraMap

theorem isIntegral_of_noetherian (H : IsNoetherian R A) (x : A) : IsIntegral R x := by
  let leval : R[X] →ₗ[R] A := (aeval x).toLinearMap
  -- ⊢ IsIntegral R x
  let D : ℕ → Submodule R A := fun n => (degreeLE R n).map leval
  -- ⊢ IsIntegral R x
  let M := WellFounded.min (isNoetherian_iff_wellFounded.1 H) (Set.range D) ⟨_, ⟨0, rfl⟩⟩
  -- ⊢ IsIntegral R x
  have HM : M ∈ Set.range D := WellFounded.min_mem _ _ _
  -- ⊢ IsIntegral R x
  cases' HM with N HN
  -- ⊢ IsIntegral R x
  have HM : ¬M < D (N + 1) :=
    WellFounded.not_lt_min (isNoetherian_iff_wellFounded.1 H) (Set.range D) _ ⟨N + 1, rfl⟩
  rw [← HN] at HM
  -- ⊢ IsIntegral R x
  have HN2 : D (N + 1) ≤ D N :=
    _root_.by_contradiction fun H =>
      HM (lt_of_le_not_le (map_mono (degreeLE_mono (WithBot.coe_le_coe.2 (Nat.le_succ N)))) H)
  have HN3 : leval (X ^ (N + 1)) ∈ D N := HN2 (mem_map_of_mem (mem_degreeLE.2 (degree_X_pow_le _)))
  -- ⊢ IsIntegral R x
  rcases HN3 with ⟨p, hdp, hpe⟩
  -- ⊢ IsIntegral R x
  refine' ⟨X ^ (N + 1) - p, monic_X_pow_sub (mem_degreeLE.1 hdp), _⟩
  -- ⊢ eval₂ (algebraMap R A) x (X ^ (N + 1) - p) = 0
  show leval (X ^ (N + 1) - p) = 0
  -- ⊢ ↑leval (X ^ (N + 1) - p) = 0
  rw [LinearMap.map_sub, hpe, sub_self]
  -- 🎉 no goals
#align is_integral_of_noetherian isIntegral_of_noetherian

theorem isIntegral_of_submodule_noetherian (S : Subalgebra R A)
    (H : IsNoetherian R (Subalgebra.toSubmodule S)) (x : A) (hx : x ∈ S) : IsIntegral R x := by
  suffices IsIntegral R (show S from ⟨x, hx⟩) by
    rcases this with ⟨p, hpm, hpx⟩
    replace hpx := congr_arg S.val hpx
    refine' ⟨p, hpm, Eq.trans _ hpx⟩
    simp only [aeval_def, eval₂, sum_def]
    rw [S.val.map_sum]
    refine' Finset.sum_congr rfl fun n _hn => _
    rw [S.val.map_mul, S.val.map_pow, S.val.commutes, S.val_apply, Subtype.coe_mk]
  refine' isIntegral_of_noetherian H ⟨x, hx⟩
  -- 🎉 no goals
#align is_integral_of_submodule_noetherian isIntegral_of_submodule_noetherian

end Ring

section

variable {K A : Type*}

variable [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]

variable (K)

theorem isIntegral_of_finite (e : A) : IsIntegral K e :=
  isIntegral_of_noetherian (IsNoetherian.iff_fg.2 inferInstance) _

variable (A)

/-- A field extension is integral if it is finite. -/
theorem Algebra.isIntegral_of_finite : Algebra.IsIntegral K A := fun x =>
  isIntegral_of_submodule_noetherian ⊤ (IsNoetherian.iff_fg.2 inferInstance) x Algebra.mem_top
#align algebra.is_integral_of_finite Algebra.isIntegral_of_finite

end

section

variable {R A B S : Type*}

variable [CommRing R] [CommRing A] [CommRing B] [CommRing S]

variable [Algebra R A] [Algebra R B] (f : R →+* S)

theorem map_isIntegral {B C F : Type*} [Ring B] [Ring C] [Algebra R B] [Algebra A B] [Algebra R C]
    [IsScalarTower R A B] [Algebra A C] [IsScalarTower R A C] {b : B} [AlgHomClass F A B C] (f : F)
    (hb : IsIntegral R b) : IsIntegral R (f b) := by
  obtain ⟨P, hP⟩ := hb
  -- ⊢ IsIntegral R (↑f b)
  refine' ⟨P, hP.1, _⟩
  -- ⊢ eval₂ (algebraMap R ((fun x => C) b)) (↑f b) P = 0
  rw [← aeval_def, show (aeval (f b)) P = (aeval (f b)) (P.map (algebraMap R A)) by simp,
    aeval_algHom_apply, aeval_map_algebraMap, aeval_def, hP.2, _root_.map_zero]
#align map_is_integral map_isIntegral

theorem isIntegral_map_of_comp_eq_of_isIntegral {R S T U : Type*} [CommRing R] [CommRing S]
    [CommRing T] [CommRing U] [Algebra R S] [Algebra T U] (φ : R →+* T) (ψ : S →+* U)
    (h : (algebraMap T U).comp φ = ψ.comp (algebraMap R S)) {a : S} (ha : IsIntegral R a) :
    IsIntegral T (ψ a) := by
  rw [IsIntegral, RingHom.IsIntegralElem] at ha ⊢
  -- ⊢ ∃ p, Monic p ∧ eval₂ (algebraMap T ((fun x => U) a)) (↑ψ a) p = 0
  obtain ⟨p, hp⟩ := ha
  -- ⊢ ∃ p, Monic p ∧ eval₂ (algebraMap T ((fun x => U) a)) (↑ψ a) p = 0
  refine' ⟨p.map φ, hp.left.map _, _⟩
  -- ⊢ eval₂ (algebraMap T ((fun x => U) a)) (↑ψ a) (Polynomial.map φ p) = 0
  rw [← eval_map, map_map, h, ← map_map, eval_map, eval₂_at_apply, eval_map, hp.right,
    RingHom.map_zero]
#align is_integral_map_of_comp_eq_of_is_integral isIntegral_map_of_comp_eq_of_isIntegral

theorem isIntegral_algHom_iff {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (hf : Function.Injective f) {x : A} : IsIntegral R (f x) ↔ IsIntegral R x := by
  refine' ⟨_, map_isIntegral f⟩
  -- ⊢ IsIntegral R (↑f x) → IsIntegral R x
  rintro ⟨p, hp, hx⟩
  -- ⊢ IsIntegral R x
  use p, hp
  -- ⊢ eval₂ (algebraMap R A) x p = 0
  rwa [← f.comp_algebraMap, ← AlgHom.coe_toRingHom, ← Polynomial.hom_eval₂, AlgHom.coe_toRingHom,
    map_eq_zero_iff f hf] at hx
#align is_integral_alg_hom_iff isIntegral_algHom_iff

@[simp]
theorem isIntegral_algEquiv {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (f : A ≃ₐ[R] B) {x : A} : IsIntegral R (f x) ↔ IsIntegral R x :=
  ⟨fun h => by simpa using map_isIntegral f.symm.toAlgHom h, map_isIntegral f.toAlgHom⟩
               -- 🎉 no goals
#align is_integral_alg_equiv isIntegral_algEquiv

theorem isIntegral_of_isScalarTower [Algebra A B] [IsScalarTower R A B] {x : B}
    (hx : IsIntegral R x) : IsIntegral A x :=
  let ⟨p, hp, hpx⟩ := hx
  ⟨p.map <| algebraMap R A, hp.map _, by rw [← aeval_def, aeval_map_algebraMap, aeval_def, hpx]⟩
                                         -- 🎉 no goals
#align is_integral_of_is_scalar_tower isIntegral_of_isScalarTower

theorem map_isIntegral_int {B C F : Type*} [Ring B] [Ring C] {b : B} [RingHomClass F B C] (f : F)
    (hb : IsIntegral ℤ b) : IsIntegral ℤ (f b) :=
  map_isIntegral (f : B →+* C).toIntAlgHom hb
#align map_is_integral_int map_isIntegral_int

theorem isIntegral_ofSubring {x : A} (T : Subring R) (hx : IsIntegral T x) : IsIntegral R x :=
  isIntegral_of_isScalarTower hx
#align is_integral_of_subring isIntegral_ofSubring

theorem IsIntegral.algebraMap [Algebra A B] [IsScalarTower R A B] {x : A} (h : IsIntegral R x) :
    IsIntegral R (algebraMap A B x) := by
  rcases h with ⟨f, hf, hx⟩
  -- ⊢ IsIntegral R (↑(_root_.algebraMap A B) x)
  use f, hf
  -- ⊢ eval₂ (_root_.algebraMap R ((fun x => B) x)) (↑(_root_.algebraMap A B) x) f  …
  rw [IsScalarTower.algebraMap_eq R A B, ← hom_eval₂, hx, RingHom.map_zero]
  -- 🎉 no goals
#align is_integral.algebra_map IsIntegral.algebraMap

theorem isIntegral_algebraMap_iff [Algebra A B] [IsScalarTower R A B] {x : A}
    (hAB : Function.Injective (algebraMap A B)) :
    IsIntegral R (algebraMap A B x) ↔ IsIntegral R x :=
  isIntegral_algHom_iff (IsScalarTower.toAlgHom R A B) hAB
#align is_integral_algebra_map_iff isIntegral_algebraMap_iff

theorem isIntegral_iff_isIntegral_closure_finite {r : A} :
    IsIntegral R r ↔ ∃ s : Set R, s.Finite ∧ IsIntegral (Subring.closure s) r := by
  constructor <;> intro hr
  -- ⊢ IsIntegral R r → ∃ s, Set.Finite s ∧ IsIntegral { x // x ∈ Subring.closure s …
                  -- ⊢ ∃ s, Set.Finite s ∧ IsIntegral { x // x ∈ Subring.closure s } r
                  -- ⊢ IsIntegral R r
  · rcases hr with ⟨p, hmp, hpr⟩
    -- ⊢ ∃ s, Set.Finite s ∧ IsIntegral { x // x ∈ Subring.closure s } r
    refine' ⟨_, Finset.finite_toSet _, p.restriction, monic_restriction.2 hmp, _⟩
    -- ⊢ eval₂ (algebraMap { x // x ∈ Subring.closure ↑(frange p) } A) r (restriction …
    rw [← aeval_def, ← aeval_map_algebraMap R r p.restriction, map_restriction, aeval_def, hpr]
    -- 🎉 no goals
  rcases hr with ⟨s, _, hsr⟩
  -- ⊢ IsIntegral R r
  exact isIntegral_ofSubring _ hsr
  -- 🎉 no goals
#align is_integral_iff_is_integral_closure_finite isIntegral_iff_isIntegral_closure_finite

theorem FG_adjoin_singleton_of_integral (x : A) (hx : IsIntegral R x) :
    (Algebra.adjoin R ({x} : Set A)).toSubmodule.FG := by
  rcases hx with ⟨f, hfm, hfx⟩
  -- ⊢ FG (↑Subalgebra.toSubmodule (Algebra.adjoin R {x}))
  exists Finset.image ((· ^ ·) x) (Finset.range (natDegree f + 1))
  -- ⊢ span R ↑(Finset.image ((fun x x_1 => x ^ x_1) x) (Finset.range (natDegree f  …
  apply le_antisymm
  -- ⊢ span R ↑(Finset.image ((fun x x_1 => x ^ x_1) x) (Finset.range (natDegree f  …
  · rw [span_le]
    -- ⊢ ↑(Finset.image ((fun x x_1 => x ^ x_1) x) (Finset.range (natDegree f + 1)))  …
    intro s hs
    -- ⊢ s ∈ ↑(↑Subalgebra.toSubmodule (Algebra.adjoin R {x}))
    rw [Finset.mem_coe] at hs
    -- ⊢ s ∈ ↑(↑Subalgebra.toSubmodule (Algebra.adjoin R {x}))
    rcases Finset.mem_image.1 hs with ⟨k, hk, rfl⟩
    -- ⊢ (fun x x_1 => x ^ x_1) x k ∈ ↑(↑Subalgebra.toSubmodule (Algebra.adjoin R {x}))
    clear hk
    -- ⊢ (fun x x_1 => x ^ x_1) x k ∈ ↑(↑Subalgebra.toSubmodule (Algebra.adjoin R {x}))
    exact (Algebra.adjoin R {x}).pow_mem (Algebra.subset_adjoin (Set.mem_singleton _)) k
    -- 🎉 no goals
  intro r hr; change r ∈ Algebra.adjoin R ({x} : Set A) at hr
  -- ⊢ r ∈ span R ↑(Finset.image ((fun x x_1 => x ^ x_1) x) (Finset.range (natDegre …
              -- ⊢ r ∈ span R ↑(Finset.image ((fun x x_1 => x ^ x_1) x) (Finset.range (natDegre …
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hr
  -- ⊢ r ∈ span R ↑(Finset.image ((fun x x_1 => x ^ x_1) x) (Finset.range (natDegre …
  rcases(aeval x).mem_range.mp hr with ⟨p, rfl⟩
  -- ⊢ ↑(aeval x) p ∈ span R ↑(Finset.image ((fun x x_1 => x ^ x_1) x) (Finset.rang …
  rw [← modByMonic_add_div p hfm]
  -- ⊢ ↑(aeval x) (p %ₘ f + f * (p /ₘ f)) ∈ span R ↑(Finset.image ((fun x x_1 => x  …
  rw [← aeval_def] at hfx
  -- ⊢ ↑(aeval x) (p %ₘ f + f * (p /ₘ f)) ∈ span R ↑(Finset.image ((fun x x_1 => x  …
  rw [AlgHom.map_add, AlgHom.map_mul, hfx, zero_mul, add_zero]
  -- ⊢ ↑(aeval x) (p %ₘ f) ∈ span R ↑(Finset.image ((fun x x_1 => x ^ x_1) x) (Fins …
  have : degree (p %ₘ f) ≤ degree f := degree_modByMonic_le p hfm
  -- ⊢ ↑(aeval x) (p %ₘ f) ∈ span R ↑(Finset.image ((fun x x_1 => x ^ x_1) x) (Fins …
  generalize p %ₘ f = q at this ⊢
  -- ⊢ ↑(aeval x) q ∈ span R ↑(Finset.image ((fun x x_1 => x ^ x_1) x) (Finset.rang …
  rw [← sum_C_mul_X_pow_eq q, aeval_def, eval₂_sum, sum_def]
  -- ⊢ ∑ n in support q, eval₂ (algebraMap R A) x (↑C (coeff q n) * X ^ n) ∈ span R …
  refine' sum_mem fun k hkq => _
  -- ⊢ eval₂ (algebraMap R A) x (↑C (coeff q k) * X ^ k) ∈ span R ↑(Finset.image (( …
  rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, ← Algebra.smul_def]
  -- ⊢ coeff q k • x ^ k ∈ span R ↑(Finset.image ((fun x x_1 => x ^ x_1) x) (Finset …
  refine' smul_mem _ _ (subset_span _)
  -- ⊢ x ^ k ∈ ↑(Finset.image ((fun x x_1 => x ^ x_1) x) (Finset.range (natDegree f …
  rw [Finset.mem_coe]; refine' Finset.mem_image.2 ⟨_, _, rfl⟩
  -- ⊢ x ^ k ∈ Finset.image ((fun x x_1 => x ^ x_1) x) (Finset.range (natDegree f + …
                       -- ⊢ k ∈ Finset.range (natDegree f + 1)
  rw [Finset.mem_range, Nat.lt_succ_iff]; refine' le_of_not_lt fun hk => _
  -- ⊢ k ≤ natDegree f
                                          -- ⊢ False
  rw [degree_le_iff_coeff_zero] at this
  -- ⊢ False
  rw [mem_support_iff] at hkq; apply hkq; apply this
  -- ⊢ False
                               -- ⊢ coeff q k = 0
                                          -- ⊢ degree f < ↑k
  exact lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.2 hk)
  -- 🎉 no goals
#align fg_adjoin_singleton_of_integral FG_adjoin_singleton_of_integral

theorem FG_adjoin_of_finite {s : Set A} (hfs : s.Finite) (his : ∀ x ∈ s, IsIntegral R x) :
    (Algebra.adjoin R s).toSubmodule.FG :=
  Set.Finite.induction_on hfs
    (fun _ =>
      ⟨{1},
        Submodule.ext fun x => by
          erw [Algebra.adjoin_empty, Finset.coe_singleton, ← one_eq_span, one_eq_range,
            LinearMap.mem_range, Algebra.mem_bot]
          rfl⟩)
          -- 🎉 no goals
    (fun {a s} _ _ ih his => by
      rw [← Set.union_singleton, Algebra.adjoin_union_coe_submodule]
      -- ⊢ FG (↑Subalgebra.toSubmodule (Algebra.adjoin R s) * ↑Subalgebra.toSubmodule ( …
      exact
        FG.mul (ih fun i hi => his i <| Set.mem_insert_of_mem a hi)
          (FG_adjoin_singleton_of_integral _ <| his a <| Set.mem_insert a s))
    his
#align fg_adjoin_of_finite FG_adjoin_of_finite

theorem isNoetherian_adjoin_finset [IsNoetherianRing R] (s : Finset A)
    (hs : ∀ x ∈ s, IsIntegral R x) : IsNoetherian R (Algebra.adjoin R (↑s : Set A)) :=
  isNoetherian_of_fg_of_noetherian _ (FG_adjoin_of_finite s.finite_toSet hs)
#align is_noetherian_adjoin_finset isNoetherian_adjoin_finset

/-- If `S` is a sub-`R`-algebra of `A` and `S` is finitely-generated as an `R`-module,
  then all elements of `S` are integral over `R`. -/
theorem isIntegral_of_mem_of_FG (S : Subalgebra R A) (HS : S.toSubmodule.FG) (x : A) (hx : x ∈ S) :
    IsIntegral R x := by
  -- say `x ∈ S`. We want to prove that `x` is integral over `R`.
  -- Say `S` is generated as an `R`-module by the set `y`.
  cases' HS with y hy
  -- ⊢ IsIntegral R x
  -- We can write `x` as `∑ rᵢ yᵢ` for `yᵢ ∈ Y`.
  obtain ⟨lx, hlx1, hlx2⟩ :
    ∃ (l : A →₀ R), l ∈ Finsupp.supported R R ↑y ∧ (Finsupp.total A A R id) l = x := by
    rwa [← @Finsupp.mem_span_image_iff_total A A R _ _ _ id (↑y) x, Set.image_id (y : Set A), hy]
  -- Note that `y ⊆ S`.
  have hyS : ∀ {p}, p ∈ y → p ∈ S := fun {p} hp =>
    show p ∈ Subalgebra.toSubmodule S by
      rw [← hy]
      exact subset_span hp
  -- Now `S` is a subalgebra so the product of two elements of `y` is also in `S`.
  have : ∀ jk : (y ×ˢ y : Finset (A × A)),
      jk.1.1 * jk.1.2 ∈ (Subalgebra.toSubmodule S) := fun jk =>
    S.mul_mem (hyS (Finset.mem_product.1 jk.2).1) (hyS (Finset.mem_product.1 jk.2).2)
  rw [← hy, ← Set.image_id (y : Set A)] at this
  -- ⊢ IsIntegral R x
  simp only [Finsupp.mem_span_image_iff_total] at this
  -- ⊢ IsIntegral R x
  -- Say `yᵢyⱼ = ∑rᵢⱼₖ yₖ`
  choose ly hly1 hly2 using this
  -- ⊢ IsIntegral R x
  -- Now let `S₀` be the subring of `R` generated by the `rᵢ` and the `rᵢⱼₖ`.
  let S₀ : Subring R :=
    Subring.closure ↑(lx.frange ∪ Finset.biUnion Finset.univ (Finsupp.frange ∘ ly))
  -- It suffices to prove that `x` is integral over `S₀`.
  refine' isIntegral_ofSubring S₀ _
  -- ⊢ IsIntegral { x // x ∈ S₀ } x
  letI : CommRing S₀ := SubringClass.toCommRing S₀
  -- ⊢ IsIntegral { x // x ∈ S₀ } x
  letI : Algebra S₀ A := Algebra.ofSubring S₀
  -- ⊢ IsIntegral { x // x ∈ S₀ } x
  -- Claim: the `S₀`-module span (in `A`) of the set `y ∪ {1}` is closed under
  -- multiplication (indeed, this is the motivation for the definition of `S₀`).
  have :
    span S₀ (insert 1 ↑y : Set A) * span S₀ (insert 1 ↑y : Set A) ≤
      span S₀ (insert 1 ↑y : Set A) := by
    rw [span_mul_span]
    refine' span_le.2 fun z hz => _
    rcases Set.mem_mul.1 hz with ⟨p, q, rfl | hp, hq, rfl⟩
    · rw [one_mul]
      exact subset_span hq
    rcases hq with (rfl | hq)
    · rw [mul_one]
      exact subset_span (Or.inr hp)
    erw [← hly2 ⟨(p, q), Finset.mem_product.2 ⟨hp, hq⟩⟩]
    rw [Finsupp.total_apply, Finsupp.sum]
    refine' (span S₀ (insert 1 ↑y : Set A)).sum_mem fun t ht => _
    have : ly ⟨(p, q), Finset.mem_product.2 ⟨hp, hq⟩⟩ t ∈ S₀ :=
      Subring.subset_closure
        (Finset.mem_union_right _ <|
          Finset.mem_biUnion.2
            ⟨⟨(p, q), Finset.mem_product.2 ⟨hp, hq⟩⟩, Finset.mem_univ _,
              Finsupp.mem_frange.2 ⟨Finsupp.mem_support_iff.1 ht, _, rfl⟩⟩)
    change (⟨_, this⟩ : S₀) • t ∈ _
    exact smul_mem _ _ (subset_span <| Or.inr <| hly1 _ ht)
  -- Hence this span is a subring. Call this subring `S₁`.
  let S₁ : Subring A :=
    { carrier := span S₀ (insert 1 ↑y : Set A)
      one_mem' := subset_span <| Or.inl rfl
      mul_mem' := fun {p q} hp hq => this <| mul_mem_mul hp hq
      zero_mem' := (span S₀ (insert 1 ↑y : Set A)).zero_mem
      add_mem' := fun {_ _} => (span S₀ (insert 1 ↑y : Set A)).add_mem
      neg_mem' := fun {_} => (span S₀ (insert 1 ↑y : Set A)).neg_mem }
  have : S₁ = Subalgebra.toSubring (Algebra.adjoin S₀ (↑y : Set A)) := by
    ext z
    suffices
      z ∈ span (↥S₀) (insert 1 ↑y : Set A) ↔
        z ∈ Subalgebra.toSubmodule (Algebra.adjoin (↥S₀) (y : Set A)) by
      simpa
    constructor <;> intro hz
    · exact
        (span_le.2
          (Set.insert_subset_iff.2
            ⟨(Algebra.adjoin S₀ (y : Set A)).one_mem, Algebra.subset_adjoin⟩)) hz
    · rw [Subalgebra.mem_toSubmodule, Algebra.mem_adjoin_iff] at hz
      suffices Subring.closure (Set.range (algebraMap (↥S₀) A) ∪ ↑y) ≤ S₁ by exact this hz
      refine' Subring.closure_le.2 (Set.union_subset _ fun t ht => subset_span <| Or.inr ht)
      rw [Set.range_subset_iff]
      intro y'
      rw [Algebra.algebraMap_eq_smul_one]
      exact smul_mem (span S₀ (insert (1 : A) (y : Set A))) y' (subset_span (Or.inl rfl))
  have foo : ∀ z, z ∈ S₁ ↔ z ∈ Algebra.adjoin (↥S₀) (y : Set A)
  -- ⊢ ∀ (z : A), z ∈ S₁ ↔ z ∈ Algebra.adjoin { x // x ∈ S₀ } ↑y
  simp [this]
  -- ⊢ IsIntegral { x // x ∈ S₀ } x
  haveI : IsNoetherianRing S₀ := is_noetherian_subring_closure _ (Finset.finite_toSet _)
  -- ⊢ IsIntegral { x // x ∈ S₀ } x
  refine'
    isIntegral_of_submodule_noetherian (Algebra.adjoin S₀ ↑y)
      (isNoetherian_of_fg_of_noetherian _
        ⟨insert 1 y, by
          rw [Finset.coe_insert]
          ext z
          simp only [Finset.coe_sort_coe, Finset.univ_eq_attach, Finset.mem_coe,
            Subalgebra.mem_toSubmodule]
          convert foo z⟩)
      _ _
  rw [← hlx2, Finsupp.total_apply, Finsupp.sum]
  -- ⊢ ∑ a in lx.support, ↑lx a • id a ∈ Algebra.adjoin { x // x ∈ S₀ } ↑y
  refine' Subalgebra.sum_mem _ fun r hr => _
  -- ⊢ ↑lx r • id r ∈ Algebra.adjoin { x // x ∈ S₀ } ↑y
  have : lx r ∈ S₀ :=
    Subring.subset_closure (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hr))
  change (⟨_, this⟩ : S₀) • r ∈ _
  -- ⊢ { val := ↑lx r, property := this } • r ∈ Algebra.adjoin { x // x ∈ S₀ } ↑y
  rw [Finsupp.mem_supported] at hlx1
  -- ⊢ { val := ↑lx r, property := this } • r ∈ Algebra.adjoin { x // x ∈ S₀ } ↑y
  exact Subalgebra.smul_mem _ (Algebra.subset_adjoin <| hlx1 hr) _
  -- 🎉 no goals
#align is_integral_of_mem_of_fg isIntegral_of_mem_of_FG

theorem Module.End.isIntegral {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Algebra.IsIntegral R (Module.End R M) :=
  LinearMap.exists_monic_and_aeval_eq_zero R
#align module.End.is_integral Module.End.isIntegral

/-- Suppose `A` is an `R`-algebra, `M` is an `A`-module such that `a • m ≠ 0` for all non-zero `a`
and `m`. If `x : A` fixes a nontrivial f.g. `R`-submodule `N` of `M`, then `x` is `R`-integral. -/
theorem isIntegral_of_smul_mem_submodule {M : Type*} [AddCommGroup M] [Module R M] [Module A M]
    [IsScalarTower R A M] [NoZeroSMulDivisors A M] (N : Submodule R M) (hN : N ≠ ⊥) (hN' : N.FG)
    (x : A) (hx : ∀ n ∈ N, x • n ∈ N) : IsIntegral R x := by
  let A' : Subalgebra R A :=
    { carrier := { x | ∀ n ∈ N, x • n ∈ N }
      mul_mem' := fun {a b} ha hb n hn => smul_smul a b n ▸ ha _ (hb _ hn)
      one_mem' := fun n hn => (one_smul A n).symm ▸ hn
      add_mem' := fun {a b} ha hb n hn => (add_smul a b n).symm ▸ N.add_mem (ha _ hn) (hb _ hn)
      zero_mem' := fun n _hn => (zero_smul A n).symm ▸ N.zero_mem
      algebraMap_mem' := fun r n hn => (algebraMap_smul A r n).symm ▸ N.smul_mem r hn }
  let f : A' →ₐ[R] Module.End R N :=
    AlgHom.ofLinearMap
      { toFun := fun x => (DistribMulAction.toLinearMap R M x).restrict x.prop
        -- porting note: was
                -- `fun x y => LinearMap.ext fun n => Subtype.ext <| add_smul x y n`
        map_add' := by intros x y; ext; exact add_smul _ _ _
        -- porting note: was
                --  `fun r s => LinearMap.ext fun n => Subtype.ext <| smul_assoc r s n`
        map_smul' := by intros r s; ext; apply smul_assoc }
      -- porting note: the next two lines were
      --`(LinearMap.ext fun n => Subtype.ext <| one_smul _ _) fun x y =>`
      --`LinearMap.ext fun n => Subtype.ext <| mul_smul x y n`
      (by ext; apply one_smul)
      (by intros x y; ext; apply mul_smul)
  obtain ⟨a, ha₁, ha₂⟩ : ∃ a ∈ N, a ≠ (0 : M) := by
    by_contra h'
    push_neg at h'
    apply hN
    rwa [eq_bot_iff]
  have : Function.Injective f := by
    show Function.Injective f.toLinearMap
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro s hs
    have : s.1 • a = 0 := congr_arg Subtype.val (LinearMap.congr_fun hs ⟨a, ha₁⟩)
    exact Subtype.ext ((eq_zero_or_eq_zero_of_smul_eq_zero this).resolve_right ha₂)
  show IsIntegral R (A'.val ⟨x, hx⟩)
  -- ⊢ IsIntegral R (↑(Subalgebra.val A') { val := x, property := hx })
  rw [isIntegral_algHom_iff A'.val Subtype.val_injective, ← isIntegral_algHom_iff f this]
  -- ⊢ IsIntegral R (↑f { val := x, property := hx })
  haveI : Module.Finite R N := by rwa [Module.finite_def, Submodule.fg_top]
  -- ⊢ IsIntegral R (↑f { val := x, property := hx })
  apply Module.End.isIntegral
  -- 🎉 no goals
#align is_integral_of_smul_mem_submodule isIntegral_of_smul_mem_submodule

variable {f}

theorem RingHom.Finite.to_isIntegral (h : f.Finite) : f.IsIntegral :=
  letI := f.toAlgebra
  fun _ => isIntegral_of_mem_of_FG ⊤ h.1 _ trivial
#align ring_hom.finite.to_is_integral RingHom.Finite.to_isIntegral

alias RingHom.IsIntegral.of_finite := RingHom.Finite.to_isIntegral
#align ring_hom.is_integral.of_finite RingHom.IsIntegral.of_finite

theorem RingHom.IsIntegral.to_finite (h : f.IsIntegral) (h' : f.FiniteType) : f.Finite := by
  letI := f.toAlgebra
  -- ⊢ Finite f
  obtain ⟨s, hs⟩ := h'
  -- ⊢ Finite f
  constructor
  -- ⊢ FG ⊤
  change (⊤ : Subalgebra R S).toSubmodule.FG
  -- ⊢ FG (↑Subalgebra.toSubmodule ⊤)
  rw [← hs]
  -- ⊢ FG (↑Subalgebra.toSubmodule (Algebra.adjoin R ↑s))
  exact FG_adjoin_of_finite (Set.toFinite _) fun x _ => h x
  -- 🎉 no goals
#align ring_hom.is_integral.to_finite RingHom.IsIntegral.to_finite

alias RingHom.Finite.of_isIntegral_of_finiteType := RingHom.IsIntegral.to_finite
#align ring_hom.finite.of_is_integral_of_finite_type RingHom.Finite.of_isIntegral_of_finiteType

/-- finite = integral + finite type -/
theorem RingHom.finite_iff_isIntegral_and_finiteType : f.Finite ↔ f.IsIntegral ∧ f.FiniteType :=
  ⟨fun h => ⟨h.to_isIntegral, h.to_finiteType⟩, fun ⟨h, h'⟩ => h.to_finite h'⟩
#align ring_hom.finite_iff_is_integral_and_finite_type RingHom.finite_iff_isIntegral_and_finiteType

theorem Algebra.IsIntegral.finite (h : Algebra.IsIntegral R A) [h' : Algebra.FiniteType R A] :
    Module.Finite R A := by
  have :=
    h.to_finite
      (by
        rw [RingHom.FiniteType]
        convert h'
        -- Porting note: was `ext`
        refine IsScalarTower.Algebra.ext (algebraMap R A).toAlgebra _ fun r x => ?_
        exact (Algebra.smul_def _ _).symm)
  rw [RingHom.Finite] at this
  -- ⊢ Module.Finite R A
  convert this
  -- ⊢ inst✝¹ = RingHom.toAlgebra (algebraMap R A)
  ext
  -- ⊢ (let_fun I := inst✝¹;
  exact Algebra.smul_def _ _
  -- 🎉 no goals
#align algebra.is_integral.finite Algebra.IsIntegral.finite

theorem Algebra.IsIntegral.of_finite [h : Module.Finite R A] : Algebra.IsIntegral R A := by
  apply RingHom.Finite.to_isIntegral
  -- ⊢ RingHom.Finite (algebraMap R A)
  rw [RingHom.Finite]
  -- ⊢ Module.Finite R A
  convert h
  -- ⊢ RingHom.toAlgebra (algebraMap R A) = inst✝¹
  ext
  -- ⊢ (let_fun I := RingHom.toAlgebra (algebraMap R A);
  exact (Algebra.smul_def _ _).symm
  -- 🎉 no goals
#align algebra.is_integral.of_finite Algebra.IsIntegral.of_finite

/-- finite = integral + finite type -/
theorem Algebra.finite_iff_isIntegral_and_finiteType :
    Module.Finite R A ↔ Algebra.IsIntegral R A ∧ Algebra.FiniteType R A :=
  ⟨fun _ => ⟨Algebra.IsIntegral.of_finite, inferInstance⟩, fun ⟨h, _⟩ => h.finite⟩
#align algebra.finite_iff_is_integral_and_finite_type Algebra.finite_iff_isIntegral_and_finiteType

variable (f)

theorem RingHom.is_integral_of_mem_closure {x y z : S} (hx : f.IsIntegralElem x)
    (hy : f.IsIntegralElem y) (hz : z ∈ Subring.closure ({x, y} : Set S)) : f.IsIntegralElem z := by
  letI : Algebra R S := f.toAlgebra
  -- ⊢ IsIntegralElem f z
  have := (FG_adjoin_singleton_of_integral x hx).mul (FG_adjoin_singleton_of_integral y hy)
  -- ⊢ IsIntegralElem f z
  rw [← Algebra.adjoin_union_coe_submodule, Set.singleton_union] at this
  -- ⊢ IsIntegralElem f z
  exact
    isIntegral_of_mem_of_FG (Algebra.adjoin R {x, y}) this z
      (Algebra.mem_adjoin_iff.2 <| Subring.closure_mono (Set.subset_union_right _ _) hz)
#align ring_hom.is_integral_of_mem_closure RingHom.is_integral_of_mem_closure

theorem isIntegral_of_mem_closure {x y z : A} (hx : IsIntegral R x) (hy : IsIntegral R y)
    (hz : z ∈ Subring.closure ({x, y} : Set A)) : IsIntegral R z :=
  (algebraMap R A).is_integral_of_mem_closure hx hy hz
#align is_integral_of_mem_closure isIntegral_of_mem_closure

theorem RingHom.is_integral_zero : f.IsIntegralElem 0 :=
  f.map_zero ▸ f.is_integral_map
#align ring_hom.is_integral_zero RingHom.is_integral_zero

theorem isIntegral_zero : IsIntegral R (0 : A) :=
  (algebraMap R A).is_integral_zero
#align is_integral_zero isIntegral_zero

theorem RingHom.is_integral_one : f.IsIntegralElem 1 :=
  f.map_one ▸ f.is_integral_map
#align ring_hom.is_integral_one RingHom.is_integral_one

theorem isIntegral_one : IsIntegral R (1 : A) :=
  (algebraMap R A).is_integral_one
#align is_integral_one isIntegral_one

theorem RingHom.is_integral_add {x y : S} (hx : f.IsIntegralElem x) (hy : f.IsIntegralElem y) :
    f.IsIntegralElem (x + y) :=
  f.is_integral_of_mem_closure hx hy <|
    Subring.add_mem _ (Subring.subset_closure (Or.inl rfl)) (Subring.subset_closure (Or.inr rfl))
#align ring_hom.is_integral_add RingHom.is_integral_add

theorem isIntegral_add {x y : A} (hx : IsIntegral R x) (hy : IsIntegral R y) :
    IsIntegral R (x + y) :=
  (algebraMap R A).is_integral_add hx hy
#align is_integral_add isIntegral_add

theorem RingHom.is_integral_neg {x : S} (hx : f.IsIntegralElem x) : f.IsIntegralElem (-x) :=
  f.is_integral_of_mem_closure hx hx (Subring.neg_mem _ (Subring.subset_closure (Or.inl rfl)))
#align ring_hom.is_integral_neg RingHom.is_integral_neg

theorem isIntegral_neg {x : A} (hx : IsIntegral R x) : IsIntegral R (-x) :=
  (algebraMap R A).is_integral_neg hx
#align is_integral_neg isIntegral_neg

theorem RingHom.is_integral_sub {x y : S} (hx : f.IsIntegralElem x) (hy : f.IsIntegralElem y) :
    f.IsIntegralElem (x - y) := by
  simpa only [sub_eq_add_neg] using f.is_integral_add hx (f.is_integral_neg hy)
  -- 🎉 no goals
#align ring_hom.is_integral_sub RingHom.is_integral_sub

theorem isIntegral_sub {x y : A} (hx : IsIntegral R x) (hy : IsIntegral R y) :
    IsIntegral R (x - y) :=
  (algebraMap R A).is_integral_sub hx hy
#align is_integral_sub isIntegral_sub

theorem RingHom.is_integral_mul {x y : S} (hx : f.IsIntegralElem x) (hy : f.IsIntegralElem y) :
    f.IsIntegralElem (x * y) :=
  f.is_integral_of_mem_closure hx hy
    (Subring.mul_mem _ (Subring.subset_closure (Or.inl rfl)) (Subring.subset_closure (Or.inr rfl)))
#align ring_hom.is_integral_mul RingHom.is_integral_mul

theorem isIntegral_mul {x y : A} (hx : IsIntegral R x) (hy : IsIntegral R y) :
    IsIntegral R (x * y) :=
  (algebraMap R A).is_integral_mul hx hy
#align is_integral_mul isIntegral_mul

theorem isIntegral_smul [Algebra S A] [Algebra R S] [IsScalarTower R S A] {x : A} (r : R)
    (hx : IsIntegral S x) : IsIntegral S (r • x) := by
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R S A]
  -- ⊢ IsIntegral S (↑(algebraMap S A) (↑(algebraMap R S) r) * x)
  exact isIntegral_mul isIntegral_algebraMap hx
  -- 🎉 no goals
#align is_integral_smul isIntegral_smul

theorem isIntegral_of_pow {x : A} {n : ℕ} (hn : 0 < n) (hx : IsIntegral R <| x ^ n) :
    IsIntegral R x := by
  rcases hx with ⟨p, ⟨hmonic, heval⟩⟩
  -- ⊢ IsIntegral R x
  exact
    ⟨expand R n p, Monic.expand hn hmonic, by
      rwa [eval₂_eq_eval_map, map_expand, expand_eval, ← eval₂_eq_eval_map]⟩
#align is_integral_of_pow isIntegral_of_pow

variable (R A)

/-- The integral closure of R in an R-algebra A. -/
def integralClosure : Subalgebra R A where
  carrier := { r | IsIntegral R r }
  zero_mem' := isIntegral_zero
  one_mem' := isIntegral_one
  add_mem' := isIntegral_add
  mul_mem' := isIntegral_mul
  algebraMap_mem' _ := isIntegral_algebraMap
#align integral_closure integralClosure

theorem mem_integralClosure_iff_mem_FG {r : A} :
    r ∈ integralClosure R A ↔ ∃ M : Subalgebra R A, M.toSubmodule.FG ∧ r ∈ M :=
  ⟨fun hr =>
    ⟨Algebra.adjoin R {r}, FG_adjoin_singleton_of_integral _ hr, Algebra.subset_adjoin rfl⟩,
    fun ⟨M, Hf, hrM⟩ => isIntegral_of_mem_of_FG M Hf _ hrM⟩
#align mem_integral_closure_iff_mem_fg mem_integralClosure_iff_mem_FG

variable {R} {A}

theorem adjoin_le_integralClosure {x : A} (hx : IsIntegral R x) :
    Algebra.adjoin R {x} ≤ integralClosure R A := by
  rw [Algebra.adjoin_le_iff]
  -- ⊢ {x} ⊆ ↑(integralClosure R A)
  simp only [SetLike.mem_coe, Set.singleton_subset_iff]
  -- ⊢ x ∈ integralClosure R A
  exact hx
  -- 🎉 no goals
#align adjoin_le_integral_closure adjoin_le_integralClosure

theorem le_integralClosure_iff_isIntegral {S : Subalgebra R A} :
    S ≤ integralClosure R A ↔ Algebra.IsIntegral R S :=
  SetLike.forall.symm.trans
    (forall_congr' fun x =>
      show IsIntegral R (algebraMap S A x) ↔ IsIntegral R x from
        isIntegral_algebraMap_iff Subtype.coe_injective)
#align le_integral_closure_iff_is_integral le_integralClosure_iff_isIntegral

theorem isIntegral_sup {S T : Subalgebra R A} :
    Algebra.IsIntegral R (S ⊔ T : Subalgebra R A) ↔
      Algebra.IsIntegral R S ∧ Algebra.IsIntegral R T := by
  simp only [← le_integralClosure_iff_isIntegral, sup_le_iff]
  -- 🎉 no goals
#align is_integral_sup isIntegral_sup

/-- Mapping an integral closure along an `AlgEquiv` gives the integral closure. -/
theorem integralClosure_map_algEquiv (f : A ≃ₐ[R] B) :
    (integralClosure R A).map (f : A →ₐ[R] B) = integralClosure R B := by
  ext y
  -- ⊢ y ∈ Subalgebra.map (↑f) (integralClosure R A) ↔ y ∈ integralClosure R B
  rw [Subalgebra.mem_map]
  -- ⊢ (∃ x, x ∈ integralClosure R A ∧ ↑↑f x = y) ↔ y ∈ integralClosure R B
  constructor
  -- ⊢ (∃ x, x ∈ integralClosure R A ∧ ↑↑f x = y) → y ∈ integralClosure R B
  · rintro ⟨x, hx, rfl⟩
    -- ⊢ ↑↑f x ∈ integralClosure R B
    exact map_isIntegral f hx
    -- 🎉 no goals
  · intro hy
    -- ⊢ ∃ x, x ∈ integralClosure R A ∧ ↑↑f x = y
    use f.symm y, map_isIntegral (f.symm : B →ₐ[R] A) hy
    -- ⊢ ↑↑f (↑(AlgEquiv.symm f) y) = y
    simp
    -- 🎉 no goals
#align integral_closure_map_alg_equiv integralClosure_map_algEquiv

theorem integralClosure.isIntegral (x : integralClosure R A) : IsIntegral R x :=
  let ⟨p, hpm, hpx⟩ := x.2
  ⟨p, hpm,
    Subtype.eq <| by
      rwa [← aeval_def, ← Subalgebra.val_apply, aeval_algHom_apply] at hpx⟩
      -- 🎉 no goals
#align integral_closure.is_integral integralClosure.isIntegral

theorem RingHom.isIntegral_of_isIntegral_mul_unit (x y : S) (r : R) (hr : f r * y = 1)
    (hx : f.IsIntegralElem (x * y)) : f.IsIntegralElem x := by
  obtain ⟨p, ⟨p_monic, hp⟩⟩ := hx
  -- ⊢ IsIntegralElem f x
  refine' ⟨scaleRoots p r, ⟨(monic_scaleRoots_iff r).2 p_monic, _⟩⟩
  -- ⊢ eval₂ f x (scaleRoots p r) = 0
  convert scaleRoots_eval₂_eq_zero f hp
  -- ⊢ x = ↑f r * (x * y)
  rw [mul_comm x y, ← mul_assoc, hr, one_mul]
  -- 🎉 no goals
#align ring_hom.is_integral_of_is_integral_mul_unit RingHom.isIntegral_of_isIntegral_mul_unit

theorem isIntegral_of_isIntegral_mul_unit {x y : A} {r : R} (hr : algebraMap R A r * y = 1)
    (hx : IsIntegral R (x * y)) : IsIntegral R x :=
  (algebraMap R A).isIntegral_of_isIntegral_mul_unit x y r hr hx
#align is_integral_of_is_integral_mul_unit isIntegral_of_isIntegral_mul_unit

/-- Generalization of `isIntegral_of_mem_closure` bootstrapped up from that lemma -/
theorem isIntegral_of_mem_closure' (G : Set A) (hG : ∀ x ∈ G, IsIntegral R x) :
    ∀ x ∈ Subring.closure G, IsIntegral R x := fun _ hx =>
  Subring.closure_induction hx hG isIntegral_zero isIntegral_one (fun _ _ => isIntegral_add)
    (fun _ => isIntegral_neg) fun _ _ => isIntegral_mul
#align is_integral_of_mem_closure' isIntegral_of_mem_closure'

theorem isIntegral_of_mem_closure'' {S : Type*} [CommRing S] {f : R →+* S} (G : Set S)
    (hG : ∀ x ∈ G, f.IsIntegralElem x) : ∀ x ∈ Subring.closure G, f.IsIntegralElem x := fun x hx =>
  @isIntegral_of_mem_closure' R S _ _ f.toAlgebra G hG x hx
#align is_integral_of_mem_closure'' isIntegral_of_mem_closure''

theorem IsIntegral.pow {x : A} (h : IsIntegral R x) (n : ℕ) : IsIntegral R (x ^ n) :=
  (integralClosure R A).pow_mem h n
#align is_integral.pow IsIntegral.pow

theorem IsIntegral.nsmul {x : A} (h : IsIntegral R x) (n : ℕ) : IsIntegral R (n • x) :=
  (integralClosure R A).nsmul_mem h n
#align is_integral.nsmul IsIntegral.nsmul

theorem IsIntegral.zsmul {x : A} (h : IsIntegral R x) (n : ℤ) : IsIntegral R (n • x) :=
  (integralClosure R A).zsmul_mem h n
#align is_integral.zsmul IsIntegral.zsmul

theorem IsIntegral.multiset_prod {s : Multiset A} (h : ∀ x ∈ s, IsIntegral R x) :
    IsIntegral R s.prod :=
  (integralClosure R A).multiset_prod_mem h
#align is_integral.multiset_prod IsIntegral.multiset_prod

theorem IsIntegral.multiset_sum {s : Multiset A} (h : ∀ x ∈ s, IsIntegral R x) :
    IsIntegral R s.sum :=
  (integralClosure R A).multiset_sum_mem h
#align is_integral.multiset_sum IsIntegral.multiset_sum

theorem IsIntegral.prod {α : Type*} {s : Finset α} (f : α → A) (h : ∀ x ∈ s, IsIntegral R (f x)) :
    IsIntegral R (∏ x in s, f x) :=
  (integralClosure R A).prod_mem h
#align is_integral.prod IsIntegral.prod

theorem IsIntegral.sum {α : Type*} {s : Finset α} (f : α → A) (h : ∀ x ∈ s, IsIntegral R (f x)) :
    IsIntegral R (∑ x in s, f x) :=
  (integralClosure R A).sum_mem h
#align is_integral.sum IsIntegral.sum

theorem IsIntegral.det {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n A}
    (h : ∀ i j, IsIntegral R (M i j)) : IsIntegral R M.det := by
  rw [Matrix.det_apply]
  -- ⊢ IsIntegral R (∑ σ : Equiv.Perm n, ↑Equiv.Perm.sign σ • ∏ i : n, M (↑σ i) i)
  exact IsIntegral.sum _ fun σ _hσ => IsIntegral.zsmul (IsIntegral.prod _ fun i _hi => h _ _) _
  -- 🎉 no goals
#align is_integral.det IsIntegral.det

@[simp]
theorem IsIntegral.pow_iff {x : A} {n : ℕ} (hn : 0 < n) : IsIntegral R (x ^ n) ↔ IsIntegral R x :=
  ⟨isIntegral_of_pow hn, fun hx => IsIntegral.pow hx n⟩
#align is_integral.pow_iff IsIntegral.pow_iff

open TensorProduct

-- porting note: I fought a lot with this proof.  I tried to follow the original,
-- but was not really able to.
theorem IsIntegral.tmul (x : A) {y : B} (h : IsIntegral R y) : IsIntegral A (x ⊗ₜ[R] y) := by
  obtain ⟨p, hp, hp'⟩ := h
  -- ⊢ IsIntegral A (x ⊗ₜ[R] y)
  refine' ⟨(p.map (_root_.algebraMap R A)).scaleRoots x, _, _⟩
  -- ⊢ Monic (scaleRoots (Polynomial.map (_root_.algebraMap R A) p) x)
  · rw [Polynomial.monic_scaleRoots_iff]
    -- ⊢ Monic (Polynomial.map (_root_.algebraMap R A) p)
    exact hp.map _
    -- 🎉 no goals
  convert Polynomial.scaleRoots_eval₂_mul (R := A ⊗[R] B) (S := A)
      Algebra.TensorProduct.includeLeftRingHom (?_) x
  any_goals exact 1 ⊗ₜ y
  -- ⊢ x ⊗ₜ[R] y = ↑Algebra.TensorProduct.includeLeftRingHom x * 1 ⊗ₜ[R] y
  · simp only [Algebra.TensorProduct.includeLeftRingHom_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  · simp only [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_pow,
      one_pow]
    convert (mul_zero (M₀ := A ⊗[R] B) _).symm
    -- ⊢ eval₂ Algebra.TensorProduct.includeLeftRingHom (1 ⊗ₜ[R] y) (Polynomial.map ( …
    erw [Polynomial.eval₂_map, Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap,
      ← Polynomial.eval₂_map]
    convert Polynomial.eval₂_at_apply
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom y
    rw [Polynomial.eval_map, hp', _root_.map_zero]
    -- 🎉 no goals
#align is_integral.tmul IsIntegral.tmul

section

variable (p : R[X]) (x : S)

/-- The monic polynomial whose roots are `p.leadingCoeff * x` for roots `x` of `p`. -/
noncomputable def normalizeScaleRoots (p : R[X]) : R[X] :=
  ∑ i in p.support,
    monomial i (if i = p.natDegree then 1 else p.coeff i * p.leadingCoeff ^ (p.natDegree - 1 - i))
#align normalize_scale_roots normalizeScaleRoots

theorem normalizeScaleRoots_coeff_mul_leadingCoeff_pow (i : ℕ) (hp : 1 ≤ natDegree p) :
    (normalizeScaleRoots p).coeff i * p.leadingCoeff ^ i =
      p.coeff i * p.leadingCoeff ^ (p.natDegree - 1) := by
  simp only [normalizeScaleRoots, finset_sum_coeff, coeff_monomial, Finset.sum_ite_eq', one_mul,
    zero_mul, mem_support_iff, ite_mul, Ne.def, ite_not]
  split_ifs with h₁ h₂
  · simp [h₁]
    -- 🎉 no goals
  · rw [h₂, leadingCoeff, ← pow_succ, tsub_add_cancel_of_le hp]
    -- 🎉 no goals
  · rw [mul_assoc, ← pow_add, tsub_add_cancel_of_le]
    -- ⊢ i ≤ natDegree p - 1
    apply Nat.le_pred_of_lt
    -- ⊢ i < natDegree p
    rw [lt_iff_le_and_ne]
    -- ⊢ i ≤ natDegree p ∧ i ≠ natDegree p
    exact ⟨le_natDegree_of_ne_zero h₁, h₂⟩
    -- 🎉 no goals
#align normalize_scale_roots_coeff_mul_leading_coeff_pow normalizeScaleRoots_coeff_mul_leadingCoeff_pow

theorem leadingCoeff_smul_normalizeScaleRoots (p : R[X]) :
    p.leadingCoeff • normalizeScaleRoots p = scaleRoots p p.leadingCoeff := by
  ext
  -- ⊢ coeff (leadingCoeff p • normalizeScaleRoots p) n✝ = coeff (scaleRoots p (lea …
  simp only [coeff_scaleRoots, normalizeScaleRoots, coeff_monomial, coeff_smul, Finset.smul_sum,
    Ne.def, Finset.sum_ite_eq', finset_sum_coeff, smul_ite, smul_zero, mem_support_iff]
  -- porting note: added the following `simp only`
  simp only [ge_iff_le, tsub_le_iff_right, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', mem_support_iff, ne_eq, ite_not]
  split_ifs with h₁ h₂
  · simp [*]
    -- 🎉 no goals
  · simp [*]
    -- 🎉 no goals
  · rw [mul_comm, mul_assoc, ← pow_succ', tsub_right_comm,
      tsub_add_cancel_of_le]
    rw [Nat.succ_le_iff]
    -- ⊢ 0 < natDegree p - n✝
    exact tsub_pos_of_lt (lt_of_le_of_ne (le_natDegree_of_ne_zero h₁) h₂)
    -- 🎉 no goals
#align leading_coeff_smul_normalize_scale_roots leadingCoeff_smul_normalizeScaleRoots

theorem normalizeScaleRoots_support : (normalizeScaleRoots p).support ≤ p.support := by
  intro x
  -- ⊢ x ∈ support (normalizeScaleRoots p) → x ∈ support p
  contrapose
  -- ⊢ ¬x ∈ support p → ¬x ∈ support (normalizeScaleRoots p)
  simp only [not_mem_support_iff, normalizeScaleRoots, finset_sum_coeff, coeff_monomial,
    Finset.sum_ite_eq', mem_support_iff, Ne.def, Classical.not_not, ite_eq_right_iff]
  intro h₁ h₂
  -- ⊢ (if x = natDegree p then 1 else coeff p x * leadingCoeff p ^ (natDegree p -  …
  exact (h₂ h₁).elim
  -- 🎉 no goals
#align normalize_scale_roots_support normalizeScaleRoots_support

theorem normalizeScaleRoots_degree : (normalizeScaleRoots p).degree = p.degree := by
  apply le_antisymm
  -- ⊢ degree (normalizeScaleRoots p) ≤ degree p
  · exact Finset.sup_mono (normalizeScaleRoots_support p)
    -- 🎉 no goals
  · rw [← degree_scaleRoots, ← leadingCoeff_smul_normalizeScaleRoots]
    -- ⊢ degree (leadingCoeff p • normalizeScaleRoots p) ≤ degree (normalizeScaleRoot …
    exact degree_smul_le _ _
    -- 🎉 no goals
#align normalize_scale_roots_degree normalizeScaleRoots_degree

theorem normalizeScaleRoots_eval₂_leadingCoeff_mul (h : 1 ≤ p.natDegree) (f : R →+* S) (x : S) :
    (normalizeScaleRoots p).eval₂ f (f p.leadingCoeff * x) =
      f p.leadingCoeff ^ (p.natDegree - 1) * p.eval₂ f x := by
  rw [eval₂_eq_sum_range, eval₂_eq_sum_range, Finset.mul_sum]
  -- ⊢ ∑ i in Finset.range (natDegree (normalizeScaleRoots p) + 1), ↑f (coeff (norm …
  apply Finset.sum_congr
  -- ⊢ Finset.range (natDegree (normalizeScaleRoots p) + 1) = Finset.range (natDegr …
  · rw [natDegree_eq_of_degree_eq (normalizeScaleRoots_degree p)]
    -- 🎉 no goals
  intro n _hn
  -- ⊢ ↑f (coeff (normalizeScaleRoots p) n) * (↑f (leadingCoeff p) * x) ^ n = ↑f (l …
  rw [mul_pow, ← mul_assoc, ← f.map_pow, ← f.map_mul,
    normalizeScaleRoots_coeff_mul_leadingCoeff_pow _ _ h, f.map_mul, f.map_pow]
  ring
  -- 🎉 no goals
#align normalize_scale_roots_eval₂_leading_coeff_mul normalizeScaleRoots_eval₂_leadingCoeff_mul

theorem normalizeScaleRoots_monic (h : p ≠ 0) : (normalizeScaleRoots p).Monic := by
  delta Monic leadingCoeff
  -- ⊢ coeff (normalizeScaleRoots p) (natDegree (normalizeScaleRoots p)) = 1
  rw [natDegree_eq_of_degree_eq (normalizeScaleRoots_degree p)]
  -- ⊢ coeff (normalizeScaleRoots p) (natDegree p) = 1
  suffices p = 0 → (0 : R) = 1 by simpa [normalizeScaleRoots, coeff_monomial]
  -- ⊢ p = 0 → 0 = 1
  exact fun h' => (h h').elim
  -- 🎉 no goals
#align normalize_scale_roots_monic normalizeScaleRoots_monic

/-- Given a `p : R[X]` and a `x : S` such that `p.eval₂ f x = 0`,
`f p.leadingCoeff * x` is integral. -/
theorem RingHom.isIntegralElem_leadingCoeff_mul (h : p.eval₂ f x = 0) :
    f.IsIntegralElem (f p.leadingCoeff * x) := by
  by_cases h' : 1 ≤ p.natDegree
  -- ⊢ IsIntegralElem f (↑f (leadingCoeff p) * x)
  · use normalizeScaleRoots p
    -- ⊢ Monic (normalizeScaleRoots p) ∧ eval₂ f (↑f (leadingCoeff p) * x) (normalize …
    have : p ≠ 0 := fun h'' => by
      rw [h'', natDegree_zero] at h'
      exact Nat.not_succ_le_zero 0 h'
    use normalizeScaleRoots_monic p this
    -- ⊢ eval₂ f (↑f (leadingCoeff p) * x) (normalizeScaleRoots p) = 0
    rw [normalizeScaleRoots_eval₂_leadingCoeff_mul p h' f x, h, mul_zero]
    -- 🎉 no goals
  · by_cases hp : p.map f = 0
    -- ⊢ IsIntegralElem f (↑f (leadingCoeff p) * x)
    · apply_fun fun q => coeff q p.natDegree at hp
      -- ⊢ IsIntegralElem f (↑f (leadingCoeff p) * x)
      rw [coeff_map, coeff_zero, coeff_natDegree] at hp
      -- ⊢ IsIntegralElem f (↑f (leadingCoeff p) * x)
      rw [hp, zero_mul]
      -- ⊢ IsIntegralElem f 0
      exact f.is_integral_zero
      -- 🎉 no goals
    · rw [Nat.one_le_iff_ne_zero, Classical.not_not] at h'
      -- ⊢ IsIntegralElem f (↑f (leadingCoeff p) * x)
      rw [eq_C_of_natDegree_eq_zero h', eval₂_C] at h
      -- ⊢ IsIntegralElem f (↑f (leadingCoeff p) * x)
      suffices p.map f = 0 by exact (hp this).elim
      -- ⊢ Polynomial.map f p = 0
      rw [eq_C_of_natDegree_eq_zero h', map_C, h, C_eq_zero]
      -- 🎉 no goals
#align ring_hom.is_integral_elem_leading_coeff_mul RingHom.isIntegralElem_leadingCoeff_mul

/-- Given a `p : R[X]` and a root `x : S`,
then `p.leadingCoeff • x : S` is integral over `R`. -/
theorem isIntegral_leadingCoeff_smul [Algebra R S] (h : aeval x p = 0) :
    IsIntegral R (p.leadingCoeff • x) := by
  rw [aeval_def] at h
  -- ⊢ IsIntegral R (leadingCoeff p • x)
  rw [Algebra.smul_def]
  -- ⊢ IsIntegral R (↑(algebraMap R S) (leadingCoeff p) * x)
  exact (algebraMap R S).isIntegralElem_leadingCoeff_mul p x h
  -- 🎉 no goals
#align is_integral_leading_coeff_smul isIntegral_leadingCoeff_smul

end

end

section IsIntegralClosure

/-- `IsIntegralClosure A R B` is the characteristic predicate stating `A` is
the integral closure of `R` in `B`,
i.e. that an element of `B` is integral over `R` iff it is an element of (the image of) `A`.
-/
class IsIntegralClosure (A R B : Type*) [CommRing R] [CommSemiring A] [CommRing B] [Algebra R B]
  [Algebra A B] : Prop where
  algebraMap_injective' : Function.Injective (algebraMap A B)
  isIntegral_iff : ∀ {x : B}, IsIntegral R x ↔ ∃ y, algebraMap A B y = x
#align is_integral_closure IsIntegralClosure

instance integralClosure.isIntegralClosure (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] :
    IsIntegralClosure (integralClosure R A) R A where
  algebraMap_injective' := Subtype.coe_injective
  isIntegral_iff {x} := ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨⟨_, h⟩, rfl⟩; exact h⟩
                                                    -- ⊢ IsIntegral R (↑(algebraMap { x // x ∈ integralClosure R A } A) { val := val✝ …
                                                                          -- 🎉 no goals
#align integral_closure.is_integral_closure integralClosure.isIntegralClosure

namespace IsIntegralClosure

-- Porting note: added to work around missing infer kind support
theorem algebraMap_injective (A R B : Type*) [CommRing R] [CommSemiring A] [CommRing B]
  [Algebra R B] [Algebra A B] [IsIntegralClosure A R B] : Function.Injective (algebraMap A B) :=
  algebraMap_injective' R

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]

variable [Algebra R B] [Algebra A B] [IsIntegralClosure A R B]

variable (R) (B) -- porting note: `{A}` was a `redundant binder annotation update`

protected theorem isIntegral [Algebra R A] [IsScalarTower R A B] (x : A) : IsIntegral R x :=
  (isIntegral_algebraMap_iff (algebraMap_injective A R B)).mp <|
    show IsIntegral R (algebraMap A B x) from isIntegral_iff.mpr ⟨x, rfl⟩
#align is_integral_closure.is_integral IsIntegralClosure.isIntegral

theorem isIntegral_algebra [Algebra R A] [IsScalarTower R A B] : Algebra.IsIntegral R A := fun x =>
  IsIntegralClosure.isIntegral R B x
#align is_integral_closure.is_integral_algebra IsIntegralClosure.isIntegral_algebra

theorem noZeroSMulDivisors [Algebra R A] [IsScalarTower R A B] [NoZeroSMulDivisors R B] :
    NoZeroSMulDivisors R A := by
  refine'
    Function.Injective.noZeroSMulDivisors _ (IsIntegralClosure.algebraMap_injective A R B)
      (map_zero _) fun _ _ => _
  simp only [Algebra.algebraMap_eq_smul_one, IsScalarTower.smul_assoc]
  -- 🎉 no goals
#align is_integral_closure.no_zero_smul_divisors IsIntegralClosure.noZeroSMulDivisors

variable {R} (A) {B}

/-- If `x : B` is integral over `R`, then it is an element of the integral closure of `R` in `B`. -/
noncomputable def mk' (x : B) (hx : IsIntegral R x) : A :=
  Classical.choose (isIntegral_iff.mp hx)
#align is_integral_closure.mk' IsIntegralClosure.mk'

@[simp]
theorem algebraMap_mk' (x : B) (hx : IsIntegral R x) : algebraMap A B (mk' A x hx) = x :=
  Classical.choose_spec (isIntegral_iff.mp hx)
#align is_integral_closure.algebra_map_mk' IsIntegralClosure.algebraMap_mk'

@[simp]
theorem mk'_one (h : IsIntegral R (1 : B) := isIntegral_one) : mk' A 1 h = 1 :=
  algebraMap_injective A R B <| by rw [algebraMap_mk', RingHom.map_one]
                                   -- 🎉 no goals
#align is_integral_closure.mk'_one IsIntegralClosure.mk'_one

@[simp]
theorem mk'_zero (h : IsIntegral R (0 : B) := isIntegral_zero) : mk' A 0 h = 0 :=
  algebraMap_injective A R B <| by rw [algebraMap_mk', RingHom.map_zero]
                                   -- 🎉 no goals
#align is_integral_closure.mk'_zero IsIntegralClosure.mk'_zero

-- Porting note: Left-hand side does not simplify @[simp]
theorem mk'_add (x y : B) (hx : IsIntegral R x) (hy : IsIntegral R y) :
    mk' A (x + y) (isIntegral_add hx hy) = mk' A x hx + mk' A y hy :=
  algebraMap_injective A R B <| by simp only [algebraMap_mk', RingHom.map_add]
                                   -- 🎉 no goals
#align is_integral_closure.mk'_add IsIntegralClosure.mk'_add

-- Porting note: Left-hand side does not simplify @[simp]
theorem mk'_mul (x y : B) (hx : IsIntegral R x) (hy : IsIntegral R y) :
    mk' A (x * y) (isIntegral_mul hx hy) = mk' A x hx * mk' A y hy :=
  algebraMap_injective A R B <| by simp only [algebraMap_mk', RingHom.map_mul]
                                   -- 🎉 no goals
#align is_integral_closure.mk'_mul IsIntegralClosure.mk'_mul

@[simp]
theorem mk'_algebraMap [Algebra R A] [IsScalarTower R A B] (x : R)
    (h : IsIntegral R (algebraMap R B x) := isIntegral_algebraMap) :
    IsIntegralClosure.mk' A (algebraMap R B x) h = algebraMap R A x :=
  algebraMap_injective A R B <| by rw [algebraMap_mk', ← IsScalarTower.algebraMap_apply]
                                   -- 🎉 no goals
#align is_integral_closure.mk'_algebra_map IsIntegralClosure.mk'_algebraMap

section lift

-- porting note: `R` and `A` were redundant binder updates
variable (B) {S : Type*} [CommRing S] [Algebra R S]
-- split from above, since otherwise it does not synthesize `Semiring S`
variable [Algebra S B] [IsScalarTower R S B]

variable [Algebra R A] [IsScalarTower R A B] (h : Algebra.IsIntegral R S)

/-- If `B / S / R` is a tower of ring extensions where `S` is integral over `R`,
then `S` maps (uniquely) into an integral closure `B / A / R`. -/
noncomputable def lift : S →ₐ[R] A where
  toFun x := mk' A (algebraMap S B x) (IsIntegral.algebraMap (h x))
  map_one' := by simp only [RingHom.map_one, mk'_one]
                 -- 🎉 no goals
  map_zero' := by simp only [RingHom.map_zero, mk'_zero]
                  -- 🎉 no goals
  map_add' x y := by simp_rw [← mk'_add, RingHom.map_add]
                     -- 🎉 no goals
                     -- 🎉 no goals
  map_mul' x y := by simp_rw [← mk'_mul, RingHom.map_mul]
  commutes' x := by simp_rw [← IsScalarTower.algebraMap_apply, mk'_algebraMap]
                    -- 🎉 no goals
#align is_integral_closure.lift IsIntegralClosure.lift

@[simp]
theorem algebraMap_lift (x : S) : algebraMap A B (lift A B h x) = algebraMap S B x :=
  algebraMap_mk' A (algebraMap S B x) (IsIntegral.algebraMap (h x))
#align is_integral_closure.algebra_map_lift IsIntegralClosure.algebraMap_lift

end lift

section Equiv

variable (R B) (A' : Type*) [CommRing A']
variable [Algebra A' B] [IsIntegralClosure A' R B]

variable [Algebra R A] [Algebra R A'] [IsScalarTower R A B] [IsScalarTower R A' B]

/-- Integral closures are all isomorphic to each other. -/
noncomputable def equiv : A ≃ₐ[R] A' :=
  AlgEquiv.ofAlgHom (lift _ B (isIntegral_algebra R B)) (lift _ B (isIntegral_algebra R B))
    (by
      ext x
      -- ⊢ ↑(AlgHom.comp (lift A' B (_ : Algebra.IsIntegral R A)) (lift A B (_ : Algebr …
      apply algebraMap_injective A' R B
      -- ⊢ ↑(algebraMap A' B) (↑(AlgHom.comp (lift A' B (_ : Algebra.IsIntegral R A)) ( …
      simp)
      -- 🎉 no goals
    (by
      ext x
      -- ⊢ ↑(AlgHom.comp (lift A B (_ : Algebra.IsIntegral R A')) (lift A' B (_ : Algeb …
      apply algebraMap_injective A R B
      -- ⊢ ↑(algebraMap A B) (↑(AlgHom.comp (lift A B (_ : Algebra.IsIntegral R A')) (l …
      simp)
      -- 🎉 no goals
#align is_integral_closure.equiv IsIntegralClosure.equiv

@[simp]
theorem algebraMap_equiv (x : A) : algebraMap A' B (equiv R A B A' x) = algebraMap A B x :=
  algebraMap_lift A' B (isIntegral_algebra R B) x
#align is_integral_closure.algebra_map_equiv IsIntegralClosure.algebraMap_equiv

end Equiv

end IsIntegralClosure

end IsIntegralClosure

section Algebra

open Algebra

variable {R A B S T : Type*}

variable [CommRing R] [CommRing A] [CommRing B] [CommRing S] [CommRing T]

variable [Algebra A B] [Algebra R B] (f : R →+* S) (g : S →+* T)

theorem isIntegral_trans_aux (x : B) {p : A[X]} (pmonic : Monic p) (hp : aeval x p = 0) :
    IsIntegral (adjoin R (↑(p.map <| algebraMap A B).frange : Set B)) x := by
  generalize hS : (↑(p.map <| algebraMap A B).frange : Set B) = S
  -- ⊢ IsIntegral { x // x ∈ adjoin R S } x
  have coeffs_mem : ∀ i, (p.map <| algebraMap A B).coeff i ∈ adjoin R S := by
    intro i
    by_cases hi : (p.map <| algebraMap A B).coeff i = 0
    · rw [hi]
      exact Subalgebra.zero_mem _
    rw [← hS]
    exact subset_adjoin (coeff_mem_frange _ _ hi)
  obtain ⟨q, hq⟩ :
    ∃ q : (adjoin R S)[X], q.map (algebraMap (adjoin R S) B) = (p.map <| algebraMap A B) := by
    rw [← Set.mem_range]
    exact (Polynomial.mem_map_range _).2 fun i => ⟨⟨_, coeffs_mem i⟩, rfl⟩
  use q
  -- ⊢ Monic q ∧ eval₂ (algebraMap { x // x ∈ adjoin R S } B) x q = 0
  constructor
  -- ⊢ Monic q
  · suffices h : (q.map (algebraMap (adjoin R S) B)).Monic
    -- ⊢ Monic q
    · refine' monic_of_injective _ h
      -- ⊢ Function.Injective ↑(algebraMap { x // x ∈ adjoin R S } B)
      exact Subtype.val_injective
      -- 🎉 no goals
    · rw [hq]
      -- ⊢ Monic (Polynomial.map (algebraMap A B) p)
      exact pmonic.map _
      -- 🎉 no goals
  · convert hp using 1
    -- ⊢ eval₂ (algebraMap { x // x ∈ adjoin R S } B) x q = ↑(aeval x) p
    replace hq := congr_arg (eval x) hq
    -- ⊢ eval₂ (algebraMap { x // x ∈ adjoin R S } B) x q = ↑(aeval x) p
    convert hq using 1 <;> symm <;> apply eval_map
    -- ⊢ eval₂ (algebraMap { x // x ∈ adjoin R S } B) x q = eval x (Polynomial.map (a …
                           -- ⊢ eval x (Polynomial.map (algebraMap { x // x ∈ adjoin R S } B) q) = eval₂ (al …
                           -- ⊢ eval x (Polynomial.map (algebraMap A B) p) = ↑(aeval x) p
                                    -- 🎉 no goals
                                    -- 🎉 no goals
#align is_integral_trans_aux isIntegral_trans_aux

variable [Algebra R A] [IsScalarTower R A B]

/-- If A is an R-algebra all of whose elements are integral over R,
and x is an element of an A-algebra that is integral over A, then x is integral over R.-/
theorem isIntegral_trans (A_int : Algebra.IsIntegral R A) (x : B) (hx : IsIntegral A x) :
    IsIntegral R x := by
  rcases hx with ⟨p, pmonic, hp⟩
  -- ⊢ IsIntegral R x
  let S : Set B := ↑(p.map <| algebraMap A B).frange
  -- ⊢ IsIntegral R x
  refine' isIntegral_of_mem_of_FG (adjoin R (S ∪ {x})) _ _ (subset_adjoin <| Or.inr rfl)
  -- ⊢ FG (↑Subalgebra.toSubmodule (adjoin R (S ∪ {x})))
  refine' fg_trans (FG_adjoin_of_finite (Finset.finite_toSet _) fun x hx => _) _
  -- ⊢ IsIntegral R x
  · rw [Finset.mem_coe, frange, Finset.mem_image] at hx
    -- ⊢ IsIntegral R x
    rcases hx with ⟨i, _, rfl⟩
    -- ⊢ IsIntegral R (coeff (Polynomial.map (algebraMap A B) p) i)
    rw [coeff_map]
    -- ⊢ IsIntegral R (↑(algebraMap A B) (coeff p i))
    exact map_isIntegral (IsScalarTower.toAlgHom R A B) (A_int _)
    -- 🎉 no goals
  · apply FG_adjoin_singleton_of_integral
    -- ⊢ IsIntegral { x // x ∈ adjoin R S } x
    exact isIntegral_trans_aux _ pmonic hp
    -- 🎉 no goals
#align is_integral_trans isIntegral_trans

/-- If A is an R-algebra all of whose elements are integral over R,
and B is an A-algebra all of whose elements are integral over A,
then all elements of B are integral over R.-/
nonrec theorem Algebra.isIntegral_trans
    (hA : Algebra.IsIntegral R A) (hB : Algebra.IsIntegral A B) : Algebra.IsIntegral R B :=
  fun x => isIntegral_trans hA x (hB x)
#align algebra.is_integral_trans Algebra.isIntegral_trans

theorem RingHom.isIntegral_trans (hf : f.IsIntegral) (hg : g.IsIntegral) : (g.comp f).IsIntegral :=
  @Algebra.isIntegral_trans R S T _ _ _ g.toAlgebra (g.comp f).toAlgebra f.toAlgebra
    (@IsScalarTower.of_algebraMap_eq R S T _ _ _ f.toAlgebra g.toAlgebra (g.comp f).toAlgebra
      (RingHom.comp_apply g f))
    hf hg
#align ring_hom.is_integral_trans RingHom.isIntegral_trans

theorem RingHom.isIntegral_of_surjective (hf : Function.Surjective f) : f.IsIntegral := fun x =>
  (hf x).recOn fun _y hy => (hy ▸ f.is_integral_map : f.IsIntegralElem x)
#align ring_hom.is_integral_of_surjective RingHom.isIntegral_of_surjective

theorem isIntegral_of_surjective (h : Function.Surjective (algebraMap R A)) :
    Algebra.IsIntegral R A :=
  (algebraMap R A).isIntegral_of_surjective h
#align is_integral_of_surjective isIntegral_of_surjective

/-- If `R → A → B` is an algebra tower with `A → B` injective,
then if the entire tower is an integral extension so is `R → A` -/
theorem isIntegral_tower_bot_of_isIntegral (H : Function.Injective (algebraMap A B)) {x : A}
    (h : IsIntegral R (algebraMap A B x)) : IsIntegral R x := by
  rcases h with ⟨p, ⟨hp, hp'⟩⟩
  -- ⊢ IsIntegral R x
  refine' ⟨p, ⟨hp, _⟩⟩
  -- ⊢ eval₂ (algebraMap R A) x p = 0
  rw [IsScalarTower.algebraMap_eq R A B, ← eval₂_map, eval₂_hom, ←
    RingHom.map_zero (algebraMap A B)] at hp'
  rw [eval₂_eq_eval_map]
  -- ⊢ eval x (Polynomial.map (algebraMap R A) p) = 0
  exact H hp'
  -- 🎉 no goals
#align is_integral_tower_bot_of_is_integral isIntegral_tower_bot_of_isIntegral

nonrec theorem RingHom.isIntegral_tower_bot_of_isIntegral (hg : Function.Injective g)
    (hfg : (g.comp f).IsIntegral) : f.IsIntegral := fun x =>
  @isIntegral_tower_bot_of_isIntegral R S T _ _ _ g.toAlgebra (g.comp f).toAlgebra f.toAlgebra
    (@IsScalarTower.of_algebraMap_eq R S T _ _ _ f.toAlgebra g.toAlgebra (g.comp f).toAlgebra
      (RingHom.comp_apply g f))
    hg x (hfg (g x))
#align ring_hom.is_integral_tower_bot_of_is_integral RingHom.isIntegral_tower_bot_of_isIntegral

theorem isIntegral_tower_bot_of_isIntegral_field {R A B : Type*} [CommRing R] [Field A]
    [CommRing B] [Nontrivial B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    {x : A} (h : IsIntegral R (algebraMap A B x)) : IsIntegral R x :=
  isIntegral_tower_bot_of_isIntegral (algebraMap A B).injective h
#align is_integral_tower_bot_of_is_integral_field isIntegral_tower_bot_of_isIntegral_field

theorem RingHom.isIntegralElem_of_isIntegralElem_comp {x : T} (h : (g.comp f).IsIntegralElem x) :
    g.IsIntegralElem x :=
  let ⟨p, ⟨hp, hp'⟩⟩ := h
  ⟨p.map f, hp.map f, by rwa [← eval₂_map] at hp'⟩
                         -- 🎉 no goals
#align ring_hom.is_integral_elem_of_is_integral_elem_comp
  RingHom.isIntegralElem_of_isIntegralElem_comp

theorem RingHom.isIntegral_tower_top_of_isIntegral (h : (g.comp f).IsIntegral) : g.IsIntegral :=
  fun x => RingHom.isIntegralElem_of_isIntegralElem_comp f g (h x)
#align ring_hom.is_integral_tower_top_of_is_integral RingHom.isIntegral_tower_top_of_isIntegral

/-- If `R → A → B` is an algebra tower,
then if the entire tower is an integral extension so is `A → B`. -/
theorem isIntegral_tower_top_of_isIntegral {x : B} (h : IsIntegral R x) : IsIntegral A x := by
  rcases h with ⟨p, ⟨hp, hp'⟩⟩
  -- ⊢ IsIntegral A x
  refine' ⟨p.map (algebraMap R A), ⟨hp.map (algebraMap R A), _⟩⟩
  -- ⊢ eval₂ (algebraMap A B) x (Polynomial.map (algebraMap R A) p) = 0
  rw [IsScalarTower.algebraMap_eq R A B, ← eval₂_map] at hp'
  -- ⊢ eval₂ (algebraMap A B) x (Polynomial.map (algebraMap R A) p) = 0
  exact hp'
  -- 🎉 no goals
#align is_integral_tower_top_of_is_integral isIntegral_tower_top_of_isIntegral

theorem RingHom.isIntegral_quotient_of_isIntegral {I : Ideal S} (hf : f.IsIntegral) :
    (Ideal.quotientMap I f le_rfl).IsIntegral := by
  rintro ⟨x⟩
  -- ⊢ IsIntegralElem (Ideal.quotientMap I f (_ : Ideal.comap f I ≤ Ideal.comap f I …
  obtain ⟨p, ⟨p_monic, hpx⟩⟩ := hf x
  -- ⊢ IsIntegralElem (Ideal.quotientMap I f (_ : Ideal.comap f I ≤ Ideal.comap f I …
  refine' ⟨p.map (Ideal.Quotient.mk _), ⟨p_monic.map _, _⟩⟩
  -- ⊢ eval₂ (Ideal.quotientMap I f (_ : Ideal.comap f I ≤ Ideal.comap f I)) (Quot. …
  simpa only [hom_eval₂, eval₂_map] using congr_arg (Ideal.Quotient.mk I) hpx
  -- 🎉 no goals
#align ring_hom.is_integral_quotient_of_is_integral RingHom.isIntegral_quotient_of_isIntegral

theorem isIntegral_quotient_of_isIntegral {I : Ideal A} (hRA : Algebra.IsIntegral R A) :
    Algebra.IsIntegral (R ⧸ I.comap (algebraMap R A)) (A ⧸ I) :=
  (algebraMap R A).isIntegral_quotient_of_isIntegral hRA
#align is_integral_quotient_of_is_integral isIntegral_quotient_of_isIntegral

theorem isIntegral_quotientMap_iff {I : Ideal S} :
    (Ideal.quotientMap I f le_rfl).IsIntegral ↔
      ((Ideal.Quotient.mk I).comp f : R →+* S ⧸ I).IsIntegral := by
  let g := Ideal.Quotient.mk (I.comap f)
  -- ⊢ RingHom.IsIntegral (Ideal.quotientMap I f (_ : Ideal.comap f I ≤ Ideal.comap …
  -- Porting note: added type ascription
  have : (Ideal.quotientMap I f le_rfl).comp g = (Ideal.Quotient.mk I).comp f :=
    Ideal.quotientMap_comp_mk le_rfl
  refine' ⟨fun h => _, fun h => RingHom.isIntegral_tower_top_of_isIntegral g _ (this ▸ h)⟩
  -- ⊢ RingHom.IsIntegral (RingHom.comp (Ideal.Quotient.mk I) f)
  refine' this ▸ RingHom.isIntegral_trans g (Ideal.quotientMap I f le_rfl) _ h
  -- ⊢ RingHom.IsIntegral g
  exact RingHom.isIntegral_of_surjective g Ideal.Quotient.mk_surjective
  -- 🎉 no goals
#align is_integral_quotient_map_iff isIntegral_quotientMap_iff

/-- If the integral extension `R → S` is injective, and `S` is a field, then `R` is also a field. -/
theorem isField_of_isIntegral_of_isField {R S : Type*} [CommRing R] [Nontrivial R] [CommRing S]
    [IsDomain S] [Algebra R S] (H : Algebra.IsIntegral R S)
    (hRS : Function.Injective (algebraMap R S)) (hS : IsField S) : IsField R := by
  refine' ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {a} ha => _⟩
  -- ⊢ ∃ b, a * b = 1
  -- Let `a_inv` be the inverse of `algebraMap R S a`,
  -- then we need to show that `a_inv` is of the form `algebraMap R S b`.
  obtain ⟨a_inv, ha_inv⟩ := hS.mul_inv_cancel
    fun h => ha (hRS (_root_.trans h (RingHom.map_zero _).symm))
  -- Let `p : R[X]` be monic with root `a_inv`,
  -- and `q` be `p` with coefficients reversed (so `q(a) = q'(a) * a + 1`).
  -- We claim that `q(a) = 0`, so `-q'(a)` is the inverse of `a`.
  obtain ⟨p, p_monic, hp⟩ := H a_inv
  -- ⊢ ∃ b, a * b = 1
  use -∑ i : ℕ in Finset.range p.natDegree, p.coeff i * a ^ (p.natDegree - i - 1)
  -- ⊢ a * -∑ i in Finset.range (natDegree p), coeff p i * a ^ (natDegree p - i - 1 …
  -- `q(a) = 0`, because multiplying everything with `a_inv^n` gives `p(a_inv) = 0`.
  -- TODO: this could be a lemma for `Polynomial.reverse`.
  have hq : (∑ i : ℕ in Finset.range (p.natDegree + 1), p.coeff i * a ^ (p.natDegree - i)) = 0 := by
    apply (injective_iff_map_eq_zero (algebraMap R S)).mp hRS
    have a_inv_ne_zero : a_inv ≠ 0 := right_ne_zero_of_mul (mt ha_inv.symm.trans one_ne_zero)
    refine' (mul_eq_zero.mp _).resolve_right (pow_ne_zero p.natDegree a_inv_ne_zero)
    rw [eval₂_eq_sum_range] at hp
    rw [map_sum, Finset.sum_mul]
    refine' (Finset.sum_congr rfl fun i hi => _).trans hp
    rw [RingHom.map_mul, mul_assoc]
    congr
    have : a_inv ^ p.natDegree = a_inv ^ (p.natDegree - i) * a_inv ^ i := by
      rw [← pow_add a_inv, tsub_add_cancel_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
    rw [RingHom.map_pow, this, ← mul_assoc, ← mul_pow, ha_inv, one_pow, one_mul]
  -- Since `q(a) = 0` and `q(a) = q'(a) * a + 1`, we have `a * -q'(a) = 1`.
  -- TODO: we could use a lemma for `Polynomial.divX` here.
  rw [Finset.sum_range_succ_comm, p_monic.coeff_natDegree, one_mul, tsub_self, pow_zero,
    add_eq_zero_iff_eq_neg, eq_comm] at hq
  rw [mul_comm, neg_mul, Finset.sum_mul]
  -- ⊢ -∑ x in Finset.range (natDegree p), coeff p x * a ^ (natDegree p - x - 1) *  …
  convert hq using 2
  -- ⊢ ∑ x in Finset.range (natDegree p), coeff p x * a ^ (natDegree p - x - 1) * a …
  refine' Finset.sum_congr rfl fun i hi => _
  -- ⊢ coeff p i * a ^ (natDegree p - i - 1) * a = coeff p i * a ^ (natDegree p - i)
  have : 1 ≤ p.natDegree - i := le_tsub_of_add_le_left (Finset.mem_range.mp hi)
  -- ⊢ coeff p i * a ^ (natDegree p - i - 1) * a = coeff p i * a ^ (natDegree p - i)
  rw [mul_assoc, ← pow_succ', tsub_add_cancel_of_le this]
  -- 🎉 no goals
#align is_field_of_is_integral_of_is_field isField_of_isIntegral_of_isField

theorem isField_of_isIntegral_of_isField' {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    [Algebra R S] (H : Algebra.IsIntegral R S) (hR : IsField R) : IsField S := by
  letI := hR.toField
  -- ⊢ IsField S
  refine' ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {x} hx => _⟩
  -- ⊢ ∃ b, x * b = 1
  let A := Algebra.adjoin R ({x} : Set S)
  -- ⊢ ∃ b, x * b = 1
  haveI : IsNoetherian R A :=
    isNoetherian_of_fg_of_noetherian (Subalgebra.toSubmodule A)
      (FG_adjoin_singleton_of_integral x (H x))
  haveI : Module.Finite R A := Module.IsNoetherian.finite R A
  -- ⊢ ∃ b, x * b = 1
  obtain ⟨y, hy⟩ :=
    LinearMap.surjective_of_injective
      (@LinearMap.mulLeft_injective R A _ _ _ _ ⟨x, subset_adjoin (Set.mem_singleton x)⟩ fun h =>
        hx (Subtype.ext_iff.mp h))
      1
  exact ⟨y, Subtype.ext_iff.mp hy⟩
  -- 🎉 no goals
#align is_field_of_is_integral_of_is_field' isField_of_isIntegral_of_isField'

theorem Algebra.IsIntegral.isField_iff_isField {R S : Type*} [CommRing R] [Nontrivial R]
    [CommRing S] [IsDomain S] [Algebra R S] (H : Algebra.IsIntegral R S)
    (hRS : Function.Injective (algebraMap R S)) : IsField R ↔ IsField S :=
  ⟨isField_of_isIntegral_of_isField' H, isField_of_isIntegral_of_isField H hRS⟩
#align algebra.is_integral.is_field_iff_is_field Algebra.IsIntegral.isField_iff_isField

end Algebra

theorem integralClosure_idem {R : Type*} {A : Type*} [CommRing R] [CommRing A] [Algebra R A] :
    integralClosure (integralClosure R A : Set A) A = ⊥ :=
  eq_bot_iff.2 fun x hx =>
    Algebra.mem_bot.2
      ⟨⟨x,
          @isIntegral_trans _ _ _ _ _ _ _ _ (integralClosure R A).algebra _
            integralClosure.isIntegral x hx⟩,
        rfl⟩
#align integral_closure_idem integralClosure_idem

section IsDomain

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]

instance : IsDomain (integralClosure R S) :=
  inferInstance

theorem roots_mem_integralClosure {f : R[X]} (hf : f.Monic) {a : S}
    (ha : a ∈ (f.map <| algebraMap R S).roots) : a ∈ integralClosure R S :=
  ⟨f, hf, (eval₂_eq_eval_map _).trans <| (mem_roots <| (hf.map _).ne_zero).1 ha⟩
#align roots_mem_integral_closure roots_mem_integralClosure

end IsDomain
