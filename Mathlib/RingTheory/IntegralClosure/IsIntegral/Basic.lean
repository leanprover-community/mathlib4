/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.Adjoin.Polynomial
import Mathlib.RingTheory.Finiteness.Subalgebra
import Mathlib.RingTheory.Polynomial.Tower

/-!
# Properties of integral elements.

We prove basic properties of integral elements in a ring extension.
-/

open Polynomial Submodule

section Ring

variable {R S A : Type*}
variable [CommRing R] [Ring A] [Ring S] (f : R →+* S)
variable [Algebra R A]

theorem RingHom.isIntegralElem_map {x : R} : f.IsIntegralElem (f x) :=
  ⟨X - C x, monic_X_sub_C _, by simp⟩

theorem isIntegral_algebraMap {x : R} : IsIntegral R (algebraMap R A x) :=
  (algebraMap R A).isIntegralElem_map

end Ring

section

variable {R A B S : Type*}
variable [CommRing R] [CommRing A] [Ring B] [CommRing S]
variable [Algebra R A] (f : R →+* S)

theorem IsIntegral.map {B C F : Type*} [Ring B] [Ring C] [Algebra R B] [Algebra A B] [Algebra R C]
    [IsScalarTower R A B] [Algebra A C] [IsScalarTower R A C] {b : B}
    [FunLike F B C] [AlgHomClass F A B C] (f : F)
    (hb : IsIntegral R b) : IsIntegral R (f b) := by
  obtain ⟨P, hP⟩ := hb
  refine ⟨P, hP.1, ?_⟩
  rw [← aeval_def, ← aeval_map_algebraMap A,
    aeval_algHom_apply, aeval_map_algebraMap, aeval_def, hP.2, map_zero]

section

variable {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]

theorem isIntegral_algHom_iff (f : A →ₐ[R] B) (hf : Function.Injective f) {x : A} :
    IsIntegral R (f x) ↔ IsIntegral R x := by
  refine ⟨fun ⟨p, hp, hx⟩ ↦ ⟨p, hp, ?_⟩, IsIntegral.map f⟩
  rwa [← f.comp_algebraMap, ← AlgHom.coe_toRingHom, ← hom_eval₂, AlgHom.coe_toRingHom,
    map_eq_zero_iff f hf] at hx

end

open Classical in
theorem Submodule.span_range_natDegree_eq_adjoin {R A} [CommRing R] [Semiring A] [Algebra R A]
    {x : A} {f : R[X]} (hf : f.Monic) (hfx : aeval x f = 0) :
    span R (Finset.image (x ^ ·) (Finset.range (natDegree f))) =
      Subalgebra.toSubmodule (Algebra.adjoin R {x}) := by
  nontriviality A
  have hf1 : f ≠ 1 := by rintro rfl; simp [one_ne_zero' A] at hfx
  refine (span_le.mpr fun s hs ↦ ?_).antisymm fun r hr ↦ ?_
  · rcases Finset.mem_image.1 hs with ⟨k, -, rfl⟩
    exact (Algebra.adjoin R {x}).pow_mem (Algebra.subset_adjoin rfl) k
  rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hr
  rcases (aeval x).mem_range.mp hr with ⟨p, rfl⟩
  rw [← modByMonic_add_div p hf, map_add, map_mul, hfx,
      zero_mul, add_zero, ← sum_C_mul_X_pow_eq (p %ₘ f), aeval_def, eval₂_sum, sum_def]
  refine sum_mem fun k hkq ↦ ?_
  rw [C_mul_X_pow_eq_monomial, eval₂_monomial, ← Algebra.smul_def]
  exact smul_mem _ _ (subset_span <| Finset.mem_image_of_mem _ <| Finset.mem_range.mpr <|
    (le_natDegree_of_mem_supp _ hkq).trans_lt <| natDegree_modByMonic_lt p hf hf1)

theorem IsIntegral.fg_adjoin_singleton [Algebra R B] {x : B} (hx : IsIntegral R x) :
    (Algebra.adjoin R {x}).toSubmodule.FG := by
  classical
  rcases hx with ⟨f, hfm, hfx⟩
  use (Finset.range <| f.natDegree).image (x ^ ·)
  exact span_range_natDegree_eq_adjoin hfm (by rwa [aeval_def])

variable (f : R →+* B)

theorem RingHom.isIntegralElem_zero : f.IsIntegralElem 0 :=
  f.map_zero ▸ f.isIntegralElem_map

theorem isIntegral_zero [Algebra R B] : IsIntegral R (0 : B) :=
  (algebraMap R B).isIntegralElem_zero

theorem RingHom.isIntegralElem_one : f.IsIntegralElem 1 :=
  f.map_one ▸ f.isIntegralElem_map

theorem isIntegral_one [Algebra R B] : IsIntegral R (1 : B) :=
  (algebraMap R B).isIntegralElem_one

variable (f : R →+* S)

theorem IsIntegral.of_pow [Algebra R B] {x : B} {n : ℕ} (hn : 0 < n) (hx : IsIntegral R <| x ^ n) :
    IsIntegral R x :=
  have ⟨p, hmonic, heval⟩ := hx
  ⟨expand R n p, hmonic.expand hn, by rwa [← aeval_def, expand_aeval]⟩

theorem IsIntegral.of_aeval_monic {x : A} {p : R[X]} (monic : p.Monic)
    (deg : p.natDegree ≠ 0) (hx : IsIntegral R (aeval x p)) : IsIntegral R x :=
  have ⟨p, hmonic, heval⟩ := hx
  ⟨_, hmonic.comp monic deg, by rwa [eval₂_comp, ← aeval_def x]⟩

end

section

variable {R A B S : Type*}
variable [CommRing R] [CommRing A] [Ring B] [CommRing S]
variable [Algebra R A] [Algebra R B] (f : R →+* S)

theorem IsIntegral.map_of_comp_eq {R S T U : Type*} [CommRing R] [Ring S]
    [CommRing T] [Ring U] [Algebra R S] [Algebra T U] (φ : R →+* T) (ψ : S →+* U)
    (h : (algebraMap T U).comp φ = ψ.comp (algebraMap R S)) {a : S} (ha : IsIntegral R a) :
    IsIntegral T (ψ a) :=
  let ⟨p, hp⟩ := ha
  ⟨p.map φ, hp.1.map _, by
    rw [← eval_map, map_map, h, ← map_map, eval_map, eval₂_at_apply, eval_map, hp.2, ψ.map_zero]⟩

@[simp]
theorem isIntegral_algEquiv {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (f : A ≃ₐ[R] B) {x : A} : IsIntegral R (f x) ↔ IsIntegral R x :=
  ⟨fun h ↦ by simpa using h.map f.symm, IsIntegral.map f⟩

/-- If `R → A → B` is an algebra tower,
then if the entire tower is an integral extension so is `A → B`. -/
theorem IsIntegral.tower_top [Algebra A B] [IsScalarTower R A B] {x : B}
    (hx : IsIntegral R x) : IsIntegral A x :=
  let ⟨p, hp, hpx⟩ := hx
  ⟨p.map <| algebraMap R A, hp.map _, by rw [← aeval_def, aeval_map_algebraMap, aeval_def, hpx]⟩

/- If `R` and `T` are isomorphic commutative rings and `S` is an `R`-algebra and a `T`-algebra in
a compatible way, then an element `a ∈ S` is integral over `R` if and only if it is integral
over `T`. -/
theorem RingEquiv.isIntegral_iff {R S T : Type*} [CommRing R] [Ring S] [CommRing T]
    [Algebra R S] [Algebra T S] (φ : R ≃+* T)
    (h : (algebraMap T S).comp φ.toRingHom = algebraMap R S) (a : S) :
    IsIntegral R a ↔ IsIntegral T a := by
  constructor <;> intro ha
  · letI : Algebra R T := φ.toRingHom.toAlgebra
    letI : IsScalarTower R T S :=
      ⟨fun r t s ↦ by simp only [Algebra.smul_def, map_mul, ← h, mul_assoc]; rfl⟩
    exact IsIntegral.tower_top ha
  · have h' : (algebraMap T S) = (algebraMap R S).comp φ.symm.toRingHom := by
      simp only [← h, RingHom.comp_assoc, RingEquiv.toRingHom_eq_coe, RingEquiv.comp_symm,
        RingHomCompTriple.comp_eq]
    letI : Algebra T R := φ.symm.toRingHom.toAlgebra
    letI : IsScalarTower T R S :=
      ⟨fun r t s ↦ by simp only [Algebra.smul_def, map_mul, h', mul_assoc]; rfl⟩
    exact IsIntegral.tower_top ha

theorem map_isIntegral_int {B C F : Type*} [Ring B] [Ring C] {b : B}
    [FunLike F B C] [RingHomClass F B C] (f : F)
    (hb : IsIntegral ℤ b) : IsIntegral ℤ (f b) :=
  hb.map (f : B →+* C).toIntAlgHom

theorem IsIntegral.of_subring {x : B} (T : Subring R) (hx : IsIntegral T x) : IsIntegral R x :=
  hx.tower_top

protected theorem IsIntegral.algebraMap [Algebra A B] [IsScalarTower R A B] {x : A}
    (h : IsIntegral R x) : IsIntegral R (algebraMap A B x) := by
  rcases h with ⟨f, hf, hx⟩
  use f, hf
  rw [IsScalarTower.algebraMap_eq R A B, ← hom_eval₂, hx, RingHom.map_zero]

theorem isIntegral_algebraMap_iff [Algebra A B] [IsScalarTower R A B] {x : A}
    (hAB : Function.Injective (algebraMap A B)) :
    IsIntegral R (algebraMap A B x) ↔ IsIntegral R x :=
  isIntegral_algHom_iff (IsScalarTower.toAlgHom R A B) hAB

theorem isIntegral_iff_isIntegral_closure_finite {r : B} :
    IsIntegral R r ↔ ∃ s : Set R, s.Finite ∧ IsIntegral (Subring.closure s) r := by
  constructor <;> intro hr
  · rcases hr with ⟨p, hmp, hpr⟩
    refine ⟨_, Finset.finite_toSet _, p.restriction, monic_restriction.2 hmp, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap R r p.restriction, map_restriction, aeval_def, hpr]
  rcases hr with ⟨s, _, hsr⟩
  exact hsr.of_subring _

@[stacks 09GH]
theorem fg_adjoin_of_finite {s : Set A} (hfs : s.Finite) (his : ∀ x ∈ s, IsIntegral R x) :
    (Algebra.adjoin R s).toSubmodule.FG := by
  induction s, hfs using Set.Finite.induction_on with
  | empty =>
    refine ⟨{1}, Submodule.ext fun x => ?_⟩
    rw [Algebra.adjoin_empty, Finset.coe_singleton, ← one_eq_span, Algebra.toSubmodule_bot]
  | @insert a s _ _ ih =>
    rw [← Set.union_singleton, Algebra.adjoin_union_coe_submodule]
    exact FG.mul
      (ih fun i hi => his i <| Set.mem_insert_of_mem a hi)
      (his a <| Set.mem_insert a s).fg_adjoin_singleton

theorem Algebra.finite_adjoin_of_finite_of_isIntegral {s : Set A} (hf : s.Finite)
    (hi : ∀ x ∈ s, IsIntegral R x) : Module.Finite R (adjoin R s) :=
  Module.Finite.iff_fg.mpr <| fg_adjoin_of_finite hf hi

theorem Algebra.finite_adjoin_simple_of_isIntegral {x : A} (hi : IsIntegral R x) :
    Module.Finite R (adjoin R {x}) :=
  Module.Finite.iff_fg.mpr hi.fg_adjoin_singleton

theorem isNoetherian_adjoin_finset [IsNoetherianRing R] (s : Finset A)
    (hs : ∀ x ∈ s, IsIntegral R x) : IsNoetherian R (Algebra.adjoin R (s : Set A)) :=
  isNoetherian_of_fg_of_noetherian _ (fg_adjoin_of_finite s.finite_toSet hs)

end

section Prod

variable {R A B : Type*}
variable [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

/-- An element of a product algebra is integral if each component is integral. -/
theorem IsIntegral.pair {x : A × B} (hx₁ : IsIntegral R x.1) (hx₂ : IsIntegral R x.2) :
    IsIntegral R x := by
  obtain ⟨p₁, ⟨hp₁Monic, hp₁Eval⟩⟩ := hx₁
  obtain ⟨p₂, ⟨hp₂Monic, hp₂Eval⟩⟩ := hx₂
  refine ⟨p₁ * p₂, ⟨hp₁Monic.mul hp₂Monic, ?_⟩⟩
  rw [← aeval_def] at *
  rw [aeval_prod_apply, aeval_mul, hp₁Eval, zero_mul, aeval_mul, hp₂Eval, mul_zero,
    Prod.zero_eq_mk]

/-- An element of a product algebra is integral iff each component is integral. -/
theorem IsIntegral.pair_iff {x : A × B} : IsIntegral R x ↔ IsIntegral R x.1 ∧ IsIntegral R x.2 :=
  ⟨fun h ↦ ⟨h.map (AlgHom.fst R A B), h.map (AlgHom.snd R A B)⟩, fun h ↦ h.1.pair h.2⟩

end Prod
