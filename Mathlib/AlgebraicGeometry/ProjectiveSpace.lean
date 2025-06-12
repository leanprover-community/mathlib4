/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Projective space

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace`: `ℙ(n; S)` is the projective `n`-space over `S`.
- `AlgebraicGeometry.ProjectiveSpace.SpecIso`: `ℙ(n; Spec R) ≅ Proj R[n]`
- `AlgebraicGeometry.ProjectiveSpace.openCover`: the canonical cover of `ℙ(n; S)` by `n` affine
  charts. The `i`ᵗʰ chart is `𝔸({k // k ≠ i}; S) ⟶ ℙ(n; S)`, and represents the open set where
  the function `Xᵢ` does not vanish.

-/

universe v w u

section MOVE

namespace CategoryTheory

theorem hom_comp_apply {C : Type u} [Category.{v, u} C] {FC : C → C → Type*}
      {CC : C → Type w} [(X Y : C) → FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
      {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (x : CC X) :
    (f ≫ g) x = g (f x) :=
  congr_fun (hom_comp f g) x

end CategoryTheory

namespace Localization

lemma awayLift_mk_self {R : Type*} [CommSemiring R]
    {A : Type*} [CommSemiring A] (f : R →+* A) (r : R)
    (a : R) (v : A) (hv : f r * v = 1) :
    Localization.awayLift f r (isUnit_iff_exists_inv.mpr ⟨v, hv⟩)
      (Localization.mk a ⟨r, 1, pow_one r⟩) = f a * v := by
  convert awayLift_mk f r a v hv 1 <;> rw [pow_one]

end Localization

namespace HomogeneousLocalization

@[simp]
lemma val_fromZeroRingHom {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (S : Submonoid A) (r : R) :
    (fromZeroRingHom 𝒜 S (algebraMap _ _ r)).val = algebraMap _ _ r :=
  rfl

instance {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι] [AddCommMonoid ι]
      (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (S : Submonoid A) :
    Algebra R (HomogeneousLocalization 𝒜 S) where
  algebraMap := (fromZeroRingHom 𝒜 S).comp (algebraMap R (𝒜 0))
  commutes' r x := mul_comm ..
  smul_def' r x := by ext; rw [val_smul, val_mul, Algebra.smul_def]; rfl

instance {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι] [AddCommMonoid ι]
      (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (S : Submonoid A) :
    IsScalarTower R (𝒜 0) (HomogeneousLocalization 𝒜 S) :=
  .of_algebraMap_eq' rfl

instance {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι] [AddCommMonoid ι]
      (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (S : Submonoid A) :
    IsScalarTower R (𝒜 0) (Localization S) :=
  .of_algebraMap_eq' rfl

instance {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι] [AddCommMonoid ι]
      (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (S : Submonoid A) :
    IsScalarTower R (HomogeneousLocalization 𝒜 S) (Localization S) :=
  .of_algebraMap_eq' rfl

instance {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι] [AddCommMonoid ι]
      (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (S : Submonoid A) :
    IsScalarTower (𝒜 0) (HomogeneousLocalization 𝒜 S) (Localization S) :=
  .of_algebraMap_eq' rfl

@[simp] lemma algebraMap_eq' {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (S : Submonoid A) :
    algebraMap R (HomogeneousLocalization 𝒜 S) = (fromZeroRingHom 𝒜 S).comp (algebraMap _ _) := rfl

theorem algebraMap_apply' {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (S : Submonoid A) (f : R) :
    algebraMap R (HomogeneousLocalization 𝒜 S) f = mk ⟨0, algebraMap _ _ f, 1, one_mem _⟩ := rfl

theorem val_sum {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {𝒜 : ι → Submodule R A}
      {x : Submonoid A} [AddCommMonoid ι] [DecidableEq ι] [GradedAlgebra 𝒜]
      {σ : Type*} {S : Finset σ} {f : σ → HomogeneousLocalization 𝒜 x} :
    (∑ s ∈ S, f s).val = ∑ s ∈ S, (f s).val :=
  map_sum (algebraMap (HomogeneousLocalization 𝒜 x) _) _ _

theorem val_prod {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {𝒜 : ι → Submodule R A}
      {x : Submonoid A} [AddCommMonoid ι] [DecidableEq ι] [GradedAlgebra 𝒜]
      {σ : Type*} {S : Finset σ} {f : σ → HomogeneousLocalization 𝒜 x} :
    (∏ s ∈ S, f s).val = ∏ s ∈ S, (f s).val :=
  map_prod (algebraMap (HomogeneousLocalization 𝒜 x) _) _ _

namespace Away

theorem mk_smul {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] {f d hf n x} (hx) {r : R} :
    r • Away.mk 𝒜 (f:=f) hf (d:=d) n x hx = .mk 𝒜 hf n (r • x) (Submodule.smul_mem _ _ hx) := rfl

theorem algebraMap_apply {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (f : A) (d hf) (r : R) :
    algebraMap R (Away 𝒜 f) r = .mk 𝒜 (d:=d) hf 0 (algebraMap R A r)
      (by rw [zero_nsmul]; exact SetLike.algebraMap_mem_graded ..) := by
  ext; simp [fromZeroRingHom]

/-- If `f = g`, then `Away 𝒜 f ≅ Away 𝒜 g`. -/
@[simps! apply] noncomputable
def congr {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (f g : A)
      {d : ι} (hf : f ∈ 𝒜 d) (h : f = g) :
    Away 𝒜 f ≃ₐ[R] Away 𝒜 g := by
  refine .ofRingEquiv (f := .ofRingHom (awayMap 𝒜 (SetLike.one_mem_graded ..) (by simp [h]))
    (awayMap 𝒜 (SetLike.one_mem_graded ..) (by simp [h]))
    (RingHom.ext fun x ↦ ?_) (RingHom.ext fun x ↦ ?_)) (fun x ↦ ?_)
  · subst h; rcases Away.mk_surjective 𝒜 hf x with ⟨n, a, ha, rfl⟩; simp
  · subst h; rcases Away.mk_surjective 𝒜 hf x with ⟨n, a, ha, rfl⟩; simp
  · subst h; ext; simp [awayMap_fromZeroRingHom]

lemma congr_mk {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (f g : A)
      {d : ι} (hf : f ∈ 𝒜 d) (h : f = g) (n x hx) :
    congr 𝒜 f g hf h (.mk 𝒜 hf n x hx) = .mk 𝒜 (by rwa [← h]) n x hx := by
  simp_rw [congr_apply, awayMap_mk, one_pow, mul_one, add_zero]

@[simp] lemma congr_symm {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (f g : A)
      {d : ι} (hf : f ∈ 𝒜 d) (h : f = g) :
    (congr 𝒜 f g hf h).symm = congr 𝒜 g f (by rwa [← h]) h.symm :=
  rfl

end Away

end HomogeneousLocalization

@[simp] theorem IsLocalization.Away.map_eq {R S P Q : Type*} [CommSemiring R] [CommSemiring S]
      [Algebra R S] [CommSemiring P] [CommSemiring Q] [Algebra P Q] {f : R →+* P} {r : R}
      [IsLocalization.Away r S] [IsLocalization.Away (f r) Q] (x : R) :
    IsLocalization.Away.map S Q f r (algebraMap R S x) = algebraMap P Q (f x) := by
  rw [IsLocalization.Away.map, IsLocalization.map_eq]

namespace MvPolynomial

attribute [local instance] gradedAlgebra
attribute [local instance] weightedGradedAlgebra
open Localization HomogeneousLocalization

theorem weightedHomogeneousComponent_eq_proj {σ R M : Type*} [CommSemiring R]
    [DecidableEq M] [AddCommMonoid M] (w : σ → M) (n : M) :
    weightedHomogeneousComponent w n = GradedAlgebra.proj (weightedHomogeneousSubmodule R w) n :=
  LinearMap.ext fun _ ↦ (weightedDecomposition.decompose'_apply ..).symm

theorem weightedHomogeneousComponent_eq_proj' {σ R M : Type*} [CommSemiring R]
    [DecidableEq M] [AddCommMonoid M] (w : σ → M) (n : M) :
    (weightedHomogeneousComponent w n).toAddMonoidHom =
      GradedRing.proj (weightedHomogeneousSubmodule R w) n :=
  congr_arg _ <| weightedHomogeneousComponent_eq_proj ..

theorem homogeneousComponent_eq_proj (σ R : Type*) [CommSemiring R] (n : ℕ) :
    homogeneousComponent n = GradedAlgebra.proj (homogeneousSubmodule σ R) n :=
  weightedHomogeneousComponent_eq_proj ..

theorem homogeneousComponent_eq_proj' (σ R : Type*) [CommSemiring R] (n : ℕ) :
    (homogeneousComponent n).toAddMonoidHom = GradedRing.proj (homogeneousSubmodule σ R) n :=
  weightedHomogeneousComponent_eq_proj' ..

theorem homogeneous_eq_span {σ R : Type*} [CommSemiring R] :
  (HomogeneousIdeal.irrelevant (homogeneousSubmodule σ R)).toIdeal = Ideal.span (Set.range .X) := by
  refine le_antisymm (fun p hp ↦ ?_) (Ideal.span_le.2 <| Set.range_subset_iff.2 <| fun _ ↦
      (HomogeneousIdeal.mem_irrelevant_iff _ _).2 ?_)
  · rw [as_sum p]
    refine Ideal.sum_mem _ (fun c hc ↦ ?_)
    rw [HomogeneousIdeal.mem_iff, HomogeneousIdeal.mem_irrelevant_iff,
      ← homogeneousComponent_eq_proj', LinearMap.toAddMonoidHom_coe, homogeneousComponent_zero,
      C_eq_zero] at hp
    by_cases hc₀ : c = 0
    · rw [hc₀, hp, monomial_zero', C_0]
      exact zero_mem ..
    · rw [Finsupp.ext_iff, not_forall] at hc₀
      rcases hc₀ with ⟨i, hci⟩
      classical
      rw [monomial_eq, Finsupp.prod, ← Finset.prod_erase_mul _ _ (Finsupp.mem_support_iff.2 hci),
        ← mul_assoc, ← Nat.sub_one_add_one hci, pow_succ, ← mul_assoc]
      exact Ideal.mul_mem_left _ _ <| Ideal.subset_span <| Set.mem_range_self _
  · rw [← homogeneousComponent_eq_proj', LinearMap.toAddMonoidHom_coe, homogeneousComponent_zero,
      coeff_zero_X, C_0]

theorem homogeneousSubmodule_zero {σ R : Type*} [CommSemiring R] :
    homogeneousSubmodule σ R 0 = 1 := by
  refine Submodule.ext fun p ↦ ?_
  rw [mem_homogeneousSubmodule, ← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C,
    Submodule.mem_one, algebraMap_eq]
  exact ⟨fun hp ↦ ⟨_, hp.symm⟩, fun ⟨y, hp⟩ ↦ by rw [← hp, coeff_zero_C]⟩

open Classical in
/-- Dehomogenisation of a polynomial, e.g. `X²+2XY+3Y² ↦ X²+2X+3`. The variable to be removed
is specified. -/
noncomputable def dehomogenise {σ R : Type*} [CommSemiring R] (i : σ) :
    MvPolynomial σ R →ₐ[R] MvPolynomial { k // k ≠ i } R :=
  aeval fun j ↦ if H : j = i then 1 else X ⟨j, H⟩

theorem dehomogenise_C {σ R : Type*} [CommSemiring R] (i : σ) (r : R) :
    dehomogenise i (C r) = C r :=
  aeval_C ..

theorem dehomogenise_X_self {σ R : Type*} [CommSemiring R] (i : σ) :
    dehomogenise (R:=R) i (X i) = 1 := by
  rw [dehomogenise, aeval_X, dif_pos rfl]

@[simp] theorem dehomogenise_X_of_ne {σ R : Type*} [CommSemiring R] {i j : σ} (h : j ≠ i) :
    dehomogenise (R:=R) i (X j) = X ⟨j, h⟩ := by
  rw [dehomogenise, aeval_X, dif_neg]

@[simp] theorem dehomogenise_X {σ R : Type*} [CommSemiring R] {i : σ} (j : {k // k ≠ i}) :
    dehomogenise (R:=R) i (X j) = X j := by
  simp [j.2]

@[simp] theorem dehomogenise_of_mem_X_powers {σ R : Type*} [CommSemiring R] {i : σ} {d}
    (hd : d ∈ Submonoid.powers (X (R:=R) i)) : dehomogenise (R:=R) i d = 1 := by
  rcases hd with ⟨_, _, rfl⟩; rw [map_pow, dehomogenise_X_self, one_pow]

theorem dehomogenise_X_powers {σ R : Type*} [CommSemiring R] (i : σ)
    (d : Submonoid.powers (X (R:=R) i)) : dehomogenise (R:=R) i d = 1 :=
  dehomogenise_of_mem_X_powers d.2

/-- Functoriality. -/
theorem map_comp_dehomogenise {σ R S : Type*} [CommSemiring R] [CommSemiring S]
      (f : R →+* S) (i : σ) :
    (map f).comp (RingHomClass.toRingHom (dehomogenise (R:=R) i)) =
      (RingHomClass.toRingHom (dehomogenise (R:=S) i)).comp (map f) :=
  ringHom_ext (by simp) fun k ↦ by by_cases h : k = i <;> simp [h]

/-- Functoriality. -/
theorem map_dehomogenise {σ R S : Type*} [CommSemiring R] [CommSemiring S]
      (f : R →+* S) (i : σ) (p : MvPolynomial σ R) :
    map f (dehomogenise i p) = dehomogenise i (map f p) :=
  RingHom.congr_fun (map_comp_dehomogenise f i) p

/-- Map `Xⱼ/Xᵢ` to `Xⱼ`, contracting away the variable `Xᵢ`. -/
noncomputable def contract {σ : Type*} (R : Type*) [CommRing R] (i : σ) :
    Away (homogeneousSubmodule σ R) (X i) →ₐ[R] MvPolynomial { k // k ≠ i } R where
  toFun p := Quotient.liftOn p (fun q ↦ q.num.val.dehomogenise i) fun q₁ q₂ hq ↦
    let ⟨x, hx⟩ := r_iff_exists.1 (mk_eq_mk_iff.1 hq)
    have := congr_arg (dehomogenise i) hx
    by simpa only [ne_eq, map_mul, SetLike.coe_mem, dehomogenise_of_mem_X_powers, q₂.den_mem,
      one_mul, q₁.den_mem] using this
  map_one' := map_one _
  map_mul' p₁ p₂ := Quotient.inductionOn₂ p₁ p₂ fun q₁ q₂ ↦ map_mul ..
  map_zero' := map_zero _
  map_add' p₁ p₂ := Quotient.inductionOn₂ p₁ p₂ fun q₁ q₂ ↦ show dehomogenise _ (_ + _) = _ by
    rw [map_add, map_mul, map_mul, dehomogenise_of_mem_X_powers q₁.den_mem,
      dehomogenise_of_mem_X_powers q₂.den_mem, one_mul, one_mul, add_comm]; rfl
  commutes' r := algHom_C ..

@[simp] theorem contract_mk {σ : Type*} (R : Type*) [CommRing R] (i : σ) (hx) (n : ℕ) (f)
    (hf : f.IsHomogeneous _) :
  contract R i (.mk _ (d:=1) hx n f hf) = f.dehomogenise i := rfl

@[simp] theorem contract_mk' {σ : Type*} (R : Type*) [CommRing R] (i : σ) (q) :
  contract R i (mk q) = q.num.val.dehomogenise i := rfl

/-- Map `Xⱼ` to `Xⱼ/Xᵢ`, expanding to the variable `Xᵢ`. -/
noncomputable def expand {σ : Type*} (R : Type*) [CommRing R] (i : σ) :
    MvPolynomial { k // k ≠ i } R →ₐ[R] Away (homogeneousSubmodule σ R) (X i) :=
  aeval fun j ↦ .mk _ (isHomogeneous_X ..) 1 (X j) (isHomogeneous_X ..)

theorem expand_C {σ R : Type*} [CommRing R] (i : σ) (r : R) :
    expand R i (C r) = .mk _ (isHomogeneous_X ..) 0 (C r) (isHomogeneous_C ..) :=
  algHom_C ..

@[simp] theorem expand_X {σ R : Type*} [CommRing R] (i : σ) (j) :
    expand R i (X j) = .mk _ (isHomogeneous_X ..) 1 (X j) (isHomogeneous_X ..) :=
  aeval_X ..

theorem expand_dehomogenise_monomial_one {σ R : Type*} [CommRing R] (i : σ) {d : ℕ} {c : σ →₀ ℕ}
    (hc : c.degree = d • 1) :
    expand R i ((monomial c 1).dehomogenise i) =
      .mk _ (isHomogeneous_X ..) d (monomial c 1) (isHomogeneous_monomial _ hc) := by
  ext : 1
  rw [Away.val_mk]
  rw [nsmul_one, Nat.cast_id] at hc
  cases hc; induction c using Finsupp.induction with
  | zero =>
      rw [monomial_zero', C_1, map_one, map_one, val_one, ← Localization.mk_one,
        mk_eq_mk_iff, r_iff_exists]
      exact ⟨1, by simp⟩
  | single_add c n b hc hn ih =>
      classical
      rw [monomial_single_add, map_mul, map_mul, val_mul, ih,
        map_pow, map_pow]
      by_cases hci : c = i
      · rw [hci, dehomogenise_X_self, map_one, one_pow, val_one, one_mul,
          mk_eq_mk_iff, r_iff_exists]
        exact ⟨1, by simp; ring⟩
      · rw [dehomogenise_X_of_ne hci, expand_X, val_pow, Away.val_mk,
          Localization.mk_pow, Localization.mk_mul, mk_eq_mk_iff, r_iff_exists]
        exact ⟨1, by simp [add_comm, monomial_add_single]; ring⟩

theorem expand_dehomogenise_monomial {σ R : Type*} [CommRing R] (i : σ) {d : ℕ} {c : σ →₀ ℕ}
      (hc : c.degree = d • 1) (r : R) :
    expand R i ((monomial c r).dehomogenise i) =
      .mk _ (isHomogeneous_X ..) d (monomial c r) (isHomogeneous_monomial _ hc) := by
  have : monomial c r = r • monomial c 1 := by rw [smul_monomial, smul_eq_mul, mul_one]
  conv_lhs => rw [this, map_smul, map_smul, expand_dehomogenise_monomial_one _ hc, Away.mk_smul]
  congr 1; exact this.symm

@[simp] theorem expand_dehomogenise_of_homogeneous {σ R : Type*} [CommRing R] (i : σ) {n : ℕ}
      {p : MvPolynomial σ R} (hp : p.IsHomogeneous n) :
    expand R i (p.dehomogenise i) =
      .mk _ (isHomogeneous_X ..) n p (by rwa [nsmul_one]) := by
  ext
  rw [Away.val_mk, ← support_sum_monomial_coeff p, map_sum, map_sum, mk_sum, val_sum]
  congr 1; ext s; rw [expand_dehomogenise_monomial _ (by rw [nsmul_one, Nat.cast_id]), Away.val_mk]
  by_cases hs : s.degree = n
  · rw [hs]
  · rw [hp.coeff_eq_zero hs, monomial_zero, Localization.mk_zero, Localization.mk_zero]

/-- Map `Xⱼ` to `Xⱼ/Xᵢ`. -/
@[simps!] noncomputable def algEquivAway {σ : Type*} (R : Type*) [CommRing R] (i : σ) :
    Away (homogeneousSubmodule σ R) (X i) ≃ₐ[R] MvPolynomial { k // k ≠ i } R where
  invFun := expand R i
  left_inv p := by
    change expand R i (contract R i p) = p
    rcases Away.mk_surjective _ (isHomogeneous_X ..) p with ⟨d, r, hr, rfl⟩
    rw [contract_mk, expand_dehomogenise_of_homogeneous _ (by rwa [nsmul_one, Nat.cast_id] at hr)]
  right_inv p := by
    change contract R i (aeval _ p) = p
    induction p using induction_on
    · rw [aeval_C, algebraMap_apply', contract_mk',
        SetLike.GradeZero.coe_algebraMap, algebraMap_eq, dehomogenise_C]
    · simp only [map_add, *]
    · simp only [map_mul, *, aeval_X, contract_mk, dehomogenise_X]
  __ := contract R i

@[simp] lemma coe_algEquivAway {σ R : Type*} [CommRing R] (i : σ) :
    (algEquivAway R i : _ →ₐ[R] _) = contract R i :=
  rfl

@[simp] lemma coe_algEquivAway' {σ R : Type*} [CommRing R] (i : σ) :
    (RingHomClass.toRingHom (algEquivAway R i)) = contract R i :=
  rfl

@[simp] lemma coe_algEquivAway_symm {σ R : Type*} [CommRing R] (i : σ) :
    ((algEquivAway R i).symm : _ →ₐ[R] _) = expand R i :=
  rfl

@[simp] lemma coe_algEquivAway_toRingEquiv_symm {σ R : Type*} [CommRing R] (i : σ) :
    ⇑(algEquivAway R i : _ ≃+* _).symm = expand R i :=
  rfl

@[simp] theorem contract_expand {σ R : Type*} [CommRing R] (i : σ) (p) :
    contract R i (expand R i p) = p :=
  (algEquivAway R i).apply_symm_apply _

@[simp] theorem contract_comp_expand {σ : Type*} (R : Type*) [CommRing R] (i : σ) :
    (contract R i).comp (expand R i) = AlgHom.id _ _ :=
  AlgHom.ext (contract_expand i)

@[simp] theorem expand_contract {σ R : Type*} [CommRing R] (i : σ) (p) :
    expand R i (contract R i p) = p :=
  (algEquivAway R i).symm_apply_apply _

@[simp] theorem expand_comp_contract {σ : Type*} (R : Type*) [CommRing R] (i : σ) :
    (expand R i).comp (contract R i) = AlgHom.id _ _ :=
  AlgHom.ext (expand_contract i)

noncomputable instance {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    Algebra (Away (homogeneousSubmodule σ R) (X i)) (Away (homogeneousSubmodule σ R) (X i * X j)) :=
  (HomogeneousLocalization.awayMap _ (isHomogeneous_X R j) rfl).toAlgebra

lemma algebraMap_away_left {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    algebraMap (Away (homogeneousSubmodule σ R) (X i))
        (Away (homogeneousSubmodule σ R) (X i * X j)) =
      HomogeneousLocalization.awayMap _ (isHomogeneous_X R j) rfl :=
  rfl

noncomputable instance {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    IsScalarTower R (Away (homogeneousSubmodule σ R) (X i))
      (Away (homogeneousSubmodule σ R) (X i * X j)) :=
  .of_algebraMap_eq fun r ↦ by ext; simp [algebraMap_away_left, awayMap_fromZeroRingHom]

noncomputable instance {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    Algebra (Away (homogeneousSubmodule σ R) (X j)) (Away (homogeneousSubmodule σ R) (X i * X j)) :=
  (HomogeneousLocalization.awayMap _ (isHomogeneous_X R i) (mul_comm ..)).toAlgebra

lemma algebraMap_away_right {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    algebraMap (Away (homogeneousSubmodule σ R) (X j))
        (Away (homogeneousSubmodule σ R) (X i * X j)) =
      HomogeneousLocalization.awayMap _ (isHomogeneous_X R i) (mul_comm ..) :=
  rfl

noncomputable instance {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    IsScalarTower R (Away (homogeneousSubmodule σ R) (X j))
      (Away (homogeneousSubmodule σ R) (X i * X j)) :=
  .of_algebraMap_eq fun r ↦ by ext; simp [algebraMap_away_right, awayMap_fromZeroRingHom]

instance isLocalization_away_X_mul_X {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    IsLocalization.Away (expand R i (dehomogenise i (X j)))
      (Away (homogeneousSubmodule σ R) (X i * X j)) := by
  convert Away.isLocalization_mul (𝒜 := homogeneousSubmodule σ R) (isHomogeneous_X R i)
    (isHomogeneous_X R j) rfl one_ne_zero
  rw [expand_dehomogenise_of_homogeneous i (isHomogeneous_X R j)]
  ext; unfold Away.isLocalizationElem; congr 2; rw [pow_one]

instance isLocalization_away_X_mul_X' {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    IsLocalization.Away (RingHomClass.toRingHom (expand R i) (dehomogenise i (X j)))
      (Away (homogeneousSubmodule σ R) (X i * X j)) :=
  isLocalization_away_X_mul_X R i j

/-- The ring `R[{Xₖ // k ≠ i}, 1/Xⱼ]`, which is our model of the natural `R[n](1/XᵢXⱼ)₀`.
See `ringEquivAwayMul` and `algEquivAwayMul`. -/
abbrev away₂ {σ : Type v} (R : Type u) [CommRing R] (i j : σ) : Type max u v :=
  Localization.Away (dehomogenise (R:=R) i (X j))

instance isLocalization_away₂ {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    IsLocalization.Away (RingHomClass.toRingHom (contract R i) (expand R i (dehomogenise i (X j))))
      (away₂ R i j) := by
  simp; infer_instance

instance isLocalization_away₂' {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    IsLocalization.Away (RingHomClass.toRingHom (algEquivAway R i)
        (expand R i (dehomogenise i (X j))))
      (away₂ R i j) :=
  isLocalization_away₂ ..

instance isLocalization_away_contract_expand {σ : Type*} (R : Type*) [CommRing R] (i : σ) (p) :
    IsLocalization.Away ((contract R i) (expand R i p)) (Localization.Away p) := by
  rw [contract_expand]; infer_instance

/-- The isomorphism between the natural `R[n](1/XᵢXⱼ)₀` and our model `R[{Xₖ // k ≠ i}, 1/Xⱼ]`. -/
@[simps! apply] noncomputable def ringEquivAwayMul {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    Away (homogeneousSubmodule σ R) (X i * X j) ≃+* away₂ R i j :=
  RingEquiv.ofRingHom
    (IsLocalization.Away.map (Away (homogeneousSubmodule σ R) (X i * X j))
      (away₂ R i j) (RingHomClass.toRingHom (contract R i)) (expand R i (dehomogenise i (X j))))
    (IsLocalization.Away.map (away₂ R i j)
      (Away (homogeneousSubmodule σ R) (X i * X j)) (RingHomClass.toRingHom (expand R i))
      (dehomogenise (R:=R) i (X j)))
    (IsLocalization.ringHom_ext (Submonoid.powers (dehomogenise (R:=R) i (X j))) <|
      RingHom.ext <| by simp)
    (IsLocalization.ringHom_ext (Submonoid.powers (expand R i (dehomogenise i (X j)))) <|
      RingHom.ext <| by simp)

@[simp] lemma ringEquivAwayMul_symm {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    RingHomClass.toRingHom (ringEquivAwayMul R i j).symm = IsLocalization.Away.map (away₂ R i j)
      (Away (homogeneousSubmodule σ R) (X i * X j)) (RingHomClass.toRingHom (expand R i))
      (dehomogenise (R:=R) i (X j)) :=
  rfl

lemma ringEquivAwayMul_symm' {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    RingHomClass.toRingHom (ringEquivAwayMul R i j).symm = awayLift
      ((algebraMap _ _).comp (RingHomClass.toRingHom (expand R i))) _
      (IsLocalization.Away.algebraMap_isUnit ..) :=
  rfl

/-- The isomorphism between the natural `R[n](1/XᵢXⱼ)₀` and our model `R[{Xₖ // k ≠ i}, 1/Xⱼ]`. -/
@[simps!] noncomputable def algEquivAwayMul {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    Away (homogeneousSubmodule σ R) (X i * X j) ≃ₐ[R] away₂ R i j :=
  .ofRingEquiv (f := ringEquivAwayMul R i j) fun x ↦ by
    rw [ringEquivAwayMul_apply,
      IsScalarTower.algebraMap_apply _ (Away (homogeneousSubmodule σ R) (X i)),
      @IsLocalization.Away.map_eq, RingHom.coe_coe, AlgHom.map_algebraMap,
      ← IsScalarTower.algebraMap_apply]

@[simp] lemma coe_algEquivAwayMul {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    (algEquivAwayMul R i j : _ ≃+* _) = ringEquivAwayMul R i j :=
  rfl

/-- The element `Xᵢ/Xⱼ` in `Away (homogeneousSubmodule σ R) (X i * X j)`. -/
noncomputable def XIDivXJ {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    Away (homogeneousSubmodule σ R) (X i * X j) :=
  .mk _ ((isHomogeneous_X ..).mul (isHomogeneous_X ..)) 1 (X i ^ 2) (isHomogeneous_X_pow ..)

lemma XIDivXJ_spec {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    algebraMap (Away (homogeneousSubmodule σ R) (X i)) (Away (homogeneousSubmodule σ R) (X i * X j))
      (expand R i (dehomogenise i (X j))) * XIDivXJ R i j = 1 := by
  ext; by_cases h : j = i
  · simp [XIDivXJ, algebraMap_away_left, h, pow_two]
  · simp [XIDivXJ, algebraMap_away_left, h, Localization.mk_mul,
      show X (R:=R) j * X j * X i ^ 2 = X i * X j * (X i * X j) by ring]

/-- The element `1/Xᵢ` in `Localization.Away (Xᵢ * Xⱼ)`. -/
noncomputable def invXI {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    Localization.Away (X (R:=R) i * X j) :=
  .mk (X j) ⟨_, 1, pow_one _⟩

lemma invXI_spec {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    algebraMap (MvPolynomial σ R) (Localization (Submonoid.powers (X i * X j))) (X i) *
      invXI R i j = 1 := by
  simp [← Localization.mk_one_eq_algebraMap, invXI, Localization.mk_mul]

/-- The element `1/Xⱼ` in `Localization.Away (Xᵢ * Xⱼ)`. -/
noncomputable def invXJ {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    Localization.Away (X (R:=R) i * X j) :=
  .mk (X i) ⟨_, 1, pow_one _⟩

lemma invXJ_spec {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    algebraMap (MvPolynomial σ R) (Localization (Submonoid.powers (X i * X j))) (X j) *
      invXJ R i j = 1 := by
  simp [← Localization.mk_one_eq_algebraMap, invXJ, Localization.mk_mul, mul_comm]

/-- Our model of the inclusion map `D(XᵢXⱼ) ⟶ D(Xᵢ)`. -/
noncomputable abbrev away₂Inl {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    MvPolynomial {k // k ≠ i} R →+* away₂ R i j :=
  algebraMap _ _

@[simp] lemma away₂Inl_comp_C {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    (away₂Inl R i j).comp C = algebraMap _ _ :=
  rfl

lemma away₂Inl_apply {σ : Type*} (R : Type*) [CommRing R] (i j : σ) (p) :
    away₂Inl R i j p = algebraMap _ _ p := rfl

/-- Our model of the inclusion map `D(XᵢXⱼ) ⟶ D(Xᵢ)`. -/
@[simps!] noncomputable def away₂InlAlgHom {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    MvPolynomial {k // k ≠ i} R →ₐ[R] away₂ R i j where
  commutes' _ := (IsScalarTower.algebraMap_apply ..).symm
  __ := away₂Inl R i j

/-- Our model of the inclusion map `D(XᵢXⱼ) ⟶ D(Xⱼ)`. -/
@[simps!] noncomputable def away₂InrAlgHom {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    MvPolynomial {k // k ≠ j} R →ₐ[R] away₂ R i j :=
  aeval (fun k ↦ Localization.mk (dehomogenise i (X k)) ⟨_, 1, pow_one _⟩)

/-- Our model of the inclusion map `D(XᵢXⱼ) ⟶ D(Xⱼ)`. -/
@[simps!] noncomputable def away₂Inr {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    MvPolynomial {k // k ≠ j} R →+* away₂ R i j :=
  away₂InrAlgHom R i j

@[simp] lemma away₂Inr_comp_C {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    (away₂Inr R i j).comp C = algebraMap _ _ :=
  RingHom.ext (aeval_C _)

noncomputable instance {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    Invertible (away₂Inl R i j (dehomogenise i (X j))) := by
  refine ⟨Away.invSelf _, ?_, ?_⟩ <;> rw [Away.invSelf, away₂Inl, ← mk_one_eq_algebraMap,
    Localization.mk_mul, mul_one, one_mul, mk_self_mk]

-- This is deliberately not tagged with `@[simp]`.
lemma invOn_away₂Inl_XJ {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    ⅟ (away₂Inl R i j (dehomogenise i (X j))) =
      Localization.mk 1 ⟨dehomogenise i (X j), Submonoid.mem_powers _⟩ :=
  rfl

lemma away₂Inr_X {σ : Type*} (R : Type*) [CommRing R] (i j : σ) (k : {k // k ≠ j}) :
    away₂Inr R i j (X k) = away₂Inl R i j (dehomogenise i (X k)) *
        ⅟ (away₂Inl R i j (dehomogenise i (X j))) := by
  rw [away₂Inr_apply, eval₂_X, away₂Inl_apply, ← mk_one_eq_algebraMap, invOn_away₂Inl_XJ,
    Localization.mk_mul, mul_one, one_mul]

lemma ringEquivAwayMul_symm_comp_away₂Inl {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    (RingHomClass.toRingHom (ringEquivAwayMul R i j).symm).comp (away₂Inl R i j) =
      (HomogeneousLocalization.awayMap _ (isHomogeneous_X R j) rfl).comp (expand R i) := by
  ext k <;> simp [val_awayMap, awayMap_fromZeroRingHom, algebraMap_away_left]

lemma ringEquivAwayMul_symm_comp_away₂Inr {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    (RingHomClass.toRingHom (ringEquivAwayMul R i j).symm).comp (away₂Inr R i j) =
      (HomogeneousLocalization.awayMap _ (isHomogeneous_X R i) (mul_comm ..)).comp
        (expand R j) := by
  ext k
  · rw [ringEquivAwayMul_symm, RingHom.comp_apply, RingHom.comp_apply, away₂Inr_apply, eval₂_C,
      IsScalarTower.algebraMap_apply _ (MvPolynomial { k // k ≠ i } R),
      IsLocalization.Away.map_eq, RingHom.coe_coe, AlgHom.map_algebraMap,
      ← IsScalarTower.algebraMap_apply, ← HomogeneousLocalization.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_coe,
      ← algebraMap_eq, AlgHom.map_algebraMap, ← awayMapₐ_apply,
      IsScalarTower.algebraMap_apply _ (homogeneousSubmodule σ R 0) (Away _ _),
      AlgHom.map_algebraMap, ← HomogeneousLocalization.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  · rw [ringEquivAwayMul_symm', RingHom.comp_apply, RingHom.comp_apply, away₂Inr_apply,
      eval₂_X, val_awayMap, awayLift_mk_self _ _ _ _ (by exact XIDivXJ_spec R i j),
      RingHom.comp_apply, RingHom.coe_coe, RingHom.coe_coe,
      expand_dehomogenise_of_homogeneous _ (isHomogeneous_X ..), algebraMap_away_left,
      val_mul, val_awayMap, Away.val_mk, awayLift_mk _ _ _ _ (by exact invXI_spec R i j),
      expand_X, Away.val_mk, awayLift_mk _ _ _ _ (by exact invXJ_spec R i j),
      ← Localization.mk_one_eq_algebraMap, pow_one, pow_one, XIDivXJ, Away.val_mk,
      invXI, invXJ, Localization.mk_mul, Localization.mk_mul, Localization.mk_mul,
      mk_eq_mk_iff, r_iff_exists]
    exact ⟨1, by simp; ring⟩

lemma ringEquivAwayMul_symm_away₂Inl {σ : Type*} (R : Type*) [CommRing R] (i j : σ) (x) :
    (ringEquivAwayMul R i j).symm (away₂Inl R i j x) =
      (HomogeneousLocalization.awayMap _ (isHomogeneous_X R j) rfl (expand R i x)) :=
  RingHom.congr_fun (ringEquivAwayMul_symm_comp_away₂Inl R i j) x

lemma ringEquivAwayMul_symm_away₂InlAlgHom
      {σ : Type*} (R : Type*) [CommRing R] (i j : σ) (x) :
    (ringEquivAwayMul R i j).symm (away₂InlAlgHom R i j x) =
      (HomogeneousLocalization.awayMap _ (isHomogeneous_X R j) rfl (expand R i x)) :=
  RingHom.congr_fun (ringEquivAwayMul_symm_comp_away₂Inl R i j) x

lemma ringEquivAwayMul_symm_away₂Inr {σ : Type*} (R : Type*) [CommRing R] (i j : σ) (x) :
    (ringEquivAwayMul R i j).symm (away₂Inr R i j x) =
      (HomogeneousLocalization.awayMap _ (isHomogeneous_X R i) (mul_comm ..) (expand R j x)) :=
  RingHom.congr_fun (ringEquivAwayMul_symm_comp_away₂Inr R i j) x

lemma ringEquivAwayMul_symm_away₂InrAlgHom
      {σ : Type*} (R : Type*) [CommRing R] (i j : σ) (x) :
    (ringEquivAwayMul R i j).symm (away₂InrAlgHom R i j x) =
      (HomogeneousLocalization.awayMap _ (isHomogeneous_X R i) (mul_comm ..) (expand R j x)) :=
  RingHom.congr_fun (ringEquivAwayMul_symm_comp_away₂Inr R i j) x

noncomputable instance {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    Algebra (MvPolynomial { k // k ≠ j } R) (away₂ R i j) :=
  (away₂Inr R i j).toAlgebra

lemma algebraMap_eq_away₂Inl {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    algebraMap (MvPolynomial { k // k ≠ i } R) (away₂ R i j) = away₂Inl R i j :=
  rfl

@[simp] lemma algebraMap_eq_away₂Inr {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    algebraMap (MvPolynomial { k // k ≠ j } R) (away₂ R i j) = away₂Inr R i j :=
  rfl

/-- `away₂ R i j ≃ₐ[R] away₂ R j i` -/
@[simps! apply] noncomputable def away₂Comm {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    away₂ R i j ≃ₐ[R] away₂ R j i :=
  (algEquivAwayMul R i j).symm.trans <|
    (Away.congr _ _ _ ((isHomogeneous_X ..).mul (isHomogeneous_X ..)) (mul_comm ..)).trans
      (algEquivAwayMul R j i)

lemma away₂Comm_comp_away₂InrAlgHom {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    (AlgHomClass.toAlgHom (away₂Comm R i j)).comp (away₂InrAlgHom R i j) =
      away₂InlAlgHom R j i := by
  ext k
  rw [AlgHom.comp_apply, away₂Comm, ← AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_algHom,
    AlgEquiv.trans_apply, AlgEquiv.trans_apply, algEquivAwayMul_symm_apply,
    ringEquivAwayMul_symm_away₂InrAlgHom, expand_X, awayMap_mk, Away.congr_mk, eq_comm,
    ← AlgEquiv.symm_apply_eq, algEquivAwayMul_symm_apply,
    ringEquivAwayMul_symm_away₂InlAlgHom, expand_X, awayMap_mk]

/-- `away₂ R i j ≅ away₂ R j i` over `R[{Xₖ // k ≠ j}]`. -/
@[simps! apply] noncomputable def away₂CommAlgEquiv {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    away₂ R i j ≃ₐ[MvPolynomial { k // k ≠ j } R] away₂ R j i :=
  .ofRingEquiv (f := away₂Comm R i j)
    fun x ↦ AlgHom.congr_fun (away₂Comm_comp_away₂InrAlgHom R i j) x

instance {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    IsLocalization.Away (dehomogenise j (X (R:=R) i)) (away₂ R i j) :=
  IsLocalization.isLocalization_of_algEquiv _ (away₂CommAlgEquiv R i j).symm

end MvPolynomial

open CategoryTheory

/-- Re-index an affine open cover along an equivalence `e : ι ≃ C.J` and equivalences
`new_obj i ≅ C.obj (e i)`. -/
@[simps! J obj map]
noncomputable def AlgebraicGeometry.Scheme.AffineOpenCover.equiv {X : Scheme.{u}}
      (C : AffineOpenCover.{w} X) {ι : Type v} (e : ι ≃ C.J)
      (new_obj : ι → CommRingCat.{u}) (new_e : (i : ι) → C.obj (e i) ≅ new_obj i) :
    AffineOpenCover.{v} X where
  J := ι
  obj := new_obj
  map i := (Scheme.Spec.mapIso (new_e i).op).hom ≫ C.map (e i)
  f := (e.symm <| C.f ·)
  covers x := let ⟨y, hy⟩ := C.covers x
    ⟨ConcreteCategory.hom (eqToHom (by simp) ≫ Spec.map (new_e _).inv).base y, by
      rw [← ConcreteCategory.comp_apply, ← Scheme.comp_base, Category.assoc,
        ← Category.assoc (Spec.map _), Functor.mapIso_hom, Spec_map, Iso.op_hom, Quiver.Hom.unop_op,
        ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id, Category.id_comp]
      convert hy
      exact eq_of_heq <| (eqToHom_comp_heq ..).trans <| by rw [e.apply_symm_apply]
    ⟩

/-- Re-index an affine open cover along an equivalence `ι ≃ C.J`. -/
@[simps! J] noncomputable def AlgebraicGeometry.Scheme.AffineOpenCover.equivJ {X : Scheme.{u}}
      (C : AffineOpenCover.{w} X) {ι : Type v} (e : ι ≃ C.J) : AffineOpenCover.{v} X :=
  C.equiv e (C.obj <| e ·) (fun _ ↦ Iso.refl _)

/-- Re-index an open cover along an equivalence `e : ι ≃ C.J` and equivalences
`new_obj i ≅ C.obj (e i)`. -/
@[simps! J obj map] noncomputable def AlgebraicGeometry.Scheme.OpenCover.equiv {X : Scheme.{u}}
      (C : OpenCover.{w} X) {ι : Type v} (e : ι ≃ C.J)
      (new_obj : ι → Scheme.{u}) (new_e : (i : ι) → new_obj i ≅ C.obj (e i)) :
    OpenCover.{v} X where
  J := ι
  obj := new_obj
  map i := (new_e i).hom ≫ C.map (e i)
  f := (e.symm <| C.f ·)
  covers x := let ⟨y, hy⟩ := C.covers x
    ⟨ConcreteCategory.hom (eqToHom (by simp) ≫ (new_e _).inv).base y, by
      rw [← ConcreteCategory.comp_apply, ← Scheme.comp_base, Category.assoc,
        ← Category.assoc (new_e _).inv, Iso.inv_hom_id,  Category.id_comp]
      convert hy
      exact eq_of_heq <| (eqToHom_comp_heq ..).trans <| by rw [e.apply_symm_apply]
    ⟩

/-- Re-index an affine open cover along an equivalence `ι ≃ C.J`. -/
@[simps! J] noncomputable def AlgebraicGeometry.Scheme.OpenCover.equivJ {X : Scheme.{u}}
    (C : OpenCover.{w} X) {ι : Type v} (e : ι ≃ C.J) : OpenCover.{v} X :=
  C.equiv e (C.obj <| e ·) (fun _ ↦ Iso.refl _)

namespace CategoryTheory.Limits

/-- Given such a diagram, then there is a natural isomorphism `W ×ₛ X ⟶ Y ×ₜ Z`.

```
W ≅ Y
 ↘   ↘
  S ≅ T
 ↗   ↗
X ≅ Z
```
-/
@[simps!] noncomputable def pullback.iso {C : Type u} [Category.{v} C] [HasPullbacks C]
      {W X Y Z S T : C} (f₁ : Y ⟶ T) (f₂ : Z ⟶ T)
      (e₁ : W ≅ Y) (e₂ : X ≅ Z) (e₃ : S ≅ T) :
    pullback (e₁.hom ≫ f₁ ≫ e₃.inv) (e₂.hom ≫ f₂ ≫ e₃.inv) ≅ pullback f₁ f₂ where
  hom := pullback.map _ _ _ _ e₁.hom e₂.hom e₃.hom (by aesop) (by aesop)
  inv := pullback.map _ _ _ _ e₁.inv e₂.inv e₃.inv (by aesop) (by aesop)

/-- Given such a diagram, then there is a natural isomorphism `W ×ₛ X ⟶ Y ×ₜ Z`.

```
W ≅ Y
 ↘   ↘
  S ≅ T
 ↗   ↗
X ≅ Z
```
-/
@[simps!] noncomputable def pullback.iso' {C : Type u} [Category.{v} C] [HasPullbacks C]
      {W X Y Z S T : C} {f₁ : Y ⟶ T} {f₂ : Z ⟶ T}
      {g₁ : W ⟶ S} {g₂ : X ⟶ S} (e₁ : W ≅ Y) (e₂ : X ≅ Z) (e₃ : S ≅ T)
      (h₁ : e₁.hom ≫ f₁ ≫ e₃.inv = g₁) (h₂ : e₂.hom ≫ f₂ ≫ e₃.inv = g₂) :
    pullback g₁ g₂ ≅ pullback f₁ f₂ where
  hom := pullback.map _ _ _ _ e₁.hom e₂.hom e₃.hom (by aesop) (by aesop)
  inv := pullback.map _ _ _ _ e₁.inv e₂.inv e₃.inv (by aesop) (by aesop)

section pullback_over

@[nolint unusedArguments]
noncomputable instance pullback_over {C : Type u} [Category.{v} C] [HasPullbacks C]
      {X₁ X₂ Y S : C} (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y)
      [OverClass X₁ S] [OverClass X₂ S] [OverClass Y S] [HomIsOver f₁ S] [HomIsOver f₂ S] :
    OverClass (pullback f₁ f₂) S :=
  ⟨pullback.fst _ _ ≫ X₁ ↘ S⟩

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {X₁ X₂ Y S : C} (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y)
  [OverClass X₁ S] [OverClass X₂ S] [OverClass Y S] [HomIsOver f₁ S] [HomIsOver f₂ S]

theorem pullback_fst_over : pullback.fst _ _ ≫ X₁ ↘ S = pullback f₁ f₂ ↘ S := rfl

theorem pullback_snd_over : pullback.snd _ _ ≫ X₂ ↘ S = pullback f₁ f₂ ↘ S := by
  rw [← pullback_fst_over, ← comp_over f₁, pullback.condition_assoc, comp_over f₂]

end pullback_over

@[reassoc] theorem pullback.map_fst {C : Type u} [Category.{v, u} C] {W X Y Z S T : C}
      (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
      (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂]
      (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
      (h₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (h₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    map f₁ f₂ g₁ g₂ i₁ i₂ i₃ h₁ h₂ ≫ fst _ _ = fst _ _ ≫ i₁ :=
  lift_fst ..

@[reassoc] theorem pullback.map_snd {C : Type u} [Category.{v, u} C] {W X Y Z S T : C}
      (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
      (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂]
      (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
      (h₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (h₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    map f₁ f₂ g₁ g₂ i₁ i₂ i₃ h₁ h₂ ≫ snd _ _ = snd _ _ ≫ i₂ :=
  lift_snd ..

open pullback in
/-- (S × Y₁) ×[S × X] (S × Y₂) ≅ S × (Y₁ ×[X] Y₂). -/
@[simps!] noncomputable
def pullbackProd {C : Type u} [Category.{v} C] [HasPullbacks C] [HasTerminal C] (X Y₁ Y₂ S : C)
      (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X) :
    pullback
        (map (terminal.from S) (terminal.from Y₁) (terminal.from S) (terminal.from X)
          (𝟙 S) f₁ (𝟙 _) (terminal.hom_ext ..) (terminal.hom_ext ..))
        (map (terminal.from S) (terminal.from Y₂) (terminal.from S) (terminal.from X)
          (𝟙 S) f₂ (𝟙 _) (terminal.hom_ext ..) (terminal.hom_ext ..)) ≅
      pullback (terminal.from S) (terminal.from (pullback f₁ f₂)) where
  hom := lift (fst _ _ ≫ fst _ _) (map _ _ _ _ (snd _ _) (snd _ _) (snd _ _) (by simp) (by simp))
    (by simp)
  inv := lift (map _ _ _ _ (𝟙 S) (fst _ _) (𝟙 _) (terminal.hom_ext ..) (terminal.hom_ext ..))
    (map _ _ _ _ (𝟙 S) (snd _ _) (𝟙 _) (terminal.hom_ext ..) (terminal.hom_ext ..))
    (by simp [map_comp, condition])
  hom_inv_id :=
    have : fst (map (terminal.from S) (terminal.from Y₁) (terminal.from S) (terminal.from X)
            (𝟙 S) f₁ (𝟙 (⊤_ C)) (terminal.hom_ext ..) (terminal.hom_ext ..))
          (map (terminal.from S) (terminal.from Y₂) (terminal.from S) (terminal.from X)
            (𝟙 S) f₂ (𝟙 (⊤_ C)) (terminal.hom_ext ..) (terminal.hom_ext ..)) ≫
          fst (terminal.from S) (terminal.from Y₁) =
        snd (map (terminal.from S) (terminal.from Y₁) (terminal.from S) (terminal.from X)
            (𝟙 S) f₁ (𝟙 (⊤_ C)) (terminal.hom_ext ..) (terminal.hom_ext ..))
          (map (terminal.from S) (terminal.from Y₂) (terminal.from S) (terminal.from X)
            (𝟙 S) f₂ (𝟙 (⊤_ C)) (terminal.hom_ext ..) (terminal.hom_ext ..)) ≫
        fst (terminal.from S) (terminal.from Y₂) := calc
      _ = _ ≫ (map (terminal.from S) (terminal.from Y₁) (terminal.from S) (terminal.from X)
            (𝟙 S) f₁ (𝟙 (⊤_ C)) (terminal.hom_ext ..) (terminal.hom_ext ..) ≫
              fst (terminal.from S) (terminal.from X)) :=
        congr_arg (_ ≫ ·) (by rw [map_fst, Category.comp_id])
      _ = _ := by rw [condition_assoc, map_fst]; congr 1; rw [Category.comp_id]
    hom_ext (hom_ext (by simp) (by simp)) (hom_ext (by simpa) (by simp))
  inv_hom_id := hom_ext (by simp) (hom_ext (by simp) (by simp))

open pullback in
/-- (S × Y₁) ×[S × X] (S × Y₂) ≅ S × (Y₁ ×[X] Y₂). -/
@[simps!] noncomputable
def pullbackProd' {C : Type u} [Category.{v} C] [HasPullbacks C] [HasTerminal C] (X Y₁ Y₂ S : C)
      (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X) {g₁ g₂}
      (h₁ : (map (terminal.from S) (terminal.from Y₁) (terminal.from S) (terminal.from X)
          (𝟙 S) f₁ (𝟙 _) (terminal.hom_ext ..) (terminal.hom_ext ..)) = g₁)
      (h₂ : (map (terminal.from S) (terminal.from Y₂) (terminal.from S) (terminal.from X)
          (𝟙 S) f₂ (𝟙 _) (terminal.hom_ext ..) (terminal.hom_ext ..)) = g₂) :
    pullback g₁ g₂ ≅ pullback (terminal.from S) (terminal.from (pullback f₁ f₂)) :=
  congrHom h₁.symm h₂.symm ≪≫ pullbackProd ..

end CategoryTheory.Limits

instance ULift.algebra' {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
    Algebra (ULift R) A :=
  { ULift.module with
    algebraMap :=
    { (algebraMap R A).comp (RingHomClass.toRingHom ULift.ringEquiv) with
      toFun r := algebraMap R A r.down }
    commutes' r := Algebra.commutes r.down
    smul_def' r := Algebra.smul_def r.down }

namespace AlgebraicGeometry

/- open CategoryTheory.Limits TensorProduct

/-- `Spec R ⨯ Spec S ≅ Spec (R ⊗[ℤ] S)`, using pullback to replace product. -/
noncomputable def pullbackTerminalSpecIso (R S : Type u) [CommRing R] [CommRing S] :
    pullback (terminal.from (Spec (.of R))) (terminal.from (Spec (.of S))) ≅
      Spec (.of (R ⊗[ℤ] S)) :=
  pullback.iso' (Iso.refl _) (Iso.refl _) (specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal)
      (terminal.hom_ext ..) (terminal.hom_ext ..) ≪≫
    pullbackSpecIso (ULift.{u} ℤ) R S ≪≫
    Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso <| RingEquivClass.toRingEquiv <|
        Algebra.TensorProduct.equivOfCompatibleSMul ..).op -/

lemma AffineSpace.SpecIso_Int {n : Type v} :
    (AffineSpace.SpecIso n (.of (ULift.{max u v} ℤ))).hom =
      toSpecMvPoly n (Spec (.of (ULift.{max u v} ℤ))) := by
  refine (toSpecMvPolyIntEquiv n).injective (funext fun i ↦ ?_)
  rw [toSpecMvPolyIntEquiv_apply, SpecIso_hom_appTop]
  simp [coord]

lemma AffineSpace.map_comp_SpecIso {n : Type v} {R : Type max u v} [CommRing R] :
    map n (Spec.map (CommRingCat.ofHom (algebraMap _ _))) ≫
        (AffineSpace.SpecIso n (.of (ULift.{max u v} ℤ))).hom =
      toSpecMvPoly n (Spec (.of R)) := by
  rw [← map_toSpecMvPoly (Spec.map (CommRingCat.ofHom (algebraMap (ULift ℤ) R))), SpecIso_Int]

lemma AffineSpace.SpecIso_comp_map {n : Type v} {R : Type max u v} [CommRing R] :
    (AffineSpace.SpecIso n (.of R)).hom ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap _ _))) =
      toSpecMvPoly n (Spec (.of R)) := by
  rw [← AffineSpace.map_comp_SpecIso, map_Spec_map, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, CommRingCat.hom_ofHom]

-- Causes a loop with `Scheme.ΓSpecIso_inv_naturality` if tagged with `@[simp]`.
lemma Spec.map_app_top {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (Spec.map f).app ⊤ = (Scheme.ΓSpecIso R).hom ≫ f ≫ (Scheme.ΓSpecIso S).inv :=
  (Iso.inv_comp_eq ..).1 (Scheme.ΓSpecIso_inv_naturality ..).symm

-- Causes a loop with `Scheme.ΓSpecIso_inv_naturality` if tagged with `@[simp]`.
lemma Spec.map_appTop {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (Spec.map f).appTop = (Scheme.ΓSpecIso R).hom ≫ f ≫ (Scheme.ΓSpecIso S).inv :=
  Spec.map_app_top f

lemma Spec.map_app_top_hom {R S : CommRingCat.{u}} (f : R ⟶ S) (x : R) :
    ((Spec.map f).app ⊤).hom ((Scheme.ΓSpecIso R).inv x) = (Scheme.ΓSpecIso S).inv (f x) :=
  ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality f).symm x

@[simp] lemma Spec.map_appTop_hom {R S : CommRingCat.{u}} (f : R ⟶ S) (x : R) :
    (Spec.map f).appTop ((Scheme.ΓSpecIso R).inv x) = (Scheme.ΓSpecIso S).inv (f x) :=
  Spec.map_app_top_hom f x

end AlgebraicGeometry

end MOVE

open CategoryTheory Limits MvPolynomial HomogeneousLocalization

noncomputable section

namespace AlgebraicGeometry

variable (n : Type v) (S : Scheme.{max u v})

attribute [local instance] gradedAlgebra

/-- `ℙ(n; S)` is the projective `n`-space over `S`.
Note that `n` is an arbitrary index type (e.g. `Fin m`). -/
def ProjectiveSpace (n : Type v) (S : Scheme.{max u v}) : Scheme.{max u v} :=
  pullback (terminal.from S) (terminal.from (Proj (homogeneousSubmodule n (ULift.{max u v} ℤ))))

@[inherit_doc] scoped notation "ℙ("n"; "S")" => ProjectiveSpace n S

namespace Proj

/- (See the notes in `SpecIso`.)
Here we construct these objects:
3. `Proj (homogeneousSubmodule n R)` is covered by `i ↦ Spec R[{Xₖ // k ≠ i}]`.
   (The open cover is `openCoverMvPolynomial n R`.)
4. The intersection is `Spec (away₂ R i j)`.
   (The isomorphism is `pullbackOpenCoverMvPolynomial R i j`.)
-/

/-- The canonical affine open cover of `Proj (MvPolynomial σ R)`. The cover is indexed by `σ`,
and each `i : σ` corresponds to `Spec (MvPolynomial {k // k ≠ i} R)`. -/
@[simps! J] def openCoverMvPolynomial (σ : Type*) (R : Type*) [CommRing R] :
    (Proj (homogeneousSubmodule σ R)).AffineOpenCover :=
  (openCoverOfISupEqTop
      (homogeneousSubmodule σ R) .X (fun _ ↦ isHomogeneous_X _ _) (fun _ ↦ zero_lt_one)
      (by rw [homogeneous_eq_span, Ideal.span_le, Set.range_subset_iff]; exact
        fun i ↦ Ideal.subset_span <| Set.mem_range_self _)).equiv
    (Equiv.refl σ) (.of <| MvPolynomial {k // k ≠ ·} R) (algEquivAway R · |>.toCommRingCatIso)

lemma openCoverMvPolynomial_obj {σ R : Type*} [CommRing R] (i : σ) :
    (Proj.openCoverMvPolynomial σ R).obj i = .of (MvPolynomial {k // k ≠ i} R) :=
  rfl

lemma openCoverMvPolynomial_map {σ R : Type*} [CommRing R] (i : σ) :
    (Proj.openCoverMvPolynomial σ R).map i = Spec.map (CommRingCat.ofHom ↑(contract R i)) ≫
      awayι (homogeneousSubmodule σ R) (X i) (isHomogeneous_X R i) zero_lt_one :=
  rfl

/-- The intersection (i.e. pullback) of the basic opens on `ℙ(n; Spec R)` defined by `Xᵢ` and `Xⱼ`
is `Spec R[n,1/Xⱼ]`. -/
def pullbackOpenCoverMvPolynomial {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    pullback (openCoverMvPolynomial σ R |>.map i) (openCoverMvPolynomial σ R |>.map j) ≅
      Spec (CommRingCat.of (away₂ R i j)) :=
  pullback.iso' _ _ (Iso.refl _) (by aesop) (by aesop) ≪≫ pullbackAwayιIso _ _ _ _ _ rfl ≪≫
    Scheme.Spec.mapIso (algEquivAwayMul R i j).symm.toCommRingCatIso.op

@[simp] lemma pullbackOpenCoverMvPolynomial_hom_inl {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    (Proj.pullbackOpenCoverMvPolynomial R i j).hom ≫
        Spec.map (CommRingCat.ofHom (away₂Inl _ _ _)) =
      pullback.fst _ _ := by
  have := congr_arg (Spec.map <| CommRingCat.ofHom ·) (ringEquivAwayMul_symm_comp_away₂Inl R i j)
  simp at this
  have := congr_arg (Spec.map <| CommRingCat.ofHom <| RingHomClass.toRingHom ·)
    (contract_comp_expand R i)
  simp [-contract_comp_expand, AlgHom.comp_toRingHom] at this
  simp [*, pullbackOpenCoverMvPolynomial, openCoverOfISupEqTop, openCoverMvPolynomial_obj,
    openCoverMvPolynomial_map]

@[simp] lemma pullbackOpenCoverMvPolynomial_hom_inr {σ : Type*} (R : Type*) [CommRing R] (i j : σ) :
    (Proj.pullbackOpenCoverMvPolynomial R i j).hom ≫
        Spec.map (CommRingCat.ofHom (away₂Inr _ _ _)) =
      pullback.snd _ _ := by
  have := congr_arg (Spec.map <| CommRingCat.ofHom ·) (ringEquivAwayMul_symm_comp_away₂Inr R i j)
  simp at this
  have := congr_arg (Spec.map <| CommRingCat.ofHom <| RingHomClass.toRingHom ·)
    (contract_comp_expand R j)
  simp [-contract_comp_expand, AlgHom.comp_toRingHom] at this
  simp [*, pullbackOpenCoverMvPolynomial, openCoverOfISupEqTop, openCoverMvPolynomial_obj,
    openCoverMvPolynomial_map]

end Proj

namespace ProjectiveSpace

@[simps -isSimp]
instance over : ℙ(n; S).CanonicallyOver S where
  hom := pullback.fst _ _

/-- The map from the projective `n`-space over `S` to the integral model `Proj ℤ[n]`. -/
def toProjMvPoly : ℙ(n; S) ⟶ Proj (homogeneousSubmodule n (ULift.{max u v} ℤ)) := pullback.snd ..

/-- The canonical open cover of `ℙ(n; S)` indexed by `n`, where each coordinate `i : n` corresponds
to the scheme `𝔸({k // k ≠ i}; S)`. -/
def openCover : Scheme.OpenCover.{v} ℙ(n; S) :=
  (Scheme.Pullback.openCoverOfRight ((Proj.openCoverMvPolynomial n
      (ULift.{max u v} ℤ)).openCover.equivJ Equiv.ulift) _ _).equiv
    Equiv.ulift.symm (fun i : n ↦ 𝔸({k // k ≠ i}; S)) (fun _ : n ↦ pullback.iso' (Iso.refl S)
      (Iso.refl _) (Iso.refl _) (terminal.hom_ext ..) (terminal.hom_ext ..))

@[simp] lemma openCover_J : (openCover n S).J = n := rfl
@[simp] lemma openCover_obj (i : n) : (openCover n S).obj i = 𝔸({k // k ≠ i}; S) := rfl

instance (i : n) : ((openCover n S).obj i).CanonicallyOver S :=
  AffineSpace.over _ _

theorem openCover_obj_over (i : n) : (openCover n S).obj i ↘ S = pullback.fst _ _ := rfl

lemma openCover_map_fst (i : n) : (openCover n S).map i ≫ pullback.fst _ _ =
    𝔸({k // k ≠ i}; S) ↘ S := by
  simp [openCover, Scheme.OpenCover.equiv, AffineSpace.over_over]

instance openCover_map_over (i : n) : ((openCover n S).map i).IsOver S :=
  ⟨openCover_map_fst ..⟩

lemma openCover_map_snd (i : n) : (openCover n S).map i ≫ pullback.snd _ _ =
    AffineSpace.toSpecMvPoly {k // k ≠ i} S ≫ (Proj.openCoverMvPolynomial n (ULift ℤ)).map i := by
  simp [openCover, Scheme.OpenCover.equiv, AffineSpace.toSpecMvPoly, Scheme.OpenCover.equivJ]

lemma openCover_map (i : n) : (openCover.{v, u} n S).map i = pullback.map _ _ _ _ (𝟙 S)
    ((Proj.openCoverMvPolynomial n _).map i) (𝟙 _) (terminal.hom_ext ..) (terminal.hom_ext ..) :=
  pullback.hom_ext (by simp [openCover_map_fst, AffineSpace.over_over])
    (by simp [openCover_map_snd, AffineSpace.toSpecMvPoly])

@[simp] lemma pullback_fst_openCover_fst (i j : n) :
    pullback.fst ((openCover n S).map i) ((openCover n S).map j) ≫ pullback.fst _ _ =
      pullback.snd ((openCover n S).map i) ((openCover n S).map j) ≫ pullback.fst _ _ :=
  (pullback_fst_over ..).trans (pullback_snd_over ..).symm

section pullback

variable {n} (i j : n)

/-- The intersection of the two open sets `Xᵢ ≠ 0` and `Xⱼ ≠ 0`. See `pullbackOpenCover`. -/
abbrev opens₂ (i j : n) : Scheme.{max u v} :=
  pullback (terminal.from S) (terminal.from (Spec <| .of <| away₂ (ULift.{max u v} ℤ) i j))

@[simps -isSimp]
instance opens₂Over : (opens₂ S i j).CanonicallyOver S where
  hom := pullback.fst _ _

/-- The map from `opens₂ S i j` to the integral model. -/
def opens₂ToSpec : opens₂ S i j ⟶ Spec (.of (away₂ (ULift.{max u v} ℤ) i j)) :=
  pullback.snd _ _

/-- The inclusion `opens₂ S i j` into `Xᵢ ≠ 0`. -/
def opens₂Fst (i j : n) : opens₂ S i j ⟶ (openCover n S).obj i :=
  pullback.map _ _ _ _ (𝟙 S) (Spec.map <| CommRingCat.ofHom <| away₂Inl _ i j) (𝟙 _)
    (terminal.hom_ext ..) (terminal.hom_ext ..)

/-- The inclusion `opens₂ S i j` into `Xⱼ ≠ 0`. -/
def opens₂Snd (i j : n) : opens₂ S i j ⟶ (openCover n S).obj j :=
  pullback.map _ _ _ _ (𝟙 S) (Spec.map <| CommRingCat.ofHom <| away₂Inr _ i j) (𝟙 _)
    (terminal.hom_ext ..) (terminal.hom_ext ..)

instance : HomIsOver (opens₂Fst S i j) S :=
  ⟨by rw [opens₂Fst, openCover_obj_over, pullback.map_fst, opens₂Over_over, Category.comp_id]⟩

instance : HomIsOver (opens₂Snd S i j) S :=
  ⟨by rw [opens₂Snd, openCover_obj_over, pullback.map_fst, opens₂Over_over, Category.comp_id]⟩

lemma opens₂Fst_comp_toSpec : opens₂Fst.{v, u} S i j ≫ AffineSpace.toSpecMvPoly _ _ =
    opens₂ToSpec.{v, u} S i j ≫ Spec.map (CommRingCat.ofHom (away₂Inl _ i j)) := by
  rw [opens₂Fst, AffineSpace.toSpecMvPoly, pullback.map_snd]; rfl

lemma opens₂Snd_comp_toSpec : opens₂Snd.{v, u} S i j ≫ AffineSpace.toSpecMvPoly _ _ =
    opens₂ToSpec.{v, u} S i j ≫ Spec.map (CommRingCat.ofHom (away₂Inr _ i j)) := by
  rw [opens₂Snd, AffineSpace.toSpecMvPoly, pullback.map_snd]; rfl

/-- The intersection (i.e. pullback) of the basic opens on `ℙ(n; S)` defined by `Xᵢ` and `Xⱼ`
is `S × ℤ[{k // k ≠ i}, 1/Xⱼ]`. -/
def pullbackOpenCover (i j : n) : pullback ((openCover n S).map i) ((openCover n S).map j) ≅
    opens₂ S i j :=
  pullbackProd' _ _ _ _ _ _ (by rw [openCover_map]) (by rw [openCover_map]) ≪≫
    pullback.iso' (Iso.refl _) (Proj.pullbackOpenCoverMvPolynomial ..) (Iso.refl _)
      (terminal.hom_ext ..) (terminal.hom_ext ..)

@[reassoc] lemma pullbackOpenCover_hom_opens₂Fst :
    (pullbackOpenCover.{v, u} S i j).hom ≫ opens₂Fst.{v, u} S i j = pullback.fst _ _ := by
  refine pullback.hom_ext ?_ ?_ <;> simp [opens₂Fst, pullbackOpenCover]

@[reassoc] lemma pullbackOpenCover_hom_opens₂Snd :
    (pullbackOpenCover.{v, u} S i j).hom ≫ opens₂Snd.{v, u} S i j = pullback.snd _ _ := by
  refine pullback.hom_ext ?_ ?_ <;> simp [opens₂Snd, pullbackOpenCover]

@[reassoc] lemma pullbackOpenCover_inv_fst :
    (pullbackOpenCover.{v, u} S i j).inv ≫ pullback.fst _ _ = opens₂Fst.{v, u} S i j := by
  rw [Iso.inv_comp_eq, pullbackOpenCover_hom_opens₂Fst]

@[reassoc] lemma pullbackOpenCover_inv_snd :
    (pullbackOpenCover.{v, u} S i j).inv ≫ pullback.snd _ _ = opens₂Snd.{v, u} S i j := by
  rw [Iso.inv_comp_eq, pullbackOpenCover_hom_opens₂Snd]

instance : HomIsOver (pullbackOpenCover S i j).hom S :=
  ⟨by simp_rw [← comp_over (f := opens₂Fst S i j) S, ← Category.assoc,
    pullbackOpenCover_hom_opens₂Fst, pullback_fst_over]⟩

instance : HomIsOver (pullbackOpenCover S i j).inv S :=
  ⟨by rw [Iso.inv_comp_eq, comp_over]⟩

instance : IsOpenImmersion (opens₂Fst S i j) := by
  rw [← (Iso.inv_comp_eq _).2 (pullbackOpenCover_hom_opens₂Fst S i j).symm]; infer_instance

instance : IsOpenImmersion (opens₂Snd S i j) := by
  rw [← (Iso.inv_comp_eq _).2 (pullbackOpenCover_hom_opens₂Snd S i j).symm]; infer_instance

lemma range_opens₂Fst : Set.range (opens₂Fst S i j).base =
    (pullback.snd _ _ : (openCover n S).obj i ⟶ _).base ⁻¹'
      (SetLike.coe (PrimeSpectrum.basicOpen (dehomogenise i (X (R:=ULift.{max u v} ℤ) j)))) := by
  rw [opens₂Fst]
  refine (Scheme.Pullback.range_map ..).trans ?_
  rw [Scheme.id.base, hom_id, Set.range_id, Set.preimage_univ, Set.univ_inter]
  exact congr_arg _ (PrimeSpectrum.localization_away_comap_range ..)

lemma range_opens₂Snd : Set.range (opens₂Snd S i j).base =
    (pullback.snd _ _ : (openCover n S).obj j ⟶ _).base ⁻¹'
      (SetLike.coe (PrimeSpectrum.basicOpen (dehomogenise j (X (R:=ULift.{max u v} ℤ) i)))) := by
  rw [opens₂Snd]
  refine (Scheme.Pullback.range_map ..).trans ?_
  rw [Scheme.id.base, hom_id, Set.range_id, Set.preimage_univ, Set.univ_inter]
  exact congr_arg _ (PrimeSpectrum.localization_away_comap_range ..)

lemma opens₂Fst_appTop_coord (k : {k // k ≠ i}) :
    (opens₂Fst.{v, u} S i j).appTop (AffineSpace.coord S k) =
      (opens₂ToSpec.{v, u} S i j).appTop.hom ((Scheme.ΓSpecIso _).inv
        (away₂Inl _ _ _ (X k))) := by
  rw [AffineSpace.coord, AffineSpace.toSpecMvPolyIntEquiv_apply]
  refine (hom_comp_apply ..).symm.trans ?_
  rw [← Scheme.comp_appTop, opens₂Fst_comp_toSpec, Scheme.comp_appTop, hom_comp_apply,
    Spec.map_appTop_hom]
  rfl

lemma opens₂Snd_appTop_coord (k : {k // k ≠ j}) :
    (opens₂Snd.{v, u} S i j).appTop (AffineSpace.coord S k) =
      (opens₂ToSpec.{v, u} S i j).appTop.hom ((Scheme.ΓSpecIso _).inv
        (away₂Inr _ _ _ (X k))) := by
  rw [AffineSpace.coord, AffineSpace.toSpecMvPolyIntEquiv_apply]
  refine (hom_comp_apply ..).symm.trans ?_
  rw [← Scheme.comp_appTop, opens₂Snd_comp_toSpec, Scheme.comp_appTop, hom_comp_apply,
    Spec.map_appTop_hom]
  rfl

end pullback

variable {S₁ S₂ S₃ : Scheme.{max u v}}

/-- Given a morphism `S₁ ⟶ S₂` of schemes, construct a morphism `ℙ(n; S₁) ⟶ ℙ(n; S₂)`. -/
def map (f : S₁ ⟶ S₂) : ℙ(n; S₁) ⟶ ℙ(n; S₂) :=
  pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (terminal.hom_ext ..) (terminal.hom_ext ..)

lemma map_id : map n (𝟙 S) = 𝟙 ℙ(n; S) := pullback.map_id

lemma map_comp (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃) : map n (f ≫ g) = map n f ≫ map n g := by
  unfold map; rw [pullback.map_comp]; rfl

/-- Given an isomorphism `S₁ ≅ S₂` of schemes, construct an isomorphism `ℙ(n; S₁) ≅ ℙ(n; S₂)`. -/
def mapIso (f : S₁ ≅ S₂) : ℙ(n; S₁) ≅ ℙ(n; S₂) :=
  ⟨map n f.hom, map n f.inv, by rw [← map_comp, f.hom_inv_id, map_id],
    by rw [← map_comp, f.inv_hom_id, map_id]⟩

lemma map_over (f : S₁ ⟶ S₂) : map n f ≫ ℙ(n; S₂) ↘ S₂ = ℙ(n; S₁) ↘ S₁ ≫ f := by
  rw [map, over_over, pullback.map_fst, over_over]

section affine

variable {n} (R : Type max u v) [CommRing R] (i j : n)

theorem Spec_away₂Inl_range :
    Set.range (ConcreteCategory.hom (Spec.map (CommRingCat.ofHom (away₂Inl R i j))).base) =
      SetLike.coe (PrimeSpectrum.basicOpen (dehomogenise i (X (R:=R) j))) :=
  PrimeSpectrum.localization_away_comap_range ..

/-- The isomorphism between `D(XᵢXⱼ)` of two models: the model `Spec R ⨯ Proj ℤ[n]` vs. the model
`Proj R[n]`. -/
def opens₂IsoSpecAway₂ (R : Type max u v) [CommRing R] (i j : n) :
    opens₂ (Spec (.of R)) i j ≅ Spec (.of (away₂ R i j)) := by
  refine AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq
    (opens₂Fst _ i j ≫ (AffineSpace.SpecIso _ (.of R)).hom)
    (Spec.map <| CommRingCat.ofHom <| away₂Inl R i j) ?_
  rw [Spec_away₂Inl_range, Scheme.comp_base, hom_comp, Set.range_comp, range_opens₂Fst,
    ← AffineSpace.toSpecMvPoly, ← AffineSpace.SpecIso_comp_map, Scheme.comp_base, hom_comp,
    Set.preimage_comp, Spec.map_base, CommRingCat.hom_ofHom, ← TopCat.Hom.hom, ← TopCat.Hom.hom,
    TopCat.hom_ofHom, ← TopologicalSpace.Opens.coe_comap]
  conv => enter [1,2,2,1]; exact PrimeSpectrum.comap_basicOpen ..
  rw [map_dehomogenise, map_X]
  exact Set.image_preimage_eq _ (ConcreteCategory.bijective_of_isIso _).surjective

@[reassoc] lemma opens₂IsoSpecAway₂_hom_comp_away₂Inl :
    (opens₂IsoSpecAway₂.{v, u} R i j).hom ≫ Spec.map (CommRingCat.ofHom (away₂Inl R i j)) =
      opens₂Fst.{v, u} (Spec (.of R)) i j ≫ (AffineSpace.SpecIso {k // k ≠ i} (.of R)).hom :=
  IsOpenImmersion.isoOfRangeEq_hom_fac ..

@[reassoc] lemma opens₂IsoSpecAway₂_inv_comp_opens₂Fst :
    (opens₂IsoSpecAway₂.{v, u} R i j).inv ≫ opens₂Fst.{v, u} (Spec (.of R)) i j =
      Spec.map.{max u v} (CommRingCat.ofHom (away₂Inl R i j)) ≫
        (AffineSpace.SpecIso.{v, u} {k // k ≠ i} (CommRingCat.of.{max u v} R)).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, opens₂IsoSpecAway₂_hom_comp_away₂Inl, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

lemma opens₂IsoSpecAway₂_hom_comp_algebraMap :
    (opens₂IsoSpecAway₂.{v, u} R i j).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (away₂ R i j))) =
      opens₂.{v, u} (Spec (.of R)) i j ↘ Spec (.of R) := by
  rw [← away₂Inl_comp_C, CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc,
    opens₂IsoSpecAway₂_hom_comp_away₂Inl, ← comp_over (f := opens₂Fst _ i j), Category.assoc]
  exact congr_arg _ <| Eq.symm <| (Iso.inv_comp_eq ..).1 <| AffineSpace.SpecIso_inv_over ..

lemma opens₂IsoSpecAway₂_hom_appTop_away₂Inl (k : {k // k ≠ i}) :
    (opens₂IsoSpecAway₂.{v, u} R i j).hom.appTop ((Scheme.ΓSpecIso _).inv
        (away₂Inl R i j (X k))) =
      (opens₂ToSpec.{v, u} (Spec (.of R)) i j).appTop
        ((Scheme.ΓSpecIso _).inv (away₂Inl _ i j (X k))) := by
  have := CategoryTheory.congr_fun (congr_arg Scheme.Hom.appTop <|
    opens₂IsoSpecAway₂_hom_comp_away₂Inl R i j) ((Scheme.ΓSpecIso _).inv (X k))
  rw [← CommRingCat.hom_ofHom (away₂Inl (ULift.{max u v, 0} ℤ) i j), ← Spec.map_appTop_hom,
    ← hom_comp_apply, ← hom_comp_apply, ← Scheme.comp_appTop, ← opens₂Fst_comp_toSpec]
  simp only [Scheme.comp_appTop, hom_comp_apply] at this ⊢
  convert this
  · rw [Spec.map_appTop_hom]; simp only [CommRingCat.hom_ofHom]
  · rw [← AffineSpace.SpecIso_inv_appTop_coord (.of R), ← hom_comp_apply, ← hom_comp_apply,
      ← Scheme.comp_appTop, Iso.hom_inv_id, Scheme.id_appTop]; rfl

lemma opens₂IsoSpecAway₂_hom_appTop_away₂Inl_dehomogenise (k : n) :
    (opens₂IsoSpecAway₂.{v, u} R i j).hom.appTop ((Scheme.ΓSpecIso _).inv
        (away₂Inl R i j (dehomogenise i (X k)))) =
      (opens₂ToSpec.{v, u} (Spec (.of R)) i j).appTop
        ((Scheme.ΓSpecIso _).inv (away₂Inl _ i j (dehomogenise i (X k)))) := by
  by_cases h : k = i
  · simp only [h, dehomogenise_X_self, map_one]
  · rw [dehomogenise_X_of_ne h, dehomogenise_X_of_ne h, opens₂IsoSpecAway₂_hom_appTop_away₂Inl]

section

attribute [local instance] Invertible.map

lemma opens₂IsoSpecAway₂_hom_appTop_away₂Inl_invOf_dehomogenise :
    (opens₂IsoSpecAway₂.{v, u} R i j).hom.appTop ((Scheme.ΓSpecIso _).inv
        (⅟ (away₂Inl R i j (dehomogenise i (X j))))) =
      (opens₂ToSpec.{v, u} (Spec (.of R)) i j).appTop
        ((Scheme.ΓSpecIso _).inv (⅟ (away₂Inl _ i j (dehomogenise i (X j))))) := by
  simp_rw [map_invOf, opens₂IsoSpecAway₂_hom_appTop_away₂Inl_dehomogenise.{v, u} R i j j]

end

@[reassoc] lemma opens₂IsoSpecAway₂_hom_comp_away₂Inr :
    (opens₂IsoSpecAway₂.{v, u} R i j).hom ≫ Spec.map (CommRingCat.ofHom (away₂Inr R i j)) =
      opens₂Snd.{v, u} (Spec (.of R)) i j ≫ (AffineSpace.SpecIso {k // k ≠ j} (.of R)).hom := by
  rw [← Iso.comp_inv_eq]
  refine AffineSpace.hom_ext ?_ fun k ↦ ?_
  · rw [Category.assoc, AffineSpace.SpecIso_inv_over, Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, away₂Inr_comp_C, opens₂IsoSpecAway₂_hom_comp_algebraMap, comp_over]
  simp only [openCover_obj, Category.assoc, Scheme.comp_appTop, CommRingCat.hom_comp,
    RingHom.coe_comp, Function.comp_apply]
  refine Eq.trans ?_ (opens₂Snd_appTop_coord ..).symm
  rw [AffineSpace.SpecIso_inv_appTop_coord, Spec.map_appTop_hom, ← CommRingCat.Hom.hom,
    ← CommRingCat.Hom.hom, ← CommRingCat.Hom.hom, CommRingCat.hom_ofHom, away₂Inr_X, away₂Inr_X]
  simp_rw [map_mul, opens₂IsoSpecAway₂_hom_appTop_away₂Inl_dehomogenise.{v, u},
    opens₂IsoSpecAway₂_hom_appTop_away₂Inl_invOf_dehomogenise.{v, u}]

@[reassoc] lemma opens₂IsoSpecAway₂_inv_comp_opens₂Snd :
    (opens₂IsoSpecAway₂.{v, u} R i j).inv ≫ opens₂Snd.{v, u} (Spec (.of R)) i j =
      Spec.map.{max u v} (CommRingCat.ofHom (away₂Inr R i j)) ≫
        (AffineSpace.SpecIso.{v, u} {k // k ≠ j} (CommRingCat.of.{max u v} R)).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, opens₂IsoSpecAway₂_hom_comp_away₂Inr, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/- Notes:
`SpecIso` is constructed using multiple steps. First we construct all of the intermediate objects:
1. `ℙ(n; S)` has a canonical open cover by `i ↦ 𝔸({k // k ≠ i}, S)`.
   (The open cover is `openCover n R`.)
2. The intersection (i.e. pullback) of the opens corresponding to `i` and `j` is `opens₂ S i j`.
   (The isomorphism is `pullbackOpenCover R i j`.)
And on the target side:
3. `Proj (homogeneousSubmodule n R)` is covered by `i ↦ Spec R[{Xₖ // k ≠ i}]`.
   (The open cover is `Proj.openCoverMvPolynomial n R`.)
4. The intersection is `Spec (away₂ R i j)`.
   (The isomorphism is `Proj.pullbackOpenCoverMvPolynomial R i j`.)

Then the comparison isomorphisms:
- `1 ≅ 3`: This is `AffineSpace.SpecIso`.
- `2 ≅ 4`: This is `opens₂IsoSpecAway₂`.

We also note that we use other comparison isomorphisms to move between the "Proj model" and the
"Spec model":
- The set `Xᵢ ≠ 0` on `Proj R[n]` is naturally `Spec (HomogeneousLocalization.Away _ (X i))`, and
  the isomorphism of that with `Spec R[{Xₖ // k ≠ i}]` is given by `algEquivAway`.
- And the set `Xᵢ ≠ 0 ∧ Xⱼ ≠ 0` is `Spec (HomogeneousLocalization.Away _ (X i * X j))`, and
  the isomorphism with `Spec R[{Xₖ // k ≠ i}, 1/Xⱼ]` is `algEquivAwayMul`. Note also we have the
  `abbrev away₂ R i j := R[{Xₖ // k ≠ i}, 1/Xⱼ]`.
- And naturally we would need maps `R[{Xₖ // k ≠ i}] ⟶ away₂ R i j` and
  `R[{Xₖ // k ≠ j}] ⟶ away₂ R i j`. These two maps are called `away₂Inl R i j` and `away₂Inr R i j`.
-/

variable (n) in
/-- `ℙ(n; Spec R)` is isomorphic to `Proj R[n]`. -/
def SpecIso (R : Type max u v) [CommRing R] :
    ℙ(n; Spec (CommRingCat.of.{max u v} R)) ≅ Proj (homogeneousSubmodule n R) := by
  refine {
    hom := Scheme.Cover.glueMorphisms (openCover n (Spec (.of R)))
      (fun i ↦ (AffineSpace.SpecIso {k // k ≠ i} (.of R)).hom ≫
        (Proj.openCoverMvPolynomial n R).map i) fun i j ↦ ?_
    inv := Scheme.Cover.glueMorphisms (Proj.openCoverMvPolynomial n R).openCover
      (fun i ↦ (AffineSpace.SpecIso {k // k ≠ i} (.of R)).inv ≫ (openCover n _).map i)
      fun i j ↦ ?_
    hom_inv_id := Scheme.Cover.hom_ext (openCover n (Spec (.of R))) _ _ fun i ↦?_
    inv_hom_id := Scheme.Cover.hom_ext (Proj.openCoverMvPolynomial n R).openCover _ _ fun i ↦?_
  }
  · rw [← pullbackOpenCover_hom_opens₂Fst, Category.assoc,
      ← opens₂IsoSpecAway₂_hom_comp_away₂Inl_assoc.{v, u} R i j,
      ← pullbackOpenCover_hom_opens₂Snd, Category.assoc,
      ← opens₂IsoSpecAway₂_hom_comp_away₂Inr_assoc.{v, u} R i j,
      ← (Iso.inv_comp_eq ..).2 (Proj.pullbackOpenCoverMvPolynomial_hom_inl ..).symm,
      ← (Iso.inv_comp_eq ..).2 (Proj.pullbackOpenCoverMvPolynomial_hom_inr ..).symm,
      Category.assoc, Category.assoc]
    simp_rw [openCover_J, pullback.condition]
  · simp only [Scheme.AffineOpenCover.openCover_J, Scheme.AffineOpenCover.openCover_obj,
      Scheme.AffineOpenCover.openCover_map]
    rw [← Proj.pullbackOpenCoverMvPolynomial_hom_inl R, Category.assoc,
      ← Proj.pullbackOpenCoverMvPolynomial_hom_inr R, Category.assoc]
    conv => enter [1,2]; exact (opens₂IsoSpecAway₂_inv_comp_opens₂Fst_assoc ..).symm
    conv => enter [2,2]; exact (opens₂IsoSpecAway₂_inv_comp_opens₂Snd_assoc ..).symm
    rw [← pullbackOpenCover_inv_fst, ← pullbackOpenCover_inv_snd, Category.assoc, Category.assoc,
      pullback.condition]
  · rw [Scheme.Cover.ι_glueMorphisms_assoc, Category.assoc]
    conv => enter [1,2]; exact Scheme.Cover.ι_glueMorphisms ..
    simp
  · rw [Scheme.Cover.ι_glueMorphisms_assoc, Category.assoc, Scheme.Cover.ι_glueMorphisms]
    simp

lemma openCover_comp_SpecIso_hom : (openCover n (Spec (.of R))).map i ≫ (SpecIso n _).hom =
    (AffineSpace.SpecIso _ _).hom ≫ (Proj.openCoverMvPolynomial n R).map i := by
  rw [SpecIso, Scheme.Cover.ι_glueMorphisms]; rfl

end affine

/- GOALS
* Subspace cut out by a polynomial
* Locally (i.e. at stalk) points given by [x₀ : ... : xₙ]
-/

end ProjectiveSpace

end AlgebraicGeometry
