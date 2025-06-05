/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Homogeneous

section MOVE

namespace HomogeneousLocalization

theorem val_fromZeroRingHom {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
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

theorem algebraMap_eq' {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
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

end Away

end HomogeneousLocalization

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
    MvPolynomial σ R →ₐ[R] MvPolynomial { j // j ≠ i } R :=
  aeval fun j ↦ if H : j = i then 1 else X ⟨j, H⟩

theorem dehomogenise_C {σ R : Type*} [CommSemiring R] (i : σ) (r : R) :
    dehomogenise i (C r) = C r :=
  aeval_C ..

@[simp] theorem dehomogenise_X_self {σ R : Type*} [CommSemiring R] (i : σ) :
    dehomogenise (R:=R) i (X i) = 1 := by
  rw [dehomogenise, aeval_X, dif_pos rfl]

@[simp] theorem dehomogenise_X {σ R : Type*} [CommSemiring R] {i : σ} (j : {j // j ≠ i}) :
    dehomogenise (R:=R) i (X j) = X j := by
  rw [dehomogenise, aeval_X, dif_neg]

@[simp] theorem dehomogenise_X_of_ne {σ R : Type*} [CommSemiring R] {i j : σ} (h : j ≠ i) :
    dehomogenise (R:=R) i (X j) = X ⟨j, h⟩ := by
  rw [dehomogenise, aeval_X, dif_neg]

@[simp] theorem dehomogenise_X_powers {σ R : Type*} [CommSemiring R] (i : σ)
    (d : Submonoid.powers (X i)) : dehomogenise (R:=R) i d.val = 1 := by
  rcases d with ⟨_, _, rfl⟩; rw [map_pow, dehomogenise_X_self, one_pow]

@[simp] theorem dehomogenise_of_mem_X_powers {σ R : Type*} [CommSemiring R] {i : σ} {d}
    (hd : d ∈ Submonoid.powers (X i)) : dehomogenise (R:=R) i d = 1 :=
  dehomogenise_X_powers _ ⟨d, hd⟩

/-- Map `Xⱼ/Xᵢ` to `Xⱼ`, contracting away the variable `Xᵢ`. -/
noncomputable def contract {σ : Type*} (R : Type*) [CommRing R] (i : σ) :
    Away (homogeneousSubmodule σ R) (X i) →ₐ[R]
      MvPolynomial { j // j ≠ i } R where
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
    MvPolynomial { j // j ≠ i } R →ₐ[R]
      Away (homogeneousSubmodule σ R) (X i) :=
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

theorem expand_dehomogenise_of_homogeneous {σ R : Type*} [CommRing R] (i : σ) {n : ℕ}
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
noncomputable def algEquivAway {σ : Type*} (R : Type*) [CommRing R] (i : σ) :
    MvPolynomial { j // j ≠ i } R ≃ₐ[R] Away (homogeneousSubmodule σ R) (X i) where
  invFun := contract R i
  left_inv p := by
    change contract R i (aeval _ p) = p
    induction p using induction_on
    · rw [aeval_C, algebraMap_apply', contract_mk',
        SetLike.GradeZero.coe_algebraMap, algebraMap_eq, dehomogenise_C]
    · simp only [map_add, *]
    · simp only [map_mul, *, aeval_X, contract_mk, dehomogenise_X]
  right_inv p := by
    change expand R i (contract R i p) = p
    rcases Away.mk_surjective _ (isHomogeneous_X ..) p with ⟨d, r, hr, rfl⟩
    rw [contract_mk, expand_dehomogenise_of_homogeneous _ (by rwa [nsmul_one, Nat.cast_id] at hr)]
  __ := expand R i

end MvPolynomial

end MOVE

open CategoryTheory Limits MvPolynomial

noncomputable section

namespace AlgebraicGeometry

universe v u

variable (n : Type v) (S : Scheme.{max u v})

attribute [local instance] gradedAlgebra

/-- `ℙ(n; S)` is the projective `n`-space over `S`.
Note that `n` is an arbitrary index type (e.g. `Fin m`). -/
def ProjectiveSpace (n : Type v) (S : Scheme.{max u v}) : Scheme.{max u v} :=
  pullback (terminal.from S) (terminal.from (Proj (homogeneousSubmodule n (ULift.{max u v} ℤ))))

namespace ProjectiveSpace

@[inherit_doc] scoped [AlgebraicGeometry] notation "ℙ("n"; "S")" => ProjectiveSpace n S

@[simps -isSimp]
instance over : ℙ(n; S).CanonicallyOver S where
  hom := pullback.fst _ _

/-- The map from the projective `n`-space over `S` to the integral model `Proj ℤ[n]`. -/
def toProjMvPoly : ℙ(n; S) ⟶ Proj (homogeneousSubmodule n (ULift.{max u v} ℤ)) := pullback.snd _ _

/-- The open set in `ℙ(n; S)` where the `i`ᵗʰ coordinate is invertible. -/
def chart (i : n) : ℙ(n; S).Opens :=
  Proj.basicOpen _ _

/-- The `i`ᵗʰ chart from `𝔸(n; S)` to `ℙ(n; S)`, formed by setting the `i`ᵗʰ coordinate to be `1`. -/
def affineToProjective (i : n) : 𝔸(n; S) ⟶ ℙ(n; S) :=
  pullback.map _ _ _ _ (𝟙 _) _ (𝟙 _) (by simp) _

-- set_option pp.universes true
/-- The canonical open cover of `ℙ(n; S)` formed by removing each coordinate `i : n`. -/
def openCover' : Scheme.OpenCover.{max u v} ℙ(n; S) :=
  Scheme.Pullback.openCoverOfRight (Proj.openCoverOfISupEqTop
      (homogeneousSubmodule n (ULift.{max u v} ℤ))
      (fun i : ULift n ↦ .X i.down) (fun _ ↦ isHomogeneous_X _ _) (fun _ ↦ zero_lt_one)
      (by rw [homogeneous_eq_span, Ideal.span_le, Set.range_subset_iff]; exact
        fun i ↦ Ideal.subset_span <| Set.mem_range_self _)).openCover _ _

variable {n} in
/-- Map `𝔸({j // j ≠ i}; S)` isomorphically to `S × Spec ℤ[n, 1/Xᵢ]`. -/
def remap (i : n) : 𝔸({j // j ≠ i}; S) ⟶ (openCover' n S).obj (ULift.up i) :=
  pullback.map _ _ _ _ (𝟙 _)
    (Spec.map <| CommRingCat.ofHom <| (algEquivAway (ULift.{max u v} ℤ) i).symm.toRingHom)
    (𝟙 _) (terminal.hom_ext ..) (terminal.hom_ext ..)

instance {R S : Type u} [CommRing R] [CommRing S] (f : R ≃+* S) : IsIso (CommRingCat.ofHom f.toRingHom) :=
  f.toCommRingCatIso.isIso_hom

instance {R S : Type u} [CommRing R] [CommRing S] (f : R ≃+* S) : IsIso (CommRingCat.ofHom (f : R →+* S)) :=
  f.toCommRingCatIso.isIso_hom

instance {C : Type*} [Category C] [HasTerminal C] (f : ⊤_ C ⟶ ⊤_ C) : IsIso f :=
  ⟨f, terminal.hom_ext .., terminal.hom_ext ..⟩

instance {C : Type*} [Category C] [HasInitial C] (f : ⊥_ C ⟶ ⊥_ C) : IsIso f :=
  ⟨f, initial.hom_ext .., initial.hom_ext ..⟩

instance (i : n) : IsIso (remap S i) :=
  pullback.map_isIso _ _ _ _ (𝟙 _) _ (𝟙 _) (terminal.hom_ext ..) (terminal.hom_ext ..)

def openCover : Scheme.OpenCover.{v} ℙ(n; S) where
  J := n
  obj i := 𝔸({j // j ≠ i}; S)
  map i := remap S i ≫ (openCover' n S).map (ULift.up.{u} i)
  f x := ((openCover' n S).f x).down
  covers x := let ⟨y, hy⟩ := (openCover' n S).covers x
    ⟨ConcreteCategory.hom (inv (remap S (((openCover' n S).f x).down))).base y,
    by rwa [← ConcreteCategory.comp_apply, Scheme.comp_base, ← Category.assoc, ← Scheme.comp_base,
      IsIso.inv_hom_id, Scheme.id.base, Category.id_comp]⟩

@[simp] lemma openCover_J : (openCover n S).J = n := rfl
@[simp] lemma openCover_obj (i : n) : (openCover n S).obj i = 𝔸({j // j ≠ i}; S) := rfl

@[simp] lemma openCover_map (i : n) : (openCover n S).map i =
    remap S i ≫ (openCover' n S).map (ULift.up.{u} i) :=
  rfl

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

/-- `ℙ(n; Spec R)` is isomorphic to `Proj R[n]`. -/
def SpecIso (R : Type max u v) [CommRing R] :
    ℙ(n; Spec (.of R)) ≅ Proj (homogeneousSubmodule n R) where
  hom := Scheme.Cover.glueMorphisms (openCover n _)
    (fun i ↦ (AffineSpace.SpecIso {j // j ≠ i} (.of R)).hom ≫
      Spec.map (CommRingCat.ofHom (by exact (algEquivAway R i).symm.toRingHom)) ≫
      Proj.awayι _ (.X i) (MvPolynomial.isHomogeneous_X R i) zero_lt_one)
    (fun i j ↦ by simp [-openCover_map])
  inv := Scheme.Cover.glueMorphisms
    (Proj.openCoverOfISupEqTop
      (homogeneousSubmodule n R) (.X) (fun _ ↦ isHomogeneous_X _ _) (fun _ ↦ zero_lt_one)
      (by rw [homogeneous_eq_span, Ideal.span_le, Set.range_subset_iff]; exact
        fun i ↦ Ideal.subset_span <| Set.mem_range_self _)).openCover
    (fun i : n ↦ _ ≫ (openCover n _).map i)
    _
  hom_inv_id := _
  inv_hom_id := _

#check Scheme.OpenCover
#check Scheme.Hom
#check Scheme.Cover.glueMorphisms
#check Scheme.Cover.ι_glueMorphisms
#check Scheme.Cover.hom_ext
#check AffineSpace.SpecIso
#check Proj.awayι

/- GOALS
* S affine
* Subspace cut out by a polynomial
* Locally (i.e. at stalk) points given by [x₀ : ... : xₙ]
-/

end ProjectiveSpace

end AlgebraicGeometry
