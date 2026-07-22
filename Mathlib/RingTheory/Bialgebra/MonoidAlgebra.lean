/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Yaël Dillies, Michał Mrugała
-/
module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.Bialgebra.Equiv
public import Mathlib.RingTheory.Bialgebra.GroupLike
public import Mathlib.RingTheory.Coalgebra.MonoidAlgebra

/-!
# The bialgebra structure on monoid algebras

Given a monoid `M`, a commutative semiring `R` and an `R`-bialgebra `A`, this file collects results
about the `R`-bialgebra instance on `A[M]` inherited from the corresponding structure on its
coefficients, building upon results in `Mathlib/RingTheory/Coalgebra/MonoidAlgebra.lean` about the
coalgebra structure.

## Main definitions

* `(Add)MonoidAlgebra.instBialgebra`: the `R`-bialgebra structure on `A[M]` when `M` is an (add)
  monoid and `A` is an `R`-bialgebra.
* `LaurentPolynomial.instBialgebra`: the `R`-bialgebra structure on the Laurent polynomials
  `A[T;T⁻¹]` when `A` is an `R`-bialgebra.
-/

public noncomputable section

open TensorProduct Bialgebra Coalgebra Function WithConv

variable {R S A B G H I M N O : Type*}

namespace MonoidAlgebra
section CommSemiring
variable [CommSemiring R] [CommSemiring S]

section Semiring
variable [Semiring A] [Semiring B] [Bialgebra R A] [Bialgebra R B]

@[to_additive (dont_translate := R A) (attr := simp) isGroupLikeElem_single_one]
lemma isGroupLikeElem_single_one (g : G) : IsGroupLikeElem R (single g 1 : A[G]) where
  counit_eq_one := by simp
  comul_eq_tmul_self := by simp [Algebra.TensorProduct.one_def]

/-- A group algebra is spanned by its group-like elements. -/
@[to_additive (dont_translate := R A) (attr := simp) span_isGroupLikeElem]
lemma span_isGroupLikeElem : Submodule.span A {a : A[G] | IsGroupLikeElem R a} = ⊤ :=
  eq_top_mono (Submodule.span_mono <| Set.range_subset_iff.2 isGroupLikeElem_single_one) <| by
    rw [← Finsupp.range_linearCombination]
    exact LinearMap.range_eq_top_of_surjective _ fun x ↦
      ⟨x.coeff, by simp [Finsupp.linearCombination_apply]⟩

variable [Monoid M] [Monoid N] [Monoid O]

variable (R A M) in
@[to_additive (dont_translate := R A)]
instance instBialgebra : Bialgebra R A[M] where
  counit_one := by simp only [one_def, counit_single, Bialgebra.counit_one]
  mul_compr₂_counit := by ext; simp
  comul_one := by
    simp only [one_def, comul_single, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
      TensorProduct.map_tmul, lsingle_apply]
  mul_compr₂_comul := by
    ext a b c d
    simp only [Function.comp_apply, LinearMap.coe_comp, LinearMap.compr₂_apply,
      LinearMap.mul_apply', single_mul_single, comul_single, Bialgebra.comul_mul,
      ← (Coalgebra.Repr.arbitrary R b).eq, ← (Coalgebra.Repr.arbitrary R d).eq, Finset.sum_mul_sum,
      Algebra.TensorProduct.tmul_mul_tmul, map_sum, TensorProduct.map_tmul, lsingle_apply,
      LinearMap.compl₁₂_apply, LinearMap.coe_sum, Finset.sum_apply,
      Finset.sum_comm (s := (Coalgebra.Repr.arbitrary R b).index)]

-- TODO: Generalise to `A[M] →ₐc[R] A[N]` under `Bialgebra R A`
variable (R) in
/-- If `f : M → N` is a monoid hom, then `MonoidAlgebra.mapDomain f` is a bialgebra hom between
their monoid algebras. -/
@[expose, to_additive (attr := simps!) (dont_translate := R)]
def mapDomainBialgHom (f : M →* N) : R[M] →ₐc[R] R[N] :=
  .ofAlgHom (mapDomainAlgHom R R f) (by ext; simp) (by ext; simp)

@[to_additive (attr := simp)]
lemma mapDomainBialgHom_id : mapDomainBialgHom R (.id M) = .id R R[M] := by ext; simp

@[to_additive (attr := simp)]
lemma mapDomainBialgHom_comp (f : N →* O) (g : M →* N) :
    mapDomainBialgHom R (f.comp g) = (mapDomainBialgHom R f).comp (mapDomainBialgHom R g) := by
  ext; simp [Finsupp.mapDomain_comp]

@[to_additive]
lemma mapDomainBialgHom_mapDomainBialgHom (f : N →* O) (g : M →* N) (x : R[M]) :
    mapDomainBialgHom R f (mapDomainBialgHom R g x) = mapDomainBialgHom R (f.comp g) x := by
  ext; simp

@[to_additive (attr := simp)]
lemma mapDomainBialgHom_single (f : M →* N) (m : M) (r : R) :
    mapDomainBialgHom R f (single m r) = single (f m) r := mapDomain_single

/-- A `R`-algebra homomorphism from `R[M]` is uniquely defined by its
values on the functions `single a 1`. -/
@[to_additive (dont_translate := A) (attr := ext high)
/-- A `R`-algebra homomorphism from `R[M]` is uniquely defined by its
values on the functions `single a 0`. -/]
lemma bialgHom_ext ⦃φ₁ φ₂ : A[M] →ₐc[R] B⦄
  (single_one_right : ∀ (m : M), φ₁ (single m 1) = φ₂ (single m 1))
  (single_one_left : (φ₁ : A[M] →ₐ[R] B).comp singleOneAlgHom =
    (φ₂ : A[M] →ₐ[R] B).comp singleOneAlgHom) : φ₁ = φ₂ :=
  BialgHom.coe_toAlgHom_injective <| algHom_ext single_one_right single_one_left

/-- See note [partially-applied ext lemmas]. -/
lemma bialgHom_ext' ⦃φ₁ φ₂ : A[M] →ₐc[R] B⦄
    (single_one_right : (φ₁ : A[M] →* B).comp (of A M) = (φ₂ : A[M] →* B).comp (of A M))
    (single_one_left : (φ₁ : A[M] →ₐ[R] B).comp singleOneAlgHom =
      (φ₂ : A[M] →ₐ[R] B).comp singleOneAlgHom) : φ₁ = φ₂ :=
  BialgHom.coe_toAlgHom_injective <| algHom_ext' single_one_right single_one_left

@[to_additive (attr := simp)]
lemma counit_domCongr (e : M ≃* N) (x : A[M]) : counit (R := R) (domCongr R A e x) = counit x := by
  induction x using MonoidAlgebra.induction_linear <;> simp [*]

variable (R A) in
/-- Isomorphic monoids have isomorphic monoid algebras. -/
@[expose, to_additive (attr := simps!) (dont_translate := R A)
/-- Isomorphic monoids have isomorphic monoid algebras. -/]
def domCongrBialgHom (e : M ≃* N) : A[M] ≃ₐc[R] A[N] :=
  .ofAlgEquiv (domCongr R A e) (by ext <;> simp) <| by
    ext a
    · simp
    · simp [← (Coalgebra.Repr.arbitrary R a).eq]

variable (M) in
/-- The trivial monoid algebra is isomorphic to the base ring. -/
@[expose, to_additive (dont_translate := R)]
def bialgEquivOfSubsingleton [Subsingleton M] : R[M] ≃ₐc[R] R where
  __ := counitBialgHom ..
  invFun := algebraMap _ _
  left_inv r := by
    change (Algebra.ofId _ _).comp (Bialgebra.counitAlgHom R _) r = AlgHom.id R _ r
    congr 1
    ext g : 2
    simp [Subsingleton.elim g 1]
  right_inv := (Bialgebra.counitAlgHom R R[M]).commutes

lemma isGroupLikeElem_of (m : M) : IsGroupLikeElem R (of A M m) := isGroupLikeElem_single_one ..

set_option linter.translate.warnInvalid false in
/-- The `R`-bialgebra map from the group algebra on the group-like elements of `A` to `A`. -/
@[expose, to_additive (dont_translate := R A) (attr := simps!)]
def liftGroupLikeBialgHom : R[GroupLike R A] →ₐc[R] A :=
  .ofAlgHom (lift R A (GroupLike R A) { toFun g := g.1, map_one' := by simp, map_mul' := by simp })
    (by ext; simp) (by ext; simp)

variable (R A M) in
/-- The bialgebra equivalence between `MonoidAlgebra` and `AddMonoidAlgebra` in terms of
`Additive`. -/
-- TODO: Make `BialgEquiv.toCoalgEquiv` the simp normal form so that this can be simp
@[expose, simps! -isSimp]
def toAdditiveBialgEquiv : A[M] ≃ₐc[R] AddMonoidAlgebra A (Additive M) :=
  .ofAlgEquiv (toAdditiveAlgEquiv R A M) (by ext <;> simp) <| by
    ext a
    · simp
    · simp [← (Coalgebra.Repr.arbitrary R a).eq]

@[simp]
lemma toAdditiveBialgEquiv_single (m : M) (a : A) :
    toAdditiveBialgEquiv R A M (single m a) = .single (.ofMul m) a := by
  simp [toAdditiveBialgEquiv]

end Semiring

section CommSemiring
variable [CommSemiring A]

section Algebra
variable [Algebra R A] [Monoid M]

variable (R M A) in
/-- `MonoidAlgebra.lift` as a `MulEquiv`. -/
def liftMulEquiv : (M →* A) ≃* WithConv (R[M] →ₐ[R] A) where
  toEquiv := (lift R A M).trans (WithConv.equiv _).symm
  map_mul' f g := by ext; simp [AlgHom.convMul_apply]

@[to_additive (dont_translate := R A) (attr := simp) convMul_algHom_single_one]
lemma convMul_algHom_single_one (f g : WithConv <| R[M] →ₐ[R] A) (x : M) :
    (f * g) (single x 1) = f (single x 1) * g (single x 1) := by simp [AlgHom.convMul_apply]

end Algebra

variable [Bialgebra R A]

@[to_additive (dont_translate := R A) (attr := simp) convMul_bialgHom_single_one]
lemma convMul_bialgHom_single [CommMonoid M] (f g : WithConv <| R[M] →ₐc[R] A) (x : M) :
    (f * g) (single x 1) = f (single x 1) * g (single x 1) := by
  simp only [BialgHom.convMul_def, BialgHom.coe_comp, Function.comp_apply]
  change mulBialgHom R A (Bialgebra.TensorProduct.map f.ofConv g.ofConv (comul (single x 1))) = _
  simp [Bialgebra.TensorProduct.map_tmul]

end CommSemiring

section CommMonoid
variable [CommMonoid M] [CommMonoid N]

@[to_additive (dont_translate := R) (attr := simp)]
lemma mapDomainBialgHom_mul (f g : M →* N) :
    mapDomainBialgHom R (f * g) =
      ofConv ((toConv <| mapDomainBialgHom R f) * (toConv <| mapDomainBialgHom R g)) := by ext; simp

lemma comulAlgHom_comp_mapRingHom (f : R →+* S) :
    (comulAlgHom S (MonoidAlgebra S M)).toRingHom.comp (mapRingHom M f) =
      .comp (Algebra.TensorProduct.mapRingHom f (mapRingHom M f) (mapRingHom M f) (by simp)
        (by simp)) (comulAlgHom R R[M]).toRingHom := by ext <;> simp

lemma counitAlgHom_comp_mapRingHom (f : R →+* S) :
    (counitAlgHom S (MonoidAlgebra S M)).toRingHom.comp (mapRingHom M f) =
      f.comp (counitAlgHom R R[M]).toRingHom := by ext <;> simp

end CommMonoid
end CommSemiring

section CommRing
variable [CommRing R] [IsDomain R]

open Submodule in
@[to_additive (dont_translate := R) (attr := simp) isGroupLikeElem_iff_mem_range_single_one]
lemma isGroupLikeElem_iff_mem_range_single_one {x : R[M]} :
    IsGroupLikeElem R x ↔ x ∈ Set.range (single · 1) where
  mp hx := by
    by_contra h
    have : LinearIndepOn R id (insert x <| .range (single · 1)) :=
      linearIndepOn_isGroupLikeElem.mono <| by simp [Set.subset_def, hx]
    have : x.coeff.sum single ∉ span R (.range (single · 1)) := by
      simpa using this.notMem_span_of_insert h
    refine this <| sum_mem fun g hg ↦ ?_
    rw [← mul_one (x.coeff g), ← smul_eq_mul, ← smul_single]
    exact smul_mem _ _ <| subset_span <| Set.mem_range_self _
  mpr := by rintro ⟨g, rfl⟩; exact isGroupLikeElem_single_one _

open Submodule in
@[to_additive (dont_translate := R) (attr := simp)]
lemma isGroupLikeElem_iff_mem_range_of {x : R[M]} :
    IsGroupLikeElem R x ↔ x ∈ Set.range (single · 1) := isGroupLikeElem_iff_mem_range_single_one

section Group
variable [Group G] [Group H] [Group I]

@[to_additive (dont_translate := R)]
private def mapDomainOfBialgHomFun (f : R[G] →ₐc[R] R[H]) : G → H :=
  fun g ↦ (isGroupLikeElem_iff_mem_range_of.1 <| (isGroupLikeElem_single_one g).map f).choose

@[to_additive (dont_translate := R) (attr := simp)]
private lemma single_mapDomainOfBialgHomFun_one (f : R[G] →ₐc[R] R[H]) (g : G) :
    single (mapDomainOfBialgHomFun f g) 1 = f (single g 1) :=
  (isGroupLikeElem_iff_mem_range_of.1 <| (isGroupLikeElem_single_one g).map f).choose_spec

open Coalgebra in
/-- A bialgebra homomorphism `R[G] → R[H]` between group algebras over a domain `R` comes from a
group hom `G → H`.

See `MonoidAlgebra.mapDomainBialgHom` for the forward map. -/
@[to_additive (dont_translate := R)
/-- A bialgebra homomorphism `R[G] → R[H]` between group algebras over a domain `R` comes from a
group hom `G → H`.

See `MonoidAlgebra.mapDomainBialgHom` for the forward map. -/]
def mapDomainOfBialgHom (f : R[G] →ₐc[R] R[H]) : G →* H where
  toFun := mapDomainOfBialgHomFun f
  map_one' := single_left_injective (R := R) one_ne_zero <| by simp [← one_def]
  map_mul' g₁ g₂ := by
    refine single_left_injective (R := R) one_ne_zero ?_
    simp only [single_mapDomainOfBialgHomFun_one]
    rw [← mul_one (1 : R), ← single_mul_single, ← single_mul_single, map_mul]
    simp

@[to_additive (dont_translate := R)]
lemma single_mapDomainOfBialgHom (f : R[G] →ₐc[R] R[H]) (g : G) (r : R) :
     single (mapDomainOfBialgHom f g) r = f (single g r) := by
  rw [← mul_one r, ← smul_eq_mul, ← smul_single, ← smul_single, map_smul]
  exact congr(r • $(single_mapDomainOfBialgHomFun_one f g))

@[to_additive (dont_translate := R) (attr := simp)]
lemma mapDomainBialgHom_mapDomainOfBialgHom (f : R[G] →ₐc[R] R[H]) :
    mapDomainBialgHom R (mapDomainOfBialgHom f) = f := by
  ext x : 1
  · rw [mapDomainBialgHom_single]
    exact single_mapDomainOfBialgHomFun_one f x
  · ext

@[to_additive (dont_translate := R) (attr := simp)]
lemma mapDomainOfBialgHom_mapDomainBialgHom (f : G →* H) :
    mapDomainOfBialgHom (mapDomainBialgHom (R := R) f) = f := by
  ext g; refine single_left_injective (R := R) one_ne_zero ?_; simp [single_mapDomainOfBialgHom]

@[to_additive (attr := simp)]
lemma mapDomainOfBialgHom_id : mapDomainOfBialgHom (.id R R[G]) = .id _ := by
  simp [← mapDomainBialgHom_id]

@[to_additive (attr := simp)]
lemma mapDomainOfBialgHom_comp (f : R[H] →ₐc[R] R[I]) (g : R[G] →ₐc[R] R[H]) :
    mapDomainOfBialgHom (f.comp g) = (mapDomainOfBialgHom f).comp (mapDomainOfBialgHom g) := by
  rw [← mapDomainOfBialgHom_mapDomainBialgHom (R := R)
    ((mapDomainOfBialgHom f).comp (mapDomainOfBialgHom g)),
    mapDomainBialgHom_comp, mapDomainBialgHom_mapDomainOfBialgHom,
    mapDomainBialgHom_mapDomainOfBialgHom]

/-- The equivalence between group homs `G → H` and bialgebra homs `R[G] → R[H]` of group algebras
over a domain. -/
@[expose, to_additive (attr := simps)
/-- The equivalence between group homs `G → H` and bialgebra homs `R[G] → R[H]` of group algebras
over a domain. -/]
def mapDomainBialgHomEquiv : (G →* H) ≃ (R[G] →ₐc[R] R[H]) where
  toFun := mapDomainBialgHom R
  invFun := mapDomainOfBialgHom
  left_inv := mapDomainOfBialgHom_mapDomainBialgHom
  right_inv := mapDomainBialgHom_mapDomainOfBialgHom

end Group

section CommGroup
variable [CommGroup G] [CommGroup H]

/-- The group isomorphism between group homs `G → H` and bialgebra homs `R[G] → R[H]` of group
algebras over a domain. -/
def mapDomainBialgHomMulEquiv : (G →* H) ≃* WithConv (R[G] →ₐc[R] R[H]) where
  toEquiv := mapDomainBialgHomEquiv.trans (WithConv.equiv _).symm
  map_mul' f g := by simp

end CommGroup
end CommRing
end MonoidAlgebra

namespace AddMonoidAlgebra
section CommSemiring
variable [CommSemiring R] [CommSemiring S]

section Semiring
variable [Semiring A] [Semiring B] [Bialgebra R A] [Bialgebra R B] [AddMonoid M] [AddMonoid N]

/-- See note [partially-applied ext lemmas]. -/
lemma bialgHom_ext' ⦃φ₁ φ₂ : A[M] →ₐc[R] B⦄
    (single_one_right : (φ₁ : A[M] →* B).comp (of A M) = (φ₂ : A[M] →* B).comp (of A M))
    (single_one_left : (φ₁ : A[M] →ₐ[R] B).comp singleZeroAlgHom =
      (φ₂ : A[M] →ₐ[R] B).comp singleZeroAlgHom) : φ₁ = φ₂ :=
  BialgHom.coe_toAlgHom_injective <| algHom_ext' single_one_right single_one_left

lemma isGroupLikeElem_of (m : M) : IsGroupLikeElem R (of A M m) := isGroupLikeElem_single_one ..

variable (R A M) in
/-- The bialgebra equivalence between `AddMonoidAlgebra` and `MonoidAlgebra` in terms of
`Multiplicative`. -/
-- TODO: Make `BialgEquiv.toCoalgEquiv` the simp normal form so that this can be simp
@[expose, simps! -isSimp]
def toMultiplicativeBialgEquiv : A[M] ≃ₐc[R] MonoidAlgebra A (Multiplicative M) :=
  .ofAlgEquiv (toMultiplicativeAlgEquiv R A M) (by ext <;> simp) <| by
    ext a
    · simp
    · simp [← (Coalgebra.Repr.arbitrary R a).eq]

@[simp]
lemma toMultiplicativeBialgEquiv_single (m : M) (a : A) :
    toMultiplicativeBialgEquiv R A M (single m a) = .single (.ofAdd m) a := by
  simp [toMultiplicativeBialgEquiv]

end Semiring

section CommSemiring
variable [CommSemiring A]

section Algebra
variable [Algebra R A] [AddMonoid M]

variable (R M A) in
/-- `AddMonoidAlgebra.lift` as a `MulEquiv`. -/
def liftMulEquiv : (Multiplicative M →* A) ≃* WithConv (R[M] →ₐ[R] A) where
  toEquiv := (lift R A M).trans (WithConv.equiv _).symm
  map_mul' f g := by ext; simp [AlgHom.convMul_apply]

end Algebra

@[simp]
lemma convMul_bialgHom_single [Bialgebra R A] [AddCommMonoid M] (f g : WithConv <| R[M] →ₐc[R] A)
    (m : M) : (f * g) (single m 1) = f (single m 1) * g (single m 1) := by
  simp only [BialgHom.convMul_def, BialgHom.coe_comp, Function.comp_apply]
  change mulBialgHom R A (Bialgebra.TensorProduct.map f.ofConv g.ofConv (comul (single m 1))) = _
  simp [Bialgebra.TensorProduct.map_tmul]

end CommSemiring

section AddCommMonoid
variable [AddCommMonoid M] [AddCommMonoid N]

lemma comulAlgHom_comp_mapRingHom (f : R →+* S) :
    (comulAlgHom S S[M]).toRingHom.comp (mapRingHom M f) =
      .comp (Algebra.TensorProduct.mapRingHom f (mapRingHom M f) (mapRingHom M f)
        (by ext; simp) (by ext; simp))
        (comulAlgHom R R[M]).toRingHom := by ext <;> simp

lemma counitAlgHom_comp_mapRingHom (f : R →+* S) :
    (counitAlgHom S S[M]).toRingHom.comp (mapRingHom M f) =
      f.comp (counitAlgHom R R[M]).toRingHom := by ext <;> simp

end AddCommMonoid
end CommSemiring

section CommRing
variable [CommRing R] [IsDomain R]

section AddGroup
variable [AddGroup G] [AddGroup H] [AddGroup I]

open Submodule in
@[simp]
lemma isGroupLikeElem_iff_mem_range_of {x : R[G]} : IsGroupLikeElem R x ↔ x ∈ Set.range (of R G) :=
  isGroupLikeElem_iff_mem_range_single_one

end AddGroup

section AddCommGroup
variable [AddCommGroup G] [AddCommGroup H]

/-- The group isomorphism between group homs `G → H` and bialgebra homs `R[G] → R[H]` of group
algebras over a domain. -/
def mapDomainBialgHomAddEquiv : (G →+ H) ≃+ Additive (WithConv <| R[G] →ₐc[R] R[H]) where
  toEquiv := mapDomainBialgHomEquiv.trans <| (WithConv.equiv _).symm.trans Additive.ofMul
  map_add' f g := by simp

end AddCommGroup
end CommRing
end AddMonoidAlgebra

namespace LaurentPolynomial

open AddMonoidAlgebra

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Bialgebra R A]

instance instBialgebra : Bialgebra R A[T;T⁻¹] :=
  inferInstanceAs <| Bialgebra R A[ℤ]

@[simp]
theorem comul_T (n : ℤ) : comul (T n : A[T;T⁻¹]) = T n ⊗ₜ[R] T n := by simp [T, -single_eq_C_mul_T]

@[simp]
theorem counit_T (n : ℤ) :
    Coalgebra.counit (R := R) (T n : A[T;T⁻¹]) = 1 := by
  simp [T, -single_eq_C_mul_T]

end LaurentPolynomial
