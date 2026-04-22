/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Algebra.Lie.Extension
public import Mathlib.Algebra.Lie.InvariantForm
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Data.Set.MulAntidiagonal

/-!
# Loop Lie algebras and their central extensions

Given a Lie algebra `L`, the loop algebra is the Lie algebra of maps from a circle into `L`. This
can mean many different things, e.g., continuous maps, smooth maps, polynomial maps. In this file,
we consider the simplest case of polynomial maps, meaning we take a base change with the ring of
Laurent polynomials.

Representations of loop algebras are not particularly interesting - a theorem of Rao (1993) asserts
that when `L` is complex semisimple, any irreducible representation of `L[z,z^{-1}]` is just given
by evaluation of loops at a finite set of specific points. However, the theory becomes much richer
when one considers projective representations, i.e., representations of a central extension. Common
examples include generalized Verma modules, given by pulling a representation of `L` back to a
representation of `L[z] ⊕ C` along the homomorphism `z ↦ 0` together with a central character, and
inducing to the central extension of the loop algebra.

We implement the basic theory using `AddMonoidAlgebra` instead of `LaurentPolynomial` for
flexibility. The classical loop algebra is then written `loopAlgebra R ℤ L`.

## Main definitions
* `LieAlgebra.loopAlgebra`: The tensor product of a Lie algebra with an `AddMonoidAlgebra`.
* `LieAlgebra.loopAlgebra.toFinsupp`: A linear equivalence from the loop algebra to the space of
  finitely supported functions.
* `LieAlgebra.loopAlgebra.twoCochainOfBilinear`: The 2-cochain for a loop algebra with trivial
  coefficients attached to a symmetric bilinear form on the base Lie algebra.
* `LieAlgebra.loopAlgebra.twoCocycleOfBilinear`: The 2-cocycle for a loop algebra with trivial
  coefficients attached to a symmetric invariant bilinear form on the base Lie algebra.

## TODO
* Evaluation representations
* Construction of central extensions from invariant forms.
* Positive energy representations induced from a fixed central character

## Tags

lie ring, lie algebra, base change, Laurent polynomial, central extension
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

variable (R A L M : Type*)

namespace LieAlgebra

variable [CommRing R] [LieRing L] [LieAlgebra R L]
 -- [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- A loop algebra is the base change of a Lie algebra `L` over `R` by `R[z,z^{-1}]`. -/
abbrev loopAlgebra := AddMonoidAlgebra R A ⊗[R] L

open LaurentPolynomial in
/-- An Lie algebra isomorphism between the Loop algebra (with `A = ℤ`) and the tensor product with
Laurent polynomials. -/
def loopAlgebraEquivLaurent :
    loopAlgebra R ℤ L ≃ₗ⁅R⁆ R[T;T⁻¹] ⊗[R] L :=
  LieEquiv.refl

namespace LoopAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- The Lie algebra homomorphism induced by an additive map of character groups. -/
def mapMonomialLieHom {A} {A' : Type*} [AddCommMonoid A] [AddCommMonoid A'] (f : A →+ A') :
    loopAlgebra R A L →ₗ⁅R⁆ loopAlgebra R A' L :=
  LieAlgebra.ExtendScalars.map (AddMonoidAlgebra.mapDomainAlgHom R R f) LieHom.id

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma mapMonomialLieHom_single {A} {A' : Type*} [AddCommMonoid A] [AddCommMonoid A'] (f : A →+ A')
    (r : R) (a : A) (x : L) :
    mapMonomialLieHom R L f (AddMonoidAlgebra.single a r ⊗ₜ x) =
      (AddMonoidAlgebra.single (f a) r ⊗ₜ x) := by
  simp [mapMonomialLieHom]

/-- The linear map taking `x` to `T ^ n ⊗ x`. -/
def monomial {A} (a : A) : L →ₗ[R] loopAlgebra R A L :=
  TensorProduct.mk R (AddMonoidAlgebra R A) L (AddMonoidAlgebra.single a (1 : R))

@[simp]
lemma addEquiv_monomial (a : A) (x : L) :
    monomial R L a x = (AddMonoidAlgebra.single a (1 : R) ⊗ₜ x) :=
  rfl

lemma monomial_smul (r : R) (a : A) (x : L) : monomial R L a (r • x) = r • (monomial R L a x) :=
  LinearMap.map_smul (monomial R L a) r x

open Classical in
/-- A linear isomorphism to finitely supported functions. -/
def toFinsupp : loopAlgebra R A L ≃ₗ[R] A →₀ L :=
  TensorProduct.equivFinsuppOfBasisLeft (AddMonoidAlgebra.basis A R)

@[simp]
lemma toFinsupp_symm_single (a : A) :
    (toFinsupp R A L).symm ∘ (Finsupp.single a) = monomial R L a := by
  ext x
  simp [toFinsupp]

@[simp]
lemma toFinsupp_comp_monomial (a : A) : toFinsupp R A L ∘ (monomial R L a) = Finsupp.single a := by
  refine Eq.symm ?_
  refine (LinearEquiv.symm_comp_eq (R₁ := R) (R₂ := R) (monomial R L a) (Finsupp.single a)).mp ?_
  simp

lemma toFinsupp_monomial_apply (a : A) (x : L) :
    toFinsupp R A L (monomial R L a x) = Finsupp.single a x:= by
  rw [← Function.comp_apply (f := toFinsupp R A L), ← toFinsupp_comp_monomial R]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma toFinsupp_single_tmul (c : A) (z : L) (r : R) :
    ((toFinsupp R A L) (AddMonoidAlgebra.single c r ⊗ₜ[R] z)) = Finsupp.single c (r • z) := by
  ext a
  by_cases h : c = a <;> simp [toFinsupp, h, AddMonoidAlgebra.basis, AddMonoidAlgebra.single,
    LinearEquiv.refl, LinearMap.id]

set_option backward.isDefEq.respectTransparency false in
lemma support_toFinsupp_mapMonomialLieHom {B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (f : B →+ A) (p : loopAlgebra R B L) {a : A}
    (ha : a ∈ ((toFinsupp R A L) ((mapMonomialLieHom R L f) p)).support) :
    a ∈ Set.range f := by
  rw [Finsupp.mem_support_iff] at ha
  induction p using TensorProduct.induction_on with
  | zero => simp at ha
  | tmul x y =>
    induction x using AddMonoidAlgebra.induction_linear with
    | zero => simp at ha
    | add x z h1 h2 =>
      rw [TensorProduct.add_tmul, map_add, map_add, Finsupp.add_apply] at ha
      obtain (h|h) := ne_zero_or_ne_zero_of_add ha
      · exact h1 h
      · exact h2 h
    | single m r =>
      rw [mapMonomialLieHom_single, toFinsupp_single_tmul, Finsupp.single_apply_ne_zero] at ha
      use m
      exact ha.1.symm
  | add x y h1 h2 =>
    rw [map_add, map_add, Finsupp.add_apply] at ha
    obtain (h|h) := ne_zero_or_ne_zero_of_add ha
    · exact h1 h
    · exact h2 h

lemma monomial_injective (a : A) : Function.Injective (monomial R L a) := by
  rw [← toFinsupp_symm_single]
  exact (EmbeddingLike.comp_injective _ (toFinsupp R A L).symm).mpr (Finsupp.single_injective a)

open Pointwise in
lemma finite_support_add {α A : Type*} [AddZeroClass A] {f g : α → A} (hf : Finite f.support)
    (hg : Finite g.support) :
    Finite (f + g).support := by
  refine Finite.Set.subset (f.support ∪ g.support) ?_
  intro n hn
  contrapose! hn
  simp only [Set.mem_union, Function.mem_support, ne_eq, not_or, not_not] at hn
  simp [hn.1, hn.2]

lemma add_finsupp {α A : Type*} [AddMonoid A] {f g : α → A} (hf : Finite f.support)
    (hg : Finite g.support) :
    Finsupp.ofSupportFinite f hf + Finsupp.ofSupportFinite g hg =
      Finsupp.ofSupportFinite (f + g) (finite_support_add hf hg) := by
  ext; simp [Finsupp.add_apply, Finsupp.ofSupportFinite_coe]
--#find_home! add_finsupp --[Mathlib.Algebra.Group.Finsupp]

lemma finite_support_bracket [AddCancelCommMonoid A] (a : A) (x y : A →₀ L) :
    Finite (fun (k : Set.addAntidiagonal Set.univ Set.univ a) ↦ ⁅x k.1.1, y k.1.2⁆).support := by
  refine Set.Finite.of_finite_image (f := fun k ↦ k.1.1) ?_ ?_
  · refine Set.Finite.subset (Finite.of_fintype x.support) ?_
    simp only [Set.image_subset_iff, Function.support_subset_iff, ne_eq, Set.mem_preimage,
      SetLike.mem_coe, Finsupp.mem_support_iff, Subtype.forall, Set.mem_addAntidiagonal,
      Set.mem_univ, true_and, Prod.forall]
    intro k l _ h
    contrapose! h
    simp [h]
  · exact fun _ _ _ _ h ↦ Set.AddAntidiagonal.eq_of_fst_eq_fst h

/-- This needs to be generalized: replace Lie bracket with any bilinear map. -/
lemma finite_support_finsum_bracket [AddCommMonoid A] (x y : A →₀ L) :
    Finite (fun (a : A) ↦
      ∑ᶠ (k : Set.addAntidiagonal Set.univ Set.univ a), ⁅x k.1.1, y k.1.2⁆).support := by
  refine Set.Finite.subset (s := Set.range (fun (k : x.support × y.support) ↦ k.1.1 + k.2.1)) ?_ ?_
  · exact Set.finite_range fun (k : x.support × y.support) ↦ k.1.1 + k.2.1
  · intro n hn
    rw [Function.mem_support, ← finsum_mem_univ] at hn
    obtain ⟨k, _, hk⟩ := exists_ne_zero_of_finsum_mem_ne_zero hn
    simp only [Set.mem_range, Prod.exists, Subtype.exists, Finsupp.mem_support_iff, exists_prop]
    contrapose! hk
    obtain ⟨k', _, _, h⟩ := k
    simp only
    by_cases hx : x k'.1 = 0
    · simp [hx]
    · have hy : y k'.2 = 0 := by
        by_contra
        exact hk k'.1 hx k'.2 this h
      simp [hy]

/-theorem finite_finsum_on_fiber {α β M : Type*} [AddCommMonoid M] (f : α → β) (g : α → M)
    (hg : (Function.support g).Finite) :
    (Function.support fun b ↦ ∑ᶠ (a : α) (_ : f a = b), g a).Finite := by
  have := Set.finite_coe_iff.mpr hg
  refine Set.Finite.subset (Finite.Set.finite_image (Function.support g) f) ?_
  intro b hb
  obtain ⟨a, hab, ha⟩ := exists_ne_zero_of_finsum_mem_ne_zero hb
  use a
  exact ⟨ha, hab⟩


theorem support_finsum_subset_image_support {α β M : Type*} [AddCommMonoid M] (f : α → β)
    (g : α → M) (hg : (Function.support g).Finite) :
    (Function.support fun b ↦ ∑ᶠ (a : α) (_ : f a = b), g a) ⊆
      (Set.Finite.image f hg).toFinset := by
  intro b hb
  obtain ⟨a, h, ha⟩ := exists_ne_zero_of_finsum_mem_ne_zero hb
  exact Finset.mem_coe.mpr <| (Set.Finite.mem_toFinset (Set.Finite.image f hg)).mpr <|
    (Set.mem_image f (Function.support g) b).mpr <| Exists.intro a ⟨ha, h⟩

theorem finsum_fiberwise {α β M : Type*} [AddCommMonoid M] (f : α → β) (g : α → M)
    (hg : (Function.support g).Finite) :
    ∑ᶠ (b : β) (a : α) (_ : f a = b), g a = ∑ᶠ (a : α), g a := by
  rw [finsum_eq_sum g hg]
  rw [finsum_eq_sum_of_support_subset (s := (Set.Finite.image f hg).toFinset)]
  swap; · exact support_finsum_subset_image_support f g hg
  have (i : β) : (Function.support fun a ↦ ∑ᶠ (_ : f a = i), g a).Finite := by
    refine (Set.Finite.subset hg fun a ha ha0 ↦ ?_)
    rw [Function.mem_support, ha0, finsum_zero] at ha
    exact ha rfl
  classical
  simp_rw [finsum_eq_sum _ (this _), finsum_eq_if]
  rw [Finset.sum_sigma']
  refine Eq.symm (Finset.sum_of_injOn (fun x ↦ ⟨f x, x⟩) (fun _ _ _ _ _ ↦ by simp_all) ?_ ?_
    (fun _ _ ↦ by simp))
  · intro a h
    simp only [Finset.coe_sigma, Set.Finite.coe_toFinset, Set.mem_sigma_iff, Set.mem_image,
      Function.mem_support, ↓reduceIte]
    have : g a ≠ 0 := by simpa using h
    exact ⟨Exists.intro a ⟨this, rfl⟩, this⟩
  · intro ⟨_, a⟩ _ h
    simp only [Set.Finite.coe_toFinset, Set.mem_image, Function.mem_support, not_exists] at h
    simp only [ite_eq_right_iff]
    contrapose
    simpa using h a
--#find_home! finsum_fiberwise --[Mathlib.Algebra.BigOperators.Finprod]

lemma finsum_fiberwise_quotient {α M : Type*} [AddCommMonoid M] (r : Setoid α) (f : α → M)
    (hf : (Function.support f).Finite) :
    ∑ᶠ (y : Quotient r) (x : (Quotient.mk r) ⁻¹' {y}), f x = ∑ᶠ x : α, f x := by
  rw [← finsum_fiberwise (Quotient.mk r) _ hf, finsum_congr]
  exact fun y ↦ finsum_set_coe_eq_finsum_mem (Quotient.mk r ⁻¹' {y})
--#find_home! finsum_fiberwise' --[Mathlib.Algebra.BigOperators.Finprod]

/-- A LieRing structure on finsupp -/
def finsuppLieRing' : LieRing (ℤ →₀ L) where
  bracket x y := Finsupp.ofSupportFinite
    (fun n ↦ ∑ᶠ (k : Set.addAntidiagonal Set.univ Set.univ n), ⁅x k.1.1, y k.1.2⁆)
    (finite_support_finsum_bracket L x y)
  add_lie x y z := by
    ext n
    simp only [Finsupp.ofSupportFinite, Finsupp.coe_add, Pi.add_apply, add_lie, Finsupp.coe_mk]
    rw [← finsum_add_distrib (finite_support_bracket L n x z) (finite_support_bracket L n y z)]
  lie_add x y z := by
    ext n
    simp only [Finsupp.ofSupportFinite, Finsupp.coe_add, Pi.add_apply, lie_add, Finsupp.coe_mk]
    rw [← finsum_add_distrib (finite_support_bracket L n x y) (finite_support_bracket L n x z)]
  lie_self x := by
    ext n
    simp only [Finsupp.ofSupportFinite, Finsupp.coe_mk, Finsupp.coe_zero, Pi.zero_apply]
    rw [← finsum_fiberwise_quotient  _ (finite_support_bracket L n x x),
      finsum_eq_zero_of_forall_eq_zero]
    intro y
    by_cases h :
    sorry
  leibniz_lie x y z := by
    ext
    simp [Finsupp.ofSupportFinite]
    sorry

/-- A Lie ring structure on finitely supported functions on a Lie algebra `L`. -/
def finsuppLieRing [AddCommMonoid A] : LieRing (A →₀ L) where
  bracket x y := toFinsupp R A L ⁅(toFinsupp R A L).symm x, (toFinsupp R A L).symm y⁆
  add_lie := by simp
  lie_add := by simp
  lie_self := by simp
  leibniz_lie := by simp

@[simp]
lemma finsuppLieRing_bracket_apply [AddCommMonoid A] (x y : A →₀ L) :
    letI := finsuppLieRing R A L
    ⁅x, y⁆ = toFinsupp R A L ⁅(toFinsupp R A L).symm x, (toFinsupp R A L).symm y⁆ :=
  rfl

lemma bracketHom [AddCommMonoid A] (x y : loopAlgebra R A L) :
    letI := finsuppLieRing R A L
    ⁅toFinsupp R A L x, toFinsupp R A L y⁆ = toFinsupp R A L ⁅x, y⁆ := by
  simp

/-- The scalar multiplication of Laurent polynomials on finsupps. -/
@[simps]
def laurentSMul [AddCommMonoid A] : SMul (AddMonoidAlgebra R A) (A →₀ L) where
  smul r x := toFinsupp R A L (r • ((toFinsupp R A L).symm x))

/-- The `R[T,T⁻¹]`-Lie algebra structure on finsupp. -/
def finsuppLieAlgebra [AddCommMonoid A] :
    letI := finsuppLieRing R A L
    LieAlgebra (AddMonoidAlgebra R A) (A →₀ L) :=
  letI := finsuppLieRing R A L
  { smul r x := (laurentSMul R A L).smul r x
    one_smul a := by ext; simp
    mul_smul r s x := by ext; simp [← mul_smul]
    smul_zero := by simp
    smul_add := by simp
    add_smul r s x := by ext; simp [add_smul]
    zero_smul := by simp
    lie_smul r x y := by
      ext n
      simp [laurentSMul_smul] }

/-- The `R`-Lie algebra structure on finsupp. -/
def finsuppRestrictLieAlgebra [AddCommMonoid A] :
    letI := finsuppLieRing R A L
    LieAlgebra R (A →₀ L) :=
  letI := finsuppLieRing R A L
  letI := finsuppLieAlgebra R A L
  LieAlgebra.RestrictScalars.lieAlgebra R (AddMonoidAlgebra R A) (A →₀ L)

/-- The evaluation representation, given by composing a representation with the evaluation map
`L[z,z^{-1}] → L` attached to a unit in `R`. -/
--define eval (x : Units R) : (loopAlgebra R L) →ₗ⁅R⁆ L where
  toFun l := sorry
  map_add' := sorry
  map_smul' := sorry
  map_lie' := sorry

/-- The evaluation module -/
-- define eval.LieModule
-/

section CentralExt

open Finsupp in
/-- The residue pairing on the loop algebra.  When `A = ℤ` and the elements are viewed as Laurent
polynomials with coefficients in `L`, the pairing is interpreted as `(f, g) ↦ Res f dg`. -/
@[simps]
def residuePairing [AddCommGroup A] [DistribSMul A R] [SMulCommClass A R R]
    (Φ : LinearMap.BilinForm R L) :
    LinearMap.BilinForm R (loopAlgebra R A L) where
  toFun f :=
    letI F := toFinsupp R A L
    { toFun g := (F g).sum fun a v ↦ a • Φ (F f (-a)) v
      map_add' x y := by
        classical
        let u : Finset A := (F x).support ∪ (F y).support
        have hu₁ : (F x).support ⊆ u := Finset.subset_union_left
        have hu₂ : (F y).support ⊆ u := Finset.subset_union_right
        have hu₃ : (F (x + y)).support ⊆ u := fun a ha ↦ by
          replace ha : F x a + F y a ≠ 0 := by simpa using ha
          grind
        rw [sum_of_support_subset _ hu₃ _ (by simp), sum_of_support_subset _ hu₁ _ (by simp),
          sum_of_support_subset _ hu₂ _ (by simp)]
        simp [Finset.sum_add_distrib, u]
      map_smul' r x := by
        rw [map_smul, sum_of_support_subset _ support_smul _ (by simp), sum, Finset.smul_sum]
        simp [-smul_eq_mul, smul_comm] }
  map_add' x y := by ext; simp [sum_add]
  map_smul' r x := by ext; simp [-smul_eq_mul, smul_comm]

open LieModule in
/-- A 2-cochain on a loop algebra given by an invariant bilinear form. When `A = ℤ`, the alternating
condition amounts to the fact that Res f df = 0. -/
def twoCochainOfBilinear [CommRing A] [IsAddTorsionFree R] [Algebra A R]
    (Φ : LinearMap.BilinForm R L) (hΦ : Φ.IsSymm) :
    Cohomology.twoCochain R (loopAlgebra R A L) (TrivialLieModule R (loopAlgebra R A L) R) where
  val := (residuePairing R A L Φ).compr₂ (TrivialLieModule.equiv R (loopAlgebra R A L) R).symm
  property := by
    refine Cohomology.mem_twoCochain_iff.mpr fun f ↦ ?_
    letI F := toFinsupp R A L
    suffices ((F f).sum fun a v ↦ a • Φ (F f (-a)) v) = 0 by simpa
    classical
    set s := (F f).support ∪ (F f).support.image (Equiv.neg A) with hs
    have hs' : (F f).support ⊆ s := Finset.subset_union_left
    rw [Finsupp.sum_of_support_subset _ hs' _ (by simp)]
    refine Function.Odd.finset_sum_eq_zero (fun n ↦ by simp [hΦ.eq]) (Finset.map_eq_of_subset ?_)
    intro x hx
    rw [Finset.mem_union]
    replace hx : -x ∈ (F f).support ∨ -x ∈ (F f).support.image Neg.neg := by simpa [hs] using hx
    obtain (h | h) := hx
    · exact Or.inr <| Finset.mem_image.mpr ⟨-x, by simp [h]⟩
    · exact Or.inl <| by simpa using h

@[simp]
lemma twoCochainOfBilinear_apply_apply [CommRing A] [IsAddTorsionFree R] [Algebra A R]
    (Φ : LinearMap.BilinForm R L) (hΦ : Φ.IsSymm) (x y : loopAlgebra R A L) :
    twoCochainOfBilinear R A L Φ hΦ x y =
      (TrivialLieModule.equiv R (loopAlgebra R A L) R).symm (residuePairing R A L Φ x y) :=
  rfl

open LieModule in
/-- A 2-cocycle on a loop algebra given by an invariant bilinear form. -/
@[simps]
def twoCocycleOfBilinear [CommRing A] [IsAddTorsionFree R] [Algebra A R]
    (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) :
    Cohomology.twoCocycle R (loopAlgebra R A L) (TrivialLieModule R (loopAlgebra R A L) R) where
  val := twoCochainOfBilinear R A L Φ hΦs
  property := by
    apply (LieModule.Cohomology.mem_twoCocycle_iff ..).mpr
    ext a x b y c z
    suffices
        b • Φ (Finsupp.single (a + c) ⁅x, z⁆ (-b)) y =
        c • Φ (Finsupp.single (a + b) ⁅x, y⁆ (-c)) z +
        a • Φ (Finsupp.single (b + c) ⁅y, z⁆ (-a)) x by
      simpa [sub_eq_zero, neg_add_eq_iff_eq_add, ← LinearEquiv.map_add, -LinearEquiv.map_add]
    by_cases h0 : a + b + c = 0
    · suffices b • Φ ⁅x, z⁆ y = c • Φ ⁅x, y⁆ z + a • Φ ⁅y, z⁆ x by
        simpa only [show a + b = -c by grind, show a + c = -b by grind, show b + c = -a by grind,
          Finsupp.single_eq_same]
      rw [hΦ, hΦs.eq z ⁅x, y⁆, hΦ y, ← lie_skew y x, hΦs.eq z, Φ.neg_left, neg_neg,
        show b = -(a + c) by grind, neg_smul, smul_neg, neg_neg, add_smul, add_comm]
    · simp [Finsupp.single_eq_of_ne (a := a + c) (a' := -b) (by grind),
        Finsupp.single_eq_of_ne (a := a + b) (a' := -c) (by grind),
        Finsupp.single_eq_of_ne (a := b + c) (a' := -a) (by grind)]

/-- We endow the trivial Lie module with a Lie ring structure with zero bracket. -/
instance {R : Type*} [CommRing R] :
    LieRing (TrivialLieModule R L R) where
  bracket _ _ := 0
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := rfl
  leibniz_lie _ _ _ := by simp

/-- We endow the trivial Lie module with an abelian Lie ring structure. -/
instance {R : Type*} [CommRing R] :
    IsLieAbelian (TrivialLieModule R L R) where
  trivial _ _ := rfl

/-- We endow the trivial Lie module with a trivial Lie algebra structure. -/
instance {R : Type*} [CommRing R] :
    LieAlgebra R (TrivialLieModule R L R) where
  lie_smul _ _ _ := by simp

set_option backward.isDefEq.respectTransparency false in
/-- The extension of a loop algebra by a trivial module. -/
def extension [CommRing A] [IsAddTorsionFree R] [Algebra A R]
    (Φ : LinearMap.BilinForm R L) (hΦ : LinearMap.BilinForm.lieInvariant L Φ)
    (hΦs : LinearMap.BilinForm.IsSymm Φ) :
    LieAlgebra.Extension R (TrivialLieModule R (loopAlgebra R A L) R) (loopAlgebra R A L) :=
  Extension.ofTwoCocycle (twoCocycleOfBilinear R A L Φ hΦ hΦs)

--letI _ := Extension.ringModuleOf (extension R A L Φ hΦ hΦs)
--    have this := Extension.lieModuleOf (extension R A L Φ hΦ hΦs)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma twoCocycleOf_extension [CommRing A] [IsAddTorsionFree R] [Algebra A R]
    (Φ : LinearMap.BilinForm R L) (hΦ : LinearMap.BilinForm.lieInvariant L Φ)
    (hΦs : LinearMap.BilinForm.IsSymm Φ) :
    ((LieAlgebra.LoopAlgebra.extension R A L Φ hΦ hΦs).twoCocycleOf
    (LieAlgebra.Extension.section_proj_leftInverse (twoCocycleOfBilinear R A L Φ hΦ hΦs))).1 =
    twoCocycleOfBilinear R A L Φ hΦ hΦs := by
  dsimp only [extension]
  rw [Extension.twoCocycleOf_ofTwoCocycle]

end CentralExt

section PositiveEnergy

variable [CommRing A] [Algebra A R]

set_option backward.isDefEq.respectTransparency false in
lemma twoCocycle_apply_single_single [IsAddTorsionFree R] (Φ : LinearMap.BilinForm R L)
    (hΦ : LinearMap.BilinForm.lieInvariant L Φ)
    (hΦs : LinearMap.BilinForm.IsSymm Φ) {a b : A} (h : -b ≠ a) (r s : R) (x y : L) :
    ((LieAlgebra.LoopAlgebra.extension R A L Φ hΦ hΦs).twoCocycleOf
    (LieAlgebra.Extension.section_proj_leftInverse (twoCocycleOfBilinear R A L Φ hΦ hΦs))).1
    ((AddMonoidAlgebra.single a r) ⊗ₜ x) ((AddMonoidAlgebra.single b s) ⊗ₜ y) = 0 := by
  simp [twoCocycleOf_extension, Finsupp.single_eq_of_ne h]

@[to_additive]
theorem _root_.Finsupp.prod_eq_one {α M N : Type*} [Zero M] [CommMonoid N] {f : α →₀ M}
    {g : α → M → N} (h₀ : ∀ b, f b ≠ 0 → g b (f b) = 1) :
    f.prod g = 1 := by
  exact Finset.prod_eq_one fun b hb ↦ h₀ b (Finsupp.mem_support_iff.mp hb)
--#find_home! Finsupp.prod_eq_one --[Mathlib.Algebra.BigOperators.Finsupp.Basic]

set_option backward.isDefEq.respectTransparency false in
lemma twoCocycle_apply_single [IsAddTorsionFree R] (Φ : LinearMap.BilinForm R L)
    (hΦ : LinearMap.BilinForm.lieInvariant L Φ)
    (hΦs : LinearMap.BilinForm.IsSymm Φ) {a : A} {p : loopAlgebra R A L}
    (h : ∀ b ∈ (toFinsupp R A L p).support, -b ≠ a) (r : R) (x : L) :
    ((LieAlgebra.LoopAlgebra.extension R A L Φ hΦ hΦs).twoCocycleOf
    (LieAlgebra.Extension.section_proj_leftInverse (twoCocycleOfBilinear R A L Φ hΦ hΦs))).1
    ((AddMonoidAlgebra.single a r) ⊗ₜ x) p = 0 := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    induction x using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add _ _ _ _ =>
      simp only [twoCocycleOf_extension, twoCocycleOfBilinear_coe, twoCochainOfBilinear_apply_apply,
        residuePairing_apply_apply, Finsupp.sum, toFinsupp_single_tmul, map_sum]
      exact Finset.sum_eq_zero fun b hb ↦ (by simp [Finsupp.single_eq_of_ne (fun x ↦ h b hb x)])
    | single m r =>
      have : r • y ≠ 0 → -m ≠ a := by simpa using h m
      simp only [twoCocycleOf_extension, twoCocycleOfBilinear_coe, twoCochainOfBilinear_apply_apply,
        residuePairing_apply_apply, toFinsupp_single_tmul, map_zero, smul_zero,
        Finsupp.sum_single_index, map_smul, EmbeddingLike.map_eq_zero_iff]
      by_cases h : -m = a
      · simp only [h, Finsupp.single_eq_same, map_smul, LinearMap.smul_apply]
        rw [smul_comm r, ← map_smul]
        simp [Function.notMem_support.mp fun a ↦ this a h]
      · simp [h]
  | add u _ _ _ =>
    induction u with
    | zero => simp_all
    | tmul _ _ =>
      simp only [twoCocycleOf_extension, twoCocycleOfBilinear_coe, twoCochainOfBilinear_apply_apply,
        residuePairing_apply_apply, toFinsupp_single_tmul, Finsupp.sum]
      exact Finset.sum_eq_zero fun b hb ↦ by simp [Finsupp.single_eq_of_ne (h b hb)]
    | add _ _ _ _ =>
      simp only [twoCocycleOf_extension, twoCocycleOfBilinear_coe, twoCochainOfBilinear_apply_apply,
        residuePairing_apply_apply, toFinsupp_single_tmul, Finsupp.sum]
      exact Finset.sum_eq_zero fun b hb ↦ by simp [Finsupp.single_eq_of_ne (h b hb)]

set_option backward.isDefEq.respectTransparency false in
lemma twoCocycle_apply_apply_zero [IsAddTorsionFree R] (Φ : LinearMap.BilinForm R L)
    (hΦ : LinearMap.BilinForm.lieInvariant L Φ)
    (hΦs : LinearMap.BilinForm.IsSymm Φ) (p q : loopAlgebra R A L)
    (hpq : ∀ a ∈ (toFinsupp R A L p).support, ∀ b ∈ (toFinsupp R A L q).support, -b ≠ a ∨ a = 0) :
    ((LieAlgebra.LoopAlgebra.extension R A L Φ hΦ hΦs).twoCocycleOf
    (LieAlgebra.Extension.section_proj_leftInverse (twoCocycleOfBilinear R A L Φ hΦ hΦs))).1
    p q = 0 := by
  simp only [twoCocycleOf_extension, twoCocycleOfBilinear_coe, twoCochainOfBilinear_apply_apply,
    residuePairing_apply_apply, EmbeddingLike.map_eq_zero_iff]
  rw [Finsupp.sum_eq_zero]
  intro a ha
  have := fun b hb ↦ hpq b hb a (Finsupp.mem_support_iff.mpr ha)
  contrapose! this
  use -a
  exact ⟨by contrapose! this; simp [Finsupp.notMem_support_iff.mp this],
    ⟨rfl, neg_ne_zero.mpr <| left_ne_zero_of_smul this⟩⟩

--Make this more general - two submonoids that don't generate nontrivial units?

set_option backward.isDefEq.respectTransparency false in
lemma twoCocycle_nat [IsAddTorsionFree R] (Φ : LinearMap.BilinForm R L)
    (hΦ : LinearMap.BilinForm.lieInvariant L Φ)
    (hΦs : LinearMap.BilinForm.IsSymm Φ) (p q : loopAlgebra R ℕ L) :
    ((LieAlgebra.LoopAlgebra.extension R ℤ L Φ hΦ hΦs).twoCocycleOf
    (LieAlgebra.Extension.section_proj_leftInverse (twoCocycleOfBilinear R ℤ L Φ hΦ hΦs))).1
    (mapMonomialLieHom R L (Nat.castAddMonoidHom ℤ) p)
    (mapMonomialLieHom R L (Nat.castAddMonoidHom ℤ) q) = 0 := by
  refine twoCocycle_apply_apply_zero R ℤ L Φ hΦ hΦs
    (mapMonomialLieHom R L (Nat.castAddMonoidHom ℤ) p)
    (mapMonomialLieHom R L (Nat.castAddMonoidHom ℤ) q) ?_
  intro a ha b hb
  have ha := support_toFinsupp_mapMonomialLieHom R ℤ L (Nat.castAddMonoidHom ℤ) p ha
  obtain ⟨a', ha'⟩ := ha
  simp only [Nat.coe_castAddMonoidHom] at ha'
  have hb := support_toFinsupp_mapMonomialLieHom R ℤ L (Nat.castAddMonoidHom ℤ) q hb
  obtain ⟨b', hb'⟩ := hb
  simp only [Nat.coe_castAddMonoidHom] at hb'
  grind

set_option backward.isDefEq.respectTransparency false in
/-- The linear map from `L` to the extended loop algebra taking `x` to `x ⊗ t^a`. -/
def monomial' [IsAddTorsionFree R] (Φ : LinearMap.BilinForm R L)
    (hΦ : LinearMap.BilinForm.lieInvariant L Φ) (hΦs : LinearMap.BilinForm.IsSymm Φ) (a : A) :
    L →ₗ[R] (extension R A L Φ hΦ hΦs).L where
  toFun x := ofProd (twoCocycleOfBilinear R A L Φ hΦ hΦs) (AddMonoidAlgebra.single a 1 ⊗ₜ x, 0)
  map_add' x y := by rw [← of_add, Prod.mk_zero_add_mk_zero, ← TensorProduct.tmul_add]
  map_smul' r x := by rw [TensorProduct.tmul_smul, RingHom.id_apply, ← of_smul, Prod.smul_mk_zero]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma proj_monomial' [IsAddTorsionFree R] (Φ : LinearMap.BilinForm R L)
    (hΦ : LinearMap.BilinForm.lieInvariant L Φ) (hΦs : LinearMap.BilinForm.IsSymm Φ) (a : A)
    (x : L) :
    (extension R A L Φ hΦ hΦs).proj ((monomial' R A L Φ hΦ hΦs a) x) =
      (AddMonoidAlgebra.single a (1 : R) ⊗ₜ x):=
  rfl

-- Introduce `A`-grading before the derivation - Any grading yields a derivation.
/-
open Finsupp Pointwise in
/-- The energy derivation on the centrally extended Lie algebra, that scalar-multiplies an
`A`-graded vector by its grading. -/
def energy [IsAddTorsionFree R] (Φ : LinearMap.BilinForm R L)
    (hΦ : LinearMap.BilinForm.lieInvariant L Φ) (hΦs : LinearMap.BilinForm.IsSymm Φ) :
    LieDerivation R (extension R A L Φ hΦ hΦs).L (extension R A L Φ hΦ hΦs).L :=
    letI F := ((toFinsupp R A L) ∘ₗ (extension R A L Φ hΦ hΦs).proj.toLinearMap :
      (extension R A L Φ hΦ hΦs).L →ₗ[R] (A →₀ L))
    { toFun g := (F g).sum fun a v ↦ (a • (1 : R)) • (monomial' R A L Φ hΦ hΦs a) v
      map_add' x y := by
        classical
        let u : Finset A := (F x).support ∪ (F y).support
        have hu₁ : (F x).support ⊆ u := Finset.subset_union_left
        have hu₂ : (F y).support ⊆ u := Finset.subset_union_right
        have hu₃ : (F (x + y)).support ⊆ u := fun a ha ↦ by
          replace ha : F x a + F y a ≠ 0 := by simpa using ha
          obtain (h|h) := ne_zero_or_ne_zero_of_add ha
          · exact hu₁ <| mem_support_iff.mpr h
          · exact hu₂ <| mem_support_iff.mpr h
        rw [sum_of_support_subset _ hu₃ _ (fun _ _ ↦ by rw [map_zero, smul_zero]),
          sum_of_support_subset _ hu₁ _ (fun _ _ ↦ by rw [map_zero, smul_zero]),
          sum_of_support_subset _ hu₂ _ (fun _ _ ↦ by rw [map_zero, smul_zero])]
        simp [map_add, Finset.sum_add_distrib, u]
      map_smul' r x := by
        rw [map_smul, sum_of_support_subset _ support_smul _
          (fun _ _ ↦ by rw [map_zero, smul_zero]), sum, Finset.smul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ by simp [smul_algebra_smul_comm r]
      leibniz' x y := by
        classical
        let u : Finset A := (F x).support + (F y).support ∪ {0}
        have hu : (F ⁅x, y⁆).support ⊆ u := by
          intro b hb
          simp only [Finset.union_singleton, Finset.mem_insert, u]
          contrapose! hb
          simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, LieHom.coe_toLinearMap,
            Function.comp_apply, LieHom.map_lie, mem_support_iff, Decidable.not_not, F]


        simp only [monomial'_apply, LinearMap.coe_mk, AddHom.coe_mk]

        sorry
      }
-/


-- smooth rep : U(positive part)v finite dimensional for all v.

--use LieRingModule.compLieHom
/-
Need a class for graded representations.
Need a class for "has central charge"

What is a positive-energy representation? Energy grading is bounded below.
Also, energy is governed by the grading on the central extension.
Maybe make a class?

def vacuum_rep [IsAddTorsionFree R]
    (Φ : LinearMap.BilinForm R L) (hΦ : LinearMap.BilinForm.lieInvariant L Φ)
    (hΦs : LinearMap.BilinForm.IsSymm Φ) : LieRingModule (extension R ℤ L Φ hΦ hΦs).L
-/
-- extend central characters to reps of positive part
-- induce positive part reps to centrally extended loop algebra
-- monomial basis of induced rep (needs PBW)
-- define positive energy reps (positive part `U+` acts locally nilpotently - `U+ • v` fin dim.)

end PositiveEnergy

end LoopAlgebra

end LieAlgebra
