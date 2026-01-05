/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Lie.BaseChange
--public import Mathlib.Algebra.Lie.InvariantForm
--public import Mathlib.Algebra.Lie.Extension
public import Mathlib.Algebra.Lie.Cochain
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Data.Set.MulAntidiagonal
public import Mathlib.LinearAlgebra.BilinearForm.Properties
--public import Mathlib.LinearAlgebra.TensorProduct.Basis

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


## Main definitions

* Loop Algebra
* Evaluation representation
* Construction of central extensions from invariant forms. (todo)
* representation with fixed central character (todo)
* Positive energy representation (todo)

## Tags

lie ring, lie algebra, base change, Laurent polynomial, central extension
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

variable (R A L M : Type*)

namespace LieAlgebra

variable [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- A loop algebra is the base change of a Lie algebra `L` over `R` by `R[z,z^{-1}]`. -/
abbrev LoopAlgebra := LaurentPolynomial R ⊗[R] L

namespace LoopAlgebra

instance instLoopLieRing : LieRing (LoopAlgebra R L) :=
  ExtendScalars.instLieRing R (LaurentPolynomial R) L

instance instLoopLaurentLieAlgebra : LieAlgebra (LaurentPolynomial R) (LoopAlgebra R L) :=
  ExtendScalars.instLieAlgebra R (LaurentPolynomial R) L

instance instLieModule : LieModule (LaurentPolynomial R) (LoopAlgebra R L) (LoopAlgebra R L) :=
    lieAlgebraSelfModule (L := LoopAlgebra R L)

--#synth LieModule R (LoopAlgebra R L) (LoopAlgebra R L) --fails

/-- The linear map taking `x` to `T ^ n ⊗ x`. -/
def monomial (n : ℤ) : L →ₗ[R] LoopAlgebra R L :=
  TensorProduct.mk R (LaurentPolynomial R) L (LaurentPolynomial.T n)

@[simp]
lemma addEquiv_monomial (n : ℤ) (x : L) :
    monomial R L n x = (LaurentPolynomial.T n ⊗ₜ x) :=
  rfl

lemma monomial_smul (r : R) (n : ℤ) (x : L) : monomial R L n (r • x) = r • (monomial R L n x) :=
  LinearMap.map_smul (monomial R L n) r x

/-- A basis of Laurent polynomials. -/
@[simps]
def basisMonomials : Module.Basis ℤ R (LaurentPolynomial R) :=
  Module.Basis.ofRepr ((LinearEquiv.refl R (ℤ →₀ R)))
--#find_home! basisMonomials --here. Move to Algebra.Polynomial.Laurent?

lemma basisMonomials_eq (n : ℤ) : basisMonomials R n = LaurentPolynomial.T n := by
  rfl

/-- A linear isomorphism to finitely supported functions. -/
def toFinsupp : LoopAlgebra R L ≃ₗ[R] ℤ →₀ L :=
  TensorProduct.equivFinsuppOfBasisLeft (basisMonomials R)

@[simp]
lemma toFinsupp_symm_single (n : ℤ) :
    (toFinsupp R L).symm ∘ (Finsupp.single n) = monomial R L n := by
  ext x
  simp [toFinsupp, basisMonomials_eq]

@[simp]
lemma toFinsupp_comp_monomial (n : ℤ) : toFinsupp R L ∘ (monomial R L n) = Finsupp.single n := by
  refine Eq.symm ?_
  refine (LinearEquiv.symm_comp_eq (R₁ := R) (R₂ := R) (monomial R L n) (Finsupp.single n)).mp ?_
  simp

lemma monomial_injective (n : ℤ) : Function.Injective (monomial R L n) := by
  rw [← toFinsupp_symm_single]
  exact (EmbeddingLike.comp_injective _ (toFinsupp R L).symm).mpr (Finsupp.single_injective n)

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

/-- Generalize: replace ℤ with an abelian group -/
lemma finite_support_bracket (n : ℤ) (x y : ℤ →₀ L) :
    Finite (fun (k : Set.addAntidiagonal Set.univ Set.univ n) ↦ ⁅x k.1.1, y k.1.2⁆).support := by
  refine Set.Finite.of_finite_image (f := fun k ↦ k.1.1) ?_ ?_
  · refine Set.Finite.subset (Finite.of_fintype x.support) ?_
    simp only [Set.image_subset_iff, Function.support_subset_iff, ne_eq, Set.mem_preimage,
      SetLike.mem_coe, Finsupp.mem_support_iff, Subtype.forall, Set.mem_addAntidiagonal,
      Set.mem_univ, true_and, Prod.forall]
    intro k l _ h
    contrapose! h
    simp [h]
  · exact fun _ _ _ _ h ↦ Set.AddAntidiagonal.eq_of_fst_eq_fst h

/-- This needs to be generalized: replace ℤ with an abelian group and Lie bracket with any bilinear
map -/
lemma finite_support_finsum_bracket (x y : ℤ →₀ L) :
    Finite (fun (n : ℤ) ↦
      ∑ᶠ (k : Set.addAntidiagonal Set.univ Set.univ n), ⁅x k.1.1, y k.1.2⁆).support := by
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
-/

theorem support_finsum_subset_image_support {α β M : Type*} [AddCommMonoid M] (f : α → β)
    (g : α → M) (hg : (Function.support g).Finite) :
    (Function.support fun b ↦ ∑ᶠ (a : α) (_ : f a = b), g a) ⊆
      (Set.Finite.image f hg).toFinset := by
  intro b hb
  obtain ⟨a, h, ha⟩ := exists_ne_zero_of_finsum_mem_ne_zero hb
  refine Finset.mem_coe.mpr ?_
  refine (Set.Finite.mem_toFinset (Set.Finite.image f hg)).mpr ?_
  refine (Set.mem_image f (Function.support g) b).mpr ?_
  use a
  exact ⟨ha, h⟩

theorem finsum_fiberwise {α β M : Type*} [AddCommMonoid M] (f : α → β) (g : α → M)
    (hg : (Function.support g).Finite) :
    ∑ᶠ (b : β) (a : α) (_ : f a = b), g a = ∑ᶠ (a : α), g a := by
  rw [finsum_eq_sum g hg]
  have : (f '' (Function.support g)).Finite := Set.Finite.image f hg
  rw [finsum_eq_sum_of_support_subset (s := (Set.Finite.image f hg).toFinset)]
  swap; · exact support_finsum_subset_image_support f g hg
  have (i : β) : (Function.support fun a ↦ ∑ᶠ (_ : f a = i), g a).Finite := by
    refine (Set.Finite.subset hg fun a ha ha0 ↦ ?_)
    rw [Function.mem_support, ha0, finsum_zero] at ha
    exact ha rfl
  have _ (a : α) (b : β) := Classical.propDecidable (f a = b)
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

/-
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
-/

/-- A Lie ring structure on finitely supported functions on a Lie algebra `L`. -/
def finsuppLieRing : LieRing (ℤ →₀ L) where
  bracket x y := toFinsupp R L ⁅(toFinsupp R L).symm x, (toFinsupp R L).symm y⁆
  add_lie := by simp
  lie_add := by simp
  lie_self := by simp
  leibniz_lie := by simp

@[simp]
lemma finsuppLieRing_apply (x y : ℤ →₀ L) :
    letI := finsuppLieRing R L
    ⁅x, y⁆ = (toFinsupp R L) ⁅(toFinsupp R L).symm x, (toFinsupp R L).symm y⁆ := rfl

lemma bracketHom (x y : LoopAlgebra R L) :
    letI := finsuppLieRing R L
    ⁅(toFinsupp R L) x, (toFinsupp R L) y⁆ = toFinsupp R L ⁅x, y⁆ := by
  simp

/-- The scalar multiplication of Laurent polynomials on finsupps. -/
@[simps]
def laurentSMul : SMul (LaurentPolynomial R) (ℤ →₀ L) where
  smul r x := toFinsupp R L (r • ((toFinsupp R L).symm x))

/-- The `R[T,T⁻¹]`-Lie algebra structure on finsupp. -/
def finsuppLieAlgebra :
    letI := finsuppLieRing R L
    LieAlgebra (LaurentPolynomial R) (ℤ →₀ L) :=
  letI := finsuppLieRing R L
  { smul r x := (laurentSMul R L).smul r x
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
def finsuppRestrictLieAlgebra :
    letI := finsuppLieRing R L
    LieAlgebra R (ℤ →₀ L) :=
  letI := finsuppLieRing R L
  letI := finsuppLieAlgebra R L
  LieAlgebra.RestrictScalars.lieAlgebra R (LaurentPolynomial R) (ℤ →₀ L)

/-!
/-- The evaluation representation, given by composing a representation with the evaluation map
`L[z,z^{-1}] → L` attached to a unit in `R`. -/
--define eval (x : Units R) : (LoopAlgebra R L) →ₗ⁅R⁆ L where
  toFun l := sorry
  map_add' := sorry
  map_smul' := sorry
  map_lie' := sorry

/-- The evaluation module -/
-- define eval.LieModule
-/

section CentralExt

lemma residuePairing_finite_support (Φ : LinearMap.BilinForm R L) (f g : ℤ →₀ L) :
    Finite (fun n ↦ n • (Φ (f (-n)) (g n))).support := by
  refine Finite.Set.subset ((fun (n : ℤ) ↦ (-n)) '' f.support) ?_
  intro n hn
  simp only [Set.image_neg_eq_neg, Set.mem_neg, SetLike.mem_coe, Finsupp.mem_support_iff]
  contrapose! hn
  simp [hn]

/-- The residue pairing on finitely supported functions.  When the functions are viewed as Laurent
polynomials with coefficients in `L`, the pairing is given by `(f, g) ↦ Res f dg`. -/
@[simps]
def residuePairingFinsupp (Φ : LinearMap.BilinForm R L) :
    (ℤ →₀ L) →ₗ[R] (ℤ →₀ L) →ₗ[R] R where
  toFun f := {
    toFun := fun g => ∑ᶠ (n : ℤ), n • (Φ (f (-n)) (g n))
    map_add' x y := by
      rw [← finsum_add_distrib (residuePairing_finite_support R L Φ f x)
        (residuePairing_finite_support R L Φ f y), finsum_congr]
      intro n
      simp
    map_smul' r x := by
      rw [RingHom.id_apply, smul_finsum' _ (residuePairing_finite_support R L Φ f x),
        finsum_congr _]
      intro n
      simp [mul_left_comm] }
  map_add' x y := by
    ext n z
    simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      Finsupp.lsingle_apply, LinearMap.add_apply]
    rw [← finsum_add_distrib (residuePairing_finite_support R L Φ x _)
      (residuePairing_finite_support R L Φ y _), finsum_congr]
    intro m
    simp
  map_smul' r x := by
    ext n y
    simp only [Finsupp.coe_smul, LinearMap.coe_comp, LinearMap.smul_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Function.comp_apply, RingHom.id_apply]
    rw [smul_finsum' _ (residuePairing_finite_support R L Φ x _), finsum_congr]
    intro k
    simp [mul_left_comm]
/-
/-- A cochain on finsupp -/
def residuePairingCochain (Φ : LinearMap.BilinForm R L) :
    letI := finsuppLieRing R L
    letI := finsuppRestrictLieAlgebra R L
    LieModule.Cohomology.twoCochain R (ℤ →₀ L) (TrivialLieModule R (LoopAlgebra R L) R) where
  val := (residuePairingFinsupp R L Φ).compr₂
    ((TrivialLieModule.equiv R (LoopAlgebra R L) R).symm.toLinearMap)
  property := sorry
-/

/-- The residue pairing on a Loop algebra, with values in a trivial module. -/
def residuePairingLoop (Φ : LinearMap.BilinForm R L) :
    (LoopAlgebra R L) →ₗ[R] (LoopAlgebra R L) →ₗ[R] (TrivialLieModule R (LoopAlgebra R L) R) :=
  (((residuePairingFinsupp R L Φ).compr₂
    ((TrivialLieModule.equiv R (LoopAlgebra R L) R).symm.toLinearMap)).compl₂
    (toFinsupp R L).toLinearMap).comp (toFinsupp R L).toLinearMap

/- Problem: `TensorProduct.toAddCommMonoid` has default priority, while the chain
`LieRing → AddCommGroup → AddCommMonoid` has reduced priority steps. -/

/-- A 2-cochain on a loop algebra given by an invariant bilinear form. The alternating condition
follows from the fact that Res f df = 0 -/
def twoCochain_of_Bilinear (Φ : LinearMap.BilinForm R L) (hΦ : LinearMap.BilinForm.IsSymm Φ) :
    LieModule.Cohomology.twoCochain R (LoopAlgebra R L)
      (TrivialLieModule R (LoopAlgebra R L) R) where
  val := residuePairingLoop R L Φ
  property := by
    simp only [LieModule.Cohomology.mem_twoCochain_iff]
    intro f
    simp only [residuePairingLoop, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.compl₂_apply, LinearMap.compr₂_apply, residuePairingFinsupp_apply_apply,
      EmbeddingLike.map_eq_zero_iff]
    rw [← finsum_fiberwise (Int.natAbs) _ (residuePairing_finite_support R L Φ (toFinsupp R L f)
      (toFinsupp R L f)), finsum_eq_zero_of_forall_eq_zero]
    intro n
    rw [finsum_eq_sum_of_support_subset (s := {(n : ℤ), -(n : ℤ)})]
    · by_cases hn : n = 0
      · simp [hn]
      · simp [hn, hΦ.eq (toFinsupp R L f n) (toFinsupp R L f (-(n : ℤ)))]
    · intro z hz
      contrapose! hz
      have : ¬ z.natAbs = n := by simpa [Int.natAbs_eq_iff] using hz
      simp [this]

-- need `public import Mathlib.Algebra.Lie.InvariantForm`
/-
/-- A 2-cocycle on a loop algebra given by an invariant bilinear form. -/
def twoCocycle_of_Bilinear (Φ : LinearMap.BilinForm R L)
    (hΦ : LinearMap.BilinForm.lieInvariant L Φ) :
    LieModule.Cohomology.twoCocycle R (LoopAlgebra R L)
      (TrivialLieModule R (LoopAlgebra R L) R) where
  val := residuePairingLoop R L Φ

  property :=

    sorry

-/
--⁅A ⊗ f(t), B ⊗ g(t)⁆ = ⁅A,B⁆ ⊗ f(t)*g(t) + (Res fdg) * (A,B) • K

-- show that an invariant bilinear form on `L` produces a 2-cocycle for `LoopAlgebra R L`.
-- define central extensions given by invariant bilinear forms
-- extend central characters to reps of positive part
-- induce positive part reps to centrally extended loop algebra
-- monomial basis of induced rep (needs PBW)
-- define positive energy reps (positive part `U+` acts locally nilpotently - `U+ • v` fin dim.)

end CentralExt

end LoopAlgebra

end LieAlgebra
