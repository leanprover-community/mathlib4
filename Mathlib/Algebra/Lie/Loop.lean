/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Algebra.Lie.InvariantForm
--public import Mathlib.Algebra.Lie.Extension
public import Mathlib.Algebra.Lie.Cochain
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
flexibility. The classical loop algebra is then written `LoopAlgebra R ℤ L`.

## Main definitions
* `LieAlgebra.LoopAlgebra`: The tensor product of a Lie algebra with an `AddMonoidAlgebra`.
* `LieAlgebra.LoopAlgebra.twoCochain_of_Bilinear`: The 2-cochain for a loop algebra with trivial
  coefficients attached to a symmetric bilinear form on the base Lie algebra.
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
abbrev LoopAlgebra := AddMonoidAlgebra R A ⊗[R] L

namespace LoopAlgebra

instance instLoopLieRing [AddCommMonoid A] : LieRing (LoopAlgebra R A L) :=
  ExtendScalars.instLieRing R (AddMonoidAlgebra R A) L

instance instLoopLaurentLieAlgebra [AddCommMonoid A] :
    LieAlgebra (AddMonoidAlgebra R A) (LoopAlgebra R A L) :=
  ExtendScalars.instLieAlgebra R (AddMonoidAlgebra R A) L

instance instLieModule [AddCommMonoid A] :
    LieModule (AddMonoidAlgebra R A) (LoopAlgebra R A L) (LoopAlgebra R A L) :=
  lieAlgebraSelfModule (L := LoopAlgebra R A L)

/-- The linear map taking `x` to `T ^ n ⊗ x`. -/
def monomial {A} (a : A) : L →ₗ[R] LoopAlgebra R A L :=
  TensorProduct.mk R (AddMonoidAlgebra R A) L (AddMonoidAlgebra.single a (1 : R))

@[simp]
lemma addEquiv_monomial (a : A) (x : L) :
    monomial R L a x = (AddMonoidAlgebra.single a (1 : R) ⊗ₜ x) :=
  rfl

lemma monomial_smul (r : R) (a : A) (x : L) : monomial R L a (r • x) = r • (monomial R L a x) :=
  LinearMap.map_smul (monomial R L a) r x

/-- A basis of Laurent polynomials. -/
@[simps]
def basisMonomials : Module.Basis A R (AddMonoidAlgebra R A) :=
  Module.Basis.ofRepr ((LinearEquiv.refl R (A →₀ R)))
--#find_home! basisMonomials --here. Move to Algebra.Polynomial.Laurent?

lemma basisMonomials_eq (a : A) : basisMonomials R A a = AddMonoidAlgebra.single a (1 : R) := by
  rfl

open Classical in
/-- A linear isomorphism to finitely supported functions. -/
def toFinsupp : LoopAlgebra R A L ≃ₗ[R] A →₀ L :=
  TensorProduct.equivFinsuppOfBasisLeft (basisMonomials R A)

@[simp]
lemma toFinsupp_symm_single (a : A) :
    (toFinsupp R A L).symm ∘ (Finsupp.single a) = monomial R L a := by
  ext x
  simp [toFinsupp, basisMonomials_eq]

@[simp]
lemma toFinsupp_comp_monomial (a : A) : toFinsupp R A L ∘ (monomial R L a) = Finsupp.single a := by
  refine Eq.symm ?_
  refine (LinearEquiv.symm_comp_eq (R₁ := R) (R₂ := R) (monomial R L a) (Finsupp.single a)).mp ?_
  simp

lemma toFinsupp_monomial_apply (a : A) (x : L) :
    toFinsupp R A L (monomial R L a x) = Finsupp.single a x:= by
  rw [← Function.comp_apply (f := toFinsupp R A L), ← toFinsupp_comp_monomial R]

@[simp]
lemma toFinsupp_single_tmul (c : A) (z : L) :
    ((toFinsupp R A L) (AddMonoidAlgebra.single c 1 ⊗ₜ[R] z)) = Finsupp.single c z := by
  ext a
  rw [← addEquiv_monomial, toFinsupp_monomial_apply]

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

/-- Generalize: replace ℤ with an abelian group -/
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
-/

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

lemma bracketHom [AddCommMonoid A] (x y : LoopAlgebra R A L) :
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

lemma residuePairing_finite_support [AddCommGroup A] [SMulZeroClass A R]
    (Φ : LinearMap.BilinForm R L) (f g : A →₀ L) :
    Finite (fun n ↦ n • (Φ (f (-n)) (g n))).support := by
  refine Finite.Set.subset ((fun n ↦ (-n)) '' f.support) ?_
  intro n hn
  simp only [Set.image_neg_eq_neg, Set.mem_neg, SetLike.mem_coe, Finsupp.mem_support_iff]
  contrapose! hn
  simp [hn]

/-- The residue pairing on finitely supported functions.  When the functions are viewed as Laurent
polynomials with coefficients in `L`, the pairing is given by `(f, g) ↦ Res f dg`. -/
@[simps]
def residuePairingFinsupp [AddCommGroup A] [DistribSMul A R] [SMulCommClass A R R]
    (Φ : LinearMap.BilinForm R L) :
    (A →₀ L) →ₗ[R] (A →₀ L) →ₗ[R] R where
  toFun f := {
    toFun := fun g => ∑ᶠ n, n • (Φ (f (-n)) (g n))
    map_add' x y := by
      rw [← finsum_add_distrib (residuePairing_finite_support R A L Φ f x)
        (residuePairing_finite_support R A L Φ f y), finsum_congr]
      intro n
      simp
    map_smul' r x := by
      rw [RingHom.id_apply, smul_finsum' _ (residuePairing_finite_support R A L Φ f x),
        finsum_congr _]
      intro n
      simp [mul_smul_comm] }
  map_add' x y := by
    ext n z
    simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      Finsupp.lsingle_apply, LinearMap.add_apply]
    rw [← finsum_add_distrib (residuePairing_finite_support R A L Φ x _)
      (residuePairing_finite_support R A L Φ y _), finsum_congr]
    intro m
    simp
  map_smul' r x := by
    ext n y
    simp only [Finsupp.coe_smul, LinearMap.coe_comp, LinearMap.smul_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Function.comp_apply, RingHom.id_apply]
    rw [smul_finsum' _ (residuePairing_finite_support R A L Φ x _), finsum_congr]
    intro k
    simp [mul_smul_comm]
/-
/-- A cochain on finsupp -/
def residuePairingCochain (Φ : LinearMap.BilinForm R L) :
    letI := finsuppLieRing R L
    letI := finsuppRestrictLieAlgebra R L
    LieModule.Cohomology.twoCochain R (ℤ →₀ L) (TrivialLieModule R (LoopAlgebra R L) R) where
  val := (residuePairingFinsupp R L Φ).compr₂
    ((TrivialLieModule.equiv R (LoopAlgebra R L) R).symm.toLinearMap)
  property := sorry

def plusMinus [InvolutiveNeg A] : Setoid A where
  r a b := a = b ∨ a = -b
  iseqv := {
    refl := by grind
    symm := by grind [neg_eq_iff_eq_neg]
    trans := by grind [neg_eq_iff_eq_neg]}

--#find_home! plusMinus --[Mathlib.Algebra.Group.Defs]

lemma plusMinus_preimage [InvolutiveNeg A] (x : Quotient (plusMinus A)) {b : A}
    (h : Quotient.mk (plusMinus A) b = x) :
    (Quotient.mk (plusMinus A)) ⁻¹' {x} = {b, -b} := by
  refine Set.Subset.antisymm ?_ ?_
  · intro c hc
    simp only [plusMinus, Set.mem_preimage, Set.mem_singleton_iff, ← h, Quotient.eq] at hc
    simp [hc]
  · intro c hc
    simp_all [plusMinus, ← h, Quotient.eq]

lemma plusMinus_finite_preimage [InvolutiveNeg A] (x : Quotient (plusMinus A)) :
    ((Quotient.mk (plusMinus A)) ⁻¹' {x}).Finite := by
  obtain ⟨b, hb⟩ := (Quotient.exists (s := plusMinus A) (p := fun b ↦ b = x)).mp exists_eq
  refine Finite.Set.subset {b, -b} ?_
  · intro c hc
    simp only [plusMinus, Set.mem_preimage, Set.mem_singleton_iff, ← hb, Quotient.eq] at hc
    simp [hc]

lemma plusMinus_preimage_singleton [InvolutiveNeg A] (x : Quotient (plusMinus A)) {b : A}
    (hx : Quotient.mk (plusMinus A) b = x) :
    ((Quotient.mk (plusMinus A)) ⁻¹' {x}) = {b} ↔ b = -b := by
  constructor
  · intro h
    have : Quotient.mk (plusMinus A) (-b) = x := by simp [← hx, Quotient.eq, plusMinus]
    have : -b ∈ Quotient.mk (plusMinus A) ⁻¹' {x} := this
    exact Eq.symm (by simpa [h] using this)
  · intro h
    rw [plusMinus_preimage A x hx, ← h, Set.pair_eq_singleton]

/-- The residue pairing on a Loop algebra, with values in a trivial module. -/
def minusFold [InvolutiveNeg A] : A → Quotient (plusMinus A) := Quotient.mk (plusMinus A)

lemma Odd.support {α β : Type*} [AddCommGroup β] [InvolutiveNeg α] {f : α → β}
    (hf : Function.Odd f) (x : α) :
    x ∈ f.support ↔ -x ∈ f.support := by
  simp only [Function.mem_support, ne_eq]
  rw [not_iff_not, hf, neg_eq_zero]
--#find_home! Odd.support --here

lemma neg_mem_of_toFinset {α : Type*} [InvolutiveNeg α] {s : Set α} (hs : s.Finite)
    (hsn : ∀ x : α, x ∈ s ↔ -x ∈ s) (x : α) :
    x ∈ hs.toFinset ↔ -x ∈ hs.toFinset := by
  simp [hsn x]
--#find_home! neg_mem_of_toFinset -- Mathlib.Data.Set.Finite.Lemmas?

@[simps]
def InvolutiveNegSubtype {α β : Type*} [Zero β] [InvolutiveNeg α] {f : α → β}
    (hf : (Function.support f).Finite)
    (hfs : ∀ x : α, x ∈ Function.support f ↔ -x ∈ Function.support f) :
    InvolutiveNeg hf.toFinset where
  neg := fun a ↦ ⟨-(a.1), (neg_mem_of_toFinset hf hfs a.1).mp a.2⟩
  neg_neg := by simp
#find_home! InvolutiveNegSubtype --
lemma Odd.finsum_zero {α β : Type*} [AddCommGroup β] [InvolutiveNeg α] [IsAddTorsionFree β]
    {f : α → β} (hf : Function.Odd f) :
    ∑ᶠ a, f a = 0 := by
  by_cases h : (Function.support f).Finite
  · rw [finsum_eq_sum f h, ← Finset.sum_coe_sort h.toFinset f]
    let _ := InvolutiveNegSubtype h (fun a ↦ Odd.support hf a)
    rw [Function.Odd.sum_eq_zero (fun x ↦ by simp only [← hf x]; congr 1)]
  · exact finsum_of_infinite_support h
--#find_home! Odd.finsum_zero --here
-/

/-- A 2-cochain on a loop algebra given by an invariant bilinear form. The alternating condition
follows from the fact that Res f df = 0 -/
def twoCochainOfBilinear [AddCommGroup A] [IsAddTorsionFree R] [DistribSMul A R]
    [SMulCommClass A R R] (Φ : LinearMap.BilinForm R L) (hΦ : LinearMap.BilinForm.IsSymm Φ)
    (h : ∀ (a b : A) (r : R), (a + b) • r = a • r + b • r) :
    LieModule.Cohomology.twoCochain R (LoopAlgebra R A L)
      (TrivialLieModule R (LoopAlgebra R A L) R) where
  val := (((residuePairingFinsupp R A L Φ).compr₂
    ((TrivialLieModule.equiv R (LoopAlgebra R A L) R).symm.toLinearMap)).compl₂
    (toFinsupp R A L).toLinearMap).comp (toFinsupp R A L).toLinearMap
  property := by
    simp only [LieModule.Cohomology.mem_twoCochain_iff]
    intro f
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.compl₂_apply, LinearMap.compr₂_apply, residuePairingFinsupp_apply_apply,
      EmbeddingLike.map_eq_zero_iff]
    have zerosmul (r : R) : (0 : A) • r = (0 : R) := by
      have : (0 : A) • r = (0 : A) • r + (0 : A) • r := by rw [← h, zero_add (0 : A)]
      rwa [right_eq_add] at this
    set φ := fun n ↦ n • (Φ (((toFinsupp R A L) f) (-n))) (((toFinsupp R A L) f) n) with hφ
    have : Function.Odd φ := by
      intro n
      simp only [hφ, neg_neg, hΦ.eq (toFinsupp R A L f n) (toFinsupp R A L f (-n))]
      rw [eq_neg_iff_add_eq_zero, ← h, neg_add_cancel, zerosmul]
    simpa [neg_eq_self, finsum_neg_distrib, funext this] using finsum_comp_equiv (.neg A) (f := φ)

@[simp]
lemma twoCochainOfBilinear_apply_apply [AddCommGroup A] [IsAddTorsionFree R] [DistribSMul A R]
    [SMulCommClass A R R] (Φ : LinearMap.BilinForm R L) (hΦ : LinearMap.BilinForm.IsSymm Φ)
    (h : ∀ (a b : A) (r : R), (a + b) • r = a • r + b • r) (x y : LoopAlgebra R A L) :
    twoCochainOfBilinear R A L Φ hΦ h x y =
      (TrivialLieModule.equiv R (LoopAlgebra R A L) R).symm
        ((residuePairingFinsupp R A L Φ) (toFinsupp R A L x) (toFinsupp R A L y)) :=
  rfl

/-- A 2-cochain on a loop algebra given by an invariant bilinear form. The alternating condition
follows from the fact that Res f df = 0 -/
def twoCochainOfBilinear' [CommRing A] [IsAddTorsionFree R] [Algebra A R]
    (Φ : LinearMap.BilinForm R L) (hΦ : LinearMap.BilinForm.IsSymm Φ) :
    LieModule.Cohomology.twoCochain R (LoopAlgebra R A L)
      (TrivialLieModule R (LoopAlgebra R A L) R) where
  val := (((residuePairingFinsupp R A L Φ).compr₂
    ((TrivialLieModule.equiv R (LoopAlgebra R A L) R).symm.toLinearMap)).compl₂
    (toFinsupp R A L).toLinearMap).comp (toFinsupp R A L).toLinearMap
  property := by
    simp only [LieModule.Cohomology.mem_twoCochain_iff]
    intro f
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.compl₂_apply, LinearMap.compr₂_apply, residuePairingFinsupp_apply_apply,
      EmbeddingLike.map_eq_zero_iff]
    set φ := fun n ↦ n • (Φ (((toFinsupp R A L) f) (-n))) (((toFinsupp R A L) f) n) with hφ
    have : Function.Odd φ := by
      intro n
      simp [hφ, neg_neg, hΦ.eq (toFinsupp R A L f n) (toFinsupp R A L f (-n))]
    simpa [neg_eq_self, finsum_neg_distrib, funext this] using finsum_comp_equiv (.neg A) (f := φ)

@[simp]
lemma twoCochainOfBilinear'_apply_apply [CommRing A] [IsAddTorsionFree R] [Algebra A R]
    (Φ : LinearMap.BilinForm R L) (hΦ : LinearMap.BilinForm.IsSymm Φ)
    (x y : LoopAlgebra R A L) :
    twoCochainOfBilinear' R A L Φ hΦ x y =
      (TrivialLieModule.equiv R (LoopAlgebra R A L) R).symm
        ((residuePairingFinsupp R A L Φ) (toFinsupp R A L x) (toFinsupp R A L y)) :=
  rfl

/-- A 2-cocycle on a loop algebra given by an invariant bilinear form. -/
def twoCocycle'_of_Bilinear [CommRing A] [IsAddTorsionFree R] [Algebra A R]
    (Φ : LinearMap.BilinForm R L) (hΦ : LinearMap.BilinForm.lieInvariant L Φ)
    (hΦs : LinearMap.BilinForm.IsSymm Φ) :
    LieModule.Cohomology.twoCocycle R (LoopAlgebra R A L)
      (TrivialLieModule R (LoopAlgebra R A L) R) where
  val := twoCochainOfBilinear' R A L Φ hΦs
  property := by
    refine (LieModule.Cohomology.mem_twoCocycle_iff R (LoopAlgebra R A L)
            (TrivialLieModule R (LoopAlgebra R A L) R) (twoCochainOfBilinear' R A L Φ hΦs)).mpr ?_
    ext a x b y c z
    simp only [LinearMap.coe_comp, Function.comp_apply, AddMonoidAlgebra.lsingle_apply,
      TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self,
      TensorProduct.curry_apply, LieModule.Cohomology.d₂₃_apply, twoCochainOfBilinear'_apply_apply,
      toFinsupp_single_tmul, residuePairingFinsupp_apply_apply, trivial_lie_zero, sub_self,
      add_zero, ExtendScalars.bracket_tmul, AddMonoidAlgebra.single_mul_single, mul_one, zero_sub,
      LinearMap.zero_apply]
    rw [sub_eq_zero, neg_add_eq_iff_eq_add, ← LinearEquiv.map_add, EquivLike.apply_eq_iff_eq,
      finsum_eq_single _ b (fun _ h ↦ by simp [h]), finsum_eq_single _ c (fun _ h ↦ by simp [h]),
      finsum_eq_single _ a (fun _ h ↦ by simp [h])]
    by_cases hz : a + b + c = 0
    · rw [show a + b = -c by grind, show a + c = -b by grind, show b + c = -a by grind]
      simp only [Finsupp.single_eq_same]
      rw [hΦ, hΦs.eq z ⁅x, y⁆, hΦ y, ← lie_skew y x, hΦs.eq z, LinearMap.BilinForm.neg_left,
        neg_neg, show b = -(a + c) by grind, neg_smul, smul_neg, neg_neg, add_smul, add_comm]
    · simp [Finsupp.single_eq_of_ne (a := a + c) (a' := -b) (by grind),
        Finsupp.single_eq_of_ne (a := a + b) (a' := -c) (by grind),
        Finsupp.single_eq_of_ne (a := b + c) (a' := -a) (by grind)]

/-- A 2-cocycle on a loop algebra given by an invariant bilinear form. -/
def twoCocycle_of_Bilinear [AddCommGroup A] [IsAddTorsionFree R] [DistribSMul A R]
    [SMulCommClass A R R] (Φ : LinearMap.BilinForm R L) (hΦ : LinearMap.BilinForm.lieInvariant L Φ)
    (hΦs : LinearMap.BilinForm.IsSymm Φ) (h : ∀ (a b : A) (r : R), (a + b) • r = a • r + b • r) :
    LieModule.Cohomology.twoCocycle R (LoopAlgebra R A L)
      (TrivialLieModule R (LoopAlgebra R A L) R) where
  val := twoCochainOfBilinear R A L Φ hΦs h
  property := by
    refine (LieModule.Cohomology.mem_twoCocycle_iff R (LoopAlgebra R A L)
            (TrivialLieModule R (LoopAlgebra R A L) R) (twoCochainOfBilinear R A L Φ hΦs h)).mpr ?_
    ext a x b y c z
    simp only [LinearMap.coe_comp, Function.comp_apply, AddMonoidAlgebra.lsingle_apply,
      TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self,
      TensorProduct.curry_apply, LieModule.Cohomology.d₂₃_apply, twoCochainOfBilinear_apply_apply,
      toFinsupp_single_tmul, residuePairingFinsupp_apply_apply, trivial_lie_zero, sub_self,
      add_zero, ExtendScalars.bracket_tmul, AddMonoidAlgebra.single_mul_single, mul_one, zero_sub,
      LinearMap.zero_apply]
    rw [sub_eq_zero, neg_add_eq_iff_eq_add, ← LinearEquiv.map_add, EquivLike.apply_eq_iff_eq,
      finsum_eq_single _ b (fun _ h ↦ by simp [h]), finsum_eq_single _ c (fun _ h ↦ by simp [h]),
      finsum_eq_single _ a (fun _ h ↦ by simp [h])]
    by_cases hz : a + b + c = 0
    · have zerosmul (r : R) : (0 : A) • r = (0 : R) := by
        have : (0 : A) • r = (0 : A) • r + (0 : A) • r := by rw [← h, zero_add (0 : A)]
        rwa [right_eq_add] at this
      have hneg (i : A) (r : R) : (-i) • r = -(i • r) := by
        refine (neg_eq_of_add_eq_zero_right ?_).symm
        rw [← h, add_neg_cancel, zerosmul]
      rw [show a + b = -c by grind, show a + c = -b by grind, show b + c = -a by grind]
      simp only [Finsupp.single_eq_same]
      rw [hΦ, hΦs.eq z ⁅x, y⁆, hΦ y, ← lie_skew y x, hΦs.eq z, LinearMap.BilinForm.neg_left,
        neg_neg, show b = -(a + c) by grind, hneg, smul_neg, neg_neg, h, add_comm]
    · simp [Finsupp.single_eq_of_ne (a := a + c) (a' := -b) (by grind),
        Finsupp.single_eq_of_ne (a := a + b) (a' := -c) (by grind),
        Finsupp.single_eq_of_ne (a := b + c) (a' := -a) (by grind)]

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
