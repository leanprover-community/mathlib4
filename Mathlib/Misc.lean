import Mathlib

@[simp]
lemma RingHom.rangeRestrict_injective_iff {R S : Type*} [Ring R] [Ring S] {f : R →+* S} :
    Function.Injective f.rangeRestrict ↔ Function.Injective f := by
  convert Set.injective_codRestrict _

@[to_additive]
theorem MonoidAlgebra.single_sub {R M : Type*} [Ring R] (a : M) (b₁ b₂ : R) :
    single a (b₁ - b₂) = single a b₁ - single a b₂ :=
  Finsupp.single_sub _ _ _

@[to_additive (attr := simp)]
theorem MonoidAlgebra.finset_sum_single {k G : Type*} [Fintype G] [Semiring k]
    (f : MonoidAlgebra k G) : ∑ g : G, single g (f g) = f := by
  classical
  rw [← sum_single f, Finsupp.sum_fintype]
  · conv_lhs =>
      enter [2, g, 2]
      rw [Finset.sum_apply']
      simp [single_apply]
  · intro _
    simp

open NumberField in
example {m : ℕ} [NeZero m] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K]
    {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 K)) [P.LiesOver (Ideal.span {(p : ℤ)})]
    (hm : (Ideal.absNorm P - 1).Coprime m) :
    (Ideal.span {(p : ℤ)}).inertiaDeg P = orderOf (ZMod.unitOfCoprime _ hm) := by
  let ζ := (IsCyclotomicExtension.zeta_spec m ℚ K).toInteger
  have : RingOfIntegers.exponent ζ = 1 := by
    rw [RingOfIntegers.exponent_eq_one_iff]
