/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Flat.Stability

/-!
# Various results about unramified algebras

We prove various theorems about unramified algebras. In fact we work in the more general setting
of formally unramified algebras which are essentially of finite type.

## Main results

- `Algebra.FormallyUnramified.iff_exists_tensorProduct`:
  A finite-type `R`-algebra `S` is (formally) unramified iff
  there exists a `t : S ⊗[R] S` satisfying
  1. `t` annihilates every `1 ⊗ s - s ⊗ 1`.
  2. the image of `t` is `1` under the map `S ⊗[R] S → S`.
- `Algebra.FormallyUnramified.finite_of_free`: An unramified free algebra is finitely generated.
- `Algebra.FormallyUnramified.flat_of_restrictScalars`:
  If `S` is an unramified `R`-algebra, then `R`-flat implies `S`-flat.

## References

- [B. Iversen, *Generic Local Structure of the Morphisms in Commutative Algebra*][iversen]

-/

open Algebra Module
open scoped TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

namespace Algebra.FormallyUnramified

/--
Proposition I.2.3 + I.2.6 of [iversen]
A finite-type `R`-algebra `S` is (formally) unramified iff there exists a `t : S ⊗[R] S` satisfying
1. `t` annihilates every `1 ⊗ s - s ⊗ 1`.
2. the image of `t` is `1` under the map `S ⊗[R] S → S`.
-/
theorem iff_exists_tensorProduct [EssFiniteType R S] :
    FormallyUnramified R S ↔ ∃ t : S ⊗[R] S,
      (∀ s, ((1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)) * t = 0) ∧ TensorProduct.lmul' R t = 1 := by
  rw [formallyUnramified_iff, KaehlerDifferential,
    Ideal.cotangent_subsingleton_iff, Ideal.isIdempotentElem_iff_of_fg _
      (KaehlerDifferential.ideal_fg R S)]
  have : ∀ t : S ⊗[R] S, TensorProduct.lmul' R t = 1 ↔ 1 - t ∈ KaehlerDifferential.ideal R S := by
    intro t
    simp only [KaehlerDifferential.ideal, RingHom.mem_ker, map_sub, map_one,
      sub_eq_zero, @eq_comm S 1]
  simp_rw [this, ← KaehlerDifferential.span_range_eq_ideal]
  constructor
  · rintro ⟨e, he₁, he₂ : _ = Ideal.span _⟩
    refine ⟨1 - e, ?_, ?_⟩
    · intro s
      obtain ⟨x, hx⟩ : e ∣ 1 ⊗ₜ[R] s - s ⊗ₜ[R] 1 := by
        rw [← Ideal.mem_span_singleton, ← he₂]
        exact Ideal.subset_span ⟨s, rfl⟩
      rw [hx, mul_comm, ← mul_assoc, sub_mul, one_mul, he₁.eq, sub_self, zero_mul]
    · rw [sub_sub_cancel, he₂, Ideal.mem_span_singleton]
  · rintro ⟨t, ht₁, ht₂⟩
    use 1 - t
    rw [← sub_sub_self 1 t] at ht₁; generalize 1 - t = e at *
    constructor
    · suffices e ∈ (Submodule.span (S ⊗[R] S) {1 - e}).annihilator by
        simpa [IsIdempotentElem, mul_sub, sub_eq_zero, eq_comm, -Ideal.submodule_span_eq,
          Submodule.mem_annihilator_span_singleton] using this
      exact (show Ideal.span _ ≤ _ by simpa only [Ideal.span_le, Set.range_subset_iff,
        Submodule.mem_annihilator_span_singleton, SetLike.mem_coe]) ht₂
    · apply le_antisymm <;> simp only [Ideal.submodule_span_eq, Ideal.mem_span_singleton, ht₂,
        Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Set.range_subset_iff]
      intro s
      use 1 ⊗ₜ[R] s - s ⊗ₜ[R] 1
      linear_combination ht₁ s

lemma finite_of_free_aux (I) [DecidableEq I] (b : Basis I R S)
    (f : I →₀ S) (x : S) (a : I → I →₀ R) (ha : a = fun i ↦ b.repr (b i * x)) :
    (1 ⊗ₜ[R] x * Finsupp.sum f fun i y ↦ y ⊗ₜ[R] b i) =
      Finset.sum (f.support.biUnion fun i ↦ (a i).support) fun k ↦
      Finsupp.sum (b.repr (f.sum fun i y ↦ a i k • y)) fun j c ↦ c • b j ⊗ₜ[R] b k := by
  rw [Finsupp.sum, Finset.mul_sum]
  subst ha
  let a i := b.repr (b i * x)
  conv_lhs =>
    simp only [TensorProduct.tmul_mul_tmul, one_mul, mul_comm x (b _),
      ← show ∀ i, Finsupp.linearCombination _ b (a i) = b i * x from
          fun _ ↦ b.linearCombination_repr _]
  conv_lhs => simp only [Finsupp.linearCombination, Finsupp.coe_lsum,
    LinearMap.coe_smulRight, LinearMap.id_coe, id_eq, Finsupp.sum, TensorProduct.tmul_sum,
    ← TensorProduct.smul_tmul]
  have h₁ : ∀ k,
    (Finsupp.sum (Finsupp.sum f fun i y ↦ a i k • b.repr y) fun j z ↦ z • b j ⊗ₜ[R] b k) =
      (f.sum fun i y ↦ (b.repr y).sum fun j z ↦ a i k • z • b j ⊗ₜ[R] b k) := by
    intro i
    rw [Finsupp.sum_sum_index]
    · congr
      ext j s
      rw [Finsupp.sum_smul_index]
      · simp only [mul_smul, Finsupp.sum, ← Finset.smul_sum]
      intro; simp only [zero_smul]
    · intro; simp only [zero_smul]
    · intros; simp only [add_smul]
  have h₂ : ∀ (x : S), ((b.repr x).support.sum fun a ↦ b.repr x a • b a) = x := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using b.linearCombination_repr
  simp only [a] at h₁
  simp_rw [map_finsuppSum, map_smul, h₁, Finsupp.sum, Finset.sum_comm (t := f.support),
    TensorProduct.smul_tmul', ← TensorProduct.sum_tmul, ← Finset.smul_sum, h₂]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_subset_zero_on_sdiff
  · exact Finset.subset_biUnion_of_mem (fun i ↦ (a i).support) hi
  · simp only [a, Finset.mem_sdiff, Finset.mem_biUnion, Finsupp.mem_support_iff, ne_eq, not_not,
      and_imp, forall_exists_index]
    simp +contextual
  · exact fun _ _ ↦ rfl

variable [FormallyUnramified R S] [EssFiniteType R S]

variable (R S) in
/--
A finite-type `R`-algebra `S` is (formally) unramified iff there exists a `t : S ⊗[R] S` satisfying
1. `t` annihilates every `1 ⊗ s - s ⊗ 1`.
2. the image of `t` is `1` under the map `S ⊗[R] S → S`.
See `Algebra.FormallyUnramified.iff_exists_tensorProduct`.
This is the choice of such a `t`.
-/
noncomputable
def elem : S ⊗[R] S :=
  (iff_exists_tensorProduct.mp inferInstance).choose

lemma one_tmul_sub_tmul_one_mul_elem
    (s : S) : (1 ⊗ₜ s - s ⊗ₜ 1) * elem R S = 0 :=
  (iff_exists_tensorProduct.mp inferInstance).choose_spec.1 s

lemma one_tmul_mul_elem
    (s : S) : (1 ⊗ₜ s) * elem R S = (s ⊗ₜ 1) * elem R S := by
  rw [← sub_eq_zero, ← sub_mul, one_tmul_sub_tmul_one_mul_elem]

lemma lmul_elem :
    TensorProduct.lmul' R (elem R S) = 1 :=
  (iff_exists_tensorProduct.mp inferInstance).choose_spec.2


variable (R S)

/-- An unramified free algebra is finitely generated. Iversen I.2.8 -/
lemma finite_of_free [Module.Free R S] : Module.Finite R S := by
  classical
  let I := Module.Free.ChooseBasisIndex R S
  -- Let `bᵢ` be an `R`-basis of `S`.
  let b : Basis I R S := Module.Free.chooseBasis R S
  -- Let `∑ₛ fᵢ ⊗ bᵢ : S ⊗[R] S` (summing over some finite `s`) be an element such that
  -- `∑ₛ fᵢbᵢ = 1` and `∀ x : S, xfᵢ ⊗ bᵢ = aᵢ ⊗ xfᵢ` which exists since `S` is unramified over `R`.
  have ⟨f, hf⟩ : ∃ (a : I →₀ S), elem R S = a.sum (fun i x ↦ x ⊗ₜ b i) := by
    let b' := ((Basis.singleton PUnit.{1} S).tensorProduct b).reindex (Equiv.punitProd I)
    use b'.repr (elem R S)
    conv_lhs => rw [← b'.linearCombination_repr (elem R S), Finsupp.linearCombination_apply]
    congr! with _ i x
    simp [b', Basis.tensorProduct, TensorProduct.smul_tmul']
  constructor
  -- I claim that `{ fᵢbⱼ | i, j ∈ s }` spans `S` over `R`.
  use Finset.image₂ (fun i j ↦ f i * b j) f.support f.support
  rw [← top_le_iff]
  -- For all `x : S`, let `bᵢx = ∑ aᵢⱼbⱼ`.
  rintro x -
  let a : I → I →₀ R := fun i ↦ b.repr (b i * x)
  -- Consider `F` such that `fⱼx = ∑ Fᵢⱼbⱼ`.
  let F : I →₀ I →₀ R := Finsupp.onFinset f.support (fun j ↦ b.repr (x * f j))
    (fun j ↦ not_imp_comm.mp fun hj ↦ by simp [Finsupp.notMem_support_iff.mp hj])
  have hG : ∀ j ∉ (Finset.biUnion f.support fun i ↦ (a i).support),
      b.repr (f.sum (fun i y ↦ a i j • y)) = 0 := by
    intro j hj
    simp only [Finset.mem_biUnion, Finsupp.mem_support_iff, ne_eq, not_exists, not_and,
      not_not] at hj
    simp only [Finsupp.sum]
    trans b.repr (f.support.sum (fun _ ↦ 0))
    · refine congr_arg b.repr (Finset.sum_congr rfl ?_)
      simp only [Finsupp.mem_support_iff]
      intro i hi
      rw [hj i hi, zero_smul]
    · simp only [Finset.sum_const_zero, map_zero]
  -- And `G` such that `∑ₛ aᵢⱼfᵢ = ∑ Gᵢⱼbⱼ`, where `aᵢⱼ` are the coefficients `bᵢx = ∑ aᵢⱼbⱼ`.
  let G : I →₀ I →₀ R := Finsupp.onFinset (Finset.biUnion f.support (fun i ↦ (a i).support))
    (fun j ↦ b.repr (f.sum (fun i y ↦ a i j • y)))
    (fun j ↦ not_imp_comm.mp (hG j))
  -- Then `∑ Fᵢⱼ(bⱼ ⊗ bᵢ) = ∑ fⱼx ⊗ bᵢ = ∑ fⱼ ⊗ xbᵢ = ∑ aᵢⱼ(fⱼ ⊗ bᵢ) = ∑ Gᵢⱼ(bⱼ ⊗ bᵢ)`.
  -- Since `bⱼ ⊗ bᵢ` forms an `R`-basis of `S ⊗ S`, we conclude that `F = G`.
  have : F = G := by
    apply Finsupp.finsuppProdEquiv.symm.injective
    apply (Finsupp.equivCongrLeft (Equiv.prodComm I I)).injective
    apply (b.tensorProduct b).repr.symm.injective
    suffices (F.sum fun a f ↦ f.sum fun b' c ↦ c • b b' ⊗ₜ[R] b a) =
        G.sum fun a f ↦ f.sum fun b' c ↦ c • b b' ⊗ₜ[R] b a by
      simpa [Finsupp.linearCombination_apply, Finsupp.sum_uncurry_index]
    have : ∀ i, ((b.repr (x * f i)).sum fun j k ↦ k • b j ⊗ₜ[R] b i) = (x * f i) ⊗ₜ[R] b i := by
      intro i
      simp_rw [Finsupp.sum, TensorProduct.smul_tmul', ← TensorProduct.sum_tmul]
      congr 1
      exact b.linearCombination_repr _
    rw [Finsupp.onFinset_sum, Finsupp.onFinset_sum]
    · trans (x ⊗ₜ 1) * elem R S
      · simp_rw [this, hf, Finsupp.sum, Finset.mul_sum, TensorProduct.tmul_mul_tmul, one_mul]
      · rw [← one_tmul_mul_elem, hf, finite_of_free_aux]
        rfl
    · intro; simp
    · intro; simp
  -- In particular, `fⱼx = ∑ Fᵢⱼbⱼ = ∑ Gᵢⱼbⱼ = ∑ₛ aᵢⱼfᵢ` for all `j`.
  have : ∀ j, x * f j = f.sum fun i y ↦ a i j • y := by
    intro j
    apply b.repr.injective
    exact DFunLike.congr_fun this j
  -- Since `∑ₛ fⱼbⱼ = 1`, `x = ∑ₛ aᵢⱼfᵢbⱼ` is indeed in the span of `{ fᵢbⱼ | i, j ∈ s }`.
  rw [← mul_one x, ← @lmul_elem R, hf, map_finsuppSum, Finsupp.sum, Finset.mul_sum]
  simp only [TensorProduct.lmul'_apply_tmul, Finset.coe_image₂, ← mul_assoc, this,
    Finsupp.sum, Finset.sum_mul, smul_mul_assoc]
  apply Submodule.sum_mem; intro i hi
  apply Submodule.sum_mem; intro j hj
  apply Submodule.smul_mem
  apply Submodule.subset_span
  use j, hj, i, hi

/--
Proposition I.2.3 of [iversen]
If `S` is an unramified `R`-algebra, and `M` is a `S`-module, then the map
`S ⊗[R] M →ₗ[S] M` taking `(b, m) ↦ b • m` admits a `S`-linear section. -/
noncomputable
def sec :
    M →ₗ[S] S ⊗[R] M where
  __ := ((TensorProduct.AlgebraTensorModule.mapBilinear R S S S S S M
    LinearMap.id).flip (elem R S)).comp (lsmul R R M).toLinearMap.flip
  map_smul' r m := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.flip_apply, TensorProduct.AlgebraTensorModule.mapBilinear_apply, RingHom.id_apply]
    trans (TensorProduct.AlgebraTensorModule.map (LinearMap.id (R := S) (M := S))
      ((LinearMap.flip (AlgHom.toLinearMap (lsmul R R M))) m)) ((1 ⊗ₜ r) * elem R S)
    · induction elem R S using TensorProduct.induction_on
      · simp
      · simp [smul_comm r]
      · simp only [map_add, mul_add, *]
    · have := one_tmul_sub_tmul_one_mul_elem (R := R) r
      rw [sub_mul, sub_eq_zero] at this
      rw [this]
      induction elem R S using TensorProduct.induction_on
      · simp
      · simp [TensorProduct.smul_tmul']
      · simp only [map_add, smul_add, mul_add, *]

lemma comp_sec :
    (TensorProduct.AlgebraTensorModule.lift
      ((lsmul S S M).toLinearMap.flip.restrictScalars R).flip).comp (sec R S M) =
      LinearMap.id := by
  ext x
  simp only [sec, LinearMap.coe_comp, LinearMap.coe_mk, LinearMap.coe_toAddHom,
    Function.comp_apply, LinearMap.flip_apply, TensorProduct.AlgebraTensorModule.mapBilinear_apply,
    TensorProduct.AlgebraTensorModule.lift_apply, LinearMap.id_coe, id_eq]
  trans (TensorProduct.lmul' R (elem R S)) • x
  · induction elem R S using TensorProduct.induction_on with
    | zero => simp
    | tmul r s => simp [mul_smul, smul_comm r s]
    | add y z hy hz => simp [hy, hz, add_smul]
  · rw [lmul_elem, one_smul]

/-- If `S` is an unramified `R`-algebra, then `R`-flat implies `S`-flat. Iversen I.2.7 -/
lemma flat_of_restrictScalars [Module.Flat R M] : Module.Flat S M :=
  Module.Flat.of_retract _ _ (comp_sec R S M)

/-- If `S` is an unramified `R`-algebra, then `R`-projective implies `S`-projective. -/
lemma projective_of_restrictScalars [Module.Projective R M] : Module.Projective S M :=
  Module.Projective.of_split _ _ (comp_sec R S M)

end Algebra.FormallyUnramified
