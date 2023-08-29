/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Best, Riccardo Brasca, Eric Rodriguez
-/
import Mathlib.Data.PNat.Prime
import Mathlib.Algebra.IsPrimePow
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Norm
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand

#align_import number_theory.cyclotomic.primitive_roots from "leanprover-community/mathlib"@"5bfbcca0a7ffdd21cf1682e59106d6c942434a32"

/-!
# Primitive roots in cyclotomic fields
If `IsCyclotomicExtension {n} A B`, we define an element `zeta n A B : B` that is a primitive
`n`th-root of unity in `B` and we study its properties. We also prove related theorems under the
more general assumption of just being a primitive root, for reasons described in the implementation
details section.

## Main definitions
* `IsCyclotomicExtension.zeta n A B`: if `IsCyclotomicExtension {n} A B`, than `zeta n A B`
  is a primitive `n`-th root of unity in `B`.
* `IsPrimitiveRoot.powerBasis`: if `K` and `L` are fields such that
  `IsCyclotomicExtension {n} K L`, then `IsPrimitiveRoot.powerBasis`
  gives a `K`-power basis for `L` given a primitive root `ζ`.
* `IsPrimitiveRoot.embeddingsEquivPrimitiveRoots`: the equivalence between `L →ₐ[K] A`
  and `primitiveroots n A` given by the choice of `ζ`.

## Main results
* `IsCyclotomicExtension.zeta_spec`: `zeta n A B` is a primitive `n`-th root of unity.
* `IsCyclotomicExtension.finrank`: if `Irreducible (cyclotomic n K)` (in particular for
  `K = ℚ`), then the `finrank` of a cyclotomic extension is `n.totient`.
* `IsPrimitiveRoot.norm_eq_one`: if `Irreducible (cyclotomic n K)` (in particular for `K = ℚ`),
  the norm of a primitive root is `1` if `n ≠ 2`.
* `IsPrimitiveRoot.sub_one_norm_eq_eval_cyclotomic`: if `Irreducible (cyclotomic n K)`
  (in particular for `K = ℚ`), then the norm of `ζ - 1` is `eval 1 (cyclotomic n ℤ)`, for a
  primitive root `ζ`. We also prove the analogous of this result for `zeta`.
* `IsPrimitiveRoot.pow_sub_one_norm_prime_pow_ne_two` : if
  `Irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is a prime,
  then the norm of `ζ ^ (p ^ s) - 1` is `p ^ (p ^ s)` `p ^ (k - s + 1) ≠ 2`. See the following
  lemmas for similar results. We also prove the analogous of this result for `zeta`.
* `IsPrimitiveRoot.sub_one_norm_prime_ne_two` : if `Irreducible (cyclotomic (p ^ (k + 1)) K)`
  (in particular for `K = ℚ`) and `p` is an odd prime, then the norm of `ζ - 1` is `p`. We also
  prove the analogous of this result for `zeta`.
* `IsPrimitiveRoot.embeddingsEquivPrimitiveRoots`: the equivalence between `L →ₐ[K] A`
  and `primitiveRoots n A` given by the choice of `ζ`.

## Implementation details
`zeta n A B` is defined as any primitive root of unity in `B`, - this must exist, by definition of
`IsCyclotomicExtension`. It is not true in general that it is a root of `cyclotomic n B`,
but this holds if `isDomain B` and `NeZero (↑n : B)`.

`zeta n A B` is defined using `Exists.choose`, which means we cannot control it.
For example, in normal mathematics, we can demand that `(zeta p ℤ ℤ[ζₚ] : ℚ(ζₚ))` is equal to
`zeta p ℚ ℚ(ζₚ)`, as we are just choosing "an arbitrary primitive root" and we can internally
specify that our choices agree. This is not the case here, and it is indeed impossible to prove that
these two are equal. Therefore, whenever possible, we prove our results for any primitive root,
and only at the "final step", when we need to provide an "explicit" primitive root, we use `zeta`.

-/


open Polynomial Algebra Finset FiniteDimensional IsCyclotomicExtension Nat PNat Set

universe u v w z

variable {p n : ℕ+} (A : Type w) (B : Type z) (K : Type u) {L : Type v} (C : Type w)

variable [CommRing A] [CommRing B] [Algebra A B] [IsCyclotomicExtension {n} A B]

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220
section Zeta

namespace IsCyclotomicExtension

variable (n)

/-- If `B` is an `n`-th cyclotomic extension of `A`, then `zeta n A B` is a primitive root of
unity in `B`. -/
noncomputable def zeta : B :=
  (exists_prim_root A <| Set.mem_singleton n : ∃ r : B, IsPrimitiveRoot r n).choose
#align is_cyclotomic_extension.zeta IsCyclotomicExtension.zeta

/-- `zeta n A B` is a primitive `n`-th root of unity. -/
@[simp]
theorem zeta_spec : IsPrimitiveRoot (zeta n A B) n :=
  Classical.choose_spec (exists_prim_root A (Set.mem_singleton n) : ∃ r : B, IsPrimitiveRoot r n)
#align is_cyclotomic_extension.zeta_spec IsCyclotomicExtension.zeta_spec

theorem aeval_zeta [IsDomain B] [NeZero ((n : ℕ) : B)] :
    aeval (zeta n A B) (cyclotomic n A) = 0 := by
  rw [aeval_def, ← eval_map, ← IsRoot.def, map_cyclotomic, isRoot_cyclotomic_iff]
  -- ⊢ IsPrimitiveRoot (zeta n A B) ↑n
  exact zeta_spec n A B
  -- 🎉 no goals
#align is_cyclotomic_extension.aeval_zeta IsCyclotomicExtension.aeval_zeta

theorem zeta_isRoot [IsDomain B] [NeZero ((n : ℕ) : B)] : IsRoot (cyclotomic n B) (zeta n A B) := by
  convert aeval_zeta n A B using 0
  -- ⊢ IsRoot (cyclotomic (↑n) B) (zeta n A B) ↔ ↑(aeval (zeta n A B)) (cyclotomic  …
  rw [IsRoot.def, aeval_def, eval₂_eq_eval_map, map_cyclotomic]
  -- 🎉 no goals
#align is_cyclotomic_extension.zeta_is_root IsCyclotomicExtension.zeta_isRoot

theorem zeta_pow : zeta n A B ^ (n : ℕ) = 1 :=
  (zeta_spec n A B).pow_eq_one
#align is_cyclotomic_extension.zeta_pow IsCyclotomicExtension.zeta_pow

end IsCyclotomicExtension

end Zeta

section NoOrder

variable [Field K] [CommRing L] [IsDomain L] [Algebra K L] [IsCyclotomicExtension {n} K L] {ζ : L}
  (hζ : IsPrimitiveRoot ζ n)

namespace IsPrimitiveRoot

variable {C}

/-- The `PowerBasis` given by a primitive root `η`. -/
@[simps!]
protected noncomputable def powerBasis : PowerBasis K L :=
  PowerBasis.map (Algebra.adjoin.powerBasis <| integral {n} K L ζ) <|
    (Subalgebra.equivOfEq _ _ (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ)).trans
      Subalgebra.topEquiv
#align is_primitive_root.power_basis IsPrimitiveRoot.powerBasis

theorem powerBasis_gen_mem_adjoin_zeta_sub_one :
    (hζ.powerBasis K).gen ∈ adjoin K ({ζ - 1} : Set L) := by
  rw [powerBasis_gen, adjoin_singleton_eq_range_aeval, AlgHom.mem_range]
  -- ⊢ ∃ x, ↑(aeval (ζ - 1)) x = ζ
  exact ⟨X + 1, by simp⟩
  -- 🎉 no goals
#align is_primitive_root.power_basis_gen_mem_adjoin_zeta_sub_one IsPrimitiveRoot.powerBasis_gen_mem_adjoin_zeta_sub_one

/-- The `PowerBasis` given by `η - 1`. -/
@[simps!]
noncomputable def subOnePowerBasis : PowerBasis K L :=
  (hζ.powerBasis K).ofGenMemAdjoin
    (isIntegral_sub (IsCyclotomicExtension.integral {n} K L ζ) isIntegral_one)
    (hζ.powerBasis_gen_mem_adjoin_zeta_sub_one _)
#align is_primitive_root.sub_one_power_basis IsPrimitiveRoot.subOnePowerBasis

variable {K} (C)

-- We are not using @[simps] to avoid a timeout.
/-- The equivalence between `L →ₐ[K] C` and `primitiveRoots n C` given by a primitive root `ζ`. -/
noncomputable def embeddingsEquivPrimitiveRoots (C : Type*) [CommRing C] [IsDomain C] [Algebra K C]
    (hirr : Irreducible (cyclotomic n K)) : (L →ₐ[K] C) ≃ primitiveRoots n C :=
  (hζ.powerBasis K).liftEquiv.trans
    { toFun := fun x => by
        haveI := IsCyclotomicExtension.neZero' n K L
        -- ⊢ { x // x ∈ primitiveRoots (↑n) C }
        haveI hn := NeZero.of_noZeroSMulDivisors K C n
        -- ⊢ { x // x ∈ primitiveRoots (↑n) C }
        refine' ⟨x.1, _⟩
        -- ⊢ ↑x ∈ primitiveRoots (↑n) C
        cases x
        -- ⊢ ↑{ val := val✝, property := property✝ } ∈ primitiveRoots (↑n) C
        rwa [mem_primitiveRoots n.pos, ← isRoot_cyclotomic_iff, IsRoot.def, ←
          map_cyclotomic _ (algebraMap K C), hζ.minpoly_eq_cyclotomic_of_irreducible hirr, ←
          eval₂_eq_eval_map, ← aeval_def]
      invFun := fun x => by
        haveI := IsCyclotomicExtension.neZero' n K L
        -- ⊢ { y // ↑(aeval y) (minpoly K (IsPrimitiveRoot.powerBasis K hζ).gen) = 0 }
        haveI hn := NeZero.of_noZeroSMulDivisors K C n
        -- ⊢ { y // ↑(aeval y) (minpoly K (IsPrimitiveRoot.powerBasis K hζ).gen) = 0 }
        refine' ⟨x.1, _⟩
        -- ⊢ ↑(aeval ↑x) (minpoly K (IsPrimitiveRoot.powerBasis K hζ).gen) = 0
        cases x
        -- ⊢ ↑(aeval ↑{ val := val✝, property := property✝ }) (minpoly K (IsPrimitiveRoot …
        rwa [aeval_def, eval₂_eq_eval_map, hζ.powerBasis_gen K, ←
          hζ.minpoly_eq_cyclotomic_of_irreducible hirr, map_cyclotomic, ← IsRoot.def,
          isRoot_cyclotomic_iff, ← mem_primitiveRoots n.pos]
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl }
#align is_primitive_root.embeddings_equiv_primitive_roots IsPrimitiveRoot.embeddingsEquivPrimitiveRoots

-- Porting note: renamed argument `φ`: "expected '_' or identifier"
@[simp]
theorem embeddingsEquivPrimitiveRoots_apply_coe (C : Type*) [CommRing C] [IsDomain C] [Algebra K C]
    (hirr : Irreducible (cyclotomic n K)) (φ' : L →ₐ[K] C) :
    (hζ.embeddingsEquivPrimitiveRoots C hirr φ' : C) = φ' ζ :=
  rfl
#align is_primitive_root.embeddings_equiv_primitive_roots_apply_coe IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe

end IsPrimitiveRoot

namespace IsCyclotomicExtension

variable {K} (L)

/-- If `Irreducible (cyclotomic n K)` (in particular for `K = ℚ`), then the `finrank` of a
cyclotomic extension is `n.totient`. -/
theorem finrank (hirr : Irreducible (cyclotomic n K)) : finrank K L = (n : ℕ).totient := by
  haveI := IsCyclotomicExtension.neZero' n K L
  -- ⊢ FiniteDimensional.finrank K L = φ ↑n
  rw [((zeta_spec n K L).powerBasis K).finrank, IsPrimitiveRoot.powerBasis_dim, ←
    (zeta_spec n K L).minpoly_eq_cyclotomic_of_irreducible hirr, natDegree_cyclotomic]
#align is_cyclotomic_extension.finrank IsCyclotomicExtension.finrank

end IsCyclotomicExtension

end NoOrder

section Norm

namespace IsPrimitiveRoot

section CommRing

variable [CommRing L] {ζ : L} (hζ : IsPrimitiveRoot ζ n)

variable {K} [Field K] [Algebra K L]

/-- This mathematically trivial result is complementary to `norm_eq_one` below. -/
theorem norm_eq_neg_one_pow (hζ : IsPrimitiveRoot ζ 2) [IsDomain L] :
    norm K ζ = (-1 : K) ^ finrank K L := by
  rw [hζ.eq_neg_one_of_two_right, show -1 = algebraMap K L (-1) by simp, Algebra.norm_algebraMap]
  -- 🎉 no goals
#align is_primitive_root.norm_eq_neg_one_pow IsPrimitiveRoot.norm_eq_neg_one_pow

/-- If `Irreducible (cyclotomic n K)` (in particular for `K = ℚ`), the norm of a primitive root is
`1` if `n ≠ 2`. -/
theorem norm_eq_one [IsDomain L] [IsCyclotomicExtension {n} K L] (hn : n ≠ 2)
    (hirr : Irreducible (cyclotomic n K)) : norm K ζ = 1 := by
  haveI := IsCyclotomicExtension.neZero' n K L
  -- ⊢ ↑(Algebra.norm K) ζ = 1
  by_cases h1 : n = 1
  -- ⊢ ↑(Algebra.norm K) ζ = 1
  · rw [h1, one_coe, one_right_iff] at hζ
    -- ⊢ ↑(Algebra.norm K) ζ = 1
    rw [hζ, show 1 = algebraMap K L 1 by simp, Algebra.norm_algebraMap, one_pow]
    -- 🎉 no goals
  · replace h1 : 2 ≤ n
    -- ⊢ 2 ≤ n
    · by_contra' h
      -- ⊢ False
      exact h1 (PNat.eq_one_of_lt_two h)
      -- 🎉 no goals
-- Porting note: specyfing the type of `cyclotomic_coeff_zero K h1` was not needed.
    rw [← hζ.powerBasis_gen K, PowerBasis.norm_gen_eq_coeff_zero_minpoly, hζ.powerBasis_gen K, ←
      hζ.minpoly_eq_cyclotomic_of_irreducible hirr,
      (cyclotomic_coeff_zero K h1 : coeff (cyclotomic n K) 0 = 1), mul_one,
      hζ.powerBasis_dim K, ← hζ.minpoly_eq_cyclotomic_of_irreducible hirr, natDegree_cyclotomic]
    exact (totient_even <| h1.lt_of_ne hn.symm).neg_one_pow
    -- 🎉 no goals
#align is_primitive_root.norm_eq_one IsPrimitiveRoot.norm_eq_one

/-- If `K` is linearly ordered, the norm of a primitive root is `1` if `n` is odd. -/
theorem norm_eq_one_of_linearly_ordered {K : Type*} [LinearOrderedField K] [Algebra K L]
    (hodd : Odd (n : ℕ)) : norm K ζ = 1 := by
  have hz := congr_arg (norm K) ((IsPrimitiveRoot.iff_def _ n).1 hζ).1
  -- ⊢ ↑(Algebra.norm K) ζ = 1
  rw [← (algebraMap K L).map_one, Algebra.norm_algebraMap, one_pow, map_pow, ← one_pow ↑n] at hz
  -- ⊢ ↑(Algebra.norm K) ζ = 1
  exact StrictMono.injective hodd.strictMono_pow hz
  -- 🎉 no goals
#align is_primitive_root.norm_eq_one_of_linearly_ordered IsPrimitiveRoot.norm_eq_one_of_linearly_ordered

theorem norm_of_cyclotomic_irreducible [IsDomain L] [IsCyclotomicExtension {n} K L]
    (hirr : Irreducible (cyclotomic n K)) : norm K ζ = ite (n = 2) (-1) 1 := by
  split_ifs with hn
  -- ⊢ ↑(Algebra.norm K) ζ = -1
  · subst hn
    -- ⊢ ↑(Algebra.norm K) ζ = -1
    convert norm_eq_neg_one_pow (K := K) hζ
    -- ⊢ -1 = (-1) ^ FiniteDimensional.finrank K L
    erw [IsCyclotomicExtension.finrank _ hirr, totient_two, pow_one]
    -- 🎉 no goals
  · exact hζ.norm_eq_one hn hirr
    -- 🎉 no goals
#align is_primitive_root.norm_of_cyclotomic_irreducible IsPrimitiveRoot.norm_of_cyclotomic_irreducible

end CommRing

section Field

variable [Field L] {ζ : L} (hζ : IsPrimitiveRoot ζ n)

variable {K} [Field K] [Algebra K L]

/-- If `Irreducible (cyclotomic n K)` (in particular for `K = ℚ`), then the norm of
`ζ - 1` is `eval 1 (cyclotomic n ℤ)`. -/
theorem sub_one_norm_eq_eval_cyclotomic [IsCyclotomicExtension {n} K L] (h : 2 < (n : ℕ))
    (hirr : Irreducible (cyclotomic n K)) : norm K (ζ - 1) = ↑(eval 1 (cyclotomic n ℤ)) := by
  haveI := IsCyclotomicExtension.neZero' n K L
  -- ⊢ ↑(Algebra.norm K) (ζ - 1) = ↑(eval 1 (cyclotomic ↑n ℤ))
  let E := AlgebraicClosure L
  -- ⊢ ↑(Algebra.norm K) (ζ - 1) = ↑(eval 1 (cyclotomic ↑n ℤ))
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ (degree_cyclotomic_pos n E n.pos).ne.symm
  -- ⊢ ↑(Algebra.norm K) (ζ - 1) = ↑(eval 1 (cyclotomic ↑n ℤ))
  apply (algebraMap K E).injective
  -- ⊢ ↑(algebraMap K E) (↑(Algebra.norm K) (ζ - 1)) = ↑(algebraMap K E) ↑(eval 1 ( …
  letI := IsCyclotomicExtension.finiteDimensional {n} K L
  -- ⊢ ↑(algebraMap K E) (↑(Algebra.norm K) (ζ - 1)) = ↑(algebraMap K E) ↑(eval 1 ( …
  letI := IsCyclotomicExtension.isGalois n K L
  -- ⊢ ↑(algebraMap K E) (↑(Algebra.norm K) (ζ - 1)) = ↑(algebraMap K E) ↑(eval 1 ( …
  rw [norm_eq_prod_embeddings]
  -- ⊢ (Finset.prod Finset.univ fun σ => ↑σ (ζ - 1)) = ↑(algebraMap K E) ↑(eval 1 ( …
  conv_lhs =>
    congr
    rfl
    ext
    rw [← neg_sub, AlgHom.map_neg, AlgHom.map_sub, AlgHom.map_one, neg_eq_neg_one_mul]
  rw [prod_mul_distrib, prod_const, card_univ, AlgHom.card, IsCyclotomicExtension.finrank L hirr,
    (totient_even h).neg_one_pow, one_mul]
  have Hprod : (Finset.univ.prod fun σ : L →ₐ[K] E => 1 - σ ζ) = eval 1 (cyclotomic' n E) := by
    rw [cyclotomic', eval_prod, ← @Finset.prod_attach E E, ← univ_eq_attach]
    refine' Fintype.prod_equiv (hζ.embeddingsEquivPrimitiveRoots E hirr) _ _ fun σ => _
    simp
  haveI : NeZero ((n : ℕ) : E) := NeZero.of_noZeroSMulDivisors K _ (n : ℕ)
  -- ⊢ (Finset.prod Finset.univ fun x => 1 - ↑x ζ) = ↑(algebraMap K E) ↑(eval 1 (cy …
  rw [Hprod, cyclotomic', ← cyclotomic_eq_prod_X_sub_primitiveRoots (isRoot_cyclotomic_iff.1 hz),
    ← map_cyclotomic_int, _root_.map_intCast, ← Int.cast_one, eval_int_cast_map, eq_intCast,
    Int.cast_id]
#align is_primitive_root.sub_one_norm_eq_eval_cyclotomic IsPrimitiveRoot.sub_one_norm_eq_eval_cyclotomic

/-- If `IsPrimePow (n : ℕ)`, `n ≠ 2` and `Irreducible (cyclotomic n K)` (in particular for
`K = ℚ`), then the norm of `ζ - 1` is `(n : ℕ).minFac`. -/
theorem sub_one_norm_isPrimePow (hn : IsPrimePow (n : ℕ)) [IsCyclotomicExtension {n} K L]
    (hirr : Irreducible (cyclotomic (n : ℕ) K)) (h : n ≠ 2) : norm K (ζ - 1) = (n : ℕ).minFac := by
  have :=
    (coe_lt_coe 2 _).1
      (lt_of_le_of_ne (succ_le_of_lt (IsPrimePow.one_lt hn))
        (Function.Injective.ne PNat.coe_injective h).symm)
  letI hprime : Fact (n : ℕ).minFac.Prime := ⟨minFac_prime (IsPrimePow.ne_one hn)⟩
  -- ⊢ ↑(Algebra.norm K) (ζ - 1) = ↑(minFac ↑n)
  rw [sub_one_norm_eq_eval_cyclotomic hζ this hirr]
  -- ⊢ ↑(eval 1 (cyclotomic ↑n ℤ)) = ↑(minFac ↑n)
  nth_rw 1 [← IsPrimePow.minFac_pow_factorization_eq hn]
  -- ⊢ ↑(eval 1 (cyclotomic (minFac ↑n ^ ↑(Nat.factorization ↑n) (minFac ↑n)) ℤ)) = …
  obtain ⟨k, hk⟩ : ∃ k, (n : ℕ).factorization (n : ℕ).minFac = k + 1 :=
    exists_eq_succ_of_ne_zero
      (((n : ℕ).factorization.mem_support_toFun (n : ℕ).minFac).1 <|
        factor_iff_mem_factorization.2 <|
          (mem_factors (IsPrimePow.ne_zero hn)).2 ⟨hprime.out, minFac_dvd _⟩)
  simp [hk, sub_one_norm_eq_eval_cyclotomic hζ this hirr]
  -- 🎉 no goals
#align is_primitive_root.sub_one_norm_is_prime_pow IsPrimitiveRoot.sub_one_norm_isPrimePow

variable {A}

theorem minpoly_sub_one_eq_cyclotomic_comp [Algebra K A] [IsDomain A] {ζ : A}
    [IsCyclotomicExtension {n} K A] (hζ : IsPrimitiveRoot ζ n)
    (h : Irreducible (Polynomial.cyclotomic n K)) :
    minpoly K (ζ - 1) = (cyclotomic n K).comp (X + 1) := by
  haveI := IsCyclotomicExtension.neZero' n K A
  -- ⊢ minpoly K (ζ - 1) = comp (cyclotomic (↑n) K) (X + 1)
  rw [show ζ - 1 = ζ + algebraMap K A (-1) by simp [sub_eq_add_neg],
    minpoly.add_algebraMap (IsCyclotomicExtension.integral {n} K A ζ),
    hζ.minpoly_eq_cyclotomic_of_irreducible h]
  simp
  -- 🎉 no goals
#align is_primitive_root.minpoly_sub_one_eq_cyclotomic_comp IsPrimitiveRoot.minpoly_sub_one_eq_cyclotomic_comp

open scoped Cyclotomic

/-- If `Irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is a prime,
then the norm of `ζ ^ (p ^ s) - 1` is `p ^ (p ^ s)` if `p ^ (k - s + 1) ≠ 2`. See the next lemmas
for similar results. -/
theorem pow_sub_one_norm_prime_pow_ne_two {k s : ℕ} (hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 1)))
    [hpri : Fact (p : ℕ).Prime] [IsCyclotomicExtension {p ^ (k + 1)} K L]
    (hirr : Irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K)) (hs : s ≤ k)
    (htwo : p ^ (k - s + 1) ≠ 2) : norm K (ζ ^ (p : ℕ) ^ s - 1) = (p : K) ^ (p : ℕ) ^ s := by
-- Porting note: `by simp` was `by linarith` that now fails.
  have hirr₁ : Irreducible (cyclotomic ((p : ℕ) ^ (k - s + 1)) K) :=
    cyclotomic_irreducible_pow_of_irreducible_pow hpri.1 (by simp) hirr
  rw [← PNat.pow_coe] at hirr₁
  -- ⊢ ↑(Algebra.norm K) (ζ ^ ↑p ^ s - 1) = ↑↑p ^ ↑p ^ s
  set η := ζ ^ (p : ℕ) ^ s - 1 with ηdef
  -- ⊢ ↑(Algebra.norm K) η = ↑↑p ^ ↑p ^ s
  let η₁ : K⟮η⟯ := IntermediateField.AdjoinSimple.gen K η
  -- ⊢ ↑(Algebra.norm K) η = ↑↑p ^ ↑p ^ s
  have hη : IsPrimitiveRoot (η + 1) ((p : ℕ) ^ (k + 1 - s)) := by
    rw [sub_add_cancel]
    refine' IsPrimitiveRoot.pow (p ^ (k + 1)).pos hζ _
    rw [PNat.pow_coe, ← pow_add, add_comm s, Nat.sub_add_cancel (le_trans hs (Nat.le_succ k))]
  have : IsCyclotomicExtension {p ^ (k - s + 1)} K K⟮η⟯ := by
    suffices IsCyclotomicExtension {p ^ (k - s + 1)} K K⟮η + 1⟯.toSubalgebra by
      have H : K⟮η + 1⟯.toSubalgebra = K⟮η⟯.toSubalgebra := by
        simp only [IntermediateField.adjoin_simple_toSubalgebra_of_integral
            (IsCyclotomicExtension.integral {p ^ (k + 1)} K L _)]
        refine' Subalgebra.ext fun x => ⟨fun hx => adjoin_le _ hx, fun hx => adjoin_le _ hx⟩
        · simp only [Set.singleton_subset_iff, SetLike.mem_coe]
          exact Subalgebra.add_mem _ (subset_adjoin (mem_singleton η)) (Subalgebra.one_mem _)
-- Porting note `ηdef` was not needed.
        · simp only [Set.singleton_subset_iff, SetLike.mem_coe, ← ηdef]
          nth_rw 1 [← add_sub_cancel η 1]
          refine' Subalgebra.sub_mem _ (subset_adjoin (mem_singleton _)) (Subalgebra.one_mem _)
-- Porting note: the previous proof was `rw [H] at this; exact this` but it now fails.
      exact IsCyclotomicExtension.equiv _ _ _ (Subalgebra.equivOfEq _ _ H)
-- Porting note: the next `refine` was `rw [H]`, abusing defeq, and it now fails.
    have H := IntermediateField.adjoin_simple_toSubalgebra_of_integral
        (IsCyclotomicExtension.integral {p ^ (k + 1)} K L (η + 1))
    refine @IsCyclotomicExtension.equiv _ _ _ _ _ _ _ _ _ ?_ (Subalgebra.equivOfEq _ _ H).symm
    have hη' : IsPrimitiveRoot (η + 1) ↑(p ^ (k + 1 - s)) := by simpa using hη
-- Porting note: `using 1` was not needed.
    convert hη'.adjoin_isCyclotomicExtension K using 1
    rw [Nat.sub_add_comm hs]
  replace hη : IsPrimitiveRoot (η₁ + 1) ↑(p ^ (k - s + 1))
  -- ⊢ IsPrimitiveRoot (η₁ + 1) ↑(p ^ (k - s + 1))
  · apply coe_submonoidClass_iff.1
    -- ⊢ IsPrimitiveRoot ↑(η₁ + 1) ↑(p ^ (k - s + 1))
    convert hη using 1
    -- ⊢ ↑(p ^ (k - s + 1)) = ↑p ^ (k + 1 - s)
    rw [Nat.sub_add_comm hs, pow_coe]
    -- 🎉 no goals
-- Porting note: the following `haveI` were not needed because the locale `cyclotomic` set them
-- as instances.
  haveI := IsCyclotomicExtension.finiteDimensional {p ^ (k + 1)} K L
  -- ⊢ ↑(Algebra.norm K) η = ↑↑p ^ ↑p ^ s
  haveI := IsCyclotomicExtension.isGalois (p ^ (k + 1)) K L
  -- ⊢ ↑(Algebra.norm K) η = ↑↑p ^ ↑p ^ s
  rw [norm_eq_norm_adjoin K]
  -- ⊢ ↑(Algebra.norm K) (IntermediateField.AdjoinSimple.gen K η) ^ FiniteDimension …
  · have H := hη.sub_one_norm_isPrimePow ?_ hirr₁ htwo
    -- ⊢ ↑(Algebra.norm K) (IntermediateField.AdjoinSimple.gen K η) ^ FiniteDimension …
    swap; · rw [PNat.pow_coe]; exact hpri.1.isPrimePow.pow (Nat.succ_ne_zero _)
    -- ⊢ IsPrimePow ↑(p ^ (k - s + 1))
            -- ⊢ IsPrimePow (↑p ^ (k - s + 1))
                               -- 🎉 no goals
    rw [add_sub_cancel] at H
    -- ⊢ ↑(Algebra.norm K) (IntermediateField.AdjoinSimple.gen K η) ^ FiniteDimension …
    rw [H]
    -- ⊢ ↑(minFac ↑(p ^ (k - s + 1))) ^ FiniteDimensional.finrank { x // x ∈ K⟮η⟯ } L …
    congr
    -- ⊢ minFac ↑(p ^ (k - s + 1)) = ↑p
    · rw [PNat.pow_coe, Nat.pow_minFac, hpri.1.minFac_eq]
      -- ⊢ k - s + 1 ≠ 0
      exact Nat.succ_ne_zero _
      -- 🎉 no goals
    have := FiniteDimensional.finrank_mul_finrank K K⟮η⟯ L
    -- ⊢ FiniteDimensional.finrank { x // x ∈ K⟮η⟯ } L = ↑p ^ s
    rw [IsCyclotomicExtension.finrank L hirr, IsCyclotomicExtension.finrank K⟮η⟯ hirr₁,
      PNat.pow_coe, PNat.pow_coe, Nat.totient_prime_pow hpri.out (k - s).succ_pos,
      Nat.totient_prime_pow hpri.out k.succ_pos, mul_comm _ ((p : ℕ) - 1), mul_assoc,
      mul_comm ((p : ℕ) ^ (k.succ - 1))] at this
    replace this := mul_left_cancel₀ (tsub_pos_iff_lt.2 hpri.out.one_lt).ne' this
    -- ⊢ FiniteDimensional.finrank { x // x ∈ K⟮η⟯ } L = ↑p ^ s
    have Hex : k.succ - 1 = (k - s).succ - 1 + s := by
      simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
      exact (Nat.sub_add_cancel hs).symm
    rw [Hex, pow_add] at this
    -- ⊢ FiniteDimensional.finrank { x // x ∈ K⟮η⟯ } L = ↑p ^ s
    exact mul_left_cancel₀ (pow_ne_zero _ hpri.out.ne_zero) this
    -- 🎉 no goals
#align is_primitive_root.pow_sub_one_norm_prime_pow_ne_two IsPrimitiveRoot.pow_sub_one_norm_prime_pow_ne_two

/-- If `Irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is a prime,
then the norm of `ζ ^ (p ^ s) - 1` is `p ^ (p ^ s)` if `p ≠ 2`. -/
theorem pow_sub_one_norm_prime_ne_two {k : ℕ} (hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 1)))
    [hpri : Fact (p : ℕ).Prime] [IsCyclotomicExtension {p ^ (k + 1)} K L]
    (hirr : Irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K)) {s : ℕ} (hs : s ≤ k) (hodd : p ≠ 2) :
    norm K (ζ ^ (p : ℕ) ^ s - 1) = (p : K) ^ (p : ℕ) ^ s := by
  refine' hζ.pow_sub_one_norm_prime_pow_ne_two hirr hs fun h => _
  -- ⊢ False
  have coe_two : ((2 : ℕ+) : ℕ) = 2 := by norm_cast
  -- ⊢ False
  rw [← PNat.coe_inj, coe_two, PNat.pow_coe, ← pow_one 2] at h
  -- ⊢ False
-- Porting note: the proof is slightly different because of coercions.
  replace h :=
    eq_of_prime_pow_eq (prime_iff.1 hpri.out) (prime_iff.1 Nat.prime_two) (k - s).succ_pos h
  exact hodd (PNat.coe_injective h)
  -- 🎉 no goals

#align is_primitive_root.pow_sub_one_norm_prime_ne_two IsPrimitiveRoot.pow_sub_one_norm_prime_ne_two

/-- If `Irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is an odd
prime, then the norm of `ζ - 1` is `p`. -/
theorem sub_one_norm_prime_ne_two {k : ℕ} (hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 1)))
    [hpri : Fact (p : ℕ).Prime] [IsCyclotomicExtension {p ^ (k + 1)} K L]
    (hirr : Irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K)) (h : p ≠ 2) : norm K (ζ - 1) = p := by
  simpa using hζ.pow_sub_one_norm_prime_ne_two hirr k.zero_le h
  -- 🎉 no goals
#align is_primitive_root.sub_one_norm_prime_ne_two IsPrimitiveRoot.sub_one_norm_prime_ne_two

/-- If `Irreducible (cyclotomic p K)` (in particular for `K = ℚ`) and `p` is an odd prime,
then the norm of `ζ - 1` is `p`. -/
theorem sub_one_norm_prime [hpri : Fact (p : ℕ).Prime] [hcyc : IsCyclotomicExtension {p} K L]
    (hζ : IsPrimitiveRoot ζ p) (hirr : Irreducible (cyclotomic p K)) (h : p ≠ 2) :
    norm K (ζ - 1) = p := by
  replace hirr : Irreducible (cyclotomic (↑(p ^ (0 + 1)) : ℕ) K) := by simp [hirr]
  -- ⊢ ↑(Algebra.norm K) (ζ - 1) = ↑↑p
  replace hζ : IsPrimitiveRoot ζ (↑(p ^ (0 + 1)) : ℕ) := by simp [hζ]
  -- ⊢ ↑(Algebra.norm K) (ζ - 1) = ↑↑p
  haveI : IsCyclotomicExtension {p ^ (0 + 1)} K L := by simp [hcyc]
  -- ⊢ ↑(Algebra.norm K) (ζ - 1) = ↑↑p
  simpa using sub_one_norm_prime_ne_two hζ hirr h
  -- 🎉 no goals
#align is_primitive_root.sub_one_norm_prime IsPrimitiveRoot.sub_one_norm_prime

/-- If `Irreducible (cyclotomic (2 ^ (k + 1)) K)` (in particular for `K = ℚ`), then the norm of
`ζ ^ (2 ^ k) - 1` is `(-2) ^ (2 ^ k)`. -/
-- Porting note: writing `(2 : ℕ+)` was not needed (similarly everywhere).
theorem pow_sub_one_norm_two {k : ℕ} (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    [IsCyclotomicExtension {(2 : ℕ+) ^ (k + 1)} K L]
    (hirr : Irreducible (cyclotomic (2 ^ (k + 1)) K)) :
    norm K (ζ ^ 2 ^ k - 1) = (-2 : K) ^ 2 ^ k := by
  have := hζ.pow_of_dvd (fun h => two_ne_zero (pow_eq_zero h)) (pow_dvd_pow 2 (le_succ k))
  -- ⊢ ↑(Algebra.norm K) (ζ ^ 2 ^ k - 1) = (-2) ^ 2 ^ k
  rw [Nat.pow_div (le_succ k) zero_lt_two, Nat.succ_sub (le_refl k), Nat.sub_self, pow_one] at this
  -- ⊢ ↑(Algebra.norm K) (ζ ^ 2 ^ k - 1) = (-2) ^ 2 ^ k
  have H : (-1 : L) - (1 : L) = algebraMap K L (-2) := by
    simp only [map_neg, map_ofNat]
    ring
-- Porting note: `simpa using hirr` was `simp [hirr]`.
  replace hirr : Irreducible (cyclotomic ((2 : ℕ+) ^ (k + 1) : ℕ+) K) := by simpa using hirr
  -- ⊢ ↑(Algebra.norm K) (ζ ^ 2 ^ k - 1) = (-2) ^ 2 ^ k
-- Porting note: the proof is slightly different because of coercions.
  rw [this.eq_neg_one_of_two_right, H, Algebra.norm_algebraMap,
    IsCyclotomicExtension.finrank L hirr, pow_coe, show ((2 : ℕ+) : ℕ) = 2 from rfl,
      totient_prime_pow Nat.prime_two (zero_lt_succ k), succ_sub_succ_eq_sub, tsub_zero]
  simp
  -- 🎉 no goals
#align is_primitive_root.pow_sub_one_norm_two IsPrimitiveRoot.pow_sub_one_norm_two

/-- If `Irreducible (cyclotomic (2 ^ k) K)` (in particular for `K = ℚ`) and `k` is at least `2`,
then the norm of `ζ - 1` is `2`. -/
theorem sub_one_norm_two {k : ℕ} (hζ : IsPrimitiveRoot ζ (2 ^ k)) (hk : 2 ≤ k)
    [H : IsCyclotomicExtension {(2 : ℕ+) ^ k} K L] (hirr : Irreducible (cyclotomic (2 ^ k) K)) :
    norm K (ζ - 1) = 2 := by
  have : 2 < (2 : ℕ+) ^ k := by
    simp only [← coe_lt_coe, one_coe, pow_coe]
    nth_rw 1 [← pow_one 2]
    exact pow_lt_pow one_lt_two (lt_of_lt_of_le one_lt_two hk)
-- Porting note: `simpa using hirr` was `simp [hirr]`_
  replace hirr : Irreducible (cyclotomic ((2 : ℕ+) ^ k : ℕ+) K) := by simpa using hirr
  -- ⊢ ↑(Algebra.norm K) (ζ - 1) = 2
-- Porting note: `simpa using hζ` was `simp [hζ]`_
  replace hζ : IsPrimitiveRoot ζ ((2 : ℕ+) ^ k) := by simpa using hζ
  -- ⊢ ↑(Algebra.norm K) (ζ - 1) = 2
  obtain ⟨k₁, hk₁⟩ := exists_eq_succ_of_ne_zero (lt_of_lt_of_le zero_lt_two hk).ne.symm
  -- ⊢ ↑(Algebra.norm K) (ζ - 1) = 2
-- Porting note: the proof is slightly different because of coercions.
  simpa [hk₁, show ((2 : ℕ+) : ℕ) = 2 from rfl] using sub_one_norm_eq_eval_cyclotomic hζ this hirr
  -- 🎉 no goals
#align is_primitive_root.sub_one_norm_two IsPrimitiveRoot.sub_one_norm_two

/-- If `Irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is a prime,
then the norm of `ζ ^ (p ^ s) - 1` is `p ^ (p ^ s)` if `k ≠ 0` and `s ≤ k`. -/
theorem pow_sub_one_norm_prime_pow_of_ne_zero {k s : ℕ} (hζ : IsPrimitiveRoot ζ ↑(p ^ (k + 1)))
    [hpri : Fact (p : ℕ).Prime] [hcycl : IsCyclotomicExtension {p ^ (k + 1)} K L]
    (hirr : Irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K)) (hs : s ≤ k) (hk : k ≠ 0) :
    norm K (ζ ^ (p : ℕ) ^ s - 1) = (p : K) ^ (p : ℕ) ^ s := by
  by_cases htwo : p ^ (k - s + 1) = 2
  -- ⊢ ↑(Algebra.norm K) (ζ ^ ↑p ^ s - 1) = ↑↑p ^ ↑p ^ s
  · have hp : p = 2 := by
      rw [← PNat.coe_inj, PNat.pow_coe, ← pow_one 2] at htwo
      replace htwo :=
        eq_of_prime_pow_eq (prime_iff.1 hpri.out) (prime_iff.1 Nat.prime_two) (succ_pos _) htwo
      rwa [show 2 = ((2 : ℕ+) : ℕ) by simp, PNat.coe_inj] at htwo
    replace hs : s = k
    -- ⊢ s = k
    · rw [hp, ← PNat.coe_inj, PNat.pow_coe] at htwo
      -- ⊢ s = k
      nth_rw 2 [← pow_one 2] at htwo
      -- ⊢ s = k
      replace htwo := Nat.pow_right_injective rfl.le htwo
      -- ⊢ s = k
      rw [add_left_eq_self, Nat.sub_eq_zero_iff_le] at htwo
      -- ⊢ s = k
      refine' le_antisymm hs htwo
      -- 🎉 no goals
    simp only [hs, hp, one_coe, cast_one, pow_coe, show ((2 : ℕ+) : ℕ) = 2 from rfl]
      at hζ hirr hcycl ⊢
    obtain ⟨k₁, hk₁⟩ := Nat.exists_eq_succ_of_ne_zero hk
    -- ⊢ ↑(Algebra.norm K) (ζ ^ 2 ^ k - 1) = ↑2 ^ 2 ^ k
-- Porting note: the proof is slightly different because of coercions.
    rw [hζ.pow_sub_one_norm_two hirr, hk₁, _root_.pow_succ, pow_mul, neg_eq_neg_one_mul, mul_pow,
      neg_one_sq, one_mul, ← pow_mul, ← _root_.pow_succ]
    simp
    -- 🎉 no goals
  · exact hζ.pow_sub_one_norm_prime_pow_ne_two hirr hs htwo
    -- 🎉 no goals
#align is_primitive_root.pow_sub_one_norm_prime_pow_of_ne_zero IsPrimitiveRoot.pow_sub_one_norm_prime_pow_of_ne_zero

end Field

end IsPrimitiveRoot

namespace IsCyclotomicExtension

open IsPrimitiveRoot

variable {K} (L) [Field K] [Field L] [Algebra K L]

/-- If `Irreducible (cyclotomic n K)` (in particular for `K = ℚ`), the norm of `zeta n K L` is `1`
if `n` is odd. -/
theorem norm_zeta_eq_one [IsCyclotomicExtension {n} K L] (hn : n ≠ 2)
    (hirr : Irreducible (cyclotomic n K)) : norm K (zeta n K L) = 1 :=
  (zeta_spec n K L).norm_eq_one hn hirr
#align is_cyclotomic_extension.norm_zeta_eq_one IsCyclotomicExtension.norm_zeta_eq_one

/-- If `IsPrimePow (n : ℕ)`, `n ≠ 2` and `Irreducible (cyclotomic n K)` (in particular for
`K = ℚ`), then the norm of `zeta n K L - 1` is `(n : ℕ).minFac`. -/
theorem isPrimePow_norm_zeta_sub_one (hn : IsPrimePow (n : ℕ)) [IsCyclotomicExtension {n} K L]
    (hirr : Irreducible (cyclotomic (n : ℕ) K)) (h : n ≠ 2) :
    norm K (zeta n K L - 1) = (n : ℕ).minFac :=
  (zeta_spec n K L).sub_one_norm_isPrimePow hn hirr h
#align is_cyclotomic_extension.is_prime_pow_norm_zeta_sub_one IsCyclotomicExtension.isPrimePow_norm_zeta_sub_one

/-- If `Irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is a prime,
then the norm of `(zeta (p ^ (k + 1)) K L) ^ (p ^ s) - 1` is `p ^ (p ^ s)`
if `p ^ (k - s + 1) ≠ 2`. -/
theorem prime_ne_two_pow_norm_zeta_pow_sub_one {k : ℕ} [Fact (p : ℕ).Prime]
    [IsCyclotomicExtension {p ^ (k + 1)} K L]
    (hirr : Irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K)) {s : ℕ} (hs : s ≤ k)
    (htwo : p ^ (k - s + 1) ≠ 2) :
    norm K (zeta (p ^ (k + 1)) K L ^ (p : ℕ) ^ s - 1) = (p : K) ^ (p : ℕ) ^ s :=
  (zeta_spec _ K L).pow_sub_one_norm_prime_pow_ne_two hirr hs htwo
#align is_cyclotomic_extension.prime_ne_two_pow_norm_zeta_pow_sub_one IsCyclotomicExtension.prime_ne_two_pow_norm_zeta_pow_sub_one

/-- If `Irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is an odd
prime, then the norm of `zeta (p ^ (k + 1)) K L - 1` is `p`. -/
theorem prime_ne_two_pow_norm_zeta_sub_one {k : ℕ} [Fact (p : ℕ).Prime]
    [IsCyclotomicExtension {p ^ (k + 1)} K L]
    (hirr : Irreducible (cyclotomic (↑(p ^ (k + 1)) : ℕ) K)) (h : p ≠ 2) :
    norm K (zeta (p ^ (k + 1)) K L - 1) = p :=
  (zeta_spec _ K L).sub_one_norm_prime_ne_two hirr h
#align is_cyclotomic_extension.prime_ne_two_pow_norm_zeta_sub_one IsCyclotomicExtension.prime_ne_two_pow_norm_zeta_sub_one

/-- If `Irreducible (cyclotomic p K)` (in particular for `K = ℚ`) and `p` is an odd prime,
then the norm of `zeta p K L - 1` is `p`. -/
theorem prime_ne_two_norm_zeta_sub_one [Fact (p : ℕ).Prime]
    [IsCyclotomicExtension {p} K L] (hirr : Irreducible (cyclotomic p K)) (h : p ≠ 2) :
    norm K (zeta p K L - 1) = p :=
  (zeta_spec _ K L).sub_one_norm_prime hirr h
#align is_cyclotomic_extension.prime_ne_two_norm_zeta_sub_one IsCyclotomicExtension.prime_ne_two_norm_zeta_sub_one

/-- If `Irreducible (cyclotomic (2 ^ k) K)` (in particular for `K = ℚ`) and `k` is at least `2`,
then the norm of `zeta (2 ^ k) K L - 1` is `2`. -/
theorem two_pow_norm_zeta_sub_one {k : ℕ} (hk : 2 ≤ k) [IsCyclotomicExtension {(2 : ℕ+) ^ k} K L]
    (hirr : Irreducible (cyclotomic (2 ^ k) K)) : norm K (zeta ((2 : ℕ+) ^ k) K L - 1) = 2 :=
  sub_one_norm_two (zeta_spec ((2 : ℕ+) ^ k) K L) hk hirr
#align is_cyclotomic_extension.two_pow_norm_zeta_sub_one IsCyclotomicExtension.two_pow_norm_zeta_sub_one

end IsCyclotomicExtension

end Norm
