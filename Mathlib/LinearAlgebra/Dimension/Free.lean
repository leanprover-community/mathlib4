/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.AlgebraTower
import Mathlib.SetTheory.Cardinal.Finsupp

/-!
# Rank of free modules

## Main result
- `LinearEquiv.nonempty_equiv_iff_lift_rank_eq`:
  Two free modules are isomorphic iff they have the same dimension.
- `Module.finBasis`:
  An arbitrary basis of a finite free module indexed by `Fin n` given `finrank R M = n`.

-/


noncomputable section

universe u v v' w

open Cardinal Basis Submodule Function Set Module

section Tower

variable (F : Type u) (K : Type v) (A : Type w)
variable [Semiring F] [Semiring K] [AddCommMonoid A]
variable [Module F K] [Module K A] [Module F A] [IsScalarTower F K A]
variable [StrongRankCondition F] [StrongRankCondition K] [Module.Free F K] [Module.Free K A]

/-- Tower law: if `A` is a `K`-module and `K` is an extension of `F` then
$\operatorname{rank}_F(A) = \operatorname{rank}_F(K) * \operatorname{rank}_K(A)$.

The universe polymorphic version of `rank_mul_rank` below. -/
theorem lift_rank_mul_lift_rank :
    Cardinal.lift.{w} (Module.rank F K) * Cardinal.lift.{v} (Module.rank K A) =
      Cardinal.lift.{v} (Module.rank F A) := by
  let b := Module.Free.chooseBasis F K
  let c := Module.Free.chooseBasis K A
  rw [← (Module.rank F K).lift_id, ← b.mk_eq_rank, ← (Module.rank K A).lift_id, ← c.mk_eq_rank,
    ← lift_umax.{w, v}, ← (b.smulTower c).mk_eq_rank, mk_prod, lift_mul, lift_lift, lift_lift,
    lift_lift, lift_lift, lift_umax.{v, w}]

/-- Tower law: if `A` is a `K`-module and `K` is an extension of `F` then
$\operatorname{rank}_F(A) = \operatorname{rank}_F(K) * \operatorname{rank}_K(A)$.

This is a simpler version of `lift_rank_mul_lift_rank` with `K` and `A` in the same universe. -/
@[stacks 09G9]
theorem rank_mul_rank (A : Type v) [AddCommMonoid A]
    [Module K A] [Module F A] [IsScalarTower F K A] [Module.Free K A] :
    Module.rank F K * Module.rank K A = Module.rank F A := by
  convert lift_rank_mul_lift_rank F K A <;> rw [lift_id]

/-- Tower law: if `A` is a `K`-module and `K` is an extension of `F` then
$\operatorname{rank}_F(A) = \operatorname{rank}_F(K) * \operatorname{rank}_K(A)$. -/
theorem Module.finrank_mul_finrank : finrank F K * finrank K A = finrank F A := by
  simp_rw [finrank]
  rw [← toNat_lift.{w} (Module.rank F K), ← toNat_lift.{v} (Module.rank K A), ← toNat_mul,
    lift_rank_mul_lift_rank, toNat_lift]

end Tower

variable {R : Type u} {S : Type*} {M M₁ : Type v} {M' : Type v'}
variable [Semiring R] [StrongRankCondition R]
variable [AddCommMonoid M] [Module R M] [Module.Free R M]
variable [AddCommMonoid M'] [Module R M'] [Module.Free R M']
variable [AddCommMonoid M₁] [Module R M₁] [Module.Free R M₁]

namespace Module.Free

variable (R M)

/-- The rank of a free module `M` over `R` is the cardinality of `ChooseBasisIndex R M`. -/
theorem rank_eq_card_chooseBasisIndex : Module.rank R M = #(ChooseBasisIndex R M) :=
  (chooseBasis R M).mk_eq_rank''.symm

/-- The `finrank` of a free module `M` over `R` is the cardinality of `ChooseBasisIndex R M`. -/
theorem _root_.Module.finrank_eq_card_chooseBasisIndex [Module.Finite R M] :
    finrank R M = Fintype.card (ChooseBasisIndex R M) := by
  simp [finrank, rank_eq_card_chooseBasisIndex]

/-- The rank of a free module `M` over an infinite scalar ring `R` is the cardinality of `M`
whenever `#R < #M`. -/
lemma rank_eq_mk_of_infinite_lt [Infinite R] (h_lt : lift.{v} #R < lift.{u} #M) :
    Module.rank R M = #M := by
  have : Infinite M := infinite_iff.mpr <| lift_le.mp <| le_trans (by simp) h_lt.le
  have h : lift #M = lift #(ChooseBasisIndex R M →₀ R) := lift_mk_eq'.mpr ⟨(chooseBasis R M).repr⟩
  simp only [mk_finsupp_lift_of_infinite', ← rank_eq_card_chooseBasisIndex, lift_max,
    lift_lift] at h
  refine lift_inj.mp ((max_eq_iff.mp h.symm).resolve_right <| not_and_of_not_left _ ?_).left
  exact (lift_umax.{v, u}.symm ▸ h_lt).ne

end Module.Free

open Module.Free

open Cardinal

/-- Two vector spaces are isomorphic if they have the same dimension. -/
theorem nonempty_linearEquiv_of_lift_rank_eq
    (cnd : Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M')) :
    Nonempty (M ≃ₗ[R] M') := by
  obtain ⟨⟨α, B⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  obtain ⟨⟨β, B'⟩⟩ := Module.Free.exists_basis (R := R) (M := M')
  have : Cardinal.lift.{v', v} #α = Cardinal.lift.{v, v'} #β := by
    rw [B.mk_eq_rank'', cnd, B'.mk_eq_rank'']
  exact (Cardinal.lift_mk_eq.{v, v', 0}.1 this).map (B.equiv B')

/-- Two vector spaces are isomorphic if they have the same dimension. -/
theorem nonempty_linearEquiv_of_rank_eq (cond : Module.rank R M = Module.rank R M₁) :
    Nonempty (M ≃ₗ[R] M₁) :=
  nonempty_linearEquiv_of_lift_rank_eq <| congr_arg _ cond

section

variable (M M' M₁)

/-- Two vector spaces are isomorphic if they have the same dimension. -/
def LinearEquiv.ofLiftRankEq
    (cond : Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M')) :
    M ≃ₗ[R] M' :=
  Classical.choice (nonempty_linearEquiv_of_lift_rank_eq cond)

/-- Two vector spaces are isomorphic if they have the same dimension. -/
def LinearEquiv.ofRankEq (cond : Module.rank R M = Module.rank R M₁) : M ≃ₗ[R] M₁ :=
  Classical.choice (nonempty_linearEquiv_of_rank_eq cond)

end

/-- Two vector spaces are isomorphic if and only if they have the same dimension. -/
theorem LinearEquiv.nonempty_equiv_iff_lift_rank_eq : Nonempty (M ≃ₗ[R] M') ↔
    Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M') :=
  ⟨fun ⟨h⟩ => LinearEquiv.lift_rank_eq h, fun h => nonempty_linearEquiv_of_lift_rank_eq h⟩

/-- Two vector spaces are isomorphic if and only if they have the same dimension. -/
theorem LinearEquiv.nonempty_equiv_iff_rank_eq :
    Nonempty (M ≃ₗ[R] M₁) ↔ Module.rank R M = Module.rank R M₁ :=
  ⟨fun ⟨h⟩ => LinearEquiv.rank_eq h, fun h => nonempty_linearEquiv_of_rank_eq h⟩

/-- Two finite and free modules are isomorphic if they have the same (finite) rank. -/
theorem FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    [Module.Finite R M] [Module.Finite R M'] (cond : finrank R M = finrank R M') :
    Nonempty (M ≃ₗ[R] M') :=
  nonempty_linearEquiv_of_lift_rank_eq <| by simp only [← finrank_eq_rank, cond, lift_natCast]

/-- Two finite and free modules are isomorphic if and only if they have the same (finite) rank. -/
theorem FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq [Module.Finite R M]
    [Module.Finite R M'] : Nonempty (M ≃ₗ[R] M') ↔ finrank R M = finrank R M' :=
  ⟨fun ⟨h⟩ => h.finrank_eq, fun h => nonempty_linearEquiv_of_finrank_eq h⟩

variable (M M')

/-- Two finite and free modules are isomorphic if they have the same (finite) rank. -/
noncomputable def LinearEquiv.ofFinrankEq [Module.Finite R M] [Module.Finite R M']
    (cond : finrank R M = finrank R M') : M ≃ₗ[R] M' :=
  Classical.choice <| FiniteDimensional.nonempty_linearEquiv_of_finrank_eq cond

variable {M M'}

namespace Module

/-- A free module of rank zero is trivial. -/
lemma subsingleton_of_rank_zero (h : Module.rank R M = 0) : Subsingleton M := by
  rw [← Basis.mk_eq_rank'' (Module.Free.chooseBasis R M), Cardinal.mk_eq_zero_iff] at h
  exact (Module.Free.chooseBasis R M).repr.subsingleton

/-- See `rank_lt_aleph0` for the inverse direction without `Module.Free R M`. -/
lemma rank_lt_aleph0_iff : Module.rank R M < ℵ₀ ↔ Module.Finite R M := by
  rw [Free.rank_eq_card_chooseBasisIndex, mk_lt_aleph0_iff]
  exact ⟨fun h ↦ Finite.of_basis (Free.chooseBasis R M),
    fun I ↦ Finite.of_fintype (Free.ChooseBasisIndex R M)⟩

theorem finrank_of_not_finite (h : ¬Module.Finite R M) : finrank R M = 0 := by
  rw [finrank, toNat_eq_zero, ← not_lt, Module.rank_lt_aleph0_iff]
  exact .inr h

theorem finite_of_finrank_pos (h : 0 < finrank R M) : Module.Finite R M := by
  contrapose h
  simp [finrank_of_not_finite h]

theorem finite_of_finrank_eq_succ {n : ℕ} (hn : finrank R M = n.succ) : Module.Finite R M :=
  finite_of_finrank_pos <| by rw [hn]; exact n.succ_pos

theorem finite_iff_of_rank_eq_nsmul {W} [AddCommMonoid W] [Module R W] [Module.Free R W] {n : ℕ}
    (hn : n ≠ 0) (hVW : Module.rank R M = n • Module.rank R W) :
    Module.Finite R M ↔ Module.Finite R W := by
  simp only [← rank_lt_aleph0_iff, hVW, nsmul_lt_aleph0_iff_of_ne_zero hn]

variable (R S M) in
omit [Module.Free R M] in
/-- Also see `Module.finrank_top_le_finrank_of_isScalarTower`
for a version with different typeclass constraints. -/
lemma finrank_top_le_finrank_of_isScalarTower_of_free [Semiring S] [StrongRankCondition S]
    [Module S M] [Module R S] [FaithfulSMul R S] [Module.Finite R S]
    [IsScalarTower R S S] [IsScalarTower R S M] [Module.Free S M] :
    finrank S M ≤ finrank R M := by
  by_cases H : Module.Finite S M
  · have := Module.Finite.trans (R := R) S M
    exact finrank_top_le_finrank_of_isScalarTower R S M
  · rw [finrank, Cardinal.toNat_eq_zero.mpr (.inr _)]
    · exact zero_le _
    · rwa [← not_lt, Module.rank_lt_aleph0_iff]

variable (R) in
/-- Also see `Module.finrank_bot_le_finrank_of_isScalarTower`
for a version with different typeclass constraints. -/
lemma finrank_bot_le_finrank_of_isScalarTower_of_free (S T : Type*) [Semiring S] [Semiring T]
    [Module R T] [Module S T] [Module R S] [IsScalarTower R S T]
    [IsScalarTower S T T] [FaithfulSMul S T] [Module.Finite S T] [Module.Free R S] :
    finrank R S ≤ finrank R T := by
  by_cases H : Module.Finite R S
  · have := Module.Finite.trans (R := R) S T
    exact finrank_bot_le_finrank_of_isScalarTower R S T
  · rw [finrank, Cardinal.toNat_eq_zero.mpr (.inr _)]
    · exact zero_le _
    · rwa [← not_lt, Module.rank_lt_aleph0_iff]

variable (R M)

/-- A finite rank free module has a basis indexed by `Fin (finrank R M)`. -/
noncomputable def finBasis [Module.Finite R M] :
    Basis (Fin (finrank R M)) R M :=
  (Module.Free.chooseBasis R M).reindex (Fintype.equivFinOfCardEq
    (finrank_eq_card_chooseBasisIndex R M).symm)

/-- A rank `n` free module has a basis indexed by `Fin n`. -/
noncomputable def finBasisOfFinrankEq [Module.Finite R M] {n : ℕ} (hn : finrank R M = n) :
    Basis (Fin n) R M := (finBasis R M).reindex (finCongr hn)

variable {R M}

/-- A free module with rank 1 has a basis with one element. -/
noncomputable def basisUnique (ι : Type*) [Unique ι]
    (h : finrank R M = 1) :
    Basis ι R M :=
  haveI : Module.Finite R M :=
    Module.finite_of_finrank_pos (_root_.zero_lt_one.trans_le h.symm.le)
  (finBasisOfFinrankEq R M h).reindex (Equiv.ofUnique _ _)

@[simp]
theorem basisUnique_repr_eq_zero_iff {ι : Type*} [Unique ι]
    {h : finrank R M = 1} {v : M} {i : ι} :
    (basisUnique ι h).repr v i = 0 ↔ v = 0 :=
  ⟨fun hv =>
    (basisUnique ι h).repr.map_eq_zero_iff.mp (Finsupp.ext fun j => Subsingleton.elim i j ▸ hv),
    fun hv => by rw [hv, LinearEquiv.map_zero, Finsupp.zero_apply]⟩

end Module

namespace Algebra

instance (R S : Type*) [CommSemiring R] [StrongRankCondition R] [Semiring S] [Algebra R S]
    [IsQuadraticExtension R S] :
    Module.Finite R S := finite_of_finrank_eq_succ <| IsQuadraticExtension.finrank_eq_two R S

end Algebra
