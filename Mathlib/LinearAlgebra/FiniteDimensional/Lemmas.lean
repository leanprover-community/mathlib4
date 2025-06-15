/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Finite dimensional vector spaces

This file contains some further development of finite dimensional vector spaces, their dimensions,
and linear maps on such spaces.

Definitions are in `Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean`
and results that require fewer imports are in `Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`.
-/

assert_not_exists Monoid.exponent Module.IsTorsion


universe u v v'

open Cardinal Submodule Module Function

variable {K : Type u} {V : Type v}

namespace Submodule

open IsNoetherian Module

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-- The dimension of a strict submodule is strictly bounded by the dimension of the ambient
space.

See also `Submodule.length_lt`. -/
theorem finrank_lt [FiniteDimensional K V] {s : Submodule K V} (h : s ≠ ⊤) :
    finrank K s < finrank K V := by
  rw [← s.finrank_quotient_add_finrank, add_comm]
  exact Nat.lt_add_of_pos_right (finrank_pos_iff.mpr (Quotient.nontrivial_of_lt_top _ h.lt_top))

/-- The sum of the dimensions of s + t and s ∩ t is the sum of the dimensions of s and t -/
theorem finrank_sup_add_finrank_inf_eq (s t : Submodule K V) [FiniteDimensional K s]
    [FiniteDimensional K t] :
    finrank K ↑(s ⊔ t) + finrank K ↑(s ⊓ t) = finrank K ↑s + finrank K ↑t := by
  have key : Module.rank K ↑(s ⊔ t) + Module.rank K ↑(s ⊓ t) = Module.rank K s + Module.rank K t :=
    rank_sup_add_rank_inf_eq s t
  repeat rw [← finrank_eq_rank] at key
  norm_cast at key

theorem finrank_add_le_finrank_add_finrank (s t : Submodule K V) [FiniteDimensional K s]
    [FiniteDimensional K t] : finrank K (s ⊔ t : Submodule K V) ≤ finrank K s + finrank K t := by
  rw [← finrank_sup_add_finrank_inf_eq]
  exact self_le_add_right _ _

theorem finrank_add_finrank_le_of_disjoint [FiniteDimensional K V]
    {s t : Submodule K V} (hdisjoint : Disjoint s t) :
    finrank K s + finrank K t ≤ finrank K V := by
  rw [← Submodule.finrank_sup_add_finrank_inf_eq s t, hdisjoint.eq_bot, finrank_bot, add_zero]
  exact Submodule.finrank_le _

theorem eq_top_of_disjoint [FiniteDimensional K V] (s t : Submodule K V)
    (hdim : finrank K V ≤ finrank K s + finrank K t) (hdisjoint : Disjoint s t) : s ⊔ t = ⊤ := by
  have h_finrank_inf : finrank K ↑(s ⊓ t) = 0 := by
    rw [disjoint_iff_inf_le, le_bot_iff] at hdisjoint
    rw [hdisjoint, finrank_bot]
  apply eq_top_of_finrank_eq
  replace hdim : finrank K V = finrank K s + finrank K t :=
    le_antisymm hdim (finrank_add_finrank_le_of_disjoint hdisjoint)
  rw [hdim]
  convert s.finrank_sup_add_finrank_inf_eq t
  rw [h_finrank_inf]
  rfl

theorem isCompl_iff_disjoint [FiniteDimensional K V] (s t : Submodule K V)
    (hdim : finrank K V ≤ finrank K s + finrank K t) :
    IsCompl s t ↔ Disjoint s t :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h, codisjoint_iff.mpr <| eq_top_of_disjoint s t hdim h⟩⟩

end DivisionRing

end Submodule

namespace FiniteDimensional

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

variable [FiniteDimensional K V] [FiniteDimensional K V₂]

/-- Given isomorphic subspaces `p q` of vector spaces `V` and `V₁` respectively,
  `p.quotient` is isomorphic to `q.quotient`. -/
noncomputable def LinearEquiv.quotEquivOfEquiv {p : Subspace K V} {q : Subspace K V₂}
    (f₁ : p ≃ₗ[K] q) (f₂ : V ≃ₗ[K] V₂) : (V ⧸ p) ≃ₗ[K] V₂ ⧸ q :=
  LinearEquiv.ofFinrankEq _ _
    (by
      rw [← @add_right_cancel_iff _ _ _ (finrank K p), Submodule.finrank_quotient_add_finrank,
        LinearEquiv.finrank_eq f₁, Submodule.finrank_quotient_add_finrank,
        LinearEquiv.finrank_eq f₂])

-- TODO: generalize to the case where one of `p` and `q` is finite-dimensional.
/-- Given the subspaces `p q`, if `p.quotient ≃ₗ[K] q`, then `q.quotient ≃ₗ[K] p` -/
noncomputable def LinearEquiv.quotEquivOfQuotEquiv {p q : Subspace K V} (f : (V ⧸ p) ≃ₗ[K] q) :
    (V ⧸ q) ≃ₗ[K] p :=
  LinearEquiv.ofFinrankEq _ _ <| by
    rw [← add_right_cancel_iff, Submodule.finrank_quotient_add_finrank, ← LinearEquiv.finrank_eq f,
      add_comm, Submodule.finrank_quotient_add_finrank]

end DivisionRing

end FiniteDimensional

namespace LinearMap

open Module

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

/-- rank-nullity theorem : the dimensions of the kernel and the range of a linear map add up to
the dimension of the source space. -/
theorem finrank_range_add_finrank_ker [FiniteDimensional K V] (f : V →ₗ[K] V₂) :
    finrank K (LinearMap.range f) + finrank K (LinearMap.ker f) = finrank K V := by
  rw [← f.quotKerEquivRange.finrank_eq]
  exact Submodule.finrank_quotient_add_finrank _

lemma ker_ne_bot_of_finrank_lt [FiniteDimensional K V] [FiniteDimensional K V₂] {f : V →ₗ[K] V₂}
    (h : finrank K V₂ < finrank K V) :
    LinearMap.ker f ≠ ⊥ := by
  have h₁ := f.finrank_range_add_finrank_ker
  have h₂ : finrank K (LinearMap.range f) ≤ finrank K V₂ := (LinearMap.range f).finrank_le
  suffices 0 < finrank K (LinearMap.ker f) from Submodule.one_le_finrank_iff.mp this
  omega

end DivisionRing

end LinearMap

open Module

namespace LinearMap

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

theorem injective_iff_surjective_of_finrank_eq_finrank [FiniteDimensional K V]
    [FiniteDimensional K V₂] (H : finrank K V = finrank K V₂) {f : V →ₗ[K] V₂} :
    Function.Injective f ↔ Function.Surjective f := by
  have := finrank_range_add_finrank_ker f
  rw [← ker_eq_bot, ← range_eq_top]; refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, finrank_bot, add_zero, H] at this
    exact eq_top_of_finrank_eq this
  · rw [h, finrank_top, H] at this
    exact Submodule.finrank_eq_zero.1 (add_right_injective _ this)

theorem ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank [FiniteDimensional K V]
    [FiniteDimensional K V₂] (H : finrank K V = finrank K V₂) {f : V →ₗ[K] V₂} :
    LinearMap.ker f = ⊥ ↔ LinearMap.range f = ⊤ := by
  rw [range_eq_top, ker_eq_bot, injective_iff_surjective_of_finrank_eq_finrank H]

/-- Given a linear map `f` between two vector spaces with the same dimension, if
`ker f = ⊥` then `linearEquivOfInjective` is the induced isomorphism
between the two vector spaces. -/
noncomputable def linearEquivOfInjective [FiniteDimensional K V] [FiniteDimensional K V₂]
    (f : V →ₗ[K] V₂) (hf : Injective f) (hdim : finrank K V = finrank K V₂) : V ≃ₗ[K] V₂ :=
  LinearEquiv.ofBijective f
    ⟨hf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf⟩

@[simp]
theorem linearEquivOfInjective_apply [FiniteDimensional K V] [FiniteDimensional K V₂]
    {f : V →ₗ[K] V₂} (hf : Injective f) (hdim : finrank K V = finrank K V₂) (x : V) :
    f.linearEquivOfInjective hf hdim x = f x :=
  rfl

end LinearMap

namespace Submodule

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

theorem finrank_lt_finrank_of_lt {s t : Submodule K V} [FiniteDimensional K t] (hst : s < t) :
    finrank K s < finrank K t :=
  (comapSubtypeEquivOfLe hst.le).finrank_eq.symm.trans_lt <|
    finrank_lt <| by simp [not_le_of_gt hst]

theorem finrank_strictMono [FiniteDimensional K V] :
    StrictMono fun s : Submodule K V => finrank K s := fun _ _ => finrank_lt_finrank_of_lt

theorem finrank_add_eq_of_isCompl [FiniteDimensional K V] {U W : Submodule K V} (h : IsCompl U W) :
    finrank K U + finrank K W = finrank K V := by
  rw [← finrank_sup_add_finrank_inf_eq, h.codisjoint.eq_top, h.disjoint.eq_bot, finrank_bot,
    add_zero]
  exact finrank_top _ _

end DivisionRing

end Submodule

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

section Basis

theorem LinearIndependent.span_eq_top_of_card_eq_finrank' {ι : Type*}
    [Fintype ι] [FiniteDimensional K V] {b : ι → V} (lin_ind : LinearIndependent K b)
    (card_eq : Fintype.card ι = finrank K V) : span K (Set.range b) = ⊤ := by
  by_contra ne_top
  rw [← finrank_span_eq_card lin_ind] at card_eq
  exact ne_of_lt (Submodule.finrank_lt ne_top) card_eq

theorem LinearIndependent.span_eq_top_of_card_eq_finrank {ι : Type*} [Nonempty ι]
    [Fintype ι] {b : ι → V} (lin_ind : LinearIndependent K b)
    (card_eq : Fintype.card ι = finrank K V) : span K (Set.range b) = ⊤ :=
  have : FiniteDimensional K V := .of_finrank_pos <| card_eq ▸ Fintype.card_pos
  lin_ind.span_eq_top_of_card_eq_finrank' card_eq

/-- A linear independent family of `finrank K V` vectors forms a basis. -/
@[simps! repr_apply]
noncomputable def basisOfLinearIndependentOfCardEqFinrank {ι : Type*} [Nonempty ι] [Fintype ι]
    {b : ι → V} (lin_ind : LinearIndependent K b) (card_eq : Fintype.card ι = finrank K V) :
    Basis ι K V :=
  Basis.mk lin_ind <| (lin_ind.span_eq_top_of_card_eq_finrank card_eq).ge

@[simp]
theorem coe_basisOfLinearIndependentOfCardEqFinrank {ι : Type*} [Nonempty ι] [Fintype ι]
    {b : ι → V} (lin_ind : LinearIndependent K b) (card_eq : Fintype.card ι = finrank K V) :
    ⇑(basisOfLinearIndependentOfCardEqFinrank lin_ind card_eq) = b :=
  Basis.coe_mk _ _

/-- In a vector space `ι → K`, a linear independent family indexed by `ι` is a basis. -/
noncomputable def basisOfPiSpaceOfLinearIndependent {ι : Type*} [Fintype ι]
    [Decidable (Nonempty ι)] {b : ι → (ι → K)} (hb : LinearIndependent K b) : Basis ι K (ι → K) :=
  if hι : Nonempty ι then
    basisOfLinearIndependentOfCardEqFinrank hb (Module.finrank_fintype_fun_eq_card K).symm
  else
    have : IsEmpty ι := not_nonempty_iff.mp hι
    Basis.empty _

open Classical in
@[simp]
theorem coe_basisOfPiSpaceOfLinearIndependent {ι : Type*} [Fintype ι]
    {b : ι → (ι → K)} (hb : LinearIndependent K b) :
    ⇑(basisOfPiSpaceOfLinearIndependent hb) = b := by
  by_cases hι : Nonempty ι
  · simp [hι, basisOfPiSpaceOfLinearIndependent]
  · rw [basisOfPiSpaceOfLinearIndependent, dif_neg hι]
    ext i
    exact ((not_nonempty_iff.mp hι).false i).elim

/-- A linear independent finset of `finrank K V` vectors forms a basis. -/
@[simps! repr_apply]
noncomputable def finsetBasisOfLinearIndependentOfCardEqFinrank {s : Finset V} (hs : s.Nonempty)
    (lin_ind : LinearIndependent K ((↑) : s → V)) (card_eq : s.card = finrank K V) : Basis s K V :=
  @basisOfLinearIndependentOfCardEqFinrank _ _ _ _ _ _
    ⟨(⟨hs.choose, hs.choose_spec⟩ : s)⟩ _ _ lin_ind (_root_.trans (Fintype.card_coe _) card_eq)

@[simp]
theorem coe_finsetBasisOfLinearIndependentOfCardEqFinrank {s : Finset V} (hs : s.Nonempty)
    (lin_ind : LinearIndependent K ((↑) : s → V)) (card_eq : s.card = finrank K V) :
    ⇑(finsetBasisOfLinearIndependentOfCardEqFinrank hs lin_ind card_eq) = ((↑) : s → V) := by
  simp [finsetBasisOfLinearIndependentOfCardEqFinrank]

/-- A linear independent set of `finrank K V` vectors forms a basis. -/
@[simps! repr_apply]
noncomputable def setBasisOfLinearIndependentOfCardEqFinrank {s : Set V} [Nonempty s] [Fintype s]
    (lin_ind : LinearIndependent K ((↑) : s → V)) (card_eq : s.toFinset.card = finrank K V) :
    Basis s K V :=
  basisOfLinearIndependentOfCardEqFinrank lin_ind (_root_.trans s.toFinset_card.symm card_eq)

@[simp]
theorem coe_setBasisOfLinearIndependentOfCardEqFinrank {s : Set V} [Nonempty s] [Fintype s]
    (lin_ind : LinearIndependent K ((↑) : s → V)) (card_eq : s.toFinset.card = finrank K V) :
    ⇑(setBasisOfLinearIndependentOfCardEqFinrank lin_ind card_eq) = ((↑) : s → V) := by
  simp [setBasisOfLinearIndependentOfCardEqFinrank]

end Basis

/-!
We now give characterisations of `finrank K V = 1` and `finrank K V ≤ 1`.
-/

section finrank_eq_one

/-- Any `K`-algebra module that is 1-dimensional over `K` is simple. -/
theorem is_simple_module_of_finrank_eq_one {A} [Semiring A] [Module A V] [SMul K A]
    [IsScalarTower K A V] (h : finrank K V = 1) : IsSimpleOrder (Submodule A V) := by
  haveI := nontrivial_of_finrank_eq_succ h
  refine ⟨fun S => or_iff_not_imp_left.2 fun hn => ?_⟩
  rw [← restrictScalars_inj K] at hn ⊢
  haveI : FiniteDimensional _ _ := .of_finrank_eq_succ h
  refine eq_top_of_finrank_eq ((Submodule.finrank_le _).antisymm ?_)
  simpa only [h, finrank_bot] using Submodule.finrank_strictMono (Ne.bot_lt hn)

end finrank_eq_one

end DivisionRing

section SubalgebraRank

open Module

variable {F E : Type*} [Field F] [Ring E] [Algebra F E]

theorem Subalgebra.isSimpleOrder_of_finrank (hr : finrank F E = 2) :
    IsSimpleOrder (Subalgebra F E) :=
  let i := nontrivial_of_finrank_pos (zero_lt_two.trans_eq hr.symm)
  { toNontrivial :=
      ⟨⟨⊥, ⊤, fun h => by cases hr.symm.trans (Subalgebra.bot_eq_top_iff_finrank_eq_one.1 h)⟩⟩
    eq_bot_or_eq_top := by
      intro S
      haveI : FiniteDimensional F E := .of_finrank_eq_succ hr
      haveI : FiniteDimensional F S :=
        FiniteDimensional.finiteDimensional_submodule (Subalgebra.toSubmodule S)
      have : finrank F S ≤ 2 := hr ▸ S.toSubmodule.finrank_le
      have : 0 < finrank F S := finrank_pos_iff.mpr inferInstance
      interval_cases h : finrank F { x // x ∈ S }
      · left
        exact Subalgebra.eq_bot_of_finrank_one h
      · right
        rw [← hr] at h
        rw [← Algebra.toSubmodule_eq_top]
        exact eq_top_of_finrank_eq h }

end SubalgebraRank

namespace Module

namespace End

variable [DivisionRing K] [AddCommGroup V] [Module K V]

theorem exists_ker_pow_eq_ker_pow_succ [FiniteDimensional K V] (f : End K V) :
    ∃ k : ℕ, k ≤ finrank K V ∧ LinearMap.ker (f ^ k) = LinearMap.ker (f ^ k.succ) := by
  classical
    by_contra h_contra
    simp_rw [not_exists, not_and] at h_contra
    have h_le_ker_pow : ∀ n : ℕ, n ≤ (finrank K V).succ →
        n ≤ finrank K (LinearMap.ker (f ^ n)) := by
      intro n hn
      induction n with
      | zero => exact zero_le (finrank _ _)
      | succ n ih =>
        have h_ker_lt_ker : LinearMap.ker (f ^ n) < LinearMap.ker (f ^ n.succ) := by
          refine lt_of_le_of_ne ?_ (h_contra n (Nat.le_of_succ_le_succ hn))
          rw [pow_succ']
          apply LinearMap.ker_le_ker_comp
        have h_finrank_lt_finrank :
            finrank K (LinearMap.ker (f ^ n)) < finrank K (LinearMap.ker (f ^ n.succ)) := by
          apply Submodule.finrank_lt_finrank_of_lt h_ker_lt_ker
        calc
          n.succ ≤ (finrank K ↑(LinearMap.ker (f ^ n))).succ :=
            Nat.succ_le_succ (ih (Nat.le_of_succ_le hn))
          _ ≤ finrank K ↑(LinearMap.ker (f ^ n.succ)) := Nat.succ_le_of_lt h_finrank_lt_finrank
    have h_any_n_lt : ∀ n, n ≤ (finrank K V).succ → n ≤ finrank K V := fun n hn =>
      (h_le_ker_pow n hn).trans (Submodule.finrank_le _)
    show False
    exact Nat.not_succ_le_self _ (h_any_n_lt (finrank K V).succ (finrank K V).succ.le_refl)

theorem ker_pow_eq_ker_pow_finrank_of_le [FiniteDimensional K V] {f : End K V} {m : ℕ}
    (hm : finrank K V ≤ m) : LinearMap.ker (f ^ m) = LinearMap.ker (f ^ finrank K V) := by
  obtain ⟨k, h_k_le, hk⟩ :
    ∃ k, k ≤ finrank K V ∧ LinearMap.ker (f ^ k) = LinearMap.ker (f ^ k.succ) :=
    exists_ker_pow_eq_ker_pow_succ f
  calc
    LinearMap.ker (f ^ m) = LinearMap.ker (f ^ (k + (m - k))) := by
      rw [add_tsub_cancel_of_le (h_k_le.trans hm)]
    _ = LinearMap.ker (f ^ k) := by rw [ker_pow_constant hk _]
    _ = LinearMap.ker (f ^ (k + (finrank K V - k))) := ker_pow_constant hk (finrank K V - k)
    _ = LinearMap.ker (f ^ finrank K V) := by rw [add_tsub_cancel_of_le h_k_le]

theorem ker_pow_le_ker_pow_finrank [FiniteDimensional K V] (f : End K V) (m : ℕ) :
    LinearMap.ker (f ^ m) ≤ LinearMap.ker (f ^ finrank K V) := by
  by_cases h_cases : m < finrank K V
  · rw [← add_tsub_cancel_of_le (Nat.le_of_lt h_cases), add_comm, pow_add]
    apply LinearMap.ker_le_ker_comp
  · rw [ker_pow_eq_ker_pow_finrank_of_le (le_of_not_gt h_cases)]

end End

end Module
