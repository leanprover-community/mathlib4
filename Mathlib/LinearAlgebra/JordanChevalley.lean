/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.Semisimple
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Dynamics.Newton
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Init
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
# Jordan-Chevalley-Dunford decomposition

Given a finite-dimensional linear endomorphism `f`, the Jordan-Chevalley-Dunford theorem provides a
sufficient condition for there to exist a nilpotent endomorphism `n` and a semisimple endomorphism
`s`, such that `f = n + s` and both `n` and `s` are polynomial expressions in `f`.

The condition is that there exists a separable polynomial `P` such that the endomorphism `P(f)` is
nilpotent. This condition is always satisfied when the coefficient field is perfect.

The proof given here uses Newton's method and is taken from Chambert-Loir's notes:
[Algèbre](http://webusers.imj-prg.fr/~antoine.chambert-loir/enseignement/2022-23/agreg/algebre.pdf)

## Main definitions / results:

* `Module.End.exists_isNilpotent_isSemisimple`: an endomorphism of a finite-dimensional vector
  space over a perfect field may be written as a sum of nilpotent and semisimple endomorphisms.
  Moreover these nilpotent and semisimple components are polynomial expressions in the original
  endomorphism.
* `Module.End.isNilpotent_isSemisimple_unique`: the Jordan-Chevalley-Dunford decomposition is
  unique: if `n₁ + s₁ = n₂ + s₂` with `nᵢ` nilpotent, `sᵢ` semisimple, and `nᵢ`, `sᵢ` commuting,
  then `n₁ = n₂` and `s₁ = s₂`.

-/

public section

open Algebra Polynomial

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {f : End K V}

theorem exists_isNilpotent_isSemisimple_of_separable_of_dvd_pow {P : K[X]} {k : ℕ}
    (sep : P.Separable) (nil : minpoly K f ∣ P ^ k) :
    ∃ᵉ (n ∈ adjoin K {f}) (s ∈ adjoin K {f}), IsNilpotent n ∧ IsSemisimple s ∧ f = n + s := by
  set ff : adjoin K {f} := ⟨f, self_mem_adjoin_singleton K f⟩
  set P' := derivative P
  have nil' : IsNilpotent (aeval ff P) := by
    use k
    obtain ⟨q, hq⟩ := nil
    rw [← map_pow, Subtype.ext_iff]
    simp [ff, hq]
  have sep' : IsUnit (aeval ff P') := by
    obtain ⟨a, b, h⟩ : IsCoprime (P ^ k) P' := sep.pow_left
    replace h : (aeval f b) * (aeval f P') = 1 := by
      simpa only [map_add, map_mul, map_one, minpoly.dvd_iff.mp nil, mul_zero, zero_add]
        using (aeval f).congr_arg h
    refine .of_mul_eq_one_right (aeval ff b) (Subtype.ext_iff.mpr ?_)
    simpa [ff, coe_aeval_mk_apply] using h
  obtain ⟨⟨s, mem⟩, ⟨⟨k, hk⟩, hss⟩, -⟩ := existsUnique_nilpotent_sub_and_aeval_eq_zero nil' sep'
  refine ⟨f - s, ?_, s, mem, ⟨k, ?_⟩, ?_, (sub_add_cancel f s).symm⟩
  · exact sub_mem (self_mem_adjoin_singleton K f) mem
  · rw [Subtype.ext_iff] at hk
    simpa using hk
  · replace hss : aeval s P = 0 := by rwa [Subtype.ext_iff, coe_aeval_mk_apply] at hss
    exact isSemisimple_of_squarefree_aeval_eq_zero sep.squarefree hss

variable [FiniteDimensional K V]

/-- **Jordan-Chevalley-Dunford decomposition**: an endomorphism of a finite-dimensional vector space
over a perfect field may be written as a sum of nilpotent and semisimple endomorphisms. Moreover
these nilpotent and semisimple components are polynomial expressions in the original endomorphism.
-/
theorem exists_isNilpotent_isSemisimple [PerfectField K] :
    ∃ᵉ (n ∈ adjoin K {f}) (s ∈ adjoin K {f}), IsNilpotent n ∧ IsSemisimple s ∧ f = n + s := by
  obtain ⟨g, k, sep, -, nil⟩ := exists_squarefree_dvd_pow_of_ne_zero (minpoly.ne_zero_of_finite K f)
  rw [← PerfectField.separable_iff_squarefree] at sep
  exact exists_isNilpotent_isSemisimple_of_separable_of_dvd_pow sep nil

/-- **Uniqueness of Jordan-Chevalley-Dunford decomposition**: if `n₁ + s₁ = n₂ + s₂` with `nᵢ`
nilpotent, `sᵢ` semisimple, and `nᵢ`, `sᵢ` commuting, then `n₁ = n₂` and `s₁ = s₂`. -/
theorem isNilpotent_isSemisimple_unique [PerfectField K]
    {n₁ s₁ n₂ s₂ : End K V}
    (hn₁ : IsNilpotent n₁) (hs₁ : s₁.IsSemisimple)
    (hn₂ : IsNilpotent n₂) (hs₂ : s₂.IsSemisimple)
    (hc₁ : Commute n₁ s₁) (hc₂ : Commute n₂ s₂)
    (h : n₁ + s₁ = n₂ + s₂) :
    n₁ = n₂ ∧ s₁ = s₂ := by
  obtain ⟨n₀, hn₀, s₀, hs₀, hn₀_nil, hs₀_ss, h₀⟩ := (n₁ + s₁).exists_isNilpotent_isSemisimple
  suffices ∀ {n s}, IsNilpotent n → s.IsSemisimple → Commute n s → n₁ + s₁ = n + s → s = s₀ by grind
  intro n s hn hs hc heq
  have hsf : Commute s (n₁ + s₁) := heq ▸ hc.symm.add_right (Commute.refl s)
  have hnf : Commute n (n₁ + s₁) := heq ▸ (Commute.refl n).add_right hc
  have hnil : IsNilpotent (s - s₀) := by
    rw [show s - s₀ = n₀ - n from by grind]
    exact (commute_of_mem_adjoin_singleton_of_commute hn₀ hnf).symm.isNilpotent_sub hn₀_nil hn
  have hss : (s - s₀).IsSemisimple :=
    hs.sub_of_commute (commute_of_mem_adjoin_singleton_of_commute hs₀ hsf) hs₀_ss
  grind [eq_zero_of_isNilpotent_isSemisimple hnil hss]

end Module.End
