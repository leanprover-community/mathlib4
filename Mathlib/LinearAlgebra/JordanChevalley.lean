/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Dynamics.Newton
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Jordan-Chevalley-Dunford decomposition

Given a finite-dimensional linear endomorphism `f`, the Jordan-Chevalley-Dunford theorem provides a
sufficient condition for there to exist a nilpotent endomorphism `n` and a semisimple endomorphism
`s`, such that `f = n + s` and both `n` and `s` are polynomial expressions in `f`.

The condition is that there exists a separable polynomial `P` such that the endomorphism `P(f)` is
nilpotent. This condition is always satisfied when the coefficients are a perfect field.

The proof given here uses Newton's method and is taken from Chambert-Loir's notes:
[Algebre](http://webusers.imj-prg.fr/~antoine.chambert-loir/enseignement/2022-23/agreg/algebre.pdf)

## Main definitions / results:

* `Module.End.exists_isNilpotent_isSemisimple`: an endomorphism of a finite-dimensional vector
  space over a perfect field may be written as a sum of nilpotent and semisimple endomorphisms.
  Moreover these nilpotent and semisimple components are polynomial expressions in the original
  endomorphism.

## TODO

* Uniqueness of decomposition (once we prove that the sum of commuting semisimple endomorphims is
  semisimple, this will follow from `Module.End.eq_zero_of_isNilpotent_isSemisimple`).

-/

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
    refine isUnit_of_mul_eq_one_right (aeval ff b) _ (Subtype.ext_iff.mpr ?_)
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

end Module.End
