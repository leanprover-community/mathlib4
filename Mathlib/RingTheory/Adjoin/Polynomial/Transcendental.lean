/-
Copyright (c) 2026 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos Fernández, Miriam Philipp, Justus Springer, Junyan Xu
-/
module

public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Polynomial.Quotient


/-!
# Polynomials and adjoining transcendental elements
-/

@[expose] public noncomputable section

variable {R S : Type*}

open Algebra

variable [CommRing R] [CommRing S] [Algebra R S]

variable (s : S)

namespace Polynomial

variable {p q : R[X]}

variable (R) in
/-- Given a transcendental element `s : S` over `R`, the `R`-algebra equivalence
between `R[X]` and `R[s]` given by sending `X` to `s`. -/
noncomputable def algEquivOfTranscendental (h : Transcendental R s) :
    R[X] ≃ₐ[R] R[s] :=
  AlgEquiv.ofBijective (aeval (s : R[s])) <| by
    refine ⟨transcendental_iff_injective.mp ?_, ?_⟩
    · rwa [Subalgebra.transcendental_iff_transcendental_val]
    rw [← AlgHom.range_eq_top, _root_.eq_top_iff]
    rintro ⟨t, ht⟩ _
    obtain ⟨r, rfl⟩ := adjoin_mem_exists_aeval _ _ ht
    exact ⟨r, by ext; simp⟩

@[simp]
theorem algEquivOfTranscendental_coe (h : Transcendental R s) :
    (algEquivOfTranscendental R s h : R[X] →+* R[s]) = aeval (R := R) (A := R[s]) s :=
  rfl

@[simp]
theorem algEquivOfTranscendental_apply (h : Transcendental R s) (f : R[X]) :
    algEquivOfTranscendental R s h f = aeval (s : R[s]) f := rfl

lemma algEquivOfTranscendental_apply_X (h : Transcendental R s) :
    algEquivOfTranscendental R s h X = (s : R[s]) := by simp

@[simp]
theorem algEquivOfTranscendental_symm_aeval (h : Transcendental R s) (f : R[X]) :
    (algEquivOfTranscendental R s h).symm (aeval (s : R[s]) f) = f :=
  (algEquivOfTranscendental R s h).toEquiv.injective (by simp)

@[simp]
theorem algEquivOfTranscendental_symm_gen (h : Transcendental R s) :
    (algEquivOfTranscendental R s h).symm s = X :=
  (algEquivOfTranscendental R s h).toEquiv.injective (by simp)

end Polynomial

namespace Algebra

open Ideal Polynomial

variable {p : R[X]}

/-- TODO: add doc -/
def adjoin.evalOfTranscendental (ht : Transcendental R s) (c : R) : R[s] →ₐ[R] R :=
  (aeval c).comp (algEquivOfTranscendental R s ht).symm

@[simp]
theorem adjoin.evalOfTranscendental_aeval (ht : Transcendental R s) (c : R) :
    (evalOfTranscendental s ht c) (p.aeval s : R[s]) = p.aeval c := by
  simp_all [evalOfTranscendental, ← adjoin_aeval_self,
    algEquivOfTranscendental_symm_aeval A y ht p]

theorem adjoin.evalOfTranscendental_eq_zero_iff (ht : Transcendental R s) (x : R[s])
    (c : R) : evalOfTranscendental s ht c x = 0 ↔ ((s : R[s]) - algebraMap R R[s] c) ∣ x := by
  simp [evalOfTranscendental, ← map_dvd_iff (algEquivOfTranscendental R s ht).symm,
    Polynomial.dvd_iff_isRoot]


end Algebra

open Polynomial

variable [UniqueFactorizationMonoid R]

theorem Transcendental.uniqueFactorizationMonoid_adjoin {s : S} (h : Transcendental R s) :
    UniqueFactorizationMonoid R[s] :=
  (algEquivOfTranscendental R s h).toMulEquiv.uniqueFactorizationMonoid inferInstance

instance {s : S} [h : Fact (Transcendental R s)] : UniqueFactorizationMonoid R[s] :=
  (algEquivOfTranscendental R s h.out).toMulEquiv.uniqueFactorizationMonoid inferInstance

theorem Transcendental.wfDvdMonoid_adjoin (ht : Transcendental R s) : WfDvdMonoid R[s] :=
  (uniqueFactorizationMonoid_adjoin ht).toIsWellFounded

end
