/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# The radical of a quadratic form

We define the radical of a quadratic form. This is a standard construction if 2 is invertible
in the coefficient ring, but is more fiddly otherwise. We follow the account in
Chapter II, §7 of [elman-karpenko-merkurjev-2008][].
-/

open Finset QuadraticMap

@[expose] public noncomputable section

section Quotient
/-!
## Lifting bilinear forms through quotients
-/

variable {R R₂ S S₂ M N P : Type*} [Ring R] [Ring R₂] [Ring S] [Ring S₂]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module S N] [Module R₂ P]
    [Module S₂ P] [SMulCommClass R₂ S₂ P] [SMulCommClass S₂ R₂ P] {ρ : R →+* R₂} {σ : S →+* S₂}

/-- Lift a bilinear form from `M × N → P` to `(M ⧸ M') × (N ⧸ N') → P`. -/
def LinearMap.liftQ₂ (M' : Submodule R M) (N' : Submodule S N) (f : M →ₛₗ[ρ] N →ₛₗ[σ] P)
    (hM' : M' ≤ f.ker) (hN' : N' ≤ f.flip.ker) :
    M ⧸ M' →ₛₗ[ρ] N ⧸ N' →ₛₗ[σ] P :=
  have : ∀ n ∈ N', n ∈ (M'.liftQ f hM').flip.ker := fun n hn ↦ by
    simp_rw [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.flip_apply, Submodule.Quotient.forall,
      Submodule.liftQ_apply, ← f.flip_apply, show f.flip n = 0 from hN' hn, LinearMap.zero_apply,
      forall_true_iff]
  (N'.liftQ (M'.liftQ f hM').flip this).flip

-- This is weird, the `def` requires both versions of `SMulCommClass` to state but somehow
-- only one of them is needed to prove a lemma about it?
omit [SMulCommClass R₂ S₂ P] in
@[simp]
lemma LinearMap.liftQ₂_mk (M' : Submodule R M) (N' : Submodule S N) (f : M →ₛₗ[ρ] N →ₛₗ[σ] P)
    (hM' : M' ≤ f.ker) (hN' : N' ≤ f.flip.ker) (m : M) (n : N) :
    f.liftQ₂ M' N' hM' hN' (Submodule.Quotient.mk m) (Submodule.Quotient.mk n) = f m n :=
  rfl

end Quotient

section QuotientRefl

/-- Special case of `Submodule.liftQ₂` with  `M × M → P` to `(M ⧸ N) × (M ⧸ N) → P`. Reducible so
that simp lemmas about `Submodule.liftQ₂` apply to it. -/
abbrev LinearMap.IsRefl.liftQ₂ {R S M P : Type*} [AddCommGroup M] [CommRing R] [CommRing S]
    [Module R M] [AddCommGroup P] [Module S P] {I₁ I₂ : R →+* S} (f : M →ₛₗ[I₁] M →ₛₗ[I₂] P)
    (N : Submodule R M) (hf : f.IsRefl) (hN : N ≤ f.ker) :
    M ⧸ N →ₛₗ[I₁] M ⧸ N →ₛₗ[I₂] P :=
  f.liftQ₂ N N hN (hf.ker_flip ▸ hN)

end QuotientRefl

namespace QuadraticMap

variable {R M M' P : Type*} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup P]
  [CommRing R] [Module R M] [Module R M'] [Module R P] (Q : QuadraticMap R M P)

/-- The radical of a quadratic form `Q` on `M`.

This is the largest submodule `N` such that `Q` lifts to a quadratic form on `M ⧸ N`; see
`Submodule.le_radical_iff` for this characterization.

See also Elman-Karpenko-Merkurjev, Chapter II, §7. -/
def radical : Submodule R M where
  carrier := {x : M | Q x = 0 ∧ QuadraticMap.polarBilin Q x = 0}
  zero_mem' := by simp
  smul_mem' a x hx := by simp [QuadraticMap.map_smul, hx.1, hx.2]
  add_mem' := fun {x y} hx hy ↦ by
    refine ⟨?_, by simp [hx.2, hy.2]⟩
    have := congr_arg (· y) hx.2
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      LinearMap.zero_apply, sub_sub, sub_eq_zero] at this
    rw [this, hx.1, hy.1, zero_add]

variable {Q}

lemma mem_radical_iff' {m : M} :
    m ∈ Q.radical ↔ Q m = 0 ∧ ∀ n : M, Q (m + n) = Q n := by
  simp +contextual [radical, QuadraticMap.polarBilin, LinearMap.ext_iff,
    QuadraticMap.polar, sub_sub, sub_eq_zero]

/-- The radical of a quadratic form is preserved by isometry equivalences. -/
@[simp] lemma IsometryEquiv.map_radical {Q' : QuadraticMap R M' P}
    (e : IsometryEquiv Q Q') : Q.radical.map e.toLinearMap = Q'.radical := by
  ext x
  simp only [Submodule.mem_map_equiv, coe_symm_toLinearEquiv, coe_toLinearEquiv,
    QuadraticMap.mem_radical_iff', ← e.map_app, e.apply_symm_apply, map_add,
    e.toEquiv.forall_congr_left, LinearEquiv.coe_symm_toEquiv]

-- auxiliary lemma for lifting quadratic maps to quotients
private lemma lift_aux {N : Submodule R M} (hN : N ≤ Q.radical)
    (m m' : M) (hmm' : Submodule.quotientRel N m m') : Q m = Q m' := by
  rw [Submodule.quotientRel_def] at hmm'
  rw [(by simp : m = m' + (m - m')), QuadraticMap.map_add Q m' (m - m'),
    (hN hmm').1, add_zero, polar_comm, ← polarBilin_apply_apply]
  simp [(hN hmm').2]

variable (Q) in
/-- Lift a quadratic map on `M` to `M ⧸ N`, where `N` is contained in the radical. -/
protected def lift (N : Submodule R M) (hN : N ≤ Q.radical) : QuadraticMap R (M ⧸ N) P := by
  refine QuadraticMap.mk (Quotient.lift Q <| by exact lift_aux hN)
    (fun a m ↦ m.inductionOn (Q.map_smul a)) ?_
  use Q.polarBilin.liftQ₂ N N (fun n hn ↦ (hN hn).2) (fun n hn ↦ ?_)
  · simp only [Submodule.Quotient.forall]
    exact QuadraticMap.map_add Q -- remarkably, this works
  · simp_rw [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.flip_apply,
      polarBilin_apply_apply, polar_comm, ← polarBilin_apply_apply, (hN hn).2, forall_true_iff]

@[simp]
lemma lift_mk {N : Submodule R M} (hN : N ≤ Q.radical) (m : M) :
    Q.lift N hN (Submodule.Quotient.mk m) = Q m :=
  rfl

/-- Universal property of the radical of a quadratic form: `Q.radical` is the largest subspace
`N` such that `Q` factors through a quadratic form on `M ⧸ N`. -/
lemma le_radical_iff {N : Submodule R M} :
    N ≤ Q.radical ↔ ∃ Q' : QuadraticMap R (M ⧸ N) P, Q'.comp N.mkQ = Q := by
  constructor
  · exact fun hN ↦ ⟨Q.lift N hN, rfl⟩
  · rintro ⟨Q', rfl⟩ m hm
    simp [radical, (Submodule.Quotient.mk_eq_zero _).mpr hm, LinearMap.ext_iff, polar]

/-- The radical of a quadratic map is contained in the kernel of its polar bilinear map.

See `radical_eq_ker_polarBilin` for the equality when 2 is invertible in the
coefficient ring. -/
lemma radical_le_ker_polarBilin : Q.radical ≤ Q.polarBilin.ker := by
  intro m
  simp +contextual [mem_radical_iff', LinearMap.ext_iff, QuadraticMap.polar]

section InvertibleTwo

variable [Invertible (2 : R)]

/-- If 2 is invertible in the coefficient ring, the radical of a quadratic map is the kernel of its
polar bilinear map. -/
lemma radical_eq_ker_polarBilin : Q.radical = Q.polarBilin.ker := by
  ext m
  simp only [mem_radical_iff', LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  refine ⟨by simp +contextual, fun h ↦ ?_⟩
  suffices Q m = 0 by grind
  specialize h m
  rwa [← two_smul R, QuadraticMap.map_smul, sub_sub, ← two_smul R, mul_smul, ← smul_sub,
    (isUnit_of_invertible 2).smul_eq_zero, two_smul, add_sub_cancel_right] at h

/-- If 2 is invertible in the coefficient ring, the radical of a quadratic map is the kernel of its
associated bilinear map. -/
lemma radical_eq_ker_associated : Q.radical = (QuadraticMap.associated Q).ker := by
  rw [radical_eq_ker_polarBilin]
  ext m
  simp [LinearMap.ext_iff, QuadraticMap.polar, -smul_eq_mul, invOf_smul_eq_iff]

end InvertibleTwo

end QuadraticMap

/-!
## Nondegenerate quadratic forms
-/

namespace QuadraticForm

variable {R M M' : Type*} [AddCommGroup M] [AddCommGroup M']
  [CommRing R] [Module R M] (Q : QuadraticForm R M)

/--
A quadratic form is said to be **nondegenerate** if its radical is 0, and the radical of
its associated polar form has rank ≤ 1. (The second condition is automatic if 2 is invertible in
`R`, but not in general.) See Elman-Karpenko-Merkurjev, Chapter II, §7.

We do not define this for general quadratic maps (only for quadratic _forms_) because I don't know
if this is a sensible definition in that generality.
-/
structure Nondegenerate : Prop where
  radical_eq_bot : Q.radical = ⊥
  rank_rad_polar_le : Module.rank R Q.polarBilin.ker ≤ 1

variable {Q}

section InvertibleTwo

variable [Invertible (2 : R)]

/-- In characteristic `≠ 2`, a quadratic form is nondegenerate iff its radical is 0. -/
lemma nondegenerate_iff_radical_eq_bot :
    Q.Nondegenerate ↔ Q.radical = ⊥ := by
  refine ⟨Nondegenerate.radical_eq_bot, fun h ↦ ⟨h, ?_⟩⟩
  rw [← QuadraticMap.radical_eq_ker_polarBilin, h]
  nontriviality R
  simp only [rank_subsingleton', zero_le]

lemma nondegenerate_associated_iff :
    (QuadraticMap.associated Q).Nondegenerate ↔ Q.Nondegenerate := by
  rw [QuadraticForm.nondegenerate_iff_radical_eq_bot, radical_eq_ker_associated,
    LinearMap.IsRefl.nondegenerate_iff_separatingLeft, LinearMap.separatingLeft_iff_ker_eq_bot]
  exact (associated_isSymm R Q).isRefl

end InvertibleTwo

end QuadraticForm
