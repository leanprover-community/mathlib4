/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# The radical of a quadratic form

We define the radical of a quadratic form. This is a standard construction if 2 is invertible
in the coefficient ring, but is more fiddly otherwise. We follow the account in
Chapter II, §7 of [elman-karpenko-merkurjev-2008][].
-/

open Finset QuadraticMap

@[expose] public noncomputable section

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

/-- The rank of the radical of a quadratic map is invariant under equivalences. -/
lemma Equivalent.rank_radical_eq {Q' : QuadraticMap R M' P} (h : Equivalent Q Q') :
    Module.finrank R Q.radical = Module.finrank R Q'.radical := by
  obtain ⟨e⟩ := h
  rw [← e.map_radical, LinearEquiv.finrank_map_eq]

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

/--
A quadratic map is said to be **nondegenerate** if its radical is 0, and the radical of
its associated polar form has rank ≤ 1. (The second condition is automatic if 2 is invertible in
`R`, but not in general.) See Elman-Karpenko-Merkurjev, Chapter II, §7.
-/
structure Nondegenerate : Prop where
  radical_eq_bot : Q.radical = ⊥
  rank_rad_polar_le : Module.rank R Q.polarBilin.ker ≤ 1

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

/-- In characteristic `≠ 2`, a quadratic map is nondegenerate iff its radical is 0. (Use
`QuadraticMap.Nondegenerate.radical_eq_bot` for the one-way implication in all characteristics.) -/
lemma nondegenerate_iff_radical_eq_bot :
    Q.Nondegenerate ↔ Q.radical = ⊥ := by
  refine ⟨Nondegenerate.radical_eq_bot, fun h ↦ ⟨h, ?_⟩⟩
  rw [← QuadraticMap.radical_eq_ker_polarBilin, h]
  nontriviality R
  simp only [rank_subsingleton', zero_le]

/-- In characteristic `≠ 2`, a quadratic map is nondegenerate iff its associated bilinear map
is nondegenerate. -/
lemma nondegenerate_associated_iff :
    (QuadraticMap.associated Q).Nondegenerate ↔ Q.Nondegenerate := by
  rw [nondegenerate_iff_radical_eq_bot, radical_eq_ker_associated,
    LinearMap.IsRefl.nondegenerate_iff_separatingLeft, LinearMap.separatingLeft_iff_ker_eq_bot]
  exact fun x y ↦ (congr_arg (· x y) (associated_flip R Q)).trans

/-- In characteristic `≠ 2`, a quadratic map is nondegenerate iff its polar bilinear map
is nondegenerate. -/
lemma nondegenerate_polar_iff :
    (QuadraticMap.polarBilin Q).Nondegenerate ↔ Q.Nondegenerate := by
  rw [nondegenerate_iff_radical_eq_bot, radical_eq_ker_polarBilin,
    LinearMap.IsRefl.nondegenerate_iff_separatingLeft, LinearMap.separatingLeft_iff_ker_eq_bot]
  exact fun x y ↦ (polar_comm Q y x).trans

end InvertibleTwo

end QuadraticMap
