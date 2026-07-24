/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.RingTheory.Invariant.Defs

/-!
# Predicate for Galois Groups

Given an action of a group `G` on an extension of fields `L/K`, we introduce a predicate
`IsGaloisGroup G K L` saying that `G` acts faithfully on `L` with fixed field `K`. In particular,
we do not assume that `L` is an algebraic extension of `K`.

## Implementation notes

We actually define `IsGaloisGroup G A B` for extensions of rings `B/A`, with the same definition
(faithful action on `B` with fixed ring `A`). This definition turns out to axiomatize a common
setup in algebraic number theory where a Galois group `Gal(L/K)` acts on an extension of subrings
`B/A` (e.g., rings of integers). In particular, there are theorems in algebraic number theory that
naturally assume `[IsGaloisGroup G A B]` and whose statements would otherwise require assuming
`(K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L]` (along with predicates relating
`K` and `L` to the rings `A` and `B`) despite `K` and `L` not appearing in the conclusion.

Unfortunately, this definition of `IsGaloisGroup G A B` for extensions of rings `B/A` is
nonstandard and clashes with other notions such as the étale fundamental group. In particular, if
`G` is finite and `A` is integrally closed, then  `IsGaloisGroup G A B` is equivalent to `B/A`
being integral and the fields of fractions `Frac(B)/Frac(A)` being Galois with Galois group `G`
(see `IsGaloisGroup.iff_isFractionRing`), rather than `B/A` being étale for instance.

But in the absence of a more suitable name, the utility of the predicate `IsGaloisGroup G A B` for
extensions of rings `B/A` seems to outweigh these terminological issues.
-/

@[expose] public section

assert_not_exists IsFractionRing

variable (G A A' B : Type*) [Group G] [CommSemiring A] [Semiring B] [Algebra A B]
  [MulSemiringAction G B]

/-- `G` is a Galois group for `L/K` if the action of `G` on `L` is faithful with fixed field `K`.
In particular, we do not assume that `L` is an algebraic extension of `K`.

See the implementation notes in this file for the meaning of this definition in the case of rings.
-/
class IsGaloisGroup where
  faithful : FaithfulSMul G B
  commutes : SMulCommClass G A B
  isInvariant : Algebra.IsInvariant A B G

namespace IsGaloisGroup

variable {G A B} in
theorem of_mulEquiv [hG : IsGaloisGroup G A B] {H : Type*} [Group H]
    [MulSemiringAction H B] (e : H ≃* G) (he : ∀ h (x : B), (e h) • x = h • x) :
    IsGaloisGroup H A B where
  faithful := ⟨fun h ↦ e.injective <| hG.faithful.eq_of_smul_eq_smul <| by simpa only [he]⟩
  commutes := ⟨fun x a b ↦ by simpa [he] using hG.commutes.smul_comm (e x) a b⟩
  isInvariant := ⟨fun b h ↦
    have he' : ∀ (g : G) (x : B), e.symm g • x = g • x := fun g x ↦ by simp [← he]
    hG.isInvariant.isInvariant b (fun g ↦ by simpa [he'] using h (e.symm g))⟩

variable {G A B} in
theorem iff_of_mulEquiv {H : Type*} [Group H] [MulSemiringAction H B]
    (e : H ≃* G) (he : ∀ h (x : B), e h • x = h • x) :
    IsGaloisGroup H A B ↔ IsGaloisGroup G A B := by
  refine ⟨fun h ↦ h.of_mulEquiv e.symm fun g x ↦ ?_, fun h ↦ h.of_mulEquiv e he⟩
  rw [← he, e.apply_symm_apply]

variable {G A B} in
@[simp]
theorem top_iff : IsGaloisGroup (⊤ : Subgroup G) A B ↔ IsGaloisGroup G A B :=
  iff_of_mulEquiv Subgroup.topEquiv fun _ _ ↦ rfl

instance [IsGaloisGroup G A B] : IsGaloisGroup (⊤ : Subgroup G) A B :=
  IsGaloisGroup.top_iff.mpr ‹_›

theorem of_algEquiv [hG : IsGaloisGroup G A B] (B' : Type*) [Semiring B']
    [Algebra A B'] [MulSemiringAction G B'] (e : B ≃ₐ[A] B')
    (he : ∀ (g : G) (x : B), e (g • x) = g • (e x)) :
    IsGaloisGroup G A B' where
  faithful := ⟨fun h ↦ hG.faithful.eq_of_smul_eq_smul fun b ↦ by simpa [← he] using h (e b)⟩
  commutes := ⟨fun g a b' ↦ by
    have h' {x'} : e.symm (g • x') = g • e.symm x' := by
      apply e.injective
      simp [he]
    apply e.symm.injective
    simpa [h', map_smul] using hG.commutes.smul_comm g a (e.symm b')⟩
  isInvariant := ⟨fun x' hx' ↦ by
    obtain ⟨a, ha⟩ := hG.isInvariant.isInvariant (e.symm x') (fun g ↦ by
      apply e.injective
      simp [he, hx'])
    exact ⟨a, by rw [← e.commutes, ha, AlgEquiv.apply_symm_apply]⟩⟩

theorem of_ringHom_surjective [hG : IsGaloisGroup G A B] [CommSemiring A']
    [Algebra A' B] (e : A →+* A') (he : ∀ a, algebraMap A' B (e a) = algebraMap A B a)
    (he' : Function.Surjective e) : IsGaloisGroup G A' B where
  faithful := hG.faithful
  commutes := ⟨by
    intro g a' b
    obtain ⟨a, rfl⟩ : ∃ a, e a = a' := he' a'
    rw [Algebra.smul_def, Algebra.smul_def, he, ← Algebra.smul_def, ← Algebra.smul_def]
    exact hG.commutes.smul_comm g a b⟩
  isInvariant := ⟨by
    intro b h
    obtain ⟨a, ha⟩ := hG.isInvariant.isInvariant b h
    exact ⟨e a, by rw [he, ha]⟩⟩

theorem of_ringEquiv [hG : IsGaloisGroup G A B] [CommSemiring A'] [Algebra A' B]
    (e : A ≃+* A') (he : ∀ a, algebraMap A' B (e a) = algebraMap A B a) :
    IsGaloisGroup G A' B :=
  .of_ringHom_surjective G A A' B e he e.surjective

attribute [instance low] IsGaloisGroup.commutes IsGaloisGroup.isInvariant

variable [hA : IsGaloisGroup G A B] [FaithfulSMul A B]

/-- If `B/A` is Galois with Galois group `G`, then `A` is isomorphic to the subring of elements of
`B` fixed by `G`. -/
@[simps apply_coe]
noncomputable def ringEquivFixedPoints :
    A ≃+* FixedPoints.subsemiring B G where
  toFun x := ⟨algebraMap A B x, fun _ ↦ by rw [smul_algebraMap]⟩
  invFun x := (hA.isInvariant.isInvariant x x.prop).choose
  map_mul' _ _ := by simp [Subtype.ext_iff]
  map_add' _ _ := by simp [Subtype.ext_iff]
  left_inv _ := by simp
  right_inv x := by simpa [Subtype.ext_iff] using (hA.isInvariant.isInvariant x x.prop).choose_spec

@[simp]
theorem algebraMap_ringEquivFixedPoints_symm_apply (x : FixedPoints.subsemiring B G) :
    algebraMap A B ((ringEquivFixedPoints G A B).symm x) = x :=
 (hA.isInvariant.isInvariant x x.prop).choose_spec

variable [CommSemiring A'] [Algebra A' B] [FaithfulSMul A' B] [hA' : IsGaloisGroup G A' B]

/-- If `B/A` and `B/A'` are Galois with the same Galois group, then `A ≃+* A'`. -/
noncomputable def ringEquiv : A ≃+* A' :=
  (ringEquivFixedPoints G A B).trans (ringEquivFixedPoints G A' B).symm

@[simp]
theorem algebraMap_ringEquiv_apply (x : A) :
    algebraMap A' B (IsGaloisGroup.ringEquiv G A A' B x) = algebraMap A B x := by
  simp [ringEquiv]

@[simp]
theorem algebraMap_ringEquiv_symm_apply (x : A') :
    algebraMap A B ((IsGaloisGroup.ringEquiv G A A' B).symm x) = algebraMap A' B x := by
  simp [ringEquiv]

end IsGaloisGroup
