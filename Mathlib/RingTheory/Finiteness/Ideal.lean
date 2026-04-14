/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Finitely generated ideals

Lemmas about finiteness of ideal operations.
-/

public section

namespace Ideal

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- The image of a finitely generated ideal is finitely generated.

This is the `Ideal` version of `Submodule.FG.map`. -/
theorem FG.map {R S : Type*} [Semiring R] [Semiring S] {I : Ideal R} (h : I.FG) (f : R →+* S) :
    (I.map f).FG := by
  classical
    obtain ⟨s, hs⟩ := h
    refine ⟨s.image f, ?_⟩
    rw [Finset.coe_image, ← map_span, hs]

theorem fg_ker_comp {R S A : Type*} [CommRing R] [CommRing S] [CommRing A] (f : R →+* S)
    (g : S →+* A) (hf : (RingHom.ker f).FG) (hg : (RingHom.ker g).FG)
    (hsur : Function.Surjective f) :
    (RingHom.ker (g.comp f)).FG := by
  letI : Algebra R S := RingHom.toAlgebra f
  letI : Algebra R A := RingHom.toAlgebra (g.comp f)
  letI : Algebra S A := RingHom.toAlgebra g
  letI : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f₁ := Algebra.linearMap R S
  let g₁ := (IsScalarTower.toAlgHom R S A).toLinearMap
  exact Submodule.fg_ker_comp f₁ g₁ hf
    (Submodule.FG.restrictScalars_of_surjective hg hsur) hsur

/-- Let `f : R →+* S` be a surjective ring homomorphism, and let `I` be an ideal of `R`. If `f(I)`
and `I ∩ ker(f)` are finitely generated ideals, then `I` is also finitely generated. -/
theorem fg_of_fg_map_of_fg_inf_ker_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    {f : R →+* S} {I : Ideal R} (hmap : (I.map f).FG) (hk : (I ⊓ (RingHom.ker f)).FG)
    (hf : Function.Surjective f) : I.FG := by
  algebraize [f]
  have h : Submodule.map (Module.compHom.toLinearMap f) I = (I.map f).restrictScalars R := by
    ext
    have : RingHomSurjective f := ⟨hf⟩
    simp [map_eq_submodule_map]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker (Module.compHom.toLinearMap f) ?_ hk
  simpa [h] using Submodule.FG.restrictScalars_of_surjective hmap hf

theorem exists_radical_pow_le_of_fg {R : Type*} [CommSemiring R] (I : Ideal R) (h : I.radical.FG) :
    ∃ n : ℕ, I.radical ^ n ≤ I := by
  have := le_refl I.radical
  revert this
  refine Submodule.fg_induction _ _ (fun J => J ≤ I.radical → ∃ n : ℕ, J ^ n ≤ I) ?_ ?_ _ h
  · intro x hx
    obtain ⟨n, hn⟩ := hx (subset_span (Set.mem_singleton x))
    exact ⟨n, by rwa [← span, span_singleton_pow, span_le, Set.singleton_subset_iff]⟩
  · intro J K hJ hK hJK
    obtain ⟨n, hn⟩ := hJ fun x hx => hJK <| mem_sup_left hx
    obtain ⟨m, hm⟩ := hK fun x hx => hJK <| mem_sup_right hx
    use n + m
    rw [← add_eq_sup, add_pow, sum_eq_sup, Finset.sup_le_iff]
    refine fun i _ => mul_le_right.trans ?_
    obtain h | h := le_or_gt n i
    · exact mul_le_right.trans ((pow_le_pow_right h).trans hn)
    · exact mul_le_left.trans ((pow_le_pow_right (by lia)).trans hm)

theorem exists_pow_le_of_le_radical_of_fg_radical {R : Type*} [CommSemiring R] {I J : Ideal R}
    (hIJ : I ≤ J.radical) (hJ : J.radical.FG) :
    ∃ k : ℕ, I ^ k ≤ J := by
  obtain ⟨k, hk⟩ := J.exists_radical_pow_le_of_fg hJ
  exact ⟨k, (pow_right_mono hIJ k).trans hk⟩

lemma exists_pow_le_of_le_radical_of_fg {R : Type*} [CommSemiring R] {I J : Ideal R}
    (h' : I ≤ J.radical) (h : I.FG) :
    ∃ n : ℕ, I ^ n ≤ J := by
  revert h'
  apply Submodule.fg_induction _ _ _ _ _ I h
  · intro x hJ
    simp only [submodule_span_eq, span_le, Set.singleton_subset_iff, SetLike.mem_coe] at hJ
    obtain ⟨n, hn⟩ := hJ
    refine ⟨n, by simpa [span_singleton_pow, span_le]⟩
  · intro I₁ I₂ h₁ h₂ hJ
    obtain ⟨n₁, hn₁⟩ := h₁ (le_sup_left.trans hJ)
    obtain ⟨n₂, hn₂⟩ := h₂ (le_sup_right.trans hJ)
    use n₁ + n₂
    exact sup_pow_add_le_pow_sup_pow.trans (sup_le hn₁ hn₂)

theorem _root_.Submodule.FG.smul {I : Ideal R} [I.IsTwoSided] {N : Submodule R M}
    (hI : I.FG) (hN : N.FG) : (I • N).FG := by
  obtain ⟨s, rfl⟩ := hI
  obtain ⟨t, rfl⟩ := hN
  classical rw [Submodule.span_smul_span, ← s.coe_smul]
  exact ⟨_, rfl⟩

theorem FG.mul {I J : Ideal R} [I.IsTwoSided] (hI : I.FG) (hJ : J.FG) : (I * J).FG :=
  Submodule.FG.smul hI hJ

theorem FG.pow {I : Ideal R} [I.IsTwoSided] {n : ℕ} (hI : I.FG) : (I ^ n).FG :=
  n.rec (by rw [I.pow_zero, one_eq_top]; exact fg_top R) fun n ih ↦ by
    rw [IsTwoSided.pow_succ]
    exact hI.mul ih

end Ideal
