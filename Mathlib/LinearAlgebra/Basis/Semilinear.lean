/-
Copyright (c) 2023 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.LinearAlgebra.Basis
import Mathlib.RingTheory.Ideal.Operations

/-!
# Mapping a basis through a semilinear map
-/

/-
/-- If we have a basis on an `R`-module `M`,
and we take the quotient of `R` and `M` by "the same thing" `p`,
then we get an `R/p`-basis of `M/p`. -/
def Basis.compSemilinear {ι R S M N : Type _} [Semiring R] [Semiring S]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]
    (g : R →+* S) (g' : ZeroHom S R) (hg : Function.RightInverse g' g)
    (f : M →ₛₗ[g] N) (f' : N → M) (hf : Function.RightInverse f' f)
    (h : sorry)
    (b : Basis ι R M) : Basis ι S N where
  repr := -- LinearEquiv.symm <|
  { toFun := fun x => Finsupp.mapRange g (map_zero g) (b.repr (f' x))
    invFun := fun x => f (b.repr.symm (Finsupp.mapRange g' (map_zero g') x))
    map_add' := by
      intros x y
      ext i
      simp?
      obtain ⟨x', rfl⟩ := hf.surjective x
      obtain ⟨y', rfl⟩ := hf.surjective y
      rw [← f.map_add, hf]
      sorry
    map_smul' := by
      intros c x
      sorry
    left_inv := by
      intros x
      sorry
    right_inv := by
      intros x
      sorry }
-/

variable {ι R S M N : Type _} [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N] (g : R →+* S) (g' : ZeroHom S R) (hg : Function.RightInverse g' g) [RingHomSurjective g] (f : M →ₛₗ[g] N) (f' : N → M) (hf : Function.RightInverse f' f)

theorem Finsupp.apply_total' (f : M →ₛₗ[g] N) (v) (l : α →₀ R) :
    f (Finsupp.total α M R v l) = Finsupp.total α N S (f ∘ v) (l.mapRange g (map_zero g)) := by
  apply Finsupp.induction_linear l
  case h0 => simp (config := { contextual := true })
  case hsingle => simp (config := { contextual := true })
  case hadd =>
    intros x y hx hy
    rw [map_add, map_add, hx, hy, mapRange_add, map_add]
    · apply map_add

/-- If `v` is a linearly independent family of vectors and the kernel of a semilinear map `f` is
disjoint with the submodule spanned by the vectors of `v`, then `f ∘ v` is a linearly independent
family of vectors. See also `LinearIndependent.mapₛₗ'` for a special case assuming `ker f = ⊥`. -/
theorem LinearIndependent.mapₛₗ {v : ι → M} (hv : LinearIndependent R v) {f : M →ₛₗ[g] N}
    (hf_inj : Submodule.comap (Finsupp.total ι M R v) (LinearMap.ker f) ≤ RingHom.ker g • ⊤) :
    LinearIndependent S (f ∘ v) := by
  unfold LinearIndependent at hv ⊢
  haveI : Inhabited M := ⟨0⟩
  rw [← le_bot_iff, Finsupp.total_comp]
  intros x hx
  let x' : ι →₀ R := x.mapRange g' (map_zero g')
  have x_eq : x = x'.mapRange g (map_zero g)
  · ext i
    rw [Finsupp.mapRange_apply, Finsupp.mapRange_apply, hg]
  suffices : ∀ i, x' i ∈ RingHom.ker g
  · rw [Submodule.mem_bot, x_eq]
    ext i
    rw [Finsupp.mapRange_apply, Finsupp.zero_apply, ← RingHom.mem_ker]
    apply this
  rw [x_eq, LinearMap.mem_ker, LinearMap.comp_apply,
      -- TODO: turn the next line into its own lemma
      Finsupp.lmapDomain_apply, Finsupp.total_mapDomain, ← Finsupp.apply_total' g f, ← LinearMap.comp_apply,
      ← LinearMap.mem_ker, LinearMap.ker_comp] at hx
  refine Submodule.smul_induction_on (hf_inj hx) ?_ ?_
  · intros r hr x _ i
    rw [Finsupp.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hr
  · intros x y hx hy i
    rw [Finsupp.add_apply]
    exact add_mem (hx i) (hy i)

theorem Submodule.finsupp_mem_smul_top (x : ι →₀ R) (I : Ideal R)
    (h : ∀ i, x i ∈ I) : x ∈ (I • ⊤ : Submodule R (ι →₀ R)) := by
  induction x using Finsupp.induction
  case _ => apply zero_mem
  case _ i b x' hix' _ ih =>
    refine add_mem ?_ (ih ?_)
    · specialize h i
      rw [← Finsupp.smul_single_one]
      rw [Finsupp.add_apply, Finsupp.not_mem_support_iff.mp hix', add_zero, Finsupp.single_eq_same] at h
      exact Submodule.smul_mem_smul h mem_top
    · intro j
      by_cases hij : i = j
      · subst hij
        rw [Finsupp.not_mem_support_iff.mp hix']
        apply zero_mem
      specialize h j
      rwa [Finsupp.add_apply, Finsupp.single_eq_of_ne hij, zero_add] at h

/-- If `v` is a linearly independent family of vectors and the kernel of a semilinear map `f` is
disjoint with the submodule spanned by the vectors of `v`, then `f ∘ v` is a linearly independent
family of vectors. See also `LinearIndependent.mapₛₗ'` for a special case assuming `ker f = ⊥`. -/
theorem LinearIndependent.mapₛₗ' {v : ι → M} (hv : LinearIndependent R v) {f : M →ₛₗ[g] N}
    (hf_inj : LinearMap.ker f ≤ RingHom.ker g • ⊤) :
    LinearIndependent S (f ∘ v) := by
  apply hv.mapₛₗ g g' hg
  intros x hx
  apply Submodule.finsupp_mem_smul_top
  intro i
  rw [Submodule.mem_comap] at hx
  -- Is this even true?

/-- If we have a basis on an `R`-module `M`,
and we take the quotient of `R` and `M` by "the same thing" `p`,
then we get an `R/p`-basis of `M/p`. -/
noncomputable def Basis.compSemilinear {ι R S M N : Type _} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (g : R →+* S) (g' : ZeroHom S R) (hg : Function.RightInverse g' g)
    [RingHomSurjective g]
    (f : M →ₛₗ[g] N) (f' : N → M) (hf : Function.RightInverse f' f)
    (b : Basis ι R M)
    (h : LinearMap.ker f ≤ RingHom.ker g • ⊤) : Basis ι S N :=
  Basis.mk (v := f ∘ b)
    (LinearIndependent.mapₛₗ' g g' hg b.linearIndependent h)
    (by rw [top_le_iff, Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_top, LinearMap.range_eq_top]
        exact hf.surjective)

#print Basis.compSemilinear
