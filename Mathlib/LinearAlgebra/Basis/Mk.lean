/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Bases as linear independent families spanning the whole space

This file shows the equivalence between bases and families of vectors that are
linearly independent and whose span is the whole space.

## Main results

* `Basis.linearIndependent`: the basis vectors are linear independent.
* `Basis.span_eq`: the basis vectors span the whole space.
* `Basis.mk`: construct a basis out of `v : ι → M` such that `LinearIndependent v` and
  `span (range v) = ⊤`.
-/

assert_not_exists Ordinal

noncomputable section

universe u

open Function Set Submodule Finsupp

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

section Module

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

namespace Basis

variable (b : Basis ι R M)

section Properties

theorem repr_range : LinearMap.range (b.repr : M →ₗ[R] ι →₀ R) = Finsupp.supported R R univ := by
  rw [LinearEquiv.range, Finsupp.supported_univ]

theorem mem_span_repr_support (m : M) : m ∈ span R (b '' (b.repr m).support) :=
  (Finsupp.mem_span_image_iff_linearCombination _).2
    ⟨b.repr m, by simp [Finsupp.mem_supported_support]⟩

theorem repr_support_subset_of_mem_span (s : Set ι) {m : M}
    (hm : m ∈ span R (b '' s)) : ↑(b.repr m).support ⊆ s := by
  rcases (Finsupp.mem_span_image_iff_linearCombination _).1 hm with ⟨l, hl, rfl⟩
  rwa [repr_linearCombination, ← Finsupp.mem_supported R l]

theorem mem_span_image {m : M} {s : Set ι} : m ∈ span R (b '' s) ↔ ↑(b.repr m).support ⊆ s :=
  ⟨repr_support_subset_of_mem_span _ _, fun h ↦
    span_mono (image_subset _ h) (mem_span_repr_support b _)⟩

@[simp]
theorem self_mem_span_image [Nontrivial R] {i : ι} {s : Set ι} :
    b i ∈ span R (b '' s) ↔ i ∈ s := by
  simp [mem_span_image, Finsupp.support_single_ne_zero]

protected theorem mem_span (x : M) : x ∈ span R (range b) :=
  span_mono (image_subset_range _ _) (mem_span_repr_support b x)

@[simp]
protected theorem span_eq : span R (range b) = ⊤ :=
  eq_top_iff.mpr fun x _ => b.mem_span x

theorem index_nonempty (b : Basis ι R M) [Nontrivial M] : Nonempty ι := by
  obtain ⟨x, y, ne⟩ : ∃ x y : M, x ≠ y := Nontrivial.exists_pair_ne
  obtain ⟨i, _⟩ := not_forall.mp (mt b.ext_elem_iff.2 ne)
  exact ⟨i⟩

protected theorem linearIndependent : LinearIndependent R b :=
  fun x y hxy => by
    rw [← b.repr_linearCombination x, hxy, b.repr_linearCombination y]

protected theorem ne_zero [Nontrivial R] (i) : b i ≠ 0 :=
  b.linearIndependent.ne_zero i

end Properties

variable {v : ι → M} {x y : M}

section Mk

variable (hli : LinearIndependent R v) (hsp : ⊤ ≤ span R (range v))

/-- A linear independent family of vectors spanning the whole module is a basis. -/
protected noncomputable def mk : Basis ι R M :=
  .ofRepr
    { hli.repr.comp (LinearMap.id.codRestrict _ fun _ => hsp Submodule.mem_top) with
      invFun := Finsupp.linearCombination _ v
      left_inv := fun x => hli.linearCombination_repr ⟨x, _⟩
      right_inv := fun _ => hli.repr_eq rfl }

@[simp]
theorem mk_repr : (Basis.mk hli hsp).repr x = hli.repr ⟨x, hsp Submodule.mem_top⟩ :=
  rfl

theorem mk_apply (i : ι) : Basis.mk hli hsp i = v i :=
  show Finsupp.linearCombination _ v _ = v i by simp

@[simp]
theorem coe_mk : ⇑(Basis.mk hli hsp) = v :=
  funext (mk_apply _ _)

end Mk

section Span

variable (hli : LinearIndependent R v)

/-- A linear independent family of vectors is a basis for their span. -/
protected noncomputable def span : Basis ι R (span R (range v)) :=
  Basis.mk (linearIndependent_span hli) <| by
    intro x _
    have : ∀ i, v i ∈ span R (range v) := fun i ↦ subset_span (Set.mem_range_self _)
    have h₁ : (((↑) : span R (range v) → M) '' range fun i => ⟨v i, this i⟩) = range v := by
      simp only [SetLike.coe_sort_coe, ← Set.range_comp]
      rfl
    have h₂ : map (Submodule.subtype (span R (range v))) (span R (range fun i => ⟨v i, this i⟩)) =
        span R (range v) := by
      rw [← span_image, Submodule.coe_subtype, h₁]
    have h₃ : (x : M) ∈ map (Submodule.subtype (span R (range v)))
        (span R (Set.range fun i => Subtype.mk (v i) (this i))) := by
      rw [h₂]
      apply Subtype.mem x
    rcases mem_map.1 h₃ with ⟨y, hy₁, hy₂⟩
    have h_x_eq_y : x = y := by
      rw [Subtype.ext_iff, ← hy₂]
      simp
    rwa [h_x_eq_y]

protected theorem span_apply (i : ι) : (Basis.span hli i : M) = v i :=
  congr_arg ((↑) : span R (range v) → M) <| Basis.mk_apply _ _ _

end Span

/-- Any basis is a maximal linear independent set.
-/
theorem maximal [Nontrivial R] (b : Basis ι R M) : b.linearIndependent.Maximal := fun w hi h => by
  -- If `w` is strictly bigger than `range b`,
  apply le_antisymm h
  -- then choose some `x ∈ w \ range b`,
  intro x p
  by_contra q
  -- and write it in terms of the basis.
  have e := b.linearCombination_repr x
  -- This then expresses `x` as a linear combination
  -- of elements of `w` which are in the range of `b`,
  let u : ι ↪ w :=
    ⟨fun i => ⟨b i, h ⟨i, rfl⟩⟩, fun i i' r =>
      b.injective (by simpa only [Subtype.mk_eq_mk] using r)⟩
  simp_rw [Finsupp.linearCombination_apply] at e
  change ((b.repr x).sum fun (i : ι) (a : R) ↦ a • (u i : M)) = ((⟨x, p⟩ : w) : M) at e
  rw [← Finsupp.sum_embDomain (f := u) (g := fun x r ↦ r • (x : M)),
      ← Finsupp.linearCombination_apply] at e
  -- Now we can contradict the linear independence of `hi`
  refine hi.linearCombination_ne_of_not_mem_support _ ?_ e
  simp only [Finset.mem_map, Finsupp.support_embDomain]
  rintro ⟨j, -, W⟩
  simp only [u, Embedding.coeFn_mk, Subtype.mk_eq_mk] at W
  apply q ⟨j, W⟩

end Basis

end Module
