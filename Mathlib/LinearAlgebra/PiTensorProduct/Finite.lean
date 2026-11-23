/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.RingTheory.Finiteness.Basic

import Mathlib.LinearAlgebra.PiTensorProduct.Generators

/-!
# A multiple tensor product of finitely generated modules is finitely generated
-/

public section

open TensorProduct

namespace PiTensorProduct

/-- The tensor product `⨂[R] i, M i` of a finite collection of finite modules `M i` over a
`CommSemiring` is finite.
-/
instance finite {R : Type*} [CommSemiring R] {ι : Type*} [Finite ι] {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, Module.Finite R (M i)] :
    Module.Finite R (⨂[R] i, M i) := by
  choose n γ hg using fun i => Module.Finite.exists_fin (R := R) (M := M i)
  rw [Module.finite_def, ← submodule_span_eq_top hg]
  exact Submodule.fg_span (Set.finite_range _)

open Submodule in
/-- For a finite subset `s` of `⨂[R] i, E i`, there exist finitely generated submodules `p i ⊆ E i`
such that `s` is contained in the image of `Π i, p i` in `⨂[R] i, E i`.

In particular, every element of a tensor product lies in the tensor product of some finite
submodules.

This is `TensorProduct.exists_finite_submodule_of_setFinite` for an arbitrary family of modules.
-/
theorem exists_finite_submodule_of_setFinite {R ι : Type*} [CommSemiring R] {E : ι → Type*}
    [∀ i, AddCommMonoid (E i)] [∀ i, Module R (E i)] (s : Set (⨂[R] i, E i)) (hs : s.Finite) :
    ∃ (p : Π i, Submodule R (E i)), (∀ i, Module.Finite R (p i)) ∧ s ⊆ (mapIncl p).range := by
  simp_rw [Module.Finite.iff_fg]
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨fun _ ↦ ⊥, fun _ ↦ fg_bot, Set.empty_subset _⟩
  | @insert x s hx _ ih =>
    obtain ⟨p', hp', hsp'⟩ := ih
    refine x.induction_on (fun r u ↦ ?_) fun y z hy hz ↦ ?_
    · refine ⟨fun i ↦ p' i ⊔ R ∙ u i, fun i ↦ (hp' i).sup (fg_span_singleton _), ?_⟩
      apply Set.insert_subset
      · exact ⟨r • ⨂ₜ[R] i, ⟨u i, mem_sup_right (mem_span_singleton_self _)⟩, by simp⟩
      · exact fun y hy ↦ range_mapIncl_mono (fun _ ↦ le_sup_left) (hsp' hy)
    · obtain ⟨py', hpy', hys⟩ := hy
      obtain ⟨pz', hpz', hzs⟩ := hz
      refine ⟨fun i ↦ py' i ⊔ pz' i, fun i ↦ (hpy' i).sup (hpz' i), ?_⟩
      refine Set.insert_subset (add_mem ?_ ?_) fun w hw ↦ ?_
      · exact range_mapIncl_mono (fun _ ↦ le_sup_left) (hys <| Set.mem_insert y s)
      · exact range_mapIncl_mono (fun _ ↦ le_sup_right) (hzs <| Set.mem_insert z s)
      · exact range_mapIncl_mono (fun _ ↦ le_sup_right) (hzs <| Set.mem_insert_of_mem z hw)

end PiTensorProduct
