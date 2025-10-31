/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Exact
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Projection

/-!
# Basis from a split exact sequence

Let `0 → K → M → P → 0` be a split exact sequence of `R`-modules, let `s : M → K` be a
retraction of `f` and `v` be a basis of `M` indexed by `κ ⊕ σ`. Then
if `s vᵢ = 0` for `i : κ` and `(s vⱼ)ⱼ` is linear independent for `j : σ`, then
the images of `vᵢ` for `i : κ` form a basis of `P`.

We treat linear independence and the span condition separately. For convenience this
is stated not for `κ ⊕ σ`, but for an arbitrary type `ι` with two maps `κ → ι` and `σ → ι`.
-/

variable {R M K P : Type*} [Ring R] [AddCommGroup M] [AddCommGroup K] [AddCommGroup P]
variable [Module R M] [Module R K] [Module R P]
variable {f : K →ₗ[R] M} {g : M →ₗ[R] P} {s : M →ₗ[R] K}
variable (hs : s ∘ₗ f = LinearMap.id) (hfg : Function.Exact f g)
variable {ι κ σ : Type*} {v : ι → M} {a : κ → ι} {b : σ → ι}

section
include hs hfg

lemma LinearIndependent.linearIndependent_of_exact_of_retraction
    (hainj : Function.Injective a) (hsa : ∀ i, s (v (a i)) = 0)
    (hli : LinearIndependent R v) :
    LinearIndependent R (g ∘ v ∘ a) := by
  apply (LinearIndependent.comp hli a hainj).map
  rw [Submodule.disjoint_def, hfg.linearMap_ker_eq]
  rintro - hy ⟨y, rfl⟩
  have hz : s (f y) = 0 := by
    revert hy
    generalize f y = x
    intro hy
    induction hy using Submodule.span_induction with
    | mem m hm => obtain ⟨i, rfl⟩ := hm; apply hsa
    | zero => simp_all
    | add => simp_all
    | smul => simp_all
  replace hs := DFunLike.congr_fun hs y
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at hs
  rw [← hs, hz, map_zero]

private lemma top_le_span_of_aux (v : κ ⊕ σ → M)
    (hg : Function.Surjective g) (hslzero : ∀ i, s (v (.inl i)) = 0)
    (hli : LinearIndependent R (s ∘ v ∘ .inr)) (hsp : ⊤ ≤ Submodule.span R (Set.range v)) :
    ⊤ ≤ Submodule.span R (Set.range <| g ∘ v ∘ .inl) := by
  rintro p -
  obtain ⟨m, rfl⟩ := hg p
  wlog h : m ∈ LinearMap.ker s
  · let x : M := f (s m)
    rw [show g m = g (m - f (s m)) by simp [hfg.apply_apply_eq_zero]]
    apply this hs hfg v hg hslzero hli hsp
    replace hs := DFunLike.congr_fun hs (s m)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at hs
    simp [hs]
  have : m ∈ Submodule.span R (Set.range v) := hsp Submodule.mem_top
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp this
  simp only [LinearMap.mem_ker, Finsupp.sum, map_sum, map_smul,
    Finset.sum_sum_eq_sum_toLeft_add_sum_toRight, map_add, hslzero, smul_zero,
    Finset.sum_const_zero, zero_add] at h
  replace hli := (linearIndependent_iff'.mp hli) c.support.toRight (c ∘ .inr) h
  simp only [Finset.mem_toRight, Finsupp.mem_support_iff, Function.comp_apply, not_imp_self] at hli
  simp only [Finsupp.sum, Finset.sum_sum_eq_sum_toLeft_add_sum_toRight, hli, zero_smul,
    Finset.sum_const_zero, add_zero, map_sum, map_smul]
  exact Submodule.sum_mem _ (fun i hi ↦ Submodule.smul_mem _ _ <| Submodule.subset_span ⟨i, rfl⟩)

lemma Submodule.top_le_span_of_exact_of_retraction (hg : Function.Surjective g)
    (hsa : ∀ i, s (v (a i)) = 0) (hlib : LinearIndependent R (s ∘ v ∘ b))
    (hab : Codisjoint (Set.range a) (Set.range b))
    (hsp : ⊤ ≤ Submodule.span R (Set.range v)) :
    ⊤ ≤ Submodule.span R (Set.range <| g ∘ v ∘ a) := by
  apply top_le_span_of_aux hs hfg (Sum.elim (v ∘ a) (v ∘ b)) hg hsa hlib
  simp only [codisjoint_iff, Set.sup_eq_union, Set.top_eq_univ] at hab
  rwa [Set.Sum.elim_range, Set.range_comp, Set.range_comp, ← Set.image_union, hab, Set.image_univ]

/-- Let `0 → K → M → P → 0` be a split exact sequence of `R`-modules, let `s : M → K` be a
retraction of `f` and `v` be a basis of `M` indexed by `κ ⊕ σ`. Then
if `s vᵢ = 0` for `i : κ` and `(s vⱼ)ⱼ` is linear independent for `j : σ`, then
the images of `vᵢ` for `i : κ` form a basis of `P`.

For convenience this is stated for an arbitrary type `ι` with two maps `κ → ι` and `σ → ι`. -/
noncomputable def Module.Basis.ofSplitExact (hg : Function.Surjective g) (v : Basis ι R M)
    (hainj : Function.Injective a) (hsa : ∀ i, s (v (a i)) = 0)
    (hlib : LinearIndependent R (s ∘ v ∘ b))
    (hab : Codisjoint (Set.range a) (Set.range b)) :
    Basis κ R P :=
  .mk (v.linearIndependent.linearIndependent_of_exact_of_retraction hs hfg hainj hsa)
    (Submodule.top_le_span_of_exact_of_retraction hs hfg hg hsa hlib hab (by rw [v.span_eq]))

end

section
include hfg

lemma Submodule.linearProjOfIsCompl_comp_surjective_of_exact
    {p q : Submodule R M} (hpq : IsCompl p q)
    (hmap : Submodule.map g q = ⊤) :
    Function.Surjective (Submodule.linearProjOfIsCompl p q hpq ∘ₗ f) := by
  rw [Set.surjective_iff_surjOn_univ, LinearMap.coe_comp, Set.surjOn_comp_iff, Set.image_univ]
  rw [← LinearMap.coe_range, ← Submodule.top_coe (R := R), LinearMap.surjOn_iff_le_map,
    ← hfg.linearMap_ker_eq]
  intro x triv
  obtain ⟨a, haq, ha⟩ : g x.val ∈ q.map g := by rwa [hmap]
  exact ⟨x - a, by simp [← ha], by simpa⟩

lemma Submodule.linearProjOfIsCompl_comp_bijective_of_exact
    (hf : Function.Injective f) {p q : Submodule R M} (hpq : IsCompl p q)
    (hker : Disjoint (LinearMap.ker g) q) (hmap : Submodule.map g q = ⊤) :
    Function.Bijective (Submodule.linearProjOfIsCompl p q hpq ∘ₗ f) := by
  refine ⟨?_, Submodule.linearProjOfIsCompl_comp_surjective_of_exact hfg _ hmap⟩
  rwa [LinearMap.coe_comp, Set.InjOn.injective_iff ↑(LinearMap.range f) _ subset_rfl]
  simpa [← LinearMap.disjoint_ker_iff_injOn, ← hfg.linearMap_ker_eq]

lemma LinearMap.linearProjOfIsCompl_comp_bijective_of_exact
    (hf : Function.Injective f) {q : Submodule R M} {E : Type*} [AddCommGroup E] [Module R E]
    {i : E →ₗ[R] M} (hi : Function.Injective i) (h : IsCompl (LinearMap.range i) q)
    (hker : Disjoint (LinearMap.ker g) q) (hmap : Submodule.map g q = ⊤) :
    Function.Bijective (LinearMap.linearProjOfIsCompl q i hi h ∘ₗ f) := by
  rw [LinearMap.linearProjOfIsCompl, LinearMap.comp_assoc, LinearMap.coe_comp,
      Function.Bijective.of_comp_iff]
  · exact (LinearEquiv.ofInjective i hi).symm.bijective
  · exact Submodule.linearProjOfIsCompl_comp_bijective_of_exact hfg hf h hker hmap

end
