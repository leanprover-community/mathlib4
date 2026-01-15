/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Pi

/-!
# The algebraic dual of a submodule

Given a bilinear pairing `p` between two `R`-modules `M` and `N` and a set `s` in `M`, we define
`Submodule.dual p s` to be the submodule in `N` consisting of all points `y` such that
`0 = p x y` for all `x ∈ s`.

-/

@[expose] public section

assert_not_exists TopologicalSpace Real -- Cardinal (comes with BilinearMap)

open Module Function LinearMap Pointwise Set OrderDual

namespace Submodule

variable {R M N : Type*}
  [CommSemiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  {p : M →ₗ[R] N →ₗ[R] R} {s t : Set M} {y : N}

variable (p s) in
/-- The dual span of a set `s` with respect to a bilinear pairing `p` is the submodule
  consisting of the points `y` such that for all points `x ∈ s` we have `0 = p x y`. -/
def dual : Submodule R N where
  carrier := {y | ∀ ⦃x⦄, x ∈ s → 0 = p x y}
  zero_mem' := by simp
  add_mem' {u v} hu hv x hx := by rw [map_add, ← hu hx, ← hv hx, add_zero]
  smul_mem' c y hy x hx := by rw [map_smul, ← hy hx, smul_eq_mul, mul_zero]

@[simp] lemma mem_dual : y ∈ dual p s ↔ ∀ ⦃x⦄, x ∈ s → 0 = p x y := .rfl

@[simp] lemma dual_empty : dual p ∅ = ⊤ := by ext; simp
@[simp] lemma dual_zero : dual p 0 = ⊤ := by ext; simp
@[simp] lemma dual_bot : dual p {0} = ⊤ := dual_zero
@[simp] lemma dual_ker : dual p (ker p) = ⊤ := by ext; simp +contextual

lemma dual_univ_ker : dual p univ = ker p.flip := by
  ext x; simpa [Eq.comm] using (funext_iff (f := (0 : M →ₗ[R] R)) (g := p.flip x)).symm

lemma dual_flip_univ_ker : dual p.flip univ = ker p := by
  nth_rw 2 [← flip_flip p]; exact dual_univ_ker

@[gcongr] lemma dual_le_dual (h : t ⊆ s) : dual p s ≤ dual p t := fun _y hy _x hx ↦ hy (h hx)

alias dual_anti := dual_le_dual

lemma dual_antitone : Antitone (dual p) := fun _ _ h => dual_le_dual h

lemma ker_le_dual (s : Set M) : ker p.flip ≤ dual p s := by
  simp [← dual_flip_univ_ker, dual_anti]

lemma ker_le_dual_flip (s : Set N) : ker p ≤ dual p.flip s := by
  simp [← dual_flip_univ_ker, dual_anti]

/-- The inner dual cone of a singleton is given by the preimage of the positive cone under the
linear map `p x`. -/
lemma dual_singleton (x : M) : dual p {x} = ker (p x) := by
  ext x; simp [Eq.comm]

lemma dual_union (s t : Set M) : dual p (s ∪ t) = dual p s ⊓ dual p t := by aesop

variable (p) in
lemma dual_union_ker (s : Set M) : dual p (s ∪ ker p) = dual p s := by
  simp [dual_union]

lemma dual_insert (x : M) (s : Set M) : dual p (insert x s) = dual p {x} ⊓ dual p s := by
  rw [insert_eq, dual_union]

lemma dual_iUnion {ι : Sort*} (f : ι → Set M) : dual p (⋃ i, f i) = ⨅ i, dual p (f i) := by
  ext; simp [forall_swap (α := M)]

lemma dual_sUnion (S : Set (Set M)) : dual p (⋃₀ S) = sInf (dual p '' S) := by
  ext; simp [forall_swap (α := M)]

/-- The dual cone of `s` equals the intersection of dual cones of the points in `s`. -/
lemma dual_eq_iInter_dual_singleton (s : Set M) :
    dual p s = ⋂ i : s, (dual p {i.val} : Set N) := by ext; simp

/-- The dual cone of `s` equals the intersection of dual cones of the points in `s`. -/
lemma dual_eq_Inf_dual_singleton (s : Set M) :
    dual p s = ⨅ x ∈ s, dual p {x} := by ext; simp

/-- The dual cone of `s` equals the intersection of dual cones of the points in `s`. -/
lemma dual_eq_Inf_dual_singleton' (s : Finset M) :
    dual p s = ⨅ x ∈ s, dual p {x} := by ext; simp

lemma dual_singleton_ker (x : M) : dual p {x} = ker (p x) := by ext; simp [Eq.comm]

/-- The dual is the kernel of a linear map into a free module. -/
lemma dual_ker_pi (s : Set M) : dual p s = ker (LinearMap.pi fun x : s => p x) := by
  simp only [dual_eq_Inf_dual_singleton s, ker_pi, dual_singleton, ← sInf_image, sInf_image']

/-- The dual is the kernel of a linear map into a free module. -/
lemma dual_ker_pi' (s : Finset M) : dual p s = ker (LinearMap.pi fun x : s => p x) := by
  simp [dual_ker_pi]

/-- The dual is the kernel of a linear map into a free module. -/
lemma dual_exists_fun_ker (s : Set M) : ∃ f : N →ₗ[R] (s → R), dual p s = ker f
    := ⟨_, dual_ker_pi s⟩

/-- The dual is the kernel of a linear map into a free module. -/
lemma dual_exists_fun_ker' (s : Finset M) : ∃ f : N →ₗ[R] (s → R), dual p s = ker f
    := ⟨_, dual_ker_pi' s⟩

/-- Any set is a subset of its double dual cone. -/
lemma subset_dual_dual : s ⊆ dual p.flip (dual p s) := fun _x hx _y hy ↦ hy hx

alias le_dual_dual := subset_dual_dual

-- variable (p) in
-- /-- Any cone is a subcone of its double dual cone. -/
-- lemma le_dual_dual (S : Submodule R M) : S ≤ dual p.flip (dual p S) := subset_dual_dual

lemma le_dual_of_le_dual {S : Submodule R M} {T : Submodule R N}
    (hST : T ≤ dual p S) : S ≤ dual p.flip T :=
  le_trans subset_dual_dual (dual_antitone hST)

lemma le_dual_iff_le_dual {S : Submodule R M} {T : Submodule R N} :
    S ≤ dual p.flip T ↔ T ≤ dual p S := ⟨le_dual_of_le_dual, le_dual_of_le_dual⟩

variable (p) in
/-- Double duality is monotone. -/
lemma dual_dual_mono {s t : Set M} (hST : s ⊆ t) :
    dual p.flip (dual p s) ≤ dual p.flip (dual p t) := dual_antitone <| dual_antitone hST

variable (p) in
/-- Double duality is monotone. -/
lemma dual_dual_monotone : Monotone (dual p.flip ∘ SetLike.coe ∘ dual p) :=
  fun _ _ h => dual_antitone <| dual_antitone h

variable (s) in
@[simp] lemma dual_dual_flip_dual : dual p (dual p.flip (dual p s)) = dual p s :=
  le_antisymm (dual_le_dual subset_dual_dual) subset_dual_dual

@[simp] lemma dual_flip_dual_dual_flip (s : Set N) :
    dual p.flip (dual p (dual p.flip s)) = dual p.flip s := dual_dual_flip_dual _

@[simp]
lemma dual_span (s : Set M) : dual p (Submodule.span R s) = dual p s := by
  refine le_antisymm (dual_le_dual Submodule.subset_span) (fun x hx y hy => ?_)
  induction hy using Submodule.span_induction with
  | mem _y h => exact hx h
  | zero => simp
  | add y z _hy _hz hy hz => rw [map_add, add_apply, ← hy, ← hz, add_zero]
  | smul t y _hy hy => simp only [map_smul, smul_apply, smul_eq_mul, ← hy, mul_zero]

lemma dual_id (s : Set M) : dual p s = dual .id (p '' s) := by ext; simp

lemma dual_id_map (S : Submodule R M) : dual p S = dual .id (map p S) := by ext; simp

lemma dual_eval (s : Set M) :
    dual p s = comap p.flip (dual (Dual.eval R M) s) := by ext; simp

lemma dual_sup (S T : Submodule R M) : dual p (S ⊔ T : Submodule R M) = dual p (S ∪ T)
    := by sorry -- nth_rw 2 [← dual_span]; simp

lemma dual_sup_dual_inf_dual (S T : Submodule R M) :
    dual p (S ⊔ T : Submodule R M) = dual p S ⊓ dual p T := by rw [dual_sup, dual_union]

/-- The dual submodule w.r.t. the standard dual map is the dual annihilator. -/
lemma dual_dualAnnihilator (S : Submodule R M) : dual (Dual.eval R M) S = S.dualAnnihilator := by
  ext x; simpa using ⟨fun h _ hw => (h hw).symm, fun h w hw => (h w hw).symm⟩

variable (p) in
lemma dual_comap_dualAnnihilator (S : Submodule R M) :
    dual p S = comap p.flip S.dualAnnihilator := by rw [← dual_dualAnnihilator, dual_eval]

/-- The dual submodule w.r.t. the identity map is the dual coannihilator. -/
lemma dual_dualCoannihilator (S : Submodule R (Dual R M)) : dual .id S = S.dualCoannihilator := by
  ext x; simpa using ⟨fun h _ hw => (h hw).symm, fun h w hw => (h w hw).symm⟩

variable (p) in
lemma dual_map_dualCoannihilator (S : Submodule R M) : dual p S = (map p S).dualCoannihilator := by
  ext x; simpa using ⟨fun h _ hw => (h hw).symm, fun h w hw => (h w hw).symm⟩

lemma le_ker_of_mem_dualAnnihilator {S : Submodule R M} {φ : Dual R M}
    (hφ : φ ∈ S.dualAnnihilator) : S ≤ ker φ := by
  intro x hxS
  rw [mem_dualAnnihilator] at hφ
  exact hφ x hxS

lemma subset_ker_of_mem_dual {s : Set M} {φ : Dual R M} (hφ : φ ∈ dual (Dual.eval R M) s) :
    s ⊆ ker φ := by
  intro x hxS
  rw [← dual_span, dual_dualAnnihilator, mem_dualAnnihilator] at hφ
  exact hφ x (subset_span hxS)

lemma le_ker_of_mem_dual {S : Submodule R M} {φ : Dual R M} (hφ : φ ∈ dual (Dual.eval R M) S) :
    S ≤ ker φ := by
  intro x hxS
  rw [S.dual_dualAnnihilator, mem_dualAnnihilator] at hφ
  exact hφ x hxS

section Map

variable {M' N' : Type*}
  [AddCommMonoid M'] [Module R M']
  [AddCommMonoid N'] [Module R N']

lemma dual_bilin_dual_id (s : Set M) : dual p s = dual .id (p '' s) := by ext x; simp

lemma dual_bilin_dual_id_submodule (S : Submodule R M) : dual p S = dual .id (map p S) := by
  rw [map_coe, dual_bilin_dual_id]

-- TODO: generalize to arbitrary pairings (but what takes the place of `f.dualMap`?)
lemma dual_map (f : M →ₗ[R] M') (s : Set M) :
    comap f.dualMap (dual (Dual.eval R M) s) = dual (Dual.eval R M') (f '' s) := by
  ext x; simp

lemma dual_map' (f : M →ₗ[R] M') (s : Set (Dual R M')) :
    comap f (dual .id s) = dual .id (f.dualMap '' s) := by
  ext x; simp

end Map

lemma dual_sSup (s : Set (Submodule R M)) :
    dual p (sSup s : Submodule R M) = dual p (sUnion (SetLike.coe '' s)) := by
  rw [sUnion_image]; nth_rw 2 [←dual_span]; sorry -- rw [span_biUnion]

lemma dual_sup_dual_eq_inf_dual (S T : Submodule R M) :
    dual p (S ⊔ T : Submodule R M) = dual p S ⊓ dual p T := by rw [dual_sup, dual_union]

lemma dual_sSup_sInf_dual (s : Set (Submodule R M)) :
    dual p (sSup s : Submodule R M) = sInf (dual p '' (SetLike.coe '' s)) := by
  rw [dual_sSup, dual_sUnion]

lemma dual_sup_dual_le_dual_inf (S T : Submodule R M) :
    dual p S ⊔ dual p T ≤ dual p (S ⊓ T : Submodule R M) := by
  intro x h y ⟨hyS, hyT⟩
  simp only [mem_sup, mem_dual, SetLike.mem_coe] at h
  obtain ⟨x', hx', y', hy', hxy⟩ := h
  rw [← hxy, ← zero_add 0]
  nth_rw 1 [hx' hyS, hy' hyT, map_add]

end Submodule
