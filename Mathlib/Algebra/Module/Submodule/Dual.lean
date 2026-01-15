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

See also `PointedCone.dual`.

## Main declarations

- `Submodule.dual` is the dual submodule of a set `s` w.r.t. a bilinear pairing `p`.

## Notes

- In case that the pairing is `Dual.eval R M`, the dual of a submodule `S` is identical to the
  dual annihilator `S` (see `dual_dualAnnihilator`).
- In case that the pairing is `LinealMap.id`, the dual of a submodule `S` is identical to the
  dual coannihilator `S` (see `dual_dualCoannihilator`).

-/

@[expose] public section

assert_not_exists TopologicalSpace Real Cardinal

open Module Function LinearMap Pointwise Set OrderDual

namespace Submodule

variable {R : Type*} [CommSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R} {s t : Set M}

variable (p s) in
/-- The dual span of a set `s` with respect to a bilinear pairing `p` is the submodule
  consisting of the points `y` such that for all points `x ∈ s` we have `0 = p x y`. -/
def dual : Submodule R N where
  carrier := {y | ∀ ⦃x⦄, x ∈ s → 0 = p x y}
  zero_mem' := by simp
  add_mem' {u v} hu hv x hx := by rw [map_add, ← hu hx, ← hv hx, add_zero]
  smul_mem' c y hy x hx := by rw [map_smul, ← hy hx, smul_eq_mul, mul_zero]

@[simp] theorem mem_dual {y : N} : y ∈ dual p s ↔ ∀ ⦃x⦄, x ∈ s → 0 = p x y := .rfl

@[simp] theorem dual_empty : dual p ∅ = ⊤ := by ext; simp

@[simp] theorem dual_zero : dual p 0 = ⊤ := by ext; simp

@[simp] theorem dual_ker : dual p (ker p) = ⊤ := by ext; simp +contextual

theorem dual_univ_eq_ker : dual p univ = ker p.flip := by
  ext x; simpa [Eq.comm] using (funext_iff (f := (0 : M →ₗ[R] R)) (g := p.flip x)).symm

theorem dual_flip_univ_eq_ker : dual p.flip univ = ker p := by
  nth_rw 2 [← flip_flip p]; exact dual_univ_eq_ker

@[gcongr] theorem dual_le_dual (h : t ⊆ s) : dual p s ≤ dual p t := fun _y hy _x hx ↦ hy (h hx)

alias dual_anti := dual_le_dual

theorem dual_antitone : Antitone (dual p) := fun _ _ h => dual_le_dual h

theorem ker_le_dual (s : Set M) : ker p.flip ≤ dual p s := by
  simp [← dual_flip_univ_eq_ker, dual_anti]

theorem ker_le_dual_flip (s : Set N) : ker p ≤ dual p.flip s := by
  simp [← dual_flip_univ_eq_ker, dual_anti]

theorem dual_singleton (x : M) : dual p {x} = ker (p x) := by ext x; simp [Eq.comm]

theorem dual_union (s t : Set M) : dual p (s ∪ t) = dual p s ⊓ dual p t := by aesop

variable (p) in
theorem dual_union_ker (s : Set M) : dual p (s ∪ ker p) = dual p s := by simp [dual_union]

theorem dual_insert (x : M) (s : Set M) : dual p (insert x s) = dual p {x} ⊓ dual p s := by
  rw [insert_eq, dual_union]

theorem dual_iUnion {ι : Sort*} (f : ι → Set M) : dual p (⋃ i, f i) = ⨅ i, dual p (f i) := by
  ext; simp [forall_swap (α := M)]

theorem dual_sUnion (S : Set (Set M)) : dual p (⋃₀ S) = sInf (dual p '' S) := by
  ext; simp [forall_swap (α := M)]

/-- The dual submodule of `s` equals the intersection of dual submodules of the points in `s`. -/
theorem dual_eq_iInter_dual_singleton (s : Set M) :
    dual p s = ⋂ i : s, (dual p {i.val} : Set N) := by ext; simp

/-- The dual submodule of `s` equals the intersection of dual submodules of the points in `s`. -/
theorem dual_eq_Inf_dual_singleton (s : Set M) :
    dual p s = ⨅ x ∈ s, dual p {x} := by ext; simp

/-- The dual submodule of `s` equals the intersection of dual submodules of the points in `s`. -/
theorem dual_eq_Inf_dual_singleton' (s : Finset M) :
    dual p s = ⨅ x ∈ s, dual p {x} := by ext; simp

/-- The dual is the kernel of a linear map into a free module. -/
theorem dual_ker_pi (s : Set M) : dual p s = ker (LinearMap.pi fun x : s => p x) := by
  simp only [dual_eq_Inf_dual_singleton s, ker_pi, dual_singleton, ← sInf_image, sInf_image']

/-- The dual is the kernel of a linear map into a free module. -/
theorem dual_ker_pi' (s : Finset M) : dual p s = ker (LinearMap.pi fun x : s => p x) := by
  simp [dual_ker_pi]

/-- Any set is a subset of its double dual cone. -/
theorem subset_dual_dual : s ⊆ dual p.flip (dual p s) := fun _x hx _y hy ↦ hy hx

/-- Any submodule is contained in its double dual cone. -/
theorem le_dual_dual {S : Submodule R M} : S ≤ dual p.flip (dual p S) := subset_dual_dual

theorem le_dual_of_le_dual {S : Submodule R M} {T : Submodule R N} (hST : T ≤ dual p S) :
    S ≤ dual p.flip T := le_trans le_dual_dual (dual_antitone hST)

theorem le_dual_iff_le_dual {S : Submodule R M} {T : Submodule R N} :
    S ≤ dual p.flip T ↔ T ≤ dual p S := ⟨le_dual_of_le_dual, le_dual_of_le_dual⟩

variable (p) in
/-- Double duality is monotone. -/
theorem dual_dual_mono {s t : Set M} (hST : s ⊆ t) :
    dual p.flip (dual p s) ≤ dual p.flip (dual p t) := dual_antitone <| dual_antitone hST

variable (p) in
/-- Double duality is monotone. -/
theorem dual_dual_monotone : Monotone (dual p.flip ∘ SetLike.coe ∘ dual p) :=
  fun _ _ h => dual_antitone <| dual_antitone h

variable (s) in
@[simp] theorem dual_dual_flip_dual : dual p (dual p.flip (dual p s)) = dual p s :=
  le_antisymm (dual_le_dual subset_dual_dual) subset_dual_dual

@[simp] theorem dual_flip_dual_dual_flip (s : Set N) :
    dual p.flip (dual p (dual p.flip s)) = dual p.flip s := dual_dual_flip_dual _

@[simp]
theorem dual_span (s : Set M) : dual p (span R s) = dual p s := by
  refine le_antisymm (dual_le_dual subset_span) (fun x hx y hy => ?_)
  induction hy using span_induction with
  | mem _y h => exact hx h
  | zero => simp
  | add y z _hy _hz hy hz => rw [map_add, add_apply, ← hy, ← hz, add_zero]
  | smul t y _hy hy => simp only [map_smul, smul_apply, smul_eq_mul, ← hy, mul_zero]

theorem dual_sup (S T : Submodule R M) : dual p (S ⊔ T : Submodule R M) = dual p (S ∪ T) := by
  nth_rw 2 [← dual_span]
  simp [span_union]

theorem dual_sSup (s : Set (Submodule R M)) :
    dual p (sSup s : Submodule R M) = dual p (⋃₀ (SetLike.coe '' s)) := by
  rw [sUnion_image]
  nth_rw 2 [←dual_span]
  -- TODO: replace below by `rw [span_biUnion]` once `span_biUnion` is merged into mathlib.
  have h : span R (⋃ S ∈ s, S) = sSup s := by simpa using (Submodule.gi R M).l_sSup_u_image s
  rw [h]

theorem dual_union_dual_inf_dual (s t : Set M) :
    dual p (s ∪ t) = dual p s ⊓ dual p t := by rw [dual_union]

theorem dual_sup_dual_inf_dual (S T : Submodule R M) :
    dual p (S ⊔ T : Submodule R M) = dual p S ⊓ dual p T := by rw [dual_sup, dual_union]

theorem dual_sUnion_sInf_dual (s : Set (Set M)) : dual p (⋃₀ s) = sInf (dual p '' s) := by
  rw [dual_sUnion]

theorem dual_sSup_sInf_dual (s : Set (Submodule R M)) :
    dual p (sSup s : Submodule R M) = sInf (dual p '' (SetLike.coe '' s)) := by
  rw [dual_sSup, dual_sUnion]

theorem dual_sup_dual_le_dual_inf (S T : Submodule R M) :
    dual p S ⊔ dual p T ≤ dual p (S ⊓ T : Submodule R M) := by
  intro x h y ⟨hyS, hyT⟩
  simp only [mem_sup, mem_dual, SetLike.mem_coe] at h
  obtain ⟨x', hx', y', hy', hxy⟩ := h
  rw [← hxy, ← zero_add 0]
  nth_rw 1 [hx' hyS, hy' hyT, map_add]

theorem dual_id (s : Set M) : dual p s = dual .id (p '' s) := by ext; simp

theorem dual_id_map (S : Submodule R M) : dual p S = dual .id (map p S) := by ext; simp

theorem dual_eval (s : Set M) : dual p s = comap p.flip (dual (Dual.eval R M) s) := by ext; simp

/-- The dual submodule w.r.t. the standard dual map is the dual annihilator. -/
theorem dual_dualAnnihilator (S : Submodule R M) :
    dual (Dual.eval R M) S = S.dualAnnihilator := by
  ext x; simpa using ⟨fun h _ hw => (h hw).symm, fun h w hw => (h w hw).symm⟩

variable (p) in
theorem dual_comap_dualAnnihilator (S : Submodule R M) :
    dual p S = comap p.flip S.dualAnnihilator := by rw [← dual_dualAnnihilator, dual_eval]

/-- The dual submodule w.r.t. the identity map is the dual coannihilator. -/
theorem dual_dualCoannihilator (S : Submodule R (Dual R M)) :
    dual .id S = S.dualCoannihilator := by
  ext x; simpa using ⟨fun h _ hw => (h hw).symm, fun h w hw => (h w hw).symm⟩

variable (p) in
theorem dual_map_dualCoannihilator (S : Submodule R M) :
    dual p S = (map p S).dualCoannihilator := by
  ext x; simpa using ⟨fun h _ hw => (h hw).symm, fun h w hw => (h w hw).symm⟩

theorem subset_ker_of_mem_dual {s : Set M} {φ : Dual R M} (hφ : φ ∈ dual (Dual.eval R M) s) :
    s ⊆ ker φ := by
  intro x hxS
  rw [← dual_span, dual_dualAnnihilator, mem_dualAnnihilator] at hφ
  exact hφ x (subset_span hxS)

theorem le_ker_of_mem_dual {S : Submodule R M} {φ : Dual R M} (hφ : φ ∈ dual (Dual.eval R M) S) :
    S ≤ ker φ := subset_ker_of_mem_dual hφ

section Map

variable {M' : Type*} [AddCommMonoid M'] [Module R M']
variable {N' : Type*} [AddCommMonoid N'] [Module R N']

theorem dual_map (f : M →ₗ[R] M') (s : Set M) :
    dual (Dual.eval R M') (f '' s) = comap f.dualMap (dual (Dual.eval R M) s) := by
  ext x; simp

theorem dual_map' (f : M →ₗ[R] M') (s : Set (Dual R M')) :
    dual .id (f.dualMap '' s) = comap f (dual .id s) := by
  ext x; simp

end Map

end Submodule
