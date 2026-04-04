/-
Copyright (c) 2026 Martin Winter, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter, Yaël Dillies
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

open Module Set LinearMap

namespace Submodule

variable {R : Type*} [CommSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {S T : Submodule R M}

variable (p S) in
/-- The dual span of a set `s` with respect to a bilinear pairing `p` is the submodule
  consisting of the points `y` such that for all points `x ∈ s` we have `0 = p x y`. -/
def dual : Submodule R N where
  carrier := {y | ∀ x ∈ S, p x y = 0}
  zero_mem' := by simp
  add_mem' {u v} hu hv x hx := by rw [map_add, hu _ hx, hv _ hx, add_zero]
  smul_mem' c y hy x hx := by rw [map_smul, hy _ hx, smul_eq_mul, mul_zero]

@[simp] theorem mem_dual {y : N} : y ∈ dual p S ↔ ∀ x ∈ S, p x y = 0 := .rfl

@[simp high] theorem mem_dual_span (s : Set M) {y : N} :
    y ∈ dual p (span R s) ↔ ∀ ⦃x⦄, x ∈ s → p x y = 0 := by
  constructor <;> intro h x hx
  · exact h _ (subset_span hx)
  induction hx using span_induction with
  | mem _ hxs => exact h hxs
  | zero => simp
  | add _ _ _ _ hy hz => rw [map_add, add_apply, hy, hz, add_zero]
  | smul _ _ _ hy => simp only [map_smul, smul_apply, smul_eq_mul, hy, mul_zero]

theorem mem_dual_iff_le_ker_flip {y : N} : y ∈ dual p S ↔ S ≤ ker (p.flip y) := .rfl

@[simp] theorem dual_zero : dual p ⊥ = ⊤ := by ext; simp

@[simp] theorem dual_ker : dual p (ker p) = ⊤ := by ext; simp +contextual

theorem dual_univ_eq_ker : dual p ⊤ = ker p.flip := by
  ext x; simpa using (LinearMap.ext_iff (g := 0) (f := p.flip x)).symm

@[gcongr] theorem dual_le_dual (h : S ≤ T) : dual p T ≤ dual p S := fun _ hy _ hx ↦ hy _ (h hx)

alias dual_anti := dual_le_dual

theorem dual_antitone : Antitone (dual p) := fun _ _ h => dual_le_dual h

theorem ker_le_dual (S) : ker p.flip ≤ dual p S := by
  simp [← dual_univ_eq_ker, dual_anti]

theorem ker_le_dual_flip (S) : ker p ≤ dual p.flip S := by
  rw [← flip_flip p]; exact ker_le_dual S

theorem dual_span_singleton (x : M) : dual p (R ∙ x) = ker (p x) := by ext x; simp [Eq.comm]

theorem dual_sSup (s : Set (Submodule R M)) : dual p (sSup s) = sInf (dual p '' s) := by
  ext y
  simp only [mem_dual, mem_sInf, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · exact fun h S hS x hx => h x (le_sSup hS hx)
  · intro h x hx
    rw [mem_sSup] at hx
    specialize hx (p.flip y).ker
    simp only [← mem_dual_iff_le_ker_flip] at hx
    exact hx h

theorem dual_iSup {ι : Sort*} (f : ι → Submodule R M) : dual p (⨆ i, f i) = ⨅ i, dual p (f i) := by
  simpa only [sSup_range, sInf_image, iInf_range] using dual_sSup (Set.range f)

theorem dual_sup (S T) : dual p (S ⊔ T) = dual p S ⊓ dual p T := by
  simpa [image_pair] using dual_sSup {S, T}

variable (p) in
@[simp] theorem dual_sup_ker (S) : dual p (S ⊔ ker p) = dual p S := by simp [dual_sup]

/-- The dual submodule of `s` equals the intersection of dual submodules of the points in `s`. -/
theorem dual_eq_iInf_dual_span_singleton (S) :
    dual p S = ⨅ x : S, dual p (R ∙ x.val) := by ext; simp

/-- The dual submodule of `s` equals the intersection of dual submodules of the points in `s`. -/
theorem dual_eq_Inf_dual_span_singleton (S) :
    dual p S = ⨅ x ∈ S, dual p (R ∙ x) := by ext; simp

theorem dual_span_eq_iInf_dual_span_singleton (s : Set M) :
    dual p (span R s) = ⨅ x ∈ s, dual p (R ∙ x) := by ext; simp

theorem dual_span_eq_Inf_dual_span_singleton (s : Set M) :
    dual p (span R s) = ⨅ x : s, dual p (R ∙ x.val) := by ext; simp

/-- The dual is the kernel of a linear map into a free module. -/
theorem dual_ker_pi (S) : dual p S = ker (.pi fun x : S => p x) := by
  ext; simp [dual_eq_Inf_dual_span_singleton S, ker_pi, dual_span_singleton]

/-- The dual is the kernel of a linear map into a free module. -/
theorem dual_span_ker_pi (s : Set M) :
    dual p (span R s) = ker (.pi fun x : s => p x) := by
  ext; simp [dual_span_eq_iInf_dual_span_singleton s, ker_pi, dual_span_singleton]

/-- The dual is the kernel of a linear map into a free module. -/
theorem dual_span_finset_ker_pi (s : Finset M) :
    dual p (span R s) = ker (.pi fun x : s => p x) := by simp [dual_span_ker_pi]

/-- Any submodule is contained in its double dual submodule. -/
theorem le_dual_dual : S ≤ dual p.flip (dual p S) := fun _x hx _y hy ↦ hy _ hx

theorem le_dual_of_le_dual {T : Submodule R N} (hST : T ≤ dual p S) :
    S ≤ dual p.flip T := le_trans le_dual_dual (dual_antitone hST)

theorem le_dual_iff_le_dual {T : Submodule R N} :
    S ≤ dual p.flip T ↔ T ≤ dual p S := ⟨le_dual_of_le_dual, le_dual_of_le_dual⟩

variable (p) in
/-- Double duality is monotone. -/
theorem dual_dual_mono (hST : S ≤ T) :
    dual p.flip (dual p S) ≤ dual p.flip (dual p T) := dual_antitone <| dual_antitone hST

variable (p) in
/-- Double duality is monotone. -/
theorem dual_dual_monotone : Monotone (dual p.flip ∘ dual p) :=
  fun _ _ h => dual_antitone <| dual_antitone h

@[simp] theorem dual_dual_flip_dual (S) : dual p (dual p.flip (dual p S)) = dual p S :=
  le_antisymm (dual_le_dual le_dual_dual) le_dual_dual

@[simp] theorem dual_flip_dual_dual_flip (S : Submodule R N) :
    dual p.flip (dual p (dual p.flip S)) = dual p.flip S := dual_dual_flip_dual S

theorem dual_sup_dual_le_dual_inf (S T) : dual p S ⊔ dual p T ≤ dual p (S ⊓ T) := by
  intro _ h _ ⟨hS, hT⟩
  simp only [mem_sup, mem_dual] at h
  obtain ⟨_, hx, _, hy, hxy⟩ := h
  simp [← hxy, hx _ hS, hy _ hT]

variable {M' : Type*} [AddCommMonoid M'] [Module R M']

@[simp] lemma dual_image (S : Submodule R M') (q : M' →ₗ[R] M) :
    dual p (S.map q) = dual (p.comp q) S := by ext; simp

/-- Duality with respect to a general bilinear map can be expressed as duality using the
  identity pairing. -/
lemma dual_eq_dual_id_map (S) : dual p S = dual .id (map p S) := by simp

/-- Duality with respect to a general bilinear map can be expressed as duality using the
  standard pairing `Dual.eval`. -/
lemma dual_eq_comap_dual_eval (S) : dual p S = comap p.flip (dual (Module.Dual.eval R M) S) := by
  ext; simp

/-- The dual submodule w.r.t. the standard dual map is the dual annihilator. -/
theorem dual_dualAnnihilator (S) : dual (Dual.eval R M) S = S.dualAnnihilator := by
  ext x; simp

variable (p) in
theorem dual_comap_dualAnnihilator (S) : dual p S = comap p.flip S.dualAnnihilator := by
  rw [← dual_dualAnnihilator, dual_eq_comap_dual_eval]

/-- The dual submodule w.r.t. the identity map is the dual coannihilator. -/
theorem dual_dualCoannihilator (S : Submodule R (Dual R M)) :
    dual .id S = S.dualCoannihilator := by ext; simp

variable (p) in
theorem dual_map_dualCoannihilator (S) : dual p S = (map p S).dualCoannihilator := by
  ext x; simp

section Map

variable {M' : Type*} [AddCommMonoid M'] [Module R M']
variable {N' : Type*} [AddCommMonoid N'] [Module R N']

theorem dual_map (f : M →ₗ[R] M') (S : Submodule R M) :
    dual (Dual.eval R M') (S.map f) = comap f.dualMap (dual (Dual.eval R M) S) := by
  ext x; simp

theorem dual_map' (f : M →ₗ[R] M') (S : Submodule R (Dual R M')) :
    dual .id (S.map f.dualMap) = comap f (dual .id S) := by
  ext x; simp

end Map

end Submodule
