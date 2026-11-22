/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Christopher Hoskin, Martin Winter
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

import Mathlib.Algebra.Module.Torsion.Field

/-!
# Orthogonal complement

This file defines the orthogonal submodule of a submodule with respect to a sesqui-blinear map.

## Main declarations

* `orthogonalBilin` provides the orthogonal complement with respect to a sesqui-bilinear map
-/

@[expose] public section

open Module LinearMap

variable {R R₁ R₂ M M₁ M₂ : Type*}

namespace Submodule

/-! ### The orthogonal complement -/

variable [CommSemiring R] [CommSemiring R₁] [CommSemiring R₂]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid M₁] [Module R₁ M₁]
variable [AddCommMonoid M₂] [Module R₂ M₂]
variable {I₁ : R₁ →+* R} {I₂ : R₂ →+* R}
variable {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M}
variable {S T : Submodule R₁ M₁}

variable (B S) in
/-- The orthogonal complement of a submodule `N` with respect to some bilinear map is the set of
elements `x` which are orthogonal to all elements of `N`; i.e., for all `y` in `N`, `B x y = 0`.

Note that for general (neither symmetric nor antisymmetric) bilinear maps this definition has a
chirality; in addition to this "left" orthogonal complement one could define a "right" orthogonal
complement for which, for all `y` in `N`, `B y x = 0`.  This variant definition is not currently
provided in mathlib. -/
def orthogonalBilin : Submodule R₂ M₂ where
  carrier := {y | ∀ x ∈ S, B x y = 0}
  zero_mem' := by simp
  add_mem' {u v} hu hv x hx := by simp [hu _ hx, hv _ hx]
  smul_mem' c y hy x hx := by simp [hy _ hx]

@[simp] theorem mem_orthogonalBilin {m : M₂} :
  m ∈ S.orthogonalBilin B ↔ ∀ n ∈ S, B n m = 0 := .rfl

@[deprecated (since := "2026-06-19")]
alias mem_orthogonalBilin_iff := mem_orthogonalBilin

theorem mem_orthogonalBilin_iff_le_ker_flip {y : M₂} :
    y ∈ orthogonalBilin B S ↔ S ≤ ker (B.flip y) := .rfl

/- This is high priority in order to be prefered over `Submodule.mem_orthogonalBilin`. -/
@[simp high] theorem mem_orthogonalBilin_span {s : Set M₁} {y : M₂} :
    y ∈ orthogonalBilin B (span R₁ s) ↔ ∀ ⦃x⦄, x ∈ s → B x y = 0 := by
  simpa using! span_le (p := LinearMap.ker (B.flip y))

variable (B) in
lemma orthogonalBilin_gc :
    @GaloisConnection (Submodule R₁ M₁) (Submodule R₂ M₂)ᵒᵈ _ _
      (orthogonalBilin B) (orthogonalBilin B.flip) :=
  fun _ _ ↦ ⟨fun h _ hx _ hy ↦ h hy _ hx, fun h _ hy _ hx ↦ h hx _ hy⟩

theorem le_orthogonalBilin_flip_iff_le_orthogonalBilin {T : Submodule R₂ M₂} :
    S ≤ orthogonalBilin B.flip T ↔ T ≤ orthogonalBilin B S :=
  ((orthogonalBilin_gc B) S T).symm

alias ⟨le_orthogonalBilin_of_le_orthogonBilin_flip, le_orthogonalBilin_flip_of_le_orthogonBilin⟩ :=
  le_orthogonalBilin_flip_iff_le_orthogonalBilin

@[simp] theorem orthogonalBilin_bot : orthogonalBilin B ⊥ = ⊤ :=
  (orthogonalBilin_gc B).l_bot

@[simp] theorem orthogonalBilin_ker : orthogonalBilin B (ker B) = ⊤ := by
  ext; simp +contextual

theorem orthogonalBilin_top_eq_ker : orthogonalBilin B ⊤ = ker B.flip := by
  ext x; simp [LinearMap.ext_iff]

@[gcongr] theorem orthogonalBilin_le (h : S ≤ T) :
    orthogonalBilin B T ≤ orthogonalBilin B S := (orthogonalBilin_gc B).monotone_l h

alias orthogonalBilin_anti := orthogonalBilin_le

theorem orthogonalBilin_antitone : Antitone (orthogonalBilin B) :=
  (orthogonalBilin_gc B).monotone_l

theorem ker_flip_le_orthogonalBilin (S) : ker B.flip ≤ orthogonalBilin B S := by
  simp [← orthogonalBilin_top_eq_ker, orthogonalBilin_anti]

theorem ker_le_orthogonalBilin_flip (S) : ker B ≤ orthogonalBilin B.flip S := by
  rw [← flip_flip B]; exact ker_flip_le_orthogonalBilin S

theorem orthogonalBilin_span_singleton (x : M₁) : orthogonalBilin B (R₁ ∙ x) = ker (B x) := by
  ext x; simp

@[deprecated (since := "2026-06-19")]
alias _root_.LinearMap.orthogonal_span_singleton_eq_to_lin_ker := orthogonalBilin_span_singleton

theorem orthogonalBilin_sSup (s : Set (Submodule R₁ M₁)) :
    orthogonalBilin B (sSup s) = ⨅ S ∈ s, orthogonalBilin B S :=
  (orthogonalBilin_gc B).l_sSup

theorem orthogonalBilin_iSup {ι : Sort*} (f : ι → Submodule R₁ M₁) :
    orthogonalBilin B (⨆ i, f i) = ⨅ i, orthogonalBilin B (f i) :=
  (orthogonalBilin_gc B).l_iSup

theorem orthogonalBilin_sup (S T) :
    orthogonalBilin B (S ⊔ T) = orthogonalBilin B S ⊓ orthogonalBilin B T :=
  (orthogonalBilin_gc B).l_sup

variable (B) in
@[simp] theorem orthogonalBilin_sup_ker (S) :
    orthogonalBilin B (S ⊔ ker B) = orthogonalBilin B S := by
  simp [orthogonalBilin_sup]

/-- Every submodule is contained in the orthogonal complement of its orthogonal complement. -/
theorem le_orthogonalBilin_flip_orthogonalBilin :
    S ≤ orthogonalBilin B.flip (orthogonalBilin B S) := (orthogonalBilin_gc B).le_u_l S

theorem le_orthogonalBilin_orthogonalBilin {I₂ : R₁ →+* R} {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] M}
    (b : B.IsRefl) : S ≤ (S.orthogonalBilin B).orthogonalBilin B :=
  fun n hn _m hm ↦ b _ _ (hm n hn)

@[simp] theorem orthogonalBilin_orthogonalBilin_flip_orthogonalBilin (S) :
    orthogonalBilin B (orthogonalBilin B.flip (orthogonalBilin B S)) = orthogonalBilin B S :=
  (orthogonalBilin_gc B).l_u_l_eq_l S

@[simp] theorem orthogonalBilin_flip_orthogonalBilin_orthogonalBilin_flip (S : Submodule R₂ M₂) :
    orthogonalBilin B.flip (orthogonalBilin B (orthogonalBilin B.flip S)) =
      orthogonalBilin B.flip S :=
  (orthogonalBilin_gc B).u_l_u_eq_u S

theorem orthogonalBilin_sup_orthogonalBilin_le_orthogonalBilin_inf (S T) :
    orthogonalBilin B S ⊔ orthogonalBilin B T ≤ orthogonalBilin B (S ⊓ T) :=
  sup_le (orthogonalBilin_le inf_le_left) (orthogonalBilin_le inf_le_right)

/-- The orthogonal submodule w.r.t. the standard bilinear pairing is the dual annihilator. -/
@[simp] theorem orthogonalBilin_eval_eq_dualAnnihilator (S) :
    orthogonalBilin (Dual.eval R₁ M₁) S = S.dualAnnihilator := by ext x; simp

/-- The orthogonal submodule w.r.t. the identity pairing is the dual coannihilator. -/
@[simp] theorem orthogonalBilin_id_eq_dualCoannihilator (S : Submodule R₁ (Dual R₁ M₁)) :
    orthogonalBilin .id S = S.dualCoannihilator := by ext; simp

variable {R₃ : Type*} [CommSemiring R₃]
variable {M₃ : Type*} [AddCommMonoid M₃] [Module R₃ M₃]
variable {J₃ : R₃ →+* R₁} {J : R₃ →+* R} [RingHomCompTriple J₃ I₁ J]

variable [RingHomSurjective J₃] in
lemma orthogonalBilin_map (S : Submodule R₃ M₃) (q : M₃ →ₛₗ[J₃] M₁) :
    orthogonalBilin B (S.map q) = orthogonalBilin (B.comp q) S := by ext; simp

variable [RingHomSurjective I₁] in
/-- Orthogonality w.r.t. a general bilinear map can be expressed as orthogonality w.r.t
the identity pairing. -/
@[simp] lemma orthogonalBilin_id_map (S) :
    orthogonalBilin .id (map B S) = orthogonalBilin B S := orthogonalBilin_map _ _

section

variable {I₂ : R₂ →+* R₁} {B : M₁ →ₗ[R₁] M₂ →ₛₗ[I₂] R₁}

/-- Orthogonality w.r.t. a general bilinear map can be expressed as orthogonality w.r.t
the evaluation pairing. -/
lemma comap_orthogonalBilin_eval (S) :
    comap B.flip (orthogonalBilin (Dual.eval R₁ M₁) S) = orthogonalBilin B S := by
  ext; simp

variable (B) in
@[simp] theorem comap_dualAnnihilator_eq_orthogonalBilin (S) :
    comap B.flip S.dualAnnihilator = orthogonalBilin B S := by
  rw [← orthogonalBilin_eval_eq_dualAnnihilator, comap_orthogonalBilin_eval]

end

variable (B) in
theorem dualCoannihilator_map_eq_orthogonalBilin {I₁ : R₁ →+* R₂} {B : M₁ →ₛₗ[I₁] M₂ →ₗ[R₂] R₂}
    [RingHomSurjective I₁] (S) : (map B S).dualCoannihilator = orthogonalBilin B S := by
  ext x; simp

section Map

variable {M₁' : Type*} [AddCommMonoid M₁'] [Module R₁ M₁']

theorem orthogonalBilin_eval_map (q : M₁ →ₗ[R₁] M₁') (S : Submodule R₁ M₁) :
    orthogonalBilin (Dual.eval R₁ M₁') (S.map q) =
      comap q.dualMap (orthogonalBilin (Dual.eval R₁ M₁) S) := by
  ext x; simp

theorem orthogonalBilin_id_map_dualMap (q : M₁ →ₗ[R₁] M₁') (S : Submodule R₁ (Dual R₁ M₁')) :
    orthogonalBilin .id (S.map q.dualMap) = comap q (orthogonalBilin .id S) := by
  ext x; simp

end Map

end Submodule

namespace LinearMap

section Orthogonal

variable {K K₁ V V₁ V₂ : Type*}
variable [Field K] [AddCommGroup V] [Module K V] [Field K₁] [AddCommGroup V₁] [Module K₁ V₁]
  [AddCommGroup V₂] [Module K V₂] {J : K →+* K} {J₁ : K₁ →+* K} {J₁' : K₁ →+* K}

-- ↓ This lemma only applies in fields as we require `a * b = 0 → a = 0 ∨ b = 0`
theorem span_singleton_inf_orthogonal_eq_bot (B : V₁ →ₛₗ[J₁] V₁ →ₛₗ[J₁'] V₂) (x : V₁)
    (hx : B x x ≠ 0) : (K₁ ∙ x) ⊓ (K₁ ∙ x).orthogonalBilin B = ⊥ := by
  rw [← Finset.coe_singleton]
  refine eq_bot_iff.2 fun y h ↦ ?_
  obtain ⟨μ, -, rfl⟩ := Submodule.mem_span_finset.1 h.1
  replace h := h.2 x (by simp [Submodule.mem_span] : x ∈ Submodule.span K₁ ({x} : Finset V₁))
  rw [Finset.sum_singleton] at h ⊢
  suffices hμzero : μ x = 0 by rw [hμzero, zero_smul, Submodule.mem_bot]
  rw [map_smulₛₗ] at h
  exact Or.elim (smul_eq_zero.mp h)
      (fun y ↦ by simpa using y)
      (fun hfalse ↦ False.elim <| hx hfalse)

-- todo: Generalize this to sesquilinear maps
theorem span_singleton_sup_orthogonal_eq_top {B : V →ₗ[K] V →ₗ[K] K} {x : V} (hx : B x x ≠ 0) :
    (K ∙ x) ⊔ (K ∙ x).orthogonalBilin B = ⊤ := by
  simp only [Submodule.orthogonalBilin_span_singleton, span_singleton_sup_ker_eq_top _ hx]

-- todo: Generalize this to sesquilinear maps
/-- Given a bilinear form `B` and some `x` such that `B x x ≠ 0`, the span of the singleton of `x`
  is complement to its orthogonal complement. -/
theorem isCompl_span_singleton_orthogonal {B : V →ₗ[K] V →ₗ[K] K} {x : V} (hx : B x x ≠ 0) :
    IsCompl (K ∙ x) ((K ∙ x).orthogonalBilin B) :=
  { disjoint := disjoint_iff.2 <| span_singleton_inf_orthogonal_eq_bot B x hx
    codisjoint := codisjoint_iff.2 <| span_singleton_sup_orthogonal_eq_top hx }

end Orthogonal

section CommRing

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M₁] [Module R M₁]

/-- The restriction of a reflexive bilinear map `B` onto a submodule `W` is
nondegenerate if `W` has trivial intersection with its orthogonal complement,
that is `Disjoint W (W.orthogonalBilin B)`. -/
theorem nondegenerate_restrict_of_disjoint_orthogonal {B : M →ₗ[R] M →ₗ[R] M₁} (hB : B.IsRefl)
    {W : Submodule R M} (hW : Disjoint W (W.orthogonalBilin B)) :
    (B.domRestrict₁₂ W W).Nondegenerate := by
  rw [(hB.domRestrict W).nondegenerate_iff_separatingLeft]
  rintro ⟨x, hx⟩ b₁
  rw [Submodule.mk_eq_zero, ← Submodule.mem_bot R]
  refine hW.le_bot ⟨hx, fun y hy ↦ ?_⟩
  specialize b₁ ⟨y, hy⟩
  simp_rw [domRestrict₁₂_apply] at b₁
  exact hB.eq_zero b₁

end CommRing

end LinearMap
