/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Geometry.Convex.Cone.Pointed

/-!
# The algebraic dual of a cone

Given a bilinear pairing `p` between two `R`-modules `M` and `N` and a cone `C` in `M`, we define
`PointedCone.dual p C` to be the cone in `N` consisting of all points `y` such that `0 ≤ p x y`
for all `x ∈ C`.

When the pairing is perfect, this gives us the algebraic dual of a cone. This is developed here.
When the pairing is continuous and perfect (as a continuous pairing), this gives us the topological
dual instead. See `Mathlib/Analysis/Convex/Cone/Dual.lean` for that case.

## Implementation notes

We do not provide a `ConvexCone`-valued version of `PointedCone.dual` since the dual cone of any set
always contains `0`, i.e. is a pointed cone.
Furthermore, the strict version `{y | ∀ x ∈ C, 0 < p x y}` is a candidate to the name
`ConvexCone.dual`.

-/

@[expose] public section

assert_not_exists TopologicalSpace Real Cardinal

open Function LinearMap Pointwise Set

namespace PointedCone

section CommSemiring

variable {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C D : PointedCone R M}

local notation3 "R≥0" => {c : R // 0 ≤ c}

set_option backward.isDefEq.respectTransparency false in
variable (p C) in
/-- The dual cone of a cone `C` with respect to a bilinear pairing `p` is the cone consisting of all
points `y` such that for all points `x ∈ C` we have `0 ≤ p x y`. -/
def dual : PointedCone R N where
  carrier := {y | ∀ ⦃x⦄, x ∈ C → 0 ≤ p x y}
  zero_mem' := by simp
  add_mem' {u v} hu hv x hx := by rw [map_add]; exact add_nonneg (hu hx) (hv hx)
  smul_mem' c y hy x hx := by rw [← Nonneg.coe_smul, map_smul]; exact mul_nonneg c.2 (hy hx)

@[simp] lemma mem_dual (y : N) : y ∈ dual p C ↔ ∀ ⦃x⦄, x ∈ C → 0 ≤ p x y := .rfl

set_option backward.isDefEq.respectTransparency false in
@[simp high] lemma mem_dual_hull (s : Set M) (y : N) :
    y ∈ dual p (hull R s) ↔ ∀ ⦃x⦄, x ∈ s → 0 ≤ p x y := by
  constructor <;> intro h x hx
  · exact h (subset_hull hx)
  induction hx using Submodule.span_induction with
  | mem _ hxs => exact h hxs
  | zero => simp
  | add _ _ _ _ hy hz => simpa using add_nonneg hy hz
  | smul c _ _ hy => simpa using mul_nonneg c.2 hy

lemma mem_dual_iff_le_positive_comap {y : N} :
    y ∈ dual p C ↔ C ≤ (positive R R).comap (p.flip y) := .rfl

@[simp] lemma dual_bot : dual p ⊥ = ⊤ := by ext; simp

@[deprecated (since := "2026-04-09")]
alias dual_singleton_zero := dual_bot
@[deprecated (since := "2026-04-09")]
alias dual_zero := dual_bot
@[deprecated (since := "2026-04-09")]
alias dual_empty := dual_bot

@[simp] lemma dual_ker : dual p p.ker = ⊤ := by ext; simp +contextual

@[gcongr] lemma dual_anti (h : C ≤ D) : dual p D ≤ dual p C := fun _y hy _x hx ↦ hy (h hx)

alias dual_le_dual := dual_anti

lemma dual_antitone : Antitone (dual p) := fun _ _ h => dual_anti h

/-- The dual cone of a ray (hull of a singleton) is given by the preimage of the positive cone
under the linear map `p x`. -/
lemma dual_hull_singleton (x : M) : dual p (R ∙₊ x) = (positive R R).comap (p x) := by ext; simp

@[deprecated (since := "2026-04-10")]
alias dual_singleton := dual_hull_singleton

lemma dual_sSup (s : Set (PointedCone R M)) : dual p (sSup s) = sInf (dual p '' s) := by
  ext y
  simp only [mem_dual, Submodule.mem_sInf, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  constructor
  · exact fun h S hS x hx => h (le_sSup hS hx)
  · intro h x hx
    rw [Submodule.mem_sSup] at hx
    specialize hx ((positive R R).comap (p.flip y))
    simp only [← mem_dual_iff_le_positive_comap] at hx
    exact hx h

@[deprecated (since := "2026-04-09")]
alias dual_sUnion := dual_sSup

lemma dual_iSup {ι : Sort*} (f : ι → PointedCone R M) :
    dual p (⨆ i, f i) = ⨅ i, dual p (f i) := by
  simpa only [sSup_range, sInf_image, iInf_range] using dual_sSup (Set.range f)

@[deprecated (since := "2026-04-09")]
alias dual_iUnion := dual_iSup

lemma dual_sup (C D) : dual p (C ⊔ D) = dual p C ⊓ dual p D := by
  simpa [image_pair] using dual_sSup {C, D}

@[deprecated (since := "2026-04-09")]
alias dual_union := dual_sup

variable (C) in
@[deprecated "Use `Submodule.span_insert` and `PointredCone.dual_sup`" (since := "2026-04-09")]
lemma dual_insert (x : M) :
    dual p (hull R (insert x C)) = dual p (R ∙₊ x) ⊓ dual p C := by
  simp [Submodule.span_insert, dual_sup, hull]

variable (p) in
@[simp] lemma dual_sup_ker (C) : dual p (C ⊔ p.ker) = dual p C := by simp [dual_sup]

/-- The dual cone of `C` equals the intersection of dual cone of the points in `C`. -/
lemma dual_eq_iInf_dual_hull_singleton (C) :
    dual p C = ⨅ x : C, dual p (R ∙₊ x.val) := by ext; simp

@[deprecated (since := "2026-04-10")]
alias dual_eq_iInter_dual_singleton := dual_eq_iInf_dual_hull_singleton

/-- The dual cone of `C` equals the intersection of dual cone of the points in `C`. -/
lemma dual_eq_Inf_dual_hull_singleton (C) :
    dual p C = ⨅ x ∈ C, dual p (R ∙₊ x) := by ext; simp

lemma dual_hull_eq_iInf_dual_hull_singleton (s : Set M) :
    dual p (hull R s) = ⨅ x ∈ s, dual p (R ∙₊ x) := by ext; simp

lemma dual_hull_eq_Inf_dual_hull_singleton (s : Set M) :
    dual p (hull R s) = ⨅ x : s, dual p (R ∙₊ x.val) := by ext; simp

/-- Any cone is contained in its double dual cone. -/
lemma le_dual_dual : C ≤ dual p.flip (dual p C) := fun _x hx _y hy ↦ hy hx

@[deprecated (since := "2026-04-09")]
alias subset_dual_dual := le_dual_dual

@[simp] lemma le_dual_flip_iff_le_dual {D} : C ≤ dual p.flip D ↔ D ≤ dual p C := by
  constructor <;> exact (le_trans le_dual_dual <| dual_anti ·)

@[deprecated (since := "2026-04-09")]
alias subset_dual_flip_iff_subset_dual := le_dual_flip_iff_le_dual

variable (s) in
@[simp] lemma dual_dual_flip_dual : dual p (dual p.flip (dual p s)) = dual p s :=
  le_antisymm (dual_anti le_dual_dual) le_dual_dual

@[simp] lemma dual_flip_dual_dual_flip (D) :
    dual p.flip (dual p (dual p.flip D)) = dual p.flip D := dual_dual_flip_dual _

@[deprecated (since := "2026-04-10")]
alias dual_hull := Submodule.span_eq

@[deprecated (since := "2026-04-10")]
alias dual_span := Submodule.span_eq

variable {M' : Type*} [AddCommMonoid M'] [Module R M']

@[simp] lemma dual_map (C : PointedCone R M') (q : M' →ₗ[R] M) :
    dual p (C.map q) = dual (p.comp q) C := by ext; simp

@[deprecated (since := "2026-04-10")]
alias dual_image := dual_map

/-- Duality with respect to a general bilinear map can be expressed as duality using the
  identity pairing. -/
lemma dual_eq_dual_id_map (C) : dual p C = dual .id (map p C) := by simp

@[deprecated (since := "2026-04-10")]
alias dual_eq_dual_id_image := dual_eq_dual_id_map

/-- Duality with respect to a general bilinear map can be expressed as duality using the
  canonical pairing `Dual.eval`. -/
lemma dual_eq_comap_dual_eval (C) :
    dual p C = comap p.flip (dual (Module.Dual.eval R M) C) := by
  ext; simp

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C : PointedCone R M}

lemma dual_univ_eq_ker : dual p ⊤ = ker p.flip := by
  ext x; simpa [Eq.comm, Iff.comm] using AddMonoidHom.ext_iff_le (f := 0) (g := p.flip x)

lemma dual_top (hp : Injective p.flip) : dual p ⊤ = 0 := by
  simpa [dual_univ_eq_ker] using ker_eq_bot_of_injective hp

@[deprecated (since := "2026-04-10")]
alias dual_univ := dual_top

variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

@[simp] lemma dual_neg : dual p (-C) = -dual p C := by
  ext x
  simp only [mem_dual, Submodule.mem_neg]
  constructor <;> exact fun h y hy => by simpa [hy] using @h (-y)

end CommRing

end PointedCone
