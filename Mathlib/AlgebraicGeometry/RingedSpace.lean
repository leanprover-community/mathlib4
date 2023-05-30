/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer, Andrew Yang

! This file was ported from Lean 3 source module algebraic_geometry.ringed_space
! leanprover-community/mathlib commit d39590fc8728fbf6743249802486f8c91ffe07bc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Ring.FilteredColimits
import Mathbin.AlgebraicGeometry.SheafedSpace
import Mathbin.Topology.Sheaves.Stalks
import Mathbin.Algebra.Category.Ring.Colimits
import Mathbin.Algebra.Category.Ring.Limits

/-!
# Ringed spaces

We introduce the category of ringed spaces, as an alias for `SheafedSpace CommRing`.

The facts collected in this file are typically stated for locally ringed spaces, but never actually
make use of the locality of stalks. See for instance <https://stacks.math.columbia.edu/tag/01HZ>.

-/


universe v

open CategoryTheory

open TopologicalSpace

open Opposite

open TopCat

open TopCat.Presheaf

namespace AlgebraicGeometry

/-- The type of Ringed spaces, as an abbreviation for `SheafedSpace CommRing`. -/
abbrev RingedSpace : Type _ :=
  SheafedSpace CommRingCat
#align algebraic_geometry.RingedSpace AlgebraicGeometry.RingedSpace

namespace RingedSpace

open SheafedSpace

variable (X : RingedSpace.{v})

/--
If the germ of a section `f` is a unit in the stalk at `x`, then `f` must be a unit on some small
neighborhood around `x`.
-/
theorem isUnit_res_of_isUnit_germ (U : Opens X) (f : X.Presheaf.obj (op U)) (x : U)
    (h : IsUnit (X.Presheaf.germ x f)) :
    ∃ (V : Opens X)(i : V ⟶ U)(hxV : x.1 ∈ V), IsUnit (X.Presheaf.map i.op f) :=
  by
  obtain ⟨g', heq⟩ := h.exists_right_inv
  obtain ⟨V, hxV, g, rfl⟩ := X.presheaf.germ_exist x.1 g'
  let W := U ⊓ V
  have hxW : x.1 ∈ W := ⟨x.2, hxV⟩
  erw [← X.presheaf.germ_res_apply (opens.inf_le_left U V) ⟨x.1, hxW⟩ f, ←
    X.presheaf.germ_res_apply (opens.inf_le_right U V) ⟨x.1, hxW⟩ g, ← RingHom.map_mul, ←
    RingHom.map_one (X.presheaf.germ (⟨x.1, hxW⟩ : W))] at heq
  obtain ⟨W', hxW', i₁, i₂, heq'⟩ := X.presheaf.germ_eq x.1 hxW hxW _ _ HEq
  use W', i₁ ≫ opens.inf_le_left U V, hxW'
  rw [RingHom.map_one, RingHom.map_mul, ← comp_apply, ← X.presheaf.map_comp, ← op_comp] at heq'
  exact isUnit_of_mul_eq_one _ _ heq'
#align algebraic_geometry.RingedSpace.is_unit_res_of_is_unit_germ AlgebraicGeometry.RingedSpace.isUnit_res_of_isUnit_germ

/-- If a section `f` is a unit in each stalk, `f` must be a unit. -/
theorem isUnit_of_isUnit_germ (U : Opens X) (f : X.Presheaf.obj (op U))
    (h : ∀ x : U, IsUnit (X.Presheaf.germ x f)) : IsUnit f :=
  by
  -- We pick a cover of `U` by open sets `V x`, such that `f` is a unit on each `V x`.
  choose V iVU m h_unit using fun x : U => X.is_unit_res_of_is_unit_germ U f x (h x)
  have hcover : U ≤ iSup V := by
    intro x hxU
    rw [opens.mem_supr]
    exact ⟨⟨x, hxU⟩, m ⟨x, hxU⟩⟩
  -- Let `g x` denote the inverse of `f` in `U x`.
  choose g hg using fun x : U => IsUnit.exists_right_inv (h_unit x)
  -- We claim that these local inverses glue together to a global inverse of `f`.
  obtain ⟨gl, gl_spec, -⟩ := X.sheaf.exists_unique_gluing' V U iVU hcover g _
  swap
  · intro x y
    apply section_ext X.sheaf (V x ⊓ V y)
    rintro ⟨z, hzVx, hzVy⟩
    rw [germ_res_apply, germ_res_apply]
    apply (IsUnit.mul_right_inj (h ⟨z, (iVU x).le hzVx⟩)).mp
    erw [← X.presheaf.germ_res_apply (iVU x) ⟨z, hzVx⟩ f, ← RingHom.map_mul,
      congr_arg (X.presheaf.germ (⟨z, hzVx⟩ : V x)) (hg x), germ_res_apply, ←
      X.presheaf.germ_res_apply (iVU y) ⟨z, hzVy⟩ f, ← RingHom.map_mul,
      congr_arg (X.presheaf.germ (⟨z, hzVy⟩ : V y)) (hg y), RingHom.map_one, RingHom.map_one]
  apply isUnit_of_mul_eq_one f gl
  apply X.sheaf.eq_of_locally_eq' V U iVU hcover
  intro i
  rw [RingHom.map_one, RingHom.map_mul, gl_spec]
  exact hg i
#align algebraic_geometry.RingedSpace.is_unit_of_is_unit_germ AlgebraicGeometry.RingedSpace.isUnit_of_isUnit_germ

/-- The basic open of a section `f` is the set of all points `x`, such that the germ of `f` at
`x` is a unit.
-/
def basicOpen {U : Opens X} (f : X.Presheaf.obj (op U)) : Opens X
    where
  carrier := coe '' { x : U | IsUnit (X.Presheaf.germ x f) }
  is_open' := by
    rw [isOpen_iff_forall_mem_open]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨V, i, hxV, hf⟩ := X.is_unit_res_of_is_unit_germ U f x hx
    use V.1
    refine' ⟨_, V.2, hxV⟩
    intro y hy
    use (⟨y, i.le hy⟩ : U)
    rw [Set.mem_setOf_eq]
    constructor
    · convert RingHom.isUnit_map (X.presheaf.germ ⟨y, hy⟩) hf
      exact (X.presheaf.germ_res_apply i ⟨y, hy⟩ f).symm
    · rfl
#align algebraic_geometry.RingedSpace.basic_open AlgebraicGeometry.RingedSpace.basicOpen

@[simp]
theorem mem_basicOpen {U : Opens X} (f : X.Presheaf.obj (op U)) (x : U) :
    ↑x ∈ X.basicOpen f ↔ IsUnit (X.Presheaf.germ x f) :=
  by
  constructor
  · rintro ⟨x, hx, a⟩; cases Subtype.eq a; exact hx
  · intro h; exact ⟨x, h, rfl⟩
#align algebraic_geometry.RingedSpace.mem_basic_open AlgebraicGeometry.RingedSpace.mem_basicOpen

@[simp]
theorem mem_top_basicOpen (f : X.Presheaf.obj (op ⊤)) (x : X) :
    x ∈ X.basicOpen f ↔ IsUnit (X.Presheaf.germ ⟨x, show x ∈ (⊤ : Opens X) by trivial⟩ f) :=
  mem_basicOpen X f ⟨x, _⟩
#align algebraic_geometry.RingedSpace.mem_top_basic_open AlgebraicGeometry.RingedSpace.mem_top_basicOpen

theorem basicOpen_le {U : Opens X} (f : X.Presheaf.obj (op U)) : X.basicOpen f ≤ U := by
  rintro _ ⟨x, hx, rfl⟩; exact x.2
#align algebraic_geometry.RingedSpace.basic_open_le AlgebraicGeometry.RingedSpace.basicOpen_le

/-- The restriction of a section `f` to the basic open of `f` is a unit. -/
theorem isUnit_res_basicOpen {U : Opens X} (f : X.Presheaf.obj (op U)) :
    IsUnit (X.Presheaf.map (@homOfLE (Opens X) _ _ _ (X.basicOpen_le f)).op f) :=
  by
  apply is_unit_of_is_unit_germ
  rintro ⟨_, ⟨x, hx, rfl⟩⟩
  convert hx
  rw [germ_res_apply]
  rfl
#align algebraic_geometry.RingedSpace.is_unit_res_basic_open AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen

@[simp]
theorem basicOpen_res {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (f : X.Presheaf.obj U) :
    @basicOpen X (unop V) (X.Presheaf.map i f) = unop V ⊓ @basicOpen X (unop U) f :=
  by
  induction U using Opposite.rec'
  induction V using Opposite.rec'
  let g := i.unop; have : i = g.op := rfl; clear_value g; subst this
  ext; constructor
  · rintro ⟨x, hx : IsUnit _, rfl⟩
    rw [germ_res_apply] at hx
    exact ⟨x.2, g x, hx, rfl⟩
  · rintro ⟨hxV, x, hx, rfl⟩
    refine' ⟨⟨x, hxV⟩, (_ : IsUnit _), rfl⟩
    rwa [germ_res_apply]
#align algebraic_geometry.RingedSpace.basic_open_res AlgebraicGeometry.RingedSpace.basicOpen_res

-- This should fire before `basic_open_res`.
@[simp]
theorem basicOpen_res_eq {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) [IsIso i] (f : X.Presheaf.obj U) :
    @basicOpen X (unop V) (X.Presheaf.map i f) = @RingedSpace.basicOpen X (unop U) f :=
  by
  apply le_antisymm
  · rw [X.basic_open_res i f]; exact inf_le_right
  · have := X.basic_open_res (inv i) (X.presheaf.map i f)
    rw [← comp_apply, ← X.presheaf.map_comp, is_iso.hom_inv_id, X.presheaf.map_id] at this
    erw [this]
    exact inf_le_right
#align algebraic_geometry.RingedSpace.basic_open_res_eq AlgebraicGeometry.RingedSpace.basicOpen_res_eq

@[simp]
theorem basicOpen_mul {U : Opens X} (f g : X.Presheaf.obj (op U)) :
    X.basicOpen (f * g) = X.basicOpen f ⊓ X.basicOpen g :=
  by
  ext1
  dsimp [RingedSpace.basic_open]
  rw [← Set.image_inter Subtype.coe_injective]
  congr
  ext
  simp_rw [map_mul]
  exact IsUnit.mul_iff
#align algebraic_geometry.RingedSpace.basic_open_mul AlgebraicGeometry.RingedSpace.basicOpen_mul

theorem basicOpen_of_isUnit {U : Opens X} {f : X.Presheaf.obj (op U)} (hf : IsUnit f) :
    X.basicOpen f = U := by
  apply le_antisymm
  · exact X.basic_open_le f
  intro x hx
  erw [X.mem_basic_open f (⟨x, hx⟩ : U)]
  exact RingHom.isUnit_map _ hf
#align algebraic_geometry.RingedSpace.basic_open_of_is_unit AlgebraicGeometry.RingedSpace.basicOpen_of_isUnit

end RingedSpace

end AlgebraicGeometry

