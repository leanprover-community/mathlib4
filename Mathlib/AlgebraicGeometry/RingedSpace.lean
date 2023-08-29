/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer, Andrew Yang
-/
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.AlgebraicGeometry.SheafedSpace
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.Limits

#align_import algebraic_geometry.ringed_space from "leanprover-community/mathlib"@"5dc6092d09e5e489106865241986f7f2ad28d4c8"

/-!
# Ringed spaces

We introduce the category of ringed spaces, as an alias for `SheafedSpace CommRingCat`.

The facts collected in this file are typically stated for locally ringed spaces, but never actually
make use of the locality of stalks. See for instance <https://stacks.math.columbia.edu/tag/01HZ>.

-/

universe v u

open CategoryTheory

open TopologicalSpace

open Opposite

open TopCat

open TopCat.Presheaf

namespace AlgebraicGeometry

/-- The type of Ringed spaces, as an abbreviation for `SheafedSpace CommRingCat`. -/
abbrev RingedSpace : TypeMax.{u+1, v+1} :=
  SheafedSpace.{_, v, u} CommRingCat.{v}
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.RingedSpace AlgebraicGeometry.RingedSpace

namespace RingedSpace

open SheafedSpace

variable (X : RingedSpace)

-- Porting note : this was not necessary in mathlib3
instance : CoeSort RingedSpace (Type*) where
  coe X := X.carrier

/--
If the germ of a section `f` is a unit in the stalk at `x`, then `f` must be a unit on some small
neighborhood around `x`.
-/
theorem isUnit_res_of_isUnit_germ (U : Opens X) (f : X.presheaf.obj (op U)) (x : U)
    (h : IsUnit (X.presheaf.germ x f)) :
    ∃ (V : Opens X) (i : V ⟶ U) (_ : x.1 ∈ V), IsUnit (X.presheaf.map i.op f) := by
  obtain ⟨g', heq⟩ := h.exists_right_inv
  -- ⊢ ∃ V i x, IsUnit (↑(X.presheaf.map i.op) f)
  obtain ⟨V, hxV, g, rfl⟩ := X.presheaf.germ_exist x.1 g'
  -- ⊢ ∃ V i x, IsUnit (↑(X.presheaf.map i.op) f)
  let W := U ⊓ V
  -- ⊢ ∃ V i x, IsUnit (↑(X.presheaf.map i.op) f)
  have hxW : x.1 ∈ W := ⟨x.2, hxV⟩
  -- ⊢ ∃ V i x, IsUnit (↑(X.presheaf.map i.op) f)
  -- Porting note : `erw` can't write into `HEq`, so this is replaced with another `HEq` in the
  -- desired form
  replace heq : (X.presheaf.germ ⟨x.val, hxW⟩) ((X.presheaf.map (U.infLELeft V).op) f *
    (X.presheaf.map (U.infLERight V).op) g) = (X.presheaf.germ ⟨x.val, hxW⟩) 1
  · dsimp [germ]
    -- ⊢ ↑(Limits.colimit.ι ((OpenNhds.inclusion ↑x).op ⋙ X.presheaf) (op { obj := U  …
    erw [map_mul, map_one, show X.presheaf.germ ⟨x, hxW⟩ ((X.presheaf.map (U.infLELeft V).op) f) =
      X.presheaf.germ x f from X.presheaf.germ_res_apply (Opens.infLELeft U V) ⟨x.1, hxW⟩ f,
      show X.presheaf.germ ⟨x, hxW⟩ (X.presheaf.map (U.infLERight V).op g) =
      X.presheaf.germ ⟨x, hxV⟩ g from X.presheaf.germ_res_apply (Opens.infLERight U V) ⟨x.1, hxW⟩ g]
    exact heq
    -- 🎉 no goals
  obtain ⟨W', hxW', i₁, i₂, heq'⟩ := X.presheaf.germ_eq x.1 hxW hxW _ _ heq
  -- ⊢ ∃ V i x, IsUnit (↑(X.presheaf.map i.op) f)
  use W', i₁ ≫ Opens.infLELeft U V, hxW'
  -- ⊢ IsUnit (↑(X.presheaf.map (i₁ ≫ Opens.infLELeft U V).op) f)
  rw [(X.presheaf.map i₂.op).map_one, (X.presheaf.map i₁.op).map_mul] at heq'
  -- ⊢ IsUnit (↑(X.presheaf.map (i₁ ≫ Opens.infLELeft U V).op) f)
  rw [← comp_apply, ←X.presheaf.map_comp, ←comp_apply, ←X.presheaf.map_comp, ←op_comp] at heq'
  -- ⊢ IsUnit (↑(X.presheaf.map (i₁ ≫ Opens.infLELeft U V).op) f)
  exact isUnit_of_mul_eq_one _ _ heq'
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.RingedSpace.is_unit_res_of_is_unit_germ AlgebraicGeometry.RingedSpace.isUnit_res_of_isUnit_germ

/-- If a section `f` is a unit in each stalk, `f` must be a unit. -/
theorem isUnit_of_isUnit_germ (U : Opens X) (f : X.presheaf.obj (op U))
    (h : ∀ x : U, IsUnit (X.presheaf.germ x f)) : IsUnit f := by
  -- We pick a cover of `U` by open sets `V x`, such that `f` is a unit on each `V x`.
  choose V iVU m h_unit using fun x : U => X.isUnit_res_of_isUnit_germ U f x (h x)
  -- ⊢ IsUnit f
  have hcover : U ≤ iSup V
  -- ⊢ U ≤ iSup V
  · intro x hxU
    -- ⊢ x ∈ ↑(iSup V)
    -- Porting note : in Lean3 `rw` is sufficient
    erw [Opens.mem_iSup]
    -- ⊢ ∃ i, x ∈ V i
    exact ⟨⟨x, hxU⟩, m ⟨x, hxU⟩⟩
    -- 🎉 no goals
  -- Let `g x` denote the inverse of `f` in `U x`.
  choose g hg using fun x : U => IsUnit.exists_right_inv (h_unit x)
  -- ⊢ IsUnit f
  have ic : IsCompatible (sheaf X).val V g
  -- ⊢ IsCompatible (sheaf X).val V g
  -- swap
  · intro x y
    -- ⊢ ↑((sheaf X).val.map (Opens.infLELeft (V x) (V y)).op) (g x) = ↑((sheaf X).va …
    apply section_ext X.sheaf (V x ⊓ V y)
    -- ⊢ ∀ (x_1 : { x_1 // x_1 ∈ V x ⊓ V y }), ↑(germ (Sheaf.presheaf (sheaf X)) x_1) …
    rintro ⟨z, hzVx, hzVy⟩
    -- ⊢ ↑(germ (Sheaf.presheaf (sheaf X)) { val := z, property := (_ : z ∈ ↑(V x) ∧  …
    erw [germ_res_apply, germ_res_apply]
    -- ⊢ ↑(germ (Sheaf.presheaf (sheaf X)) ((fun x_1 => { val := ↑x_1, property := (_ …
    apply (IsUnit.mul_right_inj (h ⟨z, (iVU x).le hzVx⟩)).mp
    -- ⊢ ↑(germ X.presheaf { val := z, property := (_ : z ∈ ↑U) }) f * ↑(germ (Sheaf. …
    -- Porting note : now need explicitly typing the rewrites
    rw [←show X.presheaf.germ ⟨z, hzVx⟩ (X.presheaf.map (iVU x).op f) =
      X.presheaf.germ ⟨z, ((iVU x) ⟨z, hzVx⟩).2⟩ f from
      X.presheaf.germ_res_apply (iVU x) ⟨z, hzVx⟩ f]
    -- Porting note : change was not necessary in Lean3
    change X.presheaf.germ ⟨z, hzVx⟩ _ * (X.presheaf.germ ⟨z, hzVx⟩ _) =
      X.presheaf.germ ⟨z, hzVx⟩ _ * X.presheaf.germ ⟨z, hzVy⟩ (g y)
    rw [← RingHom.map_mul,
      congr_arg (X.presheaf.germ (⟨z, hzVx⟩ : V x)) (hg x),
      -- Porting note : now need explicitly typing the rewrites
      show X.presheaf.germ ⟨z, hzVx⟩ (X.presheaf.map (iVU x).op f) =
        X.presheaf.germ ⟨z, ((iVU x) ⟨z, hzVx⟩).2⟩ f from X.presheaf.germ_res_apply _ _ f,
      -- Porting note : now need explicitly typing the rewrites
      ← show X.presheaf.germ ⟨z, hzVy⟩ (X.presheaf.map (iVU y).op f) =
          X.presheaf.germ ⟨z, ((iVU x) ⟨z, hzVx⟩).2⟩ f from
          X.presheaf.germ_res_apply (iVU y) ⟨z, hzVy⟩ f,
      ← RingHom.map_mul,
      congr_arg (X.presheaf.germ (⟨z, hzVy⟩ : V y)) (hg y), RingHom.map_one, RingHom.map_one]
  -- We claim that these local inverses glue together to a global inverse of `f`.
  obtain ⟨gl, gl_spec, -⟩ := X.sheaf.existsUnique_gluing' V U iVU hcover g ic
  -- ⊢ IsUnit f
  apply isUnit_of_mul_eq_one f gl
  -- ⊢ f * gl = 1
  apply X.sheaf.eq_of_locally_eq' V U iVU hcover
  -- ⊢ ∀ (i : { x // x ∈ U }), ↑((sheaf X).val.map (iVU i).op) (f * gl) = ↑((sheaf  …
  intro i
  -- ⊢ ↑((sheaf X).val.map (iVU i).op) (f * gl) = ↑((sheaf X).val.map (iVU i).op) 1
  rw [RingHom.map_one, RingHom.map_mul, gl_spec]
  -- ⊢ ↑((sheaf X).val.map (iVU i).op) f * g i = 1
  exact hg i
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.RingedSpace.is_unit_of_is_unit_germ AlgebraicGeometry.RingedSpace.isUnit_of_isUnit_germ

/-- The basic open of a section `f` is the set of all points `x`, such that the germ of `f` at
`x` is a unit.
-/
def basicOpen {U : Opens X} (f : X.presheaf.obj (op U)) : Opens X where
  -- Porting note : `coe` does not work
  carrier := Subtype.val '' { x : U | IsUnit (X.presheaf.germ x f) }
  is_open' := by
    rw [isOpen_iff_forall_mem_open]
    -- ⊢ ∀ (x : ↑↑X.toPresheafedSpace), x ∈ Subtype.val '' {x | IsUnit (↑(germ X.pres …
    rintro _ ⟨x, hx, rfl⟩
    -- ⊢ ∃ t, t ⊆ Subtype.val '' {x | IsUnit (↑(germ X.presheaf x) f)} ∧ IsOpen t ∧ ↑ …
    obtain ⟨V, i, hxV, hf⟩ := X.isUnit_res_of_isUnit_germ U f x hx
    -- ⊢ ∃ t, t ⊆ Subtype.val '' {x | IsUnit (↑(germ X.presheaf x) f)} ∧ IsOpen t ∧ ↑ …
    use V.1
    -- ⊢ V.carrier ⊆ Subtype.val '' {x | IsUnit (↑(germ X.presheaf x) f)} ∧ IsOpen V. …
    refine' ⟨_, V.2, hxV⟩
    -- ⊢ V.carrier ⊆ Subtype.val '' {x | IsUnit (↑(germ X.presheaf x) f)}
    intro y hy
    -- ⊢ y ∈ Subtype.val '' {x | IsUnit (↑(germ X.presheaf x) f)}
    use (⟨y, i.le hy⟩ : U)
    -- ⊢ { val := y, property := (_ : y ∈ ↑U) } ∈ {x | IsUnit (↑(germ X.presheaf x) f …
    rw [Set.mem_setOf_eq]
    -- ⊢ IsUnit (↑(germ X.presheaf { val := y, property := (_ : y ∈ ↑U) }) f) ∧ ↑{ va …
    constructor
    -- ⊢ IsUnit (↑(germ X.presheaf { val := y, property := (_ : y ∈ ↑U) }) f)
    · convert RingHom.isUnit_map (X.presheaf.germ ⟨y, hy⟩) hf
      -- ⊢ ↑(germ X.presheaf { val := y, property := (_ : y ∈ ↑U) }) f = ↑(germ X.presh …
      exact (X.presheaf.germ_res_apply i ⟨y, hy⟩ f).symm
      -- 🎉 no goals
    · rfl
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.RingedSpace.basic_open AlgebraicGeometry.RingedSpace.basicOpen

@[simp]
theorem mem_basicOpen {U : Opens X} (f : X.presheaf.obj (op U)) (x : U) :
    ↑x ∈ X.basicOpen f ↔ IsUnit (X.presheaf.germ x f) := by
  constructor
  -- ⊢ ↑x ∈ basicOpen X f → IsUnit (↑(germ X.presheaf x) f)
  · rintro ⟨x, hx, a⟩; cases Subtype.eq a; exact hx
    -- ⊢ IsUnit (↑(germ X.presheaf x✝) f)
                       -- ⊢ IsUnit (↑(germ X.presheaf x) f)
                                           -- 🎉 no goals
  · intro h; exact ⟨x, h, rfl⟩
    -- ⊢ ↑x ∈ basicOpen X f
             -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.RingedSpace.mem_basic_open AlgebraicGeometry.RingedSpace.mem_basicOpen

@[simp]
theorem mem_top_basicOpen (f : X.presheaf.obj (op ⊤)) (x : X) :
    x ∈ X.basicOpen f ↔ IsUnit (X.presheaf.germ ⟨x, show x ∈ (⊤ : Opens X) by trivial⟩ f) :=
                                                                              -- 🎉 no goals
  mem_basicOpen X f ⟨x, _⟩
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.RingedSpace.mem_top_basic_open AlgebraicGeometry.RingedSpace.mem_top_basicOpen

theorem basicOpen_le {U : Opens X} (f : X.presheaf.obj (op U)) : X.basicOpen f ≤ U := by
  rintro _ ⟨x, _, rfl⟩; exact x.2
  -- ⊢ ↑x ∈ ↑U
                        -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.RingedSpace.basic_open_le AlgebraicGeometry.RingedSpace.basicOpen_le

/-- The restriction of a section `f` to the basic open of `f` is a unit. -/
theorem isUnit_res_basicOpen {U : Opens X} (f : X.presheaf.obj (op U)) :
    IsUnit (X.presheaf.map (@homOfLE (Opens X) _ _ _ (X.basicOpen_le f)).op f) := by
  apply isUnit_of_isUnit_germ
  -- ⊢ ∀ (x : { x // x ∈ basicOpen X f }), IsUnit (↑(germ X.presheaf x) (↑(X.preshe …
  rintro ⟨_, ⟨x, (hx : IsUnit _), rfl⟩⟩
  -- ⊢ IsUnit (↑(germ X.presheaf { val := ↑x, property := (_ : ∃ a, a ∈ {x | IsUnit …
  convert hx
  -- ⊢ ↑(germ X.presheaf { val := ↑x, property := (_ : ∃ a, a ∈ {x | IsUnit (↑(germ …
  convert X.presheaf.germ_res_apply _ _ _
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.RingedSpace.is_unit_res_basic_open AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen

@[simp]
theorem basicOpen_res {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (f : X.presheaf.obj U) :
    @basicOpen X (unop V) (X.presheaf.map i f) = unop V ⊓ @basicOpen X (unop U) f := by
  induction U using Opposite.rec'
  -- ⊢ basicOpen X (↑(X.presheaf.map i) f) = V.unop ⊓ basicOpen X f
  induction V using Opposite.rec'
  -- ⊢ basicOpen X (↑(X.presheaf.map i) f) = (op X✝).unop ⊓ basicOpen X f
  let g := i.unop; have : i = g.op := rfl; clear_value g; subst this
  -- ⊢ basicOpen X (↑(X.presheaf.map i) f) = (op X✝).unop ⊓ basicOpen X f
                   -- ⊢ basicOpen X (↑(X.presheaf.map i) f) = (op X✝).unop ⊓ basicOpen X f
                                           -- ⊢ basicOpen X (↑(X.presheaf.map i) f) = (op X✝).unop ⊓ basicOpen X f
                                                          -- ⊢ basicOpen X (↑(X.presheaf.map g.op) f) = (op X✝).unop ⊓ basicOpen X f
  ext; constructor
  -- ⊢ x✝ ∈ ↑(basicOpen X (↑(X.presheaf.map g.op) f)) ↔ x✝ ∈ ↑((op X✝).unop ⊓ basic …
       -- ⊢ x✝ ∈ ↑(basicOpen X (↑(X.presheaf.map g.op) f)) → x✝ ∈ ↑((op X✝).unop ⊓ basic …
  · rintro ⟨x, hx : IsUnit _, rfl⟩
    -- ⊢ ↑x ∈ ↑((op X✝).unop ⊓ basicOpen X f)
    erw [X.presheaf.germ_res_apply _ _ _] at hx
    -- ⊢ ↑x ∈ ↑((op X✝).unop ⊓ basicOpen X f)
    exact ⟨x.2, g x, hx, rfl⟩
    -- 🎉 no goals
  · rintro ⟨hxV, x, hx, rfl⟩
    -- ⊢ ↑x ∈ ↑(basicOpen X (↑(X.presheaf.map g.op) f))
    refine' ⟨⟨x, hxV⟩, (_ : IsUnit _), rfl⟩
    -- ⊢ IsUnit (↑(germ X.presheaf { val := ↑x, property := hxV }) (↑(X.presheaf.map  …
    erw [X.presheaf.germ_res_apply _ _ _]
    -- ⊢ IsUnit (↑(germ X.presheaf ((fun x => { val := ↑x, property := (_ : ↑x ∈ ↑(op …
    exact hx
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.RingedSpace.basic_open_res AlgebraicGeometry.RingedSpace.basicOpen_res

-- This should fire before `basicOpen_res`.
-- Porting note : this lemma is not in simple normal form because of `basicOpen_res`, as in Lean3
-- it is specifically said "This should fire before `basic_open_res`", this lemma is marked with
-- high priority
@[simp (high)]
theorem basicOpen_res_eq {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) [IsIso i] (f : X.presheaf.obj U) :
    @basicOpen X (unop V) (X.presheaf.map i f) = @RingedSpace.basicOpen X (unop U) f := by
  apply le_antisymm
  -- ⊢ basicOpen X (↑(X.presheaf.map i) f) ≤ basicOpen X f
  · rw [X.basicOpen_res i f]; exact inf_le_right
    -- ⊢ V.unop ⊓ basicOpen X f ≤ basicOpen X f
                              -- 🎉 no goals
  · have := X.basicOpen_res (inv i) (X.presheaf.map i f)
    -- ⊢ basicOpen X f ≤ basicOpen X (↑(X.presheaf.map i) f)
    rw [← comp_apply, ← X.presheaf.map_comp, IsIso.hom_inv_id, X.presheaf.map_id, id_apply] at this
    -- ⊢ basicOpen X f ≤ basicOpen X (↑(X.presheaf.map i) f)
    rw [this]
    -- ⊢ U.unop ⊓ basicOpen X (↑(X.presheaf.map i) f) ≤ basicOpen X (↑(X.presheaf.map …
    exact inf_le_right
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.RingedSpace.basic_open_res_eq AlgebraicGeometry.RingedSpace.basicOpen_res_eq

@[simp]
theorem basicOpen_mul {U : Opens X} (f g : X.presheaf.obj (op U)) :
    X.basicOpen (f * g) = X.basicOpen f ⊓ X.basicOpen g := by
  ext1
  -- ⊢ ↑(basicOpen X (f * g)) = ↑(basicOpen X f ⊓ basicOpen X g)
  dsimp [RingedSpace.basicOpen]
  -- ⊢ Subtype.val '' {x | IsUnit (↑(germ X.presheaf x) (f * g))} = Subtype.val ''  …
  rw [← Set.image_inter Subtype.coe_injective]
  -- ⊢ Subtype.val '' {x | IsUnit (↑(germ X.presheaf x) (f * g))} = (fun a => ↑a) ' …
  congr
  -- ⊢ Subtype.val '' {x | IsUnit (↑(germ X.presheaf x) (f * g))} = (fun a => ↑a) ' …
  ext x
  -- ⊢ x ∈ Subtype.val '' {x | IsUnit (↑(germ X.presheaf x) (f * g))} ↔ x ∈ (fun a  …
  simp [map_mul, Set.mem_image]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.RingedSpace.basic_open_mul AlgebraicGeometry.RingedSpace.basicOpen_mul

theorem basicOpen_of_isUnit {U : Opens X} {f : X.presheaf.obj (op U)} (hf : IsUnit f) :
    X.basicOpen f = U := by
  apply le_antisymm
  -- ⊢ basicOpen X f ≤ U
  · exact X.basicOpen_le f
    -- 🎉 no goals
  intro x hx
  -- ⊢ x ∈ ↑(basicOpen X f)
  erw [X.mem_basicOpen f (⟨x, hx⟩ : U)]
  -- ⊢ IsUnit (↑(germ X.presheaf { val := x, property := hx }) f)
  exact RingHom.isUnit_map _ hf
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.RingedSpace.basic_open_of_is_unit AlgebraicGeometry.RingedSpace.basicOpen_of_isUnit

end RingedSpace

end AlgebraicGeometry
