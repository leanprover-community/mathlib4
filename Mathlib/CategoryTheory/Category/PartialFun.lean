/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.Data.PFun

/-!
# The category of types with partial functions

This defines `PartialFun`, the category of types equipped with partial functions.

This category is classically equivalent to the category of pointed types. The reason it doesn't hold
constructively stems from the difference between `Part` and `Option`. Both can model partial
functions, but the latter forces a decidable domain.

Precisely, `PartialFunToPointed` turns a partial function `α →. β` into a function
`Option α → Option β` by sending to `none` the undefined values (and `none` to `none`). But being
defined is (generally) undecidable while being sent to `none` is decidable. So it can't be
constructive.

## References

* [nLab, *The category of sets and partial functions*]
  (https://ncatlab.org/nlab/show/partial+function)
-/

open CategoryTheory Option

universe u

/-- The category of types equipped with partial functions. -/
def PartialFun : Type _ :=
  Type*

namespace PartialFun

instance : CoeSort PartialFun Type* :=
  ⟨id⟩

/-- Turns a type into a `PartialFun`. -/
def of : Type* → PartialFun :=
  id

instance : Inhabited PartialFun :=
  ⟨Type*⟩

instance largeCategory : LargeCategory.{u} PartialFun where
  Hom := PFun
  id := PFun.id
  comp f g := g.comp f
  id_comp := @PFun.comp_id
  comp_id := @PFun.id_comp
  assoc _ _ _ := (PFun.comp_assoc _ _ _).symm

/-- Constructs a partial function isomorphism between types from an equivalence between them. -/
@[simps]
def Iso.mk {α β : PartialFun.{u}} (e : α ≃ β) : α ≅ β where
  hom x := e x
  inv x := e.symm x
  hom_inv_id := (PFun.coe_comp _ _).symm.trans (by
    simp only [Equiv.symm_comp_self, PFun.coe_id]
    rfl)
  inv_hom_id := (PFun.coe_comp _ _).symm.trans (by
    simp only [Equiv.self_comp_symm, PFun.coe_id]
    rfl)

end PartialFun

/-- The forgetful functor from `Type` to `PartialFun` which forgets that the maps are total. -/
def typeToPartialFun : Type u ⥤ PartialFun where
  obj := id
  map := @PFun.lift
  map_comp _ _ := PFun.coe_comp _ _

instance : typeToPartialFun.Faithful where
  map_injective {_ _} := PFun.lift_injective

-- b ∈ PFun.toSubtype (fun x ↦ x ≠ X.point) Subtype.val a ↔ b ∈ Part.some a
/-- The functor which deletes the point of a pointed type. In return, this makes the maps partial.
This is the computable part of the equivalence `PartialFunEquivPointed`. -/
@[simps obj map]
def pointedToPartialFun : Pointed.{u} ⥤ PartialFun where
  obj X := { x : X // x ≠ X.point }
  map f := PFun.toSubtype _ f.toFun ∘ Subtype.val
  map_id _ :=
    PFun.ext fun _ b =>
      PFun.mem_toSubtype_iff (b := b).trans (Subtype.coe_inj.trans Part.mem_some_iff.symm)
  map_comp f g := by
    -- Porting note: the proof was changed because the original mathlib3 proof no longer works
    apply PFun.ext _
    rintro ⟨a, ha⟩ ⟨c, hc⟩
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨⟨fun h₀ => h₁ ((congr_arg g.toFun h₀).trans g.map_point), h₁⟩, h₂⟩
    · rintro ⟨_, _, _⟩
      exact ⟨_, rfl⟩

/-- The functor which maps undefined values to a new point. This makes the maps total and creates
pointed types. This is the noncomputable part of the equivalence `PartialFunEquivPointed`. It can't
be computable because `= Option.none` is decidable while the domain of a general `Part` isn't. -/
@[simps obj map]
noncomputable def partialFunToPointed : PartialFun ⥤ Pointed := by
  classical
  exact
    { obj := fun X => ⟨Option X, none⟩
      map := fun f => ⟨Option.elim' none fun a => (f a).toOption, rfl⟩
      map_id := fun X => Pointed.Hom.ext <| funext fun o => Option.recOn o rfl fun a => (by
        dsimp [CategoryStruct.id]
        convert Part.some_toOption a)
      map_comp := fun f g => Pointed.Hom.ext <| funext fun o => Option.recOn o rfl fun a => by
        dsimp [CategoryStruct.comp]
        rw [Part.bind_toOption g (f a), Option.elim'_eq_elim] }

/-- The equivalence induced by `PartialFunToPointed` and `PointedToPartialFun`.
`Part.equivOption` made functorial. -/
@[simps!]
noncomputable def partialFunEquivPointed : PartialFun.{u} ≌ Pointed where
  functor := partialFunToPointed
  inverse := pointedToPartialFun
  unitIso := NatIso.ofComponents (fun X => PartialFun.Iso.mk
      { toFun := fun a => ⟨some a, some_ne_none a⟩
        invFun := fun a => Option.get _ (Option.ne_none_iff_isSome.1 a.2)
        left_inv := fun _ => Option.get_some _ _
        right_inv := fun a => by simp only [some_get, Subtype.coe_eta] })
      fun f =>
        PFun.ext fun a b => by
          dsimp [PartialFun.Iso.mk, CategoryStruct.comp, pointedToPartialFun]
          rw [Part.bind_some]
          -- Porting note: the proof below has changed a lot because
          -- `Part.mem_bind_iff` means that `b ∈ Part.bind f g` is equivalent
          -- to `∃ (a : α), a ∈ f ∧ b ∈ g a`, while in mathlib3 it was equivalent
          -- to `∃ (a : α) (H : a ∈ f), b ∈ g a`
          refine (Part.mem_bind_iff.trans ?_).trans PFun.mem_toSubtype_iff.symm
          obtain ⟨b | b, hb⟩ := b
          · exact (hb rfl).elim
          · dsimp [Part.toOption]
            simp_rw [Part.mem_some_iff, Subtype.mk_eq_mk]
            constructor
            · rintro ⟨_, ⟨h₁, h₂⟩, h₃⟩
              rw [h₃, ← h₂, dif_pos h₁]
            · intro h
              split_ifs at h with ha
              rw [some_inj] at h
              exact ⟨b, ⟨ha, h.symm⟩, rfl⟩
  counitIso :=
    NatIso.ofComponents
      (fun X ↦ Pointed.Iso.mk (by classical exact Equiv.optionSubtypeNe X.point) (by rfl))
      fun {X Y} f ↦ Pointed.Hom.ext <| funext fun a ↦ by
        obtain _ | ⟨a, ha⟩ := a
        · exact f.map_point.symm
        simp_all [Option.casesOn'_eq_elim, Part.elim_toOption]
  functor_unitIso_comp X := by
    ext (_ | x)
    · rfl
    · simp
      rfl

/-- Forgetting that maps are total and making them total again by adding a point is the same as just
adding a point. -/
@[simps!]
noncomputable def typeToPartialFunIsoPartialFunToPointed :
    typeToPartialFun ⋙ partialFunToPointed ≅ typeToPointed :=
  NatIso.ofComponents
    (fun _ =>
      { hom := ⟨id, rfl⟩
        inv := ⟨id, rfl⟩
        hom_inv_id := rfl
        inv_hom_id := rfl })
    fun f =>
    Pointed.Hom.ext <|
      funext fun a => Option.recOn a rfl fun a => by
        convert Part.some_toOption _
        simpa using (Part.get_eq_iff_mem (by trivial)).mp rfl
