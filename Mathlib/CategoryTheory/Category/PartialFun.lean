/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.CategoryTheory.Category.Pointed
public import Mathlib.Data.PFun

/-!
# The category of types with partial functions

This defines `PartialFun`, the category of types equipped with partial functions.
This category is classically equivalent to the category of pointed types.
The reason it doesn't hold constructively stems from the difference between `Part` and `Option`.
Both can model partial functions, but the latter forces a decidable domain.

Precisely, `PartialFunToPointed` turns a partial function `α →. β` into a function
`Option α → Option β` by sending to `none` the undefined values (and `none` to `none`).
But being defined is (generally) undecidable while being sent to `none` is decidable.
So it can't be constructive.

## References

* [nLab, *The category of sets and partial functions*](https://ncatlab.org/nlab/show/partial+function)
-/

@[expose] public section

open CategoryTheory Option

universe u

/-- The category of types equipped with partial functions. -/
def PartialFun : Type (u + 1) := Type u

namespace PartialFun

instance : CoeSort PartialFun Type* :=
  ⟨id⟩

/-- Turns a type into a `PartialFun`. -/
def of (X : Type u) : PartialFun :=
  X

instance : Inhabited PartialFun.{u} :=
  ⟨PartialFun.of PUnit⟩

-- TODO: wrap morphisms in this category into a one-field `PFun.Hom` structure
instance largeCategory : LargeCategory.{u} PartialFun where
  Hom X Y := PFun X Y
  id X := PFun.id X
  comp f g := g.comp f

/-- Constructs a partial function isomorphism between types from an equivalence between them.
Note: `@[simps!]` is used here to force projections through the new `PFun` structure. -/
@[simps!]
def Iso.mk {α β : PartialFun.{u}} (e : α ≃ β) : α ≅ β where
  hom := PFun.lift e
  inv := PFun.lift e.symm
  hom_inv_id := (PFun.coe_comp _ _).symm.trans (by
    simp only [Equiv.symm_comp_self, PFun.coe_id]; rfl)
  inv_hom_id := (PFun.coe_comp _ _).symm.trans (by
    simp only [Equiv.self_comp_symm, PFun.coe_id]; rfl)

end PartialFun

/-- The forgetful functor from `Type` to `PartialFun` which forgets that the maps are total.
Note: `@[simps!]` is used here to force projections through the new `PFun` structure. -/
@[simps!]
def typeToPartialFun : Type u ⥤ PartialFun where
  obj X := X
  map f := PFun.lift f
  map_comp f g := PFun.coe_comp g f

instance : typeToPartialFun.Faithful where
  map_injective {_ _} _ _ h := by
    ext x; exact congrFun (PFun.lift_injective h) x

namespace PartialFun

/-- Internal helper lemma for `pointedToPartialFun.map_comp`. -/
theorem pointed_comp_toSubtype_aux {X Y Z : Pointed} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (PFun.mk (PFun.toSubtype (fun x => x ≠ Z.point) g.toFun ∘
      (Subtype.val : {y : Y // y ≠ Y.point} → Y))).comp
      (PFun.mk (PFun.toSubtype (fun x => x ≠ Y.point) f.toFun ∘
        (Subtype.val : {x : X // x ≠ X.point} → X))) =
    PFun.mk (PFun.toSubtype (fun x => x ≠ Z.point) (g.toFun ∘ f.toFun) ∘
      (Subtype.val : {x : X // x ≠ X.point} → X)) := by
  ext ⟨a, ha⟩ ⟨c, hc⟩
  simp only [PFun.comp_apply, PFun.mk_apply, Function.comp_apply,
             Part.mem_bind_iff, PFun.mem_toSubtype_iff]
  constructor
  · rintro ⟨b, hb_eq, h_final⟩
    rw [← hb_eq]; exact h_final
  · intro h
    exact ⟨⟨f.toFun a, fun h_eq => hc (h ▸ h_eq ▸ g.map_point)⟩, rfl, h⟩

end PartialFun

/-- The functor which deletes the point of a pointed type. In return, this makes the maps partial.
This is the computable part of the equivalence `PartialFunEquivPointed`. -/
@[simps! obj map]
def pointedToPartialFun : Pointed.{u} ⥤ PartialFun where
  obj X := PartialFun.of { x : X // x ≠ X.point }
  map f := PFun.mk (PFun.toSubtype _ f.toFun ∘ Subtype.val)
  map_id _ :=
    PFun.ext fun _ b =>
      PFun.mem_toSubtype_iff (b := b).trans (Subtype.coe_inj.trans Part.mem_some_iff.symm)
  map_comp f g := (PartialFun.pointed_comp_toSubtype_aux f g).symm

open Classical in
/-- The functor which maps undefined values to a new point. This makes the maps total and creates
pointed types. This is the noncomputable part of the equivalence `PartialFunEquivPointed`. It can't
be computable because `= Option.none` is decidable while the domain of a general `Part` isn't. -/
noncomputable def partialFunToPointed : PartialFun ⥤ Pointed where
  obj X := ⟨Option X, none⟩
  map f := ⟨Option.elim' none fun a => (f.toFun a).toOption, rfl⟩
  map_id X := Pointed.Hom.ext <|
    funext fun o => Option.recOn o rfl fun a => by
      dsimp [CategoryStruct.id]
      convert Part.some_toOption a
  map_comp f g := Pointed.Hom.ext <|
    funext fun o => Option.recOn o rfl fun a => by
      dsimp [CategoryStruct.comp]
      rw [Part.bind_toOption]
      -- Splitting on the Option natively evaluates the bound state, matching Pointed behavior
      cases (f.toFun a).toOption <;> rfl

/-- The equivalence induced by `PartialFunToPointed` and `PointedToPartialFun`. -/
@[simps! functor inverse]
noncomputable def partialFunEquivPointed : PartialFun.{u} ≌ Pointed where
  functor := partialFunToPointed
  inverse := pointedToPartialFun
  unitIso := NatIso.ofComponents (fun X => PartialFun.Iso.mk
      { toFun := fun a => Subtype.mk (some a) (some_ne_none a)
        invFun := fun a => Option.get _ (Option.ne_none_iff_isSome.1 a.property)
        left_inv := fun _ => Option.get_some _ _
        right_inv := fun ⟨a, ha⟩ => Subtype.ext (Option.some_get _) })
      -- TODO(PFun-refactor): further golf this proof once global simp sets for PFun are established
      -- Stability Note: This proof uses explicit `change` and `erw` to bypass defeq boundaries and
      -- is fragile.
      fun {X Y} f => PFun.ext fun a ⟨b_val, hb⟩ => by
        classical
        cases b_val with
        | none => exact (hb rfl).elim
        | some b =>
          dsimp [PartialFun.Iso.mk, CategoryStruct.comp, pointedToPartialFun,
            partialFunToPointed, PFun.lift, PartialFun.of, PFun.comp]
          constructor
          · intro h
            change _ ∈ (f.toFun a).bind _ at h
            obtain ⟨c, hc_mem, hc_eq⟩ := Part.mem_bind_iff.mp h
            have h_eq : b = c :=
            Option.some_inj.mp (Subtype.ext_iff.mp (Part.mem_some_iff.mp hc_eq))
            subst h_eq
            change _ ∈ (Part.some _).bind _
            erw [Part.bind_some, PFun.mem_toSubtype_iff]
            exact (Part.mem_toOption.mpr hc_mem).symm
          · intro h
            change _ ∈ (Part.some _).bind _ at h
            erw [Part.bind_some, PFun.mem_toSubtype_iff] at h
            change _ ∈ (f.toFun a).bind _
            exact Part.mem_bind_iff.mpr ⟨b, Part.mem_toOption.mp h.symm,
              Part.mem_some_iff.mpr (Subtype.ext rfl)⟩
  counitIso :=
    NatIso.ofComponents
      (fun X ↦ by
        classical
        exact Pointed.Iso.mk (Equiv.optionSubtypeNe X.point) rfl)
      fun {X Y} f ↦ Pointed.Hom.ext <| funext fun a ↦ by
        classical
        obtain _ | ⟨a, ha⟩ := a
        · exact f.map_point.symm
        dsimp [CategoryStruct.comp]
        change Equiv.optionSubtypeNe Y.point
          ((PFun.toSubtype (fun x => x ≠ Y.point) f.toFun a).toOption) = f.toFun a
        simp only [PFun.toOption_toSubtype]
        split_ifs with h <;> aesop
  functor_unitIso_comp X := by
    ext (_ | x)
    · rfl
    · classical
      simp [partialFunToPointed, PartialFun.Iso.mk, PFun.lift]
      rfl

/-- Forgetting that maps are total and making them total again by adding a point is the same as just
adding a point. -/
@[simps!]
noncomputable def typeToPartialFunIsoPartialFunToPointed :
    typeToPartialFun ⋙ partialFunToPointed ≅ typeToPointed :=
  NatIso.ofComponents
    (fun X => Pointed.Iso.mk (Equiv.refl (Option X)) rfl)
    fun {X Y} f => Pointed.Hom.ext <| funext fun a => by
      cases a with
      | none => rfl
      | some x =>
        dsimp [partialFunToPointed, typeToPartialFun, typeToPointed, PFun.lift]
        erw [Part.some_toOption]
