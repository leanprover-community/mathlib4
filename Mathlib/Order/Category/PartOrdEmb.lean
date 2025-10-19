/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Johan Commelin
-/
import Mathlib.Order.Category.PartOrd
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Category of partial orders, with order embeddings as morphisms

This defines `PartOrdEmb`, the category of partial orders with order embeddings
as morphisms.

-/

open CategoryTheory Limits

universe u

/-- The category of partial orders. -/
structure PartOrdEmb where
  /-- The underlying partially ordered type. -/
  (carrier : Type*)
  [str : PartialOrder carrier]

attribute [instance] PartOrdEmb.str

initialize_simps_projections PartOrdEmb (carrier → coe, -str)

namespace PartOrdEmb

instance : CoeSort PartOrdEmb (Type _) :=
  ⟨PartOrdEmb.carrier⟩

attribute [coe] PartOrdEmb.carrier

/-- Construct a bundled `PartOrdEmb` from the underlying type and typeclass. -/
abbrev of (X : Type*) [PartialOrder X] : PartOrdEmb := ⟨X⟩

/-- The type of morphisms in `PartOrdEmb R`. -/
@[ext]
structure Hom (X Y : PartOrdEmb.{u}) where
  private mk ::
  /-- The underlying `OrderEmbedding`. -/
  hom' : X ↪o Y

instance : Category PartOrdEmb.{u} where
  Hom X Y := Hom X Y
  id _ := ⟨RelEmbedding.refl _⟩
  comp f g := ⟨f.hom'.trans g.hom'⟩

instance : ConcreteCategory PartOrdEmb (· ↪o ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `PartOrdEmb` back into a `OrderEmbedding`. -/
abbrev Hom.hom {X Y : PartOrdEmb.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := PartOrdEmb) f

/-- Typecheck a `OrderEmbedding` as a morphism in `PartOrdEmb`. -/
abbrev ofHom {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ↪o Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := PartOrdEmb) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : PartOrdEmb.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
lemma coe_id {X : PartOrdEmb} : (𝟙 X : X → X) = id := rfl

@[simp]
lemma coe_comp {X Y Z : PartOrdEmb} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[simp]
lemma forget_map {X Y : PartOrdEmb} (f : X ⟶ Y) :
    (forget PartOrdEmb).map f = f := rfl

@[ext]
lemma ext {X Y : PartOrdEmb} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
theorem coe_of (X : Type u) [PartialOrder X] : (PartOrdEmb.of X : Type u) = X := rfl

lemma hom_id {X : PartOrdEmb} : (𝟙 X : X ⟶ X).hom = RelEmbedding.refl _ := rfl

/- Provided for rewriting. -/
lemma id_apply (X : PartOrdEmb) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
lemma hom_comp {X Y Z : PartOrdEmb} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom.trans g.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply {X Y Z : PartOrdEmb} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

lemma Hom.injective {X Y : PartOrdEmb.{u}} (f : X ⟶ Y) : Function.Injective f :=
  f.hom'.injective

lemma Hom.le_iff {X Y : PartOrdEmb.{u}} (f : X ⟶ Y) (x₁ x₂ : X) :
    f x₁ ≤ f x₂ ↔ x₁ ≤ x₂ :=
  f.hom'.map_rel_iff

@[ext]
lemma hom_ext {X Y : PartOrdEmb} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
lemma hom_ofHom {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ↪o Y) :
    (ofHom f).hom = f :=
  rfl

@[simp]
lemma ofHom_hom {X Y : PartOrdEmb} (f : X ⟶ Y) : ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {X : Type u} [PartialOrder X] : ofHom (RelEmbedding.refl _) = 𝟙 (of X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type u} [PartialOrder X] [PartialOrder Y] [PartialOrder Z]
    (f : X ↪o Y) (g : Y ↪o Z) :
    ofHom (f.trans g) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ↪o Y) (x : X) :
    (ofHom f) x = f x := rfl

lemma inv_hom_apply {X Y : PartOrdEmb} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

lemma hom_inv_apply {X Y : PartOrdEmb} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

instance hasForgetToPartOrd : HasForget₂ PartOrdEmb PartOrd where
  forget₂.obj X := .of X
  forget₂.map f := PartOrd.ofHom f.hom

/-- Constructs an equivalence between partial orders from an order isomorphism between them. -/
@[simps]
def Iso.mk {α β : PartOrdEmb.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
def dual : PartOrdEmb ⥤ PartOrdEmb where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `PartOrdEmb` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
def dualEquiv : PartOrdEmb ≌ PartOrdEmb where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X

end PartOrdEmb

theorem partOrdEmb_dual_comp_forget_to_pardOrd :
    PartOrdEmb.dual ⋙ forget₂ PartOrdEmb PartOrd =
      forget₂ PartOrdEmb PartOrd ⋙ PartOrd.dual :=
  rfl

namespace PartOrdEmb

variable {J : Type u} [SmallCategory J] [IsFiltered J] {F : J ⥤ PartOrdEmb.{u}}

namespace Limits

variable {c : Cocone (F ⋙ forget _)} (hc : IsColimit c)

@[nolint unusedArguments]
def CoconePt (_ : IsColimit c) : Type u := c.pt

open IsFiltered

instance : PartialOrder (CoconePt hc) where
  le x y := ∃ (j : J) (x' y' : F.obj j) (hx : c.ι.app j x' = x)
      (hy : c.ι.app j y' = y), x' ≤ y'
  le_refl x := by
    obtain ⟨j, x', hx⟩ := Types.jointly_surjective_of_isColimit hc x
    exact ⟨j, x', x', hx, hx, le_rfl⟩
  le_trans := by
    rintro x y z ⟨j, x₁, y₁, hx₁, hy₁, hxy⟩ ⟨k, y₂, z₁, hy₂, hz₁, hyz⟩
    obtain ⟨l, a, b, h⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff _ hc (xi := y₁) (xj := y₂)).1
        (hy₁.trans hy₂.symm)
    exact ⟨l, F.map a x₁, F.map b z₁,
      (ConcreteCategory.congr_hom (c.w a) x₁).trans hx₁,
      (ConcreteCategory.congr_hom (c.w b) z₁).trans hz₁,
      ((F.map a).hom.monotone hxy).trans
        (le_of_eq_of_le h ((F.map b).hom.monotone hyz))⟩
  le_antisymm := by
    rintro x y ⟨j, x₁, y₁, hx₁, hy₁, h₁⟩ ⟨k, y₂, x₂, hy₂, hx₂, h₂⟩
    obtain ⟨l, a, b, x₃, y₃, h₃, h₄, h₅, h₆⟩ :
        ∃ (l : J) (a : j ⟶ l) (b : k ⟶ l) (x₃ y₃ : _),
        x₃ = F.map a x₁ ∧ x₃ = F.map b x₂ ∧ y₃ = F.map a y₁ ∧ y₃ = F.map b y₂ := by
      obtain ⟨l₁, a, b, h₃⟩ :=
        (Types.FilteredColimit.isColimit_eq_iff _ hc (xi := x₁) (xj := x₂)).1
          (hx₁.trans hx₂.symm)
      obtain ⟨l₂, a', b', h₄⟩ :=
        (Types.FilteredColimit.isColimit_eq_iff _ hc (xi := y₁) (xj := y₂)).1
          (hy₁.trans hy₂.symm)
      obtain ⟨l, c, c', h₅, h₆⟩ := IsFiltered.bowtie a a' b b'
      exact ⟨l, a ≫ c, b ≫ c, F.map (a ≫ c) x₁, F.map (a' ≫ c') y₁, rfl,
        by simpa, by rw [h₅], by simpa [h₆]⟩
    have h₇ : x₃ = y₃ :=
      le_antisymm
        (by simpa only [h₃, h₅] using (F.map a).hom.monotone h₁)
        (by simpa only [h₄, h₆] using (F.map b).hom.monotone h₂)
    exact hx₁.symm.trans ((ConcreteCategory.congr_hom (c.w a) x₁).symm.trans
      ((congr_arg (c.ι.app l) (h₃.symm.trans (h₇.trans h₅))).trans
        ((ConcreteCategory.congr_hom (c.w a) y₁).trans hy₁)))

@[simps]
def cocone : Cocone F where
  pt := .of (CoconePt hc)
  ι.app j := ofHom
    { toFun := c.ι.app j
      inj' x y h := by
        obtain ⟨k, a, ha⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc x y).1 h
        exact (F.map a).injective  ha
      map_rel_iff' {x y} := by
        refine ⟨?_, fun h ↦ ⟨j, x, y, rfl, rfl, h⟩⟩
        rintro ⟨k, x', y', hx', hy', h⟩
        sorry }
  ι.naturality _ _ f := by ext x; exact ConcreteCategory.congr_hom (c.w f) x

def CoconePt.desc (s : Cocone F) : CoconePt hc ↪o s.pt where
  toFun := hc.desc ((forget _).mapCocone s)
  inj' x y h := by
    obtain ⟨j, x', y', rfl, rfl⟩ :
        ∃ (j : J) (x' y' : F.obj j), c.ι.app j x' = x ∧ c.ι.app j y' = y := by
      sorry
    have := ((congr_fun (hc.fac ((forget _).mapCocone s) j) x').symm.trans h).trans
      (congr_fun (hc.fac ((forget _).mapCocone s) j) y')
    obtain rfl := (s.ι.app j).injective this
    rfl
  map_rel_iff' := sorry

@[simp]
lemma CoconePt.fac_apply (s : Cocone F) (j : J) (x : F.obj j) :
    CoconePt.desc hc s (c.ι.app j x) = s.ι.app j x :=
  congr_fun (hc.fac ((forget _).mapCocone s) j) x

def isColimitCocone : IsColimit (cocone hc) where
  desc s := ofHom (CoconePt.desc hc s)
  uniq s m hm := by
    ext x
    obtain ⟨j, x, rfl⟩ := Types.jointly_surjective_of_isColimit hc x
    exact ((ConcreteCategory.congr_hom (hm j)) x).trans (CoconePt.fac_apply hc s j x).symm

instance : HasColimit F where
  exists_colimit := ⟨_, isColimitCocone (colimit.isColimit (F ⋙ forget _))⟩

instance : HasColimitsOfShape J PartOrdEmb.{u} where

end Limits

end PartOrdEmb
