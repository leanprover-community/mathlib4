/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.limits.shapes.types
! leanprover-community/mathlib commit 5dc6092d09e5e489106865241986f7f2ad28d4c8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Tactic.CategoryTheory.Elementwise

/-!
# Special shapes for limits in `Type`.

The general shape (co)limits defined in `CategoryTheory.Limits.Types`
are intended for use through the limits API,
and the actual implementation should mostly be considered "sealed".

In this file, we provide definitions of the "standard" special shapes of limits in `Type`,
giving the expected definitional implementation:
* the terminal object is `PUnit`
* the binary product of `X` and `Y` is `X × Y`
* the product of a family `f : J → Type` is `Π j, f j`
* the coproduct of a family `f : J → Type` is `Σ j, f j`
* the binary coproduct of `X` and `Y` is the sum type `X ⊕ Y`
* the equalizer of a pair of maps `(g, h)` is the subtype `{x : Y // g x = h x}`
* the coequalizer of a pair of maps `(f, g)` is the quotient of `Y` by `∀ x : Y, f x ~ g x`
* the pullback of `f : X ⟶ Z` and `g : Y ⟶ Z` is the subtype `{ p : X × Y // f p.1 = g p.2 }`
  of the product

We first construct terms of `IsLimit` and `LimitCone`, and then provide isomorphisms with the
types generated by the `HasLimit` API.

As an example, when setting up the monoidal category structure on `Type`
we use the `Types.terminalLimitCone` and `Types.binaryProductLimitCone` definitions.
-/


universe v u

open CategoryTheory Limits

namespace CategoryTheory.Limits.Types

instance {β : Type v} (f : β → TypeMax.{v, u}) : HasProduct f :=
HasLimitsOfShape.has_limit (Discrete.functor f)

-- This must have higher priority than the instance for `TypeMax`.
-- (Merely being defined later is enough, but that is fragile.)
instance (priority := high) {β : Type v} (f : β → Type v) : HasProduct f :=
HasLimitsOfShape.has_limit (Discrete.functor f)

/-- A restatement of `Types.Limit.lift_π_apply` that uses `Pi.π` and `Pi.lift`. -/
@[simp 1001]
theorem pi_lift_π_apply {β : Type v} (f : β → TypeMax.{v, u}) {P : TypeMax.{v, u}}
    (s : ∀ b, P ⟶ f b) (b : β) (x : P) :
    (Pi.π f b : (piObj f) → f b) (@Pi.lift β _ _ f _ P s x) = s b x :=
  congr_fun (limit.lift_π (Fan.mk P s) ⟨b⟩) x
#align category_theory.limits.types.pi_lift_π_apply CategoryTheory.Limits.Types.pi_lift_π_apply

/-- A restatement of `Types.Limit.lift_π_apply` that uses `Pi.π` and `Pi.lift`,
with specialized universes. -/
@[simp 1001]
theorem pi_lift_π_apply' {β : Type v} (f : β → Type v) {P : Type v}
    (s : ∀ b, P ⟶ f b) (b : β) (x : P) :
    (Pi.π f b : (piObj f) → f b) (@Pi.lift β _ _ f _ P s x) = s b x :=
  congr_fun (limit.lift_π (Fan.mk P s) ⟨b⟩) x
#align category_theory.limits.types.pi_lift_π_apply' CategoryTheory.Limits.Types.pi_lift_π_apply'

/-- A restatement of `Types.Limit.map_π_apply` that uses `Pi.π` and `Pi.map`. -/
@[simp 1001]
theorem pi_map_π_apply {β : Type v} {f g : β → TypeMax.{v, u}} (α : ∀ j, f j ⟶ g j) (b : β) (x) :
    (Pi.π g b : ∏ g → g b) (Pi.map α x) = α b ((Pi.π f b : ∏ f → f b) x) :=
  Limit.map_π_apply _ _ _
#align category_theory.limits.types.pi_map_π_apply CategoryTheory.Limits.Types.pi_map_π_apply

/-- A restatement of `Types.Limit.map_π_apply` that uses `Pi.π` and `Pi.map`,
with specialized universes. -/
@[simp 1001]
theorem pi_map_π_apply' {β : Type v} {f g : β → Type v} (α : ∀ j, f j ⟶ g j) (b : β) (x) :
    (Pi.π g b : ∏ g → g b) (Pi.map α x) = α b ((Pi.π f b : ∏ f → f b) x) :=
  Limit.map_π_apply' _ _ _
#align category_theory.limits.types.pi_map_π_apply' CategoryTheory.Limits.Types.pi_map_π_apply'

/-- The category of types has `PUnit` as a terminal object. -/
def terminalLimitCone : Limits.LimitCone (Functor.empty (Type u)) where
  -- porting note: tidy was able to fill the structure automatically
  cone :=
    { pt := PUnit
      π := (Functor.uniqueFromEmpty _).hom }
  isLimit :=
    { lift := fun _ _ => PUnit.unit
      fac := fun _ => by rintro ⟨⟨⟩⟩
      uniq := fun _ _ _ => by
        funext
        apply Subsingleton.elim }
#align category_theory.limits.types.terminal_limit_cone CategoryTheory.Limits.Types.terminalLimitCone

/-- The terminal object in `Type u` is `PUnit`. -/
noncomputable def terminalIso : ⊤_ Type u ≅ PUnit :=
  limit.isoLimitCone terminalLimitCone.{u, 0}
#align category_theory.limits.types.terminal_iso CategoryTheory.Limits.Types.terminalIso

/-- The terminal object in `Type u` is `PUnit`. -/
noncomputable def isTerminalPunit : IsTerminal (PUnit : Type u) :=
  terminalIsTerminal.ofIso terminalIso
#align category_theory.limits.types.is_terminal_punit CategoryTheory.Limits.Types.isTerminalPunit

/-- The category of types has `PEmpty` as an initial object. -/
def initialColimitCocone : Limits.ColimitCocone (Functor.empty (Type u)) where
  -- porting note: tidy was able to fill the structure automatically
  cocone :=
    { pt := PEmpty
      ι := (Functor.uniqueFromEmpty _).inv }
  isColimit :=
    { desc := fun _ => by rintro ⟨⟩
      fac := fun _ => by rintro ⟨⟨⟩⟩
      uniq := fun _ _ _ => by funext x; cases x }
#align category_theory.limits.types.initial_colimit_cocone CategoryTheory.Limits.Types.initialColimitCocone

/-- The initial object in `Type u` is `PEmpty`. -/
noncomputable def initialIso : ⊥_ Type u ≅ PEmpty :=
  colimit.isoColimitCocone initialColimitCocone.{u, 0}
#align category_theory.limits.types.initial_iso CategoryTheory.Limits.Types.initialIso

/-- The initial object in `Type u` is `PEmpty`. -/
noncomputable def isInitialPunit : IsInitial (PEmpty : Type u) :=
  initialIsInitial.ofIso initialIso
#align category_theory.limits.types.is_initial_punit CategoryTheory.Limits.Types.isInitialPunit

open CategoryTheory.Limits.WalkingPair

-- We manually generate the other projection lemmas since the simp-normal form for the legs is
-- otherwise not created correctly.
/-- The product type `X × Y` forms a cone for the binary product of `X` and `Y`. -/
@[simps! pt]
def binaryProductCone (X Y : Type u) : BinaryFan X Y :=
  BinaryFan.mk _root_.Prod.fst _root_.Prod.snd
#align category_theory.limits.types.binary_product_cone CategoryTheory.Limits.Types.binaryProductCone

@[simp]
theorem binaryProductCone_fst (X Y : Type u) : (binaryProductCone X Y).fst = _root_.Prod.fst :=
  rfl
#align category_theory.limits.types.binary_product_cone_fst CategoryTheory.Limits.Types.binaryProductCone_fst

@[simp]
theorem binaryProductCone_snd (X Y : Type u) : (binaryProductCone X Y).snd = _root_.Prod.snd :=
  rfl
#align category_theory.limits.types.binary_product_cone_snd CategoryTheory.Limits.Types.binaryProductCone_snd

/-- The product type `X × Y` is a binary product for `X` and `Y`. -/
@[simps]
def binaryProductLimit (X Y : Type u) : IsLimit (binaryProductCone X Y) where
  lift (s : BinaryFan X Y) x := (s.fst x, s.snd x)
  fac _ j := Discrete.recOn j fun j => WalkingPair.casesOn j rfl rfl
  uniq _ _ w := funext fun x => Prod.ext (congr_fun (w ⟨left⟩) x) (congr_fun (w ⟨right⟩) x)
#align category_theory.limits.types.binary_product_limit CategoryTheory.Limits.Types.binaryProductLimit

/-- The category of types has `X × Y`, the usual cartesian product,
as the binary product of `X` and `Y`.
-/
@[simps]
def binaryProductLimitCone (X Y : Type u) : Limits.LimitCone (pair X Y) :=
  ⟨_, binaryProductLimit X Y⟩
#align category_theory.limits.types.binary_product_limit_cone CategoryTheory.Limits.Types.binaryProductLimitCone

/-- The categorical binary product in `Type u` is cartesian product. -/
noncomputable def binaryProductIso (X Y : Type u) : Limits.prod X Y ≅ X × Y :=
  limit.isoLimitCone (binaryProductLimitCone X Y)
#align category_theory.limits.types.binary_product_iso CategoryTheory.Limits.Types.binaryProductIso

@[elementwise (attr := simp)]
theorem binaryProductIso_hom_comp_fst (X Y : Type u) :
    (binaryProductIso X Y).hom ≫ _root_.Prod.fst = Limits.prod.fst :=
  limit.isoLimitCone_hom_π (binaryProductLimitCone X Y) ⟨WalkingPair.left⟩
#align category_theory.limits.types.binary_product_iso_hom_comp_fst CategoryTheory.Limits.Types.binaryProductIso_hom_comp_fst

@[elementwise (attr := simp)]
theorem binaryProductIso_hom_comp_snd (X Y : Type u) :
    (binaryProductIso X Y).hom ≫ _root_.Prod.snd = Limits.prod.snd :=
  limit.isoLimitCone_hom_π (binaryProductLimitCone X Y) ⟨WalkingPair.right⟩
#align category_theory.limits.types.binary_product_iso_hom_comp_snd CategoryTheory.Limits.Types.binaryProductIso_hom_comp_snd

@[elementwise (attr := simp)]
theorem binaryProductIso_inv_comp_fst (X Y : Type u) :
    (binaryProductIso X Y).inv ≫ Limits.prod.fst = _root_.Prod.fst :=
  limit.isoLimitCone_inv_π (binaryProductLimitCone X Y) ⟨WalkingPair.left⟩
#align category_theory.limits.types.binary_product_iso_inv_comp_fst CategoryTheory.Limits.Types.binaryProductIso_inv_comp_fst

@[elementwise (attr := simp)]
theorem binaryProductIso_inv_comp_snd (X Y : Type u) :
    (binaryProductIso X Y).inv ≫ Limits.prod.snd = _root_.Prod.snd :=
  limit.isoLimitCone_inv_π (binaryProductLimitCone X Y) ⟨WalkingPair.right⟩
#align category_theory.limits.types.binary_product_iso_inv_comp_snd CategoryTheory.Limits.Types.binaryProductIso_inv_comp_snd

-- porting note: it was originally @[simps (config := { typeMd := reducible })]
-- We add the option `type_md` to tell `@[simps]` to not treat homomorphisms `X ⟶ Y` in `Type*` as
-- a function type
/-- The functor which sends `X, Y` to the product type `X × Y`. -/
@[simps]
def binaryProductFunctor : Type u ⥤ Type u ⥤ Type u where
  obj X :=
    { obj := fun Y => X × Y
      map := fun { Y₁ Y₂} f => (binaryProductLimit X Y₂).lift
        (BinaryFan.mk _root_.Prod.fst (_root_.Prod.snd ≫ f)) }
  map {X₁ X₂} f :=
    { app := fun Y =>
      (binaryProductLimit X₂ Y).lift (BinaryFan.mk (_root_.Prod.fst ≫ f) _root_.Prod.snd) }
#align category_theory.limits.types.binary_product_functor CategoryTheory.Limits.Types.binaryProductFunctor

/-- The product functor given by the instance `HasBinaryProducts (Type u)` is isomorphic to the
explicit binary product functor given by the product type.
-/
noncomputable def binaryProductIsoProd : binaryProductFunctor ≅ (prod.functor : Type u ⥤ _) := by
  refine' NatIso.ofComponents (fun X => _) (fun _ => _)
  · refine' NatIso.ofComponents (fun Y => _) (fun _ => _)
    · exact ((limit.isLimit _).conePointUniqueUpToIso (binaryProductLimit X Y)).symm
    · apply Limits.prod.hom_ext <;> simp <;> rfl
  · ext : 2
    apply Limits.prod.hom_ext <;> simp <;> rfl
#align category_theory.limits.types.binary_product_iso_prod CategoryTheory.Limits.Types.binaryProductIsoProd

/-- The sum type `X ⊕ Y` forms a cocone for the binary coproduct of `X` and `Y`. -/
@[simps!]
def binaryCoproductCocone (X Y : Type u) : Cocone (pair X Y) :=
  BinaryCofan.mk Sum.inl Sum.inr
#align category_theory.limits.types.binary_coproduct_cocone CategoryTheory.Limits.Types.binaryCoproductCocone

/-- The sum type `X ⊕ Y` is a binary coproduct for `X` and `Y`. -/
@[simps]
def binaryCoproductColimit (X Y : Type u) : IsColimit (binaryCoproductCocone X Y) where
  desc := fun s : BinaryCofan X Y => Sum.elim s.inl s.inr
  fac _ j := Discrete.recOn j fun j => WalkingPair.casesOn j rfl rfl
  uniq _ _ w := funext fun x => Sum.casesOn x (congr_fun (w ⟨left⟩)) (congr_fun (w ⟨right⟩))
#align category_theory.limits.types.binary_coproduct_colimit CategoryTheory.Limits.Types.binaryCoproductColimit

/-- The category of types has `X ⊕ Y`,
as the binary coproduct of `X` and `Y`.
-/
def binaryCoproductColimitCocone (X Y : Type u) : Limits.ColimitCocone (pair X Y) :=
  ⟨_, binaryCoproductColimit X Y⟩
#align category_theory.limits.types.binary_coproduct_colimit_cocone CategoryTheory.Limits.Types.binaryCoproductColimitCocone

/-- The categorical binary coproduct in `Type u` is the sum `X ⊕ Y`. -/
noncomputable def binaryCoproductIso (X Y : Type u) : Limits.coprod X Y ≅ Sum X Y :=
  colimit.isoColimitCocone (binaryCoproductColimitCocone X Y)
#align category_theory.limits.types.binary_coproduct_iso CategoryTheory.Limits.Types.binaryCoproductIso

--open CategoryTheory.Type

@[elementwise (attr := simp)]
theorem binaryCoproductIso_inl_comp_hom (X Y : Type u) :
    Limits.coprod.inl ≫ (binaryCoproductIso X Y).hom = Sum.inl :=
  colimit.isoColimitCocone_ι_hom (binaryCoproductColimitCocone X Y) ⟨WalkingPair.left⟩
#align category_theory.limits.types.binary_coproduct_iso_inl_comp_hom CategoryTheory.Limits.Types.binaryCoproductIso_inl_comp_hom

@[elementwise (attr := simp)]
theorem binaryCoproductIso_inr_comp_hom (X Y : Type u) :
    Limits.coprod.inr ≫ (binaryCoproductIso X Y).hom = Sum.inr :=
  colimit.isoColimitCocone_ι_hom (binaryCoproductColimitCocone X Y) ⟨WalkingPair.right⟩
#align category_theory.limits.types.binary_coproduct_iso_inr_comp_hom CategoryTheory.Limits.Types.binaryCoproductIso_inr_comp_hom

@[elementwise (attr := simp)]
theorem binaryCoproductIso_inl_comp_inv (X Y : Type u) :
    ↾(Sum.inl : X ⟶ Sum X Y) ≫ (binaryCoproductIso X Y).inv = Limits.coprod.inl :=
  colimit.isoColimitCocone_ι_inv (binaryCoproductColimitCocone X Y) ⟨WalkingPair.left⟩
#align category_theory.limits.types.binary_coproduct_iso_inl_comp_inv CategoryTheory.Limits.Types.binaryCoproductIso_inl_comp_inv

@[elementwise (attr := simp)]
theorem binaryCoproductIso_inr_comp_inv (X Y : Type u) :
    ↾(Sum.inr : Y ⟶ Sum X Y) ≫ (binaryCoproductIso X Y).inv = Limits.coprod.inr :=
  colimit.isoColimitCocone_ι_inv (binaryCoproductColimitCocone X Y) ⟨WalkingPair.right⟩
#align category_theory.limits.types.binary_coproduct_iso_inr_comp_inv CategoryTheory.Limits.Types.binaryCoproductIso_inr_comp_inv

open Function (Injective)

theorem binaryCofan_isColimit_iff {X Y : Type u} (c : BinaryCofan X Y) :
    Nonempty (IsColimit c) ↔
      Injective c.inl ∧ Injective c.inr ∧ IsCompl (Set.range c.inl) (Set.range c.inr) := by
  classical
    constructor
    · rintro ⟨h⟩
      rw [← show _ = c.inl from
          h.comp_coconePointUniqueUpToIso_inv (binaryCoproductColimit X Y) ⟨WalkingPair.left⟩,
        ← show _ = c.inr from
          h.comp_coconePointUniqueUpToIso_inv (binaryCoproductColimit X Y) ⟨WalkingPair.right⟩]
      dsimp [binaryCoproductCocone]
      refine'
        ⟨(h.coconePointUniqueUpToIso (binaryCoproductColimit X Y)).symm.toEquiv.injective.comp
            Sum.inl_injective,
          (h.coconePointUniqueUpToIso (binaryCoproductColimit X Y)).symm.toEquiv.injective.comp
            Sum.inr_injective, _⟩
      erw [Set.range_comp, ← eq_compl_iff_isCompl, Set.range_comp _ Sum.inr, ←
        Set.image_compl_eq
          (h.coconePointUniqueUpToIso (binaryCoproductColimit X Y)).symm.toEquiv.bijective]
      simp
    · rintro ⟨h₁, h₂, h₃⟩
      have : ∀ x, x ∈ Set.range c.inl ∨ x ∈ Set.range c.inr := by
        rw [eq_compl_iff_isCompl.mpr h₃.symm]
        exact fun _ => or_not
      refine' ⟨BinaryCofan.IsColimit.mk _ _ _ _ _⟩
      · intro T f g x
        exact
          if h : x ∈ Set.range c.inl then f ((Equiv.ofInjective _ h₁).symm ⟨x, h⟩)
          else g ((Equiv.ofInjective _ h₂).symm ⟨x, (this x).resolve_left h⟩)
      · intro T f g
        funext x
        dsimp
        simp [h₁.eq_iff]
      · intro T f g
        funext x
        dsimp
        simp only [Set.mem_range, Equiv.ofInjective_symm_apply,
          dite_eq_right_iff, forall_exists_index]
        intro y e
        have : c.inr x ∈ Set.range c.inl ⊓ Set.range c.inr := ⟨⟨_, e⟩, ⟨_, rfl⟩⟩
        rw [disjoint_iff.mp h₃.1] at this
        exact this.elim
      · rintro T _ _ m rfl rfl
        funext x
        dsimp
        split_ifs <;> exact congr_arg _ (Equiv.apply_ofInjective_symm _ ⟨_, _⟩).symm
#align category_theory.limits.types.binary_cofan_is_colimit_iff CategoryTheory.Limits.Types.binaryCofan_isColimit_iff

/-- Any monomorphism in `Type` is a coproduct injection. -/
noncomputable def isCoprodOfMono {X Y : Type u} (f : X ⟶ Y) [Mono f] :
    IsColimit (BinaryCofan.mk f (Subtype.val : ↑(Set.range f)ᶜ → Y)) := by
  apply Nonempty.some
  rw [binaryCofan_isColimit_iff]
  refine' ⟨(mono_iff_injective f).mp inferInstance, Subtype.val_injective, _⟩
  symm
  rw [← eq_compl_iff_isCompl]
  exact Subtype.range_val
#align category_theory.limits.types.is_coprod_of_mono CategoryTheory.Limits.Types.isCoprodOfMono

/-- The category of types has `Π j, f j` as the product of a type family `f : J → Type`.
-/
def productLimitCone {J : Type v} (F : J → TypeMax.{v, u}) :
    Limits.LimitCone (Discrete.functor F) where
  cone :=
    { pt := ∀ j, F j
      π := Discrete.natTrans (fun ⟨j⟩ f => f j) }
  isLimit :=
    { lift := fun s x j => s.π.app ⟨j⟩ x
      uniq := fun s m w => funext fun x => funext fun j => (congr_fun (w ⟨j⟩) x : _) }
#align category_theory.limits.types.product_limit_cone CategoryTheory.Limits.Types.productLimitCone

/-- The categorical product in `Type u` is the type theoretic product `Π j, F j`. -/
noncomputable def productIso {J : Type v} (F : J → TypeMax.{v, u}) : ∏ F ≅ ∀ j, F j :=
  limit.isoLimitCone (productLimitCone.{v, u} F)
#align category_theory.limits.types.product_iso CategoryTheory.Limits.Types.productIso

-- porting note: was `@[elementwise (attr := simp)]`, but it produces a trivial lemma.
@[simp]
theorem productIso_hom_comp_eval {J : Type v} (F : J → TypeMax.{v, u}) (j : J) :
    ((productIso.{v, u} F).hom ≫ fun f => f j) = Pi.π F j :=
  rfl
#align category_theory.limits.types.product_iso_hom_comp_eval CategoryTheory.Limits.Types.productIso_hom_comp_eval

@[elementwise (attr := simp)]
theorem productIso_inv_comp_π {J : Type v} (F : J → TypeMax.{v, u}) (j : J) :
    (productIso.{v, u} F).inv ≫ Pi.π F j = fun f => f j :=
  limit.isoLimitCone_inv_π (productLimitCone.{v, u} F) ⟨j⟩
#align category_theory.limits.types.product_iso_inv_comp_π CategoryTheory.Limits.Types.productIso_inv_comp_π

/-- The category of types has `Σ j, f j` as the coproduct of a type family `f : J → Type`.
-/
def coproductColimitCocone {J : Type u} (F : J → Type u) :
    Limits.ColimitCocone (Discrete.functor F) where
  cocone :=
    { pt := Σj, F j
      ι := Discrete.natTrans (fun ⟨j⟩ x => ⟨j, x⟩)}
  isColimit :=
    { desc := fun s x => s.ι.app ⟨x.1⟩ x.2
      uniq := fun s m w => by
        funext ⟨j, x⟩
        exact congr_fun (w ⟨j⟩) x }
#align category_theory.limits.types.coproduct_colimit_cocone CategoryTheory.Limits.Types.coproductColimitCocone

/-- The categorical coproduct in `Type u` is the type theoretic coproduct `Σ j, F j`. -/
noncomputable def coproductIso {J : Type u} (F : J → Type u) : ∐ F ≅ Σj, F j :=
  colimit.isoColimitCocone (coproductColimitCocone F)
#align category_theory.limits.types.coproduct_iso CategoryTheory.Limits.Types.coproductIso

@[elementwise (attr := simp)]
theorem coproductIso_ι_comp_hom {J : Type u} (F : J → Type u) (j : J) :
    Sigma.ι F j ≫ (coproductIso F).hom = fun x : F j => (⟨j, x⟩ : Σj, F j) :=
  colimit.isoColimitCocone_ι_hom (coproductColimitCocone F) ⟨j⟩
#align category_theory.limits.types.coproduct_iso_ι_comp_hom CategoryTheory.Limits.Types.coproductIso_ι_comp_hom

-- porting note: was @[elementwise (attr := simp)], but it produces a trivial lemma
-- removed simp attribute because it seems it never applies
theorem coproductIso_mk_comp_inv {J : Type u} (F : J → Type u) (j : J) :
    (↾fun x : F j => (⟨j, x⟩ : Σj, F j)) ≫ (coproductIso F).inv = Sigma.ι F j :=
  rfl
#align category_theory.limits.types.coproduct_iso_mk_comp_inv CategoryTheory.Limits.Types.coproductIso_mk_comp_inv

section Fork

variable {X Y Z : Type u} (f : X ⟶ Y) {g h : Y ⟶ Z} (w : f ≫ g = f ≫ h)

/--
Show the given fork in `Type u` is an equalizer given that any element in the "difference kernel"
comes from `X`.
The converse of `unique_of_type_equalizer`.
-/
noncomputable def typeEqualizerOfUnique (t : ∀ y : Y, g y = h y → ∃! x : X, f x = y) :
    IsLimit (Fork.ofι _ w) :=
  Fork.IsLimit.mk' _ fun s => by
    refine' ⟨fun i => _, _, _⟩
    · apply Classical.choose (t (s.ι i) _)
      apply congr_fun s.condition i
    · funext i
      exact (Classical.choose_spec (t (s.ι i) (congr_fun s.condition i))).1
    · intro m hm
      funext i
      exact (Classical.choose_spec (t (s.ι i) (congr_fun s.condition i))).2 _ (congr_fun hm i)
#align category_theory.limits.types.type_equalizer_of_unique CategoryTheory.Limits.Types.typeEqualizerOfUnique

/-- The converse of `type_equalizer_of_unique`. -/
theorem unique_of_type_equalizer (t : IsLimit (Fork.ofι _ w)) (y : Y) (hy : g y = h y) :
    ∃! x : X, f x = y := by
  let y' : PUnit ⟶ Y := fun _ => y
  have hy' : y' ≫ g = y' ≫ h := funext fun _ => hy
  refine' ⟨(Fork.IsLimit.lift' t _ hy').1 ⟨⟩, congr_fun (Fork.IsLimit.lift' t y' _).2 ⟨⟩, _⟩
  intro x' hx'
  suffices : (fun _ : PUnit => x') = (Fork.IsLimit.lift' t y' hy').1
  rw [← this]
  apply Fork.IsLimit.hom_ext t
  funext ⟨⟩
  apply hx'.trans (congr_fun (Fork.IsLimit.lift' t _ hy').2 ⟨⟩).symm
#align category_theory.limits.types.unique_of_type_equalizer CategoryTheory.Limits.Types.unique_of_type_equalizer

theorem type_equalizer_iff_unique :
    Nonempty (IsLimit (Fork.ofι _ w)) ↔ ∀ y : Y, g y = h y → ∃! x : X, f x = y :=
  ⟨fun i => unique_of_type_equalizer _ _ (Classical.choice i), fun k =>
    ⟨typeEqualizerOfUnique f w k⟩⟩
#align category_theory.limits.types.type_equalizer_iff_unique CategoryTheory.Limits.Types.type_equalizer_iff_unique

/-- Show that the subtype `{x : Y // g x = h x}` is an equalizer for the pair `(g,h)`. -/
def equalizerLimit : Limits.LimitCone (parallelPair g h) where
  cone := Fork.ofι (Subtype.val : { x : Y // g x = h x } → Y) (funext Subtype.prop)
  isLimit :=
    Fork.IsLimit.mk' _ fun s =>
      ⟨fun i => ⟨s.ι i, by apply congr_fun s.condition i⟩, rfl, fun hm =>
        funext fun x => Subtype.ext (congr_fun hm x)⟩
#align category_theory.limits.types.equalizer_limit CategoryTheory.Limits.Types.equalizerLimit

variable (g h)

/-- The categorical equalizer in `Type u` is `{x : Y // g x = h x}`. -/
noncomputable def equalizerIso : equalizer g h ≅ { x : Y // g x = h x } :=
  limit.isoLimitCone equalizerLimit
#align category_theory.limits.types.equalizer_iso CategoryTheory.Limits.Types.equalizerIso

-- porting note: was @[elementwise], but it produces a trivial lemma
@[simp]
theorem equalizerIso_hom_comp_subtype : (equalizerIso g h).hom ≫ Subtype.val = equalizer.ι g h := by
  rfl
#align category_theory.limits.types.equalizer_iso_hom_comp_subtype CategoryTheory.Limits.Types.equalizerIso_hom_comp_subtype

@[elementwise (attr := simp)]
theorem equalizerIso_inv_comp_ι : (equalizerIso g h).inv ≫ equalizer.ι g h = Subtype.val :=
  limit.isoLimitCone_inv_π equalizerLimit WalkingParallelPair.zero
#align category_theory.limits.types.equalizer_iso_inv_comp_ι CategoryTheory.Limits.Types.equalizerIso_inv_comp_ι

end Fork

section Cofork

variable {X Y Z : Type u} (f g : X ⟶ Y)

/-- (Implementation) The relation to be quotiented to obtain the coequalizer. -/
inductive CoequalizerRel : Y → Y → Prop
  | Rel (x : X) : CoequalizerRel (f x) (g x)
#align category_theory.limits.types.coequalizer_rel CategoryTheory.Limits.Types.CoequalizerRel

/-- Show that the quotient by the relation generated by `f(x) ~ g(x)`
is a coequalizer for the pair `(f, g)`.
-/
def coequalizerColimit : Limits.ColimitCocone (parallelPair f g) where
  cocone :=
    Cofork.ofπ (Quot.mk (CoequalizerRel f g)) (funext fun x => Quot.sound (CoequalizerRel.Rel x))
  isColimit :=
    Cofork.IsColimit.mk _
      (fun s => Quot.lift s.π
        (fun a b (h : CoequalizerRel f g a b) => by
          cases h
          apply congr_fun s.condition))
      (fun s => rfl)
      (fun s m hm => funext (fun x => Quot.inductionOn x (congr_fun hm)))
#align category_theory.limits.types.coequalizer_colimit CategoryTheory.Limits.Types.coequalizerColimit

/-- If `π : Y ⟶ Z` is an equalizer for `(f, g)`, and `U ⊆ Y` such that `f ⁻¹' U = g ⁻¹' U`,
then `π ⁻¹' (π '' U) = U`.
-/
theorem coequalizer_preimage_image_eq_of_preimage_eq (π : Y ⟶ Z) (e : f ≫ π = g ≫ π)
    (h : IsColimit (Cofork.ofπ π e)) (U : Set Y) (H : f ⁻¹' U = g ⁻¹' U) : π ⁻¹' (π '' U) = U := by
  have lem : ∀ x y, CoequalizerRel f g x y → (x ∈ U ↔ y ∈ U) := by
    rintro _ _ ⟨x⟩
    change x ∈ f ⁻¹' U ↔ x ∈ g ⁻¹' U
    rw [H]
  -- porting note: tidy was able to fill the structure automatically
  have eqv : _root_.Equivalence fun x y => x ∈ U ↔ y ∈ U :=
    { refl := by tauto
      symm := by tauto
      trans := by tauto }
  ext
  constructor
  · rw [←
      show _ = π from
        h.comp_coconePointUniqueUpToIso_inv (coequalizerColimit f g).2
          WalkingParallelPair.one]
    rintro ⟨y, hy, e'⟩
    dsimp at e'
    replace e' :=
      (mono_iff_injective
            (h.coconePointUniqueUpToIso (coequalizerColimit f g).isColimit).inv).mp
        inferInstance e'
    exact (eqv.eqvGen_iff.mp (EqvGen.mono lem (Quot.exact _ e'))).mp hy
  · exact fun hx => ⟨_, hx, rfl⟩
#align category_theory.limits.types.coequalizer_preimage_image_eq_of_preimage_eq CategoryTheory.Limits.Types.coequalizer_preimage_image_eq_of_preimage_eq

/-- The categorical coequalizer in `Type u` is the quotient by `f g ~ g x`. -/
noncomputable def coequalizerIso : coequalizer f g ≅ _root_.Quot (CoequalizerRel f g) :=
  colimit.isoColimitCocone (coequalizerColimit f g)
#align category_theory.limits.types.coequalizer_iso CategoryTheory.Limits.Types.coequalizerIso

@[elementwise (attr := simp)]
theorem coequalizerIso_π_comp_hom :
    coequalizer.π f g ≫ (coequalizerIso f g).hom = Quot.mk (CoequalizerRel f g) :=
  colimit.isoColimitCocone_ι_hom (coequalizerColimit f g) WalkingParallelPair.one
#align category_theory.limits.types.coequalizer_iso_π_comp_hom CategoryTheory.Limits.Types.coequalizerIso_π_comp_hom

-- porting note: was @[elementwise], but it produces a trivial lemma
@[simp]
theorem coequalizerIso_quot_comp_inv :
    ↾Quot.mk (CoequalizerRel f g) ≫ (coequalizerIso f g).inv = coequalizer.π f g :=
  rfl
#align category_theory.limits.types.coequalizer_iso_quot_comp_inv CategoryTheory.Limits.Types.coequalizerIso_quot_comp_inv

end Cofork

section Pullback

open CategoryTheory.Limits.WalkingPair

open CategoryTheory.Limits.WalkingCospan

open CategoryTheory.Limits.WalkingCospan.Hom

variable {W X Y Z : Type u}

variable (f : X ⟶ Z) (g : Y ⟶ Z)

-- porting note: removed @[nolint has_nonempty_instance]
/-- The usual explicit pullback in the category of types, as a subtype of the product.
The full `LimitCone` data is bundled as `pullbackLimitCone f g`.
-/
abbrev PullbackObj : Type u :=
  { p : X × Y // f p.1 = g p.2 }
#align category_theory.limits.types.pullback_obj CategoryTheory.Limits.Types.PullbackObj

-- `PullbackObj f g` comes with a coercion to the product type `X × Y`.
example (p : PullbackObj f g) : X × Y :=
  p

/-- The explicit pullback cone on `PullbackObj f g`.
This is bundled with the `IsLimit` data as `pullbackLimitCone f g`.
-/
abbrev pullbackCone : Limits.PullbackCone f g :=
  PullbackCone.mk (fun p : PullbackObj f g => p.1.1) (fun p => p.1.2) (funext fun p => p.2)
#align category_theory.limits.types.pullback_cone CategoryTheory.Limits.Types.pullbackCone

/-- The explicit pullback in the category of types, bundled up as a `LimitCone`
for given `f` and `g`.
-/
@[simps]
def pullbackLimitCone (f : X ⟶ Z) (g : Y ⟶ Z) : Limits.LimitCone (cospan f g) where
  cone := pullbackCone f g
  isLimit :=
    PullbackCone.isLimitAux _ (fun s x => ⟨⟨s.fst x, s.snd x⟩, congr_fun s.condition x⟩)
      (by aesop) (by aesop) fun s m w =>
      funext fun x =>
        Subtype.ext <|
          Prod.ext (congr_fun (w WalkingCospan.left) x) (congr_fun (w WalkingCospan.right) x)
#align category_theory.limits.types.pullback_limit_cone CategoryTheory.Limits.Types.pullbackLimitCone

/-- The pullback cone given by the instance `HasPullbacks (Type u)` is isomorphic to the
explicit pullback cone given by `pullbackLimitCone`.
-/
noncomputable def pullbackConeIsoPullback : limit.cone (cospan f g) ≅ pullbackCone f g :=
  (limit.isLimit _).uniqueUpToIso (pullbackLimitCone f g).isLimit
#align category_theory.limits.types.pullback_cone_iso_pullback CategoryTheory.Limits.Types.pullbackConeIsoPullback

/-- The pullback given by the instance `HasPullbacks (Type u)` is isomorphic to the
explicit pullback object given by `PullbackObj`.
-/
noncomputable def pullbackIsoPullback : pullback f g ≅ PullbackObj f g :=
  (Cones.forget _).mapIso <| pullbackConeIsoPullback f g
#align category_theory.limits.types.pullback_iso_pullback CategoryTheory.Limits.Types.pullbackIsoPullback

@[simp]
theorem pullbackIsoPullback_hom_fst (p : pullback f g) :
    ((pullbackIsoPullback f g).hom p : X × Y).fst = (pullback.fst : _ ⟶ X) p :=
  congr_fun ((pullbackConeIsoPullback f g).hom.w left) p
#align category_theory.limits.types.pullback_iso_pullback_hom_fst CategoryTheory.Limits.Types.pullbackIsoPullback_hom_fst

@[simp]
theorem pullbackIsoPullback_hom_snd (p : pullback f g) :
    ((pullbackIsoPullback f g).hom p : X × Y).snd = (pullback.snd : _ ⟶ Y) p :=
  congr_fun ((pullbackConeIsoPullback f g).hom.w right) p
#align category_theory.limits.types.pullback_iso_pullback_hom_snd CategoryTheory.Limits.Types.pullbackIsoPullback_hom_snd

@[simp]
theorem pullbackIsoPullback_inv_fst :
    (pullbackIsoPullback f g).inv ≫ pullback.fst = fun p => (p.1 : X × Y).fst :=
  (pullbackConeIsoPullback f g).inv.w left
#align category_theory.limits.types.pullback_iso_pullback_inv_fst CategoryTheory.Limits.Types.pullbackIsoPullback_inv_fst

@[simp]
theorem pullbackIsoPullback_inv_snd :
    (pullbackIsoPullback f g).inv ≫ pullback.snd = fun p => (p.1 : X × Y).snd :=
  (pullbackConeIsoPullback f g).inv.w right
#align category_theory.limits.types.pullback_iso_pullback_inv_snd CategoryTheory.Limits.Types.pullbackIsoPullback_inv_snd

end Pullback

end CategoryTheory.Limits.Types
