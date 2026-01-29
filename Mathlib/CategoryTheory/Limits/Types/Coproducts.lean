/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.Tactic.CategoryTheory.Elementwise

/-!
# Coproducts in `Type`

If `F : J → Type max v u` (with `J : Type v`), we show that the coproduct
of `F` exists in `Type max v u` and identifies to the sigma type `Σ j, F j`.
Similarly, the binary coproduct of two types `X` and `Y` identifies to
`X ⊕ Y`, and the initial object of `Type u` if `PEmpty`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

namespace Limits

variable {C : Type u} (F : C → Type v)

/-- Given a functor `F : Discrete C ⥤ Type v`, this is a "cofan" for `F`,
but we allow the point to be in `Type w` for an arbitrary universe `w`. -/
abbrev CofanTypes := Functor.CoconeTypes.{w} (Discrete.functor F)

variable {F}

namespace CofanTypes

/-- The injection map for a cofan of a functor to types. -/
abbrev inj (c : CofanTypes.{w} F) (i : C) : F i → c.pt := c.ι ⟨i⟩

variable (F) in
/-- The cofan given by a sigma type. -/
@[simps]
def sigma : CofanTypes F where
  pt := Σ (i : C), F i
  ι := fun ⟨i⟩ x ↦ ⟨i, x⟩
  ι_naturality := by
    rintro ⟨i⟩ ⟨j⟩ f
    obtain rfl : i = j := by simpa using Discrete.eq_of_hom f
    rfl

@[simp]
lemma sigma_inj (i : C) (x : F i) :
    (sigma F).inj i x = ⟨i, x⟩ := rfl

lemma isColimit_mk (c : CofanTypes.{w} F)
    (h₁ : ∀ (x : c.pt), ∃ (i : C) (y : F i), c.inj i y = x)
    (h₂ : ∀ (i : C), Function.Injective (c.inj i))
    (h₃ : ∀ (i j : C) (x : F i) (y : F j), c.inj i x = c.inj j y → i = j) :
    Functor.CoconeTypes.IsColimit c where
  bijective := by
    constructor
    · intro x y h
      obtain ⟨⟨i⟩, x, rfl⟩ := (Discrete.functor F).ιColimitType_jointly_surjective x
      obtain ⟨⟨j⟩, y, rfl⟩ := (Discrete.functor F).ιColimitType_jointly_surjective y
      obtain rfl := h₃ _ _ _ _ h
      obtain rfl := h₂ _ h
      rfl
    · intro x
      obtain ⟨i, y, rfl⟩ := h₁ x
      exact ⟨(Discrete.functor F).ιColimitType ⟨i⟩ y, rfl⟩

variable (F) in
lemma isColimit_sigma : Functor.CoconeTypes.IsColimit (sigma F) :=
  isColimit_mk _ (by aesop)
    (fun _ _ _ h ↦ by rw [Sigma.ext_iff] at h; simpa using h)
    (fun _ _ _ _ h ↦ congr_arg Sigma.fst h)

variable (F) in
/-- Given a cofan of a functor to types, this is a canonical map
from the Sigma type to the point of the cofan. -/
@[simp]
def fromSigma (c : CofanTypes.{w} F) (x : Σ (i : C), F i) : c.pt :=
  c.inj x.1 x.2

lemma isColimit_iff_bijective_fromSigma (c : CofanTypes.{w} F) :
    c.IsColimit ↔ Function.Bijective c.fromSigma := by
  rw [(isColimit_sigma F).iff_bijective]
  aesop

section

variable {c : CofanTypes.{w} F} (hc : Functor.CoconeTypes.IsColimit c)

include hc

lemma bijective_fromSigma_of_isColimit :
    Function.Bijective c.fromSigma := by
  rwa [← isColimit_iff_bijective_fromSigma]

/-- The bijection from the sigma type to the point of a colimit cofan
of a functor to types. -/
noncomputable def equivOfIsColimit :
    (Σ (i : C), F i) ≃ c.pt :=
  Equiv.ofBijective _ (bijective_fromSigma_of_isColimit hc)

@[simp]
lemma equivOfIsColimit_apply (i : C) (x : F i) :
    equivOfIsColimit hc ⟨i, x⟩ = c.inj i x := rfl

@[simp]
lemma equivOfIsColimit_symm_apply (i : C) (x : F i) :
    (equivOfIsColimit hc).symm (c.inj i x) = ⟨i, x⟩ :=
  (equivOfIsColimit hc).injective (by simp)

lemma inj_jointly_surjective_of_isColimit (x : c.pt) :
    ∃ (i : C) (y : F i), c.inj i y = x := by
  obtain ⟨⟨i⟩, y, rfl⟩ := hc.ι_jointly_surjective x
  exact ⟨i, y, rfl⟩

lemma inj_injective_of_isColimit (i : C) :
    Function.Injective (c.inj i) := by
  intro y₁ y₂ h
  simpa using (equivOfIsColimit hc).injective (a₁ := ⟨i, y₁⟩) (a₂ := ⟨i, y₂⟩) h

lemma eq_of_inj_apply_eq_of_isColimit
    {i₁ i₂ : C} (y₁ : F i₁) (y₂ : F i₂) (h : c.inj i₁ y₁ = c.inj i₂ y₂) :
    i₁ = i₂ :=
  congr_arg Sigma.fst ((equivOfIsColimit hc).injective (a₁ := ⟨i₁, y₁⟩) (a₂ := ⟨i₂, y₂⟩) h)

end

end CofanTypes

namespace Cofan

variable {C : Type u} {F : C → Type v} (c : Cofan F)

/-- If `F : C → Type v`, then the data of a "type-theoretic" cofan of `F`
with a point in `Type v` is the same as the data of a cocone (in a categorical sense). -/
@[simps]
def cofanTypes :
    CofanTypes.{v} F where
  pt := c.pt
  ι := fun ⟨j⟩ ↦ c.inj j
  ι_naturality := by
    rintro ⟨i⟩ ⟨j⟩ f
    obtain rfl : i = j := by simpa using Discrete.eq_of_hom f
    rfl

lemma isColimit_cofanTypes_iff :
    c.cofanTypes.IsColimit ↔ Nonempty (IsColimit c) :=
  Functor.CoconeTypes.isColimit_iff _

lemma nonempty_isColimit_iff_bijective_fromSigma :
    Nonempty (IsColimit c) ↔ Function.Bijective c.cofanTypes.fromSigma := by
  rw [← isColimit_cofanTypes_iff, CofanTypes.isColimit_iff_bijective_fromSigma]

variable {c}

lemma inj_jointly_surjective_of_isColimit (hc : IsColimit c) (x : c.pt) :
    ∃ (i : C) (y : F i), c.inj i y = x :=
  CofanTypes.inj_jointly_surjective_of_isColimit
    ((isColimit_cofanTypes_iff c).2 ⟨hc⟩) x

lemma inj_injective_of_isColimit (hc : IsColimit c) (i : C) :
    Function.Injective (c.inj i) :=
  CofanTypes.inj_injective_of_isColimit ((isColimit_cofanTypes_iff c).2 ⟨hc⟩) i

lemma eq_of_inj_apply_eq_of_isColimit (hc : IsColimit c)
    {i₁ i₂ : C} (y₁ : F i₁) (y₂ : F i₂) (h : c.inj i₁ y₁ = c.inj i₂ y₂) :
    i₁ = i₂ :=
  CofanTypes.eq_of_inj_apply_eq_of_isColimit ((isColimit_cofanTypes_iff c).2 ⟨hc⟩) _ _ h

end Cofan

namespace Types

/-- The category of types has `PEmpty` as an initial object. -/
def initialColimitCocone : Limits.ColimitCocone (Functor.empty (Type u)) where
  -- Porting note: tidy was able to fill the structure automatically
  cocone :=
    { pt := PEmpty
      ι := (Functor.uniqueFromEmpty _).inv }
  isColimit :=
    { desc := fun _ => by rintro ⟨⟩
      fac := fun _ => by rintro ⟨⟨⟩⟩
      uniq := fun _ _ _ => by funext x; cases x }

/-- The initial object in `Type u` is `PEmpty`. -/
noncomputable def initialIso : ⊥_ Type u ≅ PEmpty :=
  colimit.isoColimitCocone initialColimitCocone.{u, 0}

/-- The initial object in `Type u` is `PEmpty`. -/
noncomputable def isInitialPunit : IsInitial (PEmpty : Type u) :=
  initialIsInitial.ofIso initialIso

/-- An object in `Type u` is initial if and only if it is empty. -/
lemma initial_iff_empty (X : Type u) : Nonempty (IsInitial X) ↔ IsEmpty X := by
  constructor
  · intro ⟨h⟩
    exact Function.isEmpty (IsInitial.to h PEmpty)
  · intro h
    exact ⟨IsInitial.ofIso Types.isInitialPunit <| Equiv.toIso <| Equiv.equivOfIsEmpty PEmpty X⟩


/-- The sum type `X ⊕ Y` forms a cocone for the binary coproduct of `X` and `Y`. -/
@[simps!]
def binaryCoproductCocone (X Y : Type u) : Cocone (pair X Y) :=
  BinaryCofan.mk Sum.inl Sum.inr

open CategoryTheory.Limits.WalkingPair

/-- The sum type `X ⊕ Y` is a binary coproduct for `X` and `Y`. -/
@[simps]
def binaryCoproductColimit (X Y : Type u) : IsColimit (binaryCoproductCocone X Y) where
  desc := fun s : BinaryCofan X Y => Sum.elim s.inl s.inr
  fac _ j := Discrete.recOn j fun j => WalkingPair.casesOn j rfl rfl
  uniq _ _ w := funext fun x => Sum.casesOn x (congr_fun (w ⟨left⟩)) (congr_fun (w ⟨right⟩))

/-- The category of types has `X ⊕ Y`,
as the binary coproduct of `X` and `Y`.
-/
def binaryCoproductColimitCocone (X Y : Type u) : Limits.ColimitCocone (pair X Y) :=
  ⟨_, binaryCoproductColimit X Y⟩

/-- The categorical binary coproduct in `Type u` is the sum `X ⊕ Y`. -/
noncomputable def binaryCoproductIso (X Y : Type u) : Limits.coprod X Y ≅ X ⊕ Y :=
  colimit.isoColimitCocone (binaryCoproductColimitCocone X Y)

--open CategoryTheory.Type

@[elementwise (attr := simp)]
theorem binaryCoproductIso_inl_comp_hom (X Y : Type u) :
    Limits.coprod.inl ≫ (binaryCoproductIso X Y).hom = Sum.inl :=
  colimit.isoColimitCocone_ι_hom (binaryCoproductColimitCocone X Y) ⟨WalkingPair.left⟩

@[elementwise (attr := simp)]
theorem binaryCoproductIso_inr_comp_hom (X Y : Type u) :
    Limits.coprod.inr ≫ (binaryCoproductIso X Y).hom = Sum.inr :=
  colimit.isoColimitCocone_ι_hom (binaryCoproductColimitCocone X Y) ⟨WalkingPair.right⟩

@[elementwise (attr := simp)]
theorem binaryCoproductIso_inl_comp_inv (X Y : Type u) :
    ↾(Sum.inl : X ⟶ X ⊕ Y) ≫ (binaryCoproductIso X Y).inv = Limits.coprod.inl :=
  colimit.isoColimitCocone_ι_inv (binaryCoproductColimitCocone X Y) ⟨WalkingPair.left⟩

@[elementwise (attr := simp)]
theorem binaryCoproductIso_inr_comp_inv (X Y : Type u) :
    ↾(Sum.inr : Y ⟶ X ⊕ Y) ≫ (binaryCoproductIso X Y).inv = Limits.coprod.inr :=
  colimit.isoColimitCocone_ι_inv (binaryCoproductColimitCocone X Y) ⟨WalkingPair.right⟩

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
      refine
        ⟨(h.coconePointUniqueUpToIso (binaryCoproductColimit X Y)).symm.toEquiv.injective.comp
            Sum.inl_injective,
          (h.coconePointUniqueUpToIso (binaryCoproductColimit X Y)).symm.toEquiv.injective.comp
            Sum.inr_injective, ?_⟩
      rw [types_comp, Set.range_comp, ← eq_compl_iff_isCompl, types_comp, Set.range_comp _ Sum.inr]
      erw [← Set.image_compl_eq
          (h.coconePointUniqueUpToIso (binaryCoproductColimit X Y)).symm.toEquiv.bijective]
      simp
    · rintro ⟨h₁, h₂, h₃⟩
      have : ∀ x, x ∈ Set.range c.inl ∨ x ∈ Set.range c.inr := by
        rw [eq_compl_iff_isCompl.mpr h₃.symm]
        exact fun _ => or_not
      refine ⟨BinaryCofan.IsColimit.mk _ ?_ ?_ ?_ ?_⟩
      · intro T f g x
        exact
          if h : x ∈ Set.range c.inl then f ((Equiv.ofInjective _ h₁).symm ⟨x, h⟩)
          else g ((Equiv.ofInjective _ h₂).symm ⟨x, (this x).resolve_left h⟩)
      · intro T f g
        funext x
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

/-- Any monomorphism in `Type` is a coproduct injection. -/
noncomputable def isCoprodOfMono {X Y : Type u} (f : X ⟶ Y) [Mono f] :
    IsColimit (BinaryCofan.mk f (Subtype.val : ↑(Set.range f)ᶜ → Y)) := by
  apply Nonempty.some
  rw [binaryCofan_isColimit_iff]
  refine ⟨(mono_iff_injective f).mp inferInstance, Subtype.val_injective, ?_⟩
  symm
  rw [← eq_compl_iff_isCompl]
  exact Subtype.range_val

/-- The category of types has `Σ j, f j` as the coproduct of a type family `f : J → Type`.
-/
def coproductColimitCocone {J : Type v} (F : J → Type max v u) :
    Limits.ColimitCocone (Discrete.functor F) where
  cocone :=
    { pt := Σ j, F j
      ι := Discrete.natTrans (fun ⟨j⟩ x => ⟨j, x⟩) }
  isColimit :=
    { desc := fun s x => s.ι.app ⟨x.1⟩ x.2
      uniq := fun s m w => by
        funext ⟨j, x⟩
        exact congr_fun (w ⟨j⟩) x }

/-- The categorical coproduct in `Type u` is the type-theoretic coproduct `Σ j, F j`. -/
noncomputable def coproductIso {J : Type v} (F : J → Type max v u) : ∐ F ≅ Σ j, F j :=
  colimit.isoColimitCocone (coproductColimitCocone F)

@[elementwise (attr := simp)]
theorem coproductIso_ι_comp_hom {J : Type v} (F : J → Type max v u) (j : J) :
    Sigma.ι F j ≫ (coproductIso F).hom = fun x : F j => (⟨j, x⟩ : Σ j, F j) :=
  colimit.isoColimitCocone_ι_hom (coproductColimitCocone F) ⟨j⟩

@[elementwise (attr := simp)]
theorem coproductIso_mk_comp_inv {J : Type v} (F : J → Type max v u) (j : J) :
    (↾fun x : F j => (⟨j, x⟩ : Σ j, F j)) ≫ (coproductIso F).inv = Sigma.ι F j :=
  rfl

end CategoryTheory.Limits.Types
