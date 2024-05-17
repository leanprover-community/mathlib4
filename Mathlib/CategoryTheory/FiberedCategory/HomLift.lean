/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/

import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.CommSq

/-!

# HomLift

Given a functor `p : 𝒳 ⥤ 𝒮`, this file provides API for expressing the fact that `p(φ) = f`
for given morphisms `φ` and `f`.

## Main definition

Given morphism `φ : a ⟶ b` in `𝒳` and `f : R ⟶ S` in `𝒮`, `IsHomLift p f φ` is defined as a
structure containing the data that `p(a) = R`, `p(b) = S` and the fact that the following square
commutes
```
  p(a) --p(φ)--> p(b)
  |               |
  |               |
  v               v
  R -----f------> S
```
where the vertical arrows are given by `eqToHom` corresponding to the equalities `p(a) = R` and
`p(b) = S`.

-/

universe u₁ v₁ u₂ v₂

open CategoryTheory Functor Category

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category 𝒳] [Category 𝒮]

/-- The proposition that an arrow a --φ--> b lifts an arrow R --f--> S in 𝒮 via p. This is
often drawn as:
```
  a --φ--> b
  -        -
  |        |
  v        v
  R --f--> S
``` -/
structure IsHomLift (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) : Prop where
  (ObjLiftDomain : p.obj a = R)
  (ObjLiftCodomain : p.obj b = S)
  (HomLift : CommSq (p.map φ) (eqToHom ObjLiftDomain) (eqToHom ObjLiftCodomain) f)

namespace IsHomLift

protected lemma hom_eq {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
    (hφ : IsHomLift p f φ) : f = eqToHom hφ.ObjLiftDomain.symm ≫ p.map φ ≫
      eqToHom hφ.ObjLiftCodomain :=
  ((eqToHom_comp_iff hφ.ObjLiftDomain _ _).1 hφ.HomLift.w.symm)

protected lemma hom_eq' {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
    (hφ : IsHomLift p f φ) : p.map φ = eqToHom hφ.ObjLiftDomain ≫ f ≫
      eqToHom hφ.ObjLiftCodomain.symm := by
  rw [← assoc, ← comp_eqToHom_iff hφ.ObjLiftCodomain _ _]
  exact hφ.HomLift.w

lemma eq_of_IsHomLift {p : 𝒳 ⥤ 𝒮} (a b : 𝒳) {f : p.obj a ⟶ p.obj b} {φ : a ⟶ b}
    (hφ : IsHomLift p f φ) : f = p.map φ := by
  simpa using IsHomLift.hom_eq hφ

/-- For any arrow `φ : a ⟶ b` in `𝒳`, `φ` lifts the arrow `p.map φ` in the base `𝒮`-/
@[simp]
protected lemma self (p : 𝒳 ⥤ 𝒮) {a b : 𝒳} (φ : a ⟶ b) : IsHomLift p (p.map φ) φ where
  ObjLiftDomain := rfl
  ObjLiftCodomain := rfl
  HomLift := ⟨by simp only [eqToHom_refl, comp_id, id_comp]⟩

@[simp]
protected lemma id {p : 𝒳 ⥤ 𝒮} {R : 𝒮} {a : 𝒳} (ha : p.obj a = R) : IsHomLift p (𝟙 R) (𝟙 a) :=
  ha ▸ (p.map_id _ ▸ IsHomLift.self p (𝟙 a))

protected lemma comp {p : 𝒳 ⥤ 𝒮} {R S T : 𝒮} {a b c : 𝒳} {f : R ⟶ S}
    {g : S ⟶ T} {φ : a ⟶ b} {ψ : b ⟶ c} (hφ : IsHomLift p f φ)
    (hψ : IsHomLift p g ψ) : IsHomLift p (f ≫ g) (φ ≫ ψ) where
  ObjLiftDomain := hφ.1
  ObjLiftCodomain := hψ.2
  HomLift := (p.map_comp _ _).symm ▸ CommSq.horiz_comp hφ.3 hψ.3

/-- If `φ : a ⟶ b` and `ψ : b ⟶ c` lift `𝟙 S`, then so does `φ ≫ ψ` -/
lemma lift_id_comp {p : 𝒳 ⥤ 𝒮} {R : 𝒮} {a b c : 𝒳} {φ : a ⟶ b} {ψ : b ⟶ c}
    (hφ : IsHomLift p (𝟙 R) φ) (hψ : IsHomLift p (𝟙 R) ψ) : IsHomLift p (𝟙 R) (φ ≫ ψ) :=
  comp_id (𝟙 R) ▸ IsHomLift.comp hφ hψ

/-- If `φ : a ⟶ b` lifts `f` and `ψ : b ⟶ c` lifts `𝟙 T`, then `φ  ≫ ψ` lifts `f` -/
lemma comp_lift_id {p : 𝒳 ⥤ 𝒮} {R S T : 𝒮} {a b c : 𝒳} {f : R ⟶ S}
    {φ : a ⟶ b} (hφ : IsHomLift p f φ) {ψ : b ⟶ c} (hψ : IsHomLift p (𝟙 T) ψ) :
    IsHomLift p f (φ ≫ ψ) where
  ObjLiftDomain := hφ.ObjLiftDomain
  ObjLiftCodomain := by rw [hψ.ObjLiftCodomain, ← hψ.ObjLiftDomain, hφ.ObjLiftCodomain]
  HomLift := ⟨by simp [IsHomLift.hom_eq' hψ, hφ.3.1]⟩

@[simp]
lemma eqToHom_domain_lift_id {p : 𝒳 ⥤ 𝒮} {a b : 𝒳} (hab : a = b) {R : 𝒮}
    (hR : p.obj a = R) : IsHomLift p (𝟙 R) (eqToHom hab) where
      ObjLiftDomain := hR
      ObjLiftCodomain := hab ▸ hR
      HomLift := ⟨by simp only [eqToHom_map, eqToHom_trans, comp_id]⟩

@[simp]
lemma eqToHom_codomain_lift_id {p : 𝒳 ⥤ 𝒮} {a b : 𝒳} (hab : a = b) {S : 𝒮}
    (hS : p.obj b = S) : IsHomLift p (𝟙 S) (eqToHom hab) where
      ObjLiftDomain := hab ▸ hS
      ObjLiftCodomain := hS
      HomLift := ⟨by simp only [eqToHom_map, eqToHom_trans, comp_id]⟩

@[simp]
lemma id_lift_eqToHom_domain {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} (hRS : R = S)
    {a : 𝒳} (ha : p.obj a = R) : IsHomLift p (eqToHom hRS) (𝟙 a) where
      ObjLiftDomain := ha
      ObjLiftCodomain := hRS ▸ ha
      HomLift := ⟨by simp only [map_id, id_comp, eqToHom_trans]⟩

@[simp]
lemma id_lift_eqToHom_codomain {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} (hRS : R = S)
    {b : 𝒳} (hb : p.obj b = S) : IsHomLift p (eqToHom hRS) (𝟙 b) where
      ObjLiftDomain := hRS ▸ hb
      ObjLiftCodomain := hb
      HomLift := ⟨by simp only [map_id, id_comp, eqToHom_trans]⟩

@[simp]
lemma comp_eqToHom_lift_iff {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a' a b : 𝒳} {f : R ⟶ S}
    {φ : a ⟶ b} {h : a' = a} : IsHomLift p f (eqToHom h ≫ φ) ↔ IsHomLift p f φ where
  mp := by intro hφ'; subst h; simpa using hφ'
  mpr := fun hφ => id_comp f ▸ IsHomLift.comp (eqToHom_codomain_lift_id h hφ.ObjLiftDomain) hφ

@[simp]
lemma eqToHom_comp_lift_iff {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b b' : 𝒳} {f : R ⟶ S}
    {φ : a ⟶ b} {h : b = b'} : IsHomLift p f (φ ≫ eqToHom h) ↔ IsHomLift p f φ where
  mp := by intro hφ'; subst h; simpa using hφ'
  mpr := fun hφ => comp_id f ▸ IsHomLift.comp hφ (eqToHom_domain_lift_id h hφ.ObjLiftCodomain)

@[simp]
lemma lift_eqToHom_comp_iff {p : 𝒳 ⥤ 𝒮} {R' R S : 𝒮} {a b : 𝒳} {f : R ⟶ S}
    {φ : a ⟶ b} (h : R' = R) : IsHomLift p ((eqToHom h) ≫ f) φ ↔ IsHomLift p f φ where
  mp := by intro hφ'; subst h; simpa using hφ'
  mpr := fun hφ =>
    id_comp φ ▸ IsHomLift.comp (IsHomLift.id_lift_eqToHom_codomain h hφ.ObjLiftDomain) hφ

@[simp]
lemma lift_comp_eqToHom_iff {p : 𝒳 ⥤ 𝒮} {R S S': 𝒮} {a b : 𝒳} {f : R ⟶ S}
    {φ : a ⟶ b} (h : S = S') : IsHomLift p (f ≫ (eqToHom h)) φ ↔ IsHomLift p f φ where
  mp := by intro hφ'; subst h; simpa using hφ'
  mpr := fun hφ =>
    comp_id φ ▸ IsHomLift.comp hφ (IsHomLift.id_lift_eqToHom_domain h hφ.ObjLiftCodomain)

/-- The isomorphism `R ≅ S` obtained from an isomorphism `φ : a ≅ b` lifting `f` -/
def Iso_of_Iso_lift {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ≅ b}
    (hφ : IsHomLift p f φ.hom) : R ≅ S :=
  eqToIso hφ.ObjLiftDomain.symm ≪≫ p.mapIso φ ≪≫ eqToIso hφ.ObjLiftCodomain

@[simp]
lemma Iso_of_Iso_lift_hom {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ≅ b}
    (hφ : IsHomLift p f φ.hom) : (Iso_of_Iso_lift hφ).hom = f := by
  simp [Iso_of_Iso_lift, IsHomLift.hom_eq hφ]

@[simp]
lemma Iso_of_Iso_lift_comp {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ≅ b}
    (hφ : IsHomLift p f φ.hom) : (Iso_of_Iso_lift hφ).inv ≫ f = 𝟙 S := by
  rw [CategoryTheory.Iso.inv_comp_eq]
  simp only [Iso_of_Iso_lift_hom, comp_id]

@[simp]
lemma comp_Iso_of_Iso_lift {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ≅ b}
    (hφ : IsHomLift p f φ.hom) : f ≫ (Iso_of_Iso_lift hφ).inv = 𝟙 R := by
  rw [CategoryTheory.Iso.comp_inv_eq]
  simp only [Iso_of_Iso_lift_hom, id_comp]

/-- If `φ : a ⟶ b` lifts `f : R ⟶ S` and `φ` is an isomorphism, then so is `f`. -/
lemma IsIso_of_lift_IsIso {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
    (hφ : IsHomLift p f φ) [IsIso φ] : IsIso f :=
  (IsHomLift.hom_eq hφ) ▸ inferInstance

/-- Given `φ : a ≅ b` and `f : R ≅ S`, such that `φ.hom` lifts `f.hom`, then `φ.inv` lifts
`f.inv`. -/
protected lemma inv_lift_inv {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ≅ S} {φ : a ≅ b}
    (hφ : IsHomLift p f.hom φ.hom) : IsHomLift p f.inv φ.inv where
  ObjLiftDomain := hφ.2
  ObjLiftCodomain := hφ.1
  HomLift := CommSq.horiz_inv (f:=p.mapIso φ) (i:=f) hφ.3

/-- Given `φ : a ≅ b` and `f : R ⟶ S`, such that `φ.hom` lifts `f`, then `φ.inv` lifts the
inverse of `f` given by `Iso_of_Iso_lift`. -/
protected lemma inv_lift_inv' {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ≅ b}
    (hφ : IsHomLift p f φ.hom) : IsHomLift p (Iso_of_Iso_lift hφ).inv φ.inv where
  ObjLiftDomain := hφ.2
  ObjLiftCodomain := hφ.1
  HomLift := CommSq.horiz_inv (f:=p.mapIso φ) (i:=Iso_of_Iso_lift hφ) (by simpa using hφ.3)

/-- If `φ : a ⟶ b` lifts `f : R ⟶ S` and both are isomorphisms, then `φ⁻¹` lifts `f⁻¹`. -/
protected lemma inv {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
    (hφ : IsHomLift p f φ) [IsIso φ] [IsIso f] : IsHomLift p (inv f) (inv φ) :=
  IsHomLift.inv_lift_inv (f:=asIso f) (φ:= asIso φ) hφ

/-- If `φ : a ⟶ b` is an isomorphism, and lifts `𝟙 S` for some `S : 𝒮`, then `φ⁻¹` also
lifts `𝟙 S` -/
lemma lift_id_inv {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a b : 𝒳} {φ : a ⟶ b} [IsIso φ]
    (hφ : IsHomLift p (𝟙 S) φ) : IsHomLift p (𝟙 S) (inv φ) :=
  (IsIso.inv_id (X:=S)) ▸ IsHomLift.inv hφ

end IsHomLift
