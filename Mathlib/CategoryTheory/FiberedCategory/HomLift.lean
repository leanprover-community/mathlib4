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
class Functor.IsHomLift (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) : Prop where
  domain_eq : p.obj a = R
  codomain_eq : p.obj b = S
  homlift : CommSq (p.map φ) (eqToHom domain_eq) (eqToHom codomain_eq) f

namespace Functor.IsHomLift

protected lemma hom_eq {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
    [hφ : IsHomLift p f φ] : f = eqToHom hφ.domain_eq.symm ≫ p.map φ ≫
      eqToHom hφ.codomain_eq :=
  ((eqToHom_comp_iff hφ.domain_eq _ _).1 hφ.homlift.w.symm)

protected lemma hom_eq' {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
   [hφ : IsHomLift p f φ] : p.map φ = eqToHom hφ.domain_eq ≫ f ≫
      eqToHom hφ.codomain_eq.symm := by
  rw [← assoc, ← comp_eqToHom_iff hφ.codomain_eq _ _]
  exact hφ.homlift.w

lemma eq_of_IsHomLift {p : 𝒳 ⥤ 𝒮} (a b : 𝒳) {f : p.obj a ⟶ p.obj b} {φ : a ⟶ b}
   [hφ : IsHomLift p f φ] : f = p.map φ := by
  simpa using hφ.hom_eq

/-- For any arrow `φ : a ⟶ b` in `𝒳`, `φ` lifts the arrow `p.map φ` in the base `𝒮`-/
@[simp]
protected lemma self (p : 𝒳 ⥤ 𝒮) {a b : 𝒳} (φ : a ⟶ b) : IsHomLift p (p.map φ) φ where
  domain_eq := rfl
  codomain_eq := rfl
  homlift := ⟨by simp only [eqToHom_refl, comp_id, id_comp]⟩

@[simp]
protected lemma id {p : 𝒳 ⥤ 𝒮} {R : 𝒮} {a : 𝒳} (ha : p.obj a = R) : IsHomLift p (𝟙 R) (𝟙 a) :=
  ha ▸ (p.map_id _ ▸ IsHomLift.self p (𝟙 a))

protected lemma comp {p : 𝒳 ⥤ 𝒮} {R S T : 𝒮} {a b c : 𝒳} {f : R ⟶ S}
    {g : S ⟶ T} {φ : a ⟶ b} {ψ : b ⟶ c} [hφ : IsHomLift p f φ]
    [hψ : IsHomLift p g ψ] : IsHomLift p (f ≫ g) (φ ≫ ψ) where
  domain_eq := hφ.1
  codomain_eq := hψ.2
  homlift := (p.map_comp _ _).symm ▸ CommSq.horiz_comp hφ.3 hψ.3

/-- If `φ : a ⟶ b` and `ψ : b ⟶ c` lift `𝟙 S`, then so does `φ ≫ ψ` -/
lemma lift_id_comp {p : 𝒳 ⥤ 𝒮} {R : 𝒮} {a b c : 𝒳} {φ : a ⟶ b} {ψ : b ⟶ c}
    (hφ : IsHomLift p (𝟙 R) φ) [IsHomLift p (𝟙 R) ψ] : IsHomLift p (𝟙 R) (φ ≫ ψ) :=
  comp_id (𝟙 R) ▸ hφ.comp

/-- If `φ : a ⟶ b` lifts `f` and `ψ : b ⟶ c` lifts `𝟙 T`, then `φ  ≫ ψ` lifts `f` -/
lemma comp_lift_id {p : 𝒳 ⥤ 𝒮} {R S T : 𝒮} {a b c : 𝒳} {f : R ⟶ S}
    {φ : a ⟶ b} [hφ : IsHomLift p f φ] {ψ : b ⟶ c} [hψ : IsHomLift p (𝟙 T) ψ] :
    IsHomLift p f (φ ≫ ψ) where
  domain_eq := hφ.domain_eq
  codomain_eq := by rw [hψ.codomain_eq, ← hψ.domain_eq, hφ.codomain_eq]
  homlift := ⟨by simp [hψ.hom_eq', hφ.3.1]⟩

@[simp]
lemma eqToHom_domain_lift_id {p : 𝒳 ⥤ 𝒮} {a b : 𝒳} (hab : a = b) {R : 𝒮}
    (hR : p.obj a = R) : IsHomLift p (𝟙 R) (eqToHom hab) where
  domain_eq := hR
  codomain_eq := hab ▸ hR
  homlift := ⟨by simp only [eqToHom_map, eqToHom_trans, comp_id]⟩

@[simp]
lemma eqToHom_codomain_lift_id {p : 𝒳 ⥤ 𝒮} {a b : 𝒳} (hab : a = b) {S : 𝒮}
    (hS : p.obj b = S) : IsHomLift p (𝟙 S) (eqToHom hab) where
  domain_eq := hab ▸ hS
  codomain_eq := hS
  homlift := ⟨by simp only [eqToHom_map, eqToHom_trans, comp_id]⟩

@[simp]
lemma id_lift_eqToHom_domain {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} (hRS : R = S)
    {a : 𝒳} (ha : p.obj a = R) : IsHomLift p (eqToHom hRS) (𝟙 a) where
  domain_eq := ha
  codomain_eq := hRS ▸ ha
  homlift := ⟨by simp only [map_id, id_comp, eqToHom_trans]⟩

@[simp]
lemma id_lift_eqToHom_codomain {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} (hRS : R = S)
    {b : 𝒳} (hb : p.obj b = S) : IsHomLift p (eqToHom hRS) (𝟙 b) where
  domain_eq := hRS ▸ hb
  codomain_eq := hb
  homlift := ⟨by simp only [map_id, id_comp, eqToHom_trans]⟩

instance comp_eqToHom_lift {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a' a b : 𝒳} {f : R ⟶ S}
    {φ : a ⟶ b} {h : a' = a} [hφ : IsHomLift p f φ] : IsHomLift p f (eqToHom h ≫ φ) :=
  id_comp f ▸ (eqToHom_codomain_lift_id h hφ.domain_eq).comp

instance eqToHom_comp_lift {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b b' : 𝒳} {f : R ⟶ S}
    {φ : a ⟶ b} {h : b = b'} [hφ : IsHomLift p f φ] : IsHomLift p f (φ ≫ eqToHom h) :=
  comp_id f ▸ hφ.comp (hψ := eqToHom_domain_lift_id h hφ.codomain_eq)

instance lift_eqToHom_comp {p : 𝒳 ⥤ 𝒮} {R' R S : 𝒮} {a b : 𝒳} {f : R ⟶ S}
    {φ : a ⟶ b} (h : R' = R) [hφ : IsHomLift p f φ] : IsHomLift p ((eqToHom h) ≫ f) φ :=
  id_comp φ ▸ (IsHomLift.id_lift_eqToHom_codomain h hφ.domain_eq).comp

instance lift_comp_eqToHom {p : 𝒳 ⥤ 𝒮} {R S S': 𝒮} {a b : 𝒳} {f : R ⟶ S}
    {φ : a ⟶ b} (h : S = S') [hφ : IsHomLift p f φ] : IsHomLift p (f ≫ (eqToHom h)) φ :=
  comp_id φ ▸ hφ.comp (hψ := IsHomLift.id_lift_eqToHom_domain h hφ.codomain_eq)

@[simp]
lemma comp_eqToHom_lift_iff {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a' a b : 𝒳} {f : R ⟶ S}
    {φ : a ⟶ b} {h : a' = a} : IsHomLift p f (eqToHom h ≫ φ) ↔ IsHomLift p f φ where
  mp := by intro hφ'; subst h; simpa using hφ'
  mpr := fun hφ => inferInstance

@[simp]
lemma eqToHom_comp_lift_iff {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b b' : 𝒳} {f : R ⟶ S}
    {φ : a ⟶ b} {h : b = b'} : IsHomLift p f (φ ≫ eqToHom h) ↔ IsHomLift p f φ where
  mp := by intro hφ'; subst h; simpa using hφ'
  mpr := fun hφ => inferInstance

@[simp]
lemma lift_eqToHom_comp_iff {p : 𝒳 ⥤ 𝒮} {R' R S : 𝒮} {a b : 𝒳} {f : R ⟶ S}
    {φ : a ⟶ b} (h : R' = R) : IsHomLift p ((eqToHom h) ≫ f) φ ↔ IsHomLift p f φ where
  mp := by intro hφ'; subst h; simpa using hφ'
  mpr := fun hφ => inferInstance

@[simp]
lemma lift_comp_eqToHom_iff {p : 𝒳 ⥤ 𝒮} {R S S': 𝒮} {a b : 𝒳} {f : R ⟶ S}
    {φ : a ⟶ b} (h : S = S') : IsHomLift p (f ≫ (eqToHom h)) φ ↔ IsHomLift p f φ where
  mp := by intro hφ'; subst h; simpa using hφ'
  mpr := fun hφ => inferInstance

/-- The isomorphism `R ≅ S` obtained from an isomorphism `φ : a ≅ b` lifting `f` -/
def Iso_of_Iso_lift {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ≅ b}
    [hφ : IsHomLift p f φ.hom] : R ≅ S :=
  eqToIso hφ.domain_eq.symm ≪≫ p.mapIso φ ≪≫ eqToIso hφ.codomain_eq

@[simp]
lemma Iso_of_Iso_lift_hom {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ≅ b}
    [hφ : IsHomLift p f φ.hom] : (hφ.Iso_of_Iso_lift).hom = f := by
  simp [Iso_of_Iso_lift, hφ.hom_eq]

@[simp]
lemma Iso_of_Iso_lift_comp {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ≅ b}
    [hφ : IsHomLift p f φ.hom] : (hφ.Iso_of_Iso_lift).inv ≫ f = 𝟙 S := by
  rw [CategoryTheory.Iso.inv_comp_eq]
  simp only [Iso_of_Iso_lift_hom, comp_id]

@[simp]
lemma comp_Iso_of_Iso_lift {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ≅ b}
    [hφ : IsHomLift p f φ.hom] : f ≫ (hφ.Iso_of_Iso_lift).inv = 𝟙 R := by
  rw [CategoryTheory.Iso.comp_inv_eq]
  simp only [Iso_of_Iso_lift_hom, id_comp]

/-- If `φ : a ⟶ b` lifts `f : R ⟶ S` and `φ` is an isomorphism, then so is `f`. -/
lemma IsIso_of_lift_IsIso {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
   [hφ : IsHomLift p f φ] [IsIso φ] : IsIso f :=
  hφ.hom_eq ▸ inferInstance

/-- Given `φ : a ≅ b` and `f : R ≅ S`, such that `φ.hom` lifts `f.hom`, then `φ.inv` lifts
`f.inv`. -/
protected instance inv_lift_inv {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ≅ S} {φ : a ≅ b}
    [hφ : IsHomLift p f.hom φ.hom] : IsHomLift p f.inv φ.inv where
  domain_eq := hφ.2
  codomain_eq := hφ.1
  homlift := CommSq.horiz_inv (f:=p.mapIso φ) (i:=f) hφ.3

/-- Given `φ : a ≅ b` and `f : R ⟶ S`, such that `φ.hom` lifts `f`, then `φ.inv` lifts the
inverse of `f` given by `Iso_of_Iso_lift`. -/
protected instance inv_lift {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ≅ b}
    [hφ : IsHomLift p f φ.hom] : IsHomLift p (hφ.Iso_of_Iso_lift).inv φ.inv where
  domain_eq := hφ.2
  codomain_eq := hφ.1
  homlift := CommSq.horiz_inv (f:=p.mapIso φ) (i:=hφ.Iso_of_Iso_lift) (by simpa using hφ.3)

/-- If `φ : a ⟶ b` lifts `f : R ⟶ S` and both are isomorphisms, then `φ⁻¹` lifts `f⁻¹`. -/
protected instance inv {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
    [hφ : IsHomLift p f φ] [IsIso φ] [IsIso f] : IsHomLift p (inv f) (inv φ) :=
  IsHomLift.inv_lift_inv (f := asIso f) (φ := asIso φ) (hφ := hφ)

/-- If `φ : a ⟶ b` is an isomorphism, and lifts `𝟙 S` for some `S : 𝒮`, then `φ⁻¹` also
lifts `𝟙 S` -/
instance lift_id_inv {p : 𝒳 ⥤ 𝒮} {S : 𝒮} {a b : 𝒳} {φ : a ⟶ b} [IsIso φ]
    [hφ : IsHomLift p (𝟙 S) φ] : IsHomLift p (𝟙 S) (inv φ) :=
  (IsIso.inv_id (X:=S)) ▸ hφ.inv

end Functor.IsHomLift
