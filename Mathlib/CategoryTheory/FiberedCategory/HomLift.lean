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

Given morphism `φ : a ⟶ b` in `𝒳` and `f : R ⟶ S` in `𝒮`, `p.IsHomLift f φ` is defined as a
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

open CategoryTheory Category

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒳] [Category.{v₂} 𝒮] (p : 𝒳 ⥤ 𝒮)

namespace CategoryTheory

/-- Given a functor `p : 𝒳 ⥤ 𝒮`, an arrow `φ : a ⟶ b` in `𝒳` and an arrow `f : R ⟶ S` in `𝒮`,
`p.IsHomLift f φ` expresses the fact that `φ` lifts `f` through `p`.
This is often drawn as:
```
  a --φ--> b
  -        -
  |        |
  v        v
  R --f--> S
``` -/
class Functor.IsHomLift  {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) : Prop where
  domain_eq : p.obj a = R := by aesop_cat
  codomain_eq : p.obj b = S := by aesop_cat
  fac : f = eqToHom domain_eq.symm ≫ p.map φ ≫ eqToHom codomain_eq := by aesop_cat

/-- For any arrow `φ : a ⟶ b` in `𝒳`, `φ` lifts the arrow `p.map φ` in the base `𝒮`-/
instance  {a b : 𝒳} (φ : a ⟶ b) : p.IsHomLift (p.map φ) φ where
instance  (a : 𝒳) : p.IsHomLift (𝟙 (p.obj a)) (𝟙 a) where

namespace IsHomLift

protected lemma id {p : 𝒳 ⥤ 𝒮} {R : 𝒮} {a : 𝒳} (ha : p.obj a = R) : p.IsHomLift (𝟙 R) (𝟙 a) where

section

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ]

lemma domain_eq : p.obj a = R :=
  Functor.IsHomLift.domain_eq f φ

lemma codomain_eq  : p.obj b = S :=
  Functor.IsHomLift.codomain_eq f φ

lemma fac : f = eqToHom (domain_eq p f φ).symm ≫ p.map φ ≫ eqToHom (codomain_eq p f φ) :=
  Functor.IsHomLift.fac

lemma fac' : p.map φ = eqToHom (domain_eq p f φ) ≫ f ≫ eqToHom (codomain_eq p f φ).symm := by
  simp [fac p f φ]

lemma commSq : CommSq (p.map φ) (eqToHom (domain_eq p f φ)) (eqToHom (codomain_eq p f φ)) f where
  w := by simp only [fac p f φ, eqToHom_trans_assoc, eqToHom_refl, id_comp]

end

lemma of_commSq {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S)
    (h : CommSq (p.map φ) (eqToHom ha) (eqToHom hb) f) : p.IsHomLift f φ where
  fac := by simp only [h.1, eqToHom_trans_assoc, eqToHom_refl, id_comp]

lemma eq_of_isHomLift {a b : 𝒳} (f : p.obj a ⟶ p.obj b) (φ : a ⟶ b) [p.IsHomLift f φ] :
    f = p.map φ := by
  simpa only [eqToHom_refl, comp_id, id_comp] using fac p f φ

instance comp {p : 𝒳 ⥤ 𝒮} {R S T : 𝒮} {a b c : 𝒳} {f : R ⟶ S} {g : S ⟶ T} (φ : a ⟶ b)
    (ψ : b ⟶ c) [p.IsHomLift f φ] [p.IsHomLift g ψ] : p.IsHomLift (f ≫ g) (φ ≫ ψ) := by
  apply of_commSq
  rw [p.map_comp]
  apply CommSq.horiz_comp (commSq p f φ) (commSq p g ψ)

/-- If `φ : a ⟶ b` and `ψ : b ⟶ c` lift `𝟙 S`, then so does `φ ≫ ψ` -/
instance lift_id_comp {p : 𝒳 ⥤ 𝒮} {R : 𝒮} {a b c : 𝒳} {φ : a ⟶ b} {ψ : b ⟶ c}
    [p.IsHomLift (𝟙 R) φ] [p.IsHomLift (𝟙 R) ψ] : p.IsHomLift (𝟙 R) (φ ≫ ψ) :=
  comp_id (𝟙 R) ▸ comp φ ψ

/-- If `φ : a ⟶ b` lifts `f` and `ψ : b ⟶ c` lifts `𝟙 T`, then `φ  ≫ ψ` lifts `f` -/
lemma comp_lift_id_right {R S : 𝒮} {a b c : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ]
    (T : 𝒮) (ψ : b ⟶ c) [p.IsHomLift (𝟙 T) ψ] : p.IsHomLift f (φ ≫ ψ) := by
  obtain rfl : S = T := by rw [← codomain_eq p f φ, domain_eq p (𝟙 T) ψ]
  simpa using inferInstanceAs (p.IsHomLift (f ≫ 𝟙 S) (φ ≫ ψ))

/-- If `φ : a ⟶ b` lifts `𝟙 T` and `ψ : b ⟶ c` lifts `f`, then `φ  ≫ ψ` lifts `f` -/
lemma comp_lift_id_left {S T : 𝒮} {a b c : 𝒳} (f : S ⟶ T) (φ : a ⟶ b) (R : 𝒮)
    [p.IsHomLift (𝟙 R) φ] (ψ : b ⟶ c) [p.IsHomLift f ψ] : p.IsHomLift f (φ ≫ ψ) := by
  obtain rfl : R = S := by rw [← codomain_eq p (𝟙 R) φ, domain_eq p f ψ]
  simpa using inferInstanceAs (p.IsHomLift (𝟙 R ≫ f) (φ ≫ ψ))

lemma eqToHom_domain_lift_id {p : 𝒳 ⥤ 𝒮} {a b : 𝒳} (hab : a = b) {R : 𝒮} (hR : p.obj a = R) :
    p.IsHomLift (𝟙 R) (eqToHom hab) where
  fac := by simp [eqToHom_map]

lemma eqToHom_codomain_lift_id {p : 𝒳 ⥤ 𝒮} {a b : 𝒳} (hab : a = b) {S : 𝒮} (hS : p.obj b = S) :
    p.IsHomLift (𝟙 S) (eqToHom hab) where
  fac := by simp [eqToHom_map]

lemma id_lift_eqToHom_domain {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} (hRS : R = S) {a : 𝒳} (ha : p.obj a = R) :
    p.IsHomLift (eqToHom hRS) (𝟙 a) where
  fac := by simp [eqToHom_map]

lemma id_lift_eqToHom_codomain {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} (hRS : R = S) {b : 𝒳} (hb : p.obj b = S) :
    p.IsHomLift (eqToHom hRS) (𝟙 b) where
  fac := by simp [eqToHom_map]

instance comp_eqToHom_lift {R S : 𝒮} {a' a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : a' = a)
    [p.IsHomLift f φ] : p.IsHomLift f (eqToHom h ≫ φ) :=
  have := eqToHom_codomain_lift_id h (domain_eq p f φ)
  id_comp f ▸ comp (eqToHom h) φ

instance eqToHom_comp_lift {R S : 𝒮} {a b b' : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : b = b')
    [p.IsHomLift f φ] : p.IsHomLift f (φ ≫ eqToHom h) :=
  have := eqToHom_domain_lift_id h (codomain_eq p f φ)
  comp_id f ▸ comp φ (eqToHom h)

instance lift_eqToHom_comp {R' R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : R' = R)
    [p.IsHomLift f φ] : p.IsHomLift ((eqToHom h) ≫ f) φ :=
  have := id_lift_eqToHom_codomain h (domain_eq p f φ)
  id_comp φ ▸ comp (𝟙 a) φ

instance lift_comp_eqToHom {R S S': 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : S = S')
    [p.IsHomLift f φ] : p.IsHomLift (f ≫ (eqToHom h)) φ :=
  have := id_lift_eqToHom_domain h (codomain_eq p f φ)
  comp_id φ ▸ comp φ (𝟙 b)

@[simp]
lemma comp_eqToHom_lift_iff {R S : 𝒮} {a' a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : a' = a) :
    p.IsHomLift f (eqToHom h ≫ φ) ↔ p.IsHomLift f φ where
  mp := by intro hφ'; subst h; simpa using hφ'
  mpr := fun hφ => inferInstance

@[simp]
lemma eqToHom_comp_lift_iff {R S : 𝒮} {a b b' : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : b = b') :
    p.IsHomLift f (φ ≫ eqToHom h) ↔ p.IsHomLift f φ where
  mp := by intro hφ'; subst h; simpa using hφ'
  mpr := fun hφ => inferInstance

@[simp]
lemma lift_eqToHom_comp_iff {R' R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : R' = R) :
    p.IsHomLift ((eqToHom h) ≫ f) φ ↔ p.IsHomLift f φ where
  mp := by intro hφ'; subst h; simpa using hφ'
  mpr := fun hφ => inferInstance

@[simp]
lemma lift_comp_eqToHom_iff {R S S' : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : S = S') :
    p.IsHomLift (f ≫ (eqToHom h)) φ ↔ p.IsHomLift f φ where
  mp := by intro hφ'; subst h; simpa using hφ'
  mpr := fun hφ => inferInstance

/-- The isomorphism `R ≅ S` obtained from an isomorphism `φ : a ≅ b` lifting `f` -/
def isoOfIsoLift  {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom] :
    R ≅ S :=
  eqToIso (domain_eq p f φ.hom).symm ≪≫ p.mapIso φ ≪≫
    eqToIso (codomain_eq p f φ.hom)

@[simp]
lemma isoOfIsoLift_hom {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom] :
    (isoOfIsoLift p f φ).hom = f := by
  simp [isoOfIsoLift, fac p f φ.hom]

@[simp]
lemma isoOfIsoLift_comp {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom] :
    (isoOfIsoLift p f φ).inv ≫ f = 𝟙 S := by
  rw [CategoryTheory.Iso.inv_comp_eq]
  simp only [isoOfIsoLift_hom, comp_id]

@[simp]
lemma comp_isoOfIsoLift {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom] :
    f ≫ (isoOfIsoLift p f φ).inv = 𝟙 R := by
  rw [CategoryTheory.Iso.comp_inv_eq]
  simp only [isoOfIsoLift_hom, id_comp]

/-- If `φ : a ⟶ b` lifts `f : R ⟶ S` and `φ` is an isomorphism, then so is `f`. -/
lemma isIso_of_lift_isIso {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ]
    [IsIso φ] : IsIso f :=
  (fac p f φ) ▸ inferInstance

/-- Given `φ : a ≅ b` and `f : R ≅ S`, such that `φ.hom` lifts `f.hom`, then `φ.inv` lifts
`f.inv`. -/
protected instance inv_lift_inv {R S : 𝒮} {a b : 𝒳} (f : R ≅ S) (φ : a ≅ b)
    [p.IsHomLift f.hom φ.hom] : p.IsHomLift f.inv φ.inv := by
  apply of_commSq
  apply CommSq.horiz_inv (f:=p.mapIso φ) (commSq p f.hom φ.hom)

/-- Given `φ : a ≅ b` and `f : R ⟶ S`, such that `φ.hom` lifts `f`, then `φ.inv` lifts the
inverse of `f` given by `isoOfIsoLift`. -/
protected instance inv_lift {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom] :
    p.IsHomLift (isoOfIsoLift p f φ).inv φ.inv := by
  apply of_commSq
  apply CommSq.horiz_inv (f:=p.mapIso φ) (by simpa using (commSq p f φ.hom))

/-- If `φ : a ⟶ b` lifts `f : R ⟶ S` and both are isomorphisms, then `φ⁻¹` lifts `f⁻¹`. -/
protected instance inv {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [IsIso f] [IsIso φ]
    [p.IsHomLift f φ] : p.IsHomLift (inv f) (inv φ) :=
  have : p.IsHomLift (asIso f).hom (asIso φ).hom := by simp; infer_instance
  IsHomLift.inv_lift_inv p (asIso f) (asIso φ)

/-- If `φ : a ⟶ b` is an isomorphism, and lifts `𝟙 S` for some `S : 𝒮`, then `φ⁻¹` also
lifts `𝟙 S` -/
instance lift_id_inv {S : 𝒮} {a b : 𝒳} (φ : a ⟶ b) [IsIso φ] [p.IsHomLift (𝟙 S) φ] :
    p.IsHomLift (𝟙 S) (inv φ) :=
  (IsIso.inv_id (X:=S)) ▸ (IsHomLift.inv p _ φ)

end IsHomLift

end CategoryTheory
