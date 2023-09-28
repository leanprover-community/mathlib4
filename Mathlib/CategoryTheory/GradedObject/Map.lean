/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.GradedObject

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category C]

-- to be moved to CategoryTheory.GradedObject
namespace GradedObject

section

variable {I J K : Type*} (X Y : GradedObject I C) (p : I → J) (q : J → K) (r : I → K)
  (hpqr : ∀ i, r i = q (p i))

section

variable (k : K) (c : ∀ (j : J) (_ : q j = k), X.CofanMapObjFun p j)
  (hc : ∀ j hj, IsColimit (c j hj))
  (c' : Cofan (fun (j : q ⁻¹' {k}) => (c j.1 j.2).pt))
  (hc' : IsColimit c')

@[simp]
def cofanMapObjComp : X.CofanMapObjFun r k :=
  CofanMapObjFun.mk _ _ _ c'.pt (fun i hi =>
    (c (p i) (by rw [← hpqr, hi])).inj ⟨i, rfl⟩ ≫ c'.inj (⟨p i, by
      rw [Set.mem_preimage, Set.mem_singleton_iff, ← hpqr, hi]⟩))

@[simp]
def isColimitCofanMapObjComp :
    IsColimit (cofanMapObjComp X p q r hpqr k c c') :=
  mkCofanColimit _
    (fun s => Cofan.IsColimit.desc hc'
      (fun ⟨j, (hj : q j = k)⟩ => Cofan.IsColimit.desc (hc j hj)
        (fun ⟨i, (hi : p i = j)⟩ => s.inj ⟨i, by
          simp only [Set.mem_preimage, Set.mem_singleton_iff, hpqr, hi, hj]⟩)))
    (fun s ⟨i, (hi : r i = k)⟩ => by simp)
    (fun s m hm => by
      apply Cofan.IsColimit.hom_ext hc'
      rintro ⟨j, rfl : q j = k⟩
      apply Cofan.IsColimit.hom_ext (hc j rfl)
      rintro ⟨i, rfl : p i = j⟩
      dsimp
      rw [Cofan.IsColimit.fac, Cofan.IsColimit.fac, ← hm]
      dsimp
      rw [assoc])

lemma hasMap_comp [X.HasMap p] [(X.mapObj p).HasMap q] : X.HasMap r :=
  fun k => ⟨_, isColimitCofanMapObjComp X p q r hpqr k _
    (fun j _ => X.isColimitCofanMapObj p j) _ ((X.mapObj p).isColimitCofanMapObj q k)⟩

end

variable [X.HasMap p] [(X.mapObj p).HasMap q] [X.HasMap r]

noncomputable def mapObjMapObjIso : (X.mapObj p).mapObj q ≅ X.mapObj r :=
  isoMk _ _ (fun k => CofanMapObjFun.iso (isColimitCofanMapObjComp X p q r hpqr k _
      (fun j _ => X.isColimitCofanMapObj p j) _ ((X.mapObj p).isColimitCofanMapObj q k)))

@[simp]
lemma mapObjMapObjIso_hom (k : K) :
    (mapObjMapObjIso X p q r hpqr).hom k =
      descMapObj _ _ (fun j hj =>
        descMapObj _ _ (fun i hi => X.ιMapObj r i k (by rw [hpqr, hi, hj]))) := rfl

@[simp]
lemma mapObjMapObjIso_inv (k : K) :
    (mapObjMapObjIso X p q r hpqr).inv k =
      descMapObj _ _ (fun i hi => X.ιMapObj p i (p i) rfl ≫
        (X.mapObj p).ιMapObj q (p i) k (by rw [← hi, hpqr])) := rfl

end

end GradedObject

end CategoryTheory
