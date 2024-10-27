/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-!

-/

universe u

open CategoryTheory Limits

namespace ModuleCat

variable (A : Type u) [Ring A]

structure AbstractPresentation where
  G : Type u
  R : Type u
  r : R → (free A).obj G

namespace AbstractPresentation

variable {A} (pres : AbstractPresentation A)

noncomputable abbrev map : (free A).obj pres.R ⟶ (free A).obj pres.G :=
  freeDesc pres.r

variable (M : ModuleCat.{u} A)

structure HomData where
  generator : pres.G → M
  freeDesc_r_eq_zero (r : pres.R) : (freeDesc generator) (pres.r r) = 0

namespace HomData

variable {pres M} (data : pres.HomData M)

noncomputable def π : (free A).obj pres.G ⟶ M := freeDesc data.generator

@[simp]
lemma π_generator (g : pres.G) :
    data.π (freeMk g) = data.generator g := by
  simp [π]

@[simp]
lemma π_r (r : pres.R) : data.π (pres.r r) = 0 := by
  simp [π, freeDesc_r_eq_zero]

@[reassoc (attr := simp)]
lemma map_π : pres.map ≫ data.π = 0 := by aesop

noncomputable abbrev cokernelCofork : CokernelCofork pres.map :=
  CokernelCofork.ofπ _ data.map_π

protected noncomputable abbrev IsColimit : Type _ :=
  IsColimit data.cokernelCofork

section

variable (π : (free A).obj pres.G ⟶ M)
  (π_r : ∀ (r : pres.R), π (pres.r r) = 0)

@[simps]
noncomputable def ofπ : pres.HomData M where
  generator g := π (freeMk g)
  freeDesc_r_eq_zero r := by convert π_r r; aesop

@[simp]
lemma ofπ_π : (ofπ π π_r).π = π := by aesop

end

/-- Alternative constructor `AbstractPresentation.HomData` where the vanishing
condition is expressed as an equality of morphisms `pres.map ≫ π = 0`. -/
noncomputable abbrev ofπ' (π : (free A).obj pres.G ⟶ M) (hπ : pres.map ≫ π = 0) :
    pres.HomData M :=
  ofπ π (fun r ↦ by simpa using congr_fun ((forget _).congr_map hπ) (freeMk r))

noncomputable abbrev ofCokernelCofork (c : CokernelCofork pres.map) :
    pres.HomData c.pt := ofπ' c.π c.condition

noncomputable def ofCokernelCoforkIsColimit {c : CokernelCofork pres.map}
    (hc : IsColimit c) :
    (ofCokernelCofork c).IsColimit :=
  IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _))

variable {data}

noncomputable def isColimitMk
    (desc : ∀ {N : ModuleCat.{u} A} (_ : pres.HomData N), M ⟶ N)
    (fac : ∀ {N : ModuleCat.{u} A} (μ : pres.HomData N) (g : pres.G),
      desc μ (data.generator g) = μ.generator g)
    (hom_ext : ∀ {N : ModuleCat.{u} A} {f f' : M ⟶ N}
      (_ : ∀ (g : pres.G), f (data.generator g) = f' (data.generator g)), f = f') :
    data.IsColimit :=
  CokernelCofork.IsColimit.ofπ _ _ (fun {N} f hf ↦ desc (ofπ' f hf))
    (fun {N} f hf ↦ by ext g; simpa using fac (ofπ' f hf) g)
    (fun {N} f hf φ hφ ↦ hom_ext (fun g ↦ by simp [fac, ← hφ]))

end HomData

noncomputable def module : ModuleCat.{u} A := cokernel pres.map

noncomputable def moduleHomData : pres.HomData pres.module :=
  HomData.ofCokernelCofork
    (CokernelCofork.ofπ _ (cokernel.condition pres.map))

@[simp]
lemma moduleHomData_π : pres.moduleHomData.π = cokernel.π _ := by
  simp [moduleHomData]

noncomputable def moduleIsCokernel : pres.moduleHomData.IsColimit :=
  HomData.ofCokernelCoforkIsColimit (cokernelIsCokernel _)

variable (A)

@[simps]
def free (G : Type u) : AbstractPresentation A where
  G := G
  R := PEmpty
  r := PEmpty.elim

@[simp]
lemma free_map (G : Type u) : (free A G).map = 0 := by ext ⟨⟩

end AbstractPresentation

section

variable {A} (M : ModuleCat.{u} A) (pres : AbstractPresentation A)

structure Presentation where
  homData : pres.HomData M
  isColimit : homData.IsColimit

end

section

noncomputable def freeObjPresentation (G : Type u) :
    ((free A).obj G).Presentation (AbstractPresentation.free A G) where
  homData := AbstractPresentation.HomData.ofπ (𝟙 _) (by simp)
  isColimit := IsColimit.ofIsoColimit
    (CokernelCofork.IsColimit.ofId _ (by simp)) (Cofork.ext (Iso.refl _))

@[simp]
lemma freeObjPresentation_homData_r (G : Type u) (g : G) :
    (freeObjPresentation A G).homData.generator g = freeMk g := rfl

end

namespace tautologicalPresentation

variable {A} (M : ModuleCat.{u} A)

inductive Relations : Type u
  | add (m₁ m₂ : M)
  | smul (r : A) (m : M)

variable {M} in
@[simp]
noncomputable def r (r : Relations M) : (free A).obj M := match r with
  | Relations.add m₁ m₂ => freeMk (m₁ + m₂) - freeMk m₁ - freeMk m₂
  | Relations.smul r m => freeMk (r • m) - r • freeMk m

@[simps]
noncomputable def abstract : AbstractPresentation A where
  G := M
  R := Relations M
  r := r

def homDataAbstract : (abstract M).HomData M where
  generator := id
  freeDesc_r_eq_zero r := by induction r <;> simp

variable {M} in
@[simps]
def desc {N : ModuleCat.{u} A} (data : (abstract M).HomData N) : M ⟶ N where
  toFun := data.generator
  map_add' m₁ m₂ := by
    have := data.π_r (.add m₁ m₂)
    dsimp at this
    rw [map_sub, map_sub, sub_eq_zero, sub_eq_iff_eq_add] at this
    erw [data.π_generator, data.π_generator, data.π_generator] at this
    rw [this]
    apply add_comm
  map_smul' r m := by
    dsimp
    have := data.π_r (.smul r m)
    dsimp at this
    rw [map_sub, map_smul, sub_eq_zero] at this
    erw [data.π_generator, data.π_generator] at this
    exact this

noncomputable def homDataAbstractIsColimit : (homDataAbstract M).IsColimit :=
  AbstractPresentation.HomData.isColimitMk desc (by aesop) (fun h ↦ by ext; apply h)

end tautologicalPresentation

variable {A} (M : ModuleCat.{u} A)

open tautologicalPresentation in
noncomputable def tautologicalPresentation :
    M.Presentation (abstract M) where
  homData := homDataAbstract M
  isColimit := homDataAbstractIsColimit M

end ModuleCat
