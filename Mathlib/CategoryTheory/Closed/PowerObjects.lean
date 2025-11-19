/-
Copyright (c) 2025 Klaus Gy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Klaus Gy
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equalizer
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
/-!
# Elementary Topos (in Elementary Form)

This ongoing work formalizes the elementary definition of a topos and the direct consequences.

## References

* [S. MacLane and I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
-/

universe u v

open CategoryTheory
open Category Functor Limits Opposite Prod

variable {ℰ : Type u} [Category.{v} ℰ]

namespace LeftRepresentable

variable (F : (ℰ × ℰ)ᵒᵖ ⥤ Type (max u v))

abbrev fixedLeft (B : ℰ) : ℰᵒᵖ ⥤ Type (max u v) :=
  (curryObj ((prodOpEquiv ℰ).inverse ⋙ F)).obj (op B)

def curryObj' : ℰᵒᵖ ⥤ ℰᵒᵖ ⥤ Type (max u v) := curryObj ((prodOpEquiv ℰ).inverse ⋙ F)

variable {F} {B PB : ℰ} (hPB : (fixedLeft F B).RepresentableBy PB)
  {C PC : ℰ} (hPC : ((curryObj' F).obj (op C)).RepresentableBy PC)

/-- The morphism induced by a morphism between the base objects. -/
def Pmap (h : B ⟶ C) : PC ⟶ PB :=
  hPB.homEquiv.symm (F.map (h ×ₘ 𝟙 PC).op (hPC.homEquiv (𝟙 PC)))

lemma map_universal (h : B ⟶ C) :
  F.map (𝟙 B ×ₘ (Pmap hPB hPC h)).op (hPB.homEquiv (𝟙 PB))
    = F.map (h ×ₘ 𝟙 PC).op (hPC.homEquiv (𝟙 PC)) := by
  calc
    _ = (fixedLeft F B).map (Pmap hPB hPC h).op (hPB.homEquiv (𝟙 PB)) := by rfl
    _ = F.map (h ×ₘ 𝟙 PC).op (hPC.homEquiv (𝟙 PC)) := by
      rw [← hPB.homEquiv_eq, Pmap, hPB.homEquiv.apply_symm_apply]

variable {D PD : ℰ} (hPD : ((curryObj' F).obj (op D)).RepresentableBy PD)

lemma comm {PB PC : ℰ} (f : B ⟶ C) (Pf : PC ⟶ PB) :
    (f ×ₘ 𝟙 PB).op ≫ (𝟙 B ×ₘ Pf).op = (𝟙 C ×ₘ Pf).op ≫ (f ×ₘ 𝟙 PC).op :=
  congrArg Quiver.Hom.op (by simp)

lemma compose (h : B ⟶ C) (h' : C ⟶ D) :
    Pmap hPB hPD (h ≫ h') = Pmap hPC hPD h' ≫ Pmap hPB hPC h := by
  let F' := (prodOpEquiv ℰ).inverse ⋙ F
  let Ph := Pmap hPB hPC h
  let Ph' := Pmap hPC hPD h'
  apply hPB.homEquiv.injective
  calc
    _ = F.map ((h ×ₘ 𝟙 _) ≫ (h' ×ₘ 𝟙 _)).op (hPD.homEquiv (𝟙 PD)) := by unfold Pmap; simp
    _ = F.map ((h' ×ₘ 𝟙 _).op ≫ (h ×ₘ 𝟙 _).op) (hPD.homEquiv (𝟙 PD)) := by rw[op_comp]
    _ = F.map ((𝟙 _ ×ₘ Ph').op ≫ (h ×ₘ 𝟙 _).op) (hPC.homEquiv (𝟙 PC)) := by
      rw[FunctorToTypes.map_comp_apply, ← map_universal, ← FunctorToTypes.map_comp_apply];
    _ = F.map ((h ×ₘ 𝟙 _).op ≫ (𝟙 _ ×ₘ Ph').op) (hPC.homEquiv (𝟙 PC)) := by rw[comm]
    _ = F.map ((𝟙 _ ×ₘ Ph).op ≫ (𝟙 _ ×ₘ Ph').op) (hPB.homEquiv (𝟙 PB)) := by
      rw[FunctorToTypes.map_comp_apply, ← map_universal, ← FunctorToTypes.map_comp_apply]
    _ = F.map (𝟙 _ ×ₘ Ph' ≫ Ph).op (hPB.homEquiv (𝟙 PB)) := by rw[comm_op]; simp
    _ = ((curryObj' F).obj _).map (Ph' ≫ Ph).op (hPB.homEquiv (𝟙 PB)) := by
      rw[prod_comp, comp_id, op_comp]; simp only [curryObj]
    _ = hPB.homEquiv (Ph' ≫ Ph) := by rw[← hPB.homEquiv_eq]

/-- Let `F : ℰᵒᵖ × ℰᵒᵖ ⥤ Type`. If for each `B` we choose an object `P B` representing
the functor `C ↦ F (B, C)`, then these choices assemble into a covariant functor `ℰᵒᵖ ⥤ ℰ`. -/
def functor (P : ℰ → ℰ) (hP : ∀ B : ℰ, ((curryObj F).obj (op B)).RepresentableBy (P B)) :
    ℰᵒᵖ ⥤ ℰ :=
  { obj (B : ℰᵒᵖ) := P (unop B),
    map {B C : ℰᵒᵖ} (h : B ⟶ C) := map (hP (unop C)) (hP (unop B)) h.unop,
    map_id _ := by
      change (hP _).homEquiv.symm (F.map (𝟙 _) ((hP _).homEquiv (𝟙 _))) = 𝟙 _
      rw[FunctorToTypes.map_id_apply]; simp
    map_comp {B C D : ℰᵒᵖ} (h : B ⟶ C) (h' : C ⟶ D) :=
      compose (hP (unop D)) (hP (unop C)) (hP (unop B)) h'.unop h.unop }

end LeftRepresentable

open CartesianMonoidalCategory MonoidalCategory

variable [CartesianMonoidalCategory ℰ]

private abbrev cmdiag (X : ℰ) : X ⟶ X ⊗ X := lift (𝟙 X) (𝟙 X)

private lemma pullback_of_diag {B X : ℰ} (b : X ⟶ B) :
    IsPullback b (lift b (𝟙 X)) (cmdiag B) (B ◁ b) :=
  let eq : lift b (𝟙 X) ≫ fst B X = lift b (𝟙 X) ≫ snd B X ≫ b := by simp
  let lim : IsLimit (Fork.ofι (lift b (𝟙 X)) eq) :=
    Fork.IsLimit.mk _
      (fun s => s.ι ≫ (snd B X))
      (fun s => by simp[← s.condition])
      (fun s m eq => by simp[← eq])
  let pb : IsPullback _ (_ ≫ fst B X) (lift (fst B X) (snd B X ≫ b)) (cmdiag B) :=
    isPullback_equalizer_binaryFan_fork _ (fst B X) (snd B X ≫ b) _ lim
  IsPullback.flip
    (by simpa using pb)

private lemma eq_of_lift_through_diag {X Y : ℰ} {f f' g : X ⟶ Y}
    (h : lift f f' = g ≫ cmdiag Y) : f = f' := by
  calc
    _ = (lift f f') ≫ (fst Y Y) := by simp
    _ = (lift f f') ≫ (snd Y Y) := by simp[h]
    _ = f' := by simp

variable [HasPullbacks ℰ]

/-- The subobject functor for products. -/
noncomputable def subobjProd : ℰᵒᵖ × ℰᵒᵖ ⥤ Type (max u v) where
  obj P := Subobject (unop P.1 ⊗ unop P.2)
  map f := (Subobject.pullback (f.1.unop ⊗ₘ f.2.unop)).obj
  map_id A := by ext1 x; simp [Subobject.pullback_id]
  map_comp f f' := by ext1 x; simp [Subobject.pullback_comp]

/-- `P` is a power object of `B` if it represents the functor `A ↦ Subobject (B ⊗ A)`. -/
def IsPowerObjectOf (B P : ℰ) :=
  (subobjProd.curryObj.obj (op B)).RepresentableBy P

namespace PowerObject

variable {B PB : ℰ} (hPB : IsPowerObjectOf B PB)

section functoriality

variable {C PC : ℰ} (hPC : IsPowerObjectOf C PC)
  {D PD : ℰ} (hPD : IsPowerObjectOf D PD)

/-- Functoriality on the left variable of the bifunctor `(B, A) ↦ Subobject (B ⊗ A)`:
a map `h : B ⟶ C` induces `PC ⟶ PB` via left-representability. -/
noncomputable def map (h : B ⟶ C) : PC ⟶ PB := LeftRepresentable.map hPB hPC h

lemma compose (h : B ⟶ C) (h' : C ⟶ D) :
    map hPB hPD (h ≫ h') = map hPC hPD h' ≫ map hPB hPC h :=
  LeftRepresentable.compose hPB hPC hPD h h'

/-- Given a choice of representing objects `P B` for the functors `A ↦ Subobject (B ⊗ A)`,
then these choices assemble into a covariant functor `ℰᵒᵖ ⥤ ℰ`. -/
noncomputable def functor (P : ℰ → ℰ) (hP : ∀ B : ℰ, IsPowerObjectOf B (P B)) : ℰᵒᵖ ⥤ ℰ :=
  LeftRepresentable.functor P hP

end functoriality

/-- The singleton morphism from `B` to `PB`. -/
def singleton : B ⟶ PB :=
  hPB.homEquiv.invFun (Subobject.mk (cmdiag B))

private lemma pullback_diag_eq_singleton {X} (f : X ⟶ B) :
      (Subobject.pullback (B ◁ f)).obj (Subobject.mk (cmdiag B)) =
    hPB.homEquiv (f ≫ singleton hPB) := by
  calc
    _ = (subobjProd.curryObj.obj (op B)).map f.op (hPB.homEquiv (singleton hPB)) := by
      simp[subobjProd, curryObj, singleton]
    _ = hPB.homEquiv (f ≫ singleton hPB) := Eq.symm (hPB.homEquiv_comp f (singleton hPB))

noncomputable instance singleton_is_mono : Mono (singleton hPB) :=
  ⟨ fun {X} (b b' : X ⟶ B) eq ↦
    let B_sub := Subobject.mk (cmdiag B)
    let P := (Subobject.pullback (B ◁ b)).obj B_sub
    let P' := (Subobject.pullback (B ◁ b')).obj B_sub
    let PeqP' : P = P' := by
      unfold P P'
      rw[pullback_diag_eq_singleton hPB b, eq, ← pullback_diag_eq_singleton hPB b']
    let iso : X ≅ Subobject.underlying.obj P :=
      IsPullback.isoIsPullback_congr
        (Subobject.underlyingIso (cmdiag B)).symm (Iso.refl _) (Iso.refl _)
        (by simpa using Subobject.underlyingIso_hom_comp_eq_mk (cmdiag B)) (by simp)
        (pullback_of_diag b) (Subobject.isPullback (B ◁ b) B_sub)
    let eq₁ : (lift b (𝟙 X)) = iso.hom ≫ P.arrow := by unfold P iso; simp
    let eq₂ := Eq.symm (Subobject.arrow_congr P P' PeqP')
    let eq₃ := Eq.symm (Subobject.isPullback (B ◁ b') B_sub).w
    let eq₄ := Eq.symm (Subobject.underlyingIso_hom_comp_eq_mk (cmdiag B))
    have : (lift b b') = _ ≫ cmdiag B := by
      calc
        _ = (lift b (𝟙 X)) ≫ B ◁ b' := by simp
        _ = _ ≫ cmdiag B := by rw[eq₁, assoc, eq₂, assoc, eq₃, assoc, eq₄, ← assoc, ← assoc]
    eq_of_lift_through_diag this ⟩

end PowerObject
