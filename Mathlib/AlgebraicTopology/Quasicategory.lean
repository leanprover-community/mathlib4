/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import Mathlib.AlgebraicTopology.KanComplex
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Closed.FunctorToTypes
import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# Quasicategories

In this file we define quasicategories,
a common model of infinity categories.
We show that every Kan complex is a quasicategory.

In `Mathlib/AlgebraicTopology/Nerve.lean`
we show (TODO) that the nerve of a category is a quasicategory.

## TODO

- Generalize the definition to higher universes.
  See the corresponding TODO in `Mathlib/AlgebraicTopology/KanComplex.lean`.

-/

namespace SSet

open CategoryTheory Simplicial

/-- A simplicial set `S` is a *quasicategory* if it satisfies the following horn-filling condition:
for every `n : ℕ` and `0 < i < n`,
every map of simplicial sets `σ₀ : Λ[n, i] → S` can be extended to a map `σ : Δ[n] → S`.

[Kerodon, 003A] -/
class Quasicategory (S : SSet) : Prop where
  hornFilling' : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (σ₀ : Λ[n+2, i] ⟶ S)
    (_h0 : 0 < i) (_hn : i < Fin.last (n+2)),
      ∃ σ : Δ[n+2] ⟶ S, σ₀ = hornInclusion (n+2) i ≫ σ

lemma Quasicategory.hornFilling {S : SSet} [Quasicategory S] ⦃n : ℕ⦄ ⦃i : Fin (n+1)⦄
    (h0 : 0 < i) (hn : i < Fin.last n)
    (σ₀ : Λ[n, i] ⟶ S) : ∃ σ : Δ[n] ⟶ S, σ₀ = hornInclusion n i ≫ σ := by
  cases n using Nat.casesAuxOn with
  | zero => simp [Fin.lt_iff_val_lt_val] at hn
  | succ n =>
  cases n using Nat.casesAuxOn with
  | zero =>
    simp only [Fin.lt_iff_val_lt_val, Fin.val_zero, Fin.val_last, zero_add, Nat.lt_one_iff] at h0 hn
    simp [hn] at h0
  | succ n => exact Quasicategory.hornFilling' σ₀ h0 hn

/-- Every Kan complex is a quasicategory.

[Kerodon, 003C] -/
instance (S : SSet) [KanComplex S] : Quasicategory S where
  hornFilling' _ _ σ₀ _ _ := KanComplex.hornFilling σ₀

lemma quasicategory_of_filler (S : SSet)
    (filler : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (σ₀ : Λ[n+2, i] ⟶ S)
      (_h0 : 0 < i) (_hn : i < Fin.last (n+2)),
      ∃ σ : S _[n+2], ∀ (j) (h : j ≠ i), S.δ j σ = σ₀.app _ (horn.face i j h)) :
    Quasicategory S where
  hornFilling' n i σ₀ h₀ hₙ := by
    obtain ⟨σ, h⟩ := filler σ₀ h₀ hₙ
    refine ⟨(S.yonedaEquiv _).symm σ, ?_⟩
    apply horn.hom_ext
    intro j hj
    rw [← h j hj, NatTrans.comp_app]
    rfl

section

instance : MonoidalClosed SSet := FunctorToTypes.monoidalClosed

/- p : X ⟶ Y is a trivial Kan fibration if it has the right lifting property wrt
  every boundary inclusion  ∂Δ[n] ⟶ Δ[n] -/
class trivialKanFibration {X Y : SSet} (p : X ⟶ Y) where
  has_rlp (n : ℕ) : HasLiftingProperty (boundaryInclusion n) p

/- equivalent definition of trivial Kan fibration by 006Y -/
class rlp_mono {X Y : SSet} (p : X ⟶ Y) where
  has_rlp {A B : SSet} (i : A ⟶ B) [Mono i] : HasLiftingProperty i p

/- RLP wrt all monomorphisms implies trivial Kan fib -/
instance tkf_of_rlp_mono {X Y : SSet} (p : X ⟶ Y) [rlp_mono p] :
    trivialKanFibration p := sorry

/- trivial Kan fib implies RLP wrt all monomorphisms -/
instance rlp_mono_of_tkf {X Y : SSet} (p : X ⟶ Y) [trivialKanFibration p] :
    rlp_mono p := sorry

open MonoidalCategory

section

open MonoidalClosed

noncomputable
abbrev Fun : SSetᵒᵖ ⥤ SSet ⥤ SSet := MonoidalClosed.internalHom

open SSet standardSimplex in
def ihom_simplices (X Y : SSet) (n : ℕ) : (ihom X).obj Y _[n] ≅ Δ[n] ⊗ X ⟶ Y where
  hom a := {
    app := fun k ⟨d, x⟩ ↦ a.app k (objEquiv _ _ d).op x
    naturality := fun m l f ↦ by
      ext ⟨d, x⟩
      exact congr_fun (a.naturality f (objEquiv _ _ d).op) x
  }
  inv a := {
    app := fun k d x ↦ a.app k ((objEquiv _ _).symm d.unop, x)
    naturality := fun f d ↦ by
      ext x
      exact congr_fun (a.naturality f) ((objEquiv _ _).symm d.unop, x)
  }

/-
noncomputable
def ihom_equiv'_aux (X Y Z : SSet) (n : ℕ) (f : Δ[n] ⊗ X ⟶ (ihom Y).obj Z) :
    Δ[n] ⊗ Y ⟶ (ihom X).obj Z :=
  curry ((α_ X Δ[n] Y).inv ≫ (β_ X Δ[n]).hom ▷ Y ≫ (β_ (Δ[n] ⊗ X) Y).hom ≫ (uncurry f))

noncomputable
def ihom_equiv' (X Y Z : SSet) (n : ℕ) :
    (Δ[n] ⊗ X ⟶ (ihom Y).obj Z) ≅ (Δ[n] ⊗ Y ⟶ (ihom X).obj Z) where
  hom f := ihom_equiv'_aux X Y Z n f
  inv f := ihom_equiv'_aux Y X Z n f
  hom_inv_id := by
    ext f m ⟨d, Xm⟩
    sorry
  inv_hom_id := sorry
-/

noncomputable
def temp1 (X Y Z : SSet) : (ihom X).obj ((ihom Y).obj Z) ⟶ (ihom (X ⊗ Y)).obj Z where
  app := fun n x ↦ by
    refine ⟨?_, ?_⟩
    · rintro m f ⟨Xm, Ym⟩
      exact (x.app m f Xm).app m (𝟙 m) Ym
    · intro m l f g
      ext ⟨Xm, Ym⟩
      change
        (x.app l (g ≫ f) (X.map f Xm)).app l (𝟙 l) (Y.map f Ym) = Z.map f ((x.app m g Xm).app m (𝟙 m) Ym)
      have := (congr_fun (x.naturality f g) Xm)
      simp at this
      rw [this]
      simp [ihom, Closed.rightAdj, FunctorToTypes.rightAdj, Functor.ihom, Functor.hom₂Functor]
      have := congr_fun ((x.app m g Xm).naturality f (𝟙 m)) Ym
      simp at this
      aesop

noncomputable
def temp2 (X Y Z : SSet) : (ihom (X ⊗ Y)).obj Z ⟶ (ihom X).obj ((ihom Y).obj Z) where
  app := fun n x ↦ by
    refine ⟨?_, ?_⟩
    · intro m f Xm
      refine ⟨?_, ?_⟩
      · intro l g Yl
        exact x.app l (f ≫ g) (X.map g Xm, Yl)
      · intro l k g h
        ext Yl
        simp
        have := congr_fun (x.naturality g (f ≫ h)) (X.map h Xm, Yl)
        simp at this
        rw [← this]
        aesop
    · intro m l f g
      ext Xm
      simp [ihom, Closed.rightAdj, FunctorToTypes.rightAdj, Functor.ihom, Functor.hom₂Functor]

variable (X Y Z : SSet) (n : SimplexCategoryᵒᵖ)

noncomputable
def temp (X Y Z : SSet) : (ihom X).obj ((ihom Y).obj Z) ≅ (ihom (X ⊗ Y)).obj Z where
  hom := temp1 X Y Z
  inv := temp2 X Y Z
  hom_inv_id := by
    ext n x
    change (X.temp2 Y Z).app n ((X.temp1 Y Z).app n x) = _
    simp [temp1, temp2]
    sorry
  inv_hom_id := sorry

noncomputable
def ihom_equiv (X Y Z : SSet) : (ihom X).obj ((ihom Y).obj Z) ≅ (ihom Y).obj ((ihom X).obj Z) where
  hom := (temp X Y Z).hom ≫ (pre (β_ X Y).inv).app Z ≫ (temp Y X Z).inv
  inv := (temp Y X Z).hom ≫ (pre (β_ X Y).hom).app Z ≫ (temp X Y Z).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

end

-- `0079`
/- if B is a quasicat, then Fun(Δ[2], B) ⟶ Fun(Λ[2, 1], B) is a trivial Kan fib -/
instance horn_tkf_of_quasicat (B : SSet) [Quasicategory B] :
    trivialKanFibration ((Fun.map (hornInclusion 2 1).op).app B) := sorry

-- `0079`
/- if Fun(Δ[2], B) ⟶ Fun(Λ[2, 1], B) is a trivial Kan fib, then B is a quasicat -/
instance quasicat_of_horn_tkf (B : SSet)
    [trivialKanFibration ((Fun.map (hornInclusion 2 1).op).app B)] :
    Quasicategory B := sorry

instance (B : SSet) (n : ℕ) : Mono ((boundaryInclusion n) ▷ B) where
  right_cancellation := sorry

/- changing the square to apply the lifting property of p
   on the monomorphism `(boundaryInclusion n ▷ B)` -/
lemma induced_tkf_aux (B X Y : SSet) (p : X ⟶ Y)
    [trivialKanFibration p] (n : ℕ) [h : HasLiftingProperty (boundaryInclusion n ▷ B) p] :
    HasLiftingProperty (boundaryInclusion n) ((Fun.obj (Opposite.op B)).map p) where
  sq_hasLift := by
    intro f g sq
    dsimp at f g sq
    have w := sq.w
    have map := (yonedaEquiv ((ihom B).obj Y) [n]).trans (ihom_simplices B Y n).toEquiv
    have g' := map g
    have δ := (boundaryInclusion n ▷ B)
    have := δ ≫ g'
    sorry

-- `0071` (special case of `0070`)
/- if p : X ⟶ Y is a trivial Kan fib, then Fun(B,X) ⟶ Fun(B, Y) is -/
noncomputable
instance induced_tkf (B X Y : SSet) (p : X ⟶ Y) [trivialKanFibration p] :
    trivialKanFibration ((Fun.obj (.op B)).map p) where
  has_rlp n := by
    have := (rlp_mono_of_tkf p).has_rlp ((boundaryInclusion n) ▷ B)
    apply induced_tkf_aux

-- uses `0071` and `0079`
/- the map Fun(Δ[2], Fun(S, D)) ⟶ Fun(Λ[2,1], Fun(S, D)) is a trivial Kan fib -/
-- apply `ihom_equiv` and `0079`
open MonoidalClosed in
noncomputable
instance fun_quasicat_aux (S D : SSet) [Quasicategory D] :
    trivialKanFibration ((Fun.map (hornInclusion 2 1).op).app ((Fun.obj (.op S)).obj D)) where
  has_rlp n := by
    -- since Fun[Δ[n], D] ⟶ Fun[Λ[2,1], D] is a TKF by `0079`,
    -- get Fun(S, Fun(Δ[n], D)) ⟶ Fun(S, (Λ[2,1], D)) is a TKF by `0071`
    have := (induced_tkf S _ _ ((Fun.map (hornInclusion 2 1).op).app D)).has_rlp n
    dsimp at this
    have H : Arrow.mk ((ihom S).map ((MonoidalClosed.pre (hornInclusion 2 1)).app D)) ≅
        Arrow.mk ((Fun.map (hornInclusion 2 1).op).app ((Fun.obj (Opposite.op S)).obj D)) :=
      CategoryTheory.Comma.isoMk (ihom_equiv _ _ _) (ihom_equiv _ _ _)
    exact HasLiftingProperty.of_arrow_iso_right (boundaryInclusion n) H

-- `0066`
/- if D is a quasicat, then Fun(S, D) is -/
instance fun_quasicat (S D : SSet) [Quasicategory D] : Quasicategory ((Fun.obj (.op S)).obj D) :=
  quasicat_of_horn_tkf ((Fun.obj (.op S)).obj D) -- instance inferred by `fun_quasicat_aux`

end

end SSet
