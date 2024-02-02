/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.AlgebraicTopology.SimplexCategory
import Mathlib.Tactic.Linarith
import Mathlib.CategoryTheory.Skeletal
import Mathlib.Data.Fin.Interval
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Category.FinLinOrd
import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial

/-! # The augmented simplex category

We construct a skeletal model of the augmented simplex category, with objects `ℕ` and the
morphism `n ⟶ m` being the monotone maps from `Fin n` to `Fin m`.

We show the following:
* This category is equivalent to `FinLinOrd`.
* This category has a strict initial object given by `0`.

We define the following:
* The obvious functor of `SimplexCategory` into `AugmentedSimplexCategory`.
* The preimage of the above functor.
-/


universe v u

open CategoryTheory CategoryTheory.Limits

/-- The augmented simplex category:
* objects are natural numbers `n : ℕ`
* morphisms from `n` to `m` are monotone functions `Fin n → Fin m`
-/
def AugmentedSimplexCategory :=
  ℕ

namespace AugmentedSimplexCategory

/-- Interpret a natural number as an object of the augmented simplex category. -/
def mk (n : ℕ) : AugmentedSimplexCategory :=
  n


/-- The length of an object of `AugmentedSimplexCategory`. -/
def len (n : AugmentedSimplexCategory) : ℕ :=
  n

/-- the `n`-dimensional augmented simplex can be denoted `[n]ₐ` -/
 notation "[" n "]ₐ" => AugmentedSimplexCategory.mk n

@[ext]
theorem ext (a b : AugmentedSimplexCategory) : a.len = b.len → a = b :=
  id


/-- Morphisms in the `AugmentedSimplexCategory`. -/
protected def Hom (a b : AugmentedSimplexCategory) :=
  Fin a.len  →o Fin b.len

namespace Hom

/-- Make a morphism in `AugmentedSimplexCategory` from a monotone map of `Fin`'s. -/
def mk {a b : AugmentedSimplexCategory} (f : Fin a.len  →o Fin b.len ):
    AugmentedSimplexCategory.Hom a b :=
  f
/-- Recover the monotone map from a morphism in the augmented simplex category. -/
def toOrderHom {a b : AugmentedSimplexCategory} (f : AugmentedSimplexCategory.Hom a b) :
    Fin a.len →o Fin b.len  :=
  f

theorem ext' {a b : AugmentedSimplexCategory} (f g : AugmentedSimplexCategory.Hom a b) :
    f.toOrderHom = g.toOrderHom → f = g :=
  id

/-- Identity morphisms of `AugmentedSimplexCategory`. -/
@[simp]
def id (a : AugmentedSimplexCategory) : AugmentedSimplexCategory.Hom a a :=
  mk OrderHom.id

/-- Composition of morphisms of `AugmentedSimplexCategory`. -/
@[simp]
def comp {a b c : AugmentedSimplexCategory} (f : AugmentedSimplexCategory.Hom b c)
    (g : AugmentedSimplexCategory.Hom a b) :
    AugmentedSimplexCategory.Hom a c :=
  mk <| f.toOrderHom.comp g.toOrderHom

end Hom

@[simps]
instance smallCategory : SmallCategory.{0} AugmentedSimplexCategory where
  Hom n m := AugmentedSimplexCategory.Hom n m
  id m := AugmentedSimplexCategory.Hom.id _
  comp f g := AugmentedSimplexCategory.Hom.comp g f

@[ext]
theorem Hom.ext {a b : AugmentedSimplexCategory} (f g : a ⟶ b) :
    f.toOrderHom = g.toOrderHom → f = g :=
  Hom.ext' _ _
section Skeleton
/-- The functor that exhibits `AugmentedSimplexCategory` as skeleton
of `FinLinOrd` -/
@[simps obj map]
def skeletalFunctor : AugmentedSimplexCategory ⥤ FinLinOrd where
  obj a := FinLinOrd.of (Fin a.len)
  map f := f.toOrderHom

theorem skeletalFunctor.coe_map {Δ₁ Δ₂ : AugmentedSimplexCategory} (f : Δ₁ ⟶ Δ₂) :
    ↑(skeletalFunctor.map f) = f.toOrderHom :=
  rfl

theorem skeletal : Skeletal AugmentedSimplexCategory := fun X Y ⟨I⟩ => by
  suffices Fintype.card (Fin X.len) = Fintype.card (Fin Y.len) by
    ext
    simpa
  apply Fintype.card_congr
  exact ((skeletalFunctor ⋙ forget FinLinOrd).mapIso I).toEquiv

namespace SkeletalFunctor

instance : Full skeletalFunctor where
  preimage f := AugmentedSimplexCategory.Hom.mk f

instance : Faithful skeletalFunctor where
  map_injective {_ _ f g} h := by
    ext1
    exact h

instance : EssSurj skeletalFunctor where
  mem_essImage X :=
    ⟨mk (Fintype.card X : ℕ),
      ⟨by
        let f :Fin (Fintype.card X) ≃o X:= monoEquivOfFin X (by rfl)
        exact
          { hom := ⟨f, OrderIso.monotone f⟩
            inv := ⟨f.symm, OrderIso.monotone (f.symm)⟩
            hom_inv_id := by ext1; apply f.symm_apply_apply
            inv_hom_id := by ext1; apply f.apply_symm_apply }
      ⟩⟩
noncomputable instance isEquivalence : IsEquivalence skeletalFunctor :=
  Equivalence.ofFullyFaithfullyEssSurj skeletalFunctor

end SkeletalFunctor
/-- The equivalence that exhibits `AugmentedSimplexCategory` as skeleton
of `FinLinOrd` -/
noncomputable def skeletalEquivalence : AugmentedSimplexCategory ≌ FinLinOrd :=
  Functor.asEquivalence skeletalFunctor

end Skeleton


noncomputable def zeroIsInitial : IsInitial [0]ₐ := CreatesColimit.toReflectsColimit.reflects
    (isColimitChangeEmptyCocone FinLinOrd (IsInitial.ofUnique (FinLinOrd.of (Fin 0)))
    (skeletalFunctor.mapCocone (asEmptyCocone [0]ₐ)) (eqToIso (by rfl)))

noncomputable def lenZeroIsInitial {Z: AugmentedSimplexCategory} (hZ : Z.len=0):
    IsInitial Z:= by
   rw  [show Z = [0]ₐ from hZ]
   exact zeroIsInitial

/-- An isomorphism in `AugmentedSimplexCategory` induces an `OrderIso`. -/
@[simp]
def orderIsoOfIso {x y : AugmentedSimplexCategory} (e : x ≅ y) : Fin x.len ≃o Fin y.len :=
  Equiv.toOrderIso
    { toFun := e.hom.toOrderHom
      invFun := e.inv.toOrderHom
      left_inv := fun i => by
        simpa only using congr_arg (fun φ => (Hom.toOrderHom φ) i) e.hom_inv_id
      right_inv := fun i => by
        simpa only using congr_arg (fun φ => (Hom.toOrderHom φ) i) e.inv_hom_id }
    e.hom.toOrderHom.monotone e.inv.toOrderHom.monotone

open Finset in
lemma iso_len {X Y : AugmentedSimplexCategory} ( f: X⟶ Y ) [IsIso f]: X.len =Y.len := by
    rw [← card_fin X.len,← card_fin Y.len,← card_image_of_injOn (Set.injOn_of_injective
    (Equiv.injective ((orderIsoOfIso (asIso f)).toEquiv)) (univ :Finset (Fin (X.len)))),
      congrArg card (image_univ_equiv ((orderIsoOfIso (asIso f)).toEquiv))]


lemma isInitial_len_zero {Z: AugmentedSimplexCategory}  (h : IsInitial Z) :Z.len = 0 := by
  refine iso_len (?_ : Z ≅ [0]ₐ).hom
  apply IsInitial.uniqueUpToIso h zeroIsInitial


lemma strict_initial' {Y Z: AugmentedSimplexCategory} (f: Z ⟶ Y) (hZ : Z.len≠ 0): Y.len≠ 0:= by
      by_contra  hYn
      let f':= f.toOrderHom
      rw [hYn] at f'
      exact ((fun a ↦ IsEmpty.false a) ∘ f') (⟨ 0 ,Nat.pos_of_ne_zero hZ⟩:Fin (Z.len) )

lemma map_into_initial_eq {Z I : AugmentedSimplexCategory} (h:IsInitial I) (f : Z ⟶ I) : Z=I := by
  by_cases hZ: Z.len=0
  · ext
    rw [hZ, isInitial_len_zero h]
  · exact ((strict_initial' f hZ) (isInitial_len_zero h)).elim

lemma map_into_initial_eqToHom {Z I : AugmentedSimplexCategory} (h : IsInitial I) (f : Z ⟶ I) :
    f = eqToHom (map_into_initial_eq h f):= by
    refine IsInitial.hom_ext ?_ f (eqToHom (map_into_initial_eq h f))
    rw [map_into_initial_eq h f]
    exact h

instance : HasStrictInitialObjects AugmentedSimplexCategory := by
  fconstructor
  intro I A f hIf
  rw [map_into_initial_eqToHom hIf f]
  exact instIsIsoEqToHom (map_into_initial_eq hIf f)

/--The unique morphism from `[0]ₐ` to `[n]ₐ`-/
def map_from_initial (n: ℕ ): [0]ₐ ⟶  [n]ₐ :=(@OrderEmbedding.ofIsEmpty (Fin 0) (Fin n)).toOrderHom


section InitialSegements

/--The morphism from `[i]ₐ` into `[n]ₐ` with `i≤n` embedding into the first i-factors.-/
def InitialSeg {n:ℕ} (i : Fin (n+1)) : [i.val]ₐ ⟶  [n]ₐ :=
  Hom.mk (Fin.castAddEmb (n-i.val)).toOrderHom ≫ eqToHom (add_tsub_cancel_of_le  (Fin.is_le i))

/--The morphism from `[n-i]ₐ` into `[n]ₐ` with `i≤n` embedding into the last (n-i)-factors.-/
def InitialSegComp {n:ℕ} (i : Fin (n+1)) : [n-i.val]ₐ ⟶ [n]ₐ  :=
 Hom.mk (Fin.addNatEmb i.val).toOrderHom ≫ eqToHom (tsub_add_cancel_of_le  (Fin.is_le i))

/--Given a morphism `f : [m]ₐ ⟶ [n]ₐ` and a `i<n`, the `j≤m` such that `∀ a< j, f a < i`
and `∀ a≥j, f a ≥ i`.-/
def preimage {m n : ℕ} (f : [m]ₐ ⟶ [n]ₐ) (i: Fin (n+1)) : Fin (m+1) :=
  ⟨ Finset.card  (Set.toFinset {a | (f.toOrderHom a).val < i.val}),by {
    rw [Nat.lt_succ]
    exact card_finset_fin_le _
  } ⟩

end InitialSegements
end AugmentedSimplexCategory
/--The functor including the simplex category into the augmented simplex category.-/
def SimplexCategory.augment : SimplexCategory ⥤ AugmentedSimplexCategory where
  obj X := (X.len+1)
  map f :=  f.toOrderHom

lemma SimplexCategory.augment_len (Z : SimplexCategory ):
    (SimplexCategory.augment.obj  Z).len ≠  0 := by
      unfold  SimplexCategory.augment
      exact Nat.succ_ne_zero (SimplexCategory.len Z)

namespace AugmentedSimplexCategory
/--Given a `Z ∈ AugmentedSimplexCategory` with `Z.len>0` the object in `SimplexCategory` which maps
 to  `Z` under `SimplexCategory.augment`.-/
def unaugment.obj (Z : AugmentedSimplexCategory)  : SimplexCategory :=
   SimplexCategory.mk (Z.len-1)

lemma unaugment_augment_obj {Z : AugmentedSimplexCategory} (hZ: Z.len ≠ 0) :
    SimplexCategory.augment.obj (unaugment.obj Z) = Z:= by
      unfold SimplexCategory.augment
      dsimp
      apply AugmentedSimplexCategory.ext
      exact Nat.succ_pred hZ

namespace unaugment
/--Given a `f: Z ⟶ Y ∈ Mor AugmentedSimplexCategory` with `Z.len>0`
the morphism in `SimplexCategory` which maps to  `f` under `SimplexCategory.augment`.-/
def map {Y Z: AugmentedSimplexCategory} (f: Z ⟶ Y) (hZ :Z.len≠ 0) : (obj Z) ⟶ (obj Y) :=
 SimplexCategory.Hom.mk (eqToHom (unaugment_augment_obj hZ) ≫ f≫
  eqToHom (unaugment_augment_obj (strict_initial' f hZ)).symm )

lemma map_id { Z: AugmentedSimplexCategory}  (hZ :Z.len≠ 0) :
    map (𝟙 Z) hZ = 𝟙 (SimplexCategory.mk (Z.len-1)) := by
       unfold map
       rw [← eqToHom_refl,← eqToHom_refl,eqToHom_trans,eqToHom_trans]
       all_goals rfl

lemma map_comp { Y Z  W: AugmentedSimplexCategory}  (hW :W.len≠ 0) (f: Z ⟶ Y) (g : W ⟶ Z):
    map (g ≫ f) hW = (map g hW) ≫  (map f (strict_initial' g hW))   := by
       nth_rewrite 1 [← Category.comp_id g ]
       rw [← eqToHom_refl,← eqToHom_trans]
       rfl

end unaugment

lemma unaugment_augment_map {X Z : AugmentedSimplexCategory  } (f: Z ⟶ X ) (hZ :Z.len ≠ 0):
    eqToHom (unaugment_augment_obj hZ).symm≫ SimplexCategory.augment.map (unaugment.map f hZ)
    ≫ eqToHom (unaugment_augment_obj (strict_initial' f hZ)) =  f := by
      rw [eqToHom_comp_iff,comp_eqToHom_iff]
      rfl

end AugmentedSimplexCategory

lemma SimplexCategory.augment_unaugment_map {X Z : SimplexCategory  } (f: Z ⟶ X):
    AugmentedSimplexCategory.unaugment.map (SimplexCategory.augment.map f)
  (SimplexCategory.augment_len Z) = f := by
    change _= SimplexCategory.Hom.mk (f.toOrderHom)
    apply congrArg SimplexCategory.Hom.mk
    apply OrderHom.ext
    rfl
