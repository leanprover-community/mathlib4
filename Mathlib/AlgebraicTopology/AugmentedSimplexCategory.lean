/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Tactic.Linarith
import Mathlib.CategoryTheory.Skeletal
import Mathlib.Data.Fin.Interval
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Category.FinLinOrd
import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.AlgebraicTopology.SimplexCategory
/-! # The augmented simplex category

We construct a skeletal model of the augmented simplex category, with objects `ℕ` and the
morphism `n ⟶ m` being the monotone maps from `Fin n` to `Fin m`.

We show that this category is equivalent to `FinLinOrd`.


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

noncomputable instance  : IsInitial [0]ₐ := by
  have h : ReflectsColimit (Functor.empty AugmentedSimplexCategory) skeletalFunctor:=
   CreatesColimit.toReflectsColimit
  apply h.reflects
  exact
    isColimitChangeEmptyCocone FinLinOrd (IsInitial.ofUnique (FinLinOrd.of (Fin 0)))
    (skeletalFunctor.mapCocone (asEmptyCocone [0]ₐ)) (eqToIso (by rfl))
lemma zero_isInitial : IsInitial [0]ₐ := by
  exact instIsInitialAugmentedSimplexCategorySmallCategoryMkOfNatNatInstOfNatNat

lemma len_zero_isInitial {Z: AugmentedSimplexCategory} (hZ : Z.len=0):
 IsInitial Z:= by
   have h : Z= [0]ₐ := by
    ext
    exact hZ
   rw  [h]
   exact instIsInitialAugmentedSimplexCategorySmallCategoryMkOfNatNatInstOfNatNat





def map_from_initial (n: ℕ ): [0]ₐ ⟶  [n]ₐ :=(@OrderEmbedding.ofIsEmpty (Fin 0) (Fin n)).toOrderHom

section InitialSegements

def InitialSeg' {n:ℕ} (i : Fin (n+1)) : Fin (i.val) →o Fin (n):=
 OrderHom.comp (@Fin.castIso (i.val+(n-i.val)) n (add_tsub_cancel_of_le  (Fin.is_le i) ))
 (@Fin.castAddEmb i.val (n-i.val)).toOrderHom


def InitialSeg_comp' {n:ℕ} (i : Fin (n+1)) : Fin (n-i.val) →o Fin (n):=
OrderHom.comp (@Fin.castIso ((n-i.val)+i.val) n (tsub_add_cancel_of_le (Fin.is_le i)))
   (@Fin.addNatEmb (n-i.val) i.val).toOrderHom

def InitialSeg {n:ℕ} (i : Fin (n+1)) : [i.val]ₐ ⟶  [n]ₐ := InitialSeg' i

def InitialSeg_comp {n:ℕ} (i : Fin (n+1)) : [n-i.val]ₐ ⟶ [n]ₐ  := InitialSeg_comp' i

def preimage {m n : ℕ} (f : [m]ₐ ⟶ [n]ₐ) (i: Fin (n+1)) : Fin (m+1) :=
  ⟨ Finset.card  (Set.toFinset {a | (f.toOrderHom a).val < i.val}),by {
    rw [Nat.lt_succ]
    exact card_finset_fin_le _
  } ⟩

end InitialSegements

end AugmentedSimplexCategory

def simplexCategoryToAugmentedSimplexCategory : SimplexCategory ⥤ AugmentedSimplexCategory where
  obj X := (X.len+1)
  map f :=  f.toOrderHom
