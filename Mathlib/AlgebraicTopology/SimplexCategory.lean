/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz
-/
import Mathlib.Tactic.Linarith
import Mathlib.CategoryTheory.Skeletal
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Category.NonemptyFinLinOrd
import Mathlib.CategoryTheory.Functor.ReflectsIso

#align_import algebraic_topology.simplex_category from "leanprover-community/mathlib"@"e8ac6315bcfcbaf2d19a046719c3b553206dac75"

/-! # The simplex category

We construct a skeletal model of the simplex category, with objects `ℕ` and the
morphism `n ⟶ m` being the monotone maps from `Fin (n+1)` to `Fin (m+1)`.

We show that this category is equivalent to `NonemptyFinLinOrd`.

## Remarks

The definitions `SimplexCategory` and `SimplexCategory.Hom` are marked as irreducible.

We provide the following functions to work with these objects:
1. `SimplexCategory.mk` creates an object of `SimplexCategory` out of a natural number.
  Use the notation `[n]` in the `Simplicial` locale.
2. `SimplexCategory.len` gives the "length" of an object of `SimplexCategory`, as a natural.
3. `SimplexCategory.Hom.mk` makes a morphism out of a monotone map between `Fin`'s.
4. `SimplexCategory.Hom.toOrderHom` gives the underlying monotone map associated to a
  term of `SimplexCategory.Hom`.

-/


universe v

open CategoryTheory CategoryTheory.Limits

/-- The simplex category:
* objects are natural numbers `n : ℕ`
* morphisms from `n` to `m` are monotone functions `Fin (n+1) → Fin (m+1)`
-/
def SimplexCategory :=
  ℕ

namespace SimplexCategory

section


-- porting note: the definition of `SimplexCategory` is made irreducible below
/-- Interpret a natural number as an object of the simplex category. -/
def mk (n : ℕ) : SimplexCategory :=
  n

/-- the `n`-dimensional simplex can be denoted `[n]` -/
scoped[Simplicial] notation "[" n "]" => SimplexCategory.mk n

-- TODO: Make `len` irreducible.
/-- The length of an object of `SimplexCategory`. -/
def len (n : SimplexCategory) : ℕ :=
  n

@[ext]
theorem ext (a b : SimplexCategory) : a.len = b.len → a = b :=
  id

attribute [irreducible] SimplexCategory

open Simplicial

@[simp]
theorem len_mk (n : ℕ) : [n].len = n :=
  rfl

@[simp]
theorem mk_len (n : SimplexCategory) : ([n.len] : SimplexCategory) = n :=
  rfl

/-- A recursor for `SimplexCategory`. Use it as `induction Δ using SimplexCategory.rec`. -/
protected def rec {F : ∀ _ : SimplexCategory, Sort*} (h : ∀ n : ℕ, F [n]) : ∀ X, F X := fun n =>
  h n.len

-- porting note: removed @[nolint has_nonempty_instance]
/-- Morphisms in the `SimplexCategory`. -/
protected def Hom (a b : SimplexCategory) :=
  Fin (a.len + 1) →o Fin (b.len + 1)

namespace Hom

/-- Make a moprhism in `SimplexCategory` from a monotone map of `Fin`'s. -/
def mk {a b : SimplexCategory} (f : Fin (a.len + 1) →o Fin (b.len + 1)) : SimplexCategory.Hom a b :=
  f

/-- Recover the monotone map from a morphism in the simplex category. -/
def toOrderHom {a b : SimplexCategory} (f : SimplexCategory.Hom a b) :
    Fin (a.len + 1) →o Fin (b.len + 1) :=
  f

theorem ext' {a b : SimplexCategory} (f g : SimplexCategory.Hom a b) :
    f.toOrderHom = g.toOrderHom → f = g :=
  id

attribute [irreducible] SimplexCategory.Hom

@[simp]
theorem mk_toOrderHom {a b : SimplexCategory} (f : SimplexCategory.Hom a b) : mk f.toOrderHom = f :=
  rfl

@[simp]
theorem toOrderHom_mk {a b : SimplexCategory} (f : Fin (a.len + 1) →o Fin (b.len + 1)) :
    (mk f).toOrderHom = f :=
  rfl

theorem mk_toOrderHom_apply {a b : SimplexCategory} (f : Fin (a.len + 1) →o Fin (b.len + 1))
    (i : Fin (a.len + 1)) : (mk f).toOrderHom i = f i :=
  rfl

/-- Identity morphisms of `SimplexCategory`. -/
@[simp]
def id (a : SimplexCategory) : SimplexCategory.Hom a a :=
  mk OrderHom.id

/-- Composition of morphisms of `SimplexCategory`. -/
@[simp]
def comp {a b c : SimplexCategory} (f : SimplexCategory.Hom b c) (g : SimplexCategory.Hom a b) :
    SimplexCategory.Hom a c :=
  mk <| f.toOrderHom.comp g.toOrderHom

end Hom

@[simps]
instance smallCategory : SmallCategory.{0} SimplexCategory where
  Hom n m := SimplexCategory.Hom n m
  id m := SimplexCategory.Hom.id _
  comp f g := SimplexCategory.Hom.comp g f

-- porting note: added because `Hom.ext'` is not triggered automatically
@[ext]
theorem Hom.ext {a b : SimplexCategory} (f g : a ⟶ b) :
    f.toOrderHom = g.toOrderHom → f = g :=
  Hom.ext' _ _

/-- The constant morphism from [0]. -/
def const (x : SimplexCategory) (i : Fin (x.len + 1)) : ([0] : SimplexCategory) ⟶ x :=
  Hom.mk <| ⟨fun _ => i, by tauto⟩

-- porting note: removed @[simp] as the linter complains
theorem const_comp (x y : SimplexCategory) (i : Fin (x.len + 1)) (f : x ⟶ y) :
    const x i ≫ f = const y (f.toOrderHom i) :=
  rfl

/-- Make a morphism `[n] ⟶ [m]` from a monotone map between fin's.
This is useful for constructing morphisms between `[n]` directly
without identifying `n` with `[n].len`.
-/
@[simp]
def mkHom {n m : ℕ} (f : Fin (n + 1) →o Fin (m + 1)) : ([n] : SimplexCategory) ⟶ [m] :=
  SimplexCategory.Hom.mk f

theorem hom_zero_zero (f : ([0] : SimplexCategory) ⟶ [0]) : f = 𝟙 _ := by
  ext : 3
  apply @Subsingleton.elim (Fin 1)

end

open Simplicial

section Generators

/-!
## Generating maps for the simplex category

TODO: prove that the simplex category is equivalent to
one given by the following generators and relations.
-/


/-- The `i`-th face map from `[n]` to `[n+1]` -/
def δ {n} (i : Fin (n + 2)) : ([n] : SimplexCategory) ⟶ [n + 1] :=
  mkHom (Fin.succAboveEmb i).toOrderHom

/-- The `i`-th degeneracy map from `[n+1]` to `[n]` -/
def σ {n} (i : Fin (n + 1)) : ([n + 1] : SimplexCategory) ⟶ [n] :=
  mkHom
    { toFun := Fin.predAbove i
      monotone' := Fin.predAbove_right_monotone i }

/-- The generic case of the first simplicial identity -/
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    δ i ≫ δ j.succ = δ j ≫ δ (Fin.castSucc i) := by
  ext k
  dsimp [δ, Fin.succAbove]
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  rcases k with ⟨k, _⟩
  split_ifs <;> · simp at * <;> linarith

theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j) :
    δ i ≫ δ j =
      δ (j.pred <| fun (hj : j = 0) => by simp [hj, Fin.not_lt_zero] at H) ≫
        δ (Fin.castSucc i) := by
  rw [← δ_comp_δ]
  · rw [Fin.succ_pred]
  · simpa only [Fin.le_iff_val_le_val, ← Nat.lt_succ_iff, Nat.succ_eq_add_one, ← Fin.val_succ,
      j.succ_pred, Fin.lt_iff_val_lt_val] using H

theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ Fin.castSucc j) :
    δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) ≫ δ j.succ =
      δ j ≫ δ i := by
  rw [δ_comp_δ]
  · rfl
  · exact H

/-- The special case of the first simplicial identity -/
@[reassoc]
theorem δ_comp_δ_self {n} {i : Fin (n + 2)} : δ i ≫ δ (Fin.castSucc i) = δ i ≫ δ i.succ :=
  (δ_comp_δ (le_refl i)).symm

@[reassoc]
theorem δ_comp_δ_self' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : j = Fin.castSucc i) :
    δ i ≫ δ j = δ i ≫ δ i.succ := by
  subst H
  rw [δ_comp_δ_self]

/-- The second simplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ Fin.castSucc j) :
    δ (Fin.castSucc i) ≫ σ j.succ = σ j ≫ δ i := by
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  ext ⟨k, hk⟩
  simp at H hk
  dsimp [σ, δ, Fin.predAbove, Fin.succAbove]
  simp only [Fin.lt_iff_val_lt_val, Fin.dite_val, Fin.ite_val, Fin.coe_pred, ge_iff_le,
    Fin.coe_castLT, dite_eq_ite, Fin.coe_castSucc, Fin.val_succ]
  split_ifs
  all_goals try simp <;> linarith
  all_goals cases k <;> simp at * <;> linarith

/-- The first part of the third simplicial identity -/
@[reassoc]
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} :
    δ (Fin.castSucc i) ≫ σ i = 𝟙 ([n] : SimplexCategory) := by
  rcases i with ⟨i, hi⟩
  ext ⟨j, hj⟩
  simp at hj
  dsimp [σ, δ, Fin.predAbove, Fin.succAbove]
  simp only [Fin.lt_iff_val_lt_val, Fin.dite_val, Fin.ite_val, Fin.coe_pred, ge_iff_le,
    Fin.coe_castLT, dite_eq_ite]
  split_ifs
  any_goals simp
  all_goals linarith

@[reassoc]
theorem δ_comp_σ_self' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = Fin.castSucc i) :
    δ j ≫ σ i = 𝟙 ([n] : SimplexCategory) := by
  subst H
  rw [δ_comp_σ_self]

/-- The second part of the third simplicial identity -/
@[reassoc]
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : δ i.succ ≫ σ i = 𝟙 ([n] : SimplexCategory) := by
  ext j
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  dsimp [δ, σ, Fin.succAbove, Fin.predAbove]
  split_ifs <;> simp <;> simp at * <;> linarith

@[reassoc]
theorem δ_comp_σ_succ' {n} (j : Fin (n + 2)) (i : Fin (n + 1)) (H : j = i.succ) :
    δ j ≫ σ i = 𝟙 ([n] : SimplexCategory) := by
  subst H
  rw [δ_comp_σ_succ]

/-- The fourth simplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i) :
    δ i.succ ≫ σ (Fin.castSucc j) = σ j ≫ δ i := by
  ext ⟨k, hk⟩
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  simp at H hk
  dsimp [δ, σ, Fin.predAbove, Fin.succAbove]
  simp only [Fin.lt_iff_val_lt_val, Fin.dite_val, Fin.ite_val, Fin.coe_pred, ge_iff_le,
    Fin.coe_castLT, dite_eq_ite, Fin.coe_castSucc, Fin.val_succ]
  split_ifs
  all_goals try simp <;> linarith
  all_goals cases k <;> simp at * <;> linarith

@[reassoc]
theorem δ_comp_σ_of_gt' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i) :
    δ i ≫ σ j = σ (j.castLT ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le H i.is_le))) ≫
      δ (i.pred <| fun (hi : i = 0) => by simp only [Fin.not_lt_zero, hi] at H) := by
  rw [← δ_comp_σ_of_gt]
  · simp
  · rw [Fin.castSucc_castLT, ← Fin.succ_lt_succ_iff, Fin.succ_pred]
    exact H

/-- The fifth simplicial identity -/
@[reassoc]
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) :
    σ (Fin.castSucc i) ≫ σ j = σ j.succ ≫ σ i := by
  ext ⟨k, hk⟩
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  simp at H hk
  dsimp [σ, Fin.predAbove]
  simp only [Fin.lt_iff_val_lt_val, Fin.ite_val, Fin.coe_pred, ge_iff_le, dite_eq_ite,
    Fin.coe_castLT]
  split_ifs
  all_goals try linarith
  all_goals cases k <;> simp at *; linarith

end Generators

section Skeleton

/-- The functor that exhibits `SimplexCategory` as skeleton
of `NonemptyFinLinOrd` -/
@[simps obj map]
def skeletalFunctor : SimplexCategory ⥤ NonemptyFinLinOrd where
  obj a := NonemptyFinLinOrd.of (Fin (a.len + 1))
  map f := f.toOrderHom

theorem skeletalFunctor.coe_map {Δ₁ Δ₂ : SimplexCategory} (f : Δ₁ ⟶ Δ₂) :
    ↑(skeletalFunctor.map f) = f.toOrderHom :=
  rfl

theorem skeletal : Skeletal SimplexCategory := fun X Y ⟨I⟩ => by
  suffices Fintype.card (Fin (X.len + 1)) = Fintype.card (Fin (Y.len + 1)) by
    ext
    simpa
  apply Fintype.card_congr
  exact ((skeletalFunctor ⋙ forget NonemptyFinLinOrd).mapIso I).toEquiv

namespace SkeletalFunctor

instance : Full skeletalFunctor where
  preimage f := SimplexCategory.Hom.mk f

instance : Faithful skeletalFunctor where
  map_injective {_ _ f g} h := by
    ext1
    exact h

instance : EssSurj skeletalFunctor where
  mem_essImage X :=
    ⟨mk (Fintype.card X - 1 : ℕ),
      ⟨by
        have aux : Fintype.card X = Fintype.card X - 1 + 1 :=
          (Nat.succ_pred_eq_of_pos <| Fintype.card_pos_iff.mpr ⟨⊥⟩).symm
        let f := monoEquivOfFin X aux
        have hf := (Finset.univ.orderEmbOfFin aux).strictMono
        refine'
          { hom := ⟨f, hf.monotone⟩
            inv := ⟨f.symm, _⟩
            hom_inv_id := by ext1; apply f.symm_apply_apply
            inv_hom_id := by ext1; apply f.apply_symm_apply }
        intro i j h
        show f.symm i ≤ f.symm j
        rw [← hf.le_iff_le]
        show f (f.symm i) ≤ f (f.symm j)
        simpa only [OrderIso.apply_symm_apply]⟩⟩

noncomputable instance isEquivalence : IsEquivalence skeletalFunctor :=
  Equivalence.ofFullyFaithfullyEssSurj skeletalFunctor

end SkeletalFunctor

/-- The equivalence that exhibits `SimplexCategory` as skeleton
of `NonemptyFinLinOrd` -/
noncomputable def skeletalEquivalence : SimplexCategory ≌ NonemptyFinLinOrd :=
  Functor.asEquivalence skeletalFunctor

end Skeleton

/-- `SimplexCategory` is a skeleton of `NonemptyFinLinOrd`.
-/
noncomputable def isSkeletonOf :
    IsSkeletonOf NonemptyFinLinOrd SimplexCategory skeletalFunctor where
  skel := skeletal
  eqv := SkeletalFunctor.isEquivalence

/-- The truncated simplex category. -/
def Truncated (n : ℕ) :=
  FullSubcategory fun a : SimplexCategory => a.len ≤ n

instance (n : ℕ) : SmallCategory.{0} (Truncated n) :=
  FullSubcategory.category _

namespace Truncated

instance {n} : Inhabited (Truncated n) :=
  ⟨⟨[0], by simp⟩⟩

/-- The fully faithful inclusion of the truncated simplex category into the usual
simplex category.
-/
def inclusion {n : ℕ} : SimplexCategory.Truncated n ⥤ SimplexCategory :=
  fullSubcategoryInclusion _

instance (n : ℕ) : Full (inclusion : Truncated n ⥤ _) := FullSubcategory.full _
instance (n : ℕ) : Faithful (inclusion : Truncated n ⥤ _) := FullSubcategory.faithful _

end Truncated

section Concrete

instance : ConcreteCategory.{0} SimplexCategory where
  forget :=
    { obj := fun i => Fin (i.len + 1)
      map := fun f => f.toOrderHom }
  forget_faithful := ⟨fun h => by ext : 2; exact h⟩

end Concrete

section EpiMono

/-- A morphism in `SimplexCategory` is a monomorphism precisely when it is an injective function
-/
theorem mono_iff_injective {n m : SimplexCategory} {f : n ⟶ m} :
    Mono f ↔ Function.Injective f.toOrderHom := by
  rw [← Functor.mono_map_iff_mono skeletalEquivalence.functor]
  dsimp only [skeletalEquivalence, Functor.asEquivalence_functor]
  simp only [skeletalFunctor_obj, skeletalFunctor_map,
    NonemptyFinLinOrd.mono_iff_injective, NonemptyFinLinOrd.coe_of]

/-- A morphism in `SimplexCategory` is an epimorphism if and only if it is a surjective function
-/
theorem epi_iff_surjective {n m : SimplexCategory} {f : n ⟶ m} :
    Epi f ↔ Function.Surjective f.toOrderHom := by
  rw [← Functor.epi_map_iff_epi skeletalEquivalence.functor]
  dsimp only [skeletalEquivalence, Functor.asEquivalence_functor]
  simp only [skeletalFunctor_obj, skeletalFunctor_map,
    NonemptyFinLinOrd.epi_iff_surjective, NonemptyFinLinOrd.coe_of]

/-- A monomorphism in `SimplexCategory` must increase lengths-/
theorem len_le_of_mono {x y : SimplexCategory} {f : x ⟶ y} : Mono f → x.len ≤ y.len := by
  intro hyp_f_mono
  have f_inj : Function.Injective f.toOrderHom.toFun := mono_iff_injective.1 hyp_f_mono
  simpa using Fintype.card_le_of_injective f.toOrderHom.toFun f_inj

theorem le_of_mono {n m : ℕ} {f : ([n] : SimplexCategory) ⟶ [m]} : CategoryTheory.Mono f → n ≤ m :=
  len_le_of_mono

/-- An epimorphism in `SimplexCategory` must decrease lengths-/
theorem len_le_of_epi {x y : SimplexCategory} {f : x ⟶ y} : Epi f → y.len ≤ x.len := by
  intro hyp_f_epi
  have f_surj : Function.Surjective f.toOrderHom.toFun := epi_iff_surjective.1 hyp_f_epi
  simpa using Fintype.card_le_of_surjective f.toOrderHom.toFun f_surj

theorem le_of_epi {n m : ℕ} {f : ([n] : SimplexCategory) ⟶ [m]} : Epi f → m ≤ n :=
  len_le_of_epi

instance {n : ℕ} {i : Fin (n + 2)} : Mono (δ i) := by
  rw [mono_iff_injective]
  exact Fin.succAbove_right_injective

instance {n : ℕ} {i : Fin (n + 1)} : Epi (σ i) := by
  rw [epi_iff_surjective]
  intro b
  simp only [σ, mkHom, Hom.toOrderHom_mk, OrderHom.coe_mk]
  by_cases b ≤ i
  · use b
    -- This was not needed before leanprover/lean4#2644
    dsimp
    rw [Fin.predAbove_below i b (by simpa only [Fin.coe_eq_castSucc] using h)]
    simp only [len_mk, Fin.coe_eq_castSucc, Fin.castPred_castSucc]
  · use b.succ
    -- This was not needed before leanprover/lean4#2644
    dsimp
    rw [Fin.predAbove_above i b.succ _, Fin.pred_succ]
    rw [not_le] at h
    rw [Fin.lt_iff_val_lt_val] at h ⊢
    simpa only [Fin.val_succ, Fin.coe_castSucc] using Nat.lt.step h

instance : ReflectsIsomorphisms (forget SimplexCategory) :=
  ⟨fun f hf =>
    IsIso.of_iso
      { hom := f
        inv := Hom.mk
            { toFun := inv ((forget SimplexCategory).map f)
              monotone' := fun y₁ y₂ h => by
                by_cases h' : y₁ < y₂
                · by_contra h''
                  apply not_le.mpr h'
                  convert f.toOrderHom.monotone (le_of_not_ge h'')
                  all_goals
                    exact (congr_hom (Iso.inv_hom_id
                      (asIso ((forget SimplexCategory).map f))) _).symm
                · rw [eq_of_le_of_not_lt h h'] }
        hom_inv_id := by
          ext1
          ext1
          exact Iso.hom_inv_id (asIso ((forget _).map f))
        inv_hom_id := by
          ext1
          ext1
          exact Iso.inv_hom_id (asIso ((forget _).map f)) }⟩

theorem isIso_of_bijective {x y : SimplexCategory} {f : x ⟶ y}
    (hf : Function.Bijective f.toOrderHom.toFun) : IsIso f :=
  haveI : IsIso ((forget SimplexCategory).map f) := (isIso_iff_bijective _).mpr hf
  isIso_of_reflects_iso f (forget SimplexCategory)

/-- An isomorphism in `SimplexCategory` induces an `OrderIso`. -/
@[simp]
def orderIsoOfIso {x y : SimplexCategory} (e : x ≅ y) : Fin (x.len + 1) ≃o Fin (y.len + 1) :=
  Equiv.toOrderIso
    { toFun := e.hom.toOrderHom
      invFun := e.inv.toOrderHom
      left_inv := fun i => by
        simpa only using congr_arg (fun φ => (Hom.toOrderHom φ) i) e.hom_inv_id
      right_inv := fun i => by
        simpa only using congr_arg (fun φ => (Hom.toOrderHom φ) i) e.inv_hom_id }
    e.hom.toOrderHom.monotone e.inv.toOrderHom.monotone

theorem iso_eq_iso_refl {x : SimplexCategory} (e : x ≅ x) : e = Iso.refl x := by
  have h : (Finset.univ : Finset (Fin (x.len + 1))).card = x.len + 1 := Finset.card_fin (x.len + 1)
  have eq₁ := Finset.orderEmbOfFin_unique' h fun i => Finset.mem_univ ((orderIsoOfIso e) i)
  have eq₂ :=
    Finset.orderEmbOfFin_unique' h fun i => Finset.mem_univ ((orderIsoOfIso (Iso.refl x)) i)
  -- Porting note: the proof was rewritten from this point in #3414 (reenableeta)
  -- It could be investigated again to see if the original can be restored.
  ext x
  replace eq₁ := congr_arg (· x) eq₁
  replace eq₂ := congr_arg (· x) eq₂.symm
  simp_all

theorem eq_id_of_isIso {x : SimplexCategory} (f : x ⟶ x) [IsIso f] : f = 𝟙 _ :=
  congr_arg (fun φ : _ ≅ _ => φ.hom) (iso_eq_iso_refl (asIso f))

theorem eq_σ_comp_of_not_injective' {n : ℕ} {Δ' : SimplexCategory} (θ : mk (n + 1) ⟶ Δ')
    (i : Fin (n + 1)) (hi : θ.toOrderHom (Fin.castSucc i) = θ.toOrderHom i.succ) :
    ∃ θ' : mk n ⟶ Δ', θ = σ i ≫ θ' := by
  use δ i.succ ≫ θ
  ext1; ext1; ext1 x
  simp only [Hom.toOrderHom_mk, Function.comp_apply, OrderHom.comp_coe, Hom.comp,
    smallCategory_comp, σ, mkHom, OrderHom.coe_mk]
  by_cases h' : x ≤ Fin.castSucc i
  · -- This was not needed before leanprover/lean4#2644
    dsimp
    rw [Fin.predAbove_below i x h']
    have eq := Fin.castSucc_castPred (gt_of_gt_of_ge (Fin.castSucc_lt_last i) h')
    dsimp [δ]
    erw [Fin.succAbove_below i.succ x.castPred _]
    swap
    · rwa [eq, ← Fin.le_castSucc_iff]
    rw [eq]
  · simp only [not_le] at h'
    let y := x.pred <| by rintro (rfl : x = 0); simp at h'
    have hy : x = y.succ := (Fin.succ_pred x _).symm
    rw [hy] at h' ⊢
    -- This was not needed before leanprover/lean4#2644
    conv_rhs => dsimp
    rw [Fin.predAbove_above i y.succ h', Fin.pred_succ]
    by_cases h'' : y = i
    · rw [h'']
      refine hi.symm.trans ?_
      congr 1
      dsimp [δ]
      erw [Fin.succAbove_below i.succ]
      exact Fin.lt_succ
    · dsimp [δ]
      erw [Fin.succAbove_above i.succ _]
      simp only [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val, Fin.val_succ, Fin.coe_castSucc,
        Nat.lt_succ_iff, Fin.ext_iff] at h' h'' ⊢
      cases' Nat.le.dest h' with c hc
      cases c
      · exfalso
        simp only [Nat.zero_eq, add_zero, len_mk, Fin.coe_pred, ge_iff_le] at hc
        rw [hc] at h''
        exact h'' rfl
      · rw [← hc]
        simp only [add_le_add_iff_left, Nat.succ_eq_add_one, le_add_iff_nonneg_left, zero_le]

theorem eq_σ_comp_of_not_injective {n : ℕ} {Δ' : SimplexCategory} (θ : mk (n + 1) ⟶ Δ')
    (hθ : ¬Function.Injective θ.toOrderHom) :
    ∃ (i : Fin (n + 1)) (θ' : mk n ⟶ Δ'), θ = σ i ≫ θ' := by
  simp only [Function.Injective, exists_prop, not_forall] at hθ
  -- as θ is not injective, there exists `x<y` such that `θ x = θ y`
  -- and then, `θ x = θ (x+1)`
  have hθ₂ : ∃ x y : Fin (n + 2), (Hom.toOrderHom θ) x = (Hom.toOrderHom θ) y ∧ x < y := by
    rcases hθ with ⟨x, y, ⟨h₁, h₂⟩⟩
    by_cases h : x < y
    · exact ⟨x, y, ⟨h₁, h⟩⟩
    · refine' ⟨y, x, ⟨h₁.symm, _⟩⟩
      cases' lt_or_eq_of_le (not_lt.mp h) with h' h'
      · exact h'
      · exfalso
        exact h₂ h'.symm
  rcases hθ₂ with ⟨x, y, ⟨h₁, h₂⟩⟩
  let z := x.castPred
  use z
  rw [← show Fin.castSucc z = x from
    Fin.castSucc_castPred (lt_of_lt_of_le h₂ (Fin.le_last y))] at h₁ h₂
  apply eq_σ_comp_of_not_injective'
  rw [Fin.castSucc_lt_iff_succ_le] at h₂
  apply le_antisymm
  · exact θ.toOrderHom.monotone (le_of_lt (Fin.castSucc_lt_succ z))
  · rw [h₁]
    exact θ.toOrderHom.monotone h₂

theorem eq_comp_δ_of_not_surjective' {n : ℕ} {Δ : SimplexCategory} (θ : Δ ⟶ mk (n + 1))
    (i : Fin (n + 2)) (hi : ∀ x, θ.toOrderHom x ≠ i) : ∃ θ' : Δ ⟶ mk n, θ = θ' ≫ δ i := by
  by_cases i < Fin.last (n + 1)
  · use θ ≫ σ (Fin.castPred i)
    ext1
    ext1
    ext1 x
    simp only [Hom.toOrderHom_mk, Function.comp_apply, OrderHom.comp_coe, Hom.comp,
      smallCategory_comp]
    by_cases h' : θ.toOrderHom x ≤ i
    · simp only [σ, mkHom, Hom.toOrderHom_mk, OrderHom.coe_mk]
      -- This was not needed before leanprover/lean4#2644
      dsimp
      -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
      erw [Fin.predAbove_below (Fin.castPred i) (θ.toOrderHom x)
          (by simpa [Fin.castSucc_castPred h] using h')]
      dsimp [δ]
      erw [Fin.succAbove_below i]
      swap
      · simp only [Fin.lt_iff_val_lt_val, Fin.coe_castSucc]
        exact
          lt_of_le_of_lt (Fin.coe_castPred_le_self _)
            (Fin.lt_iff_val_lt_val.mp ((Ne.le_iff_lt (hi x)).mp h'))
      rw [Fin.castSucc_castPred]
      apply lt_of_le_of_lt h' h
    · simp only [not_le] at h'
      -- The next three tactics used to be a simp only call before leanprover/lean4#2644
      rw [σ, mkHom, Hom.toOrderHom_mk, OrderHom.coe_mk, OrderHom.coe_mk]
      erw [OrderHom.coe_mk]
      erw [Fin.predAbove_above (Fin.castPred i) (θ.toOrderHom x)
          (by simpa only [Fin.castSucc_castPred h] using h')]
      dsimp [δ]
      rw [Fin.succAbove_above i _]
      -- This was not needed before leanprover/lean4#2644
      conv_rhs => dsimp
      erw [Fin.succ_pred]
      simpa only [Fin.le_iff_val_le_val, Fin.coe_castSucc, Fin.coe_pred] using
        Nat.le_sub_one_of_lt (Fin.lt_iff_val_lt_val.mp h')
  · obtain rfl := le_antisymm (Fin.le_last i) (not_lt.mp h)
    use θ ≫ σ (Fin.last _)
    ext x : 4
    dsimp [δ, σ]
    dsimp only [Fin.castPred]
    rw [Fin.predAbove_last, Fin.succAbove_last, Fin.castSucc_castPred]
    exact (Ne.le_iff_lt (hi x)).mp (Fin.le_last _)

theorem eq_comp_δ_of_not_surjective {n : ℕ} {Δ : SimplexCategory} (θ : Δ ⟶ mk (n + 1))
    (hθ : ¬Function.Surjective θ.toOrderHom) :
    ∃ (i : Fin (n + 2)) (θ' : Δ ⟶ mk n), θ = θ' ≫ δ i := by
  cases' not_forall.mp hθ with i hi
  use i
  exact eq_comp_δ_of_not_surjective' θ i (not_exists.mp hi)

theorem eq_id_of_mono {x : SimplexCategory} (i : x ⟶ x) [Mono i] : i = 𝟙 _ := by
  suffices IsIso i by
    apply eq_id_of_isIso
  apply isIso_of_bijective
  dsimp
  rw [Fintype.bijective_iff_injective_and_card i.toOrderHom, ← mono_iff_injective,
    eq_self_iff_true, and_true_iff]
  infer_instance

theorem eq_id_of_epi {x : SimplexCategory} (i : x ⟶ x) [Epi i] : i = 𝟙 _ := by
  suffices IsIso i by
    haveI := this
    apply eq_id_of_isIso
  apply isIso_of_bijective
  dsimp
  rw [Fintype.bijective_iff_surjective_and_card i.toOrderHom, ← epi_iff_surjective,
    eq_self_iff_true, and_true_iff]
  infer_instance

theorem eq_σ_of_epi {n : ℕ} (θ : mk (n + 1) ⟶ mk n) [Epi θ] : ∃ i : Fin (n + 1), θ = σ i := by
  rcases eq_σ_comp_of_not_injective θ (by
    by_contra h
    simpa using le_of_mono (mono_iff_injective.mpr h)) with ⟨i, θ', h⟩
  use i
  haveI : Epi (σ i ≫ θ') := by
    rw [← h]
    infer_instance
  haveI := CategoryTheory.epi_of_epi (σ i) θ'
  rw [h, eq_id_of_epi θ', Category.comp_id]

theorem eq_δ_of_mono {n : ℕ} (θ : mk n ⟶ mk (n + 1)) [Mono θ] : ∃ i : Fin (n + 2), θ = δ i := by
  rcases eq_comp_δ_of_not_surjective θ (by
    by_contra h
    simpa using le_of_epi (epi_iff_surjective.mpr h)) with ⟨i, θ', h⟩
  use i
  haveI : Mono (θ' ≫ δ i) := by
    rw [← h]
    infer_instance
  haveI := CategoryTheory.mono_of_mono θ' (δ i)
  rw [h, eq_id_of_mono θ', Category.id_comp]

theorem len_lt_of_mono {Δ' Δ : SimplexCategory} (i : Δ' ⟶ Δ) [hi : Mono i] (hi' : Δ ≠ Δ') :
    Δ'.len < Δ.len := by
  rcases lt_or_eq_of_le (len_le_of_mono hi) with (h | h)
  · exact h
  · exfalso
    exact hi' (by ext; exact h.symm)

noncomputable instance : SplitEpiCategory SimplexCategory :=
  skeletalEquivalence.inverse.splitEpiCategoryImpOfIsEquivalence

instance : HasStrongEpiMonoFactorisations SimplexCategory :=
  Functor.hasStrongEpiMonoFactorisations_imp_of_isEquivalence
    SimplexCategory.skeletalEquivalence.inverse

instance : HasStrongEpiImages SimplexCategory :=
  Limits.hasStrongEpiImages_of_hasStrongEpiMonoFactorisations

instance (Δ Δ' : SimplexCategory) (θ : Δ ⟶ Δ') : Epi (factorThruImage θ) :=
  StrongEpi.epi

theorem image_eq {Δ Δ' Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ Δ'} [Epi e] {i : Δ' ⟶ Δ''}
    [Mono i] (fac : e ≫ i = φ) : image φ = Δ' := by
  haveI := strongEpi_of_epi e
  let e := image.isoStrongEpiMono e i fac
  ext
  exact
    le_antisymm (len_le_of_epi (inferInstance : Epi e.hom))
      (len_le_of_mono (inferInstance : Mono e.hom))

theorem image_ι_eq {Δ Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ image φ} [Epi e]
    {i : image φ ⟶ Δ''} [Mono i] (fac : e ≫ i = φ) : image.ι φ = i := by
  haveI := strongEpi_of_epi e
  rw [← image.isoStrongEpiMono_hom_comp_ι e i fac,
    SimplexCategory.eq_id_of_isIso (image.isoStrongEpiMono e i fac).hom, Category.id_comp]

theorem factorThruImage_eq {Δ Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ image φ} [Epi e]
    {i : image φ ⟶ Δ''} [Mono i] (fac : e ≫ i = φ) : factorThruImage φ = e := by
  rw [← cancel_mono i, fac, ← image_ι_eq fac, image.fac]

end EpiMono

/-- This functor `SimplexCategory ⥤ Cat` sends `[n]` (for `n : ℕ`)
to the category attached to the ordered set `{0, 1, ..., n}` -/
@[simps! obj map]
def toCat : SimplexCategory ⥤ Cat.{0} :=
  SimplexCategory.skeletalFunctor ⋙ forget₂ NonemptyFinLinOrd LinOrd ⋙
      forget₂ LinOrd Lat ⋙ forget₂ Lat PartOrd ⋙
      forget₂ PartOrd Preord ⋙ preordToCat

end SimplexCategory
