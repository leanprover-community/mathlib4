/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.Proper

/-!
# Homotopy cartesian squares in right proper model categories

In a right proper model category `C`, we introduce a predicate
`HoCartSq t l r b` for homotopy cartesian squares:
```
   t
X₁ ⟶ X₂
l|   |r
 v   v
X₃ ⟶ X₄
   b
```
Given a factorization `r' ≫ r'' = r` of `r` as a weak equivalence `r' : X₂ ⟶ X₂'`
followed by a fibration `r'' : X₂' ⟶ X₄`, the commutative square is homotopy
cartesian iff the morphism `X₁ ⟶ pullback r'' b` intduces by `t ≫ r'` and `l`
is a weak equivalence (see the lemma `HoCartSq.iff_of_fac_right`,
and the transposed version `HoCartSq.iff_of_fac_bottom`).

We obtain results about the horizontal and the vertical composition of
homotopy cartesian squares. We also show that when we have two
"weakly equivalent commutative squares", then one is homotopy cartesian
iff the other is.

## References
* [Paul G. Goerss, John F. Jardine, Simplicial Homotopy Theory][goerss-jardine-2009]
* https://ncatlab.org/nlab/show/proper+model+category

-/

@[expose] public section

namespace HomotopicalAlgebra

open CategoryTheory Limits

variable {C : Type*} [Category* C]
  {X₁ X₂ X₃ X₄ : C} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

namespace HoCartSq

variable [CategoryWithWeakEquivalences C] [CategoryWithFibrations C]
  [(fibrations C).IsStableUnderBaseChange]

lemma key_lemma (sq : CommSq t l r b)
    {X₂' : C} (r' : X₂ ⟶ X₂') (r'' : X₂' ⟶ X₄) [WeakEquivalence r'] [Fibration r'']
    {X₃' : C} (b' : X₃ ⟶ X₃') (b'' : X₃' ⟶ X₄) [WeakEquivalence b'] [Fibration b'']
    [IsRightProper C] [HasPullback r'' b] [HasPullback r b''] [HasPullback r'' b'']
    [(weakEquivalences C).HasTwoOutOfThreeProperty]
    (hr : r' ≫ r'' = r := by cat_disch)
    (hb : b' ≫ b'' = b := by cat_disch) :
    WeakEquivalence (pullback.lift (t ≫ r') l (by simp [hr, sq.w]) : X₁ ⟶ pullback r'' b) ↔
      WeakEquivalence (pullback.lift t (l ≫ b') (by simp [hb, sq.w]) : X₁ ⟶ pullback r b'') := by
  let α : X₁ ⟶ pullback r'' b := pullback.lift (t ≫ r') l (by simp [hr, sq.w])
  let β : X₁ ⟶ pullback r b'' := pullback.lift t (l ≫ b') (by simp [hb, sq.w])
  let α' := pullback.map r'' b r'' b'' (𝟙 _) b' (𝟙 _) (by simp) (by simp [hb])
  let β' := pullback.map r b'' r'' b'' r' (𝟙 _) (𝟙 _) (by simp [hr]) (by simp)
  have w : α ≫ α' = β ≫ β' := by cat_disch
  subst hb hr
  rw [← weakEquivalence_postcomp_iff _ α', ← weakEquivalence_postcomp_iff _ β', w]

end HoCartSq

variable [ModelCategory C]

variable (t l r b) in
/--
Consider a commutative square in a model category `C`
```
   t
X₁ ⟶ X₂
l|   |r
 v   v
X₃ ⟶ X₄
   b
```
We say that this is a homotopy cartesian square if for any factorization
`r' ≫ r'' = r` of `r` as a weak equivalence `r' : X₂ ⟶ X₂'` followed
by a fibration `r'' : X₂' ⟶ X₄`, the morphism `X₁ ⟶ pullback r'' b`
induced by `t ≫ r'` and `l` is a weak equivalence.
(This notion behaves well only in a right proper model category.)
-/
structure HoCartSq : Prop extends CommSq t l r b where
  weakEquivalence_of_fac_right {X₂' : C} (r' : X₂ ⟶ X₂') (r'' : X₂' ⟶ X₄)
      [WeakEquivalence r'] [Fibration r''] (hr : r' ≫ r'' = r := by cat_disch) :
    WeakEquivalence (pullback.lift (t ≫ r') l (by simp [hr, w]) : X₁ ⟶ pullback r'' b)

namespace HoCartSq

variable [IsRightProper C]

lemma of_fac_bottom
    (sq : CommSq t l r b) {X₃' : C} (b' : X₃ ⟶ X₃') (b'' : X₃' ⟶ X₄)
    [WeakEquivalence b'] [Fibration b''] (hb : b' ≫ b'' = b := by cat_disch)
    (h : WeakEquivalence (pullback.lift t (l ≫ b') (by simp [hb, sq.w]) : X₁ ⟶ pullback r b'') :=
      by infer_instance) :
    HoCartSq t l r b where
  w := sq.w
  weakEquivalence_of_fac_right r' r'' _ _ hr := by
    rwa [key_lemma sq r' r'' b' b'']

lemma of_fac_right
    (sq : CommSq t l r b) {X₂' : C} (r' : X₂ ⟶ X₂') (r'' : X₂' ⟶ X₄)
    [WeakEquivalence r'] [Fibration r''] (hr : r' ≫ r'' = r := by cat_disch)
    (h : WeakEquivalence (pullback.lift (t ≫ r') l (by simp [hr, sq.w]) : X₁ ⟶ pullback r'' b) :=
      by infer_instance) :
    HoCartSq t l r b := by
  let Φ := (trivialCofibrations C).factorizationData (fibrations C) b
  refine of_fac_bottom sq Φ.i Φ.p Φ.fac ?_
  rwa [← key_lemma sq r' r'' Φ.i Φ.p]

lemma weakEquivalence_of_fac_bottom
      (sq : HoCartSq t l r b) {X₃' : C} (b' : X₃ ⟶ X₃') (b'' : X₃' ⟶ X₄)
      [WeakEquivalence b'] [Fibration b''] (hb : b' ≫ b'' = b := by cat_disch) :
    WeakEquivalence (pullback.lift t (l ≫ b') (by simp [hb, sq.w]) : X₁ ⟶ pullback r b'') := by
  let Φ := (trivialCofibrations C).factorizationData (fibrations C) r
  rw [← key_lemma sq.toCommSq Φ.i Φ.p b' b'']
  exact sq.weakEquivalence_of_fac_right _ _ Φ.fac

lemma weakEquivalence_of_fac_bottom'
    (sq : HoCartSq t l r b) {X₃' P : C} {b'' : X₃' ⟶ X₄}
    {fst : P ⟶ X₂} {snd : P ⟶ X₃'} (sq' : IsPullback fst snd r b'')
    (b' : X₃ ⟶ X₃') (α : X₁ ⟶ P)
    (hb : b' ≫ b'' = b := by cat_disch)
    (hα₁ : α ≫ fst = t := by cat_disch)
    (hα₂ : α ≫ snd = l ≫ b' := by cat_disch)
    (hb' : WeakEquivalence b' := by infer_instance)
    (hb'' : Fibration b'' := by infer_instance) :
    WeakEquivalence α := by
  have := sq.weakEquivalence_of_fac_bottom _ _ hb
  have : α = (pullback.lift t (l ≫ b') (by simp [sq.w, hb])) ≫
      ((IsPullback.of_hasPullback _ _).isoIsPullback sq').hom :=
    sq'.hom_ext (by simpa) (by simpa)
  rw [this]
  infer_instance

lemma of_fac_bottom'
    (sq : CommSq t l r b)
    {X₃' P : C} {b'' : X₃' ⟶ X₄}
    {fst : P ⟶ X₂} {snd : P ⟶ X₃'} (sq' : IsPullback fst snd r b'')
    (b' : X₃ ⟶ X₃') (α : X₁ ⟶ P)
    (hb : b' ≫ b'' = b := by cat_disch)
    (hα₁ : α ≫ fst = t := by cat_disch)
    (hα₂ : α ≫ snd = l ≫ b' := by cat_disch)
    (hb' : WeakEquivalence b' := by infer_instance)
    (hb'' : Fibration b'' := by infer_instance)
    (hα : WeakEquivalence α := by infer_instance) :
    HoCartSq t l r b := by
  refine of_fac_bottom sq _ _ hb ?_
  have : pullback.lift t (l ≫ b') (by simp [hb, sq.w]) =
      α ≫ (sq'.isoIsPullback (.of_hasPullback r b'')).hom := by
    cat_disch
  rw [this]
  infer_instance

lemma iff_of_fac_bottom'
    (sq : CommSq t l r b)
    {X₃' P : C} {b'' : X₃' ⟶ X₄}
    {fst : P ⟶ X₂} {snd : P ⟶ X₃'} (sq' : IsPullback fst snd r b'')
    (b' : X₃ ⟶ X₃') (α : X₁ ⟶ P)
    (hb : b' ≫ b'' = b := by cat_disch)
    (hα₁ : α ≫ fst = t := by cat_disch)
    (hα₂ : α ≫ snd = l ≫ b' := by cat_disch)
    (hb' : WeakEquivalence b' := by infer_instance)
    (hb'' : Fibration b'' := by infer_instance) :
    HoCartSq t l r b ↔ WeakEquivalence α :=
  ⟨fun sq'' ↦ sq''.weakEquivalence_of_fac_bottom' sq' _ _ hb,
    fun _ ↦ of_fac_bottom' sq sq' _ _ hb⟩

lemma iff_of_fac_bottom
    (sq : CommSq t l r b)
    {X₃' : C} (b' : X₃ ⟶ X₃') (b'' : X₃' ⟶ X₄)
    (hb : b' ≫ b'' = b := by cat_disch)
    (hb' : WeakEquivalence b' := by infer_instance)
    (hb'' : Fibration b'' := by infer_instance) :
    HoCartSq t l r b ↔
      WeakEquivalence (pullback.lift t (l ≫ b') (by simp [hb, sq.w]) : X₁ ⟶ pullback r b'') :=
  iff_of_fac_bottom' sq (.of_hasPullback _ _) _ _ hb

lemma flip (sq : HoCartSq t l r b) : HoCartSq l t b r where
  w := sq.w.symm
  weakEquivalence_of_fac_right b' b'' _ _ hb :=
    sq.weakEquivalence_of_fac_bottom'
      (IsPullback.of_hasPullback _ _).flip b' _ hb

lemma of_fac_right'
    (sq : CommSq t l r b)
    {X₂' P : C} {r'' : X₂' ⟶ X₄}
    {fst : P ⟶ X₂'} {snd : P ⟶ X₃} (sq' : IsPullback fst snd r'' b)
    (r' : X₂ ⟶ X₂') (α : X₁ ⟶ P)
    (hr : r' ≫ r'' = r := by cat_disch)
    (hα₁ : α ≫ fst = t ≫ r' := by cat_disch)
    (hα₂ : α ≫ snd = l := by cat_disch)
    (hr' : WeakEquivalence r' := by infer_instance)
    (hr'' : Fibration r'' := by infer_instance)
    (hα : WeakEquivalence α := by infer_instance) :
    HoCartSq t l r b :=
  .flip (of_fac_bottom' sq.flip sq'.flip r' α)

lemma weakEquivalence_of_fac_right'
    (sq : HoCartSq t l r b) {X₂' P : C} {r'' : X₂' ⟶ X₄}
    {fst : P ⟶ X₂'} {snd : P ⟶ X₃} (sq' : IsPullback fst snd r'' b)
    (r' : X₂ ⟶ X₂') (α : X₁ ⟶ P)
    (hr : r' ≫ r'' = r := by cat_disch)
    (hα₁ : α ≫ fst = t ≫ r' := by cat_disch)
    (hα₂ : α ≫ snd = l := by cat_disch)
    (hr' : WeakEquivalence r' := by infer_instance)
    (hr'' : Fibration r'' := by infer_instance) :
    WeakEquivalence α :=
  sq.flip.weakEquivalence_of_fac_bottom' sq'.flip r' α

lemma iff_of_fac_right'
    (sq : CommSq t l r b)
    {X₂' P : C} {r'' : X₂' ⟶ X₄}
    {fst : P ⟶ X₂'} {snd : P ⟶ X₃} (sq' : IsPullback fst snd r'' b)
    (r' : X₂ ⟶ X₂') (α : X₁ ⟶ P)
    (hr : r' ≫ r'' = r := by cat_disch)
    (hα₁ : α ≫ fst = t ≫ r' := by cat_disch)
    (hα₂ : α ≫ snd = l := by cat_disch)
    (hr' : WeakEquivalence r' := by infer_instance)
    (hr'' : Fibration r'' := by infer_instance) :
    HoCartSq t l r b ↔ WeakEquivalence α :=
  ⟨fun sq'' ↦ sq''.weakEquivalence_of_fac_right' sq' _ _ hr,
    fun _ ↦ of_fac_right' sq sq' _ _ hr⟩

lemma iff_of_fac_right
    (sq : CommSq t l r b)
    {X₂' : C} (r' : X₂ ⟶ X₂') (r'' : X₂' ⟶ X₄)
    (hr : r' ≫ r'' = r := by cat_disch)
    (hr' : WeakEquivalence r' := by infer_instance)
    (hr'' : Fibration r'' := by infer_instance) :
    HoCartSq t l r b ↔
      WeakEquivalence (pullback.lift (t ≫ r') l (by simp [hr, sq.w]) : X₁ ⟶ pullback r'' b) :=
  iff_of_fac_right' sq (.of_hasPullback _ _) _ _ hr

variable (r b) in
lemma of_hasPullback_of_fibration [Fibration r] :
    HoCartSq (pullback.fst r b) (pullback.snd r b) r b :=
  of_fac_right' ⟨pullback.condition⟩ (.of_hasPullback _ _) (𝟙 _) (𝟙 _)

variable (r b) in
lemma of_hasPullback_of_fibration' [Fibration b] :
    HoCartSq (pullback.fst r b) (pullback.snd r b) r b :=
  of_fac_bottom' ⟨pullback.condition⟩ (.of_hasPullback _ _) (𝟙 _) (𝟙 _)

lemma of_vert_weakEquivalence
    (sq : CommSq t l r b) [WeakEquivalence l] [WeakEquivalence r] :
    HoCartSq t l r b :=
  of_fac_right' sq (.id_vert b) r l (by simp) sq.w.symm

lemma of_horiz_weakEquivalence
    (sq : CommSq t l r b) [WeakEquivalence t] [WeakEquivalence b] :
    HoCartSq t l r b :=
  (of_vert_weakEquivalence sq.flip).flip

lemma paste_vert_iff (sq : CommSq t l r b)
    {X₅ X₆ : C} {l' : X₃ ⟶ X₅} {r' : X₄ ⟶ X₆} {b' : X₅ ⟶ X₆}
    (sq' : HoCartSq b l' r' b') :
    HoCartSq t (l ≫ l') (r ≫ r') b' ↔ HoCartSq t l r b := by
  have sq'' : CommSq t (l ≫ l') (r ≫ r') b' := ⟨by simp [sq.w_assoc, sq'.w]⟩
  let Φ := (trivialCofibrations C).factorizationData (fibrations C) b'
  let α : X₃ ⟶ pullback r' Φ.p :=
    pullback.lift b (l' ≫ Φ.i) (by simp [sq'.w])
  let β : X₁ ⟶ pullback r (pullback.fst r' Φ.p) :=
    pullback.lift t (pullback.lift (l ≫ b)
      (l ≫ l' ≫ Φ.i) (by simp [sq'.w])) (by simp [sq.w])
  have := sq'.weakEquivalence_of_fac_bottom'
    (IsPullback.of_hasPullback r' Φ.p) Φ.i α Φ.fac
  rw [iff_of_fac_bottom' sq'' (.paste_vert
    (.of_hasPullback r (pullback.fst r' Φ.p)) (.of_hasPullback r' Φ.p)) Φ.i β Φ.fac,
    iff_of_fac_bottom' sq (.of_hasPullback r (pullback.fst r' Φ.p)) α β]

lemma paste_vert (sq : HoCartSq t l r b)
    {X₅ X₆ : C} {l' : X₃ ⟶ X₅} {r' : X₄ ⟶ X₆} {b' : X₅ ⟶ X₆}
    (sq' : HoCartSq b l' r' b') :
    HoCartSq t (l ≫ l') (r ≫ r') b' := by
  rwa [paste_vert_iff sq.toCommSq sq']

lemma paste_horiz (sq : HoCartSq t l r b)
    {X₅ X₆ : C} {t' : X₂ ⟶ X₅} {r' : X₅ ⟶ X₆} {b' : X₄ ⟶ X₆}
    (sq' : HoCartSq t' r r' b') :
    HoCartSq (t ≫ t') l r' (b ≫ b') :=
  (sq.flip.paste_vert sq'.flip).flip

lemma iff_of_weakEquivalence (sq : CommSq t l r b)
    {Y₁ Y₂ Y₃ Y₄ : C} {t' : Y₁ ⟶ Y₂} {l' : Y₁ ⟶ Y₃} {r' : Y₂ ⟶ Y₄}
    {b' : Y₃ ⟶ Y₄} (sq' : CommSq t' l' r' b')
    (e₁ : X₁ ⟶ Y₁) (e₂ : X₂ ⟶ Y₂) (e₃ : X₃ ⟶ Y₃) (e₄ : X₄ ⟶ Y₄)
    (ht : t ≫ e₂ = e₁ ≫ t' := by cat_disch)
    (hl : l ≫ e₃ = e₁ ≫ l' := by cat_disch)
    (hr : r ≫ e₄ = e₂ ≫ r' := by cat_disch)
    (hb : b ≫ e₄ = e₃ ≫ b' := by cat_disch)
    (he₁ : WeakEquivalence e₁ := by infer_instance)
    (he₂ : WeakEquivalence e₂ := by infer_instance)
    (he₃ : WeakEquivalence e₃ := by infer_instance)
    (he₄ : WeakEquivalence e₄ := by infer_instance) :
    HoCartSq t l r b ↔ HoCartSq t' l' r' b' := by
  trans HoCartSq t (e₁ ≫ l') (e₂ ≫ r') b'
  · rw [← hl, ← hr]
    exact (paste_vert_iff sq (.of_vert_weakEquivalence ⟨hb⟩)).symm
  · let Φ := (trivialCofibrations C).factorizationData (fibrations C) b'
    let α : Y₁ ⟶ pullback r' Φ.p :=
      pullback.lift t' (l' ≫ Φ.i) (by simp [sq'.w])
    let β : X₁ ⟶ pullback e₂ (pullback.fst r' Φ.p) :=
      pullback.lift t (pullback.lift (e₁ ≫ t') (e₁ ≫ l' ≫ Φ.i) (by simp [sq'.w])) (by simpa)
    rw [iff_of_fac_bottom' sq' (.of_hasPullback r' Φ.p) Φ.i α,
      iff_of_fac_bottom' ⟨by simp [← hr, sq.w_assoc, ← sq'.w, hb, reassoc_of% hl]⟩
        (.paste_vert (.of_hasPullback e₂ (pullback.fst r' Φ.p)) (.of_hasPullback r' Φ.p)) Φ.i β]
    rw [← weakEquivalence_precomp_iff e₁,
      show e₁ ≫ α = β ≫ pullback.snd _ _ by cat_disch,
      weakEquivalence_postcomp_iff]

lemma of_weakEquivalence (sq : HoCartSq t l r b)
    {Y₁ Y₂ Y₃ Y₄ : C} {t' : Y₁ ⟶ Y₂} {l' : Y₁ ⟶ Y₃} {r' : Y₂ ⟶ Y₄}
    {b' : Y₃ ⟶ Y₄} (sq' : CommSq t' l' r' b')
    (e₁ : X₁ ⟶ Y₁) (e₂ : X₂ ⟶ Y₂) (e₃ : X₃ ⟶ Y₃) (e₄ : X₄ ⟶ Y₄)
    (ht : t ≫ e₂ = e₁ ≫ t' := by cat_disch)
    (hl : l ≫ e₃ = e₁ ≫ l' := by cat_disch)
    (hr : r ≫ e₄ = e₂ ≫ r' := by cat_disch)
    (hb : b ≫ e₄ = e₃ ≫ b' := by cat_disch)
    (he₁ : WeakEquivalence e₁ := by infer_instance)
    (he₂ : WeakEquivalence e₂ := by infer_instance)
    (he₃ : WeakEquivalence e₃ := by infer_instance)
    (he₄ : WeakEquivalence e₄ := by infer_instance) :
    HoCartSq t' l' r' b' := by
  rwa [← iff_of_weakEquivalence sq.toCommSq sq' e₁ e₂ e₃ e₄]

lemma of_weakEquivalence' (sq : CommSq t l r b)
    {Y₁ Y₂ Y₃ Y₄ : C} {t' : Y₁ ⟶ Y₂} {l' : Y₁ ⟶ Y₃} {r' : Y₂ ⟶ Y₄}
    {b' : Y₃ ⟶ Y₄} (sq' : HoCartSq t' l' r' b')
    (e₁ : X₁ ⟶ Y₁) (e₂ : X₂ ⟶ Y₂) (e₃ : X₃ ⟶ Y₃) (e₄ : X₄ ⟶ Y₄)
    (ht : t ≫ e₂ = e₁ ≫ t' := by cat_disch)
    (hl : l ≫ e₃ = e₁ ≫ l' := by cat_disch)
    (hr : r ≫ e₄ = e₂ ≫ r' := by cat_disch)
    (hb : b ≫ e₄ = e₃ ≫ b' := by cat_disch)
    (he₁ : WeakEquivalence e₁ := by infer_instance)
    (he₂ : WeakEquivalence e₂ := by infer_instance)
    (he₃ : WeakEquivalence e₃ := by infer_instance)
    (he₄ : WeakEquivalence e₄ := by infer_instance) :
    HoCartSq t l r b := by
  rwa [iff_of_weakEquivalence sq sq'.toCommSq e₁ e₂ e₃ e₄]

lemma weakEquivalence (sq : HoCartSq t l r b)
    {Y₁ Y₂ Y₃ Y₄ : C} {t' : Y₁ ⟶ Y₂} {l' : Y₁ ⟶ Y₃} {r' : Y₂ ⟶ Y₄}
    {b' : Y₃ ⟶ Y₄} (sq' : HoCartSq t' l' r' b')
    (e₁ : X₁ ⟶ Y₁) (e₂ : X₂ ⟶ Y₂) (e₃ : X₃ ⟶ Y₃) (e₄ : X₄ ⟶ Y₄)
    (ht : t ≫ e₂ = e₁ ≫ t' := by cat_disch)
    (hl : l ≫ e₃ = e₁ ≫ l' := by cat_disch)
    (hr : r ≫ e₄ = e₂ ≫ r' := by cat_disch)
    (hb : b ≫ e₄ = e₃ ≫ b' := by cat_disch)
    (he₂ : WeakEquivalence e₂ := by infer_instance)
    (he₃ : WeakEquivalence e₃ := by infer_instance)
    (he₄ : WeakEquivalence e₄ := by infer_instance) :
    WeakEquivalence e₁ := by
  let Φ := (trivialCofibrations C).factorizationData (fibrations C) b'
  have sq'' : HoCartSq (e₁ ≫ t') (e₁ ≫ l') r' b' :=
    of_weakEquivalence sq ⟨by simp [sq'.w]⟩ (𝟙 _) e₂ e₃ e₄
  let α : Y₁ ⟶ pullback r' Φ.p := pullback.lift t' (l' ≫ Φ.i) (by simp [sq'.w])
  have := sq'.weakEquivalence_of_fac_bottom' (.of_hasPullback r' Φ.p) Φ.i α
  have := sq''.weakEquivalence_of_fac_bottom' (sq' := .of_hasPullback r' Φ.p) Φ.i (e₁ ≫ α)
  exact weakEquivalence_of_postcomp _ α

instance {Y₂ Y₃ Y₄ : C} (r' : Y₂ ⟶ Y₄) (b' : Y₃ ⟶ Y₄)
    (e₂ : X₂ ⟶ Y₂) (e₃ : X₃ ⟶ Y₃) (e₄ : X₄ ⟶ Y₄)
    (hr : r ≫ e₄ = e₂ ≫ r') (hb : b ≫ e₄ = e₃ ≫ b')
    [Fibration r] [Fibration r']
    [WeakEquivalence e₂] [WeakEquivalence e₃] [WeakEquivalence e₄] :
    WeakEquivalence (pullback.map r b r' b' e₂ e₃ e₄ hr hb) :=
  weakEquivalence (.of_hasPullback_of_fibration r b)
    (.of_hasPullback_of_fibration r' b') _ e₂ e₃ e₄

instance {Y₂ Y₃ Y₄ : C} (r' : Y₂ ⟶ Y₄) (b' : Y₃ ⟶ Y₄)
    (e₂ : X₂ ⟶ Y₂) (e₃ : X₃ ⟶ Y₃) (e₄ : X₄ ⟶ Y₄)
    (hr : r ≫ e₄ = e₂ ≫ r') (hb : b ≫ e₄ = e₃ ≫ b')
    [Fibration b] [Fibration b']
    [WeakEquivalence e₂] [WeakEquivalence e₃] [WeakEquivalence e₄] :
    WeakEquivalence (pullback.map r b r' b' e₂ e₃ e₄ hr hb) :=
  weakEquivalence (.of_hasPullback_of_fibration' r b)
    (.of_hasPullback_of_fibration' r' b') _ e₂ e₃ e₄

end HoCartSq

end HomotopicalAlgebra
