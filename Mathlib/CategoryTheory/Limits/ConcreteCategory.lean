/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Adam Topaz
-/
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.Tactic.ApplyFun

#align_import category_theory.limits.concrete_category from "leanprover-community/mathlib"@"c3019c79074b0619edb4b27553a91b2e82242395"

/-!
# Facts about (co)limits of functors into concrete categories
-/


universe w v u

open CategoryTheory

namespace CategoryTheory.Limits

attribute [local instance] ConcreteCategory.funLike ConcreteCategory.hasCoeToSort

section Limits

variable {C : Type u} [Category.{v} C] [ConcreteCategory.{max w v} C] {J : Type w} [SmallCategory J]
  (F : J ⥤ C) [PreservesLimit F (forget C)]

theorem Concrete.to_product_injective_of_isLimit {D : Cone F} (hD : IsLimit D) :
    Function.Injective fun (x : D.pt) (j : J) => D.π.app j x := by
  let E := (forget C).mapCone D
  -- ⊢ Function.Injective fun x j => ↑(NatTrans.app D.π j) x
  let hE : IsLimit E := isLimitOfPreserves _ hD
  -- ⊢ Function.Injective fun x j => ↑(NatTrans.app D.π j) x
  let G := Types.limitCone.{w, v} (F ⋙ forget C)
  -- ⊢ Function.Injective fun x j => ↑(NatTrans.app D.π j) x
  let hG := Types.limitConeIsLimit.{w, v} (F ⋙ forget C)
  -- ⊢ Function.Injective fun x j => ↑(NatTrans.app D.π j) x
  let T : E.pt ≅ G.pt := hE.conePointUniqueUpToIso hG
  -- ⊢ Function.Injective fun x j => ↑(NatTrans.app D.π j) x
  change Function.Injective (T.hom ≫ fun x j => G.π.app j x)
  -- ⊢ Function.Injective (T.hom ≫ fun x j => NatTrans.app G.π j x)
  have h : Function.Injective T.hom := by
    intro a b h
    suffices T.inv (T.hom a) = T.inv (T.hom b) by simpa
    rw [h]
  suffices Function.Injective fun (x : G.pt) j => G.π.app j x by exact this.comp h
  -- ⊢ Function.Injective fun x j => NatTrans.app G.π j x
  apply Subtype.ext
  -- 🎉 no goals
#align category_theory.limits.concrete.to_product_injective_of_is_limit CategoryTheory.Limits.Concrete.to_product_injective_of_isLimit

theorem Concrete.isLimit_ext {D : Cone F} (hD : IsLimit D) (x y : D.pt) :
    (∀ j, D.π.app j x = D.π.app j y) → x = y := fun h =>
  Concrete.to_product_injective_of_isLimit _ hD (funext h)
#align category_theory.limits.concrete.is_limit_ext CategoryTheory.Limits.Concrete.isLimit_ext

theorem Concrete.limit_ext [HasLimit F] (x y : ↑(limit F)) :
    (∀ j, limit.π F j x = limit.π F j y) → x = y :=
  Concrete.isLimit_ext F (limit.isLimit _) _ _
#align category_theory.limits.concrete.limit_ext CategoryTheory.Limits.Concrete.limit_ext

section WidePullback

open WidePullback

open WidePullbackShape

theorem Concrete.widePullback_ext {B : C} {ι : Type w} {X : ι → C} (f : ∀ j : ι, X j ⟶ B)
    [HasWidePullback B X f] [PreservesLimit (wideCospan B X f) (forget C)]
    (x y : ↑(widePullback B X f)) (h₀ : base f x = base f y) (h : ∀ j, π f j x = π f j y) :
    x = y := by
  apply Concrete.limit_ext
  -- ⊢ ∀ (j : WidePullbackShape ι), ↑(limit.π (wideCospan B X f) j) x = ↑(limit.π ( …
  rintro (_ | j)
  -- ⊢ ↑(limit.π (wideCospan B X f) none) x = ↑(limit.π (wideCospan B X f) none) y
  · exact h₀
    -- 🎉 no goals
  · apply h
    -- 🎉 no goals
#align category_theory.limits.concrete.wide_pullback_ext CategoryTheory.Limits.Concrete.widePullback_ext

theorem Concrete.widePullback_ext' {B : C} {ι : Type w} [Nonempty ι] {X : ι → C}
    (f : ∀ j : ι, X j ⟶ B) [HasWidePullback.{w} B X f]
    [PreservesLimit (wideCospan B X f) (forget C)] (x y : ↑(widePullback B X f))
    (h : ∀ j, π f j x = π f j y) : x = y := by
  apply Concrete.widePullback_ext _ _ _ _ h
  -- ⊢ ↑(base f) x = ↑(base f) y
  inhabit ι
  -- ⊢ ↑(base f) x = ↑(base f) y
  simp only [← π_arrow f default, comp_apply, h]
  -- 🎉 no goals
#align category_theory.limits.concrete.wide_pullback_ext' CategoryTheory.Limits.Concrete.widePullback_ext'

end WidePullback

section Multiequalizer

theorem Concrete.multiequalizer_ext {I : MulticospanIndex.{w} C} [HasMultiequalizer I]
    [PreservesLimit I.multicospan (forget C)] (x y : ↑(multiequalizer I))
    (h : ∀ t : I.L, Multiequalizer.ι I t x = Multiequalizer.ι I t y) : x = y := by
  apply Concrete.limit_ext
  -- ⊢ ∀ (j : WalkingMulticospan I.fstTo I.sndTo), ↑(limit.π (MulticospanIndex.mult …
  rintro (a | b)
  -- ⊢ ↑(limit.π (MulticospanIndex.multicospan I) (WalkingMulticospan.left a)) x =  …
  · apply h
    -- 🎉 no goals
  · rw [← limit.w I.multicospan (WalkingMulticospan.Hom.fst b), comp_apply, comp_apply]
    -- ⊢ ↑((MulticospanIndex.multicospan I).map (WalkingMulticospan.Hom.fst b)) (↑(li …
    simp [h]
    -- 🎉 no goals
#align category_theory.limits.concrete.multiequalizer_ext CategoryTheory.Limits.Concrete.multiequalizer_ext

/-- An auxiliary equivalence to be used in `multiequalizerEquiv` below.-/
def Concrete.multiequalizerEquivAux (I : MulticospanIndex C) :
    (I.multicospan ⋙ forget C).sections ≃
    { x : ∀ i : I.L, I.left i // ∀ i : I.R, I.fst i (x _) = I.snd i (x _) } where
  toFun x :=
    ⟨fun i => x.1 (WalkingMulticospan.left _), fun i => by
      have a := x.2 (WalkingMulticospan.Hom.fst i)
      -- ⊢ ↑(MulticospanIndex.fst I i) ((fun i => ↑x (WalkingMulticospan.left i)) (Mult …
      have b := x.2 (WalkingMulticospan.Hom.snd i)
      -- ⊢ ↑(MulticospanIndex.fst I i) ((fun i => ↑x (WalkingMulticospan.left i)) (Mult …
      rw [← b] at a
      -- ⊢ ↑(MulticospanIndex.fst I i) ((fun i => ↑x (WalkingMulticospan.left i)) (Mult …
      exact a⟩
      -- 🎉 no goals
  invFun x :=
    { val := fun j =>
        match j with
        | WalkingMulticospan.left a => x.1 _
        | WalkingMulticospan.right b => I.fst b (x.1 _)
      property := by
        rintro (a | b) (a' | b') (f | f | f)
        · simp
          -- 🎉 no goals
        · rfl
          -- 🎉 no goals
        · dsimp
          -- ⊢ (forget C).map (MulticospanIndex.snd I b') (↑x (MulticospanIndex.sndTo I b') …
          exact (x.2 b').symm
          -- 🎉 no goals
        · simp }
          -- 🎉 no goals
  left_inv := by
    intro x; ext (a | b)
    -- ⊢ (fun x =>
    · rfl
      -- 🎉 no goals
    · rw [← x.2 (WalkingMulticospan.Hom.fst b)]
      -- ⊢ ↑((fun x =>
      rfl
      -- 🎉 no goals
  right_inv := by
    intro x
    -- ⊢ (fun x => { val := fun i => ↑x (WalkingMulticospan.left i), property := (_ : …
    ext i
    -- ⊢ ↑((fun x => { val := fun i => ↑x (WalkingMulticospan.left i), property := (_ …
    rfl
    -- 🎉 no goals
#align category_theory.limits.concrete.multiequalizer_equiv_aux CategoryTheory.Limits.Concrete.multiequalizerEquivAux

/-- The equivalence between the noncomputable multiequalizer and
the concrete multiequalizer. -/
noncomputable def Concrete.multiequalizerEquiv (I : MulticospanIndex.{w} C) [HasMultiequalizer I]
    [PreservesLimit I.multicospan (forget C)] :
    (multiequalizer I : C) ≃
      { x : ∀ i : I.L, I.left i // ∀ i : I.R, I.fst i (x _) = I.snd i (x _) } := by
  let h1 := limit.isLimit I.multicospan
  -- ⊢ (forget C).obj (multiequalizer I) ≃ { x // ∀ (i : I.R), ↑(MulticospanIndex.f …
  let h2 := isLimitOfPreserves (forget C) h1
  -- ⊢ (forget C).obj (multiequalizer I) ≃ { x // ∀ (i : I.R), ↑(MulticospanIndex.f …
  let E := h2.conePointUniqueUpToIso (Types.limitConeIsLimit.{w, v} _)
  -- ⊢ (forget C).obj (multiequalizer I) ≃ { x // ∀ (i : I.R), ↑(MulticospanIndex.f …
  exact Equiv.trans E.toEquiv (Concrete.multiequalizerEquivAux.{w, v} I)
  -- 🎉 no goals
#align category_theory.limits.concrete.multiequalizer_equiv CategoryTheory.Limits.Concrete.multiequalizerEquiv

@[simp]
theorem Concrete.multiequalizerEquiv_apply (I : MulticospanIndex.{w} C) [HasMultiequalizer I]
    [PreservesLimit I.multicospan (forget C)] (x : ↑(multiequalizer I)) (i : I.L) :
    ((Concrete.multiequalizerEquiv I) x : ∀ i : I.L, I.left i) i = Multiequalizer.ι I i x :=
  rfl
#align category_theory.limits.concrete.multiequalizer_equiv_apply CategoryTheory.Limits.Concrete.multiequalizerEquiv_apply

end Multiequalizer

-- TODO: Add analogous lemmas about products and equalizers.
end Limits

section Colimits

-- We don't mark this as an `@[ext]` lemma as we don't always want to work elementwise.
theorem cokernel_funext {C : Type*} [Category C] [HasZeroMorphisms C] [ConcreteCategory C]
    {M N K : C} {f : M ⟶ N} [HasCokernel f] {g h : cokernel f ⟶ K}
    (w : ∀ n : N, g (cokernel.π f n) = h (cokernel.π f n)) : g = h := by
  ext x
  -- ⊢ ↑(coequalizer.π f 0 ≫ g) x = ↑(coequalizer.π f 0 ≫ h) x
  simpa using w x
  -- 🎉 no goals
#align category_theory.limits.cokernel_funext CategoryTheory.Limits.cokernel_funext

variable {C : Type u} [Category.{v} C] [ConcreteCategory.{v} C] {J : Type v} [SmallCategory J]
  (F : J ⥤ C) [PreservesColimit F (forget C)]

theorem Concrete.from_union_surjective_of_isColimit {D : Cocone F} (hD : IsColimit D) :
    let ff : (Σj : J, F.obj j) → D.pt := fun a => D.ι.app a.1 a.2
    Function.Surjective ff := by
  intro ff
  -- ⊢ Function.Surjective ff
  let E := (forget C).mapCocone D
  -- ⊢ Function.Surjective ff
  let hE : IsColimit E := isColimitOfPreserves _ hD
  -- ⊢ Function.Surjective ff
  let G := Types.colimitCocone.{v, v} (F ⋙ forget C)
  -- ⊢ Function.Surjective ff
  let hG := Types.colimitCoconeIsColimit.{v, v} (F ⋙ forget C)
  -- ⊢ Function.Surjective ff
  let T : E ≅ G := hE.uniqueUpToIso hG
  -- ⊢ Function.Surjective ff
  let TX : E.pt ≅ G.pt := (Cocones.forget _).mapIso T
  -- ⊢ Function.Surjective ff
  suffices Function.Surjective (TX.hom ∘ ff) by
    intro a
    obtain ⟨b, hb⟩ := this (TX.hom a)
    refine' ⟨b, _⟩
    apply_fun TX.inv at hb
    change (TX.hom ≫ TX.inv) (ff b) = (TX.hom ≫ TX.inv) _ at hb
    simpa only [TX.hom_inv_id] using hb
  have : TX.hom ∘ ff = fun a => G.ι.app a.1 a.2 := by
    ext a
    change (E.ι.app a.1 ≫ hE.desc G) a.2 = _
    rw [hE.fac]
  rw [this]
  -- ⊢ Function.Surjective fun a => NatTrans.app G.ι a.fst a.snd
  rintro ⟨⟨j, a⟩⟩
  -- ⊢ ∃ a_1, (fun a => NatTrans.app G.ι a.fst a.snd) a_1 = Quot.mk (Types.Quot.Rel …
  exact ⟨⟨j, a⟩, rfl⟩
  -- 🎉 no goals
#align category_theory.limits.concrete.from_union_surjective_of_is_colimit CategoryTheory.Limits.Concrete.from_union_surjective_of_isColimit

theorem Concrete.isColimit_exists_rep {D : Cocone F} (hD : IsColimit D) (x : D.pt) :
    ∃ (j : J) (y : F.obj j), D.ι.app j y = x := by
  obtain ⟨a, rfl⟩ := Concrete.from_union_surjective_of_isColimit F hD x
  -- ⊢ ∃ j y, ↑(NatTrans.app D.ι j) y = (fun a => ↑(NatTrans.app D.ι a.fst) a.snd) a
  exact ⟨a.1, a.2, rfl⟩
  -- 🎉 no goals
#align category_theory.limits.concrete.is_colimit_exists_rep CategoryTheory.Limits.Concrete.isColimit_exists_rep

theorem Concrete.colimit_exists_rep [HasColimit F] (x : ↑(colimit F)) :
    ∃ (j : J) (y : F.obj j), colimit.ι F j y = x :=
  Concrete.isColimit_exists_rep F (colimit.isColimit _) x
#align category_theory.limits.concrete.colimit_exists_rep CategoryTheory.Limits.Concrete.colimit_exists_rep

theorem Concrete.isColimit_rep_eq_of_exists {D : Cocone F} {i j : J} (hD : IsColimit D)
    (x : F.obj i) (y : F.obj j) (h : ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y) :
    D.ι.app i x = D.ι.app j y := by
  let E := (forget C).mapCocone D
  -- ⊢ ↑(NatTrans.app D.ι i) x = ↑(NatTrans.app D.ι j) y
  let hE : IsColimit E := isColimitOfPreserves _ hD
  -- ⊢ ↑(NatTrans.app D.ι i) x = ↑(NatTrans.app D.ι j) y
  let G := Types.colimitCocone.{v, v} (F ⋙ forget C)
  -- ⊢ ↑(NatTrans.app D.ι i) x = ↑(NatTrans.app D.ι j) y
  let hG := Types.colimitCoconeIsColimit.{v, v} (F ⋙ forget C)
  -- ⊢ ↑(NatTrans.app D.ι i) x = ↑(NatTrans.app D.ι j) y
  let T : E ≅ G := hE.uniqueUpToIso hG
  -- ⊢ ↑(NatTrans.app D.ι i) x = ↑(NatTrans.app D.ι j) y
  let TX : E.pt ≅ G.pt := (Cocones.forget _).mapIso T
  -- ⊢ ↑(NatTrans.app D.ι i) x = ↑(NatTrans.app D.ι j) y
  apply_fun TX.hom using injective_of_mono TX.hom
  -- ⊢ TX.hom (↑(NatTrans.app D.ι i) x) = TX.hom (↑(NatTrans.app D.ι j) y)
  change (E.ι.app i ≫ TX.hom) x = (E.ι.app j ≫ TX.hom) y
  -- ⊢ (NatTrans.app E.ι i ≫ TX.hom) x = (NatTrans.app E.ι j ≫ TX.hom) y
  erw [T.hom.w, T.hom.w]
  -- ⊢ NatTrans.app G.ι i x = NatTrans.app G.ι j y
  obtain ⟨k, f, g, h⟩ := h
  -- ⊢ NatTrans.app G.ι i x = NatTrans.app G.ι j y
  have : G.ι.app i x = (G.ι.app k (F.map f x) : G.pt) := Quot.sound ⟨f, rfl⟩
  -- ⊢ NatTrans.app G.ι i x = NatTrans.app G.ι j y
  rw [this, h]
  -- ⊢ NatTrans.app G.ι k (↑(F.map g) y) = NatTrans.app G.ι j y
  symm
  -- ⊢ NatTrans.app G.ι j y = NatTrans.app G.ι k (↑(F.map g) y)
  exact Quot.sound ⟨g, rfl⟩
  -- 🎉 no goals
#align category_theory.limits.concrete.is_colimit_rep_eq_of_exists CategoryTheory.Limits.Concrete.isColimit_rep_eq_of_exists

theorem Concrete.colimit_rep_eq_of_exists [HasColimit F] {i j : J} (x : F.obj i) (y : F.obj j)
    (h : ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y) :
    colimit.ι F i x = colimit.ι F j y :=
  Concrete.isColimit_rep_eq_of_exists F (colimit.isColimit _) x y h
#align category_theory.limits.concrete.colimit_rep_eq_of_exists CategoryTheory.Limits.Concrete.colimit_rep_eq_of_exists

section FilteredColimits

variable [IsFiltered J]

theorem Concrete.isColimit_exists_of_rep_eq {D : Cocone F} {i j : J} (hD : IsColimit D)
    (x : F.obj i) (y : F.obj j) (h : D.ι.app _ x = D.ι.app _ y) :
    ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y := by
  let E := (forget C).mapCocone D
  -- ⊢ ∃ k f g, ↑(F.map f) x = ↑(F.map g) y
  let hE : IsColimit E := isColimitOfPreserves _ hD
  -- ⊢ ∃ k f g, ↑(F.map f) x = ↑(F.map g) y
  let G := Types.colimitCocone.{v, v} (F ⋙ forget C)
  -- ⊢ ∃ k f g, ↑(F.map f) x = ↑(F.map g) y
  let hG := Types.colimitCoconeIsColimit.{v, v} (F ⋙ forget C)
  -- ⊢ ∃ k f g, ↑(F.map f) x = ↑(F.map g) y
  let T : E ≅ G := hE.uniqueUpToIso hG
  -- ⊢ ∃ k f g, ↑(F.map f) x = ↑(F.map g) y
  let TX : E.pt ≅ G.pt := (Cocones.forget _).mapIso T
  -- ⊢ ∃ k f g, ↑(F.map f) x = ↑(F.map g) y
  apply_fun TX.hom at h
  -- ⊢ ∃ k f g, ↑(F.map f) x = ↑(F.map g) y
  change (E.ι.app i ≫ TX.hom) x = (E.ι.app j ≫ TX.hom) y at h
  -- ⊢ ∃ k f g, ↑(F.map f) x = ↑(F.map g) y
  erw [T.hom.w, T.hom.w] at h
  -- ⊢ ∃ k f g, ↑(F.map f) x = ↑(F.map g) y
  replace h := Quot.exact _ h
  -- ⊢ ∃ k f g, ↑(F.map f) x = ↑(F.map g) y
  suffices
    ∀ (a b : Σj, F.obj j) (_ : EqvGen (Limits.Types.Quot.Rel.{v, v} (F ⋙ forget C)) a b),
      ∃ (k : _) (f : a.1 ⟶ k) (g : b.1 ⟶ k), F.map f a.2 = F.map g b.2
    by exact this ⟨i, x⟩ ⟨j, y⟩ h
  intro a b h
  -- ⊢ ∃ k f g, ↑(F.map f) a.snd = ↑(F.map g) b.snd
  induction h
  case rel x y hh =>
    obtain ⟨e, he⟩ := hh
    use y.1, e, 𝟙 _
    simpa using he.symm
  case refl x =>
    exact ⟨x.1, 𝟙 _, 𝟙 _, rfl⟩
  case symm x y _ hh =>
    obtain ⟨k, f, g, hh⟩ := hh
    exact ⟨k, g, f, hh.symm⟩
  case trans x y z _ _ hh1 hh2 =>
    obtain ⟨k1, f1, g1, h1⟩ := hh1
    obtain ⟨k2, f2, g2, h2⟩ := hh2
    let k0 : J := IsFiltered.max k1 k2
    let e1 : k1 ⟶ k0 := IsFiltered.leftToMax _ _
    let e2 : k2 ⟶ k0 := IsFiltered.rightToMax _ _
    let k : J := IsFiltered.coeq (g1 ≫ e1) (f2 ≫ e2)
    let e : k0 ⟶ k := IsFiltered.coeqHom _ _
    use k, f1 ≫ e1 ≫ e, g2 ≫ e2 ≫ e
    simp only [F.map_comp, comp_apply, h1, ← h2]
    simp only [← comp_apply, ← F.map_comp]
    rw [IsFiltered.coeq_condition]
#align category_theory.limits.concrete.is_colimit_exists_of_rep_eq CategoryTheory.Limits.Concrete.isColimit_exists_of_rep_eq

theorem Concrete.isColimit_rep_eq_iff_exists {D : Cocone F} {i j : J} (hD : IsColimit D)
    (x : F.obj i) (y : F.obj j) :
    D.ι.app i x = D.ι.app j y ↔ ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y :=
  ⟨Concrete.isColimit_exists_of_rep_eq _ hD _ _, Concrete.isColimit_rep_eq_of_exists _ hD _ _⟩
#align category_theory.limits.concrete.is_colimit_rep_eq_iff_exists CategoryTheory.Limits.Concrete.isColimit_rep_eq_iff_exists

theorem Concrete.colimit_exists_of_rep_eq [HasColimit F] {i j : J} (x : F.obj i) (y : F.obj j)
    (h : colimit.ι F _ x = colimit.ι F _ y) :
    ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y :=
  Concrete.isColimit_exists_of_rep_eq F (colimit.isColimit _) x y h
#align category_theory.limits.concrete.colimit_exists_of_rep_eq CategoryTheory.Limits.Concrete.colimit_exists_of_rep_eq

theorem Concrete.colimit_rep_eq_iff_exists [HasColimit F] {i j : J} (x : F.obj i) (y : F.obj j) :
    colimit.ι F i x = colimit.ι F j y ↔ ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y :=
  ⟨Concrete.colimit_exists_of_rep_eq _ _ _, Concrete.colimit_rep_eq_of_exists _ _ _⟩
#align category_theory.limits.concrete.colimit_rep_eq_iff_exists CategoryTheory.Limits.Concrete.colimit_rep_eq_iff_exists

end FilteredColimits

section WidePushout

open WidePushout

open WidePushoutShape

theorem Concrete.widePushout_exists_rep {B : C} {α : Type _} {X : α → C} (f : ∀ j : α, B ⟶ X j)
    [HasWidePushout.{v} B X f] [PreservesColimit (wideSpan B X f) (forget C)]
    (x : ↑(widePushout B X f)) : (∃ y : B, head f y = x) ∨ ∃ (i : α) (y : X i), ι f i y = x := by
  obtain ⟨_ | j, y, rfl⟩ := Concrete.colimit_exists_rep _ x
  -- ⊢ (∃ y_1, ↑(head f) y_1 = ↑(colimit.ι (wideSpan B X f) none) y) ∨ ∃ i y_1, ↑(ι …
  · left
    -- ⊢ ∃ y_1, ↑(head f) y_1 = ↑(colimit.ι (wideSpan B X f) none) y
    use y
    -- ⊢ ↑(head f) y = ↑(colimit.ι (wideSpan B X f) none) y
    rfl
    -- 🎉 no goals
  · right
    -- ⊢ ∃ i y_1, ↑(ι f i) y_1 = ↑(colimit.ι (wideSpan B X f) (some j)) y
    use j, y
    -- ⊢ ↑(ι f j) y = ↑(colimit.ι (wideSpan B X f) (some j)) y
    rfl
    -- 🎉 no goals
#align category_theory.limits.concrete.wide_pushout_exists_rep CategoryTheory.Limits.Concrete.widePushout_exists_rep

theorem Concrete.widePushout_exists_rep' {B : C} {α : Type _} [Nonempty α] {X : α → C}
    (f : ∀ j : α, B ⟶ X j) [HasWidePushout.{v} B X f] [PreservesColimit (wideSpan B X f) (forget C)]
    (x : ↑(widePushout B X f)) : ∃ (i : α) (y : X i), ι f i y = x := by
  rcases Concrete.widePushout_exists_rep f x with (⟨y, rfl⟩ | ⟨i, y, rfl⟩)
  -- ⊢ ∃ i y_1, ↑(ι f i) y_1 = ↑(head f) y
  · inhabit α
    -- ⊢ ∃ i y_1, ↑(ι f i) y_1 = ↑(head f) y
    use default, f _ y
    -- ⊢ ↑(ι f default) (↑(f default) y) = ↑(head f) y
    simp only [← arrow_ι _ default, comp_apply]
    -- 🎉 no goals
  · use i, y
    -- 🎉 no goals
#align category_theory.limits.concrete.wide_pushout_exists_rep' CategoryTheory.Limits.Concrete.widePushout_exists_rep'

end WidePushout

-- TODO: Add analogous lemmas about coproducts and coequalizers.
end Colimits

end CategoryTheory.Limits
