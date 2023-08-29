/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.Logic.Equiv.Fin

#align_import category_theory.limits.constructions.finite_products_of_binary_products from "leanprover-community/mathlib"@"ac3ae212f394f508df43e37aa093722fa9b65d31"

/-!
# Constructing finite products from binary products and terminal.

If a category has binary products and a terminal object then it has finite products.
If a functor preserves binary products and the terminal object then it preserves finite products.

# TODO

Provide the dual results.
Show the analogous results for functors which reflect or create (co)limits.
-/


universe v v' u u'

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace CategoryTheory

variable {J : Type v} [SmallCategory J]

variable {C : Type u} [Category.{v} C]

variable {D : Type u'} [Category.{v'} D]

/--
Given `n+1` objects of `C`, a fan for the last `n` with point `c₁.pt` and
a binary fan on `c₁.pt` and `f 0`, we can build a fan for all `n+1`.

In `extendFanIsLimit` we show that if the two given fans are limits, then this fan is also a
limit.
-/
@[simps!] -- Porting note: removed semi-reducible config
def extendFan {n : ℕ} {f : Fin (n + 1) → C} (c₁ : Fan fun i : Fin n => f i.succ)
    (c₂ : BinaryFan (f 0) c₁.pt) : Fan f :=
  Fan.mk c₂.pt
    (by
      refine' Fin.cases _ _
      -- ⊢ c₂.pt ⟶ f 0
      · apply c₂.fst
        -- 🎉 no goals
      · intro i
        -- ⊢ c₂.pt ⟶ f (Fin.succ i)
        apply c₂.snd ≫ c₁.π.app ⟨i⟩)
        -- 🎉 no goals
#align category_theory.extend_fan CategoryTheory.extendFan

/-- Show that if the two given fans in `extendFan` are limits, then the constructed fan is also a
limit.
-/
def extendFanIsLimit {n : ℕ} (f : Fin (n + 1) → C) {c₁ : Fan fun i : Fin n => f i.succ}
    {c₂ : BinaryFan (f 0) c₁.pt} (t₁ : IsLimit c₁) (t₂ : IsLimit c₂) : IsLimit (extendFan c₁ c₂)
    where
  lift s := by
    apply (BinaryFan.IsLimit.lift' t₂ (s.π.app ⟨0⟩) _).1
    -- ⊢ ((Functor.const (Discrete (Fin (n + 1)))).obj s.pt).obj { as := 0 } ⟶ c₁.pt
    apply t₁.lift ⟨_, Discrete.natTrans fun ⟨i⟩ => s.π.app ⟨i.succ⟩⟩
    -- 🎉 no goals
  fac := fun s ⟨j⟩ => by
    refine' Fin.inductionOn j ?_ ?_
    · apply (BinaryFan.IsLimit.lift' t₂ _ _).2.1
      -- 🎉 no goals
    · rintro i -
      -- ⊢ (fun s =>
      dsimp only [extendFan_π_app]
      -- ⊢ ↑(BinaryFan.IsLimit.lift' t₂ (NatTrans.app s.π { as := 0 }) (IsLimit.lift t₁ …
      rw [Fin.cases_succ, ← assoc, (BinaryFan.IsLimit.lift' t₂ _ _).2.2, t₁.fac]
      -- ⊢ NatTrans.app { pt := s.pt, π := Discrete.natTrans fun x => NatTrans.app s.π  …
      rfl
      -- 🎉 no goals
  uniq s m w := by
    apply BinaryFan.IsLimit.hom_ext t₂
    · rw [(BinaryFan.IsLimit.lift' t₂ _ _).2.1]
      -- ⊢ m ≫ BinaryFan.fst c₂ = NatTrans.app s.π { as := 0 }
      apply w ⟨0⟩
      -- 🎉 no goals
    · rw [(BinaryFan.IsLimit.lift' t₂ _ _).2.2]
      -- ⊢ m ≫ BinaryFan.snd c₂ =
      apply t₁.uniq ⟨_, _⟩
      -- ⊢ ∀ (j : Discrete (Fin n)),
      rintro ⟨j⟩
      -- ⊢ (m ≫ BinaryFan.snd c₂) ≫ NatTrans.app c₁.π { as := j } =
      rw [assoc]
      -- ⊢ m ≫ BinaryFan.snd c₂ ≫ NatTrans.app c₁.π { as := j } =
      dsimp only [Discrete.natTrans_app]
      -- ⊢ m ≫ BinaryFan.snd c₂ ≫ NatTrans.app c₁.π { as := j } = NatTrans.app s.π { as …
      rw [← w ⟨j.succ⟩]
      -- ⊢ m ≫ BinaryFan.snd c₂ ≫ NatTrans.app c₁.π { as := j } = m ≫ NatTrans.app (ext …
      dsimp only [extendFan_π_app]
      -- ⊢ m ≫ BinaryFan.snd c₂ ≫ NatTrans.app c₁.π { as := j } = m ≫ Fin.cases (Binary …
      rw [Fin.cases_succ]
      -- 🎉 no goals
#align category_theory.extend_fan_is_limit CategoryTheory.extendFanIsLimit

section

variable [HasBinaryProducts C] [HasTerminal C]

/-- If `C` has a terminal object and binary products, then it has a product for objects indexed by
`Fin n`.
This is a helper lemma for `hasFiniteProductsOfHasBinaryAndTerminal`, which is more general
than this.
-/
private theorem hasProduct_fin : ∀ (n : ℕ) (f : Fin n → C), HasProduct f
  | 0 => fun f => by
    letI : HasLimitsOfShape (Discrete (Fin 0)) C :=
      hasLimitsOfShape_of_equivalence (Discrete.equivalence.{0} finZeroEquiv'.symm)
    infer_instance
    -- 🎉 no goals
  | n + 1 => fun f => by
    haveI := hasProduct_fin n
    -- ⊢ HasProduct f
    apply HasLimit.mk ⟨_, extendFanIsLimit f (limit.isLimit _) (limit.isLimit _)⟩
    -- 🎉 no goals

/-- If `C` has a terminal object and binary products, then it has finite products. -/
theorem hasFiniteProducts_of_has_binary_and_terminal : HasFiniteProducts C := by
  refine' ⟨fun n => ⟨fun K => _⟩⟩
  -- ⊢ HasLimit K
  letI := hasProduct_fin n fun n => K.obj ⟨n⟩
  -- ⊢ HasLimit K
  let that : (Discrete.functor fun n => K.obj ⟨n⟩) ≅ K := Discrete.natIso fun ⟨i⟩ => Iso.refl _
  -- ⊢ HasLimit K
  apply @hasLimitOfIso _ _ _ _ _ _ this that
  -- 🎉 no goals
#align category_theory.has_finite_products_of_has_binary_and_terminal CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal

end

section Preserves

variable (F : C ⥤ D)

variable [PreservesLimitsOfShape (Discrete WalkingPair) F]

variable [PreservesLimitsOfShape (Discrete.{0} PEmpty) F]

variable [HasFiniteProducts.{v} C]

/-- If `F` preserves the terminal object and binary products, then it preserves products indexed by
`Fin n` for any `n`.
-/
noncomputable def preservesFinOfPreservesBinaryAndTerminal :
    ∀ (n : ℕ) (f : Fin n → C), PreservesLimit (Discrete.functor f) F
  | 0 => fun f => by
    letI : PreservesLimitsOfShape (Discrete (Fin 0)) F :=
      preservesLimitsOfShapeOfEquiv.{0, 0} (Discrete.equivalence finZeroEquiv'.symm) _
    infer_instance
    -- 🎉 no goals
  | n + 1 => by
    haveI := preservesFinOfPreservesBinaryAndTerminal n
    -- ⊢ (f : Fin (n + 1) → C) → PreservesLimit (Discrete.functor f) F
    intro f
    -- ⊢ PreservesLimit (Discrete.functor f) F
    refine'
      preservesLimitOfPreservesLimitCone
        (extendFanIsLimit f (limit.isLimit _) (limit.isLimit _)) _
    apply (isLimitMapConeFanMkEquiv _ _ _).symm _
    -- ⊢ IsLimit (Fan.mk (F.obj (limit.cone (pair (f 0) (limit.cone (Discrete.functor …
    let this :=
      extendFanIsLimit (fun i => F.obj (f i)) (isLimitOfHasProductOfPreservesLimit F _)
        (isLimitOfHasBinaryProductOfPreservesLimit F _ _)
    refine' IsLimit.ofIsoLimit this _
    -- ⊢ extendFan (Fan.mk (F.obj (∏ fun i => f (Fin.succ i))) fun j => F.map (Pi.π ( …
    apply Cones.ext _ _
    -- ⊢ (extendFan (Fan.mk (F.obj (∏ fun i => f (Fin.succ i))) fun j => F.map (Pi.π  …
    apply Iso.refl _
    -- ⊢ ∀ (j : Discrete (Fin (n + 1))), NatTrans.app (extendFan (Fan.mk (F.obj (∏ fu …
    rintro ⟨j⟩
    -- ⊢ NatTrans.app (extendFan (Fan.mk (F.obj (∏ fun i => f (Fin.succ i))) fun j => …
    refine' Fin.inductionOn j ?_ ?_
    -- ⊢ NatTrans.app (extendFan (Fan.mk (F.obj (∏ fun i => f (Fin.succ i))) fun j => …
    · apply (Category.id_comp _).symm
      -- 🎉 no goals
    · rintro i _
      -- ⊢ NatTrans.app (extendFan (Fan.mk (F.obj (∏ fun i => f (Fin.succ i))) fun j => …
      dsimp [extendFan_π_app, Iso.refl_hom, Fan.mk_π_app]
      -- ⊢ F.map prod.snd ≫ F.map (Pi.π (fun i => f (Fin.succ i)) i) = 𝟙 (F.obj (f 0 ⨯  …
      change F.map _ ≫ _ = 𝟙 _ ≫ _
      -- ⊢ F.map prod.snd ≫ F.map (Pi.π (fun i => f (Fin.succ i)) i) = 𝟙 (F.obj (f 0 ⨯  …
      simp only [id_comp, ← F.map_comp]
      -- ⊢ F.map (prod.snd ≫ Pi.π (fun i => f (Fin.succ i)) i) = F.map (BinaryFan.snd ( …
      rfl
      -- 🎉 no goals
#align category_theory.preserves_fin_of_preserves_binary_and_terminal CategoryTheory.preservesFinOfPreservesBinaryAndTerminalₓ -- Porting note: order of universes changed

/-- If `F` preserves the terminal object and binary products, then it preserves limits of shape
`Discrete (Fin n)`.
-/
def preservesShapeFinOfPreservesBinaryAndTerminal (n : ℕ) :
    PreservesLimitsOfShape (Discrete (Fin n)) F where
  preservesLimit {K} := by
    let that : (Discrete.functor fun n => K.obj ⟨n⟩) ≅ K := Discrete.natIso fun ⟨i⟩ => Iso.refl _
    -- ⊢ PreservesLimit K F
    haveI := preservesFinOfPreservesBinaryAndTerminal F n fun n => K.obj ⟨n⟩
    -- ⊢ PreservesLimit K F
    apply preservesLimitOfIsoDiagram F that
    -- 🎉 no goals
#align category_theory.preserves_shape_fin_of_preserves_binary_and_terminal CategoryTheory.preservesShapeFinOfPreservesBinaryAndTerminal

/-- If `F` preserves the terminal object and binary products then it preserves finite products. -/
def preservesFiniteProductsOfPreservesBinaryAndTerminal (J : Type) [Fintype J] :
    PreservesLimitsOfShape (Discrete J) F := by
  classical
    let e := Fintype.equivFin J
    haveI := preservesShapeFinOfPreservesBinaryAndTerminal F (Fintype.card J)
    apply preservesLimitsOfShapeOfEquiv.{0, 0} (Discrete.equivalence e).symm
#align category_theory.preserves_finite_products_of_preserves_binary_and_terminal CategoryTheory.preservesFiniteProductsOfPreservesBinaryAndTerminal

end Preserves

/-- Given `n+1` objects of `C`, a cofan for the last `n` with point `c₁.pt`
and a binary cofan on `c₁.X` and `f 0`, we can build a cofan for all `n+1`.

In `extendCofanIsColimit` we show that if the two given cofans are colimits,
then this cofan is also a colimit.
-/

@[simps!] -- Porting note: removed semireducible config
def extendCofan {n : ℕ} {f : Fin (n + 1) → C} (c₁ : Cofan fun i : Fin n => f i.succ)
    (c₂ : BinaryCofan (f 0) c₁.pt) : Cofan f :=
  Cofan.mk c₂.pt
    (by
      refine' Fin.cases _ _
      -- ⊢ f 0 ⟶ c₂.pt
      · apply c₂.inl
        -- 🎉 no goals
      · intro i
        -- ⊢ f (Fin.succ i) ⟶ c₂.pt
        apply c₁.ι.app ⟨i⟩ ≫ c₂.inr)
        -- 🎉 no goals
#align category_theory.extend_cofan CategoryTheory.extendCofan

/-- Show that if the two given cofans in `extendCofan` are colimits,
then the constructed cofan is also a colimit.
-/
def extendCofanIsColimit {n : ℕ} (f : Fin (n + 1) → C) {c₁ : Cofan fun i : Fin n => f i.succ}
    {c₂ : BinaryCofan (f 0) c₁.pt} (t₁ : IsColimit c₁) (t₂ : IsColimit c₂) :
    IsColimit (extendCofan c₁ c₂) where
  desc s := by
    apply (BinaryCofan.IsColimit.desc' t₂ (s.ι.app ⟨0⟩) _).1
    -- ⊢ c₁.pt ⟶ ((Functor.const (Discrete (Fin (n + 1)))).obj s.pt).obj { as := 0 }
    apply t₁.desc ⟨_, Discrete.natTrans fun i => s.ι.app ⟨i.as.succ⟩⟩
    -- 🎉 no goals
  fac s := by
    rintro ⟨j⟩
    -- ⊢ NatTrans.app (extendCofan c₁ c₂).ι { as := j } ≫ (fun s => ↑(BinaryCofan.IsC …
    refine' Fin.inductionOn j ?_ ?_
    -- ⊢ NatTrans.app (extendCofan c₁ c₂).ι { as := 0 } ≫ (fun s => ↑(BinaryCofan.IsC …
    · apply (BinaryCofan.IsColimit.desc' t₂ _ _).2.1
      -- 🎉 no goals
    · rintro i -
      -- ⊢ NatTrans.app (extendCofan c₁ c₂).ι { as := Fin.succ i } ≫ (fun s => ↑(Binary …
      dsimp only [extendCofan_ι_app]
      -- ⊢ Fin.cases (BinaryCofan.inl c₂) (fun i => NatTrans.app c₁.ι { as := i } ≫ Bin …
      rw [Fin.cases_succ, assoc, (BinaryCofan.IsColimit.desc' t₂ _ _).2.2, t₁.fac]
      -- ⊢ NatTrans.app { pt := s.pt, ι := Discrete.natTrans fun i => NatTrans.app s.ι  …
      rfl
      -- 🎉 no goals
  uniq s m w := by
    apply BinaryCofan.IsColimit.hom_ext t₂
    -- ⊢ BinaryCofan.inl c₂ ≫ m = BinaryCofan.inl c₂ ≫ (fun s => ↑(BinaryCofan.IsColi …
    · rw [(BinaryCofan.IsColimit.desc' t₂ _ _).2.1]
      -- ⊢ BinaryCofan.inl c₂ ≫ m = NatTrans.app s.ι { as := 0 }
      apply w ⟨0⟩
      -- 🎉 no goals
    · rw [(BinaryCofan.IsColimit.desc' t₂ _ _).2.2]
      -- ⊢ BinaryCofan.inr c₂ ≫ m = IsColimit.desc t₁ { pt := s.pt, ι := Discrete.natTr …
      apply t₁.uniq ⟨_, _⟩
      -- ⊢ ∀ (j : Discrete (Fin n)), NatTrans.app c₁.ι j ≫ BinaryCofan.inr c₂ ≫ m = Nat …
      rintro ⟨j⟩
      -- ⊢ NatTrans.app c₁.ι { as := j } ≫ BinaryCofan.inr c₂ ≫ m = NatTrans.app { pt : …
      dsimp only [Discrete.natTrans_app]
      -- ⊢ NatTrans.app c₁.ι { as := j } ≫ BinaryCofan.inr c₂ ≫ m = NatTrans.app s.ι {  …
      rw [← w ⟨j.succ⟩]
      -- ⊢ NatTrans.app c₁.ι { as := j } ≫ BinaryCofan.inr c₂ ≫ m = NatTrans.app (exten …
      dsimp only [extendCofan_ι_app]
      -- ⊢ NatTrans.app c₁.ι { as := j } ≫ BinaryCofan.inr c₂ ≫ m = Fin.cases (BinaryCo …
      rw [Fin.cases_succ, assoc]
      -- 🎉 no goals
#align category_theory.extend_cofan_is_colimit CategoryTheory.extendCofanIsColimit

section

variable [HasBinaryCoproducts C] [HasInitial C]

/--
If `C` has an initial object and binary coproducts, then it has a coproduct for objects indexed by
`Fin n`.
This is a helper lemma for `hasCofiniteProductsOfHasBinaryAndTerminal`, which is more general
than this.
-/
private theorem hasCoproduct_fin : ∀ (n : ℕ) (f : Fin n → C), HasCoproduct f
  | 0 => fun f => by
    letI : HasColimitsOfShape (Discrete (Fin 0)) C :=
      hasColimitsOfShape_of_equivalence (Discrete.equivalence.{0} finZeroEquiv'.symm)
    infer_instance
    -- 🎉 no goals
  | n + 1 => fun f => by
    haveI := hasCoproduct_fin n
    -- ⊢ HasCoproduct f
    apply
      HasColimit.mk ⟨_, extendCofanIsColimit f (colimit.isColimit _) (colimit.isColimit _)⟩

/-- If `C` has an initial object and binary coproducts, then it has finite coproducts. -/
theorem hasFiniteCoproducts_of_has_binary_and_initial : HasFiniteCoproducts C := by
  refine' ⟨fun n => ⟨fun K => _⟩⟩
  -- ⊢ HasColimit K
  letI := hasCoproduct_fin n fun n => K.obj ⟨n⟩
  -- ⊢ HasColimit K
  let that : K ≅ Discrete.functor fun n => K.obj ⟨n⟩ := Discrete.natIso fun ⟨i⟩ => Iso.refl _
  -- ⊢ HasColimit K
  apply @hasColimitOfIso _ _ _ _ _ _ this that
  -- 🎉 no goals
#align category_theory.has_finite_coproducts_of_has_binary_and_initial CategoryTheory.hasFiniteCoproducts_of_has_binary_and_initial

end

section Preserves

variable (F : C ⥤ D)

variable [PreservesColimitsOfShape (Discrete WalkingPair) F]

variable [PreservesColimitsOfShape (Discrete.{0} PEmpty) F]

variable [HasFiniteCoproducts.{v} C]

/-- If `F` preserves the initial object and binary coproducts, then it preserves products indexed by
`Fin n` for any `n`.
-/
noncomputable def preservesFinOfPreservesBinaryAndInitial :
    ∀ (n : ℕ) (f : Fin n → C), PreservesColimit (Discrete.functor f) F
  | 0 => fun f => by
    letI : PreservesColimitsOfShape (Discrete (Fin 0)) F :=
      preservesColimitsOfShapeOfEquiv.{0, 0} (Discrete.equivalence finZeroEquiv'.symm) _
    infer_instance
    -- 🎉 no goals
  | n + 1 => by
    haveI := preservesFinOfPreservesBinaryAndInitial n
    -- ⊢ (f : Fin (n + 1) → C) → PreservesColimit (Discrete.functor f) F
    intro f
    -- ⊢ PreservesColimit (Discrete.functor f) F
    refine'
      preservesColimitOfPreservesColimitCocone
        (extendCofanIsColimit f (colimit.isColimit _) (colimit.isColimit _)) _
    apply (isColimitMapCoconeCofanMkEquiv _ _ _).symm _
    -- ⊢ IsColimit (Cofan.mk (F.obj (colimit.cocone (pair (f 0) (colimit.cocone (Disc …
    let this :=
      extendCofanIsColimit (fun i => F.obj (f i))
        (isColimitOfHasCoproductOfPreservesColimit F _)
        (isColimitOfHasBinaryCoproductOfPreservesColimit F _ _)
    refine' IsColimit.ofIsoColimit this _
    -- ⊢ extendCofan (Cofan.mk (F.obj (∐ fun i => f (Fin.succ i))) fun j => F.map (Si …
    apply Cocones.ext _ _
    -- ⊢ (extendCofan (Cofan.mk (F.obj (∐ fun i => f (Fin.succ i))) fun j => F.map (S …
    apply Iso.refl _
    -- ⊢ ∀ (j : Discrete (Fin (n + 1))), NatTrans.app (extendCofan (Cofan.mk (F.obj ( …
    rintro ⟨j⟩
    -- ⊢ NatTrans.app (extendCofan (Cofan.mk (F.obj (∐ fun i => f (Fin.succ i))) fun  …
    refine' Fin.inductionOn j ?_ ?_
    -- ⊢ NatTrans.app (extendCofan (Cofan.mk (F.obj (∐ fun i => f (Fin.succ i))) fun  …
    · apply Category.comp_id
      -- 🎉 no goals
    · rintro i _
      -- ⊢ NatTrans.app (extendCofan (Cofan.mk (F.obj (∐ fun i => f (Fin.succ i))) fun  …
      dsimp [extendCofan_ι_app, Iso.refl_hom, Cofan.mk_ι_app]
      -- ⊢ (F.map (Sigma.ι (fun i => f (Fin.succ i)) i) ≫ F.map coprod.inr) ≫ 𝟙 (F.obj  …
      rw [comp_id, ← F.map_comp]
      -- 🎉 no goals
#align category_theory.preserves_fin_of_preserves_binary_and_initial CategoryTheory.preservesFinOfPreservesBinaryAndInitialₓ  -- Porting note: order of universes changed

/-- If `F` preserves the initial object and binary coproducts, then it preserves colimits of shape
`Discrete (Fin n)`.
-/
def preservesShapeFinOfPreservesBinaryAndInitial (n : ℕ) :
    PreservesColimitsOfShape (Discrete (Fin n)) F where
  preservesColimit {K} := by
    let that : (Discrete.functor fun n => K.obj ⟨n⟩) ≅ K := Discrete.natIso fun ⟨i⟩ => Iso.refl _
    -- ⊢ PreservesColimit K F
    haveI := preservesFinOfPreservesBinaryAndInitial F n fun n => K.obj ⟨n⟩
    -- ⊢ PreservesColimit K F
    apply preservesColimitOfIsoDiagram F that
    -- 🎉 no goals
#align category_theory.preserves_shape_fin_of_preserves_binary_and_initial CategoryTheory.preservesShapeFinOfPreservesBinaryAndInitial

/-- If `F` preserves the initial object and binary coproducts then it preserves finite products. -/
def preservesFiniteCoproductsOfPreservesBinaryAndInitial (J : Type) [Fintype J] :
    PreservesColimitsOfShape (Discrete J) F := by
  classical
    let e := Fintype.equivFin J
    haveI := preservesShapeFinOfPreservesBinaryAndInitial F (Fintype.card J)
    apply preservesColimitsOfShapeOfEquiv.{0, 0} (Discrete.equivalence e).symm
#align category_theory.preserves_finite_coproducts_of_preserves_binary_and_initial CategoryTheory.preservesFiniteCoproductsOfPreservesBinaryAndInitial

end Preserves

end CategoryTheory
