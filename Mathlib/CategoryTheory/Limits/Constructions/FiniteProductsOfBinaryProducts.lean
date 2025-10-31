/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Constructing finite products from binary products and terminal.

If a category has binary products and a terminal object then it has finite products.
If a functor preserves binary products and the terminal object then it preserves finite products.

## TODO

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
@[simps!]
def extendFan {n : ℕ} {f : Fin (n + 1) → C} (c₁ : Fan fun i : Fin n => f i.succ)
    (c₂ : BinaryFan (f 0) c₁.pt) : Fan f :=
  Fan.mk c₂.pt
    (by
      refine Fin.cases ?_ ?_
      · apply c₂.fst
      · intro i
        apply c₂.snd ≫ c₁.π.app ⟨i⟩)

/-- Show that if the two given fans in `extendFan` are limits, then the constructed fan is also a
limit.
-/
def extendFanIsLimit {n : ℕ} (f : Fin (n + 1) → C) {c₁ : Fan fun i : Fin n => f i.succ}
    {c₂ : BinaryFan (f 0) c₁.pt} (t₁ : IsLimit c₁) (t₂ : IsLimit c₂) :
    IsLimit (extendFan c₁ c₂) where
  lift s := by
    apply (BinaryFan.IsLimit.lift' t₂ (s.π.app ⟨0⟩) _).1
    apply t₁.lift ⟨_, Discrete.natTrans fun ⟨i⟩ => s.π.app ⟨i.succ⟩⟩
  fac := fun s ⟨j⟩ => by
    refine Fin.inductionOn j ?_ ?_
    · apply (BinaryFan.IsLimit.lift' t₂ _ _).2.1
    · rintro i -
      dsimp only [extendFan_π_app]
      rw [Fin.cases_succ, ← assoc, (BinaryFan.IsLimit.lift' t₂ _ _).2.2, t₁.fac]
      rfl
  uniq s m w := by
    apply BinaryFan.IsLimit.hom_ext t₂
    · rw [(BinaryFan.IsLimit.lift' t₂ _ _).2.1]
      apply w ⟨0⟩
    · rw [(BinaryFan.IsLimit.lift' t₂ _ _).2.2]
      apply t₁.uniq ⟨_, _⟩
      rintro ⟨j⟩
      rw [assoc]
      dsimp only [Discrete.natTrans_app]
      rw [← w ⟨j.succ⟩]
      dsimp only [extendFan_π_app]
      rw [Fin.cases_succ]

section

variable [HasBinaryProducts C] [HasTerminal C]

/-- If `C` has a terminal object and binary products, then it has a product for objects indexed by
`Fin n`.
This is a helper lemma for `hasFiniteProductsOfHasBinaryAndTerminal`, which is more general
than this.
-/
private theorem hasProduct_fin : ∀ (n : ℕ) (f : Fin n → C), HasProduct f
  | 0 => fun _ =>
    letI : HasLimitsOfShape (Discrete (Fin 0)) C :=
      hasLimitsOfShape_of_equivalence (Discrete.equivalence.{0} finZeroEquiv'.symm)
    inferInstance
  | n + 1 => fun f =>
    haveI := hasProduct_fin n
    HasLimit.mk ⟨_, extendFanIsLimit f (limit.isLimit _) (limit.isLimit _)⟩

/-- If `C` has a terminal object and binary products, then it has finite products. -/
theorem hasFiniteProducts_of_has_binary_and_terminal : HasFiniteProducts C :=
  ⟨fun n => ⟨fun K => by
    let that : (Discrete.functor fun n => K.obj ⟨n⟩) ≅ K := Discrete.natIso fun ⟨_⟩ => Iso.refl _
    rw [← hasLimit_iff_of_iso that]
    apply hasProduct_fin⟩⟩


end

section Preserves

variable (F : C ⥤ D)
variable [PreservesLimitsOfShape (Discrete WalkingPair) F]
variable [PreservesLimitsOfShape (Discrete.{0} PEmpty) F]
variable [HasFiniteProducts.{v} C]

/-- If `F` preserves the terminal object and binary products, then it preserves products indexed by
`Fin n` for any `n`.
-/
lemma preservesFinOfPreservesBinaryAndTerminal :
    ∀ (n : ℕ) (f : Fin n → C), PreservesLimit (Discrete.functor f) F
  | 0 => fun f => by
    letI : PreservesLimitsOfShape (Discrete (Fin 0)) F :=
      preservesLimitsOfShape_of_equiv.{0, 0} (Discrete.equivalence finZeroEquiv'.symm) _
    infer_instance
  | n + 1 => by
    haveI := preservesFinOfPreservesBinaryAndTerminal n
    intro f
    apply
      preservesLimit_of_preserves_limit_cone
        (extendFanIsLimit f (limit.isLimit _) (limit.isLimit _)) _
    apply (isLimitMapConeFanMkEquiv _ _ _).symm _
    let this :=
      extendFanIsLimit (fun i => F.obj (f i)) (isLimitOfHasProductOfPreservesLimit F _)
        (isLimitOfHasBinaryProductOfPreservesLimit F _ _)
    refine IsLimit.ofIsoLimit this ?_
    apply Cones.ext _ _
    · apply Iso.refl _
    rintro ⟨j⟩
    refine Fin.inductionOn j ?_ ?_
    · apply (Category.id_comp _).symm
    · rintro i _
      dsimp [extendFan_π_app, Iso.refl_hom, Fan.mk_π_app]
      change F.map _ ≫ _ = 𝟙 _ ≫ _
      simp only [id_comp, ← F.map_comp]
      rfl

/-- If `F` preserves the terminal object and binary products then it preserves finite products. -/
lemma Limits.PreservesFiniteProducts.of_preserves_binary_and_terminal :
    PreservesFiniteProducts F where
  preserves n := by
    refine ⟨fun {K} ↦ ?_⟩
    let that : (Discrete.functor fun n => K.obj ⟨n⟩) ≅ K := Discrete.natIso fun ⟨i⟩ => Iso.refl _
    haveI := preservesFinOfPreservesBinaryAndTerminal F n fun n => K.obj ⟨n⟩
    apply preservesLimit_of_iso_diagram F that

@[deprecated PreservesFiniteProducts.of_preserves_binary_and_terminal (since := "2025-04-22")]
lemma preservesShape_fin_of_preserves_binary_and_terminal (n : ℕ) :
    PreservesLimitsOfShape (Discrete (Fin n)) F :=
  have : PreservesFiniteProducts F := .of_preserves_binary_and_terminal _; inferInstance

end Preserves

/-- Given `n+1` objects of `C`, a cofan for the last `n` with point `c₁.pt`
and a binary cofan on `c₁.X` and `f 0`, we can build a cofan for all `n+1`.

In `extendCofanIsColimit` we show that if the two given cofans are colimits,
then this cofan is also a colimit.
-/
@[simps!]
def extendCofan {n : ℕ} {f : Fin (n + 1) → C} (c₁ : Cofan fun i : Fin n => f i.succ)
    (c₂ : BinaryCofan (f 0) c₁.pt) : Cofan f :=
  Cofan.mk c₂.pt
    (by
      refine Fin.cases ?_ ?_
      · apply c₂.inl
      · intro i
        apply c₁.ι.app ⟨i⟩ ≫ c₂.inr)

/-- Show that if the two given cofans in `extendCofan` are colimits,
then the constructed cofan is also a colimit.
-/
def extendCofanIsColimit {n : ℕ} (f : Fin (n + 1) → C) {c₁ : Cofan fun i : Fin n => f i.succ}
    {c₂ : BinaryCofan (f 0) c₁.pt} (t₁ : IsColimit c₁) (t₂ : IsColimit c₂) :
    IsColimit (extendCofan c₁ c₂) where
  desc s := by
    apply (BinaryCofan.IsColimit.desc' t₂ (s.ι.app ⟨0⟩) _).1
    apply t₁.desc ⟨_, Discrete.natTrans fun i => s.ι.app ⟨i.as.succ⟩⟩
  fac s := by
    rintro ⟨j⟩
    refine Fin.inductionOn j ?_ ?_
    · apply (BinaryCofan.IsColimit.desc' t₂ _ _).2.1
    · rintro i -
      dsimp only [extendCofan_ι_app]
      rw [Fin.cases_succ, assoc, (BinaryCofan.IsColimit.desc' t₂ _ _).2.2, t₁.fac]
      rfl
  uniq s m w := by
    apply BinaryCofan.IsColimit.hom_ext t₂
    · rw [(BinaryCofan.IsColimit.desc' t₂ _ _).2.1]
      apply w ⟨0⟩
    · rw [(BinaryCofan.IsColimit.desc' t₂ _ _).2.2]
      apply t₁.uniq ⟨_, _⟩
      rintro ⟨j⟩
      dsimp only [Discrete.natTrans_app]
      rw [← w ⟨j.succ⟩]
      dsimp only [extendCofan_ι_app]
      rw [Fin.cases_succ, assoc]

section

variable [HasBinaryCoproducts C] [HasInitial C]

/--
If `C` has an initial object and binary coproducts, then it has a coproduct for objects indexed by
`Fin n`.
This is a helper lemma for `hasCofiniteProductsOfHasBinaryAndTerminal`, which is more general
than this.
-/
private theorem hasCoproduct_fin : ∀ (n : ℕ) (f : Fin n → C), HasCoproduct f
  | 0 => fun _ =>
    letI : HasColimitsOfShape (Discrete (Fin 0)) C :=
      hasColimitsOfShape_of_equivalence (Discrete.equivalence.{0} finZeroEquiv'.symm)
    inferInstance
  | n + 1 => fun f =>
    haveI := hasCoproduct_fin n
    HasColimit.mk ⟨_, extendCofanIsColimit f (colimit.isColimit _) (colimit.isColimit _)⟩

/-- If `C` has an initial object and binary coproducts, then it has finite coproducts. -/
theorem hasFiniteCoproducts_of_has_binary_and_initial : HasFiniteCoproducts C :=
  ⟨fun n => ⟨fun K => by
    let that : K ≅ Discrete.functor fun n => K.obj ⟨n⟩ := Discrete.natIso fun ⟨_⟩ => Iso.refl _
    rw [hasColimit_iff_of_iso that]
    apply hasCoproduct_fin⟩⟩

end

section Preserves

variable (F : C ⥤ D)
variable [PreservesColimitsOfShape (Discrete WalkingPair) F]
variable [PreservesColimitsOfShape (Discrete.{0} PEmpty) F]
variable [HasFiniteCoproducts.{v} C]

/-- If `F` preserves the initial object and binary coproducts, then it preserves products indexed by
`Fin n` for any `n`.
-/
lemma preserves_fin_of_preserves_binary_and_initial :
    ∀ (n : ℕ) (f : Fin n → C), PreservesColimit (Discrete.functor f) F
  | 0 => fun f => by
    letI : PreservesColimitsOfShape (Discrete (Fin 0)) F :=
      preservesColimitsOfShape_of_equiv.{0, 0} (Discrete.equivalence finZeroEquiv'.symm) _
    infer_instance
  | n + 1 => by
    haveI := preserves_fin_of_preserves_binary_and_initial n
    intro f
    apply
      preservesColimit_of_preserves_colimit_cocone
        (extendCofanIsColimit f (colimit.isColimit _) (colimit.isColimit _)) _
    apply (isColimitMapCoconeCofanMkEquiv _ _ _).symm _
    let this :=
      extendCofanIsColimit (fun i => F.obj (f i))
        (isColimitOfHasCoproductOfPreservesColimit F _)
        (isColimitOfHasBinaryCoproductOfPreservesColimit F _ _)
    refine IsColimit.ofIsoColimit this ?_
    apply Cocones.ext _ _
    · apply Iso.refl _
    rintro ⟨j⟩
    refine Fin.inductionOn j ?_ ?_
    · apply Category.comp_id
    · rintro i _
      dsimp [extendCofan_ι_app, Iso.refl_hom, Cofan.mk_ι_app]
      rw [comp_id, ← F.map_comp]

/-- If `F` preserves the initial object and binary coproducts, then it preserves colimits of shape
`Discrete (Fin n)`.
-/
lemma preservesShape_fin_of_preserves_binary_and_initial (n : ℕ) :
    PreservesColimitsOfShape (Discrete (Fin n)) F where
  preservesColimit {K} := by
    let that : (Discrete.functor fun n => K.obj ⟨n⟩) ≅ K := Discrete.natIso fun ⟨i⟩ => Iso.refl _
    haveI := preserves_fin_of_preserves_binary_and_initial F n fun n => K.obj ⟨n⟩
    apply preservesColimit_of_iso_diagram F that

/-- If `F` preserves the initial object and binary coproducts then it preserves finite products. -/
lemma preservesFiniteCoproductsOfPreservesBinaryAndInitial (J : Type*) [Finite J] :
    PreservesColimitsOfShape (Discrete J) F :=
  let ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have := preservesShape_fin_of_preserves_binary_and_initial F n
  preservesColimitsOfShape_of_equiv (Discrete.equivalence e).symm _

end Preserves

end CategoryTheory
