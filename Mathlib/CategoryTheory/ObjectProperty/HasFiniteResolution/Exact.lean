/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.HasFiniteResolution.Basic

/-!
# The short exact sequences of objects admitting finite `P`-resolutions

This file proves that in a short exact sequence `0 → M₁ → M₂ → M₃ → 0`, if any two of these modules
have a finite `P`-resolution, then so does the third .
-/

public section

universe v u

namespace CategoryTheory

open Category Limits ZeroObject Preadditive

namespace ObjectProperty

variable {A : Type u} [Category.{v} A] [Abelian A]

theorem prop_biprod {P : ObjectProperty A} [P.IsClosedUnderBinaryProducts] {X Y : A}
    (hX : P X) (hY : P Y) : P (X ⊞ Y) :=
  P.prop_of_isLimit_binaryFan (BinaryBiproduct.isLimit X Y) hX hY

theorem HasFiniteResolutionOfLength.biprod_right {P : ObjectProperty A}
    [P.IsClosedUnderBinaryProducts] {X Y : A} {n : ℕ}
    (hX : P.HasFiniteResolutionOfLength X n) (hY : P Y) :
    P.HasFiniteResolutionOfLength (X ⊞ Y) n := by
  cases hX with
  | zero X hX => exact HasFiniteResolutionOfLength.zero _ (prop_biprod hX hY)
  | succ S n hS h₂ h₁ =>
      refine HasFiniteResolutionOfLength.succ
        (ShortComplex.mk (biprod.lift S.f 0) (biprod.map S.g (𝟙 Y)) (by ext <;> simp [S.zero])) n
          ?_ (prop_biprod h₂ hY) h₁
      have := hS.mono_f
      have := hS.epi_g
      refine ⟨ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι' _ _ fun {W} a ha ↦ ?_)⟩
      have hker : (a ≫ biprod.fst) ≫ S.g = 0 := by simpa using ha =≫ biprod.fst
      refine ⟨hS.exact.lift (a ≫ biprod.fst) hker, biprod.hom_ext _ _ (by simp) ?_⟩
      simpa using ha.symm =≫ biprod.snd

theorem _root_.CategoryTheory.ShortComplex.ShortExact.pullback
    {S : ShortComplex A} (hS : S.ShortExact) {Y : A} (t : Y ⟶ S.X₃) :
    (ShortComplex.mk (pullback.lift S.f 0 (by rw [S.zero, zero_comp])) (pullback.snd S.g t)
      (by rw [pullback.lift_snd])).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have : Mono (pullback.lift (g := t) S.f (0 : S.X₁ ⟶ Y) (by rw [S.zero, zero_comp])) :=
    mono_of_mono_fac (pullback.lift_fst S.f 0 _)
  have hker {W : A} (a : W ⟶ Limits.pullback S.g t) (ha : a ≫ pullback.snd S.g t = 0) :
      (a ≫ pullback.fst S.g t) ≫ S.g = 0 := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ha, zero_comp]
  refine ⟨ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι' _ _ fun {W} a ha ↦ ?_)⟩
  refine ⟨hS.exact.lift (a ≫ pullback.fst S.g t) (hker a ha), pullback.hom_ext ?_ ?_⟩
  · simp [pullback.lift_fst]
  · simpa [pullback.lift_snd] using ha.symm

theorem _root_.CategoryTheory.ShortComplex.ShortExact.pullback_symm
    {S : ShortComplex A} (hS : S.ShortExact) {Y : A} (t : Y ⟶ S.X₃) :
    (ShortComplex.mk (pullback.lift 0 S.f (by rw [zero_comp, S.zero]))
      (pullback.fst t S.g) (by rw [pullback.lift_fst])).ShortExact := by
  refine ShortComplex.shortExact_of_iso ?_ (hS.pullback t)
  refine ShortComplex.isoMk (Iso.refl _) (pullbackSymmetry S.g t) (Iso.refl _)
    (pullback.hom_ext ?_ ?_) (by simp)
      <;> simp only [Iso.refl_hom, Category.id_comp, Category.assoc]
  · rw [pullbackSymmetry_hom_comp_fst, pullback.lift_fst, pullback.lift_snd]
  · rw [pullbackSymmetry_hom_comp_snd, pullback.lift_fst, pullback.lift_snd]

theorem horseshoe_middle_shortExact {X₁ X₂ X₃ F₁ K₃ F₃ : A}
    {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} (p₁ : F₁ ⟶ X₁) {i₃ : K₃ ⟶ F₃} {p₃ : F₃ ⟶ X₃}
    {wS : f ≫ g = 0} {wT₃ : i₃ ≫ p₃ = 0} [Epi p₁]
    (hS : (ShortComplex.mk f g wS).ShortExact) (hS₃ : (ShortComplex.mk i₃ p₃ wT₃).ShortExact)
    (l : F₃ ⟶ X₂) (t : K₃ ⟶ X₁) (hl : l ≫ g = p₃) (ht : t ≫ f = i₃ ≫ l) :
    (ShortComplex.mk
      (biprod.lift (pullback.fst p₁ (- t)) (pullback.snd p₁ (- t) ≫ i₃)) (biprod.desc (p₁ ≫ f) l)
        (by simp [biprod.lift_desc, pullback.condition_assoc, ht])).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have := hS₃.mono_f
  have := hS₃.epi_g
  let m : F₁ ⊞ F₃ ⟶ X₂ := biprod.desc (p₁ ≫ f) l
  let S : ShortComplex A := ShortComplex.mk
    (biprod.lift (pullback.fst p₁ (- t)) (pullback.snd p₁ (- t) ≫ i₃)) m
      (by simp [m, biprod.lift_desc, pullback.condition_assoc, ht])
  have hker₃ {W : A} (a : W ⟶ F₁ ⊞ F₃) (ha : a ≫ m = 0) : (a ≫ biprod.snd) ≫ p₃ = 0 := by
    simpa [m, biprod.desc_eq, comp_add, add_comp, wS, hl] using ha =≫ g
  have mk_hpb {W : A} (a : W ⟶ F₁ ⊞ F₃) (ha : a ≫ m = 0)
      (k₃ : W ⟶ K₃) (hk₃ : k₃ ≫ i₃ = a ≫ biprod.snd) :
      (a ≫ biprod.fst) ≫ p₁ = k₃ ≫ (- t) := by
    apply (cancel_mono f).1
    trans - (a ≫ biprod.snd) ≫ l
    · simpa [m, biprod.desc_eq, comp_add, eq_neg_iff_add_eq_zero, add_comm] using ha
    · simp [← hk₃, ht]
  have : Mono S.f := by
    dsimp [S]
    refine mono_of_cancel_zero _ fun {W} a ha ↦ ?_
    apply pullback.hom_ext
    · simpa using ha =≫ biprod.fst
    · simpa [← cancel_mono i₃] using ha =≫ biprod.snd
  have : Epi m := by
    let φ : ShortComplex.mk biprod.inl biprod.snd
        (BinaryBicone.inl_snd (BinaryBiproduct.bicone F₁ F₃)) ⟶ ShortComplex.mk f g wS :=
      ⟨p₁, biprod.desc (p₁ ≫ f) l, p₃, by simp, by ext <;> simp [hl, Category.assoc, wS]⟩
    exact ShortComplex.epi_τ₂_of_exact_of_epi φ hS.exact
  refine ⟨ShortComplex.exact_of_f_is_kernel S (KernelFork.IsLimit.ofι' S.f S.zero fun {W} a h ↦ ?_)⟩
  let k₃ : W ⟶ K₃ := hS₃.exact.lift (a ≫ biprod.snd) (hker₃ a h)
  have hk₃ : k₃ ≫ i₃ = a ≫ biprod.snd := hS₃.exact.lift_f _ _
  refine ⟨pullback.lift (a ≫ biprod.fst) k₃ (mk_hpb a h k₃ hk₃), ?_⟩
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, biprod.lift_snd, ← Category.assoc, pullback.lift_snd, hk₃]

namespace HasFiniteResolution

private theorem middle_of_right {P : ObjectProperty A} [P.IsClosedUnderBinaryProducts]
    [P.IsClosedUnderIsomorphisms] (hP : P ≤ isProjective A) {S : ShortComplex A}
    (hS : S.ShortExact) {n : ℕ} (h₁ : P.HasFiniteResolutionOfLength S.X₁ n)
    (h₃ : P S.X₃) : P.HasFiniteResolution S.X₂ := by
  have : Projective S.X₃ := hP _ h₃
  exact ⟨n, (h₁.biprod_right h₃).of_iso hS.splittingOfProjective.isoBinaryBiproduct.symm⟩

/-- In a short exact sequence, if the left and right objects have finite `P`-resolutions,
then so does the middle object. -/
theorem of_shortExact_of_left_of_right {P : ObjectProperty A}
    [P.IsClosedUnderBinaryProducts] [P.IsClosedUnderIsomorphisms]
    (hP : P ≤ isProjective A) {S : ShortComplex A} (hS : S.ShortExact)
    [P.HasFiniteResolution S.X₁] [P.HasFiniteResolution S.X₃] :
    P.HasFiniteResolution S.X₂ := by
  rcases S with @⟨X₁, X₂, X₃, f, g, w⟩
  obtain ⟨_, h₁⟩ := HasFiniteResolution.out P X₁
  induction h₁ generalizing X₂ X₃ with
  | zero X₁ hX₁ =>
      obtain ⟨_, h₃⟩ := HasFiniteResolution.out P X₃
      have := hS.mono_f
      have := hS.epi_g
      cases h₃ with
      | zero X₃ hX₃ => exact middle_of_right hP hS (HasFiniteResolutionOfLength.zero X₁ hX₁) hX₃
      | succ T₃ _ hS₃ hF₃ hK₃ =>
          have : Projective T₃.X₂ := hP T₃.X₂ hF₃
          let l : T₃.X₂ ⟶ X₂ := Projective.factorThru T₃.g g
          have hl : l ≫ g = T₃.g := Projective.factorThru_comp T₃.g g
          let t : T₃.X₁ ⟶ X₁ := hS.exact.lift (T₃.f ≫ l) (by rw [Category.assoc, hl, T₃.zero])
          have ht : t ≫ f = T₃.f ≫ l := hS.exact.lift_f _ _
          have : P.HasFiniteResolution T₃.X₁ := hK₃.hasFiniteResolution
          have : P.HasFiniteResolution (pullback (𝟙 X₁) (- t)) :=
            HasFiniteResolution.of_iso (asIso (pullback.snd (𝟙 X₁) (- t))).symm
          exact HasFiniteResolution.of_shortExact
            (horseshoe_middle_shortExact (𝟙 X₁) hS hS₃ l t hl ht) (prop_biprod hX₁ hF₃)
  | succ T₁ n hS₁ hF₁ hK₁ ih =>
      obtain ⟨_, h₃⟩ := HasFiniteResolution.out P X₃
      have := hS.mono_f
      have := hS.epi_g
      cases h₃ with
      | zero X₃ hX₃ => exact middle_of_right hP hS (hK₁.succ T₁ n hS₁ hF₁) hX₃
      | succ T₃ _ hS₃ hF₃ hK₃ =>
          have : Projective T₃.X₂ := hP T₃.X₂ hF₃
          let l : T₃.X₂ ⟶ X₂ := Projective.factorThru T₃.g g
          have hl : l ≫ g = T₃.g := Projective.factorThru_comp T₃.g g
          let t : T₃.X₁ ⟶ T₁.X₃ := hS.exact.lift (T₃.f ≫ l) (by rw [Category.assoc, hl, T₃.zero])
          have ht : t ≫ f = T₃.f ≫ l := hS.exact.lift_f _ _
          have : P.HasFiniteResolution T₁.X₁ := hK₁.hasFiniteResolution
          have : P.HasFiniteResolution T₃.X₁ := hK₃.hasFiniteResolution
          have : P.HasFiniteResolution (pullback T₁.g (- t)) :=
            ih (pullback.lift T₁.f 0 (by rw [T₁.zero, zero_comp]))
              (pullback.snd T₁.g (- t)) (by rw [pullback.lift_snd]) (hS₁.pullback (- t))
          have := hS₁.epi_g
          exact HasFiniteResolution.of_shortExact
            (horseshoe_middle_shortExact T₁.g hS hS₃ l t hl ht) (prop_biprod hF₁ hF₃)

/-- In a short exact sequence, if the left and middle objects have finite `P`-resolutions,
then so does the right object. -/
theorem of_shortExact_of_left_of_middle {P : ObjectProperty A}
    [P.IsClosedUnderBinaryProducts] [P.IsClosedUnderIsomorphisms]
    (hP : P ≤ isProjective A) {S : ShortComplex A} (hS : S.ShortExact)
    [P.HasFiniteResolution S.X₁] [P.HasFiniteResolution S.X₂] :
    P.HasFiniteResolution S.X₃ := by
  rcases S with @⟨X₁, X₂, X₃, f, g, w⟩
  obtain ⟨_, h₂⟩ := HasFiniteResolution.out P X₂
  cases h₂ with
  | zero X₂ hX₂ => exact HasFiniteResolution.of_shortExact hS hX₂
  | succ T₂ _ hS₂ hF₂ hK₂ =>
    have : P.HasFiniteResolution (pullback T₂.g f) := by
      have : P.HasFiniteResolution T₂.X₁ := hK₂.hasFiniteResolution
      exact of_shortExact_of_left_of_right hP (hS₂.pullback f)
    have := hS₂.epi_g
    have h : (ShortComplex.mk (pullback.fst T₂.g f) (T₂.g ≫ g) (by
        rw [← Category.assoc, pullback.condition, Category.assoc, w, comp_zero])).ShortExact := by
      have := hS.mono_f
      have := hS.epi_g
      refine ⟨ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι' _ _ fun {W} a ha ↦ ?_)⟩
      have hker : (a ≫ T₂.g) ≫ g = 0 := by simpa [Category.assoc] using ha
      exact ⟨pullback.lift a (hS.exact.lift (a ≫ T₂.g) hker) (hS.exact.lift_f _ _).symm,
        pullback.lift_fst a _ _⟩
    simpa using HasFiniteResolution.of_shortExact h hF₂

private theorem left_of_right {P : ObjectProperty A} [P.IsClosedUnderBinaryProducts]
    [P.IsClosedUnderIsomorphisms] (hP : P ≤ isProjective A) {S : ShortComplex A}
    (hS : S.ShortExact) (h₃ : P S.X₃) [P.HasFiniteResolution S.X₂] :
    P.HasFiniteResolution S.X₁ := by
  have : Projective S.X₃ := hP _ h₃
  let e : S.X₂ ≅ S.X₁ ⊞ S.X₃ := hS.splittingOfProjective.isoBinaryBiproduct
  have : P.HasFiniteResolution (S.X₁ ⊞ S.X₃) := HasFiniteResolution.of_iso e
  have : P.HasFiniteResolution S.X₃ := HasFiniteResolution.of_property h₃
  exact of_shortExact_of_left_of_middle hP
    (S := ⟨biprod.inr, biprod.fst, (BinaryBicone.inr_fst (BinaryBiproduct.bicone S.X₁ S.X₃))⟩)
      (ShortComplex.Splitting.mk biprod.snd biprod.inl).shortExact

/-- In a short exact sequence, if the middle and right objects have finite `P`-resolutions,
then so does the left object. -/
theorem of_shortExact_of_middle_of_right {P : ObjectProperty A}
    [P.IsClosedUnderBinaryProducts] [P.IsClosedUnderIsomorphisms]
    (hP : P ≤ isProjective A) {S : ShortComplex A} (hS : S.ShortExact)
    [P.HasFiniteResolution S.X₂] [P.HasFiniteResolution S.X₃] : P.HasFiniteResolution S.X₁ := by
  rcases S with @⟨X₁, X₂, X₃, f, g, w⟩
  obtain ⟨_, h₃⟩ := HasFiniteResolution.out P X₃
  cases h₃ with
  | zero _ hX₃ => exact left_of_right hP hS hX₃
  | succ T₃ _ hS₃ hF₃ hK₃ =>
    have : P.HasFiniteResolution (pullback T₃.g g) := by
      have : P.HasFiniteResolution T₃.X₁ := hK₃.hasFiniteResolution
      exact of_shortExact_of_left_of_right hP (hS₃.pullback g)
    simpa using left_of_right hP (hS.pullback_symm T₃.g) hF₃

end HasFiniteResolution

end ObjectProperty

end CategoryTheory
