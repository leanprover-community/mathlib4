import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Tactic.Linarith
import Mathlib.CategoryTheory.Shift.ShiftSequence

namespace CategoryTheory

-- should be moved to CategoryTheory.Shift.Basic
section

open Category

variable (C : Type _) {A A' : Type _} [Category C] [AddMonoid A] [HasShift C A]
  [AddCommGroup A'] [HasShift C A']

noncomputable def shiftFunctorAdd₃' (a₁ a₂ a₃ b : A) (h :  a₁ + a₂ + a₃ = b) :
    shiftFunctor C b ≅ shiftFunctor C a₁ ⋙ shiftFunctor C a₂ ⋙ shiftFunctor C a₃ :=
  shiftFunctorAdd' C (a₁ + a₂) a₃ b h ≪≫ isoWhiskerRight (shiftFunctorAdd C a₁ a₂) _ ≪≫
    Functor.associator _ _ _

variable {C}

lemma shiftFunctorAdd₃'_hom_app (a₁ a₂ a₃ : A) (b : A) (h : a₁ + a₂ + a₃ = b) (a₁₂ : A)
    (h₁₂ : a₁ + a₂ = a₁₂) (X : C) :
    (shiftFunctorAdd₃' C a₁ a₂ a₃ b h).hom.app X =
      (shiftFunctorAdd' C a₁₂ a₃ b (by rw [← h₁₂, h])).hom.app X ≫
        ((shiftFunctorAdd' C a₁ a₂ a₁₂ h₁₂).hom.app X)⟦a₃⟧' := by
  subst h₁₂ h
  simp only [Functor.comp_obj, shiftFunctorAdd₃', shiftFunctorAdd'_eq_shiftFunctorAdd,
    Iso.trans_hom, isoWhiskerRight_hom, NatTrans.comp_app, whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id]

lemma shiftFunctorAdd₃'_inv_app (a₁ a₂ a₃ : A) (b : A) (h : a₁ + a₂ + a₃ = b) (a₁₂ : A)
    (h₁₂ : a₁ + a₂ = a₁₂) (X : C) :
    (shiftFunctorAdd₃' C a₁ a₂ a₃ b h).inv.app X =
        ((shiftFunctorAdd' C a₁ a₂ a₁₂ h₁₂).inv.app X)⟦a₃⟧' ≫
      (shiftFunctorAdd' C a₁₂ a₃ b (by rw [← h₁₂, h])).inv.app X := by
  subst h₁₂ h
  simp only [Functor.comp_obj, shiftFunctorAdd₃', shiftFunctorAdd'_eq_shiftFunctorAdd,
    Iso.trans_inv, isoWhiskerRight_inv, assoc, NatTrans.comp_app,
    Functor.associator_inv_app, whiskerRight_app, Category.id_comp]

lemma shiftFunctorAdd₃'_hom_app' (a₁ a₂ a₃ : A) (b : A) (h : a₁ + a₂ + a₃ = b) (a₂₃ : A)
    (h₂₃ : a₂ + a₃ = a₂₃) (X : C) :
    (shiftFunctorAdd₃' C a₁ a₂ a₃ b h).hom.app X =
      (shiftFunctorAdd' C a₁ a₂₃ b (by rw [← h₂₃, ← h, add_assoc])).hom.app X ≫
        (shiftFunctorAdd' C a₂ a₃ a₂₃ h₂₃).hom.app (X⟦a₁⟧) := by
  simp only [shiftFunctorAdd₃'_hom_app a₁ a₂ a₃ b h (a₁ + a₂) rfl,
    shiftFunctorAdd'_assoc_hom_app _ _ _ _ _ _ _ h₂₃ h _]

lemma shiftFunctorAdd₃'_inv_app' (a₁ a₂ a₃ : A) (b : A) (h : a₁ + a₂ + a₃ = b) (a₂₃ : A)
    (h₂₃ : a₂ + a₃ = a₂₃) (X : C) :
    (shiftFunctorAdd₃' C a₁ a₂ a₃ b h).inv.app X =
      (shiftFunctorAdd' C a₂ a₃ a₂₃ h₂₃).inv.app (X⟦a₁⟧) ≫
        (shiftFunctorAdd' C a₁ a₂₃ b (by rw [← h₂₃, ← h, add_assoc])).inv.app X := by
  simp only [shiftFunctorAdd₃'_inv_app a₁ a₂ a₃ b h (a₁ + a₂) rfl,
    shiftFunctorAdd'_assoc_inv_app _ _ _ _ _ _ _ h₂₃ h _]

lemma shift_shiftFunctorCompIsoId_hom_app'
  (a a' b c : A') (h₁ : a + a' = 0) (h₂ : b + a = c) (X : C) :
  ((shiftFunctorCompIsoId C a a' h₁).hom.app X)⟦c⟧' =
    (shiftFunctorAdd' C a' c b (by rw [← add_zero b, ← h₁,
      ← add_assoc, h₂, add_comm a'])).inv.app (X⟦a⟧) ≫
      (shiftFunctorAdd' C a b c (by rw [add_comm a, h₂])).inv.app X := by
  dsimp [shiftFunctorCompIsoId]
  rw [← shiftFunctorAdd₃'_inv_app' _ _ _ _ (by rw [h₁, zero_add]),
    shiftFunctorAdd₃'_inv_app a a' c c (by rw [h₁, zero_add]) 0 h₁ X,
    shiftFunctorAdd'_zero_add_inv_app, Functor.map_comp]

end

open Category Limits Pretriangulated ZeroObject Preadditive

variable {C D A : Type _} [Category C] [Category D] [HasZeroObject C] [HasZeroObject D]
  [HasShift C ℤ] [Preadditive C] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive]
  [∀ (n : ℤ), (CategoryTheory.shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  [Category A] [Abelian A]

namespace Functor

variable (F : C ⥤ A) [F.PreservesZeroMorphisms]

class IsHomological : Prop where
  exact : ∀ (T : Triangle C) (hT : T ∈ distTriang C),
    ((shortComplexOfDistTriangle T hT).map F).Exact

lemma map_distinguished_exact [F.IsHomological] (T : Triangle C) (hT : T ∈ distTriang C) :
    ((shortComplexOfDistTriangle T hT).map F).Exact :=
  IsHomological.exact _ hT

lemma IsHomological.mk' (hF : ∀ (T : Pretriangulated.Triangle C) (hT : T ∈ distTriang C),
  ∃ (T' : Pretriangulated.Triangle C) (e : T ≅ T'),
    ((shortComplexOfDistTriangle T' (isomorphic_distinguished _ hT _ e.symm)).map F).Exact) :
    F.IsHomological where
  exact T hT := by
    obtain ⟨T', e, h'⟩ := hF T hT
    exact (ShortComplex.exact_iff_of_iso
      (F.mapShortComplex.mapIso ((shortComplexOfDistTriangleIsoOfIso e hT)))).2 h'

lemma IsHomological.of_iso {F₁ F₂ : C ⥤ A} [F₁.PreservesZeroMorphisms]
    [F₂.PreservesZeroMorphisms] [F₁.IsHomological] (e : F₁ ≅ F₂) :
    F₂.IsHomological where
  exact T hT := ShortComplex.exact_of_iso (ShortComplex.mapNatIso _ e)
    (F₁.map_distinguished_exact T hT)

def homologicalKernel [F.IsHomological] :
    Triangulated.Subcategory C where
  set := fun X => ∀ (n : ℤ), IsZero (F.obj (X⟦n⟧))
  zero := fun n => by rw [IsZero.iff_id_eq_zero, ← F.map_id, ← Functor.map_id,
    id_zero, Functor.map_zero, Functor.map_zero]
  shift := fun X a hX b =>
    IsZero.of_iso (hX (a + b)) (F.mapIso ((shiftFunctorAdd C a b).app X).symm)
  ext₂ := fun T hT h₁ h₃ n => (F.map_distinguished_exact _
    (shift_distinguished T hT n)).isZero_of_both_zeros
      (IsZero.eq_of_src (h₁ n) _ _) (IsZero.eq_of_tgt (h₃ n) _ _)

lemma mem_homologicalKernel_iff [F.IsHomological] [F.ShiftSequence ℤ]
    (X : C) : X ∈ F.homologicalKernel.set ↔
      ∀ (n : ℤ), IsZero ((F.shift n).obj X) := by
  simp only [← fun (n : ℤ) => Iso.isZero_iff ((F.isoShift n).app X)]
  rfl

@[nolint unusedArguments]
def IsHomological.W [F.IsHomological] : MorphismProperty C := fun _ _ f =>
  ∀ (n : ℤ), IsIso (F.map (f⟦n⟧'))

lemma IsHomological.mem_W_iff [F.IsHomological] [F.ShiftSequence ℤ] {X Y : C}
    (f : X ⟶ Y) : IsHomological.W F f ↔ ∀ (n : ℤ), IsIso ((F.shift n).map f) := by
  simp only [← fun (n : ℤ) => NatIso.isIso_map_iff (F.isoShift n) f]
  rfl

noncomputable instance [F.IsHomological] : PreservesLimitsOfShape (Discrete WalkingPair) F := by
  suffices ∀ (X₁ X₂ : C), PreservesLimit (pair X₁ X₂) F from
    ⟨fun {X} => preservesLimitOfIsoDiagram F (diagramIsoPair X).symm⟩
  intro X₁ X₂
  have : HasBinaryBiproduct (F.obj X₁) (F.obj X₂) := HasBinaryBiproducts.has_binary_biproduct _ _
  have : Mono (F.biprodComparison X₁ X₂) := by
    rw [mono_iff_cancel_zero]
    intro Z f hf
    have h₂ : f ≫ F.map biprod.snd = 0 := by simpa using hf =≫ biprod.snd
    let S := ShortComplex.mk (F.map (biprod.inl : X₁ ⟶ _)) (F.map (biprod.snd : _ ⟶ X₂))
      (by rw [← F.map_comp, biprod.inl_snd, F.map_zero])
    have ex : S.Exact := F.map_distinguished_exact _ (binaryBiproductTriangle_distinguished X₁ X₂)
    obtain ⟨g, rfl⟩ : ∃ (f₁ : Z ⟶ F.obj X₁), f₁ ≫ F.map biprod.inl = f := ⟨_, ex.lift_f f h₂⟩
    replace hf := hf =≫ biprod.fst
    simp only [assoc, biprodComparison_fst, zero_comp, ← F.map_comp, biprod.inl_fst,
      F.map_id, comp_id] at hf
    rw [hf, zero_comp]
  have : PreservesBinaryBiproduct X₁ X₂ F := preservesBinaryBiproductOfMonoBiprodComparison _
  apply Limits.preservesBinaryProductOfPreservesBinaryBiproduct

instance [F.IsHomological] : F.Additive := F.additive_of_preserves_binary_products

instance (L : C ⥤ D) [CommShift L ℤ] [IsTriangulated L]
  (F : D ⥤ A) [F.PreservesZeroMorphisms] [F.IsHomological] :
    (L ⋙ F).IsHomological :=
  ⟨fun T hT => F.map_distinguished_exact _ (L.map_distinguished T hT)⟩

lemma isHomological_of_localization (L : C ⥤ D)
    [L.CommShift ℤ] [L.IsTriangulated] [EssSurj L.mapArrow] (F : D ⥤ A)
    (G : C ⥤ A) (e : L ⋙ F ≅ G) [G.PreservesZeroMorphisms] [G.IsHomological]
    [F.PreservesZeroMorphisms] : F.IsHomological := by
  have : (L ⋙ F).IsHomological := IsHomological.of_iso e.symm
  refine' IsHomological.mk' _ (fun T hT => _)
  rw [Triangulated.Localization.distTriang_iff L] at hT
  obtain ⟨T₀, e, hT₀⟩ := hT
  exact ⟨L.mapTriangle.obj T₀, e, (L ⋙ F).map_distinguished_exact _ hT₀⟩

section

variable [F.IsHomological] [F.ShiftSequence ℤ] (T T' : Triangle C) (hT : T ∈ distTriang C)
  (φ : T ⟶ T') (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)

noncomputable def homology_sequence_δ : (F.shift n₀).obj T.obj₃ ⟶ (F.shift n₁).obj T.obj₁ :=
  F.shiftMap T.mor₃ n₀ n₁ (by rw [add_comm 1, h])

variable {T T'}

@[reassoc (attr := simp)]
noncomputable def homology_sequence_δ_naturality :
    (F.shift n₀).map φ.hom₃ ≫ F.homology_sequence_δ T' n₀ n₁ h =
      F.homology_sequence_δ T n₀ n₁ h ≫ (F.shift n₁).map φ.hom₁ := by
  dsimp only [homology_sequence_δ]
  rw [← shiftMap_comp', ← φ.comm₃, shiftMap_comp]

variable (T T')

@[simp]
lemma comp_homology_sequence_δ :
    (F.shift n₀).map T.mor₂ ≫ F.homology_sequence_δ T n₀ n₁ h = 0 := by
  dsimp only [homology_sequence_δ]
  rw [← F.shiftMap_comp', comp_dist_triangle_mor_zero₂₃ _ hT, shiftMap_zero]

@[simp]
lemma homology_sequence_δ_comp :
    F.homology_sequence_δ T n₀ n₁ h ≫ (F.shift n₁).map T.mor₁ = 0 := by
  dsimp only [homology_sequence_δ]
  rw [← F.shiftMap_comp, comp_dist_triangle_mor_zero₃₁ _ hT, shiftMap_zero]

lemma homology_sequence_comp  :
    (F.shift n₀).map T.mor₁ ≫ (F.shift n₀).map T.mor₂ = 0 := by
  rw [← Functor.map_comp, comp_dist_triangle_mor_zero₁₂ _ hT, Functor.map_zero]

lemma homology_sequence_exact₂ :
  (ShortComplex.mk _ _ (F.homology_sequence_comp T hT n₀)).Exact := by
  refine' ShortComplex.exact_of_iso _ (F.map_distinguished_exact _ (shift_distinguished _ hT n₀))
  refine' ShortComplex.isoMk ((F.isoShift n₀).app _)
    (mulIso ((-1 : Units ℤ)^n₀) ((F.isoShift n₀).app _)) ((F.isoShift n₀).app _) _ _
  . dsimp
    simp only [CochainComplex.ε_def', comp_zsmul, zsmul_comp, Functor.map_zsmul, smul_smul,
      CochainComplex.mul_ε_self, one_smul, isoShift_hom_naturality]
  . dsimp
    simp only [CochainComplex.ε_def', zsmul_comp, map_zsmul, isoShift_hom_naturality]

lemma homology_sequence_exact₃ :
    (ShortComplex.mk _ _ (F.comp_homology_sequence_δ T hT _ _ h)).Exact := by
  refine' ShortComplex.exact_of_iso _ (F.homology_sequence_exact₂ _ (rot_of_dist_triangle _ hT) n₀)
  refine' ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    ((F.shiftIso 1 n₀ n₁ (by linarith)).app _) _ _
  . dsimp
    simp
  . dsimp [homology_sequence_δ, shiftMap]
    simp only [id_comp]

lemma homology_sequence_exact₁ :
    (ShortComplex.mk _ _ (F.homology_sequence_δ_comp T hT _ _ h)).Exact := by
  refine' ShortComplex.exact_of_iso _ (F.homology_sequence_exact₂ _ (inv_rot_of_dist_triangle _ hT) n₁)
  refine' ShortComplex.isoMk (mulIso (-1) ((F.shiftIso (-1) n₁ n₀ (by linarith)).app _))
    (Iso.refl _) (Iso.refl _) _ _
  . dsimp
    simp only [neg_smul, one_smul, homology_sequence_δ, neg_comp, comp_id,
      Functor.map_neg, F.shiftIso_hom_app_comp_shiftMap_of_add_eq_zero T.mor₃ (-1)
      (neg_add_self 1) n₀ n₁ (by linarith)]
  . dsimp
    simp

lemma homology_sequence_epi_shift_map_mor₁_iff :
    Epi ((F.shift n₀).map T.mor₁) ↔ (F.shift n₀).map T.mor₂ = 0 := by
  constructor
  . intro H
    rw [← cancel_epi ((F.shift n₀).map T.mor₁), ← Functor.map_comp,
      comp_dist_triangle_mor_zero₁₂ _ hT, Functor.map_zero, comp_zero]
  . intro H
    refine' (ShortComplex.exact_iff_epi _ _).1 ((F.homology_sequence_exact₂ _ hT n₀))
    exact H

lemma homology_sequence_mono_shift_map_mor₁_iff :
    Mono ((F.shift n₁).map T.mor₁) ↔ F.homology_sequence_δ T n₀ n₁ h = 0 := by
  constructor
  . intro H
    rw [← cancel_mono ((F.shift n₁).map T.mor₁), zero_comp, F.homology_sequence_δ_comp _ hT]
  . intro H
    refine' (ShortComplex.exact_iff_mono _ _).1 (F.homology_sequence_exact₁ _ hT _  _ h)
    exact H

lemma homology_sequence_isIso_shift_map_mor₁_iff :
    IsIso ((F.shift n₁).map T.mor₁) ↔
      F.homology_sequence_δ T n₀ n₁ h = 0 ∧ (F.shift n₁).map T.mor₂ = 0 := by
  rw [← F.homology_sequence_mono_shift_map_mor₁_iff _ hT,
    ← F.homology_sequence_epi_shift_map_mor₁_iff _ hT]
  constructor
  . intro h
    exact ⟨inferInstance, inferInstance⟩
  . rintro ⟨h₀, h₁⟩
    apply isIso_of_mono_of_epi

end

lemma IsHomological.W_eq_homologicalKernelW [F.IsHomological] :
    IsHomological.W F = F.homologicalKernel.W := by
  letI := ShiftSequence.tautological F ℤ
  apply MorphismProperty.ext
  intro X Y f
  constructor
  . intro hf
    obtain ⟨Z, g, h, mem⟩ := distinguished_cocone_triangle f
    refine' ⟨Z, g, h, mem, fun n =>
      (F.homology_sequence_exact₃ _ mem n _ rfl).isZero_of_both_zeros _ _⟩
    . dsimp
      have := hf n
      have zero : f ≫ g = 0 := comp_dist_triangle_mor_zero₁₂ _ mem
      simp only [← cancel_epi (F.map (f⟦n⟧')), ← Functor.map_comp, zero,
        Functor.map_zero, comp_zero]
    . dsimp
      have := hf (n + 1)
      simp only [← cancel_mono (F.map (f⟦n+1⟧')), zero_comp]
      exact F.homology_sequence_δ_comp _ mem n (n+1) rfl
  . intro hf n
    obtain ⟨Z, g, h, mem, hZ⟩ := hf
    have : Mono (F.map (f⟦n⟧')) := (ShortComplex.exact_iff_mono _ ((hZ _).eq_of_src _ _)).1
      (F.homology_sequence_exact₁ _ mem (n-1) n (by linarith))
    have : Epi (F.map (f⟦n⟧')) := (ShortComplex.exact_iff_epi _ ((hZ n).eq_of_tgt _ _)).1
      (F.homology_sequence_exact₂ _ mem n)
    apply isIso_of_mono_of_epi

end Functor

end CategoryTheory
