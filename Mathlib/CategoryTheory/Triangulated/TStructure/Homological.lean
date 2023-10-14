import Mathlib.CategoryTheory.Triangulated.TStructure.Abelian
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Homology.ShortComplex.Ab

open CategoryTheory Category Limits Pretriangulated

lemma AddCommGroupCat.isZero (X : AddCommGroupCat) (hX : ∀ (x : X), x = 0) :
    Limits.IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  ext x
  exact hX x

namespace CategoryTheory

namespace Pretriangulated

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

lemma preadditiveYoneda_map_distinguished (A : C) (T : Triangle C) (hT : T ∈ distTriang C) :
    ((ShortComplex.mk _ _ (comp_dist_triangle_mor_zero₁₂ T hT)).op.map (preadditiveYoneda.obj A)).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro (x₂ : T.obj₂ ⟶ A) (hx₂ : T.mor₁ ≫ x₂ = 0)
  obtain ⟨x₃, hx₃⟩ := T.yoneda_exact₂ hT x₂ hx₂
  exact ⟨x₃, hx₃.symm⟩

end Pretriangulated

namespace Limits

namespace CokernelCofork

variable {C : Type*} [Category C] [Preadditive C]

def nonempty_isColimit_iff_preadditiveYoneda {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f) :
    Nonempty (IsColimit c) ↔ ∀ (A : C), ((ShortComplex.mk _ _ c.condition).op.map (preadditiveYoneda.obj A)).Exact ∧
      Mono (((ShortComplex.mk _ _ c.condition).op.map (preadditiveYoneda.obj A)).f) := by
  simp_rw [ShortComplex.ab_exact_iff, AddCommGroupCat.mono_iff_injective]
  constructor
  · intro ⟨h⟩ A
    constructor
    · rintro (x₂ : Y ⟶ A) (hx₂ : f ≫ x₂ = 0)
      exact ⟨_, (CokernelCofork.IsColimit.desc' h x₂ hx₂).2⟩
    · rintro (x₁ : c.pt ⟶ A) (x₁' : c.pt ⟶ A) (h₁ : c.π ≫ x₁ = c.π ≫ x₁')
      exact Cofork.IsColimit.hom_ext h h₁
  · rintro h
    exact ⟨Cofork.IsColimit.mk _
      (fun s => ((h _).1 s.π (CokernelCofork.condition s)).choose)
      (fun s => ((h _).1 s.π (CokernelCofork.condition s)).choose_spec)
      (fun s m hm => (h _).2
        (hm.trans ((h _).1 s.π (CokernelCofork.condition s)).choose_spec.symm))⟩

end CokernelCofork

end Limits

namespace ShortComplex

variable {C : Type*} [Category C]

lemma exact_and_mono_f_iff_of_iso [HasZeroMorphisms C] {S T : ShortComplex C} (e : S ≅ T) :
    (S.Exact ∧ Mono S.f) ↔ (T.Exact ∧ Mono T.f) := by
  have : Mono S.f ↔ Mono T.f :=
    MorphismProperty.RespectsIso.arrow_mk_iso_iff
      (MorphismProperty.RespectsIso.monomorphisms C)
      (Arrow.isoMk (ShortComplex.π₁.mapIso e) (ShortComplex.π₂.mapIso e) e.hom.comm₁₂)
  rw [exact_iff_of_iso e, this]

lemma exact_and_epi_g_iff_of_iso [HasZeroMorphisms C] {S T : ShortComplex C} (e : S ≅ T) :
    (S.Exact ∧ Epi S.g) ↔ (T.Exact ∧ Epi T.g) := by
  have : Epi S.g ↔ Epi T.g :=
    MorphismProperty.RespectsIso.arrow_mk_iso_iff
      (MorphismProperty.RespectsIso.epimorphisms C)
      (Arrow.isoMk (ShortComplex.π₂.mapIso e) (ShortComplex.π₃.mapIso e) e.hom.comm₂₃)
  rw [exact_iff_of_iso e, this]

variable [Preadditive C]

lemma exact_and_epi_g_iff (S : ShortComplex C) [Balanced C] [S.HasHomology] :
    (S.Exact ∧ Epi S.g) ↔
      Nonempty (IsColimit (CokernelCofork.ofπ _ S.zero)) := by
  constructor
  · rintro ⟨hS, _⟩
    exact ⟨hS.gIsCokernel⟩
  · intro ⟨h⟩
    exact ⟨S.exact_of_g_is_cokernel h, ⟨fun _ _ => Cofork.IsColimit.hom_ext h⟩⟩

lemma exact_and_epi_g_iff_preadditiveYoneda (S : ShortComplex C) [Balanced C] [S.HasHomology] :
    (S.Exact ∧ Epi S.g) ↔
      ∀ (A : C), (S.op.map (preadditiveYoneda.obj A)).Exact ∧
        Mono (S.op.map (preadditiveYoneda.obj A)).f := by
  rw [exact_and_epi_g_iff, CokernelCofork.nonempty_isColimit_iff_preadditiveYoneda]
  rfl

end ShortComplex

namespace Triangulated

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  (t : TStructure C)

namespace TStructure

section

variable (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) [t.IsLE T.obj₁ n]

@[simps! obj₁ obj₂ obj₃ mor₁ mor₂]
noncomputable def truncLETriangle  :
    Triangle C :=
  Triangle.mk ((t.truncLE n).map T.mor₁)
    ((t.truncLE n).map T.mor₂)
    ((t.truncLEι n).app T.obj₃ ≫ T.mor₃ ≫ (asIso ((t.truncLEι n).app T.obj₁)).inv⟦(1 : ℤ)⟧')

instance : t.IsLE (t.truncLETriangle T n).obj₁ n := by dsimp; infer_instance
instance : t.IsLE (t.truncLETriangle T n).obj₂ n := by dsimp; infer_instance
instance : t.IsLE (t.truncLETriangle T n).obj₃ n := by dsimp; infer_instance

/-lemma truncLETriangle_distinguished :
    t.truncLETriangle T n ∈ distTriang C := by
  have := hT
  let a : T.obj₁ ⟶ (t.truncLE n).obj T.obj₂ :=
    (asIso ((t.truncLEι n).app T.obj₁)).inv ≫ (t.truncLE n).map T.mor₁
  let b := (t.truncLEι n).app T.obj₂
  have comm : a ≫ b = T.mor₁ := by simp
  obtain ⟨Z, f₂, f₃, h₁⟩ := distinguished_cocone_triangle a
  have h₂ := (t.triangleLEGT_distinguished n T.obj₂)
  have H := someOctahedron comm h₁ h₂ hT
  refine' isomorphic_distinguished _ h₁ _ _
  have paf := H.mem
  have e : (t.truncLE n).obj T.obj₃ ≅ Z := sorry
  have he₁ : (truncLE t n).map T.mor₂ ≫ e.hom = f₂ := sorry
  have he₂ : (t.truncLETriangle T n).mor₃ ≫
    (shiftFunctor C 1).map ((truncLEι t n).app T.obj₁) = e.hom ≫ f₃ := sorry
  exact Triangle.isoMk _ _ (asIso ((t.truncLEι n).app T.obj₁))
    (Iso.refl _) e (by simp) (by simp [he₁]) he₂-/

end

noncomputable def toHomology₀ (X : C) [t.IsLE X 0] : X ⟶ t.ιHeart.obj ((t.homology 0).obj X) :=
  (asIso ((t.truncLEι 0).app X)).inv ≫ (t.truncGEπ 0).app _ ≫ (shiftFunctorZero C ℤ).inv.app _

@[reassoc]
lemma truncLEι_toHomology₀_shiftFunctorZero_hom (X : C) [t.IsLE X 0] :
    (t.truncLEι 0).app X ≫ t.toHomology₀ X ≫ (shiftFunctorZero C ℤ).hom.app _ =
      (t.truncGEπ 0).app _ := by
  dsimp only [toHomology₀]
  rw [assoc, assoc]
  erw [Iso.inv_hom_id_app, comp_id]
  rw [asIso_inv, IsIso.hom_inv_id_assoc]

lemma toHomology₀_naturality {X Y : C} (f : X ⟶ Y) [t.IsLE X 0] [t.IsLE Y 0] :
    t.toHomology₀ X ≫ (t.homology 0 ⋙ t.ιHeart).map f = f ≫ t.toHomology₀ Y := by
  rw [← cancel_mono ((shiftFunctorZero C ℤ).hom.app _), assoc, assoc,
    ← cancel_epi ((t.truncLEι 0).app X)]
  erw [← (t.truncLEι 0).naturality_assoc f]
  rw [t.truncLEι_toHomology₀_shiftFunctorZero_hom Y]
  erw [(shiftFunctorZero C ℤ).hom.naturality]
  rw [t.truncLEι_toHomology₀_shiftFunctorZero_hom_assoc X]
  erw [(t.truncGEπ 0).naturality]
  rfl

instance (X : C) : t.IsLE ((t.truncLT 0).obj X) (-1) :=
  t.isLE_of_iso ((t.truncLEIsoTruncLT (-1) 0 (by linarith)).app X) (-1)

instance (A X : C) [t.IsLE X 0] [t.IsGE A 0] :
    IsIso ((preadditiveYoneda.obj A).map ((t.truncGEπ 0).app X).op) := by
  have : Mono ((preadditiveYoneda.obj A).map ((t.truncGEπ 0).app X).op) :=
    (preadditiveYoneda_map_distinguished A _ (rot_of_dist_triangle _ (t.triangleLTGE_distinguished 0 X))).mono_g (by
      apply IsZero.eq_of_src
      apply AddCommGroupCat.isZero
      intro (x : ((t.truncLT 0).obj X)⟦(1 : ℤ)⟧ ⟶ A)
      have : t.IsLE (((t.truncLT 0).obj X)⟦(1 : ℤ)⟧) (-1) :=
        t.isLE_shift ((t.truncLT 0).obj X) 0 1 (-1) (by linarith)
      exact t.zero x (-1) 0 (by linarith))
  have : Epi ((preadditiveYoneda.obj A).map ((t.truncGEπ 0).app X).op) :=
    (preadditiveYoneda_map_distinguished A _ (t.triangleLTGE_distinguished 0 X)).epi_f (by
      apply IsZero.eq_of_tgt
      apply AddCommGroupCat.isZero
      intro (x : (t.truncLT 0).obj X ⟶ A)
      exact t.zero x (-1) 0 (by linarith))
  apply isIso_of_mono_of_epi

instance (A X : C) [t.IsLE X 0] [t.IsGE A 0]:
    IsIso ((preadditiveYoneda.obj A).map (t.toHomology₀ X).op) := by
  dsimp only [toHomology₀]
  rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp]
  infer_instance

namespace HomologicalFunctorAux

variable {T : Triangle C} (hT : T ∈ distTriang C)

instance : (t.homology 0).Additive where
  map_add {X Y f g} := by
    apply t.ιHeart.map_injective
    simp [homology]

@[simps!]
noncomputable def shortComplex :=
  (ShortComplex.mk _ _ (comp_dist_triangle_mor_zero₁₂ T hT)).map (t.homology 0)

section

def case₁ [t.IsLE T.obj₁ 0] [t.IsLE T.obj₂ 0] [t.IsLE T.obj₃ 0] :
    (shortComplex t hT).Exact ∧ Epi (shortComplex t hT).g := by
  let S := fun A => (shortComplex t hT).op.map (preadditiveYoneda.obj A)
  let S' := fun A => (ShortComplex.mk _ _ (comp_dist_triangle_mor_zero₁₂ T hT)).op.map (preadditiveYoneda.obj A)
  suffices ∀ A, (S A).Exact ∧ Mono (S A).f by
    simpa only [ShortComplex.exact_and_epi_g_iff_preadditiveYoneda] using this
  intro A
  let e' : ∀ (X : C) [t.IsLE X 0],
    (preadditiveYoneda.obj A).obj (Opposite.op ((t.homology 0).obj X)) ≅ (preadditiveYoneda.obj A.1).obj (Opposite.op X) :=
      fun X _ => asIso ((preadditiveYoneda.obj A.1).map (t.toHomology₀ X).op)
  have e : S A ≅ S' A.1 := by
    refine' ShortComplex.isoMk (e' T.obj₃) (e' T.obj₂) (e' T.obj₁) _ _
    · simpa only [op_comp, Functor.map_comp] using (preadditiveYoneda.obj A.1).congr_map
        (congr_arg Quiver.Hom.op (t.toHomology₀_naturality T.mor₂).symm)
    · simpa only [op_comp, Functor.map_comp] using (preadditiveYoneda.obj A.1).congr_map
        (congr_arg Quiver.Hom.op (t.toHomology₀_naturality T.mor₁).symm)
  rw [ShortComplex.exact_and_mono_f_iff_of_iso e]
  refine' ⟨preadditiveYoneda_map_distinguished A.1 _ hT,
    (preadditiveYoneda_map_distinguished A.1 _ (rot_of_dist_triangle _ hT)).mono_g _⟩
  apply IsZero.eq_of_src
  apply AddCommGroupCat.isZero
  intro (x : T.obj₁⟦(1 : ℤ)⟧ ⟶ A.obj)
  have : t.IsLE (T.obj₁⟦(1 : ℤ)⟧) (-1) := t.isLE_shift T.obj₁ 0 1 (-1) (by linarith)
  exact t.zero x (-1) 0 (by linarith)

instance (X : C) (n : ℤ) : IsIso ((t.truncGELE n n).map ((t.truncLEι n).app X)) := by
  dsimp [truncGELE]
  infer_instance

instance (X : C) (n : ℤ) : IsIso ((t.homology n).map ((t.truncLEι n).app X)) := by
  suffices IsIso (t.ιHeart.map ((t.homology n).map ((t.truncLEι n).app X))) from
    isIso_of_reflects_iso ((t.homology n).map ((t.truncLEι n).app X)) t.ιHeart
  dsimp [homology]
  infer_instance

/-def case₂ [t.IsLE T.obj₁ 0] :
    (shortComplex t hT).Exact ∧ Epi (shortComplex t hT).g := by
  have h' := case₁ t (t.truncLETriangle_distinguished T hT 0)
  refine' (ShortComplex.exact_and_epi_g_iff_of_iso _).1 h'
  refine' ShortComplex.isoMk
    (asIso ((t.homology 0).map ((t.truncLEι 0).app T.obj₁)))
    (asIso ((t.homology 0).map ((t.truncLEι 0).app T.obj₂)))
    (asIso ((t.homology 0).map ((t.truncLEι 0).app T.obj₃))) _ _
  all_goals
    dsimp
    simp only [← Functor.map_comp, NatTrans.naturality, Functor.id_obj, Functor.id_map]-/

end

end HomologicalFunctorAux

end TStructure

end Triangulated

end CategoryTheory
