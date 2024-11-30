<<<<<<< HEAD
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.Refinements
import Mathlib.Algebra.Homology.HomologicalComplexLimits

open CategoryTheory Category Limits Preadditive
  HomologicalComplex
variable {C : Type _} [Category C] [Abelian C]

namespace CochainComplex

variable (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)

namespace mappingCone

noncomputable def fromOfShortComplex :
  mappingCone S.f ⟶ S.X₃ := desc S.f 0 S.g (by simp)

variable {S}

lemma isIso_homologyMap_fromOfShortComplex (n : ℤ) :
    IsIso (HomologicalComplex.homologyMap (fromOfShortComplex S) n) := by
  have hS' := fun i => hS.map_of_exact (HomologicalComplex.eval C (ComplexShape.up ℤ) i)
  have : ∀ i, Mono (S.f.f i) := fun i => (hS' i).mono_f
  have : ∀ i, Epi (S.g.f i) := fun i => (hS' i).epi_g
  rw [isIso_iff_mono_and_epi]
  constructor
  · rw [mono_homologyMap_iff_up_to_refinements _ (n-1) n (n+1) (by simp) (by simp)]
    intro A₀ a ha b hb
    obtain ⟨a₁, a₂, ha₁₂⟩ := to_break _ a _ rfl
    simp [ha₁₂, ext_to_iff _ _ (n+2) (show n + 1 + 1 = n + 2 by linarith),
      inl_v_d_assoc _ (n + 1) n (n + 2) (by linarith) (by linarith)] at ha
    obtain ⟨A₁, π₁, hπ₁, c, hc⟩ := surjective_up_to_refinements_of_epi (S.g.f (n-1)) b
    obtain ⟨A₂, π₂, hπ₂, e, he⟩ := (hS' n).exact.exact_up_to_refinements
      (π₁ ≫ a₂ - c ≫ S.X₂.d (n-1) n) (by
        dsimp
        simp only [sub_comp, assoc, ← S.g.comm, ← reassoc_of% hc, ← hb, ha₁₂, add_comp,
          fromOfShortComplex, inl_v_desc_f, HomComplex.Cochain.zero_v, comp_zero,
          inr_f_desc_f, zero_add, sub_self])
    dsimp at e he
    simp only [comp_sub] at he
    refine' ⟨A₂, π₂ ≫ π₁, epi_comp _ _, e ≫ (inl S.f).v n (n - 1) (by linarith) +
      π₂ ≫ c ≫ (inr S.f).f (n - 1), _⟩
    simp only [ext_to_iff _ _ (n + 1) rfl, ha₁₂, comp_add, assoc, sub_add_cancel,
      add_comp, inr_f_d, inl_v_fst_v, comp_id, inr_f_fst_v, comp_zero, add_zero,
      d_fst_v', comp_neg, inl_v_fst_v_assoc, inl_v_snd_v, inr_f_snd_v, zero_add,
      d_snd_v', inl_v_snd_v_assoc, zero_comp]
    constructor
    · simp only [← cancel_mono (S.f.f (n+1)), assoc, neg_comp, ← S.f.comm,
        ← reassoc_of% he, d_comp_d, sub_comp, comp_zero, sub_zero]
      simp only [← add_eq_zero_iff_eq_neg, ← comp_add, ha.2, comp_zero]
    · rw [← he, sub_add_cancel]
  · rw [epi_homologyMap_iff_up_to_refinements _ (n-1) n (n+1) (by simp) (by simp)]
    intro A₀ a ha
    obtain ⟨A₁, π₁, hπ₁, b, hb⟩ := surjective_up_to_refinements_of_epi (S.g.f n) a
    obtain ⟨A₂, π₂, hπ₂, c, hc⟩ := (hS' (n+1)).exact.exact_up_to_refinements (b ≫ S.X₂.d n (n+1)) (by
      dsimp
      simp only [assoc, ← S.g.comm, ← reassoc_of% hb, ha, comp_zero])
    dsimp at c hc
    refine' ⟨A₂, π₂ ≫ π₁, epi_comp _ _ , -c ≫ (inl S.f).v (n+1) n (by linarith) +
        π₂ ≫ b ≫ (inr S.f).f n, _, 0, _ ⟩
    · dsimp
      simp [ext_to_iff _ _ (n + 2) (show n + 1 + 1 = n + 2 by linarith),
        d_fst_v _ n (n+1) (n+2) (by linarith) (by linarith)]
      constructor
      · simp only [← cancel_mono (S.f.f (n+2)), assoc, zero_comp, ← S.f.comm,
          ← reassoc_of% hc, d_comp_d, comp_zero]
      · dsimp
        simp only [d_snd_v _ n (n + 1) rfl, comp_add, inl_v_fst_v_assoc,
          inl_v_snd_v_assoc, zero_comp, add_zero, hc, add_left_neg]
    · dsimp [fromOfShortComplex]
      simp only [hb, assoc, add_comp, neg_comp, inl_v_desc_f, HomComplex.Cochain.zero_v,
        comp_zero, neg_zero, inr_f_desc_f, zero_add, ComplexShape.up_Rel,
        sub_add_cancel, not_true, zero_comp, add_zero]
=======
/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.Refinements

/-!
# The mapping cone of a monomorphism, up to a quasi-isomophism

If `S` is a short exact short complex of cochain complexes in an abelian category,
we construct a quasi-isomorphism `descShortComplex S : mappingCone S.f ⟶ S.X₃`.

We obtain this by comparing the homology sequence of `S` and the homology
sequence of the homology functor on the homotopy category, applied to the
distinguished triangle attached to the mapping cone of `S.f`.

-/

open CategoryTheory Category ComplexShape HomotopyCategory Limits
  HomologicalComplex.HomologySequence Pretriangulated Preadditive

variable {C : Type*} [Category C] [Abelian C]

namespace CochainComplex

@[reassoc]
lemma homologySequenceδ_quotient_mapTriangle_obj
    (T : Triangle (CochainComplex C ℤ)) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (homologyFunctor C (up ℤ) 0).homologySequenceδ
        ((quotient C (up ℤ)).mapTriangle.obj T) n₀ n₁ h =
      (homologyFunctorFactors C (up ℤ) n₀).hom.app _ ≫
        (HomologicalComplex.homologyFunctor C (up ℤ) 0).shiftMap T.mor₃ n₀ n₁ (by omega) ≫
        (homologyFunctorFactors C (up ℤ) n₁).inv.app _ := by
  apply homologyFunctor_shiftMap

namespace mappingCone

variable (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)

/-- The canonical morphism `mappingCone S.f ⟶ S.X₃` when `S` is a short complex
of cochain complexes. -/
noncomputable def descShortComplex : mappingCone S.f ⟶ S.X₃ := desc S.f 0 S.g (by simp)

@[reassoc (attr := simp)]
lemma inr_descShortComplex : inr S.f ≫ descShortComplex S = S.g := by
  simp [descShortComplex]

@[reassoc (attr := simp)]
lemma inr_f_descShortComplex_f (n : ℤ) : (inr S.f).f n ≫ (descShortComplex S).f n = S.g.f n := by
  simp [descShortComplex]

@[reassoc (attr := simp)]
lemma inl_v_descShortComplex_f (i j : ℤ) (h : i + (-1) = j) :
    (inl S.f).v i j h ≫ (descShortComplex S).f j = 0 := by
  simp [descShortComplex]

variable {S}

lemma homologySequenceδ_triangleh (n₀ : ℤ) (n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (homologyFunctor C (up ℤ) 0).homologySequenceδ (triangleh S.f) n₀ n₁ h =
      (homologyFunctorFactors C (up ℤ) n₀).hom.app _ ≫
        HomologicalComplex.homologyMap (descShortComplex S) n₀ ≫ hS.δ n₀ n₁ h ≫
          (homologyFunctorFactors C (up ℤ) n₁).inv.app _ := by
  /- We proceed by diagram chase. We test the identity on
     cocycles `x' : A' ⟶ (mappingCone S.f).X n₀` -/
  dsimp
  rw [← cancel_mono ((homologyFunctorFactors C (up ℤ) n₁).hom.app _),
    assoc, assoc, assoc, Iso.inv_hom_id_app,
    ← cancel_epi ((homologyFunctorFactors C (up ℤ) n₀).inv.app _), Iso.inv_hom_id_app_assoc]
  apply yoneda.map_injective
  ext ⟨A⟩ (x : A ⟶ _)
  obtain ⟨A', π, _, x', w, hx'⟩ :=
    (mappingCone S.f).eq_liftCycles_homologyπ_up_to_refinements x n₁ (by simpa using h)
  erw [homologySequenceδ_quotient_mapTriangle_obj_assoc _ _ _ h]
  dsimp
  rw [comp_id, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  erw [comp_id]
  rw [← cancel_epi π, reassoc_of% hx', reassoc_of% hx',
    HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
  /- We decompose the cocycle `x'` into two morphisms `a : A' ⟶ S.X₁.X n₁`
     and `b : A' ⟶ S.X₂.X n₀` satisfying certain relations. -/
  obtain ⟨a, b, hab⟩ := decomp_to _ x' n₁ h
  rw [hab, ext_to_iff _ n₁ (n₁ + 1) rfl, add_comp, assoc, assoc, inr_f_d, add_comp, assoc,
    assoc, assoc, assoc, inr_f_fst_v, comp_zero, comp_zero, add_zero, zero_comp,
    d_fst_v _ _ _ _ h, comp_neg, inl_v_fst_v_assoc, comp_neg, neg_eq_zero,
    add_comp, assoc, assoc, assoc, assoc, inr_f_snd_v, comp_id, zero_comp,
    d_snd_v _ _ _ h, comp_add, inl_v_fst_v_assoc, inl_v_snd_v_assoc, zero_comp, add_zero] at w
  /- We simplify the RHS. -/
  conv_rhs => simp only [hab, add_comp, assoc, inr_f_descShortComplex_f,
    inl_v_descShortComplex_f, comp_zero, zero_add]
  rw [hS.δ_eq n₀ n₁ (by simpa using h) (b ≫ S.g.f n₀) _ b rfl (-a)
    (by simp only [neg_comp, neg_eq_iff_add_eq_zero, w.2]) (n₁ + 1) (by simp)]
  /- We simplify the LHS. -/
  dsimp [Functor.shiftMap, homologyFunctor_shift]
  rw [HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc,
    S.X₁.liftCycles_shift_homologyπ_assoc _ _ _ _ n₁ (by omega) (n₁ + 1) (by simp),
    Iso.inv_hom_id_app]
  dsimp [homologyFunctor_shift]
  simp only [hab, add_comp, assoc, inl_v_triangle_mor₃_f_assoc,
    shiftFunctorObjXIso, neg_comp, Iso.inv_hom_id, comp_neg, comp_id,
    inr_f_triangle_mor₃_f_assoc, zero_comp, comp_zero, add_zero]

open ComposableArrows

set_option simprocs false

include hS in
lemma quasiIso_descShortComplex : QuasiIso (descShortComplex S) where
  quasiIsoAt n := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    let φ : ((homologyFunctor C (up ℤ) 0).homologySequenceComposableArrows₅
        (triangleh S.f) n _ rfl).δlast ⟶ (composableArrows₅ hS n _ rfl).δlast :=
      homMk₄ ((homologyFunctorFactors C (up ℤ) _).hom.app _)
        ((homologyFunctorFactors C (up ℤ) _).hom.app _)
        ((homologyFunctorFactors C (up ℤ) _).hom.app _ ≫
          HomologicalComplex.homologyMap (descShortComplex S) n)
        ((homologyFunctorFactors C (up ℤ) _).hom.app _)
        ((homologyFunctorFactors C (up ℤ) _).hom.app _)
        ((homologyFunctorFactors C (up ℤ) _).hom.naturality S.f)
        (by
          erw [(homologyFunctorFactors C (up ℤ) n).hom.naturality_assoc]
          dsimp
          rw [← HomologicalComplex.homologyMap_comp, inr_descShortComplex])
        (by
          dsimp
          erw [homologySequenceδ_triangleh hS]
          simp only [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj, assoc,
            Iso.inv_hom_id_app, comp_id])
        ((homologyFunctorFactors C (up ℤ) _).hom.naturality S.f)
    have : IsIso ((homologyFunctorFactors C (up ℤ) n).hom.app (mappingCone S.f) ≫
        HomologicalComplex.homologyMap (descShortComplex S) n) := by
      apply Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
        ((homologyFunctor C (up ℤ) 0).homologySequenceComposableArrows₅_exact _
          (mappingCone_triangleh_distinguished S.f) n _ rfl).δlast
        (composableArrows₅_exact hS n _ rfl).δlast φ
      all_goals dsimp [φ]; infer_instance
    apply IsIso.of_isIso_comp_left ((homologyFunctorFactors C (up ℤ) n).hom.app (mappingCone S.f))
>>>>>>> origin/ext-change-of-universes

end mappingCone

end CochainComplex
