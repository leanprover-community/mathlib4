/-import Mathlib.Algebra.Homology.SpectralSequence.Basic
import Mathlib.Algebra.Homology.SpectralSequence.SpectralObject
import Mathlib.Algebra.Homology.SpectralSequence.ZTilde

open CategoryTheory Category Limits

variable {C : Type _} [Category C] [Abelian C]

namespace CategoryTheory

namespace Abelian

namespace SpectralObject

open CohomologicalSpectralSequence

variable (X : SpectralObject C ℤt)

@[simps]
def Bounds.quadrantUR (p q : ℤ) : Bounds ℤt where
  γ₁ _ := ℤt.mk q
  γ₂ n := ℤt.mk (n - p + 1)

abbrev Bounds.firstQuadrant := Bounds.quadrantUR 0 0

namespace ToE₂CohomologicalSpectralSequence

noncomputable def page (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) : C :=
  (X.E (pq.1+pq.2-1) (pq.1+pq.2) (pq.1+pq.2+1) (by linarith) (by linarith)).obj
    (ιℤt.mapArrow₃.obj (Arrow₃.mkOfLE (pq.2-r+2) pq.2 (pq.2+1) (pq.2+r-1)))

noncomputable def pageIsoE (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn : pq.1 + pq.2 = n₁)
    (D : Arrow₃ ℤt) (hD₀ : D.X₀ = ℤt.mk (pq.2-r+2))
    (hD₁ : D.X₁ = ℤt.mk pq.2) (hD₂ : D.X₂ = ℤt.mk (pq.2+1))
    (hD₃ : D.X₃ = ℤt.mk (pq.2+r-1)) :
    page X r hr pq ≅ (X.E n₀ n₁ n₂ hn₁ hn₂).obj D :=
  (X.EIsoOfEq (pq.1+pq.2-1) (pq.1+pq.2) (pq.1+pq.2+1) _ _
    n₀ n₁ n₂ hn₁ hn₂ hn).app _ ≪≫ (X.E n₀ n₁ n₂ hn₁ hn₂).mapIso
      (Arrow₃.isoMk _ _ (eqToIso hD₀.symm) (eqToIso hD₁.symm) (eqToIso hD₂.symm) (eqToIso hD₃.symm)
        (Subsingleton.elim _ _) (Subsingleton.elim _ _) (Subsingleton.elim _ _))

noncomputable def d (r : ℤ) (hr : 2 ≤ r) (pq pq' : ℤ × ℤ) (hpq' : pq + (r, 1-r) = pq') :
    page X r hr pq ⟶ page X r hr pq' := by
  let n := pq.1 + pq.2
  have h₁ : pq.1 + r = pq'.1 := congr_arg _root_.Prod.fst hpq'
  have h₂ : pq.2 + (1-r) = pq'.2 := congr_arg _root_.Prod.snd hpq'
  refine' (X.d (n-1) n (n+1) (n+2) _ _ _).app
    (ιℤt.mapArrow₅.obj
      (Arrow₅.mkOfLE (pq'.2-r+2) pq'.2 (pq.2-r+2) pq.2 (pq.2+1) (pq.2+r-1))) ≫
      Iso.inv (pageIsoE X r hr _ _ _ _ _ _ _ _ _ _ _ _)
  · linarith
  · dsimp
    linarith
  · rfl
  · rfl
  · dsimp
    congr 1
    linarith
  · dsimp
    congr 1
    linarith

lemma d_eq (r : ℤ) (hr : 2 ≤ r) (pq pq' : ℤ × ℤ) (hpq' : pq + (r, 1-r) = pq')
    (n₀ n₁ n₂ n₃ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃)
    (hn : pq.1 + pq.2 = n₁)
    (D : Arrow₅ ℤt) (hD₀ : D.X₀ = ℤt.mk (pq'.2-r+2)) (hD₁ : D.X₁ = ℤt.mk pq'.2)
      (hD₂ : D.X₂ = ℤt.mk (pq.2-r+2)) (hD₃ : D.X₃ = ℤt.mk pq.2)
      (hD₄ : D.X₄ = ℤt.mk (pq.2+1)) (hD₅ : D.X₅ = ℤt.mk (pq.2+r-1)) :
    d X r hr pq pq' hpq' = Iso.hom (pageIsoE X r hr pq n₀ n₁ n₂ hn₁ hn₂ hn
        ((Arrow₅.δ₀ ⋙ Arrow₄.δ₀).obj D) hD₂ hD₃ hD₄ hD₅) ≫
          (X.d n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃).app D ≫
          Iso.inv (pageIsoE X r hr pq' n₁ n₂ n₃ hn₂ hn₃
            (by subst hpq' ; dsimp ; linarith) _ hD₀ hD₁
            (by subst hpq' ; dsimp ; rw [hD₂] ; congr 1 ; linarith)
            (by subst hpq' ; dsimp ; rw [hD₃] ; congr 1 ; linarith)) := by
  obtain rfl : n₀ = n₁ - 1 := by linarith
  obtain rfl : n₂ = n₁ + 1 := by linarith
  obtain rfl : n₃ = n₁ + 2 := by linarith
  subst hn
  obtain ⟨f₁, f₂, f₃, f₄, f₅⟩ := D
  dsimp at hD₀ hD₁ hD₂ hD₃ hD₄ hD₅
  substs hD₀ hD₁ hD₂ hD₃ hD₄ hD₅
  dsimp [d, pageIsoE, Arrow₃.isoMk, Arrow₄.δ₀, Arrow₅.δ₀]
  erw [EIsoOfEq_refl, Iso.refl_hom, NatTrans.id_app]
  erw [id_comp, Functor.map_id, id_comp]
  rfl

lemma d_comp_d (r : ℤ) (hr : 2 ≤ r) (pq pq' pq'' : ℤ × ℤ) (hpq' : pq + (r, 1 - r) = pq')
    (hpq'' : pq' + (r, 1 - r) = pq'') :
    d X r hr pq pq' hpq' ≫ d X r hr pq' pq'' hpq'' = 0 := by
  have h₁ : pq.1 + r = pq'.1 := congr_arg _root_.Prod.fst hpq'
  have h₂ : pq.2 + (1-r) = pq'.2 := congr_arg _root_.Prod.snd hpq'
  have h₄ : pq'.2 + (1-r) = pq''.2 := congr_arg _root_.Prod.snd hpq''
  let n := pq.1 + pq.2
  have hn : n = pq.1 + pq.2 := rfl
  let D₇ := ιℤt.mapArrow₇.obj (Arrow₇.mkOfLE (pq''.2-r+2) pq''.2 (pq'.2-r+2) pq'.2 (pq.2-r+2) pq.2 (pq.2+1) (pq.2+r-1))
  rw [d_eq X r hr pq pq' hpq' (n-1) n (n+1) (n+2) (by linarith) (by linarith)
    (by linarith) rfl ((Arrow₇.δ₀ ⋙ Arrow₆.δ₀).obj D₇) rfl rfl rfl rfl rfl rfl]
  rw [d_eq X r hr pq' pq'' hpq'' n (n+1) (n+2) (n+3) (by linarith) (by linarith)
    (by linarith) (by linarith) ((Arrow₇.δ₇ ⋙ Arrow₆.δ₆).obj D₇) rfl rfl rfl rfl, assoc, assoc]
  erw [Iso.inv_hom_id_assoc, X.d_comp_d_app_assoc, zero_comp, comp_zero]

noncomputable def shortComplexIso (r : ℤ) (hr : 2 ≤ r) (pq pq' pq'' : ℤ × ℤ) (hpq' : pq + (r, 1 - r) = pq')
    (hpq'' : pq' + (r, 1 - r) = pq'')
    (n₀ n₁ n₂ n₃ n₄ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃)
      (hn₄ : n₃ + 1 = n₄) (hn : pq.1 + pq.2 = n₁) (D : Arrow₇ ℤt)
      (hD₀ : D.X₀ = ℤt.mk (pq''.snd-r+2))
      (hD₁ : D.X₁ = ℤt.mk pq''.snd)
      (hD₂ : D.X₂ = ℤt.mk (pq''.snd + 1))
      (hD₃ : D.X₃ = ℤt.mk pq'.snd)
      (hD₄ : D.X₄ = ℤt.mk (pq'.snd + 1))
      (hD₅ : D.X₅ = ℤt.mk pq.snd)
      (hD₆ : D.X₆ = ℤt.mk (pq.snd+1))
      (hD₇ : D.X₇ = ℤt.mk (pq.snd+r-1)) :
    ShortComplex.mk _ _ (d_comp_d X r hr pq pq' pq'' hpq' hpq'') ≅
      X.shortComplexEEEObj n₀ n₁ n₂ n₃ n₄ hn₁ hn₂ hn₃ hn₄ D := by
  have h₁ : pq.1 + r = pq'.1 := congr_arg _root_.Prod.fst hpq'
  have h₂ : pq.2 + (1-r) = pq'.2 := congr_arg _root_.Prod.snd hpq'
  have h₃ : pq'.1 + r = pq''.1 := congr_arg _root_.Prod.fst hpq''
  have h₄ : pq'.2 + (1-r) = pq''.2 := congr_arg _root_.Prod.snd hpq''
  refine' ShortComplex.isoMk (pageIsoE X r hr pq n₀ n₁ n₂ hn₁ hn₂ hn _ _ hD₅ hD₆ hD₇)
    (pageIsoE X r hr pq' n₁ n₂ n₃ hn₂ hn₃ (by linarith) _ _ hD₃ hD₄ _)
    (pageIsoE X r hr pq'' n₂ n₃ n₄ hn₃ hn₄ (by linarith) _ hD₀ hD₁ hD₂ _) _ _
  · dsimp
    rw [hD₄]
    congr 1
    linarith
  · dsimp
    rw [hD₂]
    congr 1
    linarith
  · dsimp
    rw [hD₅]
    congr 1
    linarith
  · dsimp
    rw [hD₃]
    congr 1
    linarith
  · dsimp [shortComplexEEEObj]
    rw [d_eq X r hr pq pq' hpq' n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ (by linarith)
      ((Arrow₇.δ₀ ⋙ Arrow₆.δ₀).obj D), assoc, assoc]
    erw [Iso.inv_hom_id, comp_id]
    rfl
  · dsimp [shortComplexEEEObj]
    rw [d_eq X r hr pq' pq'' hpq'' n₁ n₂ n₃ n₄ hn₂ hn₃ hn₄ (by linarith)
      ((Arrow₇.δ₇ ⋙ Arrow₆.δ₆).obj D), assoc, assoc]
    erw [Iso.inv_hom_id, comp_id]
    rfl

noncomputable def iso (r r' : ℤ) (hr : 2 ≤ r) (hr' : r + 1 = r') (pq pq' pq'' : ℤ × ℤ)
    (hpq' : pq + (r, 1 - r) = pq') (hpq'' : pq' + (r, 1 - r) = pq'') :
    (ShortComplex.mk _ _ (ToE₂CohomologicalSpectralSequence.d_comp_d
      X r hr pq pq' pq'' hpq' hpq'')).homology ≅ page X r' (by linarith) pq' := by
  have h₁ : pq.1 + r = pq'.1 := congr_arg _root_.Prod.fst hpq'
  have h₂ : pq.2 + (1-r) = pq'.2 := congr_arg _root_.Prod.snd hpq'
  have h₄ : pq'.2 + (1-r) = pq''.2 := congr_arg _root_.Prod.snd hpq''
  let n := pq.1 + pq.2
  have hn : n = pq.1 + pq.2 := rfl
  refine' ShortComplex.homologyMapIso (shortComplexIso X r hr pq pq' pq'' hpq' hpq'' (n-1) n (n+1) (n+2) (n+3)
    _ _ _ _ (by linarith)
    (ιℤt.mapArrow₇.obj (Arrow₇.mkOfLE (pq''.2-r+2) pq''.2 (pq'.2-r+2) pq'.2 (pq.2-r+2) pq.2 (pq.2+1) (pq.2+r-1)))
    _ _ _ _ _ _ _ _) ≪≫
    X.homologyShortComplexEEEObjIso _ _ _ _ _ _ _ _ _ _ ≪≫
    (pageIsoE X r' _ _ _ _ _ _ _ _ _ _ _ _ _).symm
  all_goals try rfl
  all_goals try linarith
  all_goals dsimp ; congr 1 ; linarith

end ToE₂CohomologicalSpectralSequence

@[pp_dot]
noncomputable def toE₂CohomologicalSpectralSequence : E₂CohomologicalSpectralSequence C where
  page' := ToE₂CohomologicalSpectralSequence.page X
  d' := ToE₂CohomologicalSpectralSequence.d X
  d_comp_d' := ToE₂CohomologicalSpectralSequence.d_comp_d X
  iso' := ToE₂CohomologicalSpectralSequence.iso X

noncomputable def toE₂CohomologicalSpectralSequencePageIso (r : ℤ)
    [X.toE₂CohomologicalSpectralSequence.HasPage r] (pq : ℤ × ℤ)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
    (hpq : pq.1 + pq.2 = n₁) (q₀ q₁ q₂ : ℤ)
    (hq₀ : q₀ + r - 2 = pq.2) (hq₁ : pq.2 + 1 = q₁) (hq₂ : q₁ + r - 2 = q₂) :
    X.toE₂CohomologicalSpectralSequence.page r pq ≅
      (X.E n₀ n₁ n₂ hn₁ hn₂).obj (ιℤt.mapArrow₃.obj (by
        have := X.toE₂CohomologicalSpectralSequence.le_of_hasPage r
        exact Arrow₃.mkOfLE q₀ pq.2 q₁ q₂)) :=
  eqToIso (by
    obtain ⟨p, q⟩ := pq
    obtain rfl : n₀ = p + q - 1 := by linarith
    obtain rfl : n₁ = p + q := by linarith
    obtain rfl : n₂ = p + q + 1 := by linarith
    obtain rfl : q₀ = q-r+2 := by linarith
    obtain rfl : q₁ = q+1 := by linarith
    obtain rfl : q₂ = q+r-1 := by linarith
    rfl)

noncomputable def toE₂CohomologicalSpectralSequenceE₂pageIso
    (pq : ℤ × ℤ) (n : ℤ) (hn : pq.1 + pq.2 = n) (q' : ℤ) (hq' : pq.2 + 1 = q') :
    X.toE₂CohomologicalSpectralSequence.page 2 pq ≅
      (X.H n).obj (ιℤt.mapArrow.obj (Arrow.mkOfLE pq.2 q')) :=
  X.toE₂CohomologicalSpectralSequencePageIso 2 pq (n-1) n (n+1)
    (by linarith) _ hn pq.2 q' q' (by linarith) (by linarith) (by linarith) ≪≫
    X.EObjIsoH (n-1) n (n+1) _ rfl _ (by dsimp ; infer_instance) (by dsimp ; infer_instance)

lemma toE₂CohomologicalSpectralSequence_isZero_page
    (r : ℤ) [X.toE₂CohomologicalSpectralSequence.HasPage r] (p₀ q₀ : ℤ)
    [X.IsStationary (Bounds.quadrantUR p₀ q₀)] (pq : ℤ × ℤ) (hpq : pq.1 < p₀ ∨ pq.2 < q₀) :
    IsZero (X.toE₂CohomologicalSpectralSequence.page r pq) := by
  obtain ⟨p, q⟩ := pq
  apply X.isZero_E_of_isZero_H
  dsimp at hpq ⊢
  cases hpq
  · apply X.isZero₂_H (Bounds.quadrantUR p₀ q₀)
    apply homOfLE
    dsimp
    simp
    linarith
  · apply X.isZero₁_H (Bounds.quadrantUR p₀ q₀)
    apply homOfLE
    dsimp
    simp
    linarith

instance [X.IsStationary Bounds.firstQuadrant] :
    X.toE₂CohomologicalSpectralSequence.IsFirstQuadrant where
  isZero := by
    intro r hr pq hpq
    exact X.toE₂CohomologicalSpectralSequence_isZero_page r 0 0 pq hpq

noncomputable def toE₂CohomologicalSpectralSequencePageTwoIso
    (pq : ℤ × ℤ) (n : ℤ) (h : pq.1 + pq.2 = n)
    (q' : ℤ) (hq' : pq.2 + 1 = q'):
    X.toE₂CohomologicalSpectralSequence.page 2 pq ≅
      (X.H n).obj (Arrow.mk (homOfLE (show ℤt.mk pq.2 ≤ ℤt.mk q'
        by simp only [ℤt.mk_le_mk_iff] ; linarith))) := by
  refine' X.toE₂CohomologicalSpectralSequencePageIso 2 pq (n-1) n (n+1)
    (by linarith) (by linarith) h pq.2 q' q' (by linarith) hq' (by linarith) ≪≫ _
  refine' X.EObjIsoH (n-1) n (n+1) _ rfl _ _ _
  all_goals dsimp ; infer_instance

noncomputable def toE₂CohomologicalSpectralSequencePageInfinityIso (pq : ℤ × ℤ) (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn : pq.1 + pq.2 = n₁)
    (D : Arrow ℤt) (hD₀ : D.left = ℤt.mk pq.2) (hD₁ : D.right = ℤt.mk (pq.2+1))
    [X.IsStationary Bounds.firstQuadrant] :
    X.toE₂CohomologicalSpectralSequence.pageInfinity pq ≅ (X.EInfty n₀ n₁ n₂ hn₁ hn₂).obj D := by
  let r := max 2 (max (pq.fst + 1) (pq.snd + 2))
  refine' (X.toE₂CohomologicalSpectralSequence.isoPageInfinityOfLE pq r
    (X.toE₂CohomologicalSpectralSequence.rMin_le_of_isFirstQuadrant pq)).symm ≪≫
    X.toE₂CohomologicalSpectralSequencePageIso r pq n₀ n₁ n₂ hn₁ hn₂ hn
      (pq.2-r+2) (pq.2+1) (pq.2+r-1) (by linarith) (by linarith) (by linarith) ≪≫
    X.isoEInfty n₀ n₁ n₂ hn₁ hn₂ Bounds.firstQuadrant _ _ _ ≪≫
    Functor.mapIso _ (Arrow.isoMk (eqToIso hD₀.symm) (eqToIso hD₁.symm)
      (Subsingleton.elim _ _))
  · refine' homOfLE _
    dsimp
    simp only [ℤt.mk_le_mk_iff]
    change pq.2 - r + 2 ≤ 0
    have : pq.2 +2 ≤ r := (le_max_right _ _ ).trans (le_max_right _ _)
    linarith
  · refine' homOfLE _
    dsimp
    simp only [ℤt.mk_le_mk_iff, sub_zero, ge_iff_le, max_le_iff,
      add_le_iff_nonpos_left, le_max_iff, le_add_iff_nonneg_left, hn₁, ← hn]
    have : pq.1 +1 ≤ r := (le_max_left _ _ ).trans (le_max_right _ _)
    change pq.1 + pq.2 ≤ pq.2 + r - 1
    linarith

noncomputable def toE₂CohomologicalSpectralSequenceStronglyConvergesToOfBoundsFirstQuadrant
    [X.IsStationary Bounds.firstQuadrant] :
  X.toE₂CohomologicalSpectralSequence.StronglyConvergesTo
    (fun n => (X.H n).obj (Arrow.mkOfLE ⊥ ⊤ bot_le)) where
  stronglyConvergesToInDegree n :=
    { hasInfinityPageAt := inferInstance
      filtration' := ιℤt ⋙ X.filtration' n
      exists_isZero_filtration' :=
        ⟨0, X.isZero_filtration_obj_eq_bot Bounds.firstQuadrant _ _ (𝟙 _)⟩
      exists_isIso_filtration'_hom :=
        ⟨n + 1, X.isIso_filtrationι Bounds.firstQuadrant _ _ (homOfLE (by simp))⟩
      π' := fun i pq hpq => X.filtrationπ (n-1) n (n+1) (by linarith) (by linarith)
          (ℤt.mk (i-1)) (ℤt.mk i) (homOfLE (by simp)) ≫ (X.toE₂CohomologicalSpectralSequencePageInfinityIso pq (n-1) n (n+1)
          _ _ (cohomologicalStripes.stripe_eq n i pq hpq)
          (ιℤt.mapArrow.obj (Arrow.mkOfLE (i-1) i)) (by
            obtain ⟨p, q⟩ := pq
            dsimp [cohomologicalStripes] at hpq ⊢
            simp only [Prod.mk.injEq] at hpq
            congr 1
            linarith) (by
            obtain ⟨p, q⟩ := pq
            dsimp [cohomologicalStripes] at hpq ⊢
            simp only [Prod.mk.injEq] at hpq
            congr 1
            linarith)).inv
      epi_π' := fun i pq hpq => epi_comp _ _
      comp_π' := fun i j hij pq hpq => by
        obtain rfl : i = j - 1 := by linarith
        erw [(X.filtrationShortComplex (n-1) n (n+1) (by linarith) (by linarith)
          _ _ _).zero_assoc, zero_comp]
      exact' := fun i j hij pq hpq => by
        obtain rfl : i = j - 1 := by linarith
        refine' ShortComplex.exact_of_iso _
          ((X.filtrationShortComplex_shortExact (n-1) n (n+1) (by linarith) (by linarith)
            (ℤt.mk (j-1)) (ℤt.mk j) (homOfLE (by simp))).exact)
        refine' ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
          (X.toE₂CohomologicalSpectralSequencePageInfinityIso pq (n-1) n (n+1) _ _
          (cohomologicalStripes.stripe_eq n j pq hpq)
          (ιℤt.mapArrow.obj (Arrow.mkOfLE (j-1) j)) (by
            obtain ⟨p, q⟩ := pq
            dsimp [cohomologicalStripes] at hpq ⊢
            simp only [Prod.mk.injEq] at hpq
            congr 1
            linarith) (by
            obtain ⟨p, q⟩ := pq
            dsimp [cohomologicalStripes] at hpq ⊢
            simp only [Prod.mk.injEq] at hpq
            congr 1
            linarith)).symm _ _
        · dsimp
          simp only [id_comp, comp_id]
          rfl
        · dsimp
          simp only [id_comp, Iso.cancel_iso_inv_right]
          rfl }

end SpectralObject

end Abelian

end CategoryTheory

-/
