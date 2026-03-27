/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Rank
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexEvaluation
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# The relative cell complex attached to a rank function for a pairing

-/

@[expose] public section

universe v u

open CategoryTheory HomotopicalAlgebra Simplicial Limits Opposite

namespace SSet

lemma stdSimplex.map_objEquiv_op_apply
    {X : SSet.{u}} {n : SimplexCategory} (x : X.obj (op n))
    {m : SimplexCategoryᵒᵖ} (y : (stdSimplex.obj n).obj m) :
    X.map (stdSimplex.objEquiv y).op x = (yonedaEquiv.symm x).app m y :=
  rfl

lemma Subcomplex.existsN {X : SSet.{u}} {n : ℕ} (s : X _⦋n⦌) {A : X.Subcomplex}
    (hs : s ∉ A.obj _) :
    ∃ (x : A.N) (f : ⦋n⦌ ⟶ ⦋x.dim⦌), Epi f ∧ X.map f.op x.simplex = s := by
  refine ⟨⟨(S.mk s).toN, fun h ↦ hs ?_⟩, ?_⟩
  · simp only [← ofSimplex_le_iff] at h ⊢
    simpa using h
  · sorry

lemma Subcomplex.N.eq_iff_sMk_eq {X : SSet.{u}} {A : X.Subcomplex} (x y : A.N) :
    x = y ↔ S.mk x.1.1.2 = S.mk y.1.1.2 := by
  rw [N.ext_iff, SSet.N.ext_iff]

@[simp]
lemma Subcomplex.ofSimplex_map {X : SSet.{u}} {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) [Epi f]
    (x : X _⦋m⦌) :
    ofSimplex (X.map f.op x) = ofSimplex x := by
  refine le_antisymm ?_ ?_
  · simp only [Subfunctor.ofSection_le_iff]
    exact ⟨f.op, by simp⟩
  · simp only [Subfunctor.ofSection_le_iff]
    have := isSplitEpi_of_epi f
    exact ⟨(section_ f).op, by simp [← FunctorToTypes.map_comp_apply, ← op_comp]⟩

lemma S.eq_iff_ofSimplex_eq {X : SSet.{u}} {n m : ℕ} (x : X _⦋n⦌) (y : X _⦋m⦌)
    (hx : x ∈ X.nonDegenerate _) (hy : y ∈ X.nonDegenerate _) :
    S.mk x = S.mk y ↔ Subcomplex.ofSimplex x = Subcomplex.ofSimplex y := by
  trans N.mk x hx = N.mk y hy
  · exact (N.ext_iff (N.mk x hx) (N.mk y hy)).symm
  · simp only [le_antisymm_iff]
    rfl

lemma objEquiv_symm_notMem_horn_of_isIso {n : ℕ} (i : Fin (n + 1))
    {d : SimplexCategory} (f : d ⟶ ⦋n⦌) [IsIso f] :
    stdSimplex.objEquiv.symm f ∉ (horn n i).obj (op d) := by
  sorry

lemma objEquiv_symm_δ_mem_horn_iff {n : ℕ} (i j : Fin (n + 2)) :
    stdSimplex.objEquiv.symm (SimplexCategory.δ i) ∈ (horn _ j).obj _ ↔
      i ≠ j := by
  sorry

end SSet

namespace SSet.Subcomplex.Pairing

variable {X : SSet.{u}} {A : X.Subcomplex} {P : A.Pairing}

namespace RankFunction

variable {ι : Type v} [LinearOrder ι] (f : P.RankFunction ι)

def Cells (i : ι) : Type u := { s : P.II // f.rank s = i }

namespace Cells

variable {f} {i : ι} (c : f.Cells i)

variable {c} in
@[ext]
lemma ext {c' : f.Cells i} (h : c.1 = c'.1) : c = c' :=
  Subtype.ext h

abbrev dim : ℕ := c.1.1.dim

variable [P.IsProper]

noncomputable def index : Fin (c.dim + 2) :=
  (P.isUniquelyCodimOneFace c.1).index rfl

protected noncomputable abbrev horn :
    (Δ[c.dim + 1] : SSet.{u}).Subcomplex :=
  SSet.horn _ c.index

abbrev cast : A.N := (P.p c.1).1.cast (P.isUniquelyCodimOneFace c.1).dim_eq

--abbrev simplex : X _⦋c.dim + 1⦌ := c.cast.simplex

/-lemma ofSimplex_simplex :
    Subcomplex.ofSimplex c.simplex = (P.p c.1).1.subcomplex := by
  rw [S.ofSimplex_eq_subcomplex_mk]
  congr 1
  exact S.cast_eq_self _ (by simp)-/

abbrev map :
    Δ[c.dim + 1] ⟶ X :=
  yonedaEquiv.symm c.cast.simplex

@[simp]
lemma range_map : Subcomplex.range c.map = (P.p c.1).1.subcomplex := by
  rw [range_eq_ofSimplex, Equiv.apply_symm_apply, S.ofSimplex_eq_subcomplex_mk,
    ← S.cast_eq_self _ (P.dim_p c.1)]
  rfl

lemma map_app_objEquiv_symm_δ_index :
    c.map.app (op ⦋_⦌) (stdSimplex.objEquiv.symm (SimplexCategory.δ c.index)) =
      c.1.1.simplex :=
  (P.isUniquelyCodimOneFace c.1).δ_index rfl

lemma subcomplex_not_le_image_horn :
    ¬ c.1.1.subcomplex ≤ c.horn.image c.map := by
  intro h
  simp only [Subfunctor.ofSection_le_iff, image_obj, Set.mem_image] at h
  obtain ⟨x, h₁, h₂⟩ := h
  obtain ⟨g, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  dsimp at g
  rw [← stdSimplex.map_objEquiv_op_apply, Equiv.apply_symm_apply] at h₂
  have := mono_of_nonDegenerate (x:= ⟨_, c.1.1.nonDegenerate⟩) _ _ _ h₂
  obtain rfl := (P.isUniquelyCodimOneFace c.1).unique rfl _ h₂
  rw [← ofSimplex_le_iff, stdSimplex.subcomplex_le_horn_iff,
    ← stdSimplex.face_singleton_compl] at h₁
  tauto

lemma image_horn_lt_subcomplex :
    c.horn.image c.map < (P.p c.1).1.subcomplex := by
  rw [lt_iff_le_and_ne]
  refine ⟨by simpa using image_le_range c.horn c.map,
    fun h ↦ c.subcomplex_not_le_image_horn (by simpa only [h] using P.le c.1)⟩

@[simp]
lemma image_face_index_compl :
    (stdSimplex.face {c.index}ᶜ).image c.map = c.1.1.subcomplex := by
  rw [stdSimplex.face_singleton_compl, image_ofSimplex]
  congr 1
  exact (P.isUniquelyCodimOneFace c.1).δ_index rfl

end Cells

variable [P.IsProper] in
noncomputable abbrev basicCell (i : ι) (c : f.Cells i) := c.horn.ι

def filtration (i : ι) : X.Subcomplex :=
  A ⊔ ⨆ (j : ι) (_ : j < i) (c : f.Cells j), (P.p c.1).1.subcomplex

lemma subcomplex_le_filtration {j : ι} (c : f.Cells j) {i : ι} (h : j < i) :
    (P.p c.1).1.subcomplex ≤ f.filtration i := by
  refine le_trans ?_ le_sup_right
  refine le_trans ?_ (le_iSup _ j)
  refine le_trans ?_ (le_iSup _ h)
  exact le_trans (by rfl) (le_iSup _ c)

@[simp]
lemma le_filtration (i : ι) : A ≤ f.filtration i := le_sup_left

@[simp]
lemma filtration_bot [OrderBot ι] : f.filtration ⊥ = A := by
  simp [filtration]

lemma filtration_monotone : Monotone f.filtration := by
  intro i₁ i₂ h
  rw [filtration]
  simp only [sup_le_iff, iSup_le_iff, le_filtration, true_and]
  intro j hj c
  exact f.subcomplex_le_filtration c (lt_of_lt_of_le hj h)

lemma filtration_succ [SuccOrder ι] (i : ι) (hi : ¬ IsMax i) :
    f.filtration (Order.succ i) =
      f.filtration i ⊔ ⨆ (c : f.Cells i), (P.p c.1).1.subcomplex := by
  apply le_antisymm
  · rw [filtration]
    simp only [sup_le_iff, iSup_le_iff]
    refine ⟨(f.le_filtration _).trans le_sup_left, fun j hj c ↦ ?_⟩
    rw [Order.lt_succ_iff_of_not_isMax hi] at hj
    obtain hj | rfl := hj.lt_or_eq
    · exact (f.subcomplex_le_filtration _ hj).trans le_sup_left
    · exact le_trans (le_trans (by rfl) (le_iSup _ c)) le_sup_right
  · simp only [sup_le_iff, iSup_le_iff]
    exact ⟨f.filtration_monotone (Order.le_succ i),
      fun c ↦ f.subcomplex_le_filtration _ (Order.lt_succ_of_not_isMax hi)⟩

lemma filtration_of_isSuccLimit [OrderBot ι] [SuccOrder ι]
    (i : ι) (hi : Order.IsSuccLimit i) :
    f.filtration i = ⨆ (j : ι) (_ : j < i), f.filtration j := by
  apply le_antisymm
  · rw [filtration]
    simp only [sup_le_iff, iSup_le_iff]
    refine ⟨?_, fun j hj c ↦ ?_⟩
    · refine le_trans ?_ (le_iSup _ ⊥)
      exact le_trans (by simp) (le_iSup _ hi.bot_lt)
    · refine le_trans ?_ (le_iSup _ (Order.succ j))
      refine le_trans ?_ (le_iSup _
        (by rwa [← Order.IsSuccLimit.succ_lt_iff hi] at hj))
      exact f.subcomplex_le_filtration _ (Order.lt_succ_of_not_isMax hj.not_isMax)
  · simp only [iSup_le_iff]
    intro j hj
    exact f.filtration_monotone hj.le

lemma iSup_filtration_iio [OrderBot ι] [SuccOrder ι] (m : ι) (hm : Order.IsSuccLimit m) :
    ⨆ (i : Set.Iio m), f.filtration i = f.filtration m :=
  le_antisymm (by
    simp only [iSup_le_iff, Subtype.forall, Set.mem_Iio]
    intro j hj
    exact f.filtration_monotone hj.le) (by
    rw [filtration]
    simp only [sup_le_iff, iSup_le_iff, ← f.filtration_bot]
    exact ⟨le_trans (by rfl) (le_iSup _ ⟨⊥, hm.bot_lt⟩), fun j hj c ↦
      (f.subcomplex_le_filtration c (Order.lt_succ_of_not_isMax (not_isMax_of_lt hj))).trans
        (le_trans (by rfl) (le_iSup _ ⟨Order.succ j, hm.succ_lt_iff.2 hj⟩))⟩)

variable {f} in
lemma Cells.subcomplex_not_le_filtration {j : ι} (x : f.Cells j) :
    ¬ x.1.1.subcomplex ≤ f.filtration j := by
  rw [ofSimplex_le_iff]
  simp only [filtration, Subfunctor.max_obj, Subfunctor.iSup_obj, Set.mem_union,
    Set.mem_iUnion, not_or, not_exists]
  refine ⟨x.1.1.notMem, fun i hi y h ↦ ?_⟩
  rw [← x.2, ← y.2] at hi
  have : P.AncestralRel x.1 y.1 := by
    refine ⟨fun hxy ↦ ?_, lt_of_le_of_ne ?_ ((P.ne _ _).symm)⟩
    · rw [hxy] at hi
      exact (lt_irrefl _ hi).elim
    · rw [← ofSimplex_le_iff] at h
      rwa [Subcomplex.N.le_iff, SSet.N.le_iff]
  exact lt_irrefl _ (hi.trans (f.lt this))

variable [P.IsProper]

set_option backward.isDefEq.respectTransparency false in
lemma iSup_filtration [OrderBot ι] [SuccOrder ι] [NoMaxOrder ι] :
    ⨆ (i : ι), f.filtration i = ⊤ := by
  refine le_antisymm (by simp) ?_
  rw [N.subcomplex_le_iff]
  intro s _
  induction s using SSet.Subcomplex.N.cases A with
  | mem s hs => exact hs.trans (le_trans (by simp) (le_iSup _ ⊥))
  | notMem s =>
    obtain ⟨t, ht⟩ := P.exists_or s
    refine le_trans ?_
      (le_trans (f.subcomplex_le_filtration ⟨t, rfl⟩ (Order.lt_succ _)) (le_iSup _ _))
    obtain rfl | rfl := ht
    · exact P.le t
    · rfl

def Cells.mapToSucc {j : ι} [SuccOrder ι] [NoMaxOrder ι] (c : f.Cells j) :
    Δ[c.dim + 1] ⟶ f.filtration (Order.succ j) :=
  Subcomplex.lift c.map (by
    rw [range_map]
    exact f.subcomplex_le_filtration c (Order.lt_succ _))

@[reassoc (attr := simp)]
lemma Cells.mapToSucc_ι {j : ι} [SuccOrder ι] [NoMaxOrder ι] (c : f.Cells j) :
    c.mapToSucc ≫ (f.filtration (Order.succ j)).ι = c.map :=
  rfl

section

noncomputable abbrev sigmaHorn (j : ι) : SSet.{u} :=
  ∐ fun (c : f.Cells j) ↦ c.horn

noncomputable abbrev Cells.ιSigmaHorn {j : ι} (c : f.Cells j) :
    (c.horn : SSet) ⟶ f.sigmaHorn j :=
  Sigma.ι (fun (c : f.Cells j) ↦ (c.horn : SSet)) c

noncomputable abbrev sigmaStdSimplex (j : ι) : SSet.{u} :=
  ∐ fun (i : f.Cells j) ↦ Δ[i.dim + 1]

noncomputable abbrev Cells.ιSigmaStdSimplex {j : ι} (c : f.Cells j) :
    Δ[c.dim + 1] ⟶ f.sigmaStdSimplex j :=
  Sigma.ι (fun (c : f.Cells j) ↦ Δ[c.dim + 1]) c

lemma ιSigmaHorn_jointly_surjective
    {d : ℕ} {j : ι} (a : (f.sigmaHorn j) _⦋d⦌) :
    ∃ (c : f.Cells j) (x : (c.horn : SSet) _⦋d⦌), c.ιSigmaHorn.app _ x = a :=
  Limits.Cofan.inj_jointly_surjective_of_isColimit
    ((isColimitCofanMkObjOfIsColimit ((CategoryTheory.evaluation _ _).obj _) _ _
      (coproductIsCoproduct _))) a

omit [P.IsProper] in
lemma ιSigmaStdSimplex_jointly_surjective
    {d : ℕ} {j : ι} (a : (f.sigmaStdSimplex j) _⦋d⦌) :
    ∃ (c : f.Cells j) (x :  Δ[c.dim + 1] _⦋d⦌), c.ιSigmaStdSimplex.app _ x = a :=
  Limits.Cofan.inj_jointly_surjective_of_isColimit
    ((isColimitCofanMkObjOfIsColimit ((CategoryTheory.evaluation _ _).obj _) _ _
      (coproductIsCoproduct _))) a

lemma ιSigmaStdSimplex_eq_iff {j : ι} {d : ℕ}
    (x : f.Cells j) (s : (Δ[x.dim + 1] : SSet.{u}) _⦋d⦌)
    (y : f.Cells j) (t : (Δ[y.dim + 1] : SSet.{u}) _⦋d⦌) :
    x.ιSigmaStdSimplex.app (op ⦋d⦌) s = y.ιSigmaStdSimplex.app (op ⦋d⦌) t ↔
      ∃ (h : x = y), t = cast (by rw [h]) s := by
  sorry

instance {j : ι} (c : f.Cells j) :
    Mono c.ιSigmaStdSimplex := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨d⟩
  induction d using SimplexCategory.rec with | _ d
  rw [mono_iff_injective]
  intro x y h
  simpa [f.ιSigmaStdSimplex_eq_iff] using h.symm

noncomputable def m (j : ι) : f.sigmaHorn j ⟶ f.sigmaStdSimplex j :=
  Limits.Sigma.map (basicCell _ _)

instance (j : ι) : Mono (f.m j) :=
  MorphismProperty.colimitsOfShape_le (W := .monomorphisms _) _
    (MorphismProperty.colimitsOfShape_colimMap _ (fun ⟨c⟩ ↦ by
      dsimp only [Discrete.functor_obj_eq_as, Discrete.natTrans_app]
      simp only [MorphismProperty.monomorphisms.iff]
      infer_instance))

@[reassoc (attr := simp)]
lemma Cells.ι_m {j : ι} (c : f.Cells j) :
    c.ιSigmaHorn ≫ f.m j = c.horn.ι ≫ c.ιSigmaStdSimplex := by
  simp [m]

@[simp]
lemma Cells.preimage_filtration_map {j : ι} (c : f.Cells j) :
    (f.filtration j).preimage c.map = c.horn := by
  refine le_antisymm ?_ ?_
  · simpa only [stdSimplex.subcomplex_le_horn_iff, ← Subcomplex.image_le_iff,
      Cells.image_face_index_compl] using c.subcomplex_not_le_filtration
  · rw [← Subcomplex.image_le_iff, N.subcomplex_le_iff]
    intro s hs
    induction s using SSet.Subcomplex.N.cases A with
    | mem s hs' => exact hs'.trans (by simp)
    | notMem s =>
      obtain ⟨t, ht⟩ := P.exists_or s
      rw [← c.prop]
      refine le_trans ?_ (f.subcomplex_le_filtration ⟨t, rfl⟩ (f.lt ?_))
      · obtain rfl | rfl := ht
        · exact P.le t
        · simp
      · replace hs : t.1.subcomplex ≤ c.horn.image c.map := by
          obtain rfl | rfl := ht
          · exact hs
          · refine le_trans ?_ hs
            rw [← S.le_def]
            exact (P.isUniquelyCodimOneFace t).le
        refine ⟨?_, ?_⟩
        · rintro rfl
          exact c.subcomplex_not_le_image_horn hs
        · rw [Subcomplex.N.lt_iff, SSet.N.lt_iff]
          exact lt_of_le_of_lt hs (c.image_horn_lt_subcomplex)

noncomputable def Cells.mapHorn {j : ι} (c : f.Cells j) : (c.horn : SSet) ⟶ f.filtration j :=
  Subcomplex.lift (c.horn.ι ≫ c.map) (by
    simp [← image_top, image_le_iff, preimage_comp, c.preimage_filtration_map])

@[reassoc (attr := simp)]
lemma Cells.mapHorn_ι {j : ι} (c : f.Cells j) :
    c.mapHorn ≫ (f.filtration j).ι = c.horn.ι ≫ c.map := rfl

noncomputable def t (j : ι) : f.sigmaHorn j ⟶ f.filtration j :=
  Limits.Sigma.desc (fun c ↦ c.mapHorn)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma Cells.ι_t {j : ι} (c : f.Cells j) :
    c.ιSigmaHorn ≫ f.t j = c.mapHorn:= by
  simp [t]

variable [SuccOrder ι] [NoMaxOrder ι]

noncomputable def b (j : ι) :
    f.sigmaStdSimplex j ⟶ f.filtration (Order.succ j) :=
  Sigma.desc (fun c ↦ c.mapToSucc)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma Cells.ι_b {j : ι} (c : f.Cells j) :
    c.ιSigmaStdSimplex ≫ f.b j = c.mapToSucc := by simp [b]

@[reassoc]
lemma w (j : ι) :
    f.t j ≫ homOfLE (f.filtration_monotone (Order.le_succ j)) = f.m j ≫ f.b j := by
  ext c : 1
  simp [← cancel_mono (Subcomplex.ι _)]

@[simps]
noncomputable def Cells.type₁ {j : ι} (c : f.Cells j) :
    (Subcomplex.range (f.m j)).N where
  simplex := c.ιSigmaStdSimplex.app _ (stdSimplex.objEquiv.symm (𝟙 _))
  nonDegenerate := by
    rw [nonDegenerate_iff_of_mono,
      stdSimplex.mem_nonDegenerate_iff_mono,
      Equiv.apply_symm_apply]
    infer_instance
  notMem := by
    rintro ⟨y, hy⟩
    obtain ⟨x', ⟨y, hy'⟩, rfl⟩ := f.ιSigmaHorn_jointly_surjective y
    rw [← FunctorToTypes.comp, ι_m, FunctorToTypes.comp,
      ιSigmaStdSimplex_eq_iff] at hy
    obtain ⟨rfl, rfl⟩ := hy
    exact objEquiv_symm_notMem_horn_of_isIso _ _ hy'

@[simps]
noncomputable def Cells.type₂ {j : ι} (c : f.Cells j) :
    (Subcomplex.range (f.m j)).N where
  simplex := c.ιSigmaStdSimplex.app _
    (stdSimplex.objEquiv.symm (SimplexCategory.δ c.index))
  nonDegenerate := by
    rw [nonDegenerate_iff_of_mono,
      stdSimplex.mem_nonDegenerate_iff_mono,
      Equiv.apply_symm_apply]
    infer_instance
  notMem := by
    rintro ⟨y, hy⟩
    obtain ⟨x', ⟨y, hy'⟩, rfl⟩ := f.ιSigmaHorn_jointly_surjective y
    rw [← FunctorToTypes.comp, ι_m, FunctorToTypes.comp,
      ιSigmaStdSimplex_eq_iff] at hy
    obtain ⟨rfl, rfl⟩ := hy
    simpa using (objEquiv_symm_δ_mem_horn_iff _ _).1 hy'

lemma isPullback (j : ι) : IsPullback (f.t j) (f.m j)
      (homOfLE (f.filtration_monotone (Order.le_succ j))) (f.b j) where
  w := f.w j
  isLimit' := ⟨evaluationJointlyReflectsLimits _ (fun ⟨d⟩ ↦ by
    refine (isLimitMapConePullbackConeEquiv _ _).2
      (IsPullback.isLimit ?_)
    induction d using SimplexCategory.rec with | _ d
    rw [Types.isPullback_iff]
    dsimp
    refine ⟨congr_app (f.w j) (op ⦋d⦌),
      fun a₁ a₂ h ↦ (mono_iff_injective _).1
        ((NatTrans.mono_iff_mono_app (f.m j)).1 inferInstance _) h.2, fun y b h ↦ ?_⟩
    obtain ⟨x, b, rfl⟩ := f.ιSigmaStdSimplex_jointly_surjective b
    have hb : b ∈ Λ[_, x.index].obj _ := by
      obtain ⟨y, hy⟩ := y
      simp only [← x.preimage_filtration_map]
      rw [Subtype.ext_iff] at h
      dsimp at h
      subst h
      rwa [← FunctorToTypes.comp, x.ι_b] at hy
    refine ⟨x.ιSigmaHorn.app _ ⟨b, hb⟩, ?_, by simp [← FunctorToTypes.comp]⟩
    rw [Subtype.ext_iff] at h ⊢
    dsimp at h
    rw [← FunctorToTypes.comp, x.ι_b] at h
    rw [← FunctorToTypes.comp, x.ι_t]
    exact h.symm)⟩

set_option backward.isDefEq.respectTransparency false in
lemma range_homOfLE_app_union_range_b_app (j : ι) (d : SimplexCategoryᵒᵖ) :
    Set.range ((homOfLE (f.filtration_monotone (Order.le_succ j))).app d) ⊔
      Set.range ((f.b j).app d) = Set.univ := by
  ext ⟨x, hx⟩
  simp only [filtration, Order.lt_succ_iff, Subfunctor.max_obj, Subfunctor.iSup_obj, Set.mem_union,
    Set.mem_iUnion, exists_prop, Subfunctor.toFunctor_obj, Set.sup_eq_union, Set.mem_range,
    Subtype.ext_iff, Subfunctor.homOfLe_app_coe, Subtype.exists, exists_eq_right, Set.mem_univ,
    iff_true] at hx ⊢
  obtain hx | ⟨i, hi, c, hx⟩ := hx
  · exact Or.inl (Or.inl hx)
  · obtain hi | rfl := hi.lt_or_eq
    · exact Or.inl (Or.inr ⟨i, hi, c, hx⟩)
    · rw [← c.range_map, ← c.mapToSucc_ι, ← c.ι_b_assoc] at hx
      obtain ⟨y, hy⟩ := hx
      exact Or.inr ⟨_, hy⟩

noncomputable def mapN {j : ι} (x : (Subcomplex.range (f.m j)).N) : X.S :=
  S.mk ((f.b j).app _ x.1.1.2).1

@[simp]
lemma mapN_type₁ {j : ι} (c : f.Cells j) :
    f.mapN c.type₁ = S.mk (P.p c.1).1.simplex := by
  dsimp only [Cells.type₁, mapN]
  rw [← S.cast_eq_self _ (P.dim_p c.1)]
  dsimp
  rw [S.ext_iff, ← FunctorToTypes.comp, c.ι_b]
  apply yonedaEquiv_symm_app_id

@[simp]
lemma mapN_type₂ {j : ι} (c : f.Cells j) :
    f.mapN c.type₂ = S.mk c.1.1.simplex := by
  dsimp [mapN]
  rw [S.ext_iff, ← FunctorToTypes.comp, c.ι_b, Cells.mapToSucc,
    lift_app_coe, Cells.map_app_objEquiv_symm_δ_index]

lemma exists_or_of_range_m_N {j : ι}
    (s : (Subcomplex.range (f.m j)).N) :
    ∃ (c : f.Cells j), s = c.type₁ ∨ s = c.type₂ := by
  sorry

lemma isPushout_aux₁ {j : ι}
    (s : (Subcomplex.range (f.m j)).N) :
    (f.mapN s).simplex  ∈ SSet.nonDegenerate _ _ := by
  obtain ⟨c, rfl | rfl⟩ := f.exists_or_of_range_m_N s
  · rw [f.mapN_type₁]
    exact (P.p c.1).1.nonDegenerate
  · rw [f.mapN_type₂]
    exact c.1.1.nonDegenerate

lemma isPushout_aux₂ {j : ι} :
    Function.Injective (f.mapN (j := j)) := by
  intro s t h
  obtain ⟨c, rfl | rfl⟩ := f.exists_or_of_range_m_N s <;>
    obtain ⟨c', rfl | rfl⟩ := f.exists_or_of_range_m_N t <;>
    simp only [mapN_type₁, mapN_type₂, ← Subcomplex.N.eq_iff_sMk_eq,
      ← Subtype.ext_iff] at h
  · obtain rfl : c = c' := by
      ext : 1
      exact P.p.injective h
    rfl
  · exact (P.ne _ _ h).elim
  · exact (P.ne _ _ h.symm).elim
  · rw [h]

lemma isPushout_aux₃ {j : ι} :
    Function.Injective fun (x : (Subcomplex.range (f.m j)).N) ↦ S.mk ((f.b j).app _ x.1.1.2) :=
  fun _ _ h ↦ f.isPushout_aux₂ (congr_arg (S.map (Subcomplex.ι _)) h)

set_option backward.isDefEq.respectTransparency false in
lemma isPushout (j : ι) :
    IsPushout (f.t j) (f.m j)
      (homOfLE (f.filtration_monotone (Order.le_succ j))) (f.b j) where
  w := f.w j
  isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun ⟨d⟩ ↦ by
    induction d using SimplexCategory.rec with | _ d
    refine (isColimitMapCoconePushoutCoconeEquiv _ _).2
      (IsPushout.isColimit ?_)
    dsimp
    refine Limits.Types.isPushout_of_isPullback_of_mono'
      ((f.isPullback j).map ((CategoryTheory.evaluation _ _).obj _))
      (f.range_homOfLE_app_union_range_b_app _ _) (fun x₁ x₂ hx₁ hx₂ h ↦ ?_)
    obtain ⟨s₁, g₁, _, hg₁⟩ := (Subcomplex.range (f.m j)).existsN x₁ hx₁
    obtain ⟨s₂, g₂, _, hg₂⟩ := (Subcomplex.range (f.m j)).existsN x₂ hx₂
    obtain rfl : s₁ = s₂ := f.isPushout_aux₃ (by
      dsimp
      rw [S.eq_iff_ofSimplex_eq,
        ← Subcomplex.ofSimplex_map g₁, ← FunctorToTypes.naturality,
        ← Subcomplex.ofSimplex_map g₂, ← FunctorToTypes.naturality,
        hg₁, hg₂, h]
      all_goals
      · rw [Subcomplex.mem_nonDegenerate_iff]
        apply f.isPushout_aux₁)
    obtain rfl := X.unique_nonDegenerate_map (x := (((f.b _)).app _ x₁).1)
      g₁ ⟨_, f.isPushout_aux₁ s₁⟩ (by simp [mapN, ← hg₁, FunctorToTypes.naturality])
      g₂ ⟨_, f.isPushout_aux₁ s₁⟩ (by simp [mapN, h, ← hg₂, FunctorToTypes.naturality])
    rw [← hg₁, hg₂])⟩

end

variable [SuccOrder ι] [OrderBot ι] [NoMaxOrder ι] [WellFoundedLT ι]

instance : f.filtration_monotone.functor.IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨Preorder.isColimitOfIsLUB _ _ (by
    dsimp
    rw [← f.iSup_filtration_iio m hm]
    apply isLUB_iSup)⟩

noncomputable def relativeCellComplex : RelativeCellComplex f.basicCell A.ι where
  F := f.filtration_monotone.functor ⋙ Subcomplex.toSSetFunctor
  isoBot := Subcomplex.eqToIso (filtration_bot _)
  isColimit :=
    IsColimit.ofIsoColimit (isColimitOfPreserves Subcomplex.toSSetFunctor
      (Preorder.colimitCoconeOfIsLUB f.filtration_monotone.functor (pt := ⊤)
        (by rw [← f.iSup_filtration]; apply isLUB_iSup)).isColimit)
        (Cocone.ext (Subcomplex.topIso _))
  isWellOrderContinuous :=
    ⟨fun m hm ↦ ⟨isColimitOfPreserves Subcomplex.toSSetFunctor
      (Functor.isColimitOfIsWellOrderContinuous f.filtration_monotone.functor m hm)⟩⟩
  incl.app i := (f.filtration i).ι
  attachCells j _ :=
    { ι := f.Cells j
      π := id
      cofan₁ := _
      cofan₂ := _
      isColimit₁ := colimit.isColimit _
      isColimit₂ := colimit.isColimit _
      m := f.m j
      hm c := c.ι_m
      g₁ := f.t j
      g₂ := f.b j
      isPushout := f.isPushout j }

end RankFunction

end SSet.Subcomplex.Pairing
