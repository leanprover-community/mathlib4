import Mathlib.Algebra.Homology.Embedding.StupidFiltration
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.TotalComplexShift

open CategoryTheory Category Limits ComplexShape

instance {C ι : Type*} [Category C] [HasZeroMorphisms C]
    {c : ComplexShape ι} (i : ι) :
    (HomologicalComplex.eval C c i).PreservesZeroMorphisms where

namespace CategoryTheory

variable {C : Type*} [Category C]

namespace GradedObject

instance {I : Type*} (i : I) [HasZeroMorphisms C] :
    (GradedObject.eval i : GradedObject I C ⥤ C).PreservesZeroMorphisms where

instance {I : Type*} (i : I) [Preadditive C] :
    (GradedObject.eval i : GradedObject I C ⥤ C).Additive where

variable [Preadditive C]
variable {I : Type*} (S : ShortComplex (GradedObject I C))
  {J : Type*} (p : I → J)
  [S.X₁.HasMap p] [S.X₂.HasMap p] [S.X₃.HasMap p]

@[simps]
noncomputable def mapShortComplex : ShortComplex (GradedObject J C) where
  f := mapMap S.f p
  g := mapMap S.g p
  zero := by rw [← mapMap_comp, S.zero, mapMap_zero]

@[simps]
def shortComplexSplittingEquiv :
    S.Splitting ≃ (∀ (i : I), (S.map (eval i)).Splitting) where
  toFun σ i := σ.map (eval i)
  invFun τ :=
    { r := fun i => (τ i).r
      s := fun i => (τ i).s
      s_g := by ext i; exact (τ i).s_g
      f_r := by ext i; exact (τ i).f_r
      id := by ext i; exact (τ i).id }
  left_inv _ := rfl
  right_inv _ := rfl

@[simps]
noncomputable def mapShortComplexSplitting (σ : S.Splitting) :
    (mapShortComplex S p).Splitting where
  r := mapMap σ.r p
  s := mapMap σ.s p
  s_g := by
    dsimp only [mapShortComplex]
    rw [← mapMap_comp, σ.s_g, mapMap_id]
  f_r := by
    dsimp only [mapShortComplex]
    rw [← mapMap_comp, σ.f_r, mapMap_id]
  id := by
    dsimp only [mapShortComplex]
    rw [← mapMap_comp, ← mapMap_comp, ← mapMap_add, σ.id, mapMap_id]

end GradedObject

namespace Limits

section

variable [IsIdempotentComplete C] {I : Type*}
  {X : I → C} (Y : I → C)
  (hX : ∀ (i : I), DirectFactor (X i) (Y i))

lemma hasCoproduct_of_direct_factor [HasCoproduct Y] : HasCoproduct X := by
  let p : ∐ Y ⟶ ∐ Y := Sigma.map (fun i => (hX i).r ≫ (hX i).s)
  obtain ⟨S, h, fac⟩ := directFactor_of_isIdempotentComplete _ p (by aesop_cat)
  refine ⟨Cofan.mk S (fun i => (hX i).s ≫ Sigma.ι Y i ≫ h.r),
    mkCofanColimit _ (fun c => h.s ≫ Sigma.desc (fun i => (hX i).r ≫ c.inj i))
      (fun c i => by simp [p, reassoc_of% fac])
      (fun c m hm => ?_)⟩
  dsimp at m ⊢
  rw [← cancel_epi h.r]
  ext i
  simp [← hm, reassoc_of% fac, p]
  simp only [← assoc]
  congr 1
  rw [← cancel_mono h.s]
  simp [fac, p]

end

section

variable [HasZeroMorphisms C] {I : Type*} (X : I → C) {J : Type*} (ι : J → I)
  [HasCoproduct (X ∘ ι)] (hι : Function.Injective ι)
  (hX : ∀ (i : I), ¬ i ∈ Set.range ι → IsZero (X i))

open Classical in
@[simps! pt]
noncomputable def cofanOfIsZero : Cofan X := Cofan.mk (∐ (X ∘ ι)) (fun i =>
  if hi : i ∈ Set.range ι
  then eqToHom (by
    congr
    exact hi.choose_spec.symm) ≫ Sigma.ι _ hi.choose
  else 0)

lemma cofanOfIsZero_inj (j : J) :
    (cofanOfIsZero X ι).inj (ι j) = Sigma.ι (X ∘ ι) j := by
  dsimp [cofanOfIsZero]
  have hi : ι j ∈ Set.range ι := ⟨j, rfl⟩
  rw [dif_pos hi]
  apply Sigma.eqToHom_comp_ι (X ∘ ι)
  exact (hι hi.choose_spec).symm

noncomputable def isColimitCofanOfIsZero : IsColimit (cofanOfIsZero X ι) :=
  mkCofanColimit _ (fun s => Sigma.desc (fun j => s.inj (ι j)))
    (fun s i => by
      by_cases hi : i ∈ Set.range ι
      · obtain ⟨j, rfl⟩ := hi
        dsimp
        simp [cofanOfIsZero_inj _ _ hι]
      · apply (hX i hi).eq_of_src)
    (fun s m hm => by
      dsimp
      ext j
      simp only [colimit.ι_desc, Cofan.mk_ι_app, ← hm, cofanOfIsZero_inj _ _ hι])

lemma hasCoproduct_of_isZero : HasCoproduct X :=
  ⟨_, isColimitCofanOfIsZero X ι hι hX⟩

end

section

variable {I : Type*} (X : I → C) (i : I)
    (hX : ∀ j, j ≠ i → IsZero (X j))

open Classical in
@[simp]
noncomputable def cofanOfIsZeroButOne : Cofan X := Cofan.mk (X i)
  (fun j => if h : j = i then eqToHom (by rw [h]) else (hX _ h).to_ _)

@[simp]
lemma cofanOfIsZeroButOne_ι_self :
    (cofanOfIsZeroButOne X i hX).inj i = 𝟙 _ :=
  dif_pos rfl

def isColimitCofanOfIsZeroButOne :
    IsColimit (cofanOfIsZeroButOne X i hX) :=
  mkCofanColimit _ (fun s => s.inj i) (fun s j => by
    by_cases hj : j = i
    · subst hj
      simp
    · apply (hX _ hj).eq_of_src) (fun s m hm => by
      dsimp
      simpa using hm i)

lemma hasCoproduct_of_isZero_but_one : HasCoproduct X :=
  ⟨⟨_, isColimitCofanOfIsZeroButOne X i hX⟩⟩

end

end Limits

end CategoryTheory

namespace HomologicalComplex₂

variable {C D : Type*} [Category C] [Preadditive C]
  {ι₁ ι₂ ι : Type*} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

section

variable [IsIdempotentComplete C]
  {K : HomologicalComplex₂ C c₁ c₂} (L : HomologicalComplex₂ C c₁ c₂)
  (c : ComplexShape ι) [TotalComplexShape c₁ c₂ c]
  (h : ∀ i₁ i₂, DirectFactor ((K.X i₁).X i₂) ((L.X i₁).X i₂))

lemma hasTotal_of_directFactor [L.HasTotal c] : K.HasTotal c :=
  fun i => hasCoproduct_of_direct_factor
    (GradedObject.mapObjFun L.toGradedObject (π c₁ c₂ c) i) (fun _ => h _ _)

variable {ι₁' : Type*} {c₁' : ComplexShape ι₁'} (e : c₁'.Embedding c₁) [e.IsRelIff]
  [HasZeroObject C]

instance [K.HasTotal c] : HomologicalComplex₂.HasTotal (K.stupidTrunc e) c :=
  hasTotal_of_directFactor K c
    (fun i₁ i₂ => (K.stupidTruncDirectFactor e i₁).map (HomologicalComplex.eval _ _ i₂))

end

section

instance : (toGradedObjectFunctor C c₁ c₂).Additive where

variable (S S' : ShortComplex (HomologicalComplex₂ C c₁ c₂)) (φ : S ⟶ S')
  (c : ComplexShape ι) [DecidableEq ι] [TotalComplexShape c₁ c₂ c]
  [S.X₁.HasTotal c] [S.X₂.HasTotal c] [S.X₃.HasTotal c]
  [S'.X₁.HasTotal c] [S'.X₂.HasTotal c] [S'.X₃.HasTotal c]

@[simps]
noncomputable def total.shortComplex : ShortComplex (HomologicalComplex C c) where
  f := total.map S.f c
  g := total.map S.g c
  zero := by rw [← total.map_comp, S.zero, total.map_zero]

noncomputable def total.shortComplexSplitting
    (σ : (S.map (toGradedObjectFunctor C c₁ c₂)).Splitting) (i : ι) :
    ((total.shortComplex S c).map (HomologicalComplex.eval _ _ i)).Splitting := by
  have : (ShortComplex.map S (toGradedObjectFunctor C c₁ c₂)).X₁.HasMap (π c₁ c₂ c) := by
    dsimp
    infer_instance
  have : (ShortComplex.map S (toGradedObjectFunctor C c₁ c₂)).X₂.HasMap (π c₁ c₂ c) := by
    dsimp
    infer_instance
  have : (ShortComplex.map S (toGradedObjectFunctor C c₁ c₂)).X₃.HasMap (π c₁ c₂ c) := by
    dsimp
    infer_instance
  exact GradedObject.shortComplexSplittingEquiv _
    (GradedObject.mapShortComplexSplitting _ _ σ) i

variable {S S'}

@[simps]
noncomputable def total.mapShortComplex : total.shortComplex S c ⟶ total.shortComplex S' c where
  τ₁ := total.map φ.τ₁ _
  τ₂ := total.map φ.τ₂ _
  τ₃ := total.map φ.τ₃ _
  comm₁₂ := by
    dsimp
    simp only [← total.map_comp, φ.comm₁₂]
  comm₂₃ := by
    dsimp
    simp only [← total.map_comp, φ.comm₂₃]

end

end HomologicalComplex₂

namespace ComplexShape

open Embedding

lemma embeddingUpIntGE_monotone (a a' : ℤ) (h : a' ≤ a):
    (embeddingUpIntGE a).Subset (embeddingUpIntGE a') where
  subset := by
    obtain ⟨k, rfl⟩ := Int.eq_add_ofNat_of_le h
    rintro _ ⟨l, rfl⟩
    exact ⟨k + l, by dsimp; omega⟩

end ComplexShape

namespace CochainComplex

section

variable (C : Type*) [Category C] [HasZeroMorphisms C] [HasZeroObject C]

noncomputable abbrev stupidFiltrationGEFunctor :
    ℤᵒᵖ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  ComplexShape.Embedding.stupidTruncGEFiltration
    (fun n => ComplexShape.embeddingUpIntGE n.unop)
      (fun _ _ φ => ComplexShape.embeddingUpIntGE_monotone _ _ (leOfHom φ.unop)) C

variable {C}
variable (K L : CochainComplex C ℤ)

noncomputable abbrev stupidFiltrationGE : ℤᵒᵖ ⥤ CochainComplex C ℤ :=
  stupidFiltrationGEFunctor C ⋙ ((evaluation _ _).obj K)

noncomputable def stupidFiltrationGEObjToSingle (n : ℤ) :
    K.stupidFiltrationGE.obj ⟨n⟩ ⟶ (HomologicalComplex.single C (up ℤ) n).obj (K.X n) :=
  HomologicalComplex.mkHomToSingle
    (K.stupidTruncXIso (embeddingUpIntGE n) (add_zero n)).hom (by
      rintro k hk
      apply IsZero.eq_of_src
      apply K.isZero_stupidTrunc_X
      dsimp at hk ⊢
      omega)

@[reassoc]
lemma stupidFiltrationGE_map_to_single (n₀ n₁ : ℤ) (h : n₀ < n₁) :
    K.stupidFiltrationGE.map (homOfLE h.le).op ≫
      K.stupidFiltrationGEObjToSingle n₀ = 0 := by
  apply HomologicalComplex.to_single_hom_ext
  apply IsZero.eq_of_src
  apply K.isZero_stupidTrunc_X
  intros
  dsimp
  omega

@[simps]
noncomputable def shortComplexStupidFiltrationGE (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk _ _ (K.stupidFiltrationGE_map_to_single n₀ n₁ (by omega))

lemma isIso_stupidFiltrationGE_map_f (n₀ n₁ : ℤ) (h : n₀ ≤ n₁) (k : ℤ) (hk : n₁ ≤ k ∨ k < n₀) :
    IsIso ((K.stupidFiltrationGE.map (homOfLE h).op).f k) := by
  apply HomologicalComplex.isIso_mapStupidTruncGE_f
  obtain hk|hk := hk
  · obtain ⟨j, hj⟩ := Int.eq_add_ofNat_of_le hk
    exact Or.inl ⟨j, by dsimp; omega⟩
  · exact Or.inr (fun i₂ => by dsimp; omega)

variable {K L} in
@[simps]
noncomputable def mapShortComplexStupidFiltrationGE (φ : K ⟶ L) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    K.shortComplexStupidFiltrationGE n₀ n₁ h ⟶ L.shortComplexStupidFiltrationGE n₀ n₁ h where
  τ₁ := ((stupidFiltrationGEFunctor C).obj ⟨n₁⟩).map φ
  τ₂ := ((stupidFiltrationGEFunctor C).obj ⟨n₀⟩).map φ
  τ₃ := (HomologicalComplex.single C (up ℤ) n₀).map (φ.f n₀)
  comm₁₂ := by dsimp; simp
  comm₂₃ := by
    apply HomologicalComplex.to_single_hom_ext
    simp [stupidFiltrationGEObjToSingle, HomologicalComplex.single_map_f_self]

end

section

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  (K L : CochainComplex C ℤ) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)

noncomputable def shortComplexStupidFiltrationGESplitting (k : ℤ) :
    ((K.shortComplexStupidFiltrationGE n₀ n₁ h).map
      (HomologicalComplex.eval _ _ k)).Splitting :=
  if hk : k = n₀
  then
    { s := eqToHom (by dsimp; rw [hk]) ≫
          (HomologicalComplex.singleObjXSelf (up ℤ) n₀ (K.X n₀)).hom ≫
          eqToHom (by rw [hk]) ≫ (K.stupidTruncXIso (embeddingUpIntGE n₀)
            (i := 0) (by dsimp; omega)).inv
      s_g := by
        subst hk
        simp [stupidFiltrationGEObjToSingle]
      r := 0
      f_r := by
        apply IsZero.eq_of_src
        apply K.isZero_stupidTrunc_X
        intro
        dsimp
        omega
      id := by
        subst hk
        simp [stupidFiltrationGEObjToSingle] }
  else
    have := K.isIso_stupidFiltrationGE_map_f n₀ n₁ (by omega) k (by omega)
    { r := inv ((K.stupidFiltrationGE.map (homOfLE (show n₀ ≤ n₁ by omega)).op).f k)
      s := 0
      s_g := by
        apply IsZero.eq_of_tgt
        exact HomologicalComplex.isZero_single_obj_X (up ℤ) _ _ _ hk }

end

end CochainComplex

namespace HomologicalComplex₂

section

variable (C : Type*) [Category C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι₁ ι₂ : Type*} [DecidableEq ι₁] (c₁ : ComplexShape ι₁) (c₂ : ComplexShape ι₂)

noncomputable abbrev singleColumn (i₁ : ι₁) :
    HomologicalComplex C c₂ ⥤ HomologicalComplex₂ C c₁ c₂ :=
  HomologicalComplex.single (HomologicalComplex C c₂) c₁ i₁

variable {C c₂}

lemma isZero_singleColumn_X (K : HomologicalComplex C c₂)
    (i₁ i₁' : ι₁) (h : i₁' ≠ i₁) :
    IsZero (((singleColumn C c₁ c₂ i₁).obj K).X i₁') :=
  HomologicalComplex.isZero_single_obj_X _ _ _ _ h

lemma isZero_singleColumn_X_X (K : HomologicalComplex C c₂)
    (i₁ i₁' : ι₁) (h : i₁' ≠ i₁) (i₂ : ι₂) :
    IsZero ((((singleColumn C c₁ c₂ i₁).obj K).X i₁').X i₂) :=
  (HomologicalComplex.eval C c₂ i₂).map_isZero (isZero_singleColumn_X c₁ K i₁ i₁' h)

noncomputable def singleColumnXIso (K : HomologicalComplex C c₂) (i₁ : ι₁) :
    ((singleColumn C c₁ c₂ i₁).obj K).X i₁ ≅ K := by
  apply HomologicalComplex.singleObjXSelf

noncomputable def singleColumnXXIso (K : HomologicalComplex C c₂) (i₁ : ι₁) (i₂ : ι₂) :
    (((singleColumn C c₁ c₂ i₁).obj K).X i₁).X i₂ ≅ K.X i₂ :=
  (HomologicalComplex.eval C c₂ i₂).mapIso (singleColumnXIso c₁ K i₁)

@[reassoc]
lemma singleColumn_obj_X_d (K : HomologicalComplex C c₂) (i₁ : ι₁) (i₂ i₂' : ι₂) :
    (((singleColumn C c₁ c₂ i₁).obj K).X i₁).d i₂ i₂' =
      (singleColumnXXIso c₁ K i₁ i₂).hom ≫ K.d i₂ i₂' ≫
        (singleColumnXXIso c₁ K i₁ i₂').inv := by
  dsimp only [singleColumn, singleColumnXXIso]
  simp only [Functor.mapIso_hom, HomologicalComplex.eval_map,
    Functor.mapIso_inv, HomologicalComplex.Hom.comm_assoc]
  rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f,
    comp_id]

end

section

variable (C : Type*) [Category C] [Preadditive C] [HasZeroObject C]
  {ι₁ ι₂ ι : Type*} [DecidableEq ι₁] [DecidableEq ι] (c₁ : ComplexShape ι₁) (c₂ : ComplexShape ι₂)
  (K : HomologicalComplex C c₂) (i₁ : ι₁) (c : ComplexShape ι)
  [TotalComplexShape c₁ c₂ c]
  [((singleColumn C c₁ c₂ i₁).obj K).HasTotal  c]

@[simp]
lemma singleColumn_d₁ (x : ι₁) (y : ι₂) (n : ι) :
    ((singleColumn C c₁ c₂ i₁).obj K).d₁ c x y n = 0 := by
  by_cases hx : c₁.Rel x (c₁.next x)
  · by_cases hx' : π c₁ c₂ c (next c₁ x, y) = n
    · rw [d₁_eq _ _ hx _ _ hx']
      simp [singleColumn]
    · rw [d₁_eq_zero' _ _ hx _ _ hx']
  · rw [d₁_eq_zero _ _ _ _ _ hx]

lemma singleColumn_d₂ (y y' : ι₂) (hy : c₂.Rel y y') (n : ι)
    (hn : π c₁ c₂ c (i₁, y') = n) :
    ((singleColumn C c₁ c₂ i₁).obj K).d₂ c i₁ y n =
      ε₂ c₁ c₂ c (i₁, y) • (singleColumnXXIso c₁ K i₁ y).hom ≫ K.d y y' ≫
        (singleColumnXXIso c₁ K i₁ y').inv ≫
        ((singleColumn C c₁ c₂ i₁).obj K).ιTotal c i₁ y' n hn := by
  simp [d₂_eq _ _ _ hy _ hn, singleColumn_obj_X_d]

end

end HomologicalComplex₂

namespace HomologicalComplex₂

variable (C : Type*) [Category C] [Abelian C]
  {D : Type*} [Category D] [Preadditive D] [HasFiniteCoproducts D]
  {ι : Type*} (c : ComplexShape ι)

noncomputable abbrev rowFiltrationGEFunctor :
    ℤᵒᵖ ⥤ HomologicalComplex₂ C (up ℤ) c ⥤ HomologicalComplex₂ C (up ℤ) c :=
  CochainComplex.stupidFiltrationGEFunctor _

instance (n : ℤᵒᵖ) {ι' : Type*} {c' : ComplexShape ι'}
    (K : HomologicalComplex₂ C (up ℤ) c) [TotalComplexShape (up ℤ) c c'] [K.HasTotal c']:
    (((rowFiltrationGEFunctor C _).obj n).obj K).HasTotal c' := by
  dsimp [rowFiltrationGEFunctor]
  infer_instance

variable {C c}

noncomputable abbrev rowFiltrationGE (K : HomologicalComplex₂ C (up ℤ) c) :
    ℤᵒᵖ ⥤ HomologicalComplex₂ C (up ℤ) c :=
  rowFiltrationGEFunctor C c ⋙ ((evaluation _ _).obj K)

instance (K : HomologicalComplex₂ C (up ℤ) c) (n : ℤ):
    CochainComplex.IsStrictlyGE ((rowFiltrationGE K).obj ⟨n⟩) n := by
  dsimp
  infer_instance

instance (K : HomologicalComplex₂ C (up ℤ) c) (n x : ℤ) [CochainComplex.IsStrictlyLE K x] :
    CochainComplex.IsStrictlyLE ((rowFiltrationGE K).obj ⟨n⟩) x := by
  dsimp
  infer_instance

noncomputable abbrev rowFiltrationGEMap {K L : HomologicalComplex₂ C (up ℤ) c} (φ : K ⟶ L) :
    K.rowFiltrationGE ⟶ L.rowFiltrationGE :=
  whiskerLeft _ ((evaluation _ _).map φ)

variable (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
variable [K.HasTotal (up ℤ)]

instance (n : ℤᵒᵖ) : (K.rowFiltrationGE.obj n).HasTotal (up ℤ) := by
  dsimp [rowFiltrationGE]
  infer_instance

instance (L : CochainComplex C ℤ) (i₂ : ℤ) :
    ((singleColumn C (up ℤ) (up ℤ) i₂).obj L).HasTotal (up ℤ) :=
  fun n => hasCoproduct_of_isZero_but_one _ ⟨⟨i₂, n - i₂⟩, by simp⟩ (by
    rintro ⟨⟨x, y⟩, hxy⟩ h
    apply isZero_singleColumn_X_X
    simp at hxy h
    omega)

@[simp]
noncomputable def cofanSingleColumnObjTotal (L : CochainComplex C ℤ) (x y n : ℤ) (h : x + y = n):
  GradedObject.CofanMapObjFun (((singleColumn C (up ℤ) (up ℤ) x).obj L).toGradedObject)
    (π (up ℤ) (up ℤ) (up ℤ)) n :=
  cofanOfIsZeroButOne  _ ⟨⟨x, y⟩, h⟩ (by
    rintro ⟨⟨x', y'⟩, hxy⟩ h'
    apply isZero_singleColumn_X_X
    simp at hxy h'
    omega)

noncomputable def isColimitCofanSingleColumnObjTotal
    (L : CochainComplex C ℤ) (x y n : ℤ) (h : x + y = n) :
    IsColimit (cofanSingleColumnObjTotal L x y n h) := by
  apply isColimitCofanOfIsZeroButOne

noncomputable def singleColumnObjTotalXIso
    (L : CochainComplex C ℤ) (x y n : ℤ) (h : x + y = n) :
    (((singleColumn C (up ℤ) (up ℤ) x).obj L).total (up ℤ)).X n ≅ L.X y :=
  ((cofanSingleColumnObjTotal L x y n h).iso
    (isColimitCofanSingleColumnObjTotal L x y n h)).symm ≪≫ (singleColumnXXIso (up ℤ) L x y)

lemma singleColumnObjTotalXIso_inv
    (L : CochainComplex C ℤ) (x y n : ℤ) (h : x + y = n) :
    (singleColumnObjTotalXIso L x y n h).inv =
      (singleColumnXXIso (up ℤ) L x y).inv ≫
        ((singleColumn C (up ℤ) (up ℤ) x).obj L).ιTotal (up ℤ) x y n h := by
  rfl

@[reassoc]
lemma singleColumn_ιTotal
    (L : CochainComplex C ℤ) (x y n : ℤ) (h : x + y = n) :
    ((singleColumn C (up ℤ) (up ℤ) x).obj L).ιTotal (up ℤ) x y n h =
      (singleColumnXXIso (up ℤ) L x y).hom ≫(singleColumnObjTotalXIso L x y n h).inv := by
  rw [singleColumnObjTotalXIso_inv, Iso.hom_inv_id_assoc]

noncomputable def singleColumnObjTotal (L : CochainComplex C ℤ) (x x' : ℤ) (h : x + x' = 0) :
    ((singleColumn C (up ℤ) (up ℤ) x).obj L).total (up ℤ) ≅ L⟦x'⟧ :=
  Iso.symm (HomologicalComplex.Hom.isoOfComponents
    (fun n => (singleColumnObjTotalXIso L _ _ _ (by dsimp; omega)).symm) (by
      intro y y' h
      dsimp at h ⊢
      simp [singleColumnObjTotalXIso_inv]
      rw [singleColumn_d₂ _ _ _ _ _ _ _ (y' + x')
        (by dsimp; omega) _ (by dsimp; omega)]
      obtain rfl : x' = -x := by omega
      simp))

@[reassoc (attr := simp)]
noncomputable def singleColumnObjTotal_inv_naturality {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    (x x' : ℤ) (h : x + x' = 0) :
    (singleColumnObjTotal K x x' h).inv ≫
      total.map ((HomologicalComplex.single _ (up ℤ) x).map φ) (up ℤ) =
      φ⟦x'⟧' ≫ (singleColumnObjTotal L x x' h).inv := by
  ext n
  dsimp [singleColumnObjTotal]
  rw [singleColumnObjTotalXIso_inv, singleColumnObjTotalXIso_inv, assoc, ιTotal_map,
    HomologicalComplex.single_map_f_self]
  simp [singleColumnXXIso, singleColumnXIso, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq]

@[reassoc (attr := simp)]
noncomputable def singleColumnObjTotal_hom_naturality {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    (x x' : ℤ) (h : x + x' = 0) :
    total.map ((HomologicalComplex.single _ (up ℤ) x).map φ) (up ℤ) ≫
      (singleColumnObjTotal L x x' h).hom =
      (singleColumnObjTotal K x x' h).hom ≫ φ⟦x'⟧' := by
  rw [← cancel_epi (singleColumnObjTotal K x x' h).inv,
    singleColumnObjTotal_inv_naturality_assoc, Iso.inv_hom_id, comp_id, Iso.inv_hom_id_assoc]

lemma hasTotal_of_isStrictlyLE (K : HomologicalComplex₂ D (up ℤ) (up ℤ)) (x₀ y₀ : ℤ)
    [CochainComplex.IsStrictlyLE K x₀] [∀ x, CochainComplex.IsStrictlyLE (K.X x) y₀] :
    K.HasTotal (up ℤ) := fun n => by
  obtain ⟨M, hM⟩ : ∃ (M : ℕ), y₀ < n - x₀ + M := by
    by_cases h : y₀ < n - x₀
    · exact ⟨0, by omega⟩
    · simp only [not_lt] at h
      obtain ⟨k, rfl⟩ := Int.eq_add_ofNat_of_le h
      exact ⟨k + 1, by omega⟩
  apply hasCoproduct_of_isZero (J := Fin M) (ι := fun ⟨k, _⟩ => ⟨⟨x₀ - k, n - x₀ + k⟩, by simp⟩)
  · rintro ⟨k, hk⟩ ⟨k', hk'⟩
    simp
  · rintro ⟨⟨x, y⟩, hxy : x + y = n⟩ h
    by_cases hx : x ≤ x₀
    · apply CochainComplex.isZero_of_isStrictlyLE (K.X x) y₀
      by_contra!
      obtain ⟨k, hk⟩ := Int.eq_add_ofNat_of_le hx
      exact h ⟨⟨k, by omega⟩, by simp only [Subtype.mk.injEq, Prod.mk.injEq]; omega⟩
    · exact (HomologicalComplex.eval _ _ y).map_isZero
        (CochainComplex.isZero_of_isStrictlyLE K x₀ x (by simpa using hx))

lemma hasTotal_of_isStrictlyGE_of_isStrictlyLE (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
    (x₀ x₁ : ℤ)
    [CochainComplex.IsStrictlyGE K x₀] [CochainComplex.IsStrictlyLE K x₁] :
    K.HasTotal (up ℤ) := fun n => by
  obtain ⟨M, hM⟩ : ∃ (M : ℕ), x₀ + M > x₁ := by
    by_cases h : x₁ < x₀
    · exact ⟨0, by omega⟩
    · simp only [not_lt] at h
      obtain ⟨k, rfl⟩ := Int.eq_add_ofNat_of_le h
      exact ⟨k + 1, by omega⟩
  apply hasCoproduct_of_isZero (J := Fin M) (ι := fun ⟨k, _⟩ => ⟨⟨x₀ + k, n - x₀ - k⟩, by simp⟩)
  · rintro ⟨k, hk⟩ ⟨k', hk'⟩
    simp
  · rintro ⟨⟨x, y⟩, hxy : x + y = n⟩ h
    by_cases hx : x₀ ≤ x
    · obtain ⟨k, hk⟩ := Int.eq_add_ofNat_of_le hx
      refine (HomologicalComplex.eval _ _ y).map_isZero
        (CochainComplex.isZero_of_isStrictlyLE K x₁ x ?_)
      by_contra!
      exact h ⟨⟨k, by omega⟩, by simp only [Subtype.mk.injEq, Prod.mk.injEq]; omega⟩
    · exact (HomologicalComplex.eval _ _ y).map_isZero
        (CochainComplex.isZero_of_isStrictlyGE K x₀ x (by simpa using hx))

lemma total.quasiIso_map_of_finitely_many_columns {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (φ : K ⟶ L) [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)] (x₀ x₁ : ℤ)
    [CochainComplex.IsStrictlyGE K x₀] [CochainComplex.IsStrictlyLE K x₁]
    [CochainComplex.IsStrictlyGE L x₀] [CochainComplex.IsStrictlyLE L x₁]
    (hφ : ∀ (i : ℤ), x₀ ≤ i → i ≤ x₁ → QuasiIso (φ.f i)) :
    QuasiIso (total.map φ (up ℤ)) := by
  suffices hφ' : ∀ (k : ℕ) (x : ℤ) (_ : x₁ + 1 - k = x),
      QuasiIso (total.map ((rowFiltrationGEMap φ).app ⟨x⟩) (up ℤ)) by
    obtain ⟨k, x, hx, hx'⟩ : ∃ (k : ℕ) (x : ℤ) (_ : x₁ + 1 - k = x), x ≤ x₀ := by
      by_cases h : x₀ ≤ x₁
      · obtain ⟨k, hk⟩ := Int.eq_add_ofNat_of_le h
        exact ⟨k + 1, _, rfl, by omega⟩
      · exact ⟨0, _, rfl, by omega⟩
    have := CochainComplex.isStrictlyGE_of_GE K _ _ hx'
    have := CochainComplex.isStrictlyGE_of_GE L _ _ hx'
    refine (quasiIso_iff_of_arrow_mk_iso _ _ ?_).1 (hφ' k x hx)
    refine' Arrow.isoMk
      (total.mapIso (asIso (HomologicalComplex.ιStupidTrunc K (embeddingUpIntGE x))) _)
      (total.mapIso (asIso (HomologicalComplex.ιStupidTrunc L (embeddingUpIntGE x))) _) ?_
    dsimp
    simp only [← map_comp, HomologicalComplex.ιStupidTrunc_naturality]
  intro k
  induction k with
  | zero =>
      intro x hx
      obtain rfl : x₁ + 1 = x := by simpa using hx
      dsimp
      rw [quasiIso_iff_acyclic]
      all_goals
        apply HomologicalComplex.acyclic_of_isZero
        apply total.isZero
        apply (Embedding.embeddingUpInt_areComplementary x₁ (x₁ + 1) rfl).symm.isZero_stupidTrunc
  | succ k hk =>
      intro x hx
      replace hx : x₁ = x + k := by omega
      replace hk := hk (x + 1) (by omega)
      let S₁ := CochainComplex.shortComplexStupidFiltrationGE K x _ rfl
      let S₂ := CochainComplex.shortComplexStupidFiltrationGE L x _ rfl
      have : HasTotal S₁.X₁ (up ℤ) := by dsimp [S₁]; infer_instance
      have : HasTotal S₁.X₂ (up ℤ) := by dsimp [S₁]; infer_instance
      have : HasTotal S₁.X₃ (up ℤ) := by dsimp [S₁]; infer_instance
      have : HasTotal S₂.X₁ (up ℤ) := by dsimp [S₂]; infer_instance
      have : HasTotal S₂.X₂ (up ℤ) := by dsimp [S₂]; infer_instance
      have : HasTotal S₂.X₃ (up ℤ) := by dsimp [S₂]; infer_instance
      let ψ : S₁ ⟶ S₂ := CochainComplex.mapShortComplexStupidFiltrationGE φ x _ rfl
      apply HomologicalComplex.HomologySequence.quasiIso_τ₂ (total.mapShortComplex ψ (up ℤ))
      · apply HomologicalComplex.shortExact_of_degreewise_shortExact
        intro i
        apply ShortComplex.Splitting.shortExact
        apply total.shortComplexSplitting
        refine (GradedObject.shortComplexSplittingEquiv _).symm ?_
        rintro ⟨a, b⟩
        exact (CochainComplex.shortComplexStupidFiltrationGESplitting K x _ rfl a).map
          (HomologicalComplex.eval _ _ b)
      · apply HomologicalComplex.shortExact_of_degreewise_shortExact
        intro i
        apply ShortComplex.Splitting.shortExact
        apply total.shortComplexSplitting
        refine (GradedObject.shortComplexSplittingEquiv _).symm ?_
        rintro ⟨a, b⟩
        exact (CochainComplex.shortComplexStupidFiltrationGESplitting L x _ rfl a).map
          (HomologicalComplex.eval _ _ b)
      · exact hk
      · have : QuasiIso (φ.f x) := by
          by_cases hx : x₀ ≤ x
          · exact hφ x hx (by omega)
          · simp only [not_le] at hx
            rw [quasiIso_iff_acyclic]
            all_goals
              apply HomologicalComplex.acyclic_of_isZero
              exact CochainComplex.isZero_of_isStrictlyGE _ x₀ _ hx
        dsimp [ψ]
        refine (quasiIso_iff_of_arrow_mk_iso _ _ ?_).2 (inferInstance : QuasiIso ((φ.f x)⟦-x⟧'))
        exact Arrow.isoMk (singleColumnObjTotal _ _ _ (by simp))
          (singleColumnObjTotal _ _ _ (by simp))

lemma total.isIso_ιStupidTrunc_map_f
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] (y₀ x n : ℤ) (hn : x + y₀ ≤ n)
    [∀ x, CochainComplex.IsStrictlyLE (K.X x) y₀] :
    IsIso ((total.map (HomologicalComplex.ιStupidTrunc K (embeddingUpIntGE x)) (up ℤ)).f n) := by
  apply GradedObject.isIso_mapMap_apply
  rintro ⟨p, q⟩ (hpq : p + q = n)
  dsimp
  by_cases hp : x ≤ p
  · obtain ⟨j, hj⟩ : ∃ j, (embeddingUpIntGE x).f j = p := by
      obtain ⟨k, rfl⟩ := Int.eq_add_ofNat_of_le hp
      exact ⟨k, rfl⟩
    have := HomologicalComplex.isIso_ιStupidTrunc_f K (embeddingUpIntGE x) hj
    change IsIso ((HomologicalComplex.eval _ _ q).map _)
    infer_instance
  · simp only [not_le] at hp
    refine' ⟨0, _, _⟩
    · apply IsZero.eq_of_src
      apply (HomologicalComplex.eval _ _ q).map_isZero
      apply HomologicalComplex.isZero_stupidTrunc_X
      intro i hi
      dsimp at hi
      omega
    · apply IsZero.eq_of_src
      dsimp
      apply CochainComplex.isZero_of_isStrictlyLE _ y₀
      omega

lemma total.quasiIsoAt_ιStupidTrunc_map
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)] (y₀ x n : ℤ) (hn : x + y₀ < n)
    [∀ x, CochainComplex.IsStrictlyLE (K.X x) y₀] :
    QuasiIsoAt (total.map (HomologicalComplex.ιStupidTrunc K (embeddingUpIntGE x)) (up ℤ)) n := by
  rw [quasiIsoAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp)]
  have : IsIso ((HomologicalComplex.shortComplexFunctor' C (up ℤ) (n - 1) n (n + 1)).map
      (map (HomologicalComplex.ιStupidTrunc K (embeddingUpIntGE x)) (up ℤ))) := by
    rw [ShortComplex.isIso_iff]
    refine' ⟨_, _, _⟩
    all_goals exact total.isIso_ιStupidTrunc_map_f K y₀ x _ (by omega)
  apply ShortComplex.quasiIso_of_isIso

lemma total.quasiIso_map_of_isStrictlyGE_of_isStrictlyLE
    {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (φ : K ⟶ L) [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)] (x₀ y₀ : ℤ)
    [CochainComplex.IsStrictlyLE K x₀] [CochainComplex.IsStrictlyLE L x₀]
    [∀ x, CochainComplex.IsStrictlyLE (K.X x) y₀]
    [∀ x, CochainComplex.IsStrictlyLE (L.X x) y₀]
    (hφ : ∀ (i : ℤ), QuasiIso (φ.f i)) :
    QuasiIso (total.map φ (up ℤ)) := by
  have hφ' : ∀ x, QuasiIso (total.map ((rowFiltrationGEMap φ).app ⟨x⟩) (up ℤ)) := fun x =>
    total.quasiIso_map_of_finitely_many_columns ((rowFiltrationGEMap φ).app ⟨x⟩) x x₀ (by
      intro i hi₁ hi₂
      obtain ⟨j, hj⟩ : ∃ j, (embeddingUpIntGE x).f j = i := by
        obtain ⟨k, rfl⟩ := Int.eq_add_ofNat_of_le hi₁
        exact ⟨k, rfl⟩
      have := fun (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) =>
        HomologicalComplex.isIso_ιStupidTrunc_f K (embeddingUpIntGE x) hj
      apply (quasiIso_iff_of_arrow_mk_iso _ _ _).2 (hφ i)
      exact Arrow.isoMk (asIso ((HomologicalComplex.ιStupidTrunc K (embeddingUpIntGE x)).f i))
        (asIso ((HomologicalComplex.ιStupidTrunc L (embeddingUpIntGE x)).f i)))
  rw [quasiIso_iff]
  intro n
  let x := n - y₀ - 1
  have := total.quasiIsoAt_ιStupidTrunc_map K y₀ x n (by omega)
  have := total.quasiIsoAt_ιStupidTrunc_map L y₀ x n (by omega)
  rw [← quasiIsoAt_iff_comp_left
    (total.map (HomologicalComplex.ιStupidTrunc K (embeddingUpIntGE x)) (up ℤ)),
    ← map_comp, ← HomologicalComplex.ιStupidTrunc_naturality, map_comp,
    quasiIsoAt_iff_comp_right]
  dsimp at hφ'
  infer_instance

end HomologicalComplex₂
