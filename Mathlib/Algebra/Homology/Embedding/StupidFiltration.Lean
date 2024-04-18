import Mathlib.Algebra.Homology.Embedding.HomEquiv
import Mathlib.Algebra.Homology.Embedding.StupidTrunc

open CategoryTheory Category Limits

namespace ComplexShape

namespace Embedding

variable {ι₁ : Type*} {c₁ : ComplexShape ι₁} {ι : Type*} {c : ComplexShape ι}
  (e₁ : Embedding c₁ c)
  {ι₂ : Type*} {c₂ : ComplexShape ι₂} (e₂ : Embedding c₂ c)
  {ι₃ : Type*} {c₃ : ComplexShape ι₃} (e₃ : Embedding c₃ c)

structure Subset : Prop where
  subset : Set.range e₁.f ⊆ Set.range e₂.f

namespace Subset

lemma refl : e₁.Subset e₁ where
  subset := by rfl

variable {e₁ e₂ e₃}

lemma trans (h₁₂ : e₁.Subset e₂) (h₂₃ : e₂.Subset e₃) : e₁.Subset e₃ where
  subset := h₁₂.subset.trans h₂₃.subset

section

variable  (h : e₁.Subset e₂)

lemma exists_index (i₁ : ι₁) : ∃ (i₂ : ι₂), e₂.f i₂ = e₁.f i₁ := h.subset ⟨i₁, rfl⟩

noncomputable def index (i₁ : ι₁) : ι₂ := (h.exists_index i₁).choose

lemma f_index (i₁ : ι₁) : e₂.f (h.index i₁) = e₁.f i₁ := (h.exists_index i₁).choose_spec

end

end Subset

end Embedding

end ComplexShape

namespace HomologicalComplex

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {ι ι₁ ι₂ ι₃ : Type*} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}
  {c₃ : ComplexShape ι₃} {c : ComplexShape ι}
  (K L : HomologicalComplex C c) (φ : K ⟶ L)
  {e₁ : c₁.Embedding c} {e₂ : c₂.Embedding c} {e₃ : c₃.Embedding c} (h : e₁.Subset e₂)

@[pp_dot]
noncomputable def restrictionStupidTruncIso [e₁.IsRelIff] [e₂.IsRelIff] :
    (K.stupidTrunc e₂).restriction e₁ ≅ K.restriction e₁ :=
  Hom.isoOfComponents (fun i₁ => K.stupidTruncXIso e₂ (h.f_index i₁)) (fun i₁ j₁ _ => by
    dsimp [stupidTrunc, stupidTruncXIso]
    rw [(K.restriction e₂).extend_d_eq e₂ (h.f_index i₁) (h.f_index j₁),
      K.restriction_d_eq e₂ (h.f_index i₁) (h.f_index j₁)]
    simp [restrictionXIso])

variable {K L} in
@[reassoc (attr := simp)]
lemma restrictionStupidTruncIso_hom_naturality [e₁.IsRelIff] [e₂.IsRelIff] :
    restrictionMap (stupidTruncMap φ e₂) e₁ ≫ (L.restrictionStupidTruncIso h).hom =
      (K.restrictionStupidTruncIso h).hom ≫ restrictionMap φ e₁ := by
  ext i₁
  dsimp [stupidTruncMap, restrictionStupidTruncIso, stupidTruncXIso]
  rw [extendMap_f _ e₂ (h.f_index i₁), restrictionMap_f' _ e₂ (h.f_index i₁)]
  simp [restrictionXIso]

variable {K L} in
@[reassoc (attr := simp)]
lemma restrictionStupidTruncIso_inv_naturality [e₁.IsRelIff] [e₂.IsRelIff] :
    (K.restrictionStupidTruncIso h).inv ≫ restrictionMap (stupidTruncMap φ e₂) e₁ =
       restrictionMap φ e₁ ≫ (L.restrictionStupidTruncIso h).inv := by
  ext i₁
  dsimp [stupidTruncMap, restrictionStupidTruncIso, stupidTruncXIso]
  rw [extendMap_f _ e₂ (h.f_index i₁), restrictionMap_f' _ e₂ (h.f_index i₁)]
  simp [restrictionXIso]

noncomputable def mapStupidTruncLE [e₁.IsTruncLE] [e₂.IsRelIff] :
    K.stupidTrunc e₂ ⟶ K.stupidTrunc e₁ :=
  e₁.liftExtend ((K.restrictionStupidTruncIso h).hom)
    (fun _ hi₁ _ _ => hi₁.false.elim)

noncomputable def mapStupidTruncGE [e₁.IsTruncGE] [e₂.IsRelIff] :
    K.stupidTrunc e₁ ⟶ K.stupidTrunc e₂ :=
  e₁.descExtend ((K.restrictionStupidTruncIso h).inv)
    (fun _ hi₁ _ _ => hi₁.false.elim)

open ComplexShape.Embedding

variable {K L} in
@[reassoc (attr := simp)]
lemma mapStupidTruncLE_naturality [e₁.IsTruncLE] [e₂.IsRelIff] :
    stupidTruncMap φ e₂ ≫ L.mapStupidTruncLE h =
      K.mapStupidTruncLE h ≫ stupidTruncMap φ e₁ := by
  apply (e₁.homEquiv _ _).injective
  ext1
  dsimp [homEquiv, mapStupidTruncLE, stupidTruncMap]
  rw [homRestrict_precomp, homRestrict_comp_extend, homRestrict_liftExtend,
    homRestrict_liftExtend]
  apply restrictionStupidTruncIso_hom_naturality

@[reassoc (attr := simp)]
lemma mapStupidTruncLE_fac [e₁.IsTruncLE] [e₂.IsTruncLE] :
    K.πStupidTrunc e₂ ≫ K.mapStupidTruncLE h = K.πStupidTrunc e₁ := by
  apply (e₁.homEquiv _ _).injective
  ext i₁ : 2
  dsimp [mapStupidTruncLE]
  rw [homRestrict_precomp, homRestrict_liftExtend, homRestrict_f e₁ _ rfl]
  dsimp [πStupidTrunc]
  rw [πStupidTruncf_eq, πStupidTruncf_eq' _ _ (h.f_index i₁)]
  simp [restrictionStupidTruncIso, stupidTruncXIso, extendXIso, extend.XIso, restrictionXIso]

instance [e₁.IsTruncLE] [e₂.IsTruncLE] : Epi (K.mapStupidTruncLE h) :=
  epi_of_epi_fac (K.mapStupidTruncLE_fac h)

variable (e₁) in
@[simp]
noncomputable def mapStupidTruncLE_refl [e₁.IsTruncLE] :
    K.mapStupidTruncLE (Subset.refl e₁) = 𝟙 _ := by
  rw [← cancel_epi (K.πStupidTrunc e₁), mapStupidTruncLE_fac, comp_id]

@[reassoc (attr := simp)]
noncomputable def mapStupidTruncLE_trans [e₁.IsTruncLE] [e₂.IsTruncLE] [e₃.IsTruncLE]
    (h' : e₂.Subset e₃) :
    K.mapStupidTruncLE h' ≫ K.mapStupidTruncLE h = K.mapStupidTruncLE (h.trans h') := by
  rw [← cancel_epi (K.πStupidTrunc e₃), mapStupidTruncLE_fac_assoc,
    mapStupidTruncLE_fac, mapStupidTruncLE_fac]

variable {K L} in
@[reassoc (attr := simp)]
lemma mapStupidTruncGE_naturality [e₁.IsTruncGE] [e₂.IsRelIff] :
    K.mapStupidTruncGE h ≫ stupidTruncMap φ e₂ =
      stupidTruncMap φ e₁ ≫ L.mapStupidTruncGE h := by
  apply (e₁.homEquiv' _ _).injective
  ext1
  dsimp [homEquiv, mapStupidTruncGE, stupidTruncMap]
  rw [homRestrict'_postcomp, extend_comp_homRestrict', homRestrict'_descExtend,
    homRestrict'_descExtend]
  apply restrictionStupidTruncIso_inv_naturality

@[reassoc (attr := simp)]
lemma mapStupidTruncGE_fac [e₁.IsTruncGE] [e₂.IsTruncGE] :
    K.mapStupidTruncGE h ≫ K.ιStupidTrunc e₂  = K.ιStupidTrunc e₁ := by
  apply (e₁.homEquiv' _ _).injective
  ext i₁ : 2
  dsimp [mapStupidTruncGE]
  rw [homRestrict'_postcomp, homRestrict'_descExtend, homRestrict'_f e₁ _ rfl]
  dsimp [ιStupidTrunc]
  rw [ιStupidTruncf_eq, ιStupidTruncf'_eq _ _ (h.f_index i₁)]
  simp [restrictionStupidTruncIso, stupidTruncXIso, extendXIso, extend.XIso, restrictionXIso]

instance [e₁.IsTruncGE] [e₂.IsTruncGE] : Mono (K.mapStupidTruncGE h) :=
  mono_of_mono_fac (K.mapStupidTruncGE_fac h)

variable (e₁) in
@[simp]
noncomputable def mapStupidTruncGE_refl [e₁.IsTruncGE] :
    K.mapStupidTruncGE (Subset.refl e₁) = 𝟙 _ := by
  rw [← cancel_mono (K.ιStupidTrunc e₁), mapStupidTruncGE_fac, id_comp]

@[reassoc (attr := simp)]
noncomputable def mapStupidTruncGE_trans [e₁.IsTruncGE] [e₂.IsTruncGE] [e₃.IsTruncGE]
    (h' : e₂.Subset e₃) :
    K.mapStupidTruncGE h ≫ K.mapStupidTruncGE h' = K.mapStupidTruncGE (h.trans h') := by
  rw [← cancel_mono (K.ιStupidTrunc e₃), assoc, mapStupidTruncGE_fac,
    mapStupidTruncGE_fac, mapStupidTruncGE_fac]

end HomologicalComplex

namespace ComplexShape

namespace Embedding

namespace Subset

variable {ι ι₁ ι₂ ι₃ : Type*} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}
  {c₃ : ComplexShape ι₃} {c : ComplexShape ι}
  {e₁ : c₁.Embedding c} {e₂ : c₂.Embedding c} (h : e₁.Subset e₂)
variable (C : Type*) [Category C] [HasZeroMorphisms C] [HasZeroObject C]

@[simps!]
noncomputable def restrictionStupidTruncNatIso [e₁.IsRelIff] [e₂.IsRelIff] :
    e₂.stupidTruncFunctor C ⋙ e₁.restrictionFunctor C ≅ e₁.restrictionFunctor C :=
  NatIso.ofComponents (fun K => K.restrictionStupidTruncIso h)

section

variable [e₁.IsTruncLE] [e₂.IsRelIff] (h : e₁.Subset e₂)
variable (C : Type*) [Category C] [HasZeroMorphisms C] [HasZeroObject C]

@[simps]
noncomputable def mapStupidTruncLE :
    e₂.stupidTruncFunctor C ⟶ e₁.stupidTruncFunctor C where
  app K := K.mapStupidTruncLE h

end

section

variable [e₁.IsTruncGE] [e₂.IsRelIff] (h : e₁.Subset e₂)
variable (C : Type*) [Category C] [HasZeroMorphisms C] [HasZeroObject C]

@[simps]
noncomputable def mapStupidTruncGE :
    e₁.stupidTruncFunctor C ⟶ e₂.stupidTruncFunctor C where
  app K := K.mapStupidTruncGE h

end


end Subset

section

variable {ι' : Type*} {c' : ComplexShape ι'} {α : Type*} [Preorder α] {ι : α → Type*}
  {c : Π (a : α), ComplexShape (ι a)} (e : Π (a : α), Embedding (c a) c')
  (he : ∀ ⦃a a' : α⦄, a' ≤ a → (e a).Subset (e a'))
  [∀ a, (e a).IsTruncLE]
  (C : Type*) [Category C] [HasZeroMorphisms C] [HasZeroObject C]

@[simps]
noncomputable def stupidTruncLEFiltration :
    α ⥤ (HomologicalComplex C c' ⥤ HomologicalComplex C c') where
  obj a := (e a).stupidTruncFunctor C
  map {a a'} φ := (he (leOfHom φ)).mapStupidTruncLE C

instance {a a' : α} (φ : a ⟶ a') (K : HomologicalComplex C c') :
    Epi (((stupidTruncLEFiltration e he C).map φ).app K) := by
  dsimp
  infer_instance

end

section

variable {ι' : Type*} {c' : ComplexShape ι'} {α : Type*} [Preorder α] {ι : α → Type*}
  {c : Π (a : α), ComplexShape (ι a)} (e : Π (a : α), Embedding (c a) c')
  (he : ∀ ⦃a a' : α⦄, a ≤ a' → (e a).Subset (e a'))
  [∀ a, (e a).IsTruncGE]
  (C : Type*) [Category C] [HasZeroMorphisms C] [HasZeroObject C]

@[simps]
noncomputable def stupidTruncGEFiltration :
    α ⥤ (HomologicalComplex C c' ⥤ HomologicalComplex C c') where
  obj a := (e a).stupidTruncFunctor C
  map {a a'} φ := (he (leOfHom φ)).mapStupidTruncGE C

instance {a a' : α} (φ : a ⟶ a') (K : HomologicalComplex C c') :
    Mono (((stupidTruncGEFiltration e he C).map φ).app K) := by
  dsimp
  infer_instance

end


end Embedding

end ComplexShape
