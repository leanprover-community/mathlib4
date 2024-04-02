import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

universe v u w₁ w₂

/-namespace CategoryTheory

open Category Limits

namespace ShortComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {K L : ShortComplex C} (φ : K ⟶ L) (ψ : L ⟶ K) (h₁ : φ.τ₂ ≫ ψ.τ₂ = 𝟙 _)
  (h₂ : ψ.τ₂ ≫ φ.τ₂ = 𝟙 _)

@[reassoc]
lemma cyclesMap_comp_eq_id_of_retraction₂ [K.HasLeftHomology] [L.HasLeftHomology] :
    cyclesMap φ ≫ cyclesMap ψ = 𝟙 _ := by
  rw [← cancel_mono K.iCycles, assoc, cyclesMap_i, cyclesMap_i_assoc, id_comp, h₁, comp_id]

@[simps]
noncomputable def isoCyclesOfIso₂ [K.HasLeftHomology] [L.HasLeftHomology] :
    K.cycles ≅ L.cycles where
  hom := cyclesMap φ
  inv := cyclesMap ψ
  hom_inv_id := cyclesMap_comp_eq_id_of_retraction₂ φ ψ h₁
  inv_hom_id := cyclesMap_comp_eq_id_of_retraction₂ ψ φ h₂

@[reassoc]
lemma isoCyclesOfIso₂_hom_comp_iCycles [K.HasLeftHomology] [L.HasLeftHomology] :
    (isoCyclesOfIso₂ φ ψ h₁ h₂).hom ≫ L.iCycles = K.iCycles ≫ φ.τ₂ := by
  simp only [isoCyclesOfIso₂_hom, cyclesMap_i]

lemma isIso_cycles_map_of_iso₂ [K.HasLeftHomology] [L.HasLeftHomology] : IsIso (cyclesMap φ) :=
  IsIso.of_iso (isoCyclesOfIso₂ φ ψ h₁ h₂)

@[reassoc]
lemma opcyclesMap_comp_eq_id_of_retraction₂ [K.HasRightHomology] [L.HasRightHomology] :
    opcyclesMap φ ≫ opcyclesMap ψ = 𝟙 _ := by
  rw [← cancel_epi K.pOpcycles, p_opcyclesMap_assoc, p_opcyclesMap, comp_id, reassoc_of% h₁]

@[simps]
noncomputable def isoOpcyclesOfIso₂ [K.HasRightHomology] [L.HasRightHomology] :
    K.opcycles ≅ L.opcycles where
  hom := opcyclesMap φ
  inv := opcyclesMap ψ
  hom_inv_id := opcyclesMap_comp_eq_id_of_retraction₂ φ ψ h₁
  inv_hom_id := opcyclesMap_comp_eq_id_of_retraction₂ ψ φ h₂

@[reassoc]
lemma pOpcycles_comp_isoOpcyclesOfIso₂_hom [K.HasRightHomology] [L.HasRightHomology] :
    K.pOpcycles ≫ (isoOpcyclesOfIso₂ φ ψ h₁ h₂).hom = φ.τ₂ ≫ L.pOpcycles:= by
  simp only [isoOpcyclesOfIso₂_hom, p_opcyclesMap]

lemma isIso_opcycles_map_of_iso₂ [K.HasRightHomology] [L.HasRightHomology] :
    IsIso (opcyclesMap φ) :=
  IsIso.of_iso (isoOpcyclesOfIso₂ φ ψ h₁ h₂)

@[reassoc]
lemma homologyMap_comp_eq_id_of_retraction₂ [K.HasHomology] [L.HasHomology] :
    homologyMap φ ≫ homologyMap ψ = 𝟙 _ := by
  rw [← cancel_epi K.homologyπ, homologyπ_naturality_assoc, homologyπ_naturality, comp_id,
      cyclesMap_comp_eq_id_of_retraction₂_assoc φ ψ h₁]

@[simps]
noncomputable def isoHomologyOfIso₂ [K.HasHomology] [L.HasHomology] :
    K.homology ≅ L.homology where
  hom := homologyMap φ
  inv := homologyMap ψ
  hom_inv_id := homologyMap_comp_eq_id_of_retraction₂ φ ψ h₁
  inv_hom_id := homologyMap_comp_eq_id_of_retraction₂ ψ φ h₂

lemma isIso_homologyMap_of_iso₂ [K.HasHomology] [L.HasHomology] : IsIso (homologyMap φ) :=
  IsIso.of_iso (isoHomologyOfIso₂ φ ψ h₁ h₂)

lemma quasiIso_of_iso₂ [K.HasHomology] [L.HasHomology] : QuasiIso φ := by
  rw [quasiIso_iff]
  exact isIso_homologyMap_of_iso₂ φ ψ h₁ h₂

@[reassoc]
lemma homologyπ_comp_isoHomologyOfIso₂_hom [K.HasHomology] [L.HasHomology] :
    K.homologyπ ≫ (isoHomologyOfIso₂ φ ψ h₁ h₂).hom =
      (isoCyclesOfIso₂ φ ψ h₁ h₂).hom ≫ L.homologyπ := by
  simp [isoCyclesOfIso₂]

end ShortComplex

end CategoryTheory

open CategoryTheory Category Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι₁ : Type w₁} {ι₂ : Type w₂} (c₁ : ComplexShape ι₁) (c₂ : ComplexShape ι₂)

open ZeroObject

namespace ComplexShape

lemma next_eq_self (x : ι₁) (hx : ¬c₁.Rel x (c₁.next x)) : c₁.next x = x := by
  dsimp [next]
  split_ifs with h
  · obtain ⟨y, hy⟩ := h
    exfalso
    obtain rfl := c₁.next_eq' hy
    exact hx hy
  · rfl

structure Embedding where
  φ : ι₁ → ι₂
  hφ : Function.Injective φ
  iff : ∀ (i j : ι₁), c₁.Rel i j ↔ c₂.Rel (φ i) (φ j)

def embeddingNatUp : Embedding (up ℕ) (up ℤ) where
  φ n := n
  hφ n n' h := by simpa using h
  iff i j := (@Nat.cast_inj ℤ _ _ _ _).symm.trans (by simp)

def embeddingNatDown : Embedding (down ℕ) (down ℤ) where
  φ n := n
  hφ n n' h := by simpa using h
  iff i j := (@Nat.cast_inj ℤ _ _ _ _).symm.trans (by simp)

namespace Embedding

variable {c₁ c₂} (e : Embedding c₁ c₂)

@[pp_dot]
noncomputable def r (x₂ : ι₂) : Option ι₁ := by
  classical
  exact if h : x₂ ∈ Set.image e.φ Set.univ
    then some h.choose
    else none

lemma r_neq_none_iff (x₂ : ι₂) :
    e.r x₂ ≠ none ↔ x₂ ∈ Set.image e.φ Set.univ := by
  dsimp [r]
  split_ifs <;> tauto

lemma r_eq_some_iff (x₁ : ι₁) (x₂ : ι₂) :
    e.r x₂ = some x₁ ↔ e.φ x₁ = x₂ := by
  dsimp [r]
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · rintro rfl
      exact h.choose_spec.2
    · rintro rfl
      exact e.hφ h.choose_spec.2
  · simp only [false_iff]
    intro h'
    exact h ⟨x₁, by tauto, h'⟩

@[simp]
lemma r_φ (x₁ : ι₁) :
    e.r (e.φ x₁) = some x₁ := by
  rw [r_eq_some_iff]

lemma r_cases (x₂ : ι₂) :
    e.r x₂ = none ∨ ∃ (x₁ : ι₁), e.r x₂ = some x₁ := by
  by_cases h : x₂ ∈ Set.image e.φ Set.univ
  · refine' Or.inr _
    obtain ⟨x₁, _, hx₁⟩ := h
    exact ⟨x₁, by simpa only [e.r_eq_some_iff x₁ x₂] using hx₁⟩
  · simp only [← r_neq_none_iff, ne_eq, not_not] at h
    exact Or.inl h

end Embedding

end ComplexShape

namespace HomologicalComplex

variable {c₁ c₂} (K L : HomologicalComplex C c₁) (ψ : K ⟶ L) (e : c₁.Embedding c₂)

noncomputable def extendX : Option ι₁ → C
  | none => 0
  | some x₁ => K.X x₁

lemma isZero_extendX (x : Option ι₁) (hx : x = none) :
    IsZero (K.extendX x) := by
  subst hx
  exact Limits.isZero_zero C

noncomputable def extendXIso (x : Option ι₁) (y : ι₁) (hx : x = some y) :
    K.extendX x ≅ K.X y :=
  eqToIso (by subst hx; rfl)

noncomputable def extendd : ∀ (x y : Option ι₁), K.extendX x ⟶ K.extendX y
  | none, _ => 0
  | some _, none => 0
  | some x₁, some x₂ => K.d x₁ x₂

lemma extendd_eq_zero (x y : Option ι₁) (hx : x = none) : K.extendd x y = 0 := by
  subst hx
  rfl

@[simp]
lemma extendd_eq_zero' (x y : Option ι₁) (hy : y = none) : K.extendd x y = 0 := by
  subst hy
  cases x <;> rfl

@[simp]
lemma extendd_eq (x₁ x₂ : Option ι₁) (y₁ y₂ : ι₁) (hy₁ : x₁ = some y₁) (hy₂ : x₂ = some y₂) :
    K.extendd x₁ x₂ = (K.extendXIso _ _ hy₁).hom ≫ K.d y₁ y₂ ≫ (K.extendXIso _ _ hy₂).inv := by
  subst hy₁ hy₂
  dsimp [extendXIso, extendd]
  erw [id_comp, comp_id]

noncomputable def extend : HomologicalComplex C c₂ where
  X x₂ := K.extendX (e.r x₂)
  d x₂ y₂ := K.extendd (e.r x₂) (e.r y₂)
  shape x₂ y₂ h := by
    dsimp
    obtain hx₂ | ⟨x₁, hx₁⟩ := e.r_cases x₂
    · exact K.extendd_eq_zero _ _ hx₂
    · obtain hy₂ | ⟨y₁, hy₁⟩ := e.r_cases y₂
      · exact K.extendd_eq_zero' _ _ hy₂
      · rw [K.extendd_eq _ _ _ _ hx₁ hy₁, K.shape, zero_comp, comp_zero]
        intro h'
        simp only [e.r_eq_some_iff] at hx₁ hy₁
        substs hx₁ hy₁
        exact h ((e.iff _ _).1 h')
  d_comp_d' x₂ y₂ z₂ _ _ := by
    dsimp
    obtain hx₂ | ⟨x₁, hx₁⟩ := e.r_cases x₂
    · rw [K.extendd_eq_zero _ _ hx₂, zero_comp]
    · obtain hy₂ | ⟨y₁, hy₁⟩ := e.r_cases y₂
      · rw [K.extendd_eq_zero _ _ hy₂, comp_zero]
      · obtain hz₂ | ⟨z₁, hz₁⟩ := e.r_cases z₂
        · rw [K.extendd_eq_zero' _ _ hz₂, comp_zero]
        · simp only [K.extendd_eq _ _ _ _ hx₁ hy₁, K.extendd_eq _ _ _ _ hy₁ hz₁,
            assoc, Iso.inv_hom_id_assoc, d_comp_d_assoc, zero_comp, comp_zero]

noncomputable def extendXIso' (x₁ : ι₁) (x₂ : ι₂) (h : e.φ x₁ = x₂) :
    (K.extend e).X x₂ ≅ K.X x₁ :=
  K.extendXIso (e.r x₂) x₁ ((e.r_eq_some_iff _ _).2 h)

lemma extend_d_eq (x₁ y₁ : ι₁) (x₂ y₂ : ι₂) (hy₁ : e.φ x₁ = x₂) (hy₂ : e.φ y₁ = y₂) :
    (K.extend e).d x₂ y₂ =
      (K.extendXIso' e _ _ hy₁).hom ≫ K.d x₁ y₁ ≫ (K.extendXIso' e _ _ hy₂).inv :=
  K.extendd_eq _ _ _ _ _ _

variable {K L}

noncomputable def extendMapf : ∀ (i : Option ι₁), K.extendX i ⟶ L.extendX i
  | none => 0
  | some x => ψ.f x

lemma extendMapf_eq_zero (x : Option ι₁) (hx : x = none) : extendMapf ψ x = 0 := by
  subst hx
  rfl

lemma extendMapf_eq (x : Option ι₁) (y : ι₁) (hx : x = some y) : extendMapf ψ x =
    (K.extendXIso _ _ hx).hom ≫ ψ.f y ≫ (L.extendXIso _ _ hx).inv := by
  subst hx
  dsimp [extendMapf, extendXIso]
  erw [comp_id, id_comp]

noncomputable def extendMap : K.extend e ⟶ L.extend e where
  f x₂ := extendMapf ψ (e.r x₂)
  comm' x₂ y₂ _ := by
    obtain hx₂ | ⟨x₁, hx₁⟩ := e.r_cases x₂
    · apply (K.isZero_extendX _ hx₂).eq_of_src
    · obtain hy₂ | ⟨y₁, hy₁⟩ := e.r_cases y₂
      · apply (L.isZero_extendX _ hy₂).eq_of_tgt
      · dsimp [extend]
        simp only [K.extendd_eq _ _ _ _ hx₁ hy₁, L.extendd_eq _ _ _ _ hx₁ hy₁,
          extendMapf_eq ψ _ _ hx₁, extendMapf_eq ψ _ _ hy₁,
          assoc, Iso.inv_hom_id_assoc, Hom.comm_assoc]

variable (C)

noncomputable def extendFunctor : HomologicalComplex C c₁ ⥤ HomologicalComplex C c₂ where
  obj K := K.extend e
  map ψ := extendMap ψ e
  map_id K := by
    ext x₂
    obtain hx₂ | ⟨x₁, hx₁⟩ := e.r_cases x₂
    · apply (K.isZero_extendX _ hx₂).eq_of_src
    · dsimp [extendMap]
      simp only [extendMapf_eq (𝟙 K) _ _ hx₁, id_f, id_comp, Iso.hom_inv_id]
      rfl
  map_comp {K L M} ψ ψ' := by
    ext x₂
    obtain hx₂ | ⟨x₁, hx₁⟩ := e.r_cases x₂
    · apply (K.isZero_extendX _ hx₂).eq_of_src
    · dsimp [extendMap]
      simp only [extendMapf_eq _ _ _ hx₁, comp_f, assoc, Iso.inv_hom_id_assoc]

section

variable {C} (K) (x₁ y₁ z₁ : ι₁) (x₂ y₂ z₂ : ι₂)

noncomputable def extendXMap : K.X x₁ ⟶ (K.extend e).X x₂ := by
  classical
  exact if h : e.φ x₁ = x₂
    then (K.extendXIso _ _ ((e.r_eq_some_iff _ _).2 h)).inv
    else 0

noncomputable def extendXMap' : (K.extend e).X x₂ ⟶ K.X x₁ := by
  classical
  exact if h : e.φ x₁ = x₂
    then (K.extendXIso _ _ ((e.r_eq_some_iff _ _).2 h)).hom
    else 0

lemma extendXMap_eq (h : e.φ x₁ = x₂) :
    K.extendXMap e x₁ x₂ =
      (K.extendXIso' e _ _ h).inv := by
  dsimp [extendXMap, extendXIso']
  rw [dif_pos h]

lemma extendXMap'_eq (h : e.φ x₁ = x₂) :
    K.extendXMap' e x₁ x₂ =
      (K.extendXIso' e _ _ h).hom := by
  dsimp [extendXMap', extendXIso']
  rw [dif_pos h]

lemma extendXMap_eq_zero (h : e.φ x₁ ≠ x₂) :
    K.extendXMap e x₁ x₂ = 0 := by
  dsimp [extendXMap]
  rw [dif_neg h]

lemma extendXMap'_eq_zero (h : e.φ x₁ ≠ x₂) :
    K.extendXMap' e x₁ x₂ = 0 := by
  dsimp [extendXMap']
  rw [dif_neg h]

variable (hy : e.φ y₁ = y₂) (hxy₁ : c₁.prev y₁ = x₁) (hyz₁ : c₁.next y₁ = z₁)
  (hxy₂ : c₂.prev y₂ = x₂) (hyz₂ : c₂.next y₂ = z₂)

@[simps]
noncomputable def extendSc'Map : K.sc' x₁ y₁ z₁ ⟶ (K.extend e).sc' x₂ y₂ z₂ where
  τ₁ := K.extendXMap e x₁ x₂
  τ₂ := K.extendXMap e y₁ y₂
  τ₃ := K.extendXMap e z₁ z₂
  comm₁₂ := by
    dsimp
    rw [K.extendXMap_eq e _ _ hy]
    by_cases h : c₁.Rel x₁ y₁
    · have hx : e.φ x₁ = x₂ := by rw [← c₂.prev_eq' ((e.iff _ _).1 h), hy, hxy₂]
      rw [K.extendXMap_eq e _ _ hx, K.extend_d_eq _ _ _ _ _ hx hy,
        Iso.inv_hom_id_assoc]
    · rw [K.shape _ _ h, zero_comp]
      by_cases h' : e.φ x₁ = x₂
      · rw [shape, comp_zero]
        intro h''
        substs h' hy
        exact h (by simpa only [← e.iff] using h'')
      · rw [extendXMap_eq_zero _ _ _ _ h', zero_comp]
  comm₂₃ := by
    dsimp
    rw [K.extendXMap_eq e _ _ hy]
    by_cases h : c₁.Rel y₁ z₁
    · have hz : e.φ z₁ = z₂ := by rw [← c₂.next_eq' ((e.iff _ _).1 h), hy, hyz₂]
      rw [K.extendXMap_eq e _ _ hz, K.extend_d_eq _ _ _ _ _ hy hz, Iso.inv_hom_id_assoc]
    · rw [K.shape _ _ h, zero_comp]
      by_cases h : e.r z₂ = none
      · dsimp [extend]
        rw [K.extendd_eq_zero' _ _ h, comp_zero]
      · obtain ⟨u, _, rfl⟩ := (e.r_neq_none_iff z₂).1 h
        rw [K.extend_d_eq e y₁ u y₂ _ hy rfl]
        subst hy
        rw [shape, zero_comp, comp_zero, comp_zero]
        intro hu
        rw [c₁.next_eq' hu] at hyz₁
        subst hyz₁
        tauto

@[simps]
noncomputable def extendSc'Map' : (K.extend e).sc' x₂ y₂ z₂ ⟶ K.sc' x₁ y₁ z₁ where
  τ₁ := K.extendXMap' e x₁ x₂
  τ₂ := K.extendXMap' e y₁ y₂
  τ₃ := K.extendXMap' e z₁ z₂
  comm₁₂ := by
    dsimp
    rw [K.extendXMap'_eq e _ _ hy]
    by_cases h : c₁.Rel x₁ y₁
    · have hx : e.φ x₁ = x₂ := by rw [← c₂.prev_eq' ((e.iff _ _).1 h), hy, hxy₂]
      rw [K.extendXMap'_eq e _ _ hx, K.extend_d_eq _ _ _ _ _ hx hy,
        assoc, assoc, Iso.inv_hom_id, comp_id]
    · rw [K.shape _ _ h, comp_zero]
      by_cases h : e.r x₂ = none
      · dsimp [extend]
        rw [K.extendd_eq_zero _ _ h, zero_comp]
      · obtain ⟨u, _, rfl⟩ := (e.r_neq_none_iff x₂).1 h
        rw [K.extend_d_eq e u y₁ _ y₂ rfl hy]
        subst hy
        rw [shape, zero_comp, comp_zero, zero_comp]
        intro hu
        rw [c₁.prev_eq' hu] at hxy₁
        subst hxy₁
        tauto
  comm₂₃ := by
    dsimp
    rw [K.extendXMap'_eq e _ _ hy]
    by_cases h : c₁.Rel y₁ z₁
    · have hz : e.φ z₁ = z₂ := by rw [← c₂.next_eq' ((e.iff _ _).1 h), hy, hyz₂]
      rw [K.extendXMap'_eq e _ _ hz, K.extend_d_eq _ _ _ _ _ hy hz,
        assoc, assoc, Iso.inv_hom_id, comp_id]
    · rw [K.shape _ _ h, comp_zero]
      by_cases h' : e.φ z₁ = z₂
      · rw [shape, zero_comp]
        intro h''
        substs h' hy
        exact h (by simpa only [← e.iff] using h'')
      · rw [extendXMap'_eq_zero _ _ _ _ h', comp_zero]

variable [(K.sc' x₁ y₁ z₁).HasHomology] [((K.extend e).sc' x₂ y₂ z₂).HasHomology]

lemma extendXMap_comp_extendXMap' :
    K.extendXMap e y₁ y₂ ≫ K.extendXMap' e y₁ y₂ = 𝟙 _ := by
  rw [K.extendXMap_eq e _ _ hy, K.extendXMap'_eq e _ _ hy, Iso.inv_hom_id]

lemma extendXMap'_comp_extendXMap :
    K.extendXMap' e y₁ y₂ ≫ K.extendXMap e y₁ y₂ = 𝟙 _ := by
  rw [K.extendXMap_eq e _ _ hy, K.extendXMap'_eq e _ _ hy, Iso.hom_inv_id]

section

variable [K.HasHomology y₁] [(K.extend e).HasHomology y₂]

noncomputable def extendCyclesIso :
    (K.extend e).cycles y₂ ≅ K.cycles y₁ :=
  ShortComplex.isoCyclesOfIso₂
    (by exact K.extendSc'Map' e _ y₁ (c₁.next y₁) _ y₂ _ hy rfl rfl rfl)
    (by exact K.extendSc'Map e (c₁.prev y₁) y₁ _ _ y₂ _ hy rfl rfl rfl)
    (by exact K.extendXMap'_comp_extendXMap e _ _ hy)
    (by exact K.extendXMap_comp_extendXMap' e _ _ hy)

noncomputable def extendOpcyclesIso :
    (K.extend e).opcycles y₂ ≅ K.opcycles y₁ :=
  ShortComplex.isoOpcyclesOfIso₂
    (by exact K.extendSc'Map' e _ y₁ (c₁.next y₁) _ y₂ _ hy rfl rfl rfl)
    (by exact K.extendSc'Map e (c₁.prev y₁) y₁ _ _ y₂ _ hy rfl rfl rfl)
    (by exact K.extendXMap'_comp_extendXMap e _ _ hy)
    (by exact K.extendXMap_comp_extendXMap' e _ _ hy)

noncomputable def extendHomologyIso :
    (K.extend e).homology y₂ ≅ K.homology y₁ :=
  ShortComplex.isoHomologyOfIso₂
    (by exact K.extendSc'Map' e _ y₁ (c₁.next y₁) _ y₂ _ hy rfl rfl rfl)
    (by exact K.extendSc'Map e (c₁.prev y₁) y₁ _ _ y₂ _ hy rfl rfl rfl)
    (by exact K.extendXMap'_comp_extendXMap e _ _ hy)
    (by exact K.extendXMap_comp_extendXMap' e _ _ hy)

@[reassoc]
lemma homologyπ_comp_extendHomologyIso_hom :
    (K.extend e).homologyπ y₂ ≫ (K.extendHomologyIso e _ _ hy).hom =
      (K.extendCyclesIso e _ _ hy).hom ≫ K.homologyπ y₁ :=  by
  apply ShortComplex.homologyπ_comp_isoHomologyOfIso₂_hom

end

section

instance [h : (K.extend e).HasHomology y₂] : ((extendFunctor C e).obj K).HasHomology y₂ := h

variable {K}
variable [K.HasHomology y₁] [(K.extend e).HasHomology y₂]
  [(K.extend e).HasHomology y₂]
  [L.HasHomology y₁] [(L.extend e).HasHomology y₂]

@[reassoc (attr := simp)]
lemma extendCyclesIso_hom_naturality :
    cyclesMap ((extendFunctor C e).map ψ) y₂ ≫ (L.extendCyclesIso e _ _ hy).hom =
      (K.extendCyclesIso e _ _ hy).hom ≫ cyclesMap ψ y₁ := by
  rw [← cancel_mono (L.iCycles y₁), assoc, assoc, cyclesMap_i]
  erw [ShortComplex.isoCyclesOfIso₂_hom_comp_iCycles,
    ShortComplex.cyclesMap_i_assoc,
    ShortComplex.isoCyclesOfIso₂_hom_comp_iCycles_assoc]
  dsimp [extendFunctor, extendMap]
  rw [extendMapf_eq ψ (e.r y₂) y₁ ((e.r_eq_some_iff _ _).2 hy),
    K.extendXMap'_eq e _ _ hy, L.extendXMap'_eq e _ _ hy]
  dsimp [extendXIso']
  simp only [assoc, Iso.inv_hom_id, comp_id]

@[reassoc (attr := simp)]
lemma extendOpcyclesIso_hom_naturality :
    opcyclesMap ((extendFunctor C e).map ψ) y₂ ≫ (L.extendOpcyclesIso e _ _ hy).hom =
      (K.extendOpcyclesIso e _ _ hy).hom ≫ opcyclesMap ψ  y₁ := by
  rw [← cancel_epi ((K.extend e).pOpcycles y₂), p_opcyclesMap_assoc]
  erw [ShortComplex.pOpcycles_comp_isoOpcyclesOfIso₂_hom]
  erw [ShortComplex.pOpcycles_comp_isoOpcyclesOfIso₂_hom_assoc]
  erw [ShortComplex.p_opcyclesMap]
  dsimp [extendFunctor, extendMap]
  simp only [← assoc]
  congr 1
  rw [extendMapf_eq ψ (e.r y₂) y₁ ((e.r_eq_some_iff _ _).2 hy),
    K.extendXMap'_eq e _ _ hy, L.extendXMap'_eq e _ _ hy]
  dsimp [extendXIso']
  simp only [assoc, Iso.inv_hom_id, comp_id]

@[reassoc (attr := simp)]
lemma extendHomologyIso_hom_naturality :
    homologyMap ((extendFunctor C e).map ψ) y₂ ≫ (L.extendHomologyIso e _ _ hy).hom =
      (K.extendHomologyIso e _ _ hy).hom ≫ homologyMap ψ  y₁ := by
  rw [← cancel_epi (HomologicalComplex.homologyπ _ _),
    homologyπ_naturality_assoc]
  erw [homologyπ_comp_extendHomologyIso_hom]
  erw [homologyπ_comp_extendHomologyIso_hom_assoc]
  rw [extendCyclesIso_hom_naturality_assoc, homologyπ_naturality]

end

section

variable [CategoryWithHomology C]

@[simps!]
noncomputable def extendCyclesNatIso :
    extendFunctor C e ⋙ cyclesFunctor C c₂ y₂ ≅ cyclesFunctor C c₁ y₁ :=
  NatIso.ofComponents (fun K => K.extendCyclesIso e _ _ hy) (by aesop_cat)

@[simps!]
noncomputable def extendOpcyclesNatIso :
    extendFunctor C e ⋙ opcyclesFunctor C c₂ y₂ ≅ opcyclesFunctor C c₁ y₁ :=
  NatIso.ofComponents (fun K => K.extendOpcyclesIso e _ _ hy) (by aesop_cat)

@[simps!]
noncomputable def extendHomologyNatIso :
    extendFunctor C e ⋙ homologyFunctor C c₂ y₂ ≅ homologyFunctor C c₁ y₁ :=
  NatIso.ofComponents (fun K => K.extendHomologyIso e _ _ hy) (by aesop_cat)

end

end

section

@[simps]
def restrictionFunctor : HomologicalComplex C c₂ ⥤ HomologicalComplex C c₁ where
  obj K :=
    { X := fun i => K.X (e.φ i)
      d := fun i j => K.d _ _
      shape := fun i j hij => K.shape _ _ (fun H => hij (by simpa only [e.iff] using H))
      d_comp_d' := fun _ _ _ _ _ => K.d_comp_d _ _ _ }
  map {K L} φ :=
    { f := fun i => φ.f (e.φ i) }

end

section

noncomputable def extendFunctorCompRestrictionFunctor :
    extendFunctor C e ⋙ restrictionFunctor C e ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun K => HomologicalComplex.Hom.isoOfComponents (fun x₁ => extendXIso _ _ _ (by simp))
      (fun i j _ => by
        simp [extendFunctor, K.extend_d_eq e _ _ _ _ rfl rfl, extendXIso']))
    (fun {K L} ψ => by
      ext n
      dsimp [extendFunctor, extendMap]
      rw [extendMapf_eq ψ (e.r (e.φ n)) n (by simp),
        assoc, assoc, Iso.inv_hom_id, comp_id])

end

end HomologicalComplex
-/
