import Mathlib.Algebra.Homology.ShortComplex.RightHomology

namespace CategoryTheory

open Category Limits

variable {C D : Type _} [Category C] [Category D]
  [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ S₄ : ShortComplex C}

namespace ShortComplex

structure HomologyData where
  left : S.LeftHomologyData
  right : S.RightHomologyData
  iso : left.H ≅ right.H
  comm : left.π ≫ iso.hom ≫ right.ι = left.i ≫ right.p := by aesop_cat

attribute [reassoc (attr := simp)] HomologyData.comm

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

structure HomologyMapData :=
(left : LeftHomologyMapData φ h₁.left h₂.left)
(right : RightHomologyMapData φ h₁.right h₂.right)

namespace HomologyMapData

attribute [nolint simpNF] mk.injEq

variable {φ h₁ h₂}

@[reassoc]
lemma comm (h : HomologyMapData φ h₁ h₂) :
    h.left.φH ≫ h₂.iso.hom = h₁.iso.hom ≫ h.right.φH := by
  simp only [← cancel_epi h₁.left.π, ← cancel_mono h₂.right.ι, assoc,
    LeftHomologyMapData.commπ_assoc, HomologyData.comm, LeftHomologyMapData.commi_assoc,
    RightHomologyMapData.commι, HomologyData.comm_assoc, RightHomologyMapData.commp]

instance : Subsingleton (HomologyMapData φ h₁ h₂) := ⟨by
  rintro ⟨left₁, right₁⟩ ⟨left₂, right₂⟩
  simp only [mk.injEq, eq_iff_true_of_subsingleton, and_self]⟩

instance : Inhabited (HomologyMapData φ h₁ h₂) :=
  ⟨⟨default, default⟩⟩

instance : Unique (HomologyMapData φ h₁ h₂) := Unique.mk' _

variable (φ h₁ h₂)

def some : HomologyMapData φ h₁ h₂ := default

variable {φ h₁ h₂}

lemma congr_left_φH {γ₁ γ₂ : HomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) :
  γ₁.left.φH = γ₂.left.φH := by rw [eq]

end HomologyMapData

namespace HomologyData

@[simps]
def ofIsLimitKernelFork (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c) :
    S.HomologyData where
  left := LeftHomologyData.ofIsLimitKernelFork S hf c hc
  right := RightHomologyData.ofIsLimitKernelFork S hf c hc
  iso := Iso.refl _

@[simps]
noncomputable def ofHasKernel (hf : S.f = 0) [HasKernel S.g] :
    S.HomologyData where
  left := LeftHomologyData.ofHasKernel S hf
  right := RightHomologyData.ofHasKernel S hf
  iso := Iso.refl _

@[simps]
def ofIsColimitCokernelCofork (hg : S.g = 0) (c : CokernelCofork S.f) (hc : IsColimit c) :
    S.HomologyData where
  left := LeftHomologyData.ofIsColimitCokernelCofork S hg c hc
  right := RightHomologyData.ofIsColimitCokernelCofork S hg c hc
  iso := Iso.refl _

@[simps]
noncomputable def ofHasCokernel (hg : S.g = 0) [HasCokernel S.f] :
    S.HomologyData where
  left := LeftHomologyData.ofHasCokernel S hg
  right := RightHomologyData.ofHasCokernel S hg
  iso := Iso.refl _

@[simps]
noncomputable def ofZeros (hf : S.f = 0) (hg : S.g = 0) :
    S.HomologyData where
  left := LeftHomologyData.ofZeros S hf hg
  right := RightHomologyData.ofZeros S hf hg
  iso := Iso.refl _

@[simps]
noncomputable def ofEpiOfIsIsoOfMono (φ : S₁ ⟶ S₂) (h : HomologyData S₁)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HomologyData S₂ where
  left := LeftHomologyData.ofEpiOfIsIsoOfMono φ h.left
  right := RightHomologyData.ofEpiOfIsIsoOfMono φ h.right
  iso := h.iso

@[simps]
noncomputable def ofEpiOfIsIsoOfMono' (φ : S₁ ⟶ S₂) (h : HomologyData S₂)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HomologyData S₁ where
  left := LeftHomologyData.ofEpiOfIsIsoOfMono' φ h.left
  right := RightHomologyData.ofEpiOfIsIsoOfMono' φ h.right
  iso := h.iso

@[simps!]
noncomputable def ofIso (e : S₁ ≅ S₂) (h : HomologyData S₁) :=
  h.ofEpiOfIsIsoOfMono e.hom

variable {S}

@[simps]
def op (h : S.HomologyData) : S.op.HomologyData where
  left := h.right.op
  right := h.left.op
  iso := h.iso.op
  comm := Quiver.Hom.unop_inj (by simp)

@[simps]
def unop {S : ShortComplex Cᵒᵖ} (h : S.HomologyData) : S.unop.HomologyData where
  left := h.right.unop
  right := h.left.unop
  iso := h.iso.unop
  comm := Quiver.Hom.op_inj (by simp)

end HomologyData

class HasHomology : Prop where
  condition : Nonempty S.HomologyData

noncomputable def homologyData [HasHomology S] :
  S.HomologyData := HasHomology.condition.some

variable {S}

lemma HasHomology.mk' (h : S.HomologyData) : HasHomology S :=
  ⟨Nonempty.intro h⟩

instance [HasHomology S] : HasHomology S.op :=
  HasHomology.mk' S.homologyData.op

instance hasLeftHomology_of_hasHomology [S.HasHomology] : S.HasLeftHomology :=
  HasLeftHomology.mk' S.homologyData.left

instance hasRightHomology_of_hasHomology [S.HasHomology] : S.HasRightHomology :=
  HasRightHomology.mk' S.homologyData.right

instance hasHomology_of_hasCokernel {X Y : C} (f : X ⟶ Y) (Z : C) [HasCokernel f] :
    (ShortComplex.mk f (0 : Y ⟶ Z) comp_zero).HasHomology :=
  HasHomology.mk' (HomologyData.ofHasCokernel _ rfl)

instance hasHomology_of_hasKernel {Y Z : C} (g : Y ⟶ Z) (X : C) [HasKernel g] :
    (ShortComplex.mk (0 : X ⟶ Y) g zero_comp).HasHomology :=
  HasHomology.mk' (HomologyData.ofHasKernel _ rfl)

instance hasHomology_of_zeros (X Y Z : C) :
    (ShortComplex.mk (0 : X ⟶ Y) (0 : Y ⟶ Z) zero_comp).HasHomology :=
  HasHomology.mk' (HomologyData.ofZeros _ rfl rfl)

lemma hasHomology_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [HasHomology S₁]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasHomology S₂ :=
  HasHomology.mk' (HomologyData.ofEpiOfIsIsoOfMono φ S₁.homologyData)

lemma hasHomology_of_epi_of_isIso_of_mono' (φ : S₁ ⟶ S₂) [HasHomology S₂]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasHomology S₁ :=
  HasHomology.mk' (HomologyData.ofEpiOfIsIsoOfMono' φ S₂.homologyData)

lemma hasHomology_of_iso (e : S₁ ≅ S₂) [HasHomology S₁] : HasHomology S₂ :=
  HasHomology.mk' (HomologyData.ofIso e S₁.homologyData)

namespace HomologyMapData

@[simps]
def id (h : S.HomologyData) : HomologyMapData (𝟙 S) h h where
  left := LeftHomologyMapData.id h.left
  right := RightHomologyMapData.id h.right

@[simps]
def zero (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) :
  HomologyMapData 0 h₁ h₂ where
  left := LeftHomologyMapData.zero h₁.left h₂.left
  right := RightHomologyMapData.zero h₁.right h₂.right

@[simps]
def comp {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃} {h₁ : S₁.HomologyData}
    {h₂ : S₂.HomologyData} {h₃ : S₃.HomologyData}
    (ψ : HomologyMapData φ h₁ h₂) (ψ' : HomologyMapData φ' h₂ h₃) :
    HomologyMapData (φ ≫ φ') h₁ h₃ where
  left := ψ.left.comp ψ'.left
  right := ψ.right.comp ψ'.right

@[simps]
def op {φ : S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}
    (ψ : HomologyMapData φ h₁ h₂) :
    HomologyMapData (opMap φ) h₂.op h₁.op where
  left := ψ.right.op
  right := ψ.left.op

@[simps]
def unop {S₁ S₂ : ShortComplex Cᵒᵖ} {φ : S₁ ⟶ S₂}
    {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}
    (ψ : HomologyMapData φ h₁ h₂) :
    HomologyMapData (unopMap φ) h₂.unop h₁.unop where
  left := ψ.right.unop
  right := ψ.left.unop

@[simps]
def ofZeros (φ : S₁ ⟶ S₂) (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (hg₂ : S₂.g = 0) :
    HomologyMapData φ (HomologyData.ofZeros S₁ hf₁ hg₁) (HomologyData.ofZeros S₂ hf₂ hg₂) where
  left := LeftHomologyMapData.ofZeros φ hf₁ hg₁ hf₂ hg₂
  right := RightHomologyMapData.ofZeros φ hf₁ hg₁ hf₂ hg₂

@[simps]
def ofIsColimitCokernelCofork (φ : S₁ ⟶ S₂)
  (hg₁ : S₁.g = 0) (c₁ : CokernelCofork S₁.f) (hc₁ : IsColimit c₁)
  (hg₂ : S₂.g = 0) (c₂ : CokernelCofork S₂.f) (hc₂ : IsColimit c₂) (f : c₁.pt ⟶ c₂.pt)
  (comm : φ.τ₂ ≫ c₂.π = c₁.π ≫ f) :
  HomologyMapData φ (HomologyData.ofIsColimitCokernelCofork S₁ hg₁ c₁ hc₁)
    (HomologyData.ofIsColimitCokernelCofork S₂ hg₂ c₂ hc₂) where
  left := LeftHomologyMapData.ofIsColimitCokernelCofork φ hg₁ c₁ hc₁ hg₂ c₂ hc₂ f comm
  right := RightHomologyMapData.ofIsColimitCokernelCofork φ hg₁ c₁ hc₁ hg₂ c₂ hc₂ f comm

@[simps]
def ofIsLimitKernelFork (φ : S₁ ⟶ S₂)
  (hf₁ : S₁.f = 0) (c₁ : KernelFork S₁.g) (hc₁ : IsLimit c₁)
  (hf₂ : S₂.f = 0) (c₂ : KernelFork S₂.g) (hc₂ : IsLimit c₂) (f : c₁.pt ⟶ c₂.pt)
  (comm : c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι) :
  HomologyMapData φ (HomologyData.ofIsLimitKernelFork S₁ hf₁ c₁ hc₁)
    (HomologyData.ofIsLimitKernelFork S₂ hf₂ c₂ hc₂) where
  left := LeftHomologyMapData.ofIsLimitKernelFork φ hf₁ c₁ hc₁ hf₂ c₂ hc₂ f comm
  right := RightHomologyMapData.ofIsLimitKernelFork φ hf₁ c₁ hc₁ hf₂ c₂ hc₂ f comm

def compatibilityOfZerosOfIsColimitCokernelCofork (hf : S.f = 0) (hg : S.g = 0)
  (c : CokernelCofork S.f) (hc : IsColimit c) :
  HomologyMapData (𝟙 S) (HomologyData.ofZeros S hf hg)
    (HomologyData.ofIsColimitCokernelCofork S hg c hc) where
  left := LeftHomologyMapData.compatibilityOfZerosOfIsColimitCokernelCofork S hf hg c hc
  right := RightHomologyMapData.compatibilityOfZerosOfIsColimitCokernelCofork S hf hg c hc

@[simps]
def compatibilityOfZerosOfIsLimitKernelFork (hf : S.f = 0) (hg : S.g = 0)
  (c : KernelFork S.g) (hc : IsLimit c) :
  HomologyMapData (𝟙 S)
    (HomologyData.ofIsLimitKernelFork S hf c hc)
    (HomologyData.ofZeros S hf hg) where
  left := LeftHomologyMapData.compatibilityOfZerosOfIsLimitKernelFork S hf hg c hc
  right := RightHomologyMapData.compatibilityOfZerosOfIsLimitKernelFork S hf hg c hc

end HomologyMapData

variable (S)

noncomputable def homology [HasHomology S] : C := S.homologyData.left.H

noncomputable def leftHomologyIso [S.HasHomology] : S.leftHomology ≅ S.homology :=
  leftHomologyMapIso' (Iso.refl _) _ _

noncomputable def rightHomologyIso [S.HasHomology] : S.rightHomology ≅ S.homology :=
  rightHomologyMapIso' (Iso.refl _) _ _ ≪≫ S.homologyData.iso.symm

variable {S}

noncomputable def LeftHomologyData.homologyIso (h : S.LeftHomologyData) [S.HasHomology] :
    S.homology ≅ h.H := S.leftHomologyIso.symm ≪≫ h.leftHomologyIso

noncomputable def RightHomologyData.homologyIso (h : S.RightHomologyData) [S.HasHomology] :
    S.homology ≅ h.H := S.rightHomologyIso.symm ≪≫ h.rightHomologyIso

def homologyMap' (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) :
  h₁.left.H ⟶ h₂.left.H := leftHomologyMap' φ _ _

noncomputable def homologyMap (φ : S₁ ⟶ S₂) [HasHomology S₁] [HasHomology S₂] :
    S₁.homology ⟶ S₂.homology :=
  homologyMap' φ _ _

namespace HomologyMapData

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}
  (γ : HomologyMapData φ h₁ h₂)

lemma homologyMap'_eq : homologyMap' φ h₁ h₂ = γ.left.φH :=
  LeftHomologyMapData.congr_φH (Subsingleton.elim _ _)

lemma cyclesMap'_eq : cyclesMap' φ h₁.left h₂.left = γ.left.φK :=
  LeftHomologyMapData.congr_φK (Subsingleton.elim _ _)

lemma cyclesCoMap'_eq : cyclesCoMap' φ h₁.right h₂.right = γ.right.φQ :=
  RightHomologyMapData.congr_φQ (Subsingleton.elim _ _)

end HomologyMapData

namespace LeftHomologyMapData

variable {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}
  (γ : LeftHomologyMapData φ h₁ h₂) [S₁.HasHomology] [S₂.HasHomology]

lemma homologyMap_eq :
    homologyMap φ = h₁.homologyIso.hom ≫ γ.φH ≫ h₂.homologyIso.inv := by
  dsimp only [homologyMap, LeftHomologyData.homologyIso,
    Iso.trans, Iso.symm, leftHomologyIso, LeftHomologyData.leftHomologyIso,
    leftHomologyMapIso', homologyMap', Iso.refl]
  simp only [← γ.leftHomologyMap'_eq, ← leftHomologyMap'_comp, id_comp, comp_id]

lemma homologyMap_comm :
    homologyMap φ ≫ h₂.homologyIso.hom = h₁.homologyIso.hom ≫ γ.φH := by
  simp only [γ.homologyMap_eq, assoc, Iso.inv_hom_id, comp_id]

end LeftHomologyMapData

namespace RightHomologyMapData

variable {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}
  (γ : RightHomologyMapData φ h₁ h₂) [S₁.HasHomology] [S₂.HasHomology]

lemma homologyMap_eq :
    homologyMap φ = h₁.homologyIso.hom ≫ γ.φH ≫ h₂.homologyIso.inv := by
  dsimp only [homologyMap, homologyMap', RightHomologyData.homologyIso, Iso.symm, Iso.trans,
    Iso.refl, rightHomologyIso, rightHomologyMapIso', RightHomologyData.rightHomologyIso]
  have γ' : HomologyMapData φ S₁.homologyData S₂.homologyData := default
  simp only [← γ.rightHomologyMap'_eq, assoc, ← rightHomologyMap'_comp_assoc,
    id_comp, comp_id, γ'.left.leftHomologyMap'_eq, γ'.right.rightHomologyMap'_eq, ← γ'.comm_assoc,
    Iso.hom_inv_id]

lemma homologyMap_comm :
    homologyMap φ ≫ h₂.homologyIso.hom = h₁.homologyIso.hom ≫ γ.φH := by
  simp only [γ.homologyMap_eq, assoc, Iso.inv_hom_id, comp_id]

end RightHomologyMapData

@[simp]
lemma homologyMap'_id (h : S.HomologyData) :
    homologyMap' (𝟙 S) h h = 𝟙 _ :=
  (HomologyMapData.id h).homologyMap'_eq

variable (S)

@[simp]
lemma homologyMap_id [HasHomology S] :
    homologyMap (𝟙 S) = 𝟙 _ :=
  homologyMap'_id _

@[simp]
lemma homologyMap'_zero (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) :
    homologyMap' 0 h₁ h₂ = 0 :=
  (HomologyMapData.zero h₁ h₂).homologyMap'_eq

variable (S₁ S₂)

@[simp]
lemma homologyMap_zero [S₁.HasHomology] [S₂.HasHomology] :
    homologyMap (0 : S₁ ⟶ S₂) = 0 :=
  homologyMap'_zero _ _

variable {S₁ S₂}

lemma homologyMap'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) (h₃ : S₃.HomologyData) :
    homologyMap' (φ₁ ≫ φ₂) h₁ h₃ = homologyMap' φ₁ h₁ h₂ ≫
      homologyMap' φ₂ h₂ h₃ :=
  leftHomologyMap'_comp _ _ _ _ _

@[simp]
lemma homologyMap_comp [HasHomology S₁] [HasHomology S₂] [HasHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    homologyMap (φ₁ ≫ φ₂) = homologyMap φ₁ ≫ homologyMap φ₂ :=
homologyMap'_comp _ _ _ _ _

@[simps]
def homologyMapIso' (e : S₁ ≅ S₂) (h₁ : S₁.HomologyData)
    (h₂ : S₂.HomologyData) : h₁.left.H ≅ h₂.left.H where
  hom := homologyMap' e.hom h₁ h₂
  inv := homologyMap' e.inv h₂ h₁
  hom_inv_id := by rw [← homologyMap'_comp, e.hom_inv_id, homologyMap'_id]
  inv_hom_id := by rw [← homologyMap'_comp, e.inv_hom_id, homologyMap'_id]

instance isIso_homologyMap'_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ]
    (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) :
    IsIso (homologyMap' φ h₁ h₂) :=
  (inferInstance : IsIso (homologyMapIso' (asIso φ) h₁ h₂).hom)

@[simps]
noncomputable def homologyMapIso (e : S₁ ≅ S₂) [S₁.HasHomology]
  [S₂.HasHomology] : S₁.homology ≅ S₂.homology where
  hom := homologyMap e.hom
  inv := homologyMap e.inv
  hom_inv_id := by rw [← homologyMap_comp, e.hom_inv_id, homologyMap_id]
  inv_hom_id := by rw [← homologyMap_comp, e.inv_hom_id, homologyMap_id]

instance isIso_homologyMap_of_iso (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasHomology]
    [S₂.HasHomology] :
    IsIso (homologyMap φ) :=
  (inferInstance : IsIso (homologyMapIso (asIso φ)).hom)

variable {S}

def leftRightHomologyComparison' (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    h₁.H ⟶ h₂.H :=
  h₂.liftH (h₁.descH (h₁.i ≫ h₂.p) (by simp))
    (by rw [← cancel_epi h₁.π, LeftHomologyData.π_descH_assoc, assoc,
      RightHomologyData.p_g', LeftHomologyData.wi, comp_zero])

lemma leftRightHomologyComparison'_eq₁ (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    leftRightHomologyComparison' h₁ h₂ =
  h₂.liftH (h₁.descH (h₁.i ≫ h₂.p) (by simp))
    (by rw [← cancel_epi h₁.π, LeftHomologyData.π_descH_assoc, assoc,
      RightHomologyData.p_g', LeftHomologyData.wi, comp_zero]) := rfl

@[simp, reassoc]
lemma π_leftRightHomologyComparison'_ι (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    h₁.π ≫ leftRightHomologyComparison' h₁ h₂ ≫ h₂.ι = h₁.i ≫ h₂.p :=
  by simp only [leftRightHomologyComparison'_eq₁,
    RightHomologyData.liftH_ι, LeftHomologyData.π_descH]

lemma leftRightHomologyComparison'_eq₂ (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    leftRightHomologyComparison' h₁ h₂ =
  h₁.descH (h₂.liftH (h₁.i ≫ h₂.p) (by simp))
    (by rw [← cancel_mono h₂.ι, assoc, RightHomologyData.liftH_ι,
      LeftHomologyData.f'_i_assoc, RightHomologyData.wp, zero_comp]) := by
  simp only [← cancel_mono h₂.ι, ← cancel_epi h₁.π, π_leftRightHomologyComparison'_ι,
    LeftHomologyData.π_descH_assoc, RightHomologyData.liftH_ι]

variable (S)

noncomputable def leftRightHomologyComparison [S.HasLeftHomology] [S.HasRightHomology] :
    S.leftHomology ⟶ S.rightHomology :=
  leftRightHomologyComparison' _ _

@[simp, reassoc]
lemma π_leftRightHomologyComparison_ι [S.HasLeftHomology] [S.HasRightHomology] :
    S.leftHomologyπ ≫ S.leftRightHomologyComparison ≫ S.rightHomologyι =
      S.iCycles ≫ S.pCyclesCo :=
  π_leftRightHomologyComparison'_ι _ _

@[reassoc]
lemma leftRightHomologyComparison'_naturality (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData)
  (h₂ : S₁.RightHomologyData) (h₁' : S₂.LeftHomologyData) (h₂' : S₂.RightHomologyData) :
  leftHomologyMap' φ h₁ h₁' ≫ leftRightHomologyComparison' h₁' h₂' =
    leftRightHomologyComparison' h₁ h₂ ≫ rightHomologyMap' φ h₂ h₂' :=
by simp only [← cancel_epi h₁.π, ← cancel_mono h₂'.ι, assoc,
    leftHomologyπ_naturality'_assoc, rightHomologyι_naturality',
    π_leftRightHomologyComparison'_ι,
    π_leftRightHomologyComparison'_ι_assoc,
    cyclesMap'_i_assoc, p_cyclesCoMap']

variable {S}

lemma leftRightHomologyComparison'_compatibility (h₁ h₁' : S.LeftHomologyData)
    (h₂ h₂' : S.RightHomologyData) :
    leftRightHomologyComparison' h₁ h₂ = leftHomologyMap' (𝟙 S) h₁ h₁' ≫
      leftRightHomologyComparison' h₁' h₂' ≫ rightHomologyMap' (𝟙 S) _ _ :=
by rw [leftRightHomologyComparison'_naturality_assoc (𝟙 S) h₁ h₂ h₁' h₂',
    ← rightHomologyMap'_comp, comp_id, rightHomologyMap'_id, comp_id]

lemma leftRightHomologyComparison_eq [S.HasLeftHomology] [S.HasRightHomology]
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    S.leftRightHomologyComparison = h₁.leftHomologyIso.hom ≫
      leftRightHomologyComparison' h₁ h₂ ≫ h₂.rightHomologyIso.inv :=
leftRightHomologyComparison'_compatibility _ _ _ _

@[simp]
lemma HomologyData.leftRightHomologyComparison'_eq (h : S.HomologyData) :
    leftRightHomologyComparison' h.left h.right = h.iso.hom := by
  simp only [←cancel_epi h.left.π, ← cancel_mono h.right.ι,
    π_leftRightHomologyComparison'_ι, HomologyData.comm]

instance isIso_leftRightHomologyComparison'_of_homologyData (h : S.HomologyData) :
  IsIso (leftRightHomologyComparison' h.left h.right) := by
    rw [h.leftRightHomologyComparison'_eq]
    infer_instance

instance isIso_leftRightHomologyComparison' [S.HasHomology]
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    IsIso (leftRightHomologyComparison' h₁ h₂) := by
  rw [leftRightHomologyComparison'_compatibility h₁ S.homologyData.left h₂
    S.homologyData.right]
  infer_instance

instance isIso_leftRightHomologyComparison [S.HasHomology] :
    IsIso S.leftRightHomologyComparison := by
  dsimp only [leftRightHomologyComparison]
  infer_instance

namespace HomologyData

@[simps]
noncomputable def ofIsIsoLeftRightHomologyComparison'
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
    [IsIso (leftRightHomologyComparison' h₁ h₂)] :
    S.HomologyData where
  left := h₁
  right := h₂
  iso := asIso (leftRightHomologyComparison' h₁ h₂)

end HomologyData

end ShortComplex

variable (C)

class CategoryWithHomology : Prop where
  hasHomology : ∀ (S : ShortComplex C), S.HasHomology

attribute [instance] CategoryWithHomology.hasHomology

end CategoryTheory


#exit

namespace left_homology_data

lemma ext_iff {A : C} (h : S.left_homology_data) [S.has_homology] (f₁ f₂ : S.homology ⟶ A) :
  f₁ = f₂ ↔ h.π ≫ h.homology_iso.inv ≫ f₁ = h.π ≫ h.homology_iso.inv ≫ f₂ :=
by rw [← cancel_epi h.homology_iso.inv, cancel_epi h.π]

end left_homology_data





namespace right_homology_data

def homology_iso (h : S.right_homology_data) [S.has_homology] :
  S.homology ≅ h.H :=
as_iso (left_right_homology_comparison' S.some_homology_data.left h)

lemma ext_iff {A : C} (h : S.right_homology_data) [S.has_homology] (f₁ f₂ : A ⟶ S.homology) :
  f₁ = f₂ ↔ f₁ ≫ h.homology_iso.hom ≫ h.ι = f₂ ≫ h.homology_iso.hom ≫ h.ι :=
by simp only [← cancel_mono h.homology_iso.hom, ← cancel_mono h.ι, assoc]

end right_homology_data

namespace homology_data

@[simps]
def of_is_iso_left_right_homology_comparison'
  (h₁ : S.left_homology_data) (h₂ : S.right_homology_data)
  [is_iso (left_right_homology_comparison' h₁ h₂)] :
  S.homology_data :=
{ left := h₁,
  right := h₂,
  iso := as_iso (left_right_homology_comparison' h₁ h₂),
  comm := by simp only [as_iso_hom, comp_left_right_homology_comparison'_comp], }

lemma has_homology_of_is_iso_left_right_homology_comparison'
  (h₁ : S.left_homology_data) (h₂ : S.right_homology_data)
  [is_iso (left_right_homology_comparison' h₁ h₂)] :
  S.has_homology :=
has_homology.mk' (of_is_iso_left_right_homology_comparison' h₁ h₂)

lemma has_homology_of_is_iso_left_right_homology_comparison [S.has_left_homology]
  [S.has_right_homology] [h : is_iso S.left_right_homology_comparison] :
  S.has_homology :=
begin
  haveI : is_iso (left_right_homology_comparison' S.some_left_homology_data
    S.some_right_homology_data) := h,
  exact has_homology_of_is_iso_left_right_homology_comparison' S.some_left_homology_data
    S.some_right_homology_data,
end

end homology_data

@[simps]
def homology_map_data.of_epi_of_is_iso_of_mono (φ : S₁ ⟶ S₂) (h : homology_data S₁)
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] :
    homology_map_data φ h (homology_data.of_epi_of_is_iso_of_mono φ h) :=
{ left := left_homology_map_data.of_epi_of_is_iso_of_mono φ h.left,
  right := right_homology_map_data.of_epi_of_is_iso_of_mono φ h.right, }

@[simps]
def homology_map_data.of_epi_of_is_iso_of_mono' (φ : S₁ ⟶ S₂) (h : homology_data S₂)
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] :
    homology_map_data φ (homology_data.of_epi_of_is_iso_of_mono' φ h) h :=
{ left := left_homology_map_data.of_epi_of_is_iso_of_mono' φ h.left,
  right := right_homology_map_data.of_epi_of_is_iso_of_mono' φ h.right, }

variable (S)

def left_homology_iso_homology [S.has_homology] :
  S.left_homology ≅ S.homology :=
S.some_left_homology_data.homology_iso.symm

@[reassoc]
lemma left_homology_iso_homology_hom_naturality [S₁.has_homology] [S₂.has_homology]
  (φ : S₁ ⟶ S₂) :
  S₁.left_homology_iso_homology.hom ≫ homology_map φ =
    left_homology_map φ ≫ S₂.left_homology_iso_homology.hom :=
begin
  dsimp only [left_homology_iso_homology, left_homology_data.homology_iso,
    homology_map, homology_map', left_homology_map_iso', iso.symm, iso.refl,
    left_homology_map],
  rw [← left_homology_map'_comp, ← left_homology_map'_comp, id_comp, comp_id],
end

def homology_iso_right_homology [S.has_homology] :
  S.homology ≅ S.right_homology :=
S.some_right_homology_data.homology_iso

variable {S}

lemma left_homology_map'_comp_iso_hom_comp_right_homology_map'
  (h : S.homology_data) (h₁ : S.left_homology_data) (h₂ : S.right_homology_data) :
  left_homology_map' (𝟙 S) h₁ h.left ≫ h.iso.hom ≫ right_homology_map' (𝟙 S) h.right h₂ =
    left_right_homology_comparison' h₁ h₂ :=
by simpa using (left_right_homology_comparison'_compatibility h₁ h.left h₂ h.right).symm

variable (S)

@[reassoc]
lemma left_right_homology_comparison_fac [S.has_homology] :
  S.left_right_homology_comparison =
    S.left_homology_iso_homology.hom ≫ S.homology_iso_right_homology.hom :=
begin
  have eq : S.some_homology_data.iso.hom ≫ right_homology_map' (𝟙 S) _ _ =
    S.homology_iso_right_homology.hom := by simpa only [left_homology_map'_id, id_comp]
    using left_homology_map'_comp_iso_hom_comp_right_homology_map' S.some_homology_data
      S.some_homology_data.left S.some_right_homology_data,
  simpa only [eq.symm] using (left_homology_map'_comp_iso_hom_comp_right_homology_map' _ _ _).symm,
end

variable (C)
/-- We shall say that a category with homology is a category for which
all short complexes have homology. -/
class _root_.category_with_homology :=
(has_homology : ∀ (S : short_complex C), S.has_homology)

@[priority 100]
instance category_with_homology.has_homology [category_with_homology C] (S : short_complex C) :
  S.has_homology := category_with_homology.has_homology S

/-- Assuming that all short complexes have homology, this is the homology functor. -/
@[simps]
def homology_functor [category_with_homology C] :
  short_complex C ⥤ C :=
{ obj := λ S, S.homology,
  map := λ S₁ S₂, homology_map, }

instance (φ : S₁ ⟶ S₂) [S₁.has_homology] [S₂.has_homology]
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] :
  is_iso (homology_map φ) :=
by { dsimp only [homology_map, homology_map'], apply_instance, }

section

variables [has_homology S] {A : C} {C}

def homology_π : S.cycles ⟶ S.homology :=
S.left_homology_π ≫ S.left_homology_iso_homology.hom

@[simp, reassoc]
lemma homology_π_comp_left_homology_iso_homology_inv :
  S.homology_π ≫ S.left_homology_iso_homology.inv = S.left_homology_π :=
begin
  dsimp only [homology_π],
  simp only [assoc, iso.hom_inv_id, comp_id],
end

@[simp, reassoc]
lemma to_cycles_comp_homology_π :
  S.to_cycles ≫ S.homology_π = 0 :=
begin
  dsimp only [homology_π],
  simp only [to_cycles_comp_left_homology_π_assoc, zero_comp],
end

def homology_is_cokernel :
  is_colimit (cokernel_cofork.of_π S.homology_π S.to_cycles_comp_homology_π) :=
is_colimit.of_iso_colimit S.left_homology_is_cokernel
  (cofork.ext S.left_homology_iso_homology rfl)

instance : epi S.homology_π :=
limits.epi_of_is_colimit_cofork (S.homology_is_cokernel)

def homology_desc (k : S.cycles ⟶ A) (hk : S.to_cycles ≫ k = 0) :
  S.homology ⟶ A :=
S.homology_is_cokernel.desc (cokernel_cofork.of_π k hk)

@[simp, reassoc]
lemma homology_π_desc (k : S.cycles ⟶ A) (hk : S.to_cycles ≫ k = 0) :
  S.homology_π ≫ S.homology_desc k hk = k :=
cofork.is_colimit.π_desc S.homology_is_cokernel

@[simp, reassoc]
lemma homology_π_naturality (φ : S₁ ⟶ S₂) [S₁.has_homology] [S₂.has_homology] :
  S₁.homology_π ≫ homology_map φ = cycles_map φ ≫ S₂.homology_π :=
begin
  have eq := left_homology_iso_homology_hom_naturality φ,
  rw [← cancel_epi S₁.left_homology_iso_homology.inv, iso.inv_hom_id_assoc] at eq,
  simp only [← cancel_mono S₂.left_homology_iso_homology.inv,
    assoc, homology_π_comp_left_homology_iso_homology_inv,
    ← left_homology_π_naturality, eq, iso.hom_inv_id, comp_id,
    homology_π_comp_left_homology_iso_homology_inv_assoc],
end

/- dualise the above -/

def homology_ι : S.homology ⟶ S.cycles_co :=
S.homology_iso_right_homology.hom ≫ S.right_homology_ι

@[simp, reassoc]
lemma right_homology_iso_homology_inv_comp_homology_ι :
  S.homology_iso_right_homology.inv ≫ S.homology_ι = S.right_homology_ι :=
begin
  dsimp only [homology_ι],
  simp only [iso.inv_hom_id_assoc],
end

@[simp, reassoc]
lemma homology_ι_comp_from_cycles_co :
  S.homology_ι ≫ S.from_cycles_co = 0 :=
begin
  dsimp only [homology_ι],
  simp only [assoc, right_homology_ι_comp_from_cycles_co, comp_zero],
end

def homology_is_kernel :
  is_limit (kernel_fork.of_ι S.homology_ι S.homology_ι_comp_from_cycles_co) :=
is_limit.of_iso_limit S.right_homology_is_kernel
(fork.ext S.homology_iso_right_homology.symm (by simp))

def homology_lift (k : A ⟶ S.cycles_co) (hk : k ≫ S.from_cycles_co = 0) :
  A ⟶ S.homology :=
S.homology_is_kernel.lift (kernel_fork.of_ι k hk)

@[simp, reassoc]
lemma homology_lift_ι (k : A ⟶ S.cycles_co) (hk : k ≫ S.from_cycles_co = 0) :
  S.homology_lift k hk ≫ S.homology_ι = k :=
fork.is_limit.lift_ι S.homology_is_kernel

@[simp, reassoc]
lemma homology_π_ι :
  S.homology_π ≫ S.homology_ι = S.cycles_i ≫ S.p_cycles_co :=
begin
  dsimp [homology_π, homology_ι],
  rw assoc,
  nth_rewrite 1 ← assoc,
  simpa only [S.left_right_homology_comparison_fac]
    using S.comp_left_right_homology_comparison_comp,
end

lemma is_iso_homology_map'_of_epi_of_is_iso_of_mono (φ : S₁ ⟶ S₂)
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] (h₁ : S₁.homology_data) (h₂ : S₂.homology_data) :
  is_iso (homology_map' φ h₁ h₂) :=
begin
  have eq := homology_map'_comp φ (𝟙 S₂) h₁ (homology_data.of_epi_of_is_iso_of_mono φ h₁) h₂,
  simp only [comp_id, (homology_map_data.of_epi_of_is_iso_of_mono φ h₁).homology_map'_eq,
    homology_map_data.of_epi_of_is_iso_of_mono_left,
    left_homology_map_data.of_epi_of_is_iso_of_mono_φH, id_comp] at eq,
  rw eq,
  apply_instance,
end

end

variable {C}

def homology_iso_kernel_desc [S.has_homology] [has_cokernel S.f]
  [has_kernel (cokernel.desc S.f S.g S.zero)] :
  S.homology ≅ kernel (cokernel.desc S.f S.g S.zero) :=
(right_homology_data.of_coker_of_ker S).homology_iso

def homology_iso_cokernel_lift [S.has_homology] [has_kernel S.g]
  [has_cokernel (kernel.lift S.g S.f S.zero)] :
  S.homology ≅ cokernel (kernel.lift S.g S.f S.zero) :=
(left_homology_data.of_ker_of_coker S).homology_iso

variable {S}

@[simp, reassoc]
lemma left_homology_data.homology_π_comp_homology_iso_hom
  (h : S.left_homology_data) [S.has_homology] :
  S.homology_π ≫ h.homology_iso.hom = h.cycles_iso.hom ≫ h.π :=
begin
  rw [← h.left_homology_π_comp_left_homology_iso_hom,
    ← S.homology_π_comp_left_homology_iso_homology_inv],
  dsimp [left_homology_iso_homology, left_homology_data.homology_iso,
    left_homology_data.left_homology_iso],
  rw [assoc, ← left_homology_map'_comp, id_comp],
end

@[simp, reassoc]
lemma right_homology_data.homology_iso_hom_comp_right_homology_iso_inv
  (h : S.right_homology_data) [S.has_homology] :
  h.homology_iso.hom ≫ h.right_homology_iso.inv = S.homology_iso_right_homology.hom :=
begin
  dsimp [right_homology_data.homology_iso, homology_iso_right_homology,
    right_homology_data.right_homology_iso],
  rw [← left_homology_map'_comp_iso_hom_comp_right_homology_map'
    S.some_homology_data S.some_homology_data.left h, left_homology_map'_id, id_comp,
    ← left_homology_map'_comp_iso_hom_comp_right_homology_map' S.some_homology_data
    S.some_homology_data.left S.some_right_homology_data, assoc,
    left_homology_map'_id, id_comp, ← right_homology_map'_comp, id_comp],
end

@[simp, reassoc]
lemma right_homology_data.homology_iso_inv_comp_homology_π
  (h : S.right_homology_data) [S.has_homology] :
  h.homology_iso.inv ≫ S.homology_ι = h.ι ≫ h.cycles_co_iso.inv :=
begin
  simp only [← right_homology_data.right_homology_iso_inv_comp_right_homology_ι,
    ← S.right_homology_iso_homology_inv_comp_homology_ι,
    ← cancel_epi h.homology_iso.hom, iso.hom_inv_id_assoc,
    h.homology_iso_hom_comp_right_homology_iso_inv_assoc],
end

@[reassoc]
lemma left_homology_data.π_comp_homology_iso_inv (h : S.left_homology_data) [S.has_homology] :
  h.π ≫ h.homology_iso.inv = h.cycles_iso.inv ≫ S.homology_π :=
by simp only [← cancel_epi h.cycles_iso.hom, ← cancel_mono h.homology_iso.hom, assoc,
  iso.inv_hom_id, comp_id, iso.hom_inv_id_assoc, h.homology_π_comp_homology_iso_hom]

@[reassoc]
lemma right_homology_data.π_comp_homology_iso_inv (h : S.right_homology_data) [S.has_homology] :
  h.homology_iso.hom ≫ h.ι = S.homology_ι ≫ h.cycles_co_iso.hom :=
by simp only [← cancel_mono h.cycles_co_iso.inv, ← cancel_epi h.homology_iso.inv, assoc,
  iso.inv_hom_id_assoc, iso.hom_inv_id, comp_id,
  right_homology_data.homology_iso_inv_comp_homology_π]

@[simp, reassoc]
lemma comp_homology_map_comp [S₁.has_homology] [S₂.has_homology] (φ : S₁ ⟶ S₂)
  (h₁ : S₁.left_homology_data) (h₂ : S₂.right_homology_data) :
  h₁.π ≫ h₁.homology_iso.inv ≫ homology_map φ ≫ h₂.homology_iso.hom ≫ h₂.ι =
    h₁.i ≫ φ.τ₂ ≫ h₂.p :=
begin
  simp only [← cancel_epi h₁.cycles_iso.hom, ← cancel_mono h₂.cycles_co_iso.inv,
    assoc, left_homology_data.cycles_iso_hom_comp_i_assoc,
    right_homology_data.p_comp_cycles_co_iso_inv,
    left_homology_data.π_comp_homology_iso_inv_assoc, iso.hom_inv_id, comp_id,
    right_homology_data.π_comp_homology_iso_inv_assoc, iso.hom_inv_id_assoc],
  dsimp only [homology_π, homology_ι],
  simp only [assoc, left_homology_iso_homology_hom_naturality_assoc φ,
    left_homology_π_naturality_assoc, ← S₂.left_right_homology_comparison_fac_assoc,
    comp_left_right_homology_comparison_comp, cycles_map_i_assoc],
end

lemma π_comp_homology_map_comp_ι [S₁.has_homology] [S₂.has_homology] (φ : S₁ ⟶ S₂) :
  S₁.homology_π ≫ homology_map φ ≫ S₂.homology_ι =
    S₁.cycles_i ≫ φ.τ₂ ≫ S₂.p_cycles_co :=
begin
  dsimp [homology_π, homology_ι],
  simpa only [assoc] using comp_homology_map_comp φ
    S₁.some_left_homology_data S₂.some_right_homology_data,
end

section quasi_iso

variables [has_homology S₁] [has_homology S₂] [has_homology S₃] [has_homology S₄]

@[protected]
def quasi_iso (φ : S₁ ⟶ S₂) := is_iso (homology_map φ)

lemma quasi_iso_of_iso (φ : S₁ ⟶ S₂) [is_iso φ] : quasi_iso φ :=
is_iso.of_iso (homology_map_iso (as_iso φ))

lemma quasi_iso_comp {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃} (h : quasi_iso φ) (h' : quasi_iso φ') :
  quasi_iso (φ ≫ φ') :=
begin
  unfreezingI { dsimp [quasi_iso] at ⊢ h h', },
  rw homology_map_comp,
  apply_instance,
end

lemma quasi_iso_of_comp_left {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃}
  (h : quasi_iso φ) (h' : quasi_iso (φ ≫ φ')) :
  quasi_iso φ' :=
begin
  unfreezingI { dsimp [quasi_iso] at ⊢ h h', },
  rw homology_map_comp at h',
  haveI := h,
  exact is_iso.of_is_iso_comp_left (homology_map φ) (homology_map φ'),
end

lemma quasi_iso_of_comp_right {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃}
  (h : quasi_iso φ') (h' : quasi_iso (φ ≫ φ')) :
  quasi_iso φ :=
begin
  unfreezingI { dsimp [quasi_iso] at ⊢ h h', },
  rw homology_map_comp at h',
  haveI := h',
  exact is_iso.of_is_iso_comp_right (homology_map φ) (homology_map φ'),
end

lemma iff_of_arrow_mk_iso (φ : S₁ ⟶ S₂) (φ' : S₃ ⟶ S₄) (e : arrow.mk φ ≅ arrow.mk φ') :
  quasi_iso φ ↔ quasi_iso φ' :=
begin
  haveI : has_homology (arrow.mk φ).left := (infer_instance : has_homology S₁),
  haveI : has_homology (arrow.mk φ).right := (infer_instance : has_homology S₂),
  haveI : has_homology (arrow.mk φ').left := (infer_instance : has_homology S₃),
  haveI : has_homology (arrow.mk φ').right := (infer_instance : has_homology S₄),
  have w := e.hom.w,
  dsimp at w,
  split,
  { intro hφ,
    replace hφ := quasi_iso_comp hφ (quasi_iso_of_iso e.hom.right),
    rw ← w at hφ,
    exact quasi_iso_of_comp_left (quasi_iso_of_iso e.hom.left) hφ, },
  { intro hφ',
    replace hφ' := quasi_iso_comp (quasi_iso_of_iso e.hom.left) hφ',
    rw w at hφ',
    exact quasi_iso_of_comp_right (quasi_iso_of_iso e.hom.right) hφ', },
end

end quasi_iso

lemma left_homology_map_data.quasi_iso_iff' {φ : S₁ ⟶ S₂} {h₁ h₁' : left_homology_data S₁}
  {h₂ h₂' : left_homology_data S₂} (ψ : left_homology_map_data φ h₁ h₂) (ψ' : left_homology_map_data φ h₁' h₂') :
  is_iso ψ.φH ↔ is_iso ψ'.φH :=
begin
  let e := left_homology_map_iso' (iso.refl S₁) h₁ h₁',
  let e' := left_homology_map_iso' (iso.refl S₂) h₂ h₂',
  have fac₁ : ψ'.φH = e.inv ≫ ψ.φH ≫ e'.hom,
  { dsimp [e, e'],
    rw [← ψ.left_homology_map'_eq, ← ψ'.left_homology_map'_eq, ← left_homology_map'_comp,
      ← left_homology_map'_comp, id_comp, comp_id], },
  have fac₂ : ψ.φH = e.hom ≫ ψ'.φH ≫ e'.inv,
  { simp only [fac₁, assoc, e.hom_inv_id_assoc, e'.hom_inv_id, comp_id], },
  split,
  { introI,
    rw fac₁,
    apply_instance, },
  { introI,
    rw fac₂,
    apply_instance, },
end

lemma left_homology_map_data.quasi_iso_iff {φ : S₁ ⟶ S₂} {h₁ : left_homology_data S₁}
  {h₂ : left_homology_data S₂} (ψ : left_homology_map_data φ h₁ h₂)
  [S₁.has_homology] [S₂.has_homology] :
  quasi_iso φ ↔ is_iso ψ.φH :=
left_homology_map_data.quasi_iso_iff' _ _

lemma homology_map_data.quasi_iso_iff' {φ : S₁ ⟶ S₂} (ψ : homology_map_data φ h₁ h₂) :
  is_iso ψ.left.φH ↔ is_iso ψ.right.φH :=
begin
  have fac₁ : ψ.right.φH = h₁.iso.inv ≫ ψ.left.φH ≫ h₂.iso.hom,
  { simp only [ψ.comm, iso.inv_hom_id_assoc], },
  have fac₂ : ψ.left.φH = h₁.iso.hom ≫ ψ.right.φH ≫ h₂.iso.inv,
  { simp only [← reassoc_of ψ.comm, iso.hom_inv_id, comp_id], },
  split,
  { introI,
    rw fac₁,
    apply_instance, },
  { introI,
    rw fac₂,
    apply_instance, },
end

lemma right_homology_map_data.quasi_iso_iff {φ : S₁ ⟶ S₂} {h₁ : right_homology_data S₁}
  {h₂ : right_homology_data S₂} (ψ : right_homology_map_data φ h₁ h₂)
  [S₁.has_homology] [S₂.has_homology] :
  quasi_iso φ ↔ is_iso ψ.φH :=
begin
  let h₁' := S₁.some_homology_data,
  let h₂' := S₂.some_homology_data,
  let ψ' : left_homology_map_data φ h₁'.left h₂'.left := default,
  let h₁'' := homology_data.of_is_iso_left_right_homology_comparison' h₁'.left h₁,
  let h₂'' := homology_data.of_is_iso_left_right_homology_comparison' h₂'.left h₂,
  let Φ : homology_map_data φ h₁'' h₂'' := ⟨ψ', ψ⟩,
  change is_iso (Φ.left.φH) ↔ is_iso (Φ.right.φH),
  have fac₁ : Φ.right.φH = h₁''.iso.inv ≫ Φ.left.φH ≫ h₂''.iso.hom,
  { rw [Φ.comm, iso.inv_hom_id_assoc], },
  have fac₂ : Φ.left.φH = h₁''.iso.hom ≫ Φ.right.φH ≫ h₂''.iso.inv,
  { rw [← Φ.comm_assoc, iso.hom_inv_id, comp_id], },
  split,
  { introI,
    rw fac₁,
    apply_instance, },
  { introI,
    rw fac₂,
    apply_instance, },
end

variable (S)

def some_homology_data' [S.has_homology] : S.homology_data :=
homology_data.of_is_iso_left_right_homology_comparison'
    S.some_left_homology_data S.some_right_homology_data

instance {D : Type*} [category D] [has_zero_morphisms D] [category_with_homology D] :
  category_with_homology Dᵒᵖ :=
⟨λ S, has_homology.mk' (homology_data.of_iso S.unop_op S.unop.some_homology_data.op)⟩

lemma quasi_iso.of_epi_of_is_iso_of_mono (φ : S₁ ⟶ S₂) [has_homology S₁] [has_homology S₂]
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] : quasi_iso φ :=
begin
  rw (left_homology_map_data.of_epi_of_is_iso_of_mono φ
    S₁.some_left_homology_data).quasi_iso_iff,
  dsimp,
  apply_instance,
end

end short_complex

end category_theory
