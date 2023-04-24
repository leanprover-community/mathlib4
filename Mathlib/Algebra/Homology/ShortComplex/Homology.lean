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

noncomputable def ofEpiOfIsIsoOfMono (φ : S₁ ⟶ S₂) (h : HomologyData S₁)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    HomologyMapData φ h (HomologyData.ofEpiOfIsIsoOfMono φ h) where
  left := LeftHomologyMapData.ofEpiOfIsIsoOfMono φ h.left
  right := RightHomologyMapData.ofEpiOfIsIsoOfMono φ h.right

noncomputable def ofEpiOfIsIsoOfMono' (φ : S₁ ⟶ S₂) (h : HomologyData S₂)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    HomologyMapData φ (HomologyData.ofEpiOfIsIsoOfMono' φ h) h where
  left := LeftHomologyMapData.ofEpiOfIsIsoOfMono' φ h.left
  right := RightHomologyMapData.ofEpiOfIsIsoOfMono' φ h.right

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

variable (S)

@[simp]
lemma LeftHomologyData.homologyIso_leftHomologyData [S.HasHomology] :
    S.leftHomologyData.homologyIso = S.leftHomologyIso.symm := by
  ext
  dsimp only [homologyIso, Iso.symm, Iso.trans, leftHomologyIso, ShortComplex.leftHomologyIso,
    Iso.refl, leftHomologyMapIso']
  rw [← leftHomologyMap'_comp, comp_id]

@[simp]
lemma RightHomologyData.homologyIso_rightHomologyData [S.HasHomology] :
    S.rightHomologyData.homologyIso = S.rightHomologyIso.symm := by
  ext
  dsimp only [homologyIso, Iso.symm, Iso.trans, Iso.refl, ShortComplex.rightHomologyIso,
    rightHomologyMapIso', rightHomologyIso]
  erw [rightHomologyMap'_id, comp_id]

variable {S}

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

lemma leftRightHomologyComparison'_eq_leftHomologpMap'_comp_iso_hom_comp_rightHomology_map'
    (h : S.HomologyData) (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    leftRightHomologyComparison' h₁ h₂ =
      leftHomologyMap' (𝟙 S) h₁ h.left ≫ h.iso.hom ≫ rightHomologyMap' (𝟙 S) h.right h₂ := by
  simpa only [h.leftRightHomologyComparison'_eq] using leftRightHomologyComparison'_compatibility h₁ h.left h₂ h.right

@[reassoc]
lemma leftRightHomologyComparison'_fac (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
    [S.HasHomology] :
    leftRightHomologyComparison' h₁ h₂ = h₁.homologyIso.inv ≫ h₂.homologyIso.hom := by
  rw [leftRightHomologyComparison'_eq_leftHomologpMap'_comp_iso_hom_comp_rightHomology_map'
    S.homologyData h₁ h₂]
  dsimp only [LeftHomologyData.homologyIso, LeftHomologyData.leftHomologyIso,
    Iso.symm, Iso.trans, Iso.refl, leftHomologyMapIso', leftHomologyIso,
    RightHomologyData.homologyIso, RightHomologyData.rightHomologyIso,
    rightHomologyMapIso', rightHomologyIso]
  simp only [assoc, ← leftHomologyMap'_comp_assoc, id_comp, ← rightHomologyMap'_comp]

variable (S)

@[reassoc]
lemma leftRightHomologyComparison_fac [S.HasHomology] :
    S.leftRightHomologyComparison = S.leftHomologyIso.hom ≫ S.rightHomologyIso.inv := by
  simpa only [LeftHomologyData.homologyIso_leftHomologyData, Iso.symm_inv,
    RightHomologyData.homologyIso_rightHomologyData, Iso.symm_hom] using
      leftRightHomologyComparison'_fac S.leftHomologyData S.rightHomologyData

variable {S}

lemma hasHomology_of_isIso_leftRightHomologyComparison'
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
    [IsIso (leftRightHomologyComparison' h₁ h₂)] :
    S.HasHomology :=
  HasHomology.mk' (HomologyData.ofIsIsoLeftRightHomologyComparison' h₁ h₂)

lemma hasHomology_of_isIsoLeftRightHomologyComparison [S.HasLeftHomology]
    [S.HasRightHomology] [h : IsIso S.leftRightHomologyComparison] :
    S.HasHomology := by
  haveI : IsIso (leftRightHomologyComparison' S.leftHomologyData S.rightHomologyData) := h
  exact hasHomology_of_isIso_leftRightHomologyComparison' S.leftHomologyData S.rightHomologyData

@[reassoc]
lemma LeftHomologyData.leftHomologyIso_hom_naturality [S₁.HasHomology] [S₂.HasHomology]
    (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    h₁.homologyIso.hom ≫ leftHomologyMap' φ h₁ h₂ =
      homologyMap φ ≫ h₂.homologyIso.hom := by
  dsimp [homologyIso, ShortComplex.leftHomologyIso, homologyMap, homologyMap', leftHomologyIso]
  simp only [← leftHomologyMap'_comp, id_comp, comp_id]

@[reassoc]
lemma LeftHomologyData.leftHomologyIso_inv_naturality [S₁.HasHomology] [S₂.HasHomology]
    (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
      h₁.homologyIso.inv ≫ homologyMap φ =
       leftHomologyMap' φ h₁ h₂ ≫ h₂.homologyIso.inv := by
  dsimp [homologyIso, ShortComplex.leftHomologyIso, homologyMap, homologyMap', leftHomologyIso]
  simp only [← leftHomologyMap'_comp, id_comp, comp_id]

@[reassoc]
lemma leftHomologyIso_hom_naturality [S₁.HasHomology] [S₂.HasHomology] (φ : S₁ ⟶ S₂) :
    S₁.leftHomologyIso.hom ≫ homologyMap φ =
      leftHomologyMap φ ≫ S₂.leftHomologyIso.hom := by
  simpa only [LeftHomologyData.homologyIso_leftHomologyData, Iso.symm_inv] using
    LeftHomologyData.leftHomologyIso_inv_naturality φ S₁.leftHomologyData S₂.leftHomologyData

@[reassoc]
lemma leftHomologyIso_inv_naturality [S₁.HasHomology] [S₂.HasHomology] (φ : S₁ ⟶ S₂) :
    S₁.leftHomologyIso.inv ≫ leftHomologyMap φ =
      homologyMap φ ≫ S₂.leftHomologyIso.inv := by
  simpa only [LeftHomologyData.homologyIso_leftHomologyData, Iso.symm_inv] using
    LeftHomologyData.leftHomologyIso_hom_naturality φ S₁.leftHomologyData S₂.leftHomologyData

@[reassoc]
lemma RightHomologyData.rightHomologyIso_hom_naturality [S₁.HasHomology] [S₂.HasHomology]
    (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    h₁.homologyIso.hom ≫ rightHomologyMap' φ h₁ h₂ =
      homologyMap φ ≫ h₂.homologyIso.hom := by
  rw [← cancel_epi h₁.homologyIso.inv, Iso.inv_hom_id_assoc,
    ← cancel_epi (leftRightHomologyComparison' S₁.leftHomologyData h₁),
    ← leftRightHomologyComparison'_naturality φ S₁.leftHomologyData h₁ S₂.leftHomologyData h₂,
    ← cancel_epi (S₁.leftHomologyData.homologyIso.hom),
    LeftHomologyData.leftHomologyIso_hom_naturality_assoc,
    leftRightHomologyComparison'_fac, leftRightHomologyComparison'_fac, assoc,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]

@[reassoc]
lemma RightHomologyData.rightHomologyIso_inv_naturality [S₁.HasHomology] [S₂.HasHomology]
    (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
      h₁.homologyIso.inv ≫ homologyMap φ =
        rightHomologyMap' φ h₁ h₂ ≫ h₂.homologyIso.inv := by
  simp only [← cancel_mono h₂.homologyIso.hom, assoc,
    ← RightHomologyData.rightHomologyIso_hom_naturality φ h₁ h₂, Iso.inv_hom_id,
    Iso.inv_hom_id_assoc, comp_id]

@[reassoc]
lemma rightHomologyIso_hom_naturality [S₁.HasHomology] [S₂.HasHomology] (φ : S₁ ⟶ S₂) :
    S₁.rightHomologyIso.hom ≫ homologyMap φ =
      rightHomologyMap φ ≫ S₂.rightHomologyIso.hom := by
  simpa only [RightHomologyData.homologyIso_rightHomologyData, Iso.symm_inv] using
    RightHomologyData.rightHomologyIso_inv_naturality φ S₁.rightHomologyData S₂.rightHomologyData

@[reassoc]
lemma rightHomologyIso_inv_naturality [S₁.HasHomology] [S₂.HasHomology] (φ : S₁ ⟶ S₂) :
    S₁.rightHomologyIso.inv ≫ rightHomologyMap φ =
      homologyMap φ ≫ S₂.rightHomologyIso.inv := by
  simpa only [RightHomologyData.homologyIso_rightHomologyData, Iso.symm_inv] using
    RightHomologyData.rightHomologyIso_hom_naturality φ S₁.rightHomologyData S₂.rightHomologyData

variable (C)

class _root_.CategoryTheory.CategoryWithHomology : Prop where
  hasHomology : ∀ (S : ShortComplex C), S.HasHomology

attribute [instance] CategoryWithHomology.hasHomology

@[simps]
noncomputable def homologyFunctor [CategoryWithHomology C] :
    ShortComplex C ⥤ C where
  obj S := S.homology
  map f := homologyMap f

instance isIso_homologyMap'_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂)
    (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso (homologyMap' φ h₁ h₂) := by
  dsimp only [homologyMap']
  infer_instance

instance isIso_homologyMap_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso (homologyMap φ) := by
  dsimp only [homologyMap]
  infer_instance

instance isIso_homologyFunctor_map_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [CategoryWithHomology C]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso ((homologyFunctor C).map φ) :=
  (inferInstance : IsIso (homologyMap φ))

instance isIso_homologyMap_of_isIso (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology] [IsIso φ] :
    IsIso (homologyMap φ) := by
  dsimp only [homologyMap, homologyMap']
  infer_instance

section

variable {C} (S) {A : C}
variable [HasHomology S]

noncomputable def homologyπ : S.cycles ⟶ S.homology :=
  S.leftHomologyπ ≫ S.leftHomologyIso.hom

noncomputable def homologyι : S.homology ⟶ S.cyclesCo :=
  S.rightHomologyIso.inv ≫ S.rightHomologyι

@[simp, reassoc]
lemma homologyπ_comp_leftHomologyIso_inv:
    S.homologyπ ≫ S.leftHomologyIso.inv = S.leftHomologyπ := by
  dsimp only [homologyπ]
  simp only [assoc, Iso.hom_inv_id, comp_id]

@[simp, reassoc]
lemma rightHomologyIso_hom_comp_homologyι :
    S.rightHomologyIso.hom ≫ S.homologyι = S.rightHomologyι := by
  dsimp only [homologyι]
  simp only [Iso.hom_inv_id_assoc]

@[simp, reassoc]
lemma toCycles_comp_homologyπ :
    S.toCycles ≫ S.homologyπ = 0 := by
  dsimp only [homologyπ]
  simp only [toCycles_comp_leftHomology_π_assoc, zero_comp]

@[simp, reassoc]
lemma homologyι_comp_fromCyclesCo :
    S.homologyι ≫ S.fromCyclesCo = 0 := by
  dsimp only [homologyι]
  simp only [assoc, rightHomologyι_comp_fromCyclesCo, comp_zero]

noncomputable def homologyIsCokernel :
  IsColimit (CokernelCofork.ofπ S.homologyπ S.toCycles_comp_homologyπ) :=
IsColimit.ofIsoColimit S.leftHomologyIsCokernel
  (Cofork.ext S.leftHomologyIso rfl)

noncomputable def homologyIsKernel :
  IsLimit (KernelFork.ofι S.homologyι S.homologyι_comp_fromCyclesCo) :=
IsLimit.ofIsoLimit S.rightHomologyIsKernel
  (Fork.ext S.rightHomologyIso (by simp))

instance : Epi S.homologyπ :=
  Limits.epi_of_isColimit_cofork (S.homologyIsCokernel)

instance : Mono S.homologyι :=
  Limits.mono_of_isLimit_fork (S.homologyIsKernel)

noncomputable def descHomology (k : S.cycles ⟶ A) (hk : S.toCycles ≫ k = 0) :
    S.homology ⟶ A :=
  S.homologyIsCokernel.desc (CokernelCofork.ofπ k hk)

noncomputable def liftHomology (k : A ⟶ S.cyclesCo) (hk : k ≫ S.fromCyclesCo = 0) :
    A ⟶ S.homology :=
  S.homologyIsKernel.lift (KernelFork.ofι k hk)

@[simp, reassoc]
lemma π_descHomology (k : S.cycles ⟶ A) (hk : S.toCycles ≫ k = 0) :
  S.homologyπ ≫ S.descHomology k hk = k :=
Cofork.IsColimit.π_desc S.homologyIsCokernel

@[simp, reassoc]
lemma liftHomology_ι (k : A ⟶ S.cyclesCo) (hk : k ≫ S.fromCyclesCo = 0) :
  S.liftHomology k hk ≫ S.homologyι = k :=
  Fork.IsLimit.lift_ι S.homologyIsKernel

@[simp, reassoc]
lemma homologyπ_naturality (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology] :
    S₁.homologyπ ≫ homologyMap φ = cyclesMap φ ≫ S₂.homologyπ := by
  simp only [← cancel_mono S₂.leftHomologyIso.inv, assoc, ← leftHomologyIso_inv_naturality φ,
    homologyπ_comp_leftHomologyIso_inv, ← leftHomologyπ_naturality]
  simp only [homologyπ, assoc, Iso.hom_inv_id_assoc, leftHomologyπ_naturality]

@[simp, reassoc]
lemma homologyι_naturality (φ : S₁ ⟶ S₂) [S₁.HasHomology] [S₂.HasHomology] :
    homologyMap φ ≫ S₂.homologyι = S₁.homologyι ≫ S₁.cyclesCoMap φ  := by
  simp only [← cancel_epi S₁.rightHomologyIso.hom, rightHomologyIso_hom_naturality_assoc φ,
    rightHomologyIso_hom_comp_homologyι, rightHomologyι_naturality]
  simp only [homologyι, assoc, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
lemma homology_π_ι :
    S.homologyπ ≫ S.homologyι = S.iCycles ≫ S.pCyclesCo := by
  dsimp only [homologyπ, homologyι]
  simpa only [assoc, S.leftRightHomologyComparison_fac] using S.π_leftRightHomologyComparison_ι


end

end ShortComplex

end CategoryTheory

#exit

--namespace left_homology_data
--
--lemma ext_iff {A : C} (h : S.left_homology_data) [S.has_homology] (f₁ f₂ : S.homology ⟶ A) :
--  f₁ = f₂ ↔ h.π ≫ h.homology_iso.inv ≫ f₁ = h.π ≫ h.homology_iso.inv ≫ f₂ :=
--by rw [← cancel_epi h.homology_iso.inv, cancel_epi h.π]
--
--end left_homology_data
--
--namespace right_homology_data
--
--lemma ext_iff {A : C} (h : S.right_homology_data) [S.has_homology] (f₁ f₂ : A ⟶ S.homology) :
--  f₁ = f₂ ↔ f₁ ≫ h.homology_iso.hom ≫ h.ι = f₂ ≫ h.homology_iso.hom ≫ h.ι :=
--by simp only [← cancel_mono h.homology_iso.hom, ← cancel_mono h.ι, assoc]
--
--end right_homology_data

namespace homology_data

end homology_data



section

/- dualise the above -/


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
