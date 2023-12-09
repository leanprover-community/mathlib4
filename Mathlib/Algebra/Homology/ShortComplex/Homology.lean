/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Homology.ShortComplex.RightHomology

/-! Homology of short complexes

In this file, we shall define the homology of short complexes `S`, i.e. diagrams
`f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` such that `f ≫ g = 0`. We shall say that
`[S.HasHomology]` when there exists `h : S.HomologyData`. A homology data
for `S` consists of compatible left/right homology data `left` and `right`. The
left homology data `left` involves an object `left.H` that is a cokernel of the canonical
map `S.X₁ ⟶ K` where `K` is a kernel of `g`. On the other hand, the dual notion `right.H`
is a kernel of the canonical morphism `Q ⟶ S.X₃` when `Q` is a cokernel of `f`.
The compatibility that is required involves an isomorphism `left.H ≅ right.H` which
makes a certain pentagon commute. When such a homology data exists, `S.homology`
shall be defined as `h.left.H` for a chosen `h : S.HomologyData`.

This definition requires very little assumption on the category (only the existence
of zero morphisms). We shall prove that in abelian categories, all short complexes
have homology data.

Note: This definition arose by the end of the Liquid Tensor Experiment which
contained a structure `has_homology` which is quite similar to `S.HomologyData`.
After the category `ShortComplex C` was introduced by J. Riou, A. Topaz suggested
such a structure could be used as a basis for the *definition* of homology.

-/

universe v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

namespace ShortComplex

/-- A homology data for a short complex consists of two compatible left and
right homology data -/
structure HomologyData where
  /-- a left homology data -/
  left : S.LeftHomologyData
  /-- a right homology data -/
  right : S.RightHomologyData
  /-- the compatibility isomorphism relating the two dual notions of
    `LeftHomologyData` and `RightHomologyData`  -/
  iso : left.H ≅ right.H
  /-- the pentagon relation expressing the compatibility of the left
  and right homology data -/
  comm : left.π ≫ iso.hom ≫ right.ι = left.i ≫ right.p := by aesop_cat

attribute [reassoc (attr := simp)] HomologyData.comm

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

/-- A homology map data for a morphism `φ : S₁ ⟶ S₂` where both `S₁` and `S₂` are
equipped with homology data consists of left and right homology map data. -/
structure HomologyMapData where
  /-- a left homology map data -/
  left : LeftHomologyMapData φ h₁.left h₂.left
  /-- a right homology map data -/
  right : RightHomologyMapData φ h₁.right h₂.right

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

/-- A choice of the (unique) homology map data associated with a morphism
`φ : S₁ ⟶ S₂` where both short complexes `S₁` and `S₂` are equipped with
homology data. -/
def homologyMapData : HomologyMapData φ h₁ h₂ := default

variable {φ h₁ h₂}

lemma congr_left_φH {γ₁ γ₂ : HomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) :
  γ₁.left.φH = γ₂.left.φH := by rw [eq]

end HomologyMapData

namespace HomologyData

/-- When the first map `S.f` is zero, this is the homology data on `S` given
by any limit kernel fork of `S.g` -/
@[simps]
def ofIsLimitKernelFork (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c) :
    S.HomologyData where
  left := LeftHomologyData.ofIsLimitKernelFork S hf c hc
  right := RightHomologyData.ofIsLimitKernelFork S hf c hc
  iso := Iso.refl _

/-- When the first map `S.f` is zero, this is the homology data on `S` given
by the chosen `kernel S.g` -/
@[simps]
noncomputable def ofHasKernel (hf : S.f = 0) [HasKernel S.g] :
    S.HomologyData where
  left := LeftHomologyData.ofHasKernel S hf
  right := RightHomologyData.ofHasKernel S hf
  iso := Iso.refl _

/-- When the second map `S.g` is zero, this is the homology data on `S` given
by any colimit cokernel cofork of `S.f` -/
@[simps]
def ofIsColimitCokernelCofork (hg : S.g = 0) (c : CokernelCofork S.f) (hc : IsColimit c) :
    S.HomologyData where
  left := LeftHomologyData.ofIsColimitCokernelCofork S hg c hc
  right := RightHomologyData.ofIsColimitCokernelCofork S hg c hc
  iso := Iso.refl _

/-- When the second map `S.g` is zero, this is the homology data on `S` given by
the chosen `cokernel S.f` -/
@[simps]
noncomputable def ofHasCokernel (hg : S.g = 0) [HasCokernel S.f] :
    S.HomologyData where
  left := LeftHomologyData.ofHasCokernel S hg
  right := RightHomologyData.ofHasCokernel S hg
  iso := Iso.refl _

/-- When both `S.f` and `S.g` are zero, the middle object `S.X₂` gives a homology data on S -/
@[simps]
noncomputable def ofZeros (hf : S.f = 0) (hg : S.g = 0) :
    S.HomologyData where
  left := LeftHomologyData.ofZeros S hf hg
  right := RightHomologyData.ofZeros S hf hg
  iso := Iso.refl _

/-- If `φ : S₁ ⟶ S₂` is a morphism of short complexes such that `φ.τ₁` is epi, `φ.τ₂` is an iso
and `φ.τ₃` is mono, then a homology data for `S₁` induces a homology data for `S₂`.
The inverse construction is `ofEpiOfIsIsoOfMono'`. -/
@[simps]
noncomputable def ofEpiOfIsIsoOfMono (φ : S₁ ⟶ S₂) (h : HomologyData S₁)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HomologyData S₂ where
  left := LeftHomologyData.ofEpiOfIsIsoOfMono φ h.left
  right := RightHomologyData.ofEpiOfIsIsoOfMono φ h.right
  iso := h.iso

/-- If `φ : S₁ ⟶ S₂` is a morphism of short complexes such that `φ.τ₁` is epi, `φ.τ₂` is an iso
and `φ.τ₃` is mono, then a homology data for `S₂` induces a homology data for `S₁`.
The inverse construction is `ofEpiOfIsIsoOfMono`. -/
@[simps]
noncomputable def ofEpiOfIsIsoOfMono' (φ : S₁ ⟶ S₂) (h : HomologyData S₂)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HomologyData S₁ where
  left := LeftHomologyData.ofEpiOfIsIsoOfMono' φ h.left
  right := RightHomologyData.ofEpiOfIsIsoOfMono' φ h.right
  iso := h.iso

/-- If `e : S₁ ≅ S₂` is an isomorphism of short complexes and `h₁ : HomologyData S₁`,
this is the homology data for `S₂` deduced from the isomorphism. -/
@[simps!]
noncomputable def ofIso (e : S₁ ≅ S₂) (h : HomologyData S₁) :=
  h.ofEpiOfIsIsoOfMono e.hom

variable {S}

/-- A homology data for a short complex `S` induces a homology data for `S.op`. -/
@[simps]
def op (h : S.HomologyData) : S.op.HomologyData where
  left := h.right.op
  right := h.left.op
  iso := h.iso.op
  comm := Quiver.Hom.unop_inj (by simp)

/-- A homology data for a short complex `S` in the opposite category
induces a homology data for `S.unop`. -/
@[simps]
def unop {S : ShortComplex Cᵒᵖ} (h : S.HomologyData) : S.unop.HomologyData where
  left := h.right.unop
  right := h.left.unop
  iso := h.iso.unop
  comm := Quiver.Hom.op_inj (by simp)

end HomologyData

/-- A short complex `S` has homology when there exists a `S.HomologyData` -/
class HasHomology : Prop where
  /-- the condition that there exists a homology data -/
  condition : Nonempty S.HomologyData

/-- A chosen `S.HomologyData` for a short complex `S` that has homology -/
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

/-- The homology map data associated to the identity morphism of a short complex. -/
@[simps]
def id (h : S.HomologyData) : HomologyMapData (𝟙 S) h h where
  left := LeftHomologyMapData.id h.left
  right := RightHomologyMapData.id h.right

/-- The homology map data associated to the zero morphism between two short complexes. -/
@[simps]
def zero (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData) :
    HomologyMapData 0 h₁ h₂ where
  left := LeftHomologyMapData.zero h₁.left h₂.left
  right := RightHomologyMapData.zero h₁.right h₂.right

/-- The composition of homology map data. -/
@[simps]
def comp {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃} {h₁ : S₁.HomologyData}
    {h₂ : S₂.HomologyData} {h₃ : S₃.HomologyData}
    (ψ : HomologyMapData φ h₁ h₂) (ψ' : HomologyMapData φ' h₂ h₃) :
    HomologyMapData (φ ≫ φ') h₁ h₃ where
  left := ψ.left.comp ψ'.left
  right := ψ.right.comp ψ'.right

/-- A homology map data for a morphism of short complexes induces
a homology map data in the opposite category. -/
@[simps]
def op {φ : S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}
    (ψ : HomologyMapData φ h₁ h₂) :
    HomologyMapData (opMap φ) h₂.op h₁.op where
  left := ψ.right.op
  right := ψ.left.op

/-- A homology map data for a morphism of short complexes in the opposite category
induces a homology map data in the original category. -/
@[simps]
def unop {S₁ S₂ : ShortComplex Cᵒᵖ} {φ : S₁ ⟶ S₂}
    {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}
    (ψ : HomologyMapData φ h₁ h₂) :
    HomologyMapData (unopMap φ) h₂.unop h₁.unop where
  left := ψ.right.unop
  right := ψ.left.unop

/-- When `S₁.f`, `S₁.g`, `S₂.f` and `S₂.g` are all zero, the action on homology of a
morphism `φ : S₁ ⟶ S₂` is given by the action `φ.τ₂` on the middle objects. -/
@[simps]
def ofZeros (φ : S₁ ⟶ S₂) (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (hg₂ : S₂.g = 0) :
    HomologyMapData φ (HomologyData.ofZeros S₁ hf₁ hg₁) (HomologyData.ofZeros S₂ hf₂ hg₂) where
  left := LeftHomologyMapData.ofZeros φ hf₁ hg₁ hf₂ hg₂
  right := RightHomologyMapData.ofZeros φ hf₁ hg₁ hf₂ hg₂

/-- When `S₁.g` and `S₂.g` are zero and we have chosen colimit cokernel coforks `c₁` and `c₂`
for `S₁.f` and `S₂.f` respectively, the action on homology of a morphism `φ : S₁ ⟶ S₂` of
short complexes is given by the unique morphism `f : c₁.pt ⟶ c₂.pt` such that
`φ.τ₂ ≫ c₂.π = c₁.π ≫ f`. -/
@[simps]
def ofIsColimitCokernelCofork (φ : S₁ ⟶ S₂)
    (hg₁ : S₁.g = 0) (c₁ : CokernelCofork S₁.f) (hc₁ : IsColimit c₁)
    (hg₂ : S₂.g = 0) (c₂ : CokernelCofork S₂.f) (hc₂ : IsColimit c₂) (f : c₁.pt ⟶ c₂.pt)
    (comm : φ.τ₂ ≫ c₂.π = c₁.π ≫ f) :
    HomologyMapData φ (HomologyData.ofIsColimitCokernelCofork S₁ hg₁ c₁ hc₁)
      (HomologyData.ofIsColimitCokernelCofork S₂ hg₂ c₂ hc₂) where
  left := LeftHomologyMapData.ofIsColimitCokernelCofork φ hg₁ c₁ hc₁ hg₂ c₂ hc₂ f comm
  right := RightHomologyMapData.ofIsColimitCokernelCofork φ hg₁ c₁ hc₁ hg₂ c₂ hc₂ f comm

/-- When `S₁.f` and `S₂.f` are zero and we have chosen limit kernel forks `c₁` and `c₂`
for `S₁.g` and `S₂.g` respectively, the action on homology of a morphism `φ : S₁ ⟶ S₂` of
short complexes is given by the unique morphism `f : c₁.pt ⟶ c₂.pt` such that
`c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι`. -/
@[simps]
def ofIsLimitKernelFork (φ : S₁ ⟶ S₂)
    (hf₁ : S₁.f = 0) (c₁ : KernelFork S₁.g) (hc₁ : IsLimit c₁)
    (hf₂ : S₂.f = 0) (c₂ : KernelFork S₂.g) (hc₂ : IsLimit c₂) (f : c₁.pt ⟶ c₂.pt)
    (comm : c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι) :
    HomologyMapData φ (HomologyData.ofIsLimitKernelFork S₁ hf₁ c₁ hc₁)
      (HomologyData.ofIsLimitKernelFork S₂ hf₂ c₂ hc₂) where
  left := LeftHomologyMapData.ofIsLimitKernelFork φ hf₁ c₁ hc₁ hf₂ c₂ hc₂ f comm
  right := RightHomologyMapData.ofIsLimitKernelFork φ hf₁ c₁ hc₁ hf₂ c₂ hc₂ f comm

/-- When both maps `S.f` and `S.g` of a short complex `S` are zero, this is the homology map
data (for the identity of `S`) which relates the homology data `ofZeros` and
`ofIsColimitCokernelCofork`. -/
def compatibilityOfZerosOfIsColimitCokernelCofork (hf : S.f = 0) (hg : S.g = 0)
    (c : CokernelCofork S.f) (hc : IsColimit c) :
    HomologyMapData (𝟙 S) (HomologyData.ofZeros S hf hg)
      (HomologyData.ofIsColimitCokernelCofork S hg c hc) where
  left := LeftHomologyMapData.compatibilityOfZerosOfIsColimitCokernelCofork S hf hg c hc
  right := RightHomologyMapData.compatibilityOfZerosOfIsColimitCokernelCofork S hf hg c hc

/-- When both maps `S.f` and `S.g` of a short complex `S` are zero, this is the homology map
data (for the identity of `S`) which relates the homology data
`HomologyData.ofIsLimitKernelFork` and `ofZeros` . -/
@[simps]
def compatibilityOfZerosOfIsLimitKernelFork (hf : S.f = 0) (hg : S.g = 0)
    (c : KernelFork S.g) (hc : IsLimit c) :
    HomologyMapData (𝟙 S)
      (HomologyData.ofIsLimitKernelFork S hf c hc)
      (HomologyData.ofZeros S hf hg) where
  left := LeftHomologyMapData.compatibilityOfZerosOfIsLimitKernelFork S hf hg c hc
  right := RightHomologyMapData.compatibilityOfZerosOfIsLimitKernelFork S hf hg c hc

/-- This homology map data expresses compatibilities of the homology data
constructed by `HomologyData.ofEpiOfIsIsoOfMono` -/
noncomputable def ofEpiOfIsIsoOfMono (φ : S₁ ⟶ S₂) (h : HomologyData S₁)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    HomologyMapData φ h (HomologyData.ofEpiOfIsIsoOfMono φ h) where
  left := LeftHomologyMapData.ofEpiOfIsIsoOfMono φ h.left
  right := RightHomologyMapData.ofEpiOfIsIsoOfMono φ h.right

/-- This homology map data expresses compatibilities of the homology data
constructed by `HomologyData.ofEpiOfIsIsoOfMono'` -/
noncomputable def ofEpiOfIsIsoOfMono' (φ : S₁ ⟶ S₂) (h : HomologyData S₂)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    HomologyMapData φ (HomologyData.ofEpiOfIsIsoOfMono' φ h) h where
  left := LeftHomologyMapData.ofEpiOfIsIsoOfMono' φ h.left
  right := RightHomologyMapData.ofEpiOfIsIsoOfMono' φ h.right

end HomologyMapData

variable (S)

/-- The homology of a short complex is the `left.H` field of a chosen homology data. -/
noncomputable def homology [HasHomology S] : C := S.homologyData.left.H

/-- When a short complex has homology, this is the canonical isomorphism
`S.leftHomology ≅ S.homology`. -/
noncomputable def leftHomologyIso [S.HasHomology] : S.leftHomology ≅ S.homology :=
  leftHomologyMapIso' (Iso.refl _) _ _

/-- When a short complex has homology, this is the canonical isomorphism
`S.rightHomology ≅ S.homology`. -/
noncomputable def rightHomologyIso [S.HasHomology] : S.rightHomology ≅ S.homology :=
  rightHomologyMapIso' (Iso.refl _) _ _ ≪≫ S.homologyData.iso.symm

variable {S}

/-- When a short complex has homology, its homology can be computed using
any left homology data. -/
noncomputable def LeftHomologyData.homologyIso (h : S.LeftHomologyData) [S.HasHomology] :
    S.homology ≅ h.H := S.leftHomologyIso.symm ≪≫ h.leftHomologyIso

/-- When a short complex has homology, its homology can be computed using
any right homology data. -/
noncomputable def RightHomologyData.homologyIso (h : S.RightHomologyData) [S.HasHomology] :
    S.homology ≅ h.H := S.rightHomologyIso.symm ≪≫ h.rightHomologyIso

end ShortComplex

end CategoryTheory
