/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Homology.ShortComplex.LeftHomology
import Mathlib.CategoryTheory.Limits.Opposites

/-! RightHomology of short complexes

In this file, we define the dual notions to those defined in
`Algebra.Homology.ShortComplex.LeftHomology`. In particular, if `S : ShortComplex C` is
a short complex consisting of two composable maps `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` such
that `f ≫ g = 0`, we define `h : S.RightHomologyData` to be the datum of morphisms
`p : X₂ ⟶ Q` and `ι : H ⟶ Q` such that `Q` identifies to the cokernel of `f` and `H`
to the kernel of the induced map `g' : Q ⟶ X₃`.

When such a `S.RightHomologyData` exists, we shall say that `[S.HasRightHomology]`
and (TODO) we define `S.rightHomology` to be the `H` field of a chosen right homology data.
Similarly, we define `S.opcycles` to be the `Q` field.

In `Homology.lean`, when `S` has two compatible left and right homology data
(i.e. they give the same `H` up to a canonical isomorphism), we shall define
`[S.HasHomology]` and `S.homology` (TODO).

-/

namespace CategoryTheory

open Category Limits

namespace ShortComplex

variable {C : Type _} [Category C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

/-- A right homology data for a short complex `S` consists of morphisms `p : S.X₂ ⟶ Q` and
`ι : H ⟶ Q` such that `p` identifies `Q` to the kernel of `f : S.X₁ ⟶ S.X₂`,
and that `ι` identifies `H` to the kernel of the induced map `g' : Q ⟶ S.X₃` --/
structure RightHomologyData where
  /-- a choice of cokernel of `S.f : S.X₁ ⟶ S.X₂`-/
  Q : C
  /-- a choice of kernel of the induced morphism `S.g' : S.Q ⟶ X₃`-/
  H : C
  /-- the projection from `S.X₂` -/
  p : S.X₂ ⟶ Q
  /-- the inclusion of the (right) homology in the chosen cokernel of `S.f` -/
  ι : H ⟶ Q
  /-- the cokernel condition for `p` -/
  wp : S.f ≫ p = 0
  /-- `p : S.X₂ ⟶ Q` is a cokernel of `S.f : S.X₁ ⟶ S.X₂` -/
  hp : IsColimit (CokernelCofork.ofπ p wp)
  /-- the kernel condition for `ι` -/
  wι : ι ≫ hp.desc (CokernelCofork.ofπ _ S.zero) = 0
  /-- `ι : H ⟶ Q` is a kernel of `S.g' : Q ⟶ S.X₃` -/
  hι : IsLimit (KernelFork.ofι ι wι)

initialize_simps_projections RightHomologyData (-hp, -hι)

namespace RightHomologyData

/-- The chosen cokernels and kernels of the limits API give a `RightHomologyData` -/
@[simps]
noncomputable def ofHasCokernelOfHasKernel
    [HasCokernel S.f] [HasKernel (cokernel.desc S.f S.g S.zero)] :
    S.RightHomologyData :=
{ Q := cokernel S.f,
  H := kernel (cokernel.desc S.f S.g S.zero),
  p := cokernel.π _,
  ι := kernel.ι _,
  wp := cokernel.condition _,
  hp := cokernelIsCokernel _,
  wι := kernel.condition _,
  hι := kernelIsKernel _, }

attribute [reassoc (attr := simp)] wp wι

variable {S}
variable (h : S.RightHomologyData) {A : C}

instance : Epi h.p := ⟨fun _ _ => Cofork.IsColimit.hom_ext h.hp⟩

instance : Mono h.ι := ⟨fun _ _ => Fork.IsLimit.hom_ext h.hι⟩

/-- Any morphism `k : S.X₂ ⟶ A` such that `S.f ≫ k = 0` descends
to a morphism `Q ⟶ A` -/
def descQ (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) : h.Q ⟶ A :=
  h.hp.desc (CokernelCofork.ofπ k hk)

@[reassoc (attr := simp)]
lemma p_descQ (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) :
  h.p ≫ h.descQ k hk = k :=
  h.hp.fac _ WalkingParallelPair.one

/-- The morphism from the (right) homology attached to a morphism
`k : S.X₂ ⟶ A` such that `S.f ≫ k = 0`. -/
@[simp]
def descH (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) : h.H ⟶ A :=
  h.ι ≫ h.descQ k hk

/-- The morphism `h.Q ⟶ S.X₃` induced by `S.g : S.X₂ ⟶ S.X₃` and the fact that
`h.Q` is a cokernel of `S.f : S.X₁ ⟶ S.X₂`. -/
def g' : h.Q ⟶ S.X₃ := h.descQ S.g S.zero

@[reassoc (attr := simp)] lemma p_g' : h.p ≫ h.g' = S.g := p_descQ _ _ _

@[reassoc (attr := simp)] lemma ι_g' : h.ι ≫ h.g' = 0 := h.wι

@[reassoc]
lemma ι_descQ_eq_zero_of_boundary (k : S.X₂ ⟶ A) (x : S.X₃ ⟶ A) (hx : k = S.g ≫ x) :
    h.ι ≫ h.descQ k (by rw [hx, S.zero_assoc, zero_comp]) = 0 := by
  rw [show 0 = h.ι ≫ h.g' ≫ x by simp]
  congr 1
  simp only [← cancel_epi h.p, hx, p_descQ, p_g'_assoc]

/-- For `h : S.RightHomologyData`, this is a restatement of `h.hι `, saying that
`ι : h.H ⟶ h.Q` is a kernel of `h.g' : h.Q ⟶ S.X₃`. -/
def hι' : IsLimit (KernelFork.ofι h.ι h.ι_g') := h.hι

/-- The morphism `A ⟶ H` induced by a morphism `k : A ⟶ Q` such that `k ≫ g' = 0` -/
def liftH (k : A ⟶ h.Q) (hk : k ≫ h.g' = 0) : A ⟶ h.H :=
  h.hι.lift (KernelFork.ofι k hk)

@[reassoc (attr := simp)]
lemma liftH_ι (k : A ⟶ h.Q) (hk : k ≫ h.g' = 0) : h.liftH k hk ≫ h.ι = k :=
  h.hι.fac (KernelFork.ofι k hk) WalkingParallelPair.zero

lemma isIso_p (hf : S.f = 0) : IsIso h.p :=
  ⟨h.descQ (𝟙 S.X₂) (by rw [hf, comp_id]), p_descQ _ _ _, by
    simp only [← cancel_epi h.p, p_descQ_assoc, id_comp, comp_id]⟩

lemma isIso_ι (hg : S.g = 0) : IsIso h.ι := by
  have ⟨φ, hφ⟩ := KernelFork.IsLimit.lift' h.hι' (𝟙 _)
    (by rw [← cancel_epi h.p, id_comp, p_g', comp_zero, hg])
  dsimp at hφ
  exact ⟨φ, by rw [← cancel_mono h.ι, assoc, hφ, comp_id, id_comp], hφ⟩

variable (S)

/-- When the first map `S.f` is zero, this is the right homology data on `S` given
by any limit kernel fork of `S.g` -/
@[simps]
def ofIsLimitKernelFork (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c) :
  S.RightHomologyData where
  Q := S.X₂
  H := c.pt
  p := 𝟙 _
  ι := c.ι
  wp := by rw [comp_id, hf]
  hp := CokernelCofork.IsColimit.ofId _ hf
  wι := KernelFork.condition _
  hι := IsLimit.ofIsoLimit hc (Fork.ext (Iso.refl _) (by aesop_cat))

@[simp] lemma ofIsLimitKernelFork_g' (hf : S.f = 0) (c : KernelFork S.g)
    (hc : IsLimit c) : (ofIsLimitKernelFork S hf c hc).g' = S.g := by
  rw [← cancel_epi (ofIsLimitKernelFork S hf c hc).p, p_g',
    ofIsLimitKernelFork_p, id_comp]

/-- When the first map `S.f` is zero, this is the right homology data on `S` given by
the chosen `kernel S.g` -/
@[simps!]
noncomputable def ofHasKernel [HasKernel S.g] (hf : S.f = 0) : S.RightHomologyData :=
ofIsLimitKernelFork S hf _ (kernelIsKernel _)

/-- When the second map `S.g` is zero, this is the right homology data on `S` given
by any colimit cokernel cofork of `S.g` -/
@[simps]
def ofIsColimitCokernelCofork (hg : S.g = 0) (c : CokernelCofork S.f) (hc : IsColimit c) :
  S.RightHomologyData where
  Q := c.pt
  H := c.pt
  p := c.π
  ι := 𝟙 _
  wp := CokernelCofork.condition _
  hp := IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _) (by aesop_cat))
  wι := Cofork.IsColimit.hom_ext hc (by simp [hg])
  hι := KernelFork.IsLimit.ofId _ (Cofork.IsColimit.hom_ext hc (by simp [hg]))

@[simp] lemma ofIsColimitCokernelCofork_g' (hg : S.g = 0) (c : CokernelCofork S.f)
  (hc : IsColimit c) : (ofIsColimitCokernelCofork S hg c hc).g' = 0 :=
by rw [← cancel_epi (ofIsColimitCokernelCofork S hg c hc).p, p_g', hg, comp_zero]

/-- When the second map `S.g` is zero, this is the right homology data on `S` given
by the chosen `cokernel S.f` -/
@[simp]
noncomputable def ofHasCokernel [HasCokernel S.f] (hg : S.g = 0) : S.RightHomologyData :=
ofIsColimitCokernelCofork S hg _ (cokernelIsCokernel _)

/-- When both `S.f` and `S.g` are zero, the middle object `S.X₂`
gives a right homology data on S -/
@[simps]
def ofZeros (hf : S.f = 0) (hg : S.g = 0) : S.RightHomologyData where
  Q := S.X₂
  H := S.X₂
  p := 𝟙 _
  ι := 𝟙 _
  wp := by rw [comp_id, hf]
  hp := CokernelCofork.IsColimit.ofId _ hf
  wι := by
    change 𝟙 _ ≫ S.g = 0
    simp only [hg, comp_zero]
  hι := KernelFork.IsLimit.ofId _ hg

@[simp]
lemma ofZeros_g' (hf : S.f = 0) (hg : S.g = 0) :
    (ofZeros S hf hg).g' = 0 := by
  rw [← cancel_epi ((ofZeros S hf hg).p), comp_zero, p_g', hg]

end RightHomologyData

/-- A short complex `S` has right homology when there exists a `S.RightHomologyData` -/
class HasRightHomology : Prop where
  condition : Nonempty S.RightHomologyData

/-- A chosen `S.RightHomologyData` for a short complex `S` that has right homology -/
noncomputable def rightHomologyData [HasRightHomology S] :
  S.RightHomologyData := HasRightHomology.condition.some

variable {S}

namespace HasRightHomology

lemma mk' (h : S.RightHomologyData) : HasRightHomology S := ⟨Nonempty.intro h⟩

instance of_hasCokernel_of_hasKernel
    [HasCokernel S.f] [HasKernel (cokernel.desc S.f S.g S.zero)] :
  S.HasRightHomology := HasRightHomology.mk' (RightHomologyData.ofHasCokernelOfHasKernel S)

instance of_hasKernel {Y Z : C} (g : Y ⟶ Z) (X : C) [HasKernel g] :
    (ShortComplex.mk (0 : X ⟶ Y) g zero_comp).HasRightHomology :=
  HasRightHomology.mk' (RightHomologyData.ofHasKernel _ rfl)

instance of_hasCokernel {X Y : C} (f : X ⟶ Y) (Z : C) [HasCokernel f] :
    (ShortComplex.mk f (0 : Y ⟶ Z) comp_zero).HasRightHomology :=
  HasRightHomology.mk' (RightHomologyData.ofHasCokernel _ rfl)

instance of_zeros (X Y Z : C) :
    (ShortComplex.mk (0 : X ⟶ Y) (0 : Y ⟶ Z) zero_comp).HasRightHomology :=
  HasRightHomology.mk' (RightHomologyData.ofZeros _ rfl rfl)

end HasRightHomology

namespace RightHomologyData

/-- A right homology data for a short complex `S` induces a left homology data for `S.op`. -/
@[simps]
def op (h : S.RightHomologyData) : S.op.LeftHomologyData where
  K := Opposite.op h.Q
  H := Opposite.op h.H
  i := h.p.op
  π := h.ι.op
  wi := Quiver.Hom.unop_inj h.wp
  hi := CokernelCofork.IsColimit.ofπOp _ _ h.hp
  wπ := Quiver.Hom.unop_inj h.wι
  hπ := KernelFork.IsLimit.ofιOp _ _ h.hι

@[simp] lemma op_f' (h : S.RightHomologyData) :
    h.op.f' = h.g'.op := rfl

/-- A right homology data for a short complex `S` in the opposite category
induces a left homology data for `S.unop`. -/
@[simps]
def unop {S : ShortComplex Cᵒᵖ} (h : S.RightHomologyData) : S.unop.LeftHomologyData where
  K := Opposite.unop h.Q
  H := Opposite.unop h.H
  i := h.p.unop
  π := h.ι.unop
  wi := Quiver.Hom.op_inj h.wp
  hi := CokernelCofork.IsColimit.ofπUnop _ _ h.hp
  wπ := Quiver.Hom.op_inj h.wι
  hπ := KernelFork.IsLimit.ofιUnop _ _ h.hι

@[simp] lemma unop_f' {S : ShortComplex Cᵒᵖ} (h : S.RightHomologyData) :
    h.unop.f' = h.g'.unop := rfl

end RightHomologyData

namespace LeftHomologyData

/-- A left homology data for a short complex `S` induces a right homology data for `S.op`. -/
@[simps]
def op (h : S.LeftHomologyData) : S.op.RightHomologyData where
  Q := Opposite.op h.K
  H := Opposite.op h.H
  p := h.i.op
  ι := h.π.op
  wp := Quiver.Hom.unop_inj h.wi
  hp := KernelFork.IsLimit.ofιOp _ _ h.hi
  wι := Quiver.Hom.unop_inj h.wπ
  hι := CokernelCofork.IsColimit.ofπOp _ _ h.hπ

@[simp] lemma op_g' (h : S.LeftHomologyData) :
    h.op.g' = h.f'.op := rfl

/-- A left homology data for a short complex `S` in the opposite category
induces a right homology data for `S.unop`. -/
@[simps]
def unop {S : ShortComplex Cᵒᵖ} (h : S.LeftHomologyData) : S.unop.RightHomologyData where
  Q := Opposite.unop h.K
  H := Opposite.unop h.H
  p := h.i.unop
  ι := h.π.unop
  wp := Quiver.Hom.op_inj h.wi
  hp := KernelFork.IsLimit.ofιUnop _ _ h.hi
  wι := Quiver.Hom.op_inj h.wπ
  hι := CokernelCofork.IsColimit.ofπUnop _ _ h.hπ

@[simp] lemma unop_g' {S : ShortComplex Cᵒᵖ} (h : S.LeftHomologyData) :
    h.unop.g' = h.f'.unop := rfl

end LeftHomologyData

instance [S.HasLeftHomology] : HasRightHomology S.op :=
  HasRightHomology.mk' S.leftHomologyData.op

instance [S.HasRightHomology] : HasLeftHomology S.op :=
  HasLeftHomology.mk' S.rightHomologyData.op

lemma hasLeftHomology_iff_op (S : ShortComplex C) :
    S.HasLeftHomology ↔ S.op.HasRightHomology :=
  ⟨fun _ => inferInstance, fun _ => HasLeftHomology.mk' S.op.rightHomologyData.unop⟩

lemma hasRightHomology_iff_op (S : ShortComplex C) :
    S.HasRightHomology ↔ S.op.HasLeftHomology :=
  ⟨fun _ => inferInstance, fun _ => HasRightHomology.mk' S.op.leftHomologyData.unop⟩

lemma hasLeftHomology_iff_unop (S : ShortComplex Cᵒᵖ) :
    S.HasLeftHomology ↔ S.unop.HasRightHomology :=
  S.unop.hasRightHomology_iff_op.symm

lemma hasRightHomology_iff_unop (S : ShortComplex Cᵒᵖ) :
    S.HasRightHomology ↔ S.unop.HasLeftHomology :=
  S.unop.hasLeftHomology_iff_op.symm

section

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData)

/-- Given right homology data `h₁` and `h₂` for two short complexes `S₁` and `S₂`,
a `RightHomologyMapData` for a morphism `φ : S₁ ⟶ S₂`
consists of a description of the induced morphisms on the `Q` (opcycles)
and `H` (right homology) fields of `h₁` and `h₂`. -/
structure RightHomologyMapData where
  /-- the induced map on opcycles -/
  φQ : h₁.Q ⟶ h₂.Q
  /-- the induced map on right homology -/
  φH : h₁.H ⟶ h₂.H
  /-- commutation with `p` -/
  commp : h₁.p ≫ φQ = φ.τ₂ ≫ h₂.p := by aesop_cat
  /-- commutation with `g'` -/
  commg' : φQ ≫ h₂.g' = h₁.g' ≫ φ.τ₃ := by aesop_cat
  /-- commutation with `ι` -/
  commι : φH ≫ h₂.ι = h₁.ι ≫ φQ := by aesop_cat

namespace RightHomologyMapData

attribute [reassoc (attr := simp)] commp commg' commι
attribute [nolint simpNF] mk.injEq

/-- The right homology map data associated to the zero morphism between two short complexes. -/
@[simps]
def zero (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
  RightHomologyMapData 0 h₁ h₂ where
  φQ := 0
  φH := 0

/-- The right homology map data associated to the identity morphism of a short complex. -/
@[simps]
def id (h : S.RightHomologyData) : RightHomologyMapData (𝟙 S) h h where
  φQ := 𝟙 _
  φH := 𝟙 _

/-- The composition of right homology map data. -/
@[simps]
def comp {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃} {h₁ : S₁.RightHomologyData}
    {h₂ : S₂.RightHomologyData} {h₃ : S₃.RightHomologyData}
    (ψ : RightHomologyMapData φ h₁ h₂) (ψ' : RightHomologyMapData φ' h₂ h₃) :
    RightHomologyMapData (φ ≫ φ') h₁ h₃ where
  φQ := ψ.φQ ≫ ψ'.φQ
  φH := ψ.φH ≫ ψ'.φH

instance : Subsingleton (RightHomologyMapData φ h₁ h₂) :=
  ⟨fun ψ₁ ψ₂ => by
    have hQ : ψ₁.φQ = ψ₂.φQ := by rw [← cancel_epi h₁.p, commp, commp]
    have hH : ψ₁.φH = ψ₂.φH := by rw [← cancel_mono h₂.ι, commι, commι, hQ]
    cases ψ₁
    cases ψ₂
    congr⟩

instance : Inhabited (RightHomologyMapData φ h₁ h₂) := ⟨by
  let φQ : h₁.Q ⟶ h₂.Q := h₁.descQ (φ.τ₂ ≫ h₂.p) (by rw [← φ.comm₁₂_assoc, h₂.wp, comp_zero])
  have commg' : φQ ≫ h₂.g' = h₁.g' ≫ φ.τ₃ :=
    by rw [← cancel_epi h₁.p, RightHomologyData.p_descQ_assoc, assoc,
      RightHomologyData.p_g', φ.comm₂₃, RightHomologyData.p_g'_assoc]
  let φH : h₁.H ⟶ h₂.H := h₂.liftH (h₁.ι ≫ φQ)
    (by rw [assoc, commg', RightHomologyData.ι_g'_assoc, zero_comp])
  exact ⟨φQ, φH, by simp, commg', by simp⟩⟩

instance : Unique (RightHomologyMapData φ h₁ h₂) := Unique.mk' _

variable {φ h₁ h₂}

lemma congr_φH {γ₁ γ₂ : RightHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) : γ₁.φH = γ₂.φH := by rw [eq]
lemma congr_φQ {γ₁ γ₂ : RightHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) : γ₁.φQ = γ₂.φQ := by rw [eq]

/-- When `S₁.f`, `S₁.g`, `S₂.f` and `S₂.g` are all zero, the action on right homology of a
morphism `φ : S₁ ⟶ S₂` is given by the action `φ.τ₂` on the middle objects. -/
@[simps]
def ofZeros (φ : S₁ ⟶ S₂) (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (hg₂ : S₂.g = 0) :
  RightHomologyMapData φ (RightHomologyData.ofZeros S₁ hf₁ hg₁)
    (RightHomologyData.ofZeros S₂ hf₂ hg₂) where
  φQ := φ.τ₂
  φH := φ.τ₂

/-- When `S₁.f` and `S₂.f` are zero and we have chosen limit kernel forks `c₁` and `c₂`
for `S₁.g` and `S₂.g` respectively, the action on right homology of a morphism `φ : S₁ ⟶ S₂` of
short complexes is given by the unique morphism `f : c₁.pt ⟶ c₂.pt` such that
`c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι`. -/
@[simps]
def ofIsLimitKernelFork (φ : S₁ ⟶ S₂)
    (hf₁ : S₁.f = 0) (c₁ : KernelFork S₁.g) (hc₁ : IsLimit c₁)
    (hf₂ : S₂.f = 0) (c₂ : KernelFork S₂.g) (hc₂ : IsLimit c₂) (f : c₁.pt ⟶ c₂.pt)
    (comm : c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι) :
    RightHomologyMapData φ (RightHomologyData.ofIsLimitKernelFork S₁ hf₁ c₁ hc₁)
      (RightHomologyData.ofIsLimitKernelFork S₂ hf₂ c₂ hc₂) where
  φQ := φ.τ₂
  φH := f
  commg' := by simp only [RightHomologyData.ofIsLimitKernelFork_g', φ.comm₂₃]
  commι := comm.symm

/-- When `S₁.g` and `S₂.g` are zero and we have chosen colimit cokernel coforks `c₁` and `c₂`
for `S₁.f` and `S₂.f` respectively, the action on right homology of a morphism `φ : S₁ ⟶ S₂` of
short complexes is given by the unique morphism `f : c₁.pt ⟶ c₂.pt` such that
`φ.τ₂ ≫ c₂.π = c₁.π ≫ f`. -/
@[simps]
def ofIsColimitCokernelCofork (φ : S₁ ⟶ S₂)
    (hg₁ : S₁.g = 0) (c₁ : CokernelCofork S₁.f) (hc₁ : IsColimit c₁)
    (hg₂ : S₂.g = 0) (c₂ : CokernelCofork S₂.f) (hc₂ : IsColimit c₂) (f : c₁.pt ⟶ c₂.pt)
    (comm : φ.τ₂ ≫ c₂.π = c₁.π ≫ f) :
    RightHomologyMapData φ (RightHomologyData.ofIsColimitCokernelCofork S₁ hg₁ c₁ hc₁)
      (RightHomologyData.ofIsColimitCokernelCofork S₂ hg₂ c₂ hc₂) where
  φQ := f
  φH := f
  commp := comm.symm

variable (S)

/-- When both maps `S.f` and `S.g` of a short complex `S` are zero, this is the homology map
data (for the identity of `S`) which relates the right homology data
`RightHomologyData.ofIsLimitKernelFork` and `ofZeros` . -/
@[simps]
def compatibilityOfZerosOfIsLimitKernelFork (hf : S.f = 0) (hg : S.g = 0)
    (c : KernelFork S.g) (hc : IsLimit c) :
    RightHomologyMapData (𝟙 S)
      (RightHomologyData.ofIsLimitKernelFork S hf c hc)
      (RightHomologyData.ofZeros S hf hg) where
  φQ := 𝟙 _
  φH := c.ι

/-- When both maps `S.f` and `S.g` of a short complex `S` are zero, this is the homology map
data (for the identity of `S`) which relates the right homology data `ofZeros` and
`ofIsColimitCokernelCofork`. -/
@[simps]
def compatibilityOfZerosOfIsColimitCokernelCofork (hf : S.f = 0) (hg : S.g = 0)
    (c : CokernelCofork S.f) (hc : IsColimit c) :
    RightHomologyMapData (𝟙 S)
      (RightHomologyData.ofZeros S hf hg)
      (RightHomologyData.ofIsColimitCokernelCofork S hg c hc) where
  φQ := c.π
  φH := c.π

end RightHomologyMapData

end

section

variable (S)
variable [S.HasRightHomology]

/-- The right homology of a short complex,
given by the `H` field of a chosen right homology data. -/
noncomputable def rightHomology : C := S.rightHomologyData.H

/-- The "opcycles" of a short complex, given by the `Q` field of a chosen right homology data.
This is the dual notion to cycles. -/
noncomputable def opcycles : C := S.rightHomologyData.Q

/-- The canonical map `S.rightHomology ⟶ S.opcycles`. -/
noncomputable def rightHomologyι : S.rightHomology ⟶ S.opcycles :=
  S.rightHomologyData.ι

/-- The projection `S.X₂ ⟶ S.opcycles`. -/
noncomputable def pOpcycles : S.X₂ ⟶ S.opcycles := S.rightHomologyData.p

/-- The canonical map `S.opcycles ⟶ X₃`. -/
noncomputable def fromOpcycles : S.opcycles ⟶ S.X₃ := S.rightHomologyData.g'

@[reassoc (attr := simp)]
lemma f_pOpcycles : S.f ≫ S.pOpcycles = 0 := S.rightHomologyData.wp

@[reassoc (attr := simp)]
lemma p_fromOpcycles : S.pOpcycles ≫ S.fromOpcycles = S.g := S.rightHomologyData.p_g'

instance : Epi S.pOpcycles := by
  dsimp only [pOpcycles]
  infer_instance

instance : Mono S.rightHomologyι := by
  dsimp only [rightHomologyι]
  infer_instance

lemma rightHomology_ext_iff (f₁ f₂ : A ⟶ S.rightHomology) :
    f₁ = f₂ ↔ f₁ ≫ S.rightHomologyι = f₂ ≫ S.rightHomologyι := by
  rw [cancel_mono]

@[ext]
lemma rightHomology_ext (f₁ f₂ : A ⟶ S.rightHomology)
    (h : f₁ ≫ S.rightHomologyι = f₂ ≫ S.rightHomologyι) : f₁ = f₂ := by
  simpa only [rightHomology_ext_iff]

lemma opcycles_ext_iff (f₁ f₂ : S.opcycles ⟶ A) :
    f₁ = f₂ ↔ S.pOpcycles ≫ f₁ = S.pOpcycles ≫ f₂ := by
  rw [cancel_epi]

@[ext]
lemma opcycles_ext (f₁ f₂ : S.opcycles ⟶ A)
    (h : S.pOpcycles ≫ f₁ = S.pOpcycles ≫ f₂) : f₁ = f₂ := by
  simpa only [opcycles_ext_iff]

lemma isIso_pOpcycles (hf : S.f = 0) : IsIso S.pOpcycles :=
  RightHomologyData.isIso_p _ hf

/-- When `S.f = 0`, this is the canonical isomorphism `S.opcycles ≅ S.X₂`
induced by `S.pOpcycles`. -/
@[simps! inv]
noncomputable def opcyclesIsoX₂ (hf : S.f = 0) : S.opcycles ≅ S.X₂ := by
  have := S.isIso_pOpcycles hf
  exact (asIso S.pOpcycles).symm

@[reassoc (attr := simp)]
lemma opcyclesIsoX₂_inv_hom_id (hf : S.f = 0) :
    S.pOpcycles ≫ (S.opcyclesIsoX₂ hf).hom = 𝟙 _ := (S.opcyclesIsoX₂ hf).inv_hom_id

@[reassoc (attr := simp)]
lemma opcyclesIsoX₂_hom_inv_id (hf : S.f = 0) :
    (S.opcyclesIsoX₂ hf).hom ≫ S.pOpcycles = 𝟙 _ := (S.opcyclesIsoX₂ hf).hom_inv_id

lemma isIso_rightHomologyι (hg : S.g = 0) : IsIso S.rightHomologyι :=
  RightHomologyData.isIso_ι _ hg

/-- When `S.g = 0`, this is the canonical isomorphism `S.opcycles ≅ S.rightHomology` induced
by `S.rightHomologyι`. -/
@[simps! inv]
noncomputable def opcyclesIsoRightHomology (hg : S.g = 0) : S.opcycles ≅ S.rightHomology := by
  have := S.isIso_rightHomologyι hg
  exact (asIso S.rightHomologyι).symm

@[reassoc (attr := simp)]
lemma opcyclesIsoRightHomology_inv_hom_id (hg : S.g = 0) :
    S.rightHomologyι ≫ (S.opcyclesIsoRightHomology hg).hom = 𝟙 _ :=
  (S.opcyclesIsoRightHomology hg).inv_hom_id

@[reassoc (attr := simp)]
lemma opcyclesIsoRightHomology_hom_inv_id (hg : S.g = 0) :
    (S.opcyclesIsoRightHomology hg).hom ≫ S.rightHomologyι  = 𝟙 _ :=
  (S.opcyclesIsoRightHomology hg).hom_inv_id

end

section

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData)

/-- The (unique) right homology map data associated to a morphism of short complexes that
are both equipped with right homology data. -/
def rightHomologyMapData : RightHomologyMapData φ h₁ h₂ := default

/-- Given a morphism `φ : S₁ ⟶ S₂` of short complexes and right homology data `h₁` and `h₂`
for `S₁` and `S₂` respectively, this is the induced right homology map `h₁.H ⟶ h₁.H`. -/
def rightHomologyMap' : h₁.H ⟶ h₂.H := (rightHomologyMapData φ _ _).φH

/-- Given a morphism `φ : S₁ ⟶ S₂` of short complexes and right homology data `h₁` and `h₂`
for `S₁` and `S₂` respectively, this is the induced morphism `h₁.K ⟶ h₁.K` on opcycles. -/
def opcyclesMap' : h₁.Q ⟶ h₂.Q := (rightHomologyMapData φ _ _).φQ

@[reassoc (attr := simp)]
lemma p_opcyclesMap' : h₁.p ≫ opcyclesMap' φ h₁ h₂ = φ.τ₂ ≫ h₂.p :=
  RightHomologyMapData.commp _

@[reassoc (attr := simp)]
lemma opcyclesMap'_g' : opcyclesMap' φ h₁ h₂ ≫ h₂.g' = h₁.g' ≫ φ.τ₃ := by
  simp only [← cancel_epi h₁.p, assoc, φ.comm₂₃, p_opcyclesMap'_assoc,
    RightHomologyData.p_g'_assoc, RightHomologyData.p_g']

@[reassoc (attr := simp)]
lemma rightHomologyι_naturality' :
    rightHomologyMap' φ h₁ h₂ ≫ h₂.ι = h₁.ι ≫ opcyclesMap' φ h₁ h₂ :=
  RightHomologyMapData.commι _

end

section

variable [HasRightHomology S₁] [HasRightHomology S₂] (φ : S₁ ⟶ S₂)

/-- The (right) homology map `S₁.rightHomology ⟶ S₂.rightHomology` induced by a morphism
`S₁ ⟶ S₂` of short complexes. -/
noncomputable def rightHomologyMap : S₁.rightHomology ⟶ S₂.rightHomology :=
  rightHomologyMap' φ _ _

/-- The morphism `S₁.opcycles ⟶ S₂.opcycles` induced by a morphism `S₁ ⟶ S₂` of short complexes. -/
noncomputable def opcyclesMap : S₁.opcycles ⟶ S₂.opcycles :=
  opcyclesMap' φ _ _

@[reassoc (attr := simp)]
lemma p_opcyclesMap : S₁.pOpcycles ≫ opcyclesMap φ = φ.τ₂ ≫ S₂.pOpcycles :=
  p_opcyclesMap' _ _ _

@[reassoc (attr := simp)]
lemma fromOpcycles_naturality : opcyclesMap φ ≫ S₂.fromOpcycles = S₁.fromOpcycles ≫ φ.τ₃ :=
  opcyclesMap'_g' _ _ _

@[reassoc (attr := simp)]
lemma rightHomologyι_naturality :
    rightHomologyMap φ ≫ S₂.rightHomologyι = S₁.rightHomologyι ≫ opcyclesMap φ :=
  rightHomologyι_naturality' _ _ _

end

namespace RightHomologyMapData

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}
  (γ : RightHomologyMapData φ h₁ h₂)

lemma rightHomologyMap'_eq : rightHomologyMap' φ h₁ h₂ = γ.φH :=
  RightHomologyMapData.congr_φH (Subsingleton.elim _ _)

lemma opcyclesMap'_eq : opcyclesMap' φ h₁ h₂ = γ.φQ :=
  RightHomologyMapData.congr_φQ (Subsingleton.elim _ _)

end RightHomologyMapData

@[simp]
lemma rightHomologyMap'_id (h : S.RightHomologyData) :
    rightHomologyMap' (𝟙 S) h h = 𝟙 _ :=
  (RightHomologyMapData.id h).rightHomologyMap'_eq

@[simp]
lemma opcyclesMap'_id (h : S.RightHomologyData) :
    opcyclesMap' (𝟙 S) h h = 𝟙 _ :=
  (RightHomologyMapData.id h).opcyclesMap'_eq

variable (S)

@[simp]
lemma rightHomologyMap_id [HasRightHomology S] :
    rightHomologyMap (𝟙 S) = 𝟙 _ :=
  rightHomologyMap'_id _

@[simp]
lemma opcyclesMap_id [HasRightHomology S] :
    opcyclesMap (𝟙 S) = 𝟙 _ :=
  opcyclesMap'_id _

@[simp]
lemma rightHomologyMap'_zero (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    rightHomologyMap' 0 h₁ h₂ = 0 :=
  (RightHomologyMapData.zero h₁ h₂).rightHomologyMap'_eq

@[simp]
lemma opcyclesMap'_zero (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    opcyclesMap' 0 h₁ h₂ = 0 :=
  (RightHomologyMapData.zero h₁ h₂).opcyclesMap'_eq

variable (S₁ S₂)

@[simp]
lemma rightHomologyMap_zero [HasRightHomology S₁] [HasRightHomology S₂] :
    rightHomologyMap (0 : S₁ ⟶ S₂) = 0 :=
  rightHomologyMap'_zero _ _

@[simp]
lemma opcyclesMap_zero [HasRightHomology S₁] [HasRightHomology S₂] :
  opcyclesMap (0 : S₁ ⟶ S₂) = 0 :=
opcyclesMap'_zero _ _

variable {S₁ S₂}

@[reassoc]
lemma rightHomologyMap'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) (h₃ : S₃.RightHomologyData) :
    rightHomologyMap' (φ₁ ≫ φ₂) h₁ h₃ = rightHomologyMap' φ₁ h₁ h₂ ≫
      rightHomologyMap' φ₂ h₂ h₃ := by
  let γ₁ := rightHomologyMapData φ₁ h₁ h₂
  let γ₂ := rightHomologyMapData φ₂ h₂ h₃
  rw [γ₁.rightHomologyMap'_eq, γ₂.rightHomologyMap'_eq, (γ₁.comp γ₂).rightHomologyMap'_eq,
    RightHomologyMapData.comp_φH]

@[reassoc]
lemma opcyclesMap'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) (h₃ : S₃.RightHomologyData) :
    opcyclesMap' (φ₁ ≫ φ₂) h₁ h₃ = opcyclesMap' φ₁ h₁ h₂ ≫ opcyclesMap' φ₂ h₂ h₃ := by
  let γ₁ := rightHomologyMapData φ₁ h₁ h₂
  let γ₂ := rightHomologyMapData φ₂ h₂ h₃
  rw [γ₁.opcyclesMap'_eq, γ₂.opcyclesMap'_eq, (γ₁.comp γ₂).opcyclesMap'_eq,
    RightHomologyMapData.comp_φQ]

@[simp]
lemma rightHomologyMap_comp [HasRightHomology S₁] [HasRightHomology S₂] [HasRightHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    rightHomologyMap (φ₁ ≫ φ₂) = rightHomologyMap φ₁ ≫ rightHomologyMap φ₂ :=
rightHomologyMap'_comp _ _ _ _ _

@[simp]
lemma opcyclesMap_comp [HasRightHomology S₁] [HasRightHomology S₂] [HasRightHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    opcyclesMap (φ₁ ≫ φ₂) = opcyclesMap φ₁ ≫ opcyclesMap φ₂ :=
  opcyclesMap'_comp _ _ _ _ _

attribute [simp] rightHomologyMap_comp opcyclesMap_comp

/-- An isomorphism of short complexes `S₁ ≅ S₂` induces an isomorphism on the `H` fields
of right homology data of `S₁` and `S₂`. -/
@[simps]
def rightHomologyMapIso' (e : S₁ ≅ S₂) (h₁ : S₁.RightHomologyData)
    (h₂ : S₂.RightHomologyData) : h₁.H ≅ h₂.H where
  hom := rightHomologyMap' e.hom h₁ h₂
  inv := rightHomologyMap' e.inv h₂ h₁
  hom_inv_id := by rw [← rightHomologyMap'_comp, e.hom_inv_id, rightHomologyMap'_id]
  inv_hom_id := by rw [← rightHomologyMap'_comp, e.inv_hom_id, rightHomologyMap'_id]

instance isIso_rightHomologyMap'_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ]
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    IsIso (rightHomologyMap' φ h₁ h₂) :=
  (inferInstance : IsIso (rightHomologyMapIso' (asIso φ) h₁ h₂).hom)

/-- An isomorphism of short complexes `S₁ ≅ S₂` induces an isomorphism on the `Q` fields
of right homology data of `S₁` and `S₂`. -/
@[simps]
def opcyclesMapIso' (e : S₁ ≅ S₂) (h₁ : S₁.RightHomologyData)
    (h₂ : S₂.RightHomologyData) : h₁.Q ≅ h₂.Q where
  hom := opcyclesMap' e.hom h₁ h₂
  inv := opcyclesMap' e.inv h₂ h₁
  hom_inv_id := by rw [← opcyclesMap'_comp, e.hom_inv_id, opcyclesMap'_id]
  inv_hom_id := by rw [← opcyclesMap'_comp, e.inv_hom_id, opcyclesMap'_id]

instance isIso_opcyclesMap'_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ]
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    IsIso (opcyclesMap' φ h₁ h₂) :=
  (inferInstance : IsIso (opcyclesMapIso' (asIso φ) h₁ h₂).hom)

/-- The isomorphism `S₁.rightHomology ≅ S₂.rightHomology` induced by an isomorphism of
short complexes `S₁ ≅ S₂`. -/
@[simps]
noncomputable def rightHomologyMapIso (e : S₁ ≅ S₂) [S₁.HasRightHomology]
    [S₂.HasRightHomology] : S₁.rightHomology ≅ S₂.rightHomology where
  hom := rightHomologyMap e.hom
  inv := rightHomologyMap e.inv
  hom_inv_id := by rw [← rightHomologyMap_comp, e.hom_inv_id, rightHomologyMap_id]
  inv_hom_id := by rw [← rightHomologyMap_comp, e.inv_hom_id, rightHomologyMap_id]

instance isIso_rightHomologyMap_of_iso (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasRightHomology]
    [S₂.HasRightHomology] :
    IsIso (rightHomologyMap φ) :=
  (inferInstance : IsIso (rightHomologyMapIso (asIso φ)).hom)

/-- The isomorphism `S₁.cycles ≅ S₂.cycles` induced by an isomorphism
of short complexes `S₁ ≅ S₂`. -/
@[simps]
noncomputable def opcyclesMapIso (e : S₁ ≅ S₂) [S₁.HasRightHomology]
    [S₂.HasRightHomology] : S₁.opcycles ≅ S₂.opcycles where
  hom := opcyclesMap e.hom
  inv := opcyclesMap e.inv
  hom_inv_id := by rw [← opcyclesMap_comp, e.hom_inv_id, opcyclesMap_id]
  inv_hom_id := by rw [← opcyclesMap_comp, e.inv_hom_id, opcyclesMap_id]

instance isIso_opcyclesMap_of_iso (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasRightHomology]
    [S₂.HasRightHomology] : IsIso (opcyclesMap φ) :=
  (inferInstance : IsIso (opcyclesMapIso (asIso φ)).hom)

variable {S}

namespace RightHomologyData

variable (h : S.RightHomologyData) [S.HasRightHomology]

/-- The isomorphism `S.rightHomology ≅ h.H` induced by a right homology data `h` for a
short complex `S`. -/
noncomputable def rightHomologyIso : S.rightHomology ≅ h.H :=
  rightHomologyMapIso' (Iso.refl _) _ _

/-- The isomorphism `S.opcycles ≅ h.Q` induced by a right homology data `h` for a
short complex `S`. -/
noncomputable def opcyclesIso : S.opcycles ≅ h.Q :=
  opcyclesMapIso' (Iso.refl _) _ _

@[reassoc (attr := simp)]
lemma p_comp_opcyclesIso_inv : h.p ≫ h.opcyclesIso.inv = S.pOpcycles := by
  dsimp [pOpcycles, RightHomologyData.opcyclesIso]
  simp only [p_opcyclesMap', id_τ₂, id_comp]

@[reassoc (attr := simp)]
lemma pOpcycles_comp_opcyclesIso_hom : S.pOpcycles ≫ h.opcyclesIso.hom = h.p := by
  simp only [← h.p_comp_opcyclesIso_inv, assoc, Iso.inv_hom_id, comp_id]

@[reassoc (attr := simp)]
lemma rightHomologyIso_inv_comp_rightHomologyι :
    h.rightHomologyIso.inv ≫ S.rightHomologyι = h.ι ≫ h.opcyclesIso.inv := by
  dsimp only [rightHomologyι, rightHomologyIso, opcyclesIso, rightHomologyMapIso',
    opcyclesMapIso', Iso.refl]
  rw [rightHomologyι_naturality']

@[reassoc (attr := simp)]
lemma rightHomologyIso_hom_comp_ι :
    h.rightHomologyIso.hom ≫ h.ι = S.rightHomologyι ≫ h.opcyclesIso.hom := by
  simp only [← cancel_mono h.opcyclesIso.inv, ← cancel_epi h.rightHomologyIso.inv,
    assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, comp_id, rightHomologyIso_inv_comp_rightHomologyι]

end RightHomologyData

namespace RightHomologyMapData

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}
  (γ : RightHomologyMapData φ h₁ h₂)

lemma rightHomologyMap_eq [S₁.HasRightHomology] [S₂.HasRightHomology] :
    rightHomologyMap φ = h₁.rightHomologyIso.hom ≫ γ.φH ≫ h₂.rightHomologyIso.inv := by
  dsimp [RightHomologyData.rightHomologyIso, rightHomologyMapIso']
  rw [← γ.rightHomologyMap'_eq, ← rightHomologyMap'_comp,
    ← rightHomologyMap'_comp, id_comp, comp_id]
  rfl

lemma opcyclesMap_eq [S₁.HasRightHomology] [S₂.HasRightHomology] :
    opcyclesMap φ = h₁.opcyclesIso.hom ≫ γ.φQ ≫ h₂.opcyclesIso.inv := by
  dsimp [RightHomologyData.opcyclesIso, cyclesMapIso']
  rw [← γ.opcyclesMap'_eq, ← opcyclesMap'_comp, ← opcyclesMap'_comp, id_comp, comp_id]
  rfl

lemma rightHomologyMap_comm [S₁.HasRightHomology] [S₂.HasRightHomology] :
    rightHomologyMap φ ≫ h₂.rightHomologyIso.hom = h₁.rightHomologyIso.hom ≫ γ.φH := by
  simp only [γ.rightHomologyMap_eq, assoc, Iso.inv_hom_id, comp_id]

lemma opcyclesMap_comm [S₁.HasRightHomology] [S₂.HasRightHomology] :
    opcyclesMap φ ≫ h₂.opcyclesIso.hom = h₁.opcyclesIso.hom ≫ γ.φQ := by
  simp only [γ.opcyclesMap_eq, assoc, Iso.inv_hom_id, comp_id]

end RightHomologyMapData

section

variable (C)
variable [HasKernels C] [HasCokernels C]

/-- The right homology functor `ShortComplex C ⥤ C`, where the right homology of a
short complex `S` is understood as a kernel of the obvious map `S.fromOpcycles : S.opcycles ⟶ S.X₃`
where `S.opcycles` is a cokernel of `S.f : S.X₁ ⟶ S.X₂`. -/
@[simps]
noncomputable def rightHomologyFunctor :
    ShortComplex C ⥤ C where
  obj S := S.rightHomology
  map := rightHomologyMap

/-- The opcycles functor `ShortComplex C ⥤ C` which sends a short complex `S` to `S.opcycles`
which is a cokernel of `S.f : S.X₁ ⟶ S.X₂`. -/
@[simps]
noncomputable def opcyclesFunctor :
    ShortComplex C ⥤ C where
  obj S := S.opcycles
  map := opcyclesMap

/-- The natural transformation `S.rightHomology ⟶ S.opcycles` for all short complexes `S`. -/
@[simps]
noncomputable def rightHomologyιNatTrans :
    rightHomologyFunctor C ⟶ opcyclesFunctor C where
  app S := rightHomologyι S
  naturality := fun _ _ φ => rightHomologyι_naturality φ

/-- The natural transformation `S.X₂ ⟶ S.opcycles` for all short complexes `S`. -/
@[simps]
noncomputable def pOpcyclesNatTrans :
    ShortComplex.π₂ ⟶ opcyclesFunctor C where
  app S := S.pOpcycles

/-- The natural transformation `S.opcycles ⟶ S.X₃` for all short complexes `S`. -/
@[simps]
noncomputable def fromOpcyclesNatTrans :
    opcyclesFunctor C ⟶ π₃ where
  app S := S.fromOpcycles
  naturality := fun _ _  φ => fromOpcycles_naturality φ

end

end ShortComplex

end CategoryTheory
