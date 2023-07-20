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

end RightHomologyMapData

end

end ShortComplex

end CategoryTheory
