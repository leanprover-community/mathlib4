/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-! LeftHomology of short complexes

Given a short complex `S : ShortComplex C`, which consists of two composable
maps `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` such that `f ≫ g = 0`, we shall define
here the "left homology" `S.leftHomology` of `S` (TODO). For this, we introduce the
notion of "left homology data". Such an `h : S.LeftHomologyData` consists of the
datum of morphisms `i : K ⟶ X₂` and `π : K ⟶ H` such that `i` identifies
`K` to the kernel of `g : X₂ ⟶ X₃`, and that `π` identifies `H` to the cokernel
of the induced map `f' : X₁ ⟶ K`.

When such a `S.LeftHomologyData` exists, we shall say that `[S.HasLeftHomology]`
and we define `S.leftHomology` to be the `H` field of a chosen left homology data.
Similarly, we define `S.cycles` to be the `K` field.

The dual notion is defined in `RightHomologyData.lean`. In `Homology.lean`,
when `S` has two compatible left and right homology data (i.e. they give
the same `H` up to a canonical isomorphism), we shall define `[S.HasHomology]`
and `S.homology` (TODO).

-/

namespace CategoryTheory

open Category Limits

namespace ShortComplex

variable {C : Type _} [Category C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

/-- A left homology data for a short complex `S` consists of morphisms `i : K ⟶ S.X₂` and
`π : K ⟶ H` such that `i` identifies `K` to the kernel of `g : S.X₂ ⟶ S.X₃`,
and that `π` identifies `H` to the cokernel of the induced map `f' : S.X₁ ⟶ K` --/
structure LeftHomologyData where
  /-- a choice of kernel of `S.g : S.X₂ ⟶ S.X₃`-/
  K : C
  /-- a choice of cokernel of the induced morphism `S.f' : S.X₁ ⟶ K`-/
  H : C
  /-- the inclusion of cycles in `S.X₂` -/
  i : K ⟶ S.X₂
  /-- the projection from cycles to the (left) homology -/
  π : K ⟶ H
  /-- the kernel condition for `i` -/
  wi : i ≫ S.g = 0
  /-- `i : K ⟶ S.X₂ ` is a kernel of `g : S.X₂ ⟶ S.X₃` -/
  hi : IsLimit (KernelFork.ofι i wi)
  /-- the cokernel condition for `π` -/
  wπ : hi.lift (KernelFork.ofι _ S.zero) ≫ π = 0
  /-- `π : K ⟶ H ` is a cokernel of the induced morphism `S.f' : S.X₁ ⟶ K` -/
  hπ : IsColimit (CokernelCofork.ofπ π wπ)

initialize_simps_projections LeftHomologyData (-hi, -hπ)

namespace LeftHomologyData

/-- The chosen kernels and cokernels of the limits API give a `LeftHomologyData` -/
@[simps]
noncomputable def ofHasKernelOfHasCokernel
    [HasKernel S.g] [HasCokernel (kernel.lift S.g S.f S.zero)] :
  S.LeftHomologyData where
  K := kernel S.g
  H := cokernel (kernel.lift S.g S.f S.zero)
  i := kernel.ι _
  π := cokernel.π _
  wi := kernel.condition _
  hi := kernelIsKernel _
  wπ := cokernel.condition _
  hπ := cokernelIsCokernel _

attribute [reassoc (attr := simp)] wi wπ

variable {S}
variable (h : S.LeftHomologyData) {A : C}

instance : Mono h.i := ⟨fun _ _ => Fork.IsLimit.hom_ext h.hi⟩

instance : Epi h.π := ⟨fun _ _ => Cofork.IsColimit.hom_ext h.hπ⟩

/-- Any morphism `k : A ⟶ S.X₂` that is a cycle (i.e. `k ≫ S.g = 0`) lifts
to a morphism `A ⟶ K` -/
def liftK (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) : A ⟶ h.K := h.hi.lift (KernelFork.ofι k hk)

@[reassoc (attr := simp)]
lemma liftK_i (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) : h.liftK k hk ≫ h.i = k :=
  h.hi.fac _ WalkingParallelPair.zero

/-- The (left) homology class `A ⟶ H` attached to a cycle `k : A ⟶ S.X₂` -/
@[simp]
def liftH (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) : A ⟶ h.H := h.liftK k hk ≫ h.π

/-- Given `h : LeftHomologyData S`, this is morphism `S.X₁ ⟶ h.K` induced
by `S.f : S.X₁ ⟶ S.X₂` and the fact that `h.K` is a kernel of `S.g : S.X₂ ⟶ S.X₃`. -/
def f' : S.X₁ ⟶ h.K := h.liftK S.f S.zero

@[reassoc (attr := simp)] lemma f'_i : h.f' ≫ h.i = S.f := liftK_i _ _ _

@[reassoc (attr := simp)] lemma f'_π : h.f' ≫ h.π = 0 := h.wπ

@[reassoc]
lemma liftK_π_eq_zero_of_boundary (k : A ⟶ S.X₂) (x : A ⟶ S.X₁) (hx : k = x ≫ S.f) :
    h.liftK k (by rw [hx, assoc, S.zero, comp_zero]) ≫ h.π = 0 := by
  rw [show 0 = (x ≫ h.f') ≫ h.π by simp]
  congr 1
  simp only [← cancel_mono h.i, hx, liftK_i, assoc, f'_i]

/-- For `h : S.LeftHomologyData`, this is a restatement of `h.hπ`, saying that
`π : h.K ⟶ h.H` is a cokernel of `h.f' : S.X₁ ⟶ h.K`. -/
def hπ' : IsColimit (CokernelCofork.ofπ h.π h.f'_π) := h.hπ

/-- The morphism `H ⟶ A` induced by a morphism `k : K ⟶ A` such that `f' ≫ k = 0` -/
def descH (k : h.K ⟶ A) (hk : h.f' ≫ k = 0) : h.H ⟶ A :=
  h.hπ.desc (CokernelCofork.ofπ k hk)

@[reassoc (attr := simp)]
lemma π_descH (k : h.K ⟶ A) (hk : h.f' ≫ k = 0) : h.π ≫ h.descH k hk = k :=
  h.hπ.fac (CokernelCofork.ofπ k hk) WalkingParallelPair.one

variable (S)

/-- When the second map `S.g` is zero, this is the left homology data on `S` given
by any colimit cokernel cofork of `S.f` -/
@[simps]
def ofIsColimitCokernelCofork (hg : S.g = 0) (c : CokernelCofork S.f) (hc : IsColimit c) :
    S.LeftHomologyData where
  K := S.X₂
  H := c.pt
  i := 𝟙 _
  π := c.π
  wi := by rw [id_comp, hg]
  hi := KernelFork.IsLimit.ofId _ hg
  wπ := CokernelCofork.condition _
  hπ := IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _) (by aesop_cat))

@[simp] lemma ofIsColimitCokernelCofork_f' (hg : S.g = 0) (c : CokernelCofork S.f)
    (hc : IsColimit c) : (ofIsColimitCokernelCofork S hg c hc).f' = S.f := by
  rw [← cancel_mono (ofIsColimitCokernelCofork S hg c hc).i, f'_i,
    ofIsColimitCokernelCofork_i]
  dsimp
  rw [comp_id]

/-- When the second map `S.g` is zero, this is the left homology data on `S` given by
the chosen `cokernel S.f` -/
@[simps!]
noncomputable def ofHasCokernel [HasCokernel S.f] (hg : S.g = 0) : S.LeftHomologyData :=
  ofIsColimitCokernelCofork S hg _ (cokernelIsCokernel _)

/-- When the first map `S.f` is zero, this is the left homology data on `S` given
by any limit kernel fork of `S.g` -/
@[simps]
def ofIsLimitKernelFork (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c) :
    S.LeftHomologyData where
  K := c.pt
  H := c.pt
  i := c.ι
  π := 𝟙 _
  wi := KernelFork.condition _
  hi := IsLimit.ofIsoLimit hc (Fork.ext (Iso.refl _) (by aesop_cat))
  wπ := Fork.IsLimit.hom_ext hc (by
    dsimp
    simp only [comp_id, zero_comp, Fork.IsLimit.lift_ι, Fork.ι_ofι, hf])
  hπ := CokernelCofork.IsColimit.ofId _ (Fork.IsLimit.hom_ext hc (by
    dsimp
    simp only [comp_id, zero_comp, Fork.IsLimit.lift_ι, Fork.ι_ofι, hf]))

@[simp] lemma ofIsLimitKernelFork_f' (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c) :
    (ofIsLimitKernelFork S hf c hc).f' = 0 := by
  rw [← cancel_mono (ofIsLimitKernelFork S hf c hc).i, f'_i, hf, zero_comp]

/-- When the first map `S.f` is zero, this is the left homology data on `S` given
by the chosen `kernel S.g` -/
@[simp]
noncomputable def ofHasKernel [HasKernel S.g] (hf : S.f = 0) : S.LeftHomologyData :=
  ofIsLimitKernelFork S hf _ (kernelIsKernel _)

/-- When both `S.f` and `S.g` are zero, the middle object `S.X₂` gives a left homology data on S -/
@[simps]
def ofZeros (hf : S.f = 0) (hg : S.g = 0) : S.LeftHomologyData where
  K := S.X₂
  H := S.X₂
  i := 𝟙 _
  π := 𝟙 _
  wi := by rw [id_comp, hg]
  hi := KernelFork.IsLimit.ofId _ hg
  wπ := by
    change S.f ≫ 𝟙 _ = 0
    simp only [hf, zero_comp]
  hπ := CokernelCofork.IsColimit.ofId _ hf

@[simp] lemma ofZeros_f' (hf : S.f = 0) (hg : S.g = 0) :
    (ofZeros S hf hg).f' = 0 := by
  rw [← cancel_mono ((ofZeros S hf hg).i), zero_comp, f'_i, hf]

end LeftHomologyData

/-- A short complex `S` has left homology when there exists a `S.LeftHomologyData` -/
class HasLeftHomology : Prop where
  condition : Nonempty S.LeftHomologyData

/-- A chosen `S.LeftHomologyData` for a short complex `S` that has left homology -/
noncomputable def leftHomologyData [S.HasLeftHomology] :
  S.LeftHomologyData := HasLeftHomology.condition.some

variable {S}

namespace HasLeftHomology

lemma mk' (h : S.LeftHomologyData) : HasLeftHomology S := ⟨Nonempty.intro h⟩

instance of_hasKernel_of_hasCokernel [HasKernel S.g] [HasCokernel (kernel.lift S.g S.f S.zero)] :
  S.HasLeftHomology := HasLeftHomology.mk' (LeftHomologyData.ofHasKernelOfHasCokernel S)

instance of_hasCokernel {X Y : C} (f : X ⟶ Y) (Z : C) [HasCokernel f] :
    (ShortComplex.mk f (0 : Y ⟶ Z) comp_zero).HasLeftHomology :=
  HasLeftHomology.mk' (LeftHomologyData.ofHasCokernel _ rfl)

instance of_hasKernel {Y Z : C} (g : Y ⟶ Z) (X : C) [HasKernel g] :
    (ShortComplex.mk (0 : X ⟶ Y) g zero_comp).HasLeftHomology :=
  HasLeftHomology.mk' (LeftHomologyData.ofHasKernel _ rfl)

instance of_zeros (X Y Z : C) :
    (ShortComplex.mk (0 : X ⟶ Y) (0 : Y ⟶ Z) zero_comp).HasLeftHomology :=
  HasLeftHomology.mk' (LeftHomologyData.ofZeros _ rfl rfl)

end HasLeftHomology

section

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)

/-- Given left homology data `h₁` and `h₂` for two short complexes `S₁` and `S₂`,
a `LeftHomologyMapData` for a morphism `φ : S₁ ⟶ S₂`
consists of a description of the induced morphisms on the `K` (cycles)
and `H` (left homology) fields of `h₁` and `h₂`. -/
structure LeftHomologyMapData where
  /-- the induced map on cycles -/
  φK : h₁.K ⟶ h₂.K
  /-- the induced map on left homology -/
  φH : h₁.H ⟶ h₂.H
  /-- commutation with `i` -/
  commi : φK ≫ h₂.i = h₁.i ≫ φ.τ₂ := by aesop_cat
  /-- commutation with `f'` -/
  commf' : h₁.f' ≫ φK = φ.τ₁ ≫ h₂.f' := by aesop_cat
  /-- commutation with `π` -/
  commπ : h₁.π ≫ φH = φK ≫ h₂.π := by aesop_cat

namespace LeftHomologyMapData

attribute [reassoc (attr := simp)] commi commf' commπ
attribute [nolint simpNF] mk.injEq

/-- The left homology map data associated to the zero morphism between two short complexes. -/
@[simps]
def zero (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    LeftHomologyMapData 0 h₁ h₂ where
  φK := 0
  φH := 0

/-- The left homology map data associated to the identity morphism of a short complex. -/
@[simps]
def id (h : S.LeftHomologyData) : LeftHomologyMapData (𝟙 S) h h where
  φK := 𝟙 _
  φH := 𝟙 _

/-- The composition of left homology map data. -/
@[simps]
def comp {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃}
    {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData} {h₃ : S₃.LeftHomologyData}
    (ψ : LeftHomologyMapData φ h₁ h₂) (ψ' : LeftHomologyMapData φ' h₂ h₃) :
    LeftHomologyMapData (φ ≫ φ') h₁ h₃ where
  φK := ψ.φK ≫ ψ'.φK
  φH := ψ.φH ≫ ψ'.φH

instance : Subsingleton (LeftHomologyMapData φ h₁ h₂) :=
  ⟨fun ψ₁ ψ₂ => by
    have hK : ψ₁.φK = ψ₂.φK := by rw [← cancel_mono h₂.i, commi, commi]
    have hH : ψ₁.φH = ψ₂.φH := by rw [← cancel_epi h₁.π, commπ, commπ, hK]
    cases ψ₁
    cases ψ₂
    congr⟩

instance : Inhabited (LeftHomologyMapData φ h₁ h₂) := ⟨by
  let φK : h₁.K ⟶ h₂.K := h₂.liftK (h₁.i ≫ φ.τ₂)
    (by rw [assoc, φ.comm₂₃, h₁.wi_assoc, zero_comp])
  have commf' : h₁.f' ≫ φK = φ.τ₁ ≫ h₂.f' := by
    rw [← cancel_mono h₂.i, assoc, assoc, LeftHomologyData.liftK_i,
      LeftHomologyData.f'_i_assoc, LeftHomologyData.f'_i, φ.comm₁₂]
  let φH : h₁.H ⟶ h₂.H := h₁.descH (φK ≫ h₂.π)
    (by rw [reassoc_of% commf', h₂.f'_π, comp_zero])
  exact ⟨φK, φH, by simp, commf', by simp⟩⟩

instance : Unique (LeftHomologyMapData φ h₁ h₂) := Unique.mk' _

variable {φ h₁ h₂}

lemma congr_φH {γ₁ γ₂ : LeftHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) : γ₁.φH = γ₂.φH := by rw [eq]
lemma congr_φK {γ₁ γ₂ : LeftHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) : γ₁.φK = γ₂.φK := by rw [eq]

/-- When `S₁.f`, `S₁.g`, `S₂.f` and `S₂.g` are all zero, the action on left homology of a
morphism `φ : S₁ ⟶ S₂` is given by the action `φ.τ₂` on the middle objects. -/
@[simps]
def ofZeros (φ : S₁ ⟶ S₂) (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (hg₂ : S₂.g = 0) :
    LeftHomologyMapData φ (LeftHomologyData.ofZeros S₁ hf₁ hg₁)
      (LeftHomologyData.ofZeros S₂ hf₂ hg₂) where
  φK := φ.τ₂
  φH := φ.τ₂

/-- When `S₁.g` and `S₂.g` are zero and we have chosen colimit cokernel coforks `c₁` and `c₂`
for `S₁.f` and `S₂.f` respectively, the action on left homology of a morphism `φ : S₁ ⟶ S₂` of
short complexes is given by the unique morphism `f : c₁.pt ⟶ c₂.pt` such that
`φ.τ₂ ≫ c₂.π = c₁.π ≫ f`. -/
@[simps]
def ofIsColimitCokernelCofork (φ : S₁ ⟶ S₂)
    (hg₁ : S₁.g = 0) (c₁ : CokernelCofork S₁.f) (hc₁ : IsColimit c₁)
    (hg₂ : S₂.g = 0) (c₂ : CokernelCofork S₂.f) (hc₂ : IsColimit c₂) (f : c₁.pt ⟶ c₂.pt)
    (comm : φ.τ₂ ≫ c₂.π = c₁.π ≫ f) :
    LeftHomologyMapData φ (LeftHomologyData.ofIsColimitCokernelCofork S₁ hg₁ c₁ hc₁)
      (LeftHomologyData.ofIsColimitCokernelCofork S₂ hg₂ c₂ hc₂) where
  φK := φ.τ₂
  φH := f
  commπ := comm.symm
  commf' := by simp only [LeftHomologyData.ofIsColimitCokernelCofork_f', φ.comm₁₂]

/-- When `S₁.f` and `S₂.f` are zero and we have chosen limit kernel forks `c₁` and `c₂`
for `S₁.g` and `S₂.g` respectively, the action on left homology of a morphism `φ : S₁ ⟶ S₂` of
short complexes is given by the unique morphism `f : c₁.pt ⟶ c₂.pt` such that
`c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι`. -/
@[simps]
def ofIsLimitKernelFork (φ : S₁ ⟶ S₂)
    (hf₁ : S₁.f = 0) (c₁ : KernelFork S₁.g) (hc₁ : IsLimit c₁)
    (hf₂ : S₂.f = 0) (c₂ : KernelFork S₂.g) (hc₂ : IsLimit c₂) (f : c₁.pt ⟶ c₂.pt)
    (comm : c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι) :
    LeftHomologyMapData φ (LeftHomologyData.ofIsLimitKernelFork S₁ hf₁ c₁ hc₁)
      (LeftHomologyData.ofIsLimitKernelFork S₂ hf₂ c₂ hc₂) where
  φK := f
  φH := f
  commi := comm.symm

variable (S)

/-- When both maps `S.f` and `S.g` of a short complex `S` are zero, this is the homology map
data (for the identity of `S`) which relates the left homology data `ofZeros` and
`ofIsColimitCokernelCofork`. -/
@[simps]
def compatibilityOfZerosOfIsColimitCokernelCofork (hf : S.f = 0) (hg : S.g = 0)
    (c : CokernelCofork S.f) (hc : IsColimit c) :
    LeftHomologyMapData (𝟙 S) (LeftHomologyData.ofZeros S hf hg)
      (LeftHomologyData.ofIsColimitCokernelCofork S hg c hc) where
  φK := 𝟙 _
  φH := c.π

/-- When both maps `S.f` and `S.g` of a short complex `S` are zero, this is the homology map
data (for the identity of `S`) which relates the left homology data
`LeftHomologyData.ofIsLimitKernelFork` and `ofZeros` . -/
@[simps]
def compatibilityOfZerosOfIsLimitKernelFork (hf : S.f = 0) (hg : S.g = 0)
    (c : KernelFork S.g) (hc : IsLimit c) :
    LeftHomologyMapData (𝟙 S) (LeftHomologyData.ofIsLimitKernelFork S hf c hc)
      (LeftHomologyData.ofZeros S hf hg) where
  φK := c.ι
  φH := c.ι

end LeftHomologyMapData

end

section

variable (S)
variable [S.HasLeftHomology]

/-- The left homology of a short complex, given by the `H` field of a chosen left homology data.  -/
noncomputable def leftHomology : C := S.leftHomologyData.H

/-- The cycles of a short complex, given by the `K` field of a chosen left homology data.  -/
noncomputable def cycles : C := S.leftHomologyData.K

/-- The "homology class" map `S.cycles ⟶ S.leftHomology`. -/
noncomputable def leftHomologyπ : S.cycles ⟶ S.leftHomology := S.leftHomologyData.π

/-- The inclusion `S.cycles ⟶ S.X₂`. -/
noncomputable def iCycles : S.cycles ⟶ S.X₂ := S.leftHomologyData.i

/-- The "boundaries" map `S.X₁ ⟶ S.cycles`. (Note that in this homology API, we make no use
of the "image" of this morphism, which under some categorical assumptions would be a subobject
of `S.X₂` contained in `S.cycles`.) -/
noncomputable def toCycles : S.X₁ ⟶ S.cycles := S.leftHomologyData.f'

@[reassoc (attr := simp)]
lemma iCycles_g : S.iCycles ≫ S.g = 0 := S.leftHomologyData.wi

@[reassoc (attr := simp)]
lemma toCycles_i : S.toCycles ≫ S.iCycles = S.f := S.leftHomologyData.f'_i

instance : Mono S.iCycles := by
  dsimp only [iCycles]
  infer_instance

instance : Epi S.leftHomologyπ := by
  dsimp only [leftHomologyπ]
  infer_instance

end

section

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)

/-- The (unique) left homology map data associated to a morphism of short complexes that
are both equipped with left homology data. -/
def leftHomologyMapData : LeftHomologyMapData φ h₁ h₂ := default

/-- Given a morphism `φ : S₁ ⟶ S₂` of short complexes and left homology data `h₁` and `h₂`
for `S₁` and `S₂` respectively, this is the induced left homology map `h₁.H ⟶ h₁.H`. -/
def leftHomologyMap' : h₁.H ⟶ h₂.H := (leftHomologyMapData φ _ _).φH

/-- Given a morphism `φ : S₁ ⟶ S₂` of short complexes and left homology data `h₁` and `h₂`
for `S₁` and `S₂` respectively, this is the induced morphism `h₁.K ⟶ h₁.K` on cycles. -/
def cyclesMap' : h₁.K ⟶ h₂.K := (leftHomologyMapData φ _ _).φK

@[reassoc (attr := simp)]
lemma cyclesMap'_i : cyclesMap' φ h₁ h₂ ≫ h₂.i = h₁.i ≫ φ.τ₂ :=
  LeftHomologyMapData.commi _

@[reassoc (attr := simp)]
lemma f'_cyclesMap' : h₁.f' ≫ cyclesMap' φ h₁ h₂ = φ.τ₁ ≫ h₂.f' := by
  simp only [← cancel_mono h₂.i, assoc, φ.comm₁₂, cyclesMap'_i,
    LeftHomologyData.f'_i_assoc, LeftHomologyData.f'_i]

@[reassoc (attr := simp)]
lemma leftHomologyπ_naturality' :
    h₁.π ≫ leftHomologyMap' φ h₁ h₂ = cyclesMap' φ h₁ h₂ ≫ h₂.π :=
  LeftHomologyMapData.commπ _

end

section

variable [HasLeftHomology S₁] [HasLeftHomology S₂] (φ : S₁ ⟶ S₂)

/-- The (left) homology map `S₁.leftHomology ⟶ S₂.leftHomology` induced by a morphism
`S₁ ⟶ S₂` of short complexes. -/
noncomputable def leftHomologyMap : S₁.leftHomology ⟶ S₂.leftHomology :=
  leftHomologyMap' φ _ _

/-- The morphism `S₁.cycles ⟶ S₂.cycles` induced by a morphism `S₁ ⟶ S₂` of short complexes. -/
noncomputable def cyclesMap : S₁.cycles ⟶ S₂.cycles := cyclesMap' φ _ _

@[reassoc (attr := simp)]
lemma cyclesMap_i : cyclesMap φ ≫ S₂.iCycles = S₁.iCycles ≫ φ.τ₂ :=
  cyclesMap'_i _ _ _

@[reassoc (attr := simp)]
lemma toCycles_naturality : S₁.toCycles ≫ cyclesMap φ = φ.τ₁ ≫ S₂.toCycles :=
  f'_cyclesMap' _ _ _

@[reassoc (attr := simp)]
lemma leftHomologyπ_naturality :
    S₁.leftHomologyπ ≫ leftHomologyMap φ = cyclesMap φ ≫ S₂.leftHomologyπ :=
  leftHomologyπ_naturality' _ _ _

end

end ShortComplex

end CategoryTheory
