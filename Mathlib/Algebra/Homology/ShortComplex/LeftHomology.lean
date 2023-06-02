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
and (TODO) we shall define `S.leftHomology` to be the `H` field of a chosen left homology data.
Similarly, we shall define `S.cycles` to be the `K` field.

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

end LeftHomologyMapData

end

end ShortComplex

end CategoryTheory
