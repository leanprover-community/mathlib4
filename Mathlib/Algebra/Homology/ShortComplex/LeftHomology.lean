/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Left Homology of short complexes

Given a short complex `S : ShortComplex C`, which consists of two composable
maps `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` such that `f ≫ g = 0`, we shall define
here the "left homology" `S.leftHomology` of `S`. For this, we introduce the
notion of "left homology data". Such an `h : S.LeftHomologyData` consists of the
data of morphisms `i : K ⟶ X₂` and `π : K ⟶ H` such that `i` identifies
`K` with the kernel of `g : X₂ ⟶ X₃`, and that `π` identifies `H` with the cokernel
of the induced map `f' : X₁ ⟶ K`.

When such a `S.LeftHomologyData` exists, we shall say that `[S.HasLeftHomology]`
and we define `S.leftHomology` to be the `H` field of a chosen left homology data.
Similarly, we define `S.cycles` to be the `K` field.

The dual notion is defined in `RightHomologyData.lean`. In `Homology.lean`,
when `S` has two compatible left and right homology data (i.e. they give
the same `H` up to a canonical isomorphism), we shall define `[S.HasHomology]`
and `S.homology`.

-/

namespace CategoryTheory

open Category Limits

namespace ShortComplex

variable {C : Type*} [Category C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

/-- A left homology data for a short complex `S` consists of morphisms `i : K ⟶ S.X₂` and
`π : K ⟶ H` such that `i` identifies `K` to the kernel of `g : S.X₂ ⟶ S.X₃`,
and that `π` identifies `H` to the cokernel of the induced map `f' : S.X₁ ⟶ K` -/
structure LeftHomologyData where
  /-- a choice of kernel of `S.g : S.X₂ ⟶ S.X₃` -/
  K : C
  /-- a choice of cokernel of the induced morphism `S.f' : S.X₁ ⟶ K` -/
  H : C
  /-- the inclusion of cycles in `S.X₂` -/
  i : K ⟶ S.X₂
  /-- the projection from cycles to the (left) homology -/
  π : K ⟶ H
  /-- the kernel condition for `i` -/
  wi : i ≫ S.g = 0
  /-- `i : K ⟶ S.X₂` is a kernel of `g : S.X₂ ⟶ S.X₃` -/
  hi : IsLimit (KernelFork.ofι i wi)
  /-- the cokernel condition for `π` -/
  wπ : hi.lift (KernelFork.ofι _ S.zero) ≫ π = 0
  /-- `π : K ⟶ H` is a cokernel of the induced morphism `S.f' : S.X₁ ⟶ K` -/
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

lemma isIso_i (hg : S.g = 0) : IsIso h.i :=
  ⟨h.liftK (𝟙 S.X₂) (by rw [hg, id_comp]),
    by simp only [← cancel_mono h.i, id_comp, assoc, liftK_i, comp_id], liftK_i _ _ _⟩

lemma isIso_π (hf : S.f = 0) : IsIso h.π := by
  have ⟨φ, hφ⟩ := CokernelCofork.IsColimit.desc' h.hπ' (𝟙 _)
    (by rw [← cancel_mono h.i, comp_id, f'_i, zero_comp, hf])
  dsimp at hφ
  exact ⟨φ, hφ, by rw [← cancel_epi h.π, reassoc_of% hφ, comp_id]⟩

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
  hπ := IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _))

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
  hi := IsLimit.ofIsoLimit hc (Fork.ext (Iso.refl _))
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

variable {S} in
/-- Given a left homology data `h` of a short complex `S`, we can construct another left homology
data by choosing another kernel and cokernel that are isomorphic to the ones in `h`. -/
@[simps] def copy {K' H' : C} (eK : K' ≅ h.K) (eH : H' ≅ h.H) : S.LeftHomologyData where
  K := K'
  H := H'
  i := eK.hom ≫ h.i
  π := eK.hom ≫ h.π ≫ eH.inv
  wi := by rw [assoc, h.wi, comp_zero]
  hi := IsKernel.isoKernel _ _ h.hi eK (by simp)
  wπ := by simp [IsKernel.isoKernel]
  hπ := IsColimit.equivOfNatIsoOfIso
    (parallelPair.ext (Iso.refl S.X₁) eK.symm (by simp [IsKernel.isoKernel]) (by simp)) _ _
    (Cocones.ext (by exact eH.symm) (by rintro (_ | _) <;> simp [IsKernel.isoKernel])) h.hπ

end LeftHomologyData

/-- A short complex `S` has left homology when there exists a `S.LeftHomologyData` -/
class HasLeftHomology : Prop where
  condition : Nonempty S.LeftHomologyData

/-- A chosen `S.LeftHomologyData` for a short complex `S` that has left homology -/
noncomputable def leftHomologyData [S.HasLeftHomology] : S.LeftHomologyData :=
  HasLeftHomology.condition.some

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
  exact ⟨φK, φH, by simp [φK], commf', by simp [φH]⟩⟩

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

/-- When both maps `S.f` and `S.g` of a short complex `S` are zero, this is the left homology map
data (for the identity of `S`) which relates the left homology data `ofZeros` and
`ofIsColimitCokernelCofork`. -/
@[simps]
def compatibilityOfZerosOfIsColimitCokernelCofork (hf : S.f = 0) (hg : S.g = 0)
    (c : CokernelCofork S.f) (hc : IsColimit c) :
    LeftHomologyMapData (𝟙 S) (LeftHomologyData.ofZeros S hf hg)
      (LeftHomologyData.ofIsColimitCokernelCofork S hg c hc) where
  φK := 𝟙 _
  φH := c.π

/-- When both maps `S.f` and `S.g` of a short complex `S` are zero, this is the left homology map
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

/-- The left homology of a short complex, given by the `H` field of a chosen left homology data. -/
noncomputable def leftHomology : C := S.leftHomologyData.H

-- `S.leftHomology` is the simp normal form.
@[simp] lemma leftHomologyData_H : S.leftHomologyData.H = S.leftHomology := rfl

/-- The cycles of a short complex, given by the `K` field of a chosen left homology data. -/
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

lemma leftHomology_ext_iff {A : C} (f₁ f₂ : S.leftHomology ⟶ A) :
    f₁ = f₂ ↔ S.leftHomologyπ ≫ f₁ = S.leftHomologyπ ≫ f₂ := by
  rw [cancel_epi]

@[ext]
lemma leftHomology_ext {A : C} (f₁ f₂ : S.leftHomology ⟶ A)
    (h : S.leftHomologyπ ≫ f₁ = S.leftHomologyπ ≫ f₂) : f₁ = f₂ := by
  simpa only [leftHomology_ext_iff] using h

lemma cycles_ext_iff {A : C} (f₁ f₂ : A ⟶ S.cycles) :
    f₁ = f₂ ↔ f₁ ≫ S.iCycles = f₂ ≫ S.iCycles := by
  rw [cancel_mono]

@[ext]
lemma cycles_ext {A : C} (f₁ f₂ : A ⟶ S.cycles) (h : f₁ ≫ S.iCycles = f₂ ≫ S.iCycles) :
    f₁ = f₂ := by
  simpa only [cycles_ext_iff] using h

lemma isIso_iCycles (hg : S.g = 0) : IsIso S.iCycles :=
  LeftHomologyData.isIso_i _ hg

/-- When `S.g = 0`, this is the canonical isomorphism `S.cycles ≅ S.X₂` induced by `S.iCycles`. -/
@[simps! hom]
noncomputable def cyclesIsoX₂ (hg : S.g = 0) : S.cycles ≅ S.X₂ := by
  have := S.isIso_iCycles hg
  exact asIso S.iCycles

@[reassoc (attr := simp)]
lemma cyclesIsoX₂_hom_inv_id (hg : S.g = 0) :
    S.iCycles ≫ (S.cyclesIsoX₂ hg).inv = 𝟙 _ := (S.cyclesIsoX₂ hg).hom_inv_id

@[reassoc (attr := simp)]
lemma cyclesIsoX₂_inv_hom_id (hg : S.g = 0) :
    (S.cyclesIsoX₂ hg).inv ≫ S.iCycles = 𝟙 _ := (S.cyclesIsoX₂ hg).inv_hom_id

lemma isIso_leftHomologyπ (hf : S.f = 0) : IsIso S.leftHomologyπ :=
  LeftHomologyData.isIso_π _ hf

/-- When `S.f = 0`, this is the canonical isomorphism `S.cycles ≅ S.leftHomology` induced
by `S.leftHomologyπ`. -/
@[simps! hom]
noncomputable def cyclesIsoLeftHomology (hf : S.f = 0) : S.cycles ≅ S.leftHomology := by
  have := S.isIso_leftHomologyπ hf
  exact asIso S.leftHomologyπ

@[reassoc (attr := simp)]
lemma cyclesIsoLeftHomology_hom_inv_id (hf : S.f = 0) :
    S.leftHomologyπ ≫ (S.cyclesIsoLeftHomology hf).inv = 𝟙 _ :=
  (S.cyclesIsoLeftHomology hf).hom_inv_id

@[reassoc (attr := simp)]
lemma cyclesIsoLeftHomology_inv_hom_id (hf : S.f = 0) :
    (S.cyclesIsoLeftHomology hf).inv ≫ S.leftHomologyπ = 𝟙 _ :=
  (S.cyclesIsoLeftHomology hf).inv_hom_id

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

namespace LeftHomologyMapData

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}
  (γ : LeftHomologyMapData φ h₁ h₂)

lemma leftHomologyMap'_eq : leftHomologyMap' φ h₁ h₂ = γ.φH :=
  LeftHomologyMapData.congr_φH (Subsingleton.elim _ _)

lemma cyclesMap'_eq : cyclesMap' φ h₁ h₂ = γ.φK :=
  LeftHomologyMapData.congr_φK (Subsingleton.elim _ _)

end LeftHomologyMapData

@[simp]
lemma leftHomologyMap'_id (h : S.LeftHomologyData) :
    leftHomologyMap' (𝟙 S) h h = 𝟙 _ :=
  (LeftHomologyMapData.id h).leftHomologyMap'_eq

@[simp]
lemma cyclesMap'_id (h : S.LeftHomologyData) :
    cyclesMap' (𝟙 S) h h = 𝟙 _ :=
  (LeftHomologyMapData.id h).cyclesMap'_eq

variable (S)

@[simp]
lemma leftHomologyMap_id [HasLeftHomology S] :
    leftHomologyMap (𝟙 S) = 𝟙 _ :=
  leftHomologyMap'_id _

@[simp]
lemma cyclesMap_id [HasLeftHomology S] :
    cyclesMap (𝟙 S) = 𝟙 _ :=
  cyclesMap'_id _

@[simp]
lemma leftHomologyMap'_zero (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    leftHomologyMap' 0 h₁ h₂ = 0 :=
  (LeftHomologyMapData.zero h₁ h₂).leftHomologyMap'_eq

@[simp]
lemma cyclesMap'_zero (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    cyclesMap' 0 h₁ h₂ = 0 :=
  (LeftHomologyMapData.zero h₁ h₂).cyclesMap'_eq

variable (S₁ S₂)

@[simp]
lemma leftHomologyMap_zero [HasLeftHomology S₁] [HasLeftHomology S₂] :
    leftHomologyMap (0 : S₁ ⟶ S₂) = 0 :=
  leftHomologyMap'_zero _ _

@[simp]
lemma cyclesMap_zero [HasLeftHomology S₁] [HasLeftHomology S₂] :
    cyclesMap (0 : S₁ ⟶ S₂) = 0 :=
  cyclesMap'_zero _ _

variable {S₁ S₂}

@[reassoc]
lemma leftHomologyMap'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) (h₃ : S₃.LeftHomologyData) :
    leftHomologyMap' (φ₁ ≫ φ₂) h₁ h₃ = leftHomologyMap' φ₁ h₁ h₂ ≫
      leftHomologyMap' φ₂ h₂ h₃ := by
  let γ₁ := leftHomologyMapData φ₁ h₁ h₂
  let γ₂ := leftHomologyMapData φ₂ h₂ h₃
  rw [γ₁.leftHomologyMap'_eq, γ₂.leftHomologyMap'_eq, (γ₁.comp γ₂).leftHomologyMap'_eq,
    LeftHomologyMapData.comp_φH]

@[reassoc]
lemma cyclesMap'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) (h₃ : S₃.LeftHomologyData) :
    cyclesMap' (φ₁ ≫ φ₂) h₁ h₃ = cyclesMap' φ₁ h₁ h₂ ≫ cyclesMap' φ₂ h₂ h₃ := by
  let γ₁ := leftHomologyMapData φ₁ h₁ h₂
  let γ₂ := leftHomologyMapData φ₂ h₂ h₃
  rw [γ₁.cyclesMap'_eq, γ₂.cyclesMap'_eq, (γ₁.comp γ₂).cyclesMap'_eq,
    LeftHomologyMapData.comp_φK]

@[reassoc]
lemma leftHomologyMap_comp [HasLeftHomology S₁] [HasLeftHomology S₂] [HasLeftHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    leftHomologyMap (φ₁ ≫ φ₂) = leftHomologyMap φ₁ ≫ leftHomologyMap φ₂ :=
  leftHomologyMap'_comp _ _ _ _ _

@[reassoc]
lemma cyclesMap_comp [HasLeftHomology S₁] [HasLeftHomology S₂] [HasLeftHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    cyclesMap (φ₁ ≫ φ₂) = cyclesMap φ₁ ≫ cyclesMap φ₂ :=
  cyclesMap'_comp _ _ _ _ _

attribute [simp] leftHomologyMap_comp cyclesMap_comp

/-- An isomorphism of short complexes `S₁ ≅ S₂` induces an isomorphism on the `H` fields
of left homology data of `S₁` and `S₂`. -/
@[simps]
def leftHomologyMapIso' (e : S₁ ≅ S₂) (h₁ : S₁.LeftHomologyData)
    (h₂ : S₂.LeftHomologyData) : h₁.H ≅ h₂.H where
  hom := leftHomologyMap' e.hom h₁ h₂
  inv := leftHomologyMap' e.inv h₂ h₁
  hom_inv_id := by rw [← leftHomologyMap'_comp, e.hom_inv_id, leftHomologyMap'_id]
  inv_hom_id := by rw [← leftHomologyMap'_comp, e.inv_hom_id, leftHomologyMap'_id]

instance isIso_leftHomologyMap'_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ]
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    IsIso (leftHomologyMap' φ h₁ h₂) :=
  (inferInstance : IsIso (leftHomologyMapIso' (asIso φ) h₁ h₂).hom)

/-- An isomorphism of short complexes `S₁ ≅ S₂` induces an isomorphism on the `K` fields
of left homology data of `S₁` and `S₂`. -/
@[simps]
def cyclesMapIso' (e : S₁ ≅ S₂) (h₁ : S₁.LeftHomologyData)
    (h₂ : S₂.LeftHomologyData) : h₁.K ≅ h₂.K where
  hom := cyclesMap' e.hom h₁ h₂
  inv := cyclesMap' e.inv h₂ h₁
  hom_inv_id := by rw [← cyclesMap'_comp, e.hom_inv_id, cyclesMap'_id]
  inv_hom_id := by rw [← cyclesMap'_comp, e.inv_hom_id, cyclesMap'_id]

instance isIso_cyclesMap'_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ]
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    IsIso (cyclesMap' φ h₁ h₂) :=
  (inferInstance : IsIso (cyclesMapIso' (asIso φ) h₁ h₂).hom)

/-- The isomorphism `S₁.leftHomology ≅ S₂.leftHomology` induced by an isomorphism of
short complexes `S₁ ≅ S₂`. -/
@[simps]
noncomputable def leftHomologyMapIso (e : S₁ ≅ S₂) [S₁.HasLeftHomology]
    [S₂.HasLeftHomology] : S₁.leftHomology ≅ S₂.leftHomology where
  hom := leftHomologyMap e.hom
  inv := leftHomologyMap e.inv
  hom_inv_id := by rw [← leftHomologyMap_comp, e.hom_inv_id, leftHomologyMap_id]
  inv_hom_id := by rw [← leftHomologyMap_comp, e.inv_hom_id, leftHomologyMap_id]

instance isIso_leftHomologyMap_of_iso (φ : S₁ ⟶ S₂)
    [IsIso φ] [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    IsIso (leftHomologyMap φ) :=
  (inferInstance : IsIso (leftHomologyMapIso (asIso φ)).hom)

/-- The isomorphism `S₁.cycles ≅ S₂.cycles` induced by an isomorphism
of short complexes `S₁ ≅ S₂`. -/
@[simps]
noncomputable def cyclesMapIso (e : S₁ ≅ S₂) [S₁.HasLeftHomology]
    [S₂.HasLeftHomology] : S₁.cycles ≅ S₂.cycles where
  hom := cyclesMap e.hom
  inv := cyclesMap e.inv
  hom_inv_id := by rw [← cyclesMap_comp, e.hom_inv_id, cyclesMap_id]
  inv_hom_id := by rw [← cyclesMap_comp, e.inv_hom_id, cyclesMap_id]

instance isIso_cyclesMap_of_iso (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasLeftHomology]
    [S₂.HasLeftHomology] : IsIso (cyclesMap φ) :=
  (inferInstance : IsIso (cyclesMapIso (asIso φ)).hom)

variable {S}

namespace LeftHomologyData

variable (h : S.LeftHomologyData) [S.HasLeftHomology]

/-- The isomorphism `S.leftHomology ≅ h.H` induced by a left homology data `h` for a
short complex `S`. -/
noncomputable def leftHomologyIso : S.leftHomology ≅ h.H :=
  leftHomologyMapIso' (Iso.refl _) _ _

/-- The isomorphism `S.cycles ≅ h.K` induced by a left homology data `h` for a
short complex `S`. -/
noncomputable def cyclesIso : S.cycles ≅ h.K :=
  cyclesMapIso' (Iso.refl _) _ _

@[reassoc (attr := simp)]
lemma cyclesIso_hom_comp_i : h.cyclesIso.hom ≫ h.i = S.iCycles := by
  dsimp [iCycles, LeftHomologyData.cyclesIso]
  simp only [cyclesMap'_i, id_τ₂, comp_id]

@[reassoc (attr := simp)]
lemma cyclesIso_inv_comp_iCycles : h.cyclesIso.inv ≫ S.iCycles = h.i := by
  simp only [← h.cyclesIso_hom_comp_i, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
lemma leftHomologyπ_comp_leftHomologyIso_hom :
    S.leftHomologyπ ≫ h.leftHomologyIso.hom = h.cyclesIso.hom ≫ h.π := by
  dsimp only [leftHomologyπ, leftHomologyIso, cyclesIso, leftHomologyMapIso',
    cyclesMapIso', Iso.refl]
  rw [← leftHomologyπ_naturality']

@[reassoc (attr := simp)]
lemma π_comp_leftHomologyIso_inv :
    h.π ≫ h.leftHomologyIso.inv = h.cyclesIso.inv ≫ S.leftHomologyπ := by
  simp only [← cancel_epi h.cyclesIso.hom, ← cancel_mono h.leftHomologyIso.hom, assoc,
    Iso.inv_hom_id, comp_id, Iso.hom_inv_id_assoc,
    LeftHomologyData.leftHomologyπ_comp_leftHomologyIso_hom]

end LeftHomologyData

namespace LeftHomologyMapData

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}
  (γ : LeftHomologyMapData φ h₁ h₂)

lemma leftHomologyMap_eq [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    leftHomologyMap φ = h₁.leftHomologyIso.hom ≫ γ.φH ≫ h₂.leftHomologyIso.inv := by
  dsimp [LeftHomologyData.leftHomologyIso, leftHomologyMapIso']
  rw [← γ.leftHomologyMap'_eq, ← leftHomologyMap'_comp,
    ← leftHomologyMap'_comp, id_comp, comp_id]
  rfl

lemma cyclesMap_eq [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    cyclesMap φ = h₁.cyclesIso.hom ≫ γ.φK ≫ h₂.cyclesIso.inv := by
  dsimp [LeftHomologyData.cyclesIso, cyclesMapIso']
  rw [← γ.cyclesMap'_eq, ← cyclesMap'_comp, ← cyclesMap'_comp, id_comp, comp_id]
  rfl

lemma leftHomologyMap_comm [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    leftHomologyMap φ ≫ h₂.leftHomologyIso.hom = h₁.leftHomologyIso.hom ≫ γ.φH := by
  simp only [γ.leftHomologyMap_eq, assoc, Iso.inv_hom_id, comp_id]

lemma cyclesMap_comm [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    cyclesMap φ ≫ h₂.cyclesIso.hom = h₁.cyclesIso.hom ≫ γ.φK := by
  simp only [γ.cyclesMap_eq, assoc, Iso.inv_hom_id, comp_id]

end LeftHomologyMapData

section

variable (C)
variable [HasKernels C] [HasCokernels C]

/-- The left homology functor `ShortComplex C ⥤ C`, where the left homology of a
short complex `S` is understood as a cokernel of the obvious map `S.toCycles : S.X₁ ⟶ S.cycles`
where `S.cycles` is a kernel of `S.g : S.X₂ ⟶ S.X₃`. -/
@[simps]
noncomputable def leftHomologyFunctor : ShortComplex C ⥤ C where
  obj S := S.leftHomology
  map := leftHomologyMap

/-- The cycles functor `ShortComplex C ⥤ C` which sends a short complex `S` to `S.cycles`
which is a kernel of `S.g : S.X₂ ⟶ S.X₃`. -/
@[simps]
noncomputable def cyclesFunctor : ShortComplex C ⥤ C where
  obj S := S.cycles
  map := cyclesMap

/-- The natural transformation `S.cycles ⟶ S.leftHomology` for all short complexes `S`. -/
@[simps]
noncomputable def leftHomologyπNatTrans : cyclesFunctor C ⟶ leftHomologyFunctor C where
  app S := leftHomologyπ S
  naturality := fun _ _ φ => (leftHomologyπ_naturality φ).symm

/-- The natural transformation `S.cycles ⟶ S.X₂` for all short complexes `S`. -/
@[simps]
noncomputable def iCyclesNatTrans : cyclesFunctor C ⟶ ShortComplex.π₂ where
  app S := S.iCycles

/-- The natural transformation `S.X₁ ⟶ S.cycles` for all short complexes `S`. -/
@[simps]
noncomputable def toCyclesNatTrans :
    π₁ ⟶ cyclesFunctor C where
  app S := S.toCycles
  naturality := fun _ _ φ => (toCycles_naturality φ).symm

end

namespace LeftHomologyData

/-- If `φ : S₁ ⟶ S₂` is a morphism of short complexes such that `φ.τ₁` is epi, `φ.τ₂` is an iso
and `φ.τ₃` is mono, then a left homology data for `S₁` induces a left homology data for `S₂` with
the same `K` and `H` fields. The inverse construction is `ofEpiOfIsIsoOfMono'`. -/
@[simps]
noncomputable def ofEpiOfIsIsoOfMono (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₁)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : LeftHomologyData S₂ := by
  let i : h.K ⟶ S₂.X₂ := h.i ≫ φ.τ₂
  have wi : i ≫ S₂.g = 0 := by simp only [i, assoc, φ.comm₂₃, h.wi_assoc, zero_comp]
  have hi : IsLimit (KernelFork.ofι i wi) := KernelFork.IsLimit.ofι _ _
    (fun x hx => h.liftK (x ≫ inv φ.τ₂) (by rw [assoc, ← cancel_mono φ.τ₃, assoc,
      assoc, ← φ.comm₂₃, IsIso.inv_hom_id_assoc, hx, zero_comp]))
    (fun x hx => by simp [i]) (fun x hx b hb => by
      dsimp
      rw [← cancel_mono h.i, ← cancel_mono φ.τ₂, assoc, assoc, liftK_i_assoc,
        assoc, IsIso.inv_hom_id, comp_id, hb])
  let f' := hi.lift (KernelFork.ofι S₂.f S₂.zero)
  have hf' : φ.τ₁ ≫ f' = h.f' := by
    have eq := @Fork.IsLimit.lift_ι _ _ _ _ _ _ _ ((KernelFork.ofι S₂.f S₂.zero)) hi
    simp only [Fork.ι_ofι] at eq
    rw [← cancel_mono h.i, ← cancel_mono φ.τ₂, assoc, assoc, eq, f'_i, φ.comm₁₂]
  have wπ : f' ≫ h.π = 0 := by
    rw [← cancel_epi φ.τ₁, comp_zero, reassoc_of% hf', h.f'_π]
  have hπ : IsColimit (CokernelCofork.ofπ h.π wπ) := CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => h.descH x (by rw [← hf', assoc, hx, comp_zero]))
    (fun x hx => by simp) (fun x hx b hb => by rw [← cancel_epi h.π, π_descH, hb])
  exact ⟨h.K, h.H, i, h.π, wi, hi, wπ, hπ⟩

@[simp]
lemma τ₁_ofEpiOfIsIsoOfMono_f' (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₁)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : φ.τ₁ ≫ (ofEpiOfIsIsoOfMono φ h).f' = h.f' := by
  rw [← cancel_mono (ofEpiOfIsIsoOfMono φ h).i, assoc, f'_i,
    ofEpiOfIsIsoOfMono_i, f'_i_assoc, φ.comm₁₂]

/-- If `φ : S₁ ⟶ S₂` is a morphism of short complexes such that `φ.τ₁` is epi, `φ.τ₂` is an iso
and `φ.τ₃` is mono, then a left homology data for `S₂` induces a left homology data for `S₁` with
the same `K` and `H` fields. The inverse construction is `ofEpiOfIsIsoOfMono`. -/
@[simps]
noncomputable def ofEpiOfIsIsoOfMono' (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₂)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : LeftHomologyData S₁ := by
  let i : h.K ⟶ S₁.X₂ := h.i ≫ inv φ.τ₂
  have wi : i ≫ S₁.g = 0 := by
    rw [assoc, ← cancel_mono φ.τ₃, zero_comp, assoc, assoc, ← φ.comm₂₃,
      IsIso.inv_hom_id_assoc, h.wi]
  have hi : IsLimit (KernelFork.ofι i wi) := KernelFork.IsLimit.ofι _ _
    (fun x hx => h.liftK (x ≫ φ.τ₂)
      (by rw [assoc, φ.comm₂₃, reassoc_of% hx, zero_comp]))
    (fun x hx => by simp [i])
    (fun x hx b hb => by rw [← cancel_mono h.i, ← cancel_mono (inv φ.τ₂), assoc, assoc,
      hb, liftK_i_assoc, assoc, IsIso.hom_inv_id, comp_id])
  let f' := hi.lift (KernelFork.ofι S₁.f S₁.zero)
  have hf' : f' ≫ i = S₁.f := Fork.IsLimit.lift_ι _
  have hf'' : f' = φ.τ₁ ≫ h.f' := by
    rw [← cancel_mono h.i, ← cancel_mono (inv φ.τ₂), assoc, assoc, assoc, hf', f'_i_assoc,
      φ.comm₁₂_assoc, IsIso.hom_inv_id, comp_id]
  have wπ : f' ≫ h.π = 0 := by simp only [hf'', assoc, f'_π, comp_zero]
  have hπ : IsColimit (CokernelCofork.ofπ h.π wπ) := CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => h.descH x (by rw [← cancel_epi φ.τ₁, ← reassoc_of% hf'', hx, comp_zero]))
    (fun x hx => π_descH _ _ _)
    (fun x hx b hx => by rw [← cancel_epi h.π, π_descH, hx])
  exact ⟨h.K, h.H, i, h.π, wi, hi, wπ, hπ⟩

@[simp]
lemma ofEpiOfIsIsoOfMono'_f' (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₂)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : (ofEpiOfIsIsoOfMono' φ h).f' = φ.τ₁ ≫ h.f' := by
  rw [← cancel_mono (ofEpiOfIsIsoOfMono' φ h).i, f'_i, ofEpiOfIsIsoOfMono'_i,
    assoc, f'_i_assoc, φ.comm₁₂_assoc, IsIso.hom_inv_id, comp_id]

/-- If `e : S₁ ≅ S₂` is an isomorphism of short complexes and `h₁ : LeftHomologyData S₁`,
this is the left homology data for `S₂` deduced from the isomorphism. -/
noncomputable def ofIso (e : S₁ ≅ S₂) (h₁ : LeftHomologyData S₁) : LeftHomologyData S₂ :=
  h₁.ofEpiOfIsIsoOfMono e.hom

end LeftHomologyData

lemma hasLeftHomology_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [HasLeftHomology S₁]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasLeftHomology S₂ :=
  HasLeftHomology.mk' (LeftHomologyData.ofEpiOfIsIsoOfMono φ S₁.leftHomologyData)

lemma hasLeftHomology_of_epi_of_isIso_of_mono' (φ : S₁ ⟶ S₂) [HasLeftHomology S₂]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasLeftHomology S₁ :=
  HasLeftHomology.mk' (LeftHomologyData.ofEpiOfIsIsoOfMono' φ S₂.leftHomologyData)

lemma hasLeftHomology_of_iso {S₁ S₂ : ShortComplex C} (e : S₁ ≅ S₂) [HasLeftHomology S₁] :
    HasLeftHomology S₂ :=
  hasLeftHomology_of_epi_of_isIso_of_mono e.hom

namespace LeftHomologyMapData

/-- This left homology map data expresses compatibilities of the left homology data
constructed by `LeftHomologyData.ofEpiOfIsIsoOfMono` -/
@[simps]
noncomputable def ofEpiOfIsIsoOfMono (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₁)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    LeftHomologyMapData φ h (LeftHomologyData.ofEpiOfIsIsoOfMono φ h) where
  φK := 𝟙 _
  φH := 𝟙 _

/-- This left homology map data expresses compatibilities of the left homology data
constructed by `LeftHomologyData.ofEpiOfIsIsoOfMono'` -/
@[simps]
noncomputable def ofEpiOfIsIsoOfMono' (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₂)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    LeftHomologyMapData φ (LeftHomologyData.ofEpiOfIsIsoOfMono' φ h) h where
  φK := 𝟙 _
  φH := 𝟙 _

end LeftHomologyMapData

instance (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso (leftHomologyMap' φ h₁ h₂) := by
  let h₂' := LeftHomologyData.ofEpiOfIsIsoOfMono φ h₁
  have : IsIso (leftHomologyMap' φ h₁ h₂') := by
    rw [(LeftHomologyMapData.ofEpiOfIsIsoOfMono φ h₁).leftHomologyMap'_eq]
    dsimp
    infer_instance
  have eq := leftHomologyMap'_comp φ (𝟙 S₂) h₁ h₂' h₂
  rw [comp_id] at eq
  rw [eq]
  infer_instance

/-- If a morphism of short complexes `φ : S₁ ⟶ S₂` is such that `φ.τ₁` is epi, `φ.τ₂` is an iso,
and `φ.τ₃` is mono, then the induced morphism on left homology is an isomorphism. -/
instance (φ : S₁ ⟶ S₂) [S₁.HasLeftHomology] [S₂.HasLeftHomology]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso (leftHomologyMap φ) := by
  dsimp only [leftHomologyMap]
  infer_instance

section

variable (S) (h : LeftHomologyData S) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0)
  [HasLeftHomology S]

/-- A morphism `k : A ⟶ S.X₂` such that `k ≫ S.g = 0` lifts to a morphism `A ⟶ S.cycles`. -/
noncomputable def liftCycles : A ⟶ S.cycles :=
  S.leftHomologyData.liftK k hk

@[reassoc (attr := simp)]
lemma liftCycles_i : S.liftCycles k hk ≫ S.iCycles = k :=
  LeftHomologyData.liftK_i _ k hk

@[reassoc]
lemma comp_liftCycles {A' : C} (α : A' ⟶ A) :
    α ≫ S.liftCycles k hk = S.liftCycles (α ≫ k) (by rw [assoc, hk, comp_zero]) := by aesop_cat

/-- Via `S.iCycles : S.cycles ⟶ S.X₂`, the object `S.cycles` identifies to the
kernel of `S.g : S.X₂ ⟶ S.X₃`. -/
noncomputable def cyclesIsKernel : IsLimit (KernelFork.ofι S.iCycles S.iCycles_g) :=
  S.leftHomologyData.hi

/-- The canonical isomorphism `S.cycles ≅ kernel S.g`. -/
@[simps]
noncomputable def cyclesIsoKernel [HasKernel S.g] : S.cycles ≅ kernel S.g where
  hom := kernel.lift S.g S.iCycles (by simp)
  inv := S.liftCycles (kernel.ι S.g) (by simp)

/-- The morphism `A ⟶ S.leftHomology` obtained from a morphism `k : A ⟶ S.X₂`
such that `k ≫ S.g = 0.` -/
@[simp]
noncomputable def liftLeftHomology : A ⟶ S.leftHomology :=
  S.liftCycles k hk ≫ S.leftHomologyπ

@[reassoc]
lemma liftCycles_leftHomologyπ_eq_zero_of_boundary (x : A ⟶ S.X₁) (hx : k = x ≫ S.f) :
    S.liftCycles k (by rw [hx, assoc, S.zero, comp_zero]) ≫ S.leftHomologyπ = 0 :=
  LeftHomologyData.liftK_π_eq_zero_of_boundary _ k x hx

@[reassoc (attr := simp)]
lemma toCycles_comp_leftHomologyπ : S.toCycles ≫ S.leftHomologyπ = 0 :=
  S.liftCycles_leftHomologyπ_eq_zero_of_boundary S.f (𝟙 _) (by rw [id_comp])

/-- Via `S.leftHomologyπ : S.cycles ⟶ S.leftHomology`, the object `S.leftHomology` identifies
to the cokernel of `S.toCycles : S.X₁ ⟶ S.cycles`. -/
noncomputable def leftHomologyIsCokernel :
    IsColimit (CokernelCofork.ofπ S.leftHomologyπ S.toCycles_comp_leftHomologyπ) :=
  S.leftHomologyData.hπ

@[reassoc (attr := simp)]
lemma liftCycles_comp_cyclesMap (φ : S ⟶ S₁) [S₁.HasLeftHomology] :
    S.liftCycles k hk ≫ cyclesMap φ =
      S₁.liftCycles (k ≫ φ.τ₂) (by rw [assoc, φ.comm₂₃, reassoc_of% hk, zero_comp]) := by
  aesop_cat

variable {S}

@[reassoc (attr := simp)]
lemma LeftHomologyData.liftCycles_comp_cyclesIso_hom :
    S.liftCycles k hk ≫ h.cyclesIso.hom = h.liftK k hk := by
  simp only [← cancel_mono h.i, assoc, LeftHomologyData.cyclesIso_hom_comp_i,
    liftCycles_i, LeftHomologyData.liftK_i]

@[reassoc (attr := simp)]
lemma LeftHomologyData.lift_K_comp_cyclesIso_inv :
    h.liftK k hk ≫ h.cyclesIso.inv = S.liftCycles k hk := by
  rw [← h.liftCycles_comp_cyclesIso_hom, assoc, Iso.hom_inv_id, comp_id]

end

namespace HasLeftHomology

variable (S)

lemma hasKernel [S.HasLeftHomology] : HasKernel S.g :=
  ⟨⟨⟨_, S.leftHomologyData.hi⟩⟩⟩

lemma hasCokernel [S.HasLeftHomology] [HasKernel S.g] :
    HasCokernel (kernel.lift S.g S.f S.zero) := by
  let h := S.leftHomologyData
  haveI : HasColimit (parallelPair h.f' 0) := ⟨⟨⟨_, h.hπ'⟩⟩⟩
  let e : parallelPair (kernel.lift S.g S.f S.zero) 0 ≅ parallelPair h.f' 0 :=
    parallelPair.ext (Iso.refl _) (IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) h.hi)
      (by aesop_cat) (by simp)
  exact hasColimit_of_iso e

end HasLeftHomology

/-- The left homology of a short complex `S` identifies to the cokernel of the canonical
morphism `S.X₁ ⟶ kernel S.g`. -/
noncomputable def leftHomologyIsoCokernelLift [S.HasLeftHomology] [HasKernel S.g]
    [HasCokernel (kernel.lift S.g S.f S.zero)] :
    S.leftHomology ≅ cokernel (kernel.lift S.g S.f S.zero) :=
  (LeftHomologyData.ofHasKernelOfHasCokernel S).leftHomologyIso

/-! The following lemmas and instance gives a sufficient condition for a morphism
of short complexes to induce an isomorphism on cycles. -/

lemma isIso_cyclesMap'_of_isIso_of_mono (φ : S₁ ⟶ S₂) (h₂ : IsIso φ.τ₂) (h₃ : Mono φ.τ₃)
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    IsIso (cyclesMap' φ h₁ h₂) := by
  refine ⟨h₁.liftK (h₂.i ≫ inv φ.τ₂) ?_, ?_, ?_⟩
  · simp only [assoc, ← cancel_mono φ.τ₃, zero_comp, ← φ.comm₂₃, IsIso.inv_hom_id_assoc, h₂.wi]
  · simp only [← cancel_mono h₁.i, assoc, h₁.liftK_i, cyclesMap'_i_assoc,
      IsIso.hom_inv_id, comp_id, id_comp]
  · simp only [← cancel_mono h₂.i, assoc, cyclesMap'_i, h₁.liftK_i_assoc,
      IsIso.inv_hom_id, comp_id, id_comp]

lemma isIso_cyclesMap_of_isIso_of_mono' (φ : S₁ ⟶ S₂) (h₂ : IsIso φ.τ₂) (h₃ : Mono φ.τ₃)
    [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    IsIso (cyclesMap φ) :=
  isIso_cyclesMap'_of_isIso_of_mono φ h₂ h₃ _ _

instance isIso_cyclesMap_of_isIso_of_mono (φ : S₁ ⟶ S₂) [IsIso φ.τ₂] [Mono φ.τ₃]
    [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    IsIso (cyclesMap φ) :=
  isIso_cyclesMap_of_isIso_of_mono' φ inferInstance inferInstance

end ShortComplex

end CategoryTheory
