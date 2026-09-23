/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Basic
public import Mathlib.Algebra.Homology.ExactSequenceFour
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Kernel and cokernel of the differential of a spectral object

Let `X` be a spectral object indexed by the category `ι`
in the abelian category `C`. In this file, we introduce
the kernel `X.cycles` and the cokernel `X.opcycles` of `X.δ`.
These are defined when `f` and `g` are composable morphisms
in `ι` and for any integer `n`.
In the documentation, the kernel `X.cycles n f g` of
`δ : H^n(g) ⟶ H^{n+1}(f)` shall be denoted `Z^n(f, g)`,
and the cokernel `X.opcycles n f g` of `δ : H^{n-1}(g) ⟶ H^n(f)`
shall be denoted `opZ^n(f, g)`.
The definitions `cyclesMap` and `opcyclesMap` give the
functoriality of these definitions with respect
to morphisms in `ComposableArrows ι 2`.

We record that `Z^n(f, g)` is a kernel by the lemma
`kernelSequenceCycles_exact` and that `opZ^n(f, g)` is
a cokernel by the lemma `cokernelSequenceOpcycles_exact`.
We also provide a constructor `X.liftCycles` for morphisms
to cycles and `X.descOpcycles` for morphisms from opcycles.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]
-/

@[expose] public section

namespace CategoryTheory

open Limits ComposableArrows

namespace Abelian

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

namespace SpectralObject

variable (X : SpectralObject C ι)

section

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ)

/-- The kernel of `δ : H^n(g) ⟶ H^{n+1}(f)`. In the documentation,
this may be shortened as `Z^n(f, g)` -/
noncomputable def cycles : C := kernel (X.δ f g n (n + 1))

/-- The cokernel of `δ : H^{n-1}(g) ⟶ H^n(g)`. In the documentation,
this may be shortened as `opZ^n₁(f, g)`. -/
noncomputable def opcycles : C := cokernel (X.δ f g (n - 1) n)

/-- The inclusion `Z^n(f, g) ⟶ H^n(g)` of the kernel of `δ`. -/
noncomputable def iCycles :
    X.cycles f g n ⟶ (X.H n).obj (mk₁ g) :=
  kernel.ι _

/-- The projection `H^n(f) ⟶ opZ^n(f, g)` to the cokernel of `δ`. -/
noncomputable def pOpcycles :
    (X.H n).obj (mk₁ f) ⟶ X.opcycles f g n :=
  cokernel.π _

set_option backward.isDefEq.respectTransparency false in
instance : Mono (X.iCycles f g n) := by
  dsimp [iCycles]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance : Epi (X.pOpcycles f g n) := by
  dsimp [pOpcycles]
  infer_instance

lemma isZero_opcycles (h : IsZero ((X.H n).obj (mk₁ f))) :
    IsZero (X.opcycles f g n) := by
  rw [IsZero.iff_id_eq_zero, ← cancel_epi (X.pOpcycles ..)]
  apply h.eq_of_src

lemma isZero_cycles (h : IsZero ((X.H n).obj (mk₁ g))) :
    IsZero (X.cycles f g n) := by
  rw [IsZero.iff_id_eq_zero, ← cancel_mono (X.iCycles ..)]
  apply h.eq_of_tgt

end

section

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n₀ n₁ : ℤ)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma iCycles_δ (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.iCycles f g n₀ ≫ X.δ f g n₀ n₁ hn₁ = 0 := by
  subst hn₁
  simp [iCycles]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma δ_pOpcycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.δ f g n₀ n₁ hn₁ ≫ X.pOpcycles f g n₁ = 0 := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  simp [pOpcycles]

/-- The short complex which expresses `X.cycles` as the kernel of `X.δ`. -/
@[simps]
noncomputable def kernelSequenceCycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    ShortComplex C :=
  ShortComplex.mk _ _ (X.iCycles_δ f g n₀ n₁ hn₁)

/-- The short complex which expresses `X.opcycles` as the cokernel of `X.δ`. -/
@[simps]
noncomputable def cokernelSequenceOpcycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    ShortComplex C :=
  ShortComplex.mk _ _ (X.δ_pOpcycles f g n₀ n₁ hn₁)

instance (hn₁ : n₀ + 1 = n₁) :
    Mono (X.kernelSequenceCycles f g n₀ n₁ hn₁).f := by
  dsimp
  infer_instance

instance (hn₁ : n₀ + 1 = n₁) :
    Epi (X.cokernelSequenceOpcycles f g n₀ n₁ hn₁).g := by
  dsimp
  infer_instance

lemma kernelSequenceCycles_exact (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.kernelSequenceCycles f g n₀ n₁ hn₁).Exact := by
  subst hn₁
  apply ShortComplex.exact_kernel

lemma cokernelSequenceOpcycles_exact (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.cokernelSequenceOpcycles f g n₀ n₁ hn₁).Exact := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  apply ShortComplex.exact_cokernel

section

variable (hn₁ : n₀ + 1 = n₁) {A : C} (x : A ⟶ (X.H n₀).obj (mk₁ g))
    (hx : x ≫ X.δ f g n₀ n₁ hn₁ = 0)

/-- Constructor for morphisms to `X.cycles`. -/
noncomputable def liftCycles :
    A ⟶ X.cycles f g n₀ :=
  kernel.lift _ x (by subst hn₁; exact hx)

@[reassoc (attr := simp)]
lemma liftCycles_i : X.liftCycles f g n₀ n₁ hn₁ x hx ≫ X.iCycles f g n₀ = x := by
  apply kernel.lift_ι

end

section

variable (hn₁ : n₀ + 1 = n₁) {A : C} (x : (X.H n₁).obj (mk₁ f) ⟶ A)
    (hx : X.δ f g n₀ n₁ hn₁ ≫ x = 0)

/-- Constructor for morphisms from `X.opcycles`. -/
noncomputable def descOpcycles :
    X.opcycles f g n₁ ⟶ A :=
  cokernel.desc _ x (by
    obtain rfl : n₀ = n₁ -1 := by lia
    exact hx)

@[reassoc (attr := simp)]
lemma p_descOpcycles : X.pOpcycles f g n₁ ≫ X.descOpcycles f g n₀ n₁ hn₁ x hx = x := by
  apply cokernel.π_desc

end

end

section

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
  {i'' j'' k'' : ι} (f'' : i'' ⟶ j'') (g'' : j'' ⟶ k'')

/-- The functoriality of `X.cycles` with respect to morphisms in
`ComposableArrows ι 2`. -/
noncomputable def cyclesMap (α : mk₂ f g ⟶ mk₂ f' g') (n : ℤ) :
    X.cycles f g n ⟶ X.cycles f' g' n :=
  X.liftCycles _ _ _ _ rfl
    (X.iCycles f g n ≫ (X.H n).map (homMk₁ (α.app 1) (α.app 2)
      (naturality' α 1 2))) (by
      rw [Category.assoc, X.δ_naturality f g f' g'
        (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
          (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) n (n + 1),
        iCycles_δ_assoc _ _ _ _ _, zero_comp])

@[reassoc]
lemma cyclesMap_i (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ g ⟶ mk₁ g') (n : ℤ)
    (hβ : β = homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2) := by cat_disch) :
    X.cyclesMap f g f' g' α n ≫ X.iCycles f' g' n =
      X.iCycles f g n ≫ (X.H n).map β := by
  subst hβ
  simp [cyclesMap]

@[simp]
lemma cyclesMap_id (n : ℤ) :
    X.cyclesMap f g f g (𝟙 _) n = 𝟙 _ := by
  rw [← cancel_mono (X.iCycles f g n), X.cyclesMap_i f g f g (𝟙 _) (𝟙 _) n,
    Functor.map_id, Category.comp_id, Category.id_comp]

@[reassoc]
lemma cyclesMap_comp (α : mk₂ f g ⟶ mk₂ f' g') (α' : mk₂ f' g' ⟶ mk₂ f'' g'')
    (α'' : mk₂ f g ⟶ mk₂ f'' g'') (n : ℤ) (h : α ≫ α' = α'' := by cat_disch) :
    X.cyclesMap f g f' g' α n ≫ X.cyclesMap f' g' f'' g'' α' n =
      X.cyclesMap f g f'' g'' α'' n := by
  subst h
  rw [← cancel_mono (X.iCycles f'' g'' n), Category.assoc,
    X.cyclesMap_i f' g' f'' g'' α' _ n rfl,
    X.cyclesMap_i_assoc f g f' g' α _ n rfl,
    ← Functor.map_comp]
  exact (X.cyclesMap_i _ _ _ _ _ _ _).symm

/-- The functoriality of `X.opcycles` with respect to morphisms in
`ComposableArrows ι 2`. -/
noncomputable def opcyclesMap (α : mk₂ f g ⟶ mk₂ f' g') (n : ℤ) :
    X.opcycles f g n ⟶ X.opcycles f' g' n :=
  X.descOpcycles _ _ (n - 1) n (by lia)
    ((X.H n).map (homMk₁ (by exact α.app 0) (by exact α.app 1)
      (naturality' α 0 1)) ≫ X.pOpcycles f' g' n) (by
      rw [← X.δ_naturality_assoc f g f' g'
        (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
        (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) _ _,
        δ_pOpcycles _ _ _ _ _, comp_zero])

@[reassoc]
lemma p_opcyclesMap (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ f ⟶ mk₁ f') (n : ℤ)
    (hβ : β = homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1) := by cat_disch) :
    X.pOpcycles f g n ≫ X.opcyclesMap f g f' g' α n =
      (X.H n).map β ≫ X.pOpcycles f' g' n := by
  subst hβ
  simp [opcyclesMap]

@[simp]
lemma opcyclesMap_id (n : ℤ) :
    X.opcyclesMap f g f g (𝟙 _) n = 𝟙 _ := by
  rw [← cancel_epi (X.pOpcycles f g n),
    X.p_opcyclesMap f g f g (𝟙 _) (𝟙 _),
    Functor.map_id, Category.comp_id, Category.id_comp]

lemma opcyclesMap_comp (α : mk₂ f g ⟶ mk₂ f' g') (α' : mk₂ f' g' ⟶ mk₂ f'' g'')
    (α'' : mk₂ f g ⟶ mk₂ f'' g'') (n : ℤ) (h : α ≫ α' = α'' := by cat_disch) :
    X.opcyclesMap f g f' g' α n ≫ X.opcyclesMap f' g' f'' g'' α' n =
      X.opcyclesMap f g f'' g'' α'' n := by
  subst h
  rw [← cancel_epi (X.pOpcycles f g n),
    X.p_opcyclesMap_assoc f g f' g' α _,
    X.p_opcyclesMap f' g' f'' g'' α' _,
    ← Functor.map_comp_assoc]
  exact (X.p_opcyclesMap _ _ _ _ _ _ _ (by cat_disch)).symm

variable (fg : i ⟶ k) (h : f ≫ g = fg) (fg' : i' ⟶ k') (h' : f' ≫ g' = fg')

/-- `X.cycles` also identifies to a cokernel. More precisely,
`Z^n(f, g)` identifies to the cokernel of `H^n(f) ⟶ H^n(f ≫ g)` -/
noncomputable def cokernelIsoCycles (n : ℤ) :
    cokernel ((X.H n).map (twoδ₂Toδ₁ f g fg h)) ≅ X.cycles f g n :=
  (X.composableArrows₅_exact f g fg h n (n + 1)).cokerIsoKer 0

@[reassoc (attr := simp)]
lemma cokernelIsoCycles_hom_fac (n : ℤ) :
    cokernel.π _ ≫ (X.cokernelIsoCycles f g fg h n).hom ≫
      X.iCycles f g n = (X.H n).map (twoδ₁Toδ₀ f g fg h) :=
  (X.composableArrows₅_exact f g fg h n (n + 1)).cokerIsoKer_hom_fac 0

/-- `X.opcycles` also identifies to a kernel. More precisely,
`opZ(f, g)` identifies to the kernel of `H^n(f ≫ g) ⟶ H^n(g)` -/
noncomputable def opcyclesIsoKernel (n : ℤ) :
    X.opcycles f g n ≅ kernel ((X.H n).map (twoδ₁Toδ₀ f g fg h)) :=
  (X.composableArrows₅_exact f g fg h (n - 1) n).cokerIsoKer 2

@[reassoc (attr := simp)]
lemma opcyclesIsoKernel_hom_fac (n : ℤ) :
    X.pOpcycles f g n ≫ (X.opcyclesIsoKernel f g fg h n).hom ≫
      kernel.ι _ = (X.H n).map (twoδ₂Toδ₁ f g fg h) :=
  (X.composableArrows₅_exact f g fg h (n - 1) n).cokerIsoKer_hom_fac 2

/-- The map `H^n(fg) ⟶ H^n(g)` factors through `Z^n(f, g)`. -/
noncomputable def toCycles (n : ℤ) :
    (X.H n).obj (mk₁ fg) ⟶ X.cycles f g n :=
  kernel.lift _ ((X.H n).map (twoδ₁Toδ₀ f g fg h)) (by simp)

instance (n : ℤ) : Epi (X.toCycles f g fg h n) :=
  (ShortComplex.exact_iff_epi_kernel_lift _).1 (X.exact₃ f g fg h n (n + 1))

@[reassoc (attr := simp)]
lemma toCycles_i (n : ℤ) :
    X.toCycles f g fg h n ≫ X.iCycles f g n = (X.H n).map (twoδ₁Toδ₀ f g fg h) :=
  kernel.lift_ι ..

@[reassoc]
lemma toCycles_cyclesMap (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ fg ⟶ mk₁ fg') (n : ℤ)
    (hβ₀ : β.app 0 = α.app 0 := by cat_disch) (hβ₁ : β.app 1 = α.app 2 := by cat_disch) :
    X.toCycles f g fg h n ≫ X.cyclesMap f g f' g' α n =
      (X.H n).map β ≫ X.toCycles f' g' fg' h' n := by
  rw [← cancel_mono (X.iCycles f' g' n), Category.assoc, Category.assoc, toCycles_i,
    X.cyclesMap_i f g f' g' α (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) n rfl,
    toCycles_i_assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext
  · dsimp
    rw [hβ₀]
    exact naturality' α 0 1
  · dsimp
    rw [hβ₁, Category.comp_id, Category.id_comp]

/-- The map `H^n(f) ⟶ H^n(f ≫ g)` factors through `opZ^n(f, g)`. -/
noncomputable def fromOpcycles (n : ℤ) :
    X.opcycles f g n ⟶ (X.H n).obj (mk₁ fg) :=
  cokernel.desc _ ((X.H n).map (twoδ₂Toδ₁ f g fg h)) (by simp)

instance (n : ℤ) : Mono (X.fromOpcycles f g fg h n) :=
  (ShortComplex.exact_iff_mono_cokernel_desc _).1 (X.exact₁ f g fg h (n - 1) n)

@[reassoc (attr := simp)]
lemma p_fromOpcycles (n : ℤ) :
    X.pOpcycles f g n ≫ X.fromOpcycles f g fg h n =
      (X.H n).map (twoδ₂Toδ₁ f g fg h) :=
  cokernel.π_desc ..

@[reassoc]
lemma opcyclesMap_fromOpcycles (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ fg ⟶ mk₁ fg') (n : ℤ)
    (hβ₀ : β.app 0 = α.app 0 := by cat_disch) (hβ₁ : β.app 1 = α.app 2 := by cat_disch) :
    X.opcyclesMap f g f' g' α n ≫ X.fromOpcycles f' g' fg' h' n =
      X.fromOpcycles f g fg h n ≫ (X.H n).map β := by
  rw [← cancel_epi (X.pOpcycles f g n), p_fromOpcycles_assoc,
    X.p_opcyclesMap_assoc f g f' g' α (homMk₁ (α.app 0) (α.app 1)
      (naturality' α 0 1)) n rfl,
    p_fromOpcycles, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext
  · cat_disch
  · dsimp
    rw [hβ₁]
    exact (naturality' α 1 2).symm

@[reassoc (attr := simp)]
lemma H_map_twoδ₂Toδ₁_toCycles (n : ℤ) :
    (X.H n).map (twoδ₂Toδ₁ f g fg h) ≫ X.toCycles f g fg h n = 0 := by
  simp [← cancel_mono (X.iCycles f g n)]

@[reassoc (attr := simp)]
lemma fromOpcycles_H_map_twoδ₁Toδ₀ (n : ℤ) :
    X.fromOpcycles f g fg h n ≫ (X.H n).map (twoδ₁Toδ₀ f g fg h) = 0 := by
  simp [← cancel_epi (X.pOpcycles f g n)]

/-- The short complex expressing `Z^n(f, g)` as a cokernel of
the map `H^n(f) ⟶ H^n(f ≫ g)`. -/
@[simps]
noncomputable def cokernelSequenceCycles (n : ℤ) : ShortComplex C :=
  ShortComplex.mk _ _ (X.H_map_twoδ₂Toδ₁_toCycles f g fg h n)

/-- The short complex expressing `opZ^n(f, g)` as a kernel of
the map `H^n(f ≫ g) ⟶ H^n(g)`. -/
@[simps]
noncomputable def kernelSequenceOpcycles (n : ℤ) : ShortComplex C :=
  ShortComplex.mk _ _ (X.fromOpcycles_H_map_twoδ₁Toδ₀ f g fg h n)

instance (n : ℤ) : Epi (X.cokernelSequenceCycles f g fg h n).g := by
  dsimp
  infer_instance

instance (n : ℤ) : Mono (X.kernelSequenceOpcycles f g fg h n).f := by
  dsimp
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- `Z^n(f, g)` identifies to a cokernel of the `H^n(f) ⟶ H^n(f ≫ g)`. -/
lemma cokernelSequenceCycles_exact (n : ℤ) :
    (X.cokernelSequenceCycles f g fg h n).Exact := by
  apply ShortComplex.exact_of_g_is_cokernel
  exact IsColimit.ofIsoColimit (cokernelIsCokernel _)
    (Cofork.ext (X.cokernelIsoCycles f g fg h n) (by
      simp [← cancel_mono (X.iCycles f g n)]))

set_option backward.isDefEq.respectTransparency false in
/-- `opZ^n(f, g)` identifies to the kernel of `H^n(f ≫ g) ⟶ H^n(g)`. -/
lemma kernelSequenceOpcycles_exact (n : ℤ) :
    (X.kernelSequenceOpcycles f g fg h n).Exact := by
  apply ShortComplex.exact_of_f_is_kernel
  exact IsLimit.ofIsoLimit (kernelIsKernel _)
    (Iso.symm (Fork.ext (X.opcyclesIsoKernel f g fg h n) (by
      simp [← cancel_epi (X.pOpcycles f g n)])))

lemma isIso_toCycles (n : ℤ) (hf : IsZero ((X.H n).obj (mk₁ f))) :
    IsIso (X.toCycles f g fg h n) := by
  have : Mono (X.toCycles f g fg h n) :=
    (X.cokernelSequenceCycles_exact f g fg h n).mono_g (hf.eq_of_src _ _)
  exact Balanced.isIso_of_mono_of_epi _

lemma isIso_fromOpcycles (n : ℤ) (hg : IsZero ((X.H n).obj (mk₁ g))) :
    IsIso (X.fromOpcycles f g fg h n) := by
  have : Epi (X.fromOpcycles f g fg h n) :=
    (X.kernelSequenceOpcycles_exact f g fg h n).epi_f (hg.eq_of_tgt _ _)
  exact Balanced.isIso_of_mono_of_epi _

section

variable {A : C} {n : ℤ} (x : (X.H n).obj (mk₁ fg) ⟶ A)
  (hx : (X.H n).map (twoδ₂Toδ₁ f g fg h) ≫ x = 0)

/-- Constructor for morphisms from `X.cycles`. -/
noncomputable def descCycles :
    X.cycles f g n ⟶ A :=
  (X.cokernelSequenceCycles_exact f g fg h n).desc x hx

@[reassoc (attr := simp)]
lemma toCycles_descCycles :
    X.toCycles f g fg h n ≫ X.descCycles f g fg h x hx = x :=
  (X.cokernelSequenceCycles_exact f g fg h n).g_desc x hx

end

section

variable {A : C} {n : ℤ} (x : A ⟶ (X.H n).obj (mk₁ fg))
  (hx : x ≫ (X.H n).map (twoδ₁Toδ₀ f g fg h) = 0)

/-- Constructor for morphisms to `X.opcycles`. -/
noncomputable def liftOpcycles :
    A ⟶ X.opcycles f g n :=
  (X.kernelSequenceOpcycles_exact f g fg h n).lift x hx

@[reassoc (attr := simp)]
lemma liftOpcycles_fromOpcycles :
    X.liftOpcycles f g fg h x hx ≫ X.fromOpcycles f g fg h n = x :=
  (X.kernelSequenceOpcycles_exact f g fg h n).lift_f x hx

end

end

section

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (n₀ n₁ : ℤ)
/-- The morphism `H^{n₀}(f₃) ⟶ Z^{n₁}(f₁, f₂)` induced by `δ`
when `f₁`, `f₂`, `f₃` are composable morphisms and `n₀ + 1 = n₁`. -/
noncomputable def δToCycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.H n₀).obj (mk₁ f₃) ⟶ X.cycles f₁ f₂ n₁ :=
  X.liftCycles f₁ f₂ _ _ rfl (X.δ f₂ f₃ n₀ n₁) (by simp)

@[reassoc (attr := simp)]
lemma δToCycles_iCycles (hn₁ : n₀ + 1 = n₁) :
    X.δToCycles f₁ f₂ f₃ n₀ n₁ hn₁ ≫ X.iCycles f₁ f₂ n₁ =
      X.δ f₂ f₃ n₀ n₁ hn₁ := by
  simp only [δToCycles, liftCycles_i]

@[reassoc (attr := simp)]
lemma δ_toCycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.δ f₁₂ f₃ n₀ n₁ hn₁ ≫ X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ =
      X.δToCycles f₁ f₂ f₃ n₀ n₁ hn₁ := by
  rw [← cancel_mono (X.iCycles f₁ f₂ n₁), Category.assoc,
    toCycles_i, δToCycles_iCycles,
    ← X.δ_naturality f₁₂ f₃ f₂ f₃ (twoδ₁Toδ₀ f₁ f₂ f₁₂ h₁₂) (𝟙 _) n₀ n₁,
    Functor.map_id, Category.id_comp]

/-- The morphism `opZ^{n₀}(f₂, f₃) ⟶ H^{n₁}(f₁)` induced by `δ`
when `f₁`, `f₂`, `f₃` are composable morphisms and `n₀ + 1 = n₁`. -/
noncomputable def δFromOpcycles (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.opcycles f₂ f₃ n₀ ⟶ (X.H n₁).obj (mk₁ f₁) :=
  X.descOpcycles f₂ f₃ (n₀ - 1) n₀ (by lia) (X.δ f₁ f₂ n₀ n₁ hn₁) (by simp)

@[reassoc (attr := simp)]
lemma pOpcycles_δFromOpcycles (hn₁ : n₀ + 1 = n₁) :
    X.pOpcycles f₂ f₃ n₀ ≫ X.δFromOpcycles f₁ f₂ f₃ n₀ n₁ hn₁ =
      X.δ f₁ f₂ n₀ n₁ hn₁ := by
  simp only [δFromOpcycles, p_descOpcycles]

@[reassoc (attr := simp)]
lemma fromOpcyles_δ (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₀ ≫ X.δ f₁ f₂₃ n₀ n₁ hn₁ =
      X.δFromOpcycles f₁ f₂ f₃ n₀ n₁ hn₁ := by
  rw [← cancel_epi (X.pOpcycles f₂ f₃ n₀),
    p_fromOpcycles_assoc, pOpcycles_δFromOpcycles,
    X.δ_naturality f₁ f₂ f₁ f₂₃ (𝟙 _) (twoδ₂Toδ₁ f₂ f₃ f₂₃ h₂₃) n₀ n₁,
    Functor.map_id, Category.comp_id]

end

end SpectralObject

end Abelian

end CategoryTheory
