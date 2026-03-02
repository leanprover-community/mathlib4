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
# Kernel and cokernel of the differentiel of a spectral object

Let `X` be a spectral object index by the category `ι`
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

variable {C ι : Type*} [Category C] [Category ι] [Abelian C]

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

instance : Mono (X.iCycles f g n) := by
  dsimp [iCycles]
  infer_instance

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

@[reassoc (attr := simp)]
lemma iCycles_δ (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.iCycles f g n₀ ≫ X.δ f g n₀ n₁ hn₁ = 0 := by
  subst hn₁
  simp [iCycles]

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
        iCycles_δ_assoc _ _ _ _ _ , zero_comp])

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
  X.descOpcycles _ _ (n - 1) _ (by lia)
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
lemma opcyclesMap_id (n : ℤ):
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
    X.p_opcyclesMap_assoc f g f' g' α _ ,
    X.p_opcyclesMap f' g' f'' g'' α' _ ,
    ← Functor.map_comp_assoc]
  exact (X.p_opcyclesMap _ _ _ _ _ _ _ (by cat_disch)).symm

end

end SpectralObject

end Abelian

end CategoryTheory
