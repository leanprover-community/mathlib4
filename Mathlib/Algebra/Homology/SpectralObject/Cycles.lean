/-
<<<<<<< HEAD
Copyright (c) 2024 Joël Riou. All rights reserved.
=======
Copyright (c) 2026 Joël Riou. All rights reserved.
>>>>>>> origin
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Basic
public import Mathlib.Algebra.Homology.ExactSequenceFour
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
<<<<<<< HEAD
# Kernel and cokernel of the differentiel of a spectral object

Let `X` be a spectral object index by the category `ι`
=======
# Kernel and cokernel of the differential of a spectral object

Let `X` be a spectral object indexed by the category `ι`
>>>>>>> origin
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

<<<<<<< HEAD
The fact that the morphisms `δ` are part of a long exact sequence allow
to show that `X.cycles` also identify to a cokernel (`cokernelIsoCycles`)
and `X.opcycles` to a kernel (`opcyclesIsoKernel`).
More precisely, the exactness of `H^n(f) ⟶ H^n(f ≫ g) ⟶ Z^n(f, g) ⟶ 0`
is `cokernelSequenceCycles_exact` and the exactness of
`0 ⟶ opZ^n(f, g) ⟶ H^n(f ≫ g) ⟶ H^n(g)` is
`kernelSequenceOpcycles_exact`. In particular, we also
get constructors `descCycles` and `liftOpcycles` for morphisms
from cycles and to opcycles.

When `f₁`, `f₂` and `f₃` are composable morphisms, we introduce
morphisms `δToCycles : H^n(f₃) ⟶ Z^{n+1}(f₁, f₂)` and .
`δFromOpcycles : opZ^n(f₂, f₃) ⟶ H^{n+1}(f₁)`.

=======
>>>>>>> origin
## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]
-/

@[expose] public section

namespace CategoryTheory

open Limits ComposableArrows

namespace Abelian

<<<<<<< HEAD
variable {C ι : Type*} [Category C] [Category ι] [Abelian C]
=======
variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]
>>>>>>> origin

namespace SpectralObject

variable (X : SpectralObject C ι)

section

<<<<<<< HEAD
variable (n : ℤ) {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)

/-- The kernel of `δ : H^n(g) ⟶ H^{n+1}(f)`. In the documentation,
this may be shortened as `Z^n(f, g)` -/
noncomputable def cycles : C := kernel (X.δ n (n + 1) rfl f g)

/-- The cokernel of `δ : H^{n-1}(g) ⟶ H^n(g)`. In the documentation,
this may be shortened as `opZ^n₁(f, g)`. -/
noncomputable def opcycles : C := cokernel (X.δ (n - 1) n (by lia) f g)

/-- The inclusion `Z^n(f, g) ⟶ H^n(g)` of the kernel of `δ`. -/
noncomputable def iCycles :
    X.cycles n f g ⟶ (X.H n).obj (mk₁ g) :=
=======
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
>>>>>>> origin
  kernel.ι _

/-- The projection `H^n(f) ⟶ opZ^n(f, g)` to the cokernel of `δ`. -/
noncomputable def pOpcycles :
<<<<<<< HEAD
    (X.H n).obj (mk₁ f) ⟶ X.opcycles n f g :=
  cokernel.π _

instance : Mono (X.iCycles n f g) := by
  dsimp [iCycles]
  infer_instance

instance : Epi (X.pOpcycles n f g) := by
=======
    (X.H n).obj (mk₁ f) ⟶ X.opcycles f g n :=
  cokernel.π _

set_option backward.isDefEq.respectTransparency false in
instance : Mono (X.iCycles f g n) := by
  dsimp [iCycles]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance : Epi (X.pOpcycles f g n) := by
>>>>>>> origin
  dsimp [pOpcycles]
  infer_instance

lemma isZero_opcycles (h : IsZero ((X.H n).obj (mk₁ f))) :
<<<<<<< HEAD
    IsZero (X.opcycles n f g) := by
=======
    IsZero (X.opcycles f g n) := by
>>>>>>> origin
  rw [IsZero.iff_id_eq_zero, ← cancel_epi (X.pOpcycles ..)]
  apply h.eq_of_src

lemma isZero_cycles (h : IsZero ((X.H n).obj (mk₁ g))) :
<<<<<<< HEAD
    IsZero (X.cycles n f g) := by
=======
    IsZero (X.cycles f g n) := by
>>>>>>> origin
  rw [IsZero.iff_id_eq_zero, ← cancel_mono (X.iCycles ..)]
  apply h.eq_of_tgt

end

section

<<<<<<< HEAD
variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)

@[reassoc (attr := simp)]
lemma iCycles_δ : X.iCycles n₀ f g ≫ X.δ n₀ n₁ hn₁ f g = 0 := by
  subst hn₁
  simp [iCycles]

@[reassoc (attr := simp)]
lemma δ_pOpcycles : X.δ n₀ n₁ hn₁ f g ≫ X.pOpcycles n₁ f g = 0 := by
=======
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
>>>>>>> origin
  obtain rfl : n₀ = n₁ - 1 := by lia
  simp [pOpcycles]

/-- The short complex which expresses `X.cycles` as the kernel of `X.δ`. -/
@[simps]
<<<<<<< HEAD
noncomputable def kernelSequenceCycles : ShortComplex C :=
  ShortComplex.mk _ _ (X.iCycles_δ n₀ n₁ hn₁ f g)

/-- The short complex which expresses `X.opcycles` as the cokernel of `X.δ`. -/
@[simps]
noncomputable def cokernelSequenceOpcycles : ShortComplex C :=
  ShortComplex.mk _ _ (X.δ_pOpcycles n₀ n₁ hn₁ f g)

instance : Mono (X.kernelSequenceCycles n₀ n₁ hn₁ f g).f := by
  dsimp
  infer_instance

instance : Epi (X.cokernelSequenceOpcycles n₀ n₁ hn₁ f g).g := by
  dsimp
  infer_instance

lemma kernelSequenceCycles_exact :
    (X.kernelSequenceCycles n₀ n₁ hn₁ f g).Exact := by
  subst hn₁
  apply ShortComplex.exact_kernel

lemma cokernelSequenceOpcycles_exact :
    (X.cokernelSequenceOpcycles n₀ n₁ hn₁ f g).Exact := by
=======
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
>>>>>>> origin
  obtain rfl : n₀ = n₁ - 1 := by lia
  apply ShortComplex.exact_cokernel

section

<<<<<<< HEAD
variable {A : C} (x : A ⟶ (X.H n₀).obj (mk₁ g)) (hx : x ≫ X.δ n₀ n₁ hn₁ f g = 0)

/-- Constructor for morphisms to `X.cycles`. -/
noncomputable def liftCycles :
    A ⟶ X.cycles n₀ f g :=
  kernel.lift _ x (by subst hn₁; exact hx)

@[reassoc (attr := simp)]
lemma liftCycles_i : X.liftCycles n₀ n₁ hn₁ f g x hx ≫ X.iCycles n₀ f g = x := by
=======
variable (hn₁ : n₀ + 1 = n₁) {A : C} (x : A ⟶ (X.H n₀).obj (mk₁ g))
    (hx : x ≫ X.δ f g n₀ n₁ hn₁ = 0)

/-- Constructor for morphisms to `X.cycles`. -/
noncomputable def liftCycles :
    A ⟶ X.cycles f g n₀ :=
  kernel.lift _ x (by subst hn₁; exact hx)

@[reassoc (attr := simp)]
lemma liftCycles_i : X.liftCycles f g n₀ n₁ hn₁ x hx ≫ X.iCycles f g n₀ = x := by
>>>>>>> origin
  apply kernel.lift_ι

end

section

<<<<<<< HEAD
variable {A : C} (x : (X.H n₁).obj (mk₁ f) ⟶ A) (hx : X.δ n₀ n₁ hn₁ f g ≫ x = 0)

/-- Constructor for morphisms from `X.opcycles`. -/
noncomputable def descOpcycles :
    X.opcycles n₁ f g ⟶ A :=
=======
variable (hn₁ : n₀ + 1 = n₁) {A : C} (x : (X.H n₁).obj (mk₁ f) ⟶ A)
    (hx : X.δ f g n₀ n₁ hn₁ ≫ x = 0)

/-- Constructor for morphisms from `X.opcycles`. -/
noncomputable def descOpcycles :
    X.opcycles f g n₁ ⟶ A :=
>>>>>>> origin
  cokernel.desc _ x (by
    obtain rfl : n₀ = n₁ -1 := by lia
    exact hx)

@[reassoc (attr := simp)]
<<<<<<< HEAD
lemma p_descOpcycles : X.pOpcycles n₁ f g ≫ X.descOpcycles n₀ n₁ hn₁ f g x hx = x := by
=======
lemma p_descOpcycles : X.pOpcycles f g n₁ ≫ X.descOpcycles f g n₀ n₁ hn₁ x hx = x := by
>>>>>>> origin
  apply cokernel.π_desc

end

end

section

<<<<<<< HEAD
variable (n : ℤ) {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
=======
variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
>>>>>>> origin
  {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
  {i'' j'' k'' : ι} (f'' : i'' ⟶ j'') (g'' : j'' ⟶ k'')

/-- The functoriality of `X.cycles` with respect to morphisms in
`ComposableArrows ι 2`. -/
<<<<<<< HEAD
noncomputable def cyclesMap (α : mk₂ f g ⟶ mk₂ f' g') :
    X.cycles n f g ⟶ X.cycles n f' g' :=
  X.liftCycles _ _ rfl _ _
    (X.iCycles n f g ≫ (X.H n).map (homMk₁ (α.app 1) (α.app 2)
      (naturality' α 1 2))) (by
      rw [Category.assoc, X.δ_naturality n _ rfl f g f' g'
        (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
          (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) rfl,
        iCycles_δ_assoc, zero_comp])

@[reassoc]
lemma cyclesMap_i (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ g ⟶ mk₁ g')
    (hβ : β = homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) :
    X.cyclesMap n f g f' g' α ≫ X.iCycles n f' g' =
      X.iCycles n f g ≫ (X.H n).map β := by
=======
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
>>>>>>> origin
  subst hβ
  simp [cyclesMap]

@[simp]
<<<<<<< HEAD
lemma cyclesMap_id :
    X.cyclesMap n f g f g (𝟙 _) = 𝟙 _ := by
  rw [← cancel_mono (X.iCycles n f g),
    X.cyclesMap_i n f g f g (𝟙 _) (𝟙 _) (by cat_disch),
=======
lemma cyclesMap_id (n : ℤ) :
    X.cyclesMap f g f g (𝟙 _) n = 𝟙 _ := by
  rw [← cancel_mono (X.iCycles f g n), X.cyclesMap_i f g f g (𝟙 _) (𝟙 _) n,
>>>>>>> origin
    Functor.map_id, Category.comp_id, Category.id_comp]

@[reassoc]
lemma cyclesMap_comp (α : mk₂ f g ⟶ mk₂ f' g') (α' : mk₂ f' g' ⟶ mk₂ f'' g'')
<<<<<<< HEAD
    (α'' : mk₂ f g ⟶ mk₂ f'' g'') (h : α ≫ α' = α'') :
    X.cyclesMap n f g f' g' α ≫ X.cyclesMap n f' g' f'' g'' α' =
      X.cyclesMap n f g f'' g'' α'' := by
  subst h
  rw [← cancel_mono (X.iCycles n f'' g''), Category.assoc,
    X.cyclesMap_i n f' g' f'' g'' α' _ rfl,
    X.cyclesMap_i_assoc n f g f' g' α _ rfl,
    ← Functor.map_comp]
  symm
  apply X.cyclesMap_i
  cat_disch

/-- The functoriality of `X.opcycles` with respect to morphisms in
`ComposableArrows ι 2`. -/
noncomputable def opcyclesMap (α : mk₂ f g ⟶ mk₂ f' g') :
    X.opcycles n f g ⟶ X.opcycles n f' g' :=
  X.descOpcycles (n - 1) n (by lia) _ _
    ((X.H n).map (homMk₁ (by exact α.app 0) (by exact α.app 1)
      (naturality' α 0 1)) ≫ X.pOpcycles n f' g') (by
        rw [← X.δ_naturality_assoc (n - 1) n (by lia) f g f' g'
          (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1))
          (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) rfl,
          δ_pOpcycles, comp_zero])

@[reassoc]
lemma p_opcyclesMap (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ f ⟶ mk₁ f')
    (hβ : β = homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1)) :
    X.pOpcycles n f g ≫ X.opcyclesMap n f g f' g' α =
      (X.H n).map β ≫ X.pOpcycles n f' g' := by
=======
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
>>>>>>> origin
  subst hβ
  simp [opcyclesMap]

@[simp]
<<<<<<< HEAD
lemma opcyclesMap_id :
    X.opcyclesMap n f g f g (𝟙 _) = 𝟙 _ := by
  rw [← cancel_epi (X.pOpcycles n f g),
    X.p_opcyclesMap n f g f g (𝟙 _) (𝟙 _) (by cat_disch),
    Functor.map_id, Category.comp_id, Category.id_comp]

lemma opcyclesMap_comp (α : mk₂ f g ⟶ mk₂ f' g') (α' : mk₂ f' g' ⟶ mk₂ f'' g'')
    (α'' : mk₂ f g ⟶ mk₂ f'' g'') (h : α ≫ α' = α'') :
    X.opcyclesMap n f g f' g' α ≫ X.opcyclesMap n f' g' f'' g'' α' =
      X.opcyclesMap n f g f'' g'' α'' := by
  subst h
  rw [← cancel_epi (X.pOpcycles n f g),
    X.p_opcyclesMap_assoc n f g f' g' α _ rfl,
    X.p_opcyclesMap n f' g' f'' g'' α' _ rfl,
    ← Functor.map_comp_assoc]
  symm
  apply X.p_opcyclesMap
  aesop_cat
=======
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
    X.p_opcyclesMap_assoc f g f' g' α _ ,
    X.p_opcyclesMap f' g' f'' g'' α' _ ,
    ← Functor.map_comp_assoc]
  exact (X.p_opcyclesMap _ _ _ _ _ _ _ (by cat_disch)).symm
>>>>>>> origin

variable (fg : i ⟶ k) (h : f ≫ g = fg) (fg' : i' ⟶ k') (h' : f' ≫ g' = fg')

/-- `X.cycles` also identifies to a cokernel. More precisely,
`Z^n(f, g)` identifies to the cokernel of `H^n(f) ⟶ H^n(f ≫ g)` -/
<<<<<<< HEAD
noncomputable def cokernelIsoCycles :
    cokernel ((X.H n).map (twoδ₂Toδ₁ f g fg h)) ≅ X.cycles n f g :=
  (X.composableArrows₅_exact n _ rfl f g fg h).cokerIsoKer 0

@[reassoc (attr := simp)]
lemma cokernelIsoCycles_hom_fac :
    cokernel.π _ ≫ (X.cokernelIsoCycles n f g fg h).hom ≫
      X.iCycles n f g = (X.H n).map (twoδ₁Toδ₀ f g fg h) :=
  (X.composableArrows₅_exact n _ rfl f g fg h).cokerIsoKer_hom_fac 0

/-- `X.opcycles` also identifies to a kernel. More precisely,
`opZ(f, g)` identifies to the kernel of `H^n(f ≫ g) ⟶ H^n(g)` -/
noncomputable def opcyclesIsoKernel :
    X.opcycles n f g ≅ kernel ((X.H n).map (twoδ₁Toδ₀ f g fg h)) :=
  (X.composableArrows₅_exact (n - 1) n (by lia) f g fg h).cokerIsoKer 2

@[reassoc (attr := simp)]
lemma opcyclesIsoKernel_hom_fac :
    X.pOpcycles n f g ≫ (X.opcyclesIsoKernel n f g fg h).hom ≫
      kernel.ι _ = (X.H n).map (twoδ₂Toδ₁ f g fg h) :=
  (X.composableArrows₅_exact (n - 1) n (by lia) f g fg h).cokerIsoKer_hom_fac 2

/-- The map `H^n(fg) ⟶ H^n(g)` factors through `Z^n(f, g)`. -/
noncomputable def toCycles : (X.H n).obj (mk₁ fg) ⟶ X.cycles n f g :=
  kernel.lift _ ((X.H n).map (twoδ₁Toδ₀ f g fg h)) (by simp)

instance : Epi (X.toCycles n f g fg h) :=
  (ShortComplex.exact_iff_epi_kernel_lift _).1 (X.exact₃ n _ rfl f g fg h)

@[reassoc (attr := simp)]
lemma toCycles_i :
    X.toCycles n f g fg h ≫ X.iCycles n f g = (X.H n).map (twoδ₁Toδ₀ f g fg h) :=
  kernel.lift_ι ..

@[reassoc]
lemma toCycles_cyclesMap (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ fg ⟶ mk₁ fg')
    (hβ₀ : β.app 0 = α.app 0) (hβ₁ : β.app 1 = α.app 2) :
    X.toCycles n f g fg h ≫ X.cyclesMap n f g f' g' α =
      (X.H n).map β ≫ X.toCycles n f' g' fg' h' := by
  rw [← cancel_mono (X.iCycles n f' g'), Category.assoc, Category.assoc, toCycles_i,
    X.cyclesMap_i n f g f' g' α (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) rfl,
=======
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
>>>>>>> origin
    toCycles_i_assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext
  · dsimp
    rw [hβ₀]
    exact naturality' α 0 1
  · dsimp
    rw [hβ₁, Category.comp_id, Category.id_comp]

/-- The map `H^n(f) ⟶ H^n(f ≫ g)` factors through `opZ^n(f, g)`. -/
<<<<<<< HEAD
noncomputable def fromOpcycles :
    X.opcycles n f g ⟶ (X.H n).obj (mk₁ fg) :=
  cokernel.desc _ ((X.H n).map (twoδ₂Toδ₁ f g fg h)) (by simp)

instance : Mono (X.fromOpcycles n f g fg h) :=
  (ShortComplex.exact_iff_mono_cokernel_desc _).1 (X.exact₁ (n - 1) n (by lia) f g fg h)

@[reassoc (attr := simp)]
lemma p_fromOpcycles :
    X.pOpcycles n f g ≫ X.fromOpcycles n f g fg h =
=======
noncomputable def fromOpcycles (n : ℤ) :
    X.opcycles f g n ⟶ (X.H n).obj (mk₁ fg) :=
  cokernel.desc _ ((X.H n).map (twoδ₂Toδ₁ f g fg h)) (by simp)

instance (n : ℤ) : Mono (X.fromOpcycles f g fg h n) :=
  (ShortComplex.exact_iff_mono_cokernel_desc _).1 (X.exact₁ f g fg h (n - 1) n)

@[reassoc (attr := simp)]
lemma p_fromOpcycles (n : ℤ) :
    X.pOpcycles f g n ≫ X.fromOpcycles f g fg h n =
>>>>>>> origin
      (X.H n).map (twoδ₂Toδ₁ f g fg h) :=
  cokernel.π_desc ..

@[reassoc]
<<<<<<< HEAD
lemma opcyclesMap_fromOpcycles (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ fg ⟶ mk₁ fg')
    (hβ₀ : β.app 0 = α.app 0) (hβ₁ : β.app 1 = α.app 2) :
    X.opcyclesMap n f g f' g' α ≫ X.fromOpcycles n f' g' fg' h' =
      X.fromOpcycles n f g fg h ≫ (X.H n).map β := by
  rw [← cancel_epi (X.pOpcycles n f g), p_fromOpcycles_assoc,
    X.p_opcyclesMap_assoc n f g f' g' α (homMk₁ (α.app 0) (α.app 1)
      (naturality' α 0 1)) rfl,
=======
lemma opcyclesMap_fromOpcycles (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ fg ⟶ mk₁ fg') (n : ℤ)
    (hβ₀ : β.app 0 = α.app 0 := by cat_disch) (hβ₁ : β.app 1 = α.app 2 := by cat_disch) :
    X.opcyclesMap f g f' g' α n ≫ X.fromOpcycles f' g' fg' h' n =
      X.fromOpcycles f g fg h n ≫ (X.H n).map β := by
  rw [← cancel_epi (X.pOpcycles f g n), p_fromOpcycles_assoc,
    X.p_opcyclesMap_assoc f g f' g' α (homMk₁ (α.app 0) (α.app 1)
      (naturality' α 0 1)) n rfl,
>>>>>>> origin
    p_fromOpcycles, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext
  · cat_disch
  · dsimp
    rw [hβ₁]
    exact (naturality' α 1 2).symm

@[reassoc (attr := simp)]
<<<<<<< HEAD
lemma H_map_twoδ₂Toδ₁_toCycles :
    (X.H n).map (twoδ₂Toδ₁ f g fg h) ≫ X.toCycles n f g fg h = 0 := by
  simp [← cancel_mono (X.iCycles n f g)]

@[reassoc (attr := simp)]
lemma fromOpcycles_H_map_twoδ₁Toδ₀ :
    X.fromOpcycles n f g fg h ≫ (X.H n).map (twoδ₁Toδ₀ f g fg h) = 0 := by
  simp [← cancel_epi (X.pOpcycles n f g)]
=======
lemma H_map_twoδ₂Toδ₁_toCycles (n : ℤ) :
    (X.H n).map (twoδ₂Toδ₁ f g fg h) ≫ X.toCycles f g fg h n = 0 := by
  simp [← cancel_mono (X.iCycles f g n)]

@[reassoc (attr := simp)]
lemma fromOpcycles_H_map_twoδ₁Toδ₀ (n : ℤ) :
    X.fromOpcycles f g fg h n ≫ (X.H n).map (twoδ₁Toδ₀ f g fg h) = 0 := by
  simp [← cancel_epi (X.pOpcycles f g n)]
>>>>>>> origin

/-- The short complex expressing `Z^n(f, g)` as a cokernel of
the map `H^n(f) ⟶ H^n(f ≫ g)`. -/
@[simps]
<<<<<<< HEAD
noncomputable def cokernelSequenceCycles : ShortComplex C :=
  ShortComplex.mk _ _ (X.H_map_twoδ₂Toδ₁_toCycles n f g fg h)
=======
noncomputable def cokernelSequenceCycles (n : ℤ) : ShortComplex C :=
  ShortComplex.mk _ _ (X.H_map_twoδ₂Toδ₁_toCycles f g fg h n)
>>>>>>> origin

/-- The short complex expressing `opZ^n(f, g)` as a kernel of
the map `H^n(f ≫ g) ⟶ H^n(g)`. -/
@[simps]
<<<<<<< HEAD
noncomputable def kernelSequenceOpcycles : ShortComplex C :=
  ShortComplex.mk _ _ (X.fromOpcycles_H_map_twoδ₁Toδ₀ n f g fg h)

instance : Epi (X.cokernelSequenceCycles n f g fg h).g := by
  dsimp
  infer_instance

instance : Mono (X.kernelSequenceOpcycles n f g fg h).f := by
  dsimp
  infer_instance

/-- `Z^n(f, g)` identifies to a cokernel of the `H^n(f) ⟶ H^n(f ≫ g)`. -/
lemma cokernelSequenceCycles_exact :
    (X.cokernelSequenceCycles n f g fg h).Exact := by
  apply ShortComplex.exact_of_g_is_cokernel
  exact IsColimit.ofIsoColimit (cokernelIsCokernel _)
    (Cofork.ext (X.cokernelIsoCycles n f g fg h) (by
      simp [← cancel_mono (X.iCycles n f g)]))

/-- `opZ^n(f, g)` identifies to the kernel of `H^n(f ≫ g) ⟶ H^n(g)`. -/
lemma kernelSequenceOpcycles_exact :
    (X.kernelSequenceOpcycles n f g fg h).Exact := by
  apply ShortComplex.exact_of_f_is_kernel
  exact IsLimit.ofIsoLimit (kernelIsKernel _)
    (Iso.symm (Fork.ext (X.opcyclesIsoKernel n f g fg h) (by
      simp [← cancel_epi (X.pOpcycles n f g)])))

lemma isIso_toCycles (hf : IsZero ((X.H n).obj (mk₁ f))) :
    IsIso (X.toCycles n f g fg h) := by
  have : Mono (X.toCycles n f g fg h) :=
    (X.cokernelSequenceCycles_exact n f g fg h).mono_g (hf.eq_of_src _ _)
  exact Balanced.isIso_of_mono_of_epi _

lemma isIso_fromOpcycles (hg : IsZero ((X.H n).obj (mk₁ g))) :
    IsIso (X.fromOpcycles n f g fg h) := by
  have : Epi (X.fromOpcycles n f g fg h) :=
    (X.kernelSequenceOpcycles_exact n f g fg h).epi_f (hg.eq_of_tgt _ _)
=======
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
>>>>>>> origin
  exact Balanced.isIso_of_mono_of_epi _

section

<<<<<<< HEAD
variable {A : C} (x : (X.H n).obj (mk₁ fg) ⟶ A)
=======
variable {A : C} {n : ℤ} (x : (X.H n).obj (mk₁ fg) ⟶ A)
>>>>>>> origin
  (hx : (X.H n).map (twoδ₂Toδ₁ f g fg h) ≫ x = 0)

/-- Constructor for morphisms from `X.cycles`. -/
noncomputable def descCycles :
<<<<<<< HEAD
    X.cycles n f g ⟶ A :=
  (X.cokernelSequenceCycles_exact n f g fg h).desc x hx

@[reassoc (attr := simp)]
lemma toCycles_descCycles :
    X.toCycles n f g fg h ≫ X.descCycles n f g fg h x hx = x :=
  (X.cokernelSequenceCycles_exact n f g fg h).g_desc x hx
=======
    X.cycles f g n ⟶ A :=
  (X.cokernelSequenceCycles_exact f g fg h n).desc x hx

@[reassoc (attr := simp)]
lemma toCycles_descCycles :
    X.toCycles f g fg h n ≫ X.descCycles f g fg h x hx = x :=
  (X.cokernelSequenceCycles_exact f g fg h n).g_desc x hx
>>>>>>> origin

end

section

<<<<<<< HEAD
variable {A : C} (x : A ⟶ (X.H n).obj (mk₁ fg))
=======
variable {A : C} {n : ℤ} (x : A ⟶ (X.H n).obj (mk₁ fg))
>>>>>>> origin
  (hx : x ≫ (X.H n).map (twoδ₁Toδ₀ f g fg h) = 0)

/-- Constructor for morphisms to `X.opcycles`. -/
noncomputable def liftOpcycles :
<<<<<<< HEAD
    A ⟶ X.opcycles n f g :=
  (X.kernelSequenceOpcycles_exact n f g fg h).lift x hx

@[reassoc (attr := simp)]
lemma liftOpcycles_fromOpcycles :
    X.liftOpcycles n f g fg h x hx ≫ X.fromOpcycles n f g fg h = x :=
  (X.kernelSequenceOpcycles_exact n f g fg h).lift_f x hx
=======
    A ⟶ X.opcycles f g n :=
  (X.kernelSequenceOpcycles_exact f g fg h n).lift x hx

@[reassoc (attr := simp)]
lemma liftOpcycles_fromOpcycles :
    X.liftOpcycles f g fg h x hx ≫ X.fromOpcycles f g fg h n = x :=
  (X.kernelSequenceOpcycles_exact f g fg h n).lift_f x hx
>>>>>>> origin

end

end

section

<<<<<<< HEAD
variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
  {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)

/-- The morphism `H^{n₀}(f₃) ⟶ Z^{n₁}(f₁, f₂)` induced by `δ`
when `f₁`, `f₂`, `f₃` are composable morphisms and `n₀ + 1 = n₁`. -/
noncomputable def δToCycles : (X.H n₀).obj (mk₁ f₃) ⟶ X.cycles n₁ f₁ f₂ :=
  X.liftCycles n₁ _ rfl f₁ f₂ (X.δ n₀ n₁ hn₁ f₂ f₃) (by simp)

@[reassoc (attr := simp)]
lemma δToCycles_iCycles :
    X.δToCycles n₀ n₁ hn₁ f₁ f₂ f₃ ≫ X.iCycles n₁ f₁ f₂ =
      X.δ n₀ n₁ hn₁ f₂ f₃ := by
  simp only [δToCycles, liftCycles_i]

@[reassoc (attr := simp)]
lemma δ_toCycles :
    X.δ n₀ n₁ hn₁ f₁₂ f₃ ≫ X.toCycles n₁ f₁ f₂ f₁₂ h₁₂ =
      X.δToCycles n₀ n₁ hn₁ f₁ f₂ f₃ := by
  rw [← cancel_mono (X.iCycles n₁ f₁ f₂), Category.assoc,
    toCycles_i, δToCycles_iCycles,
    ← X.δ_naturality n₀ n₁ hn₁ f₁₂ f₃ f₂ f₃ (twoδ₁Toδ₀ f₁ f₂ f₁₂ h₁₂) (𝟙 _) rfl,
=======
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
>>>>>>> origin
    Functor.map_id, Category.id_comp]

/-- The morphism `opZ^{n₀}(f₂, f₃) ⟶ H^{n₁}(f₁)` induced by `δ`
when `f₁`, `f₂`, `f₃` are composable morphisms and `n₀ + 1 = n₁`. -/
<<<<<<< HEAD
noncomputable def δFromOpcycles : X.opcycles n₀ f₂ f₃ ⟶ (X.H n₁).obj (mk₁ f₁) :=
  X.descOpcycles (n₀ - 1) n₀ (by lia) f₂ f₃ (X.δ n₀ n₁ hn₁ f₁ f₂) (by simp)

@[reassoc (attr := simp)]
lemma pOpcycles_δFromOpcycles :
    X.pOpcycles n₀ f₂ f₃ ≫ X.δFromOpcycles n₀ n₁ hn₁ f₁ f₂ f₃ =
      X.δ n₀ n₁ hn₁ f₁ f₂ := by
  simp only [δFromOpcycles, p_descOpcycles]

@[reassoc (attr := simp)]
lemma fromOpcyles_δ :
    X.fromOpcycles n₀ f₂ f₃ f₂₃ h₂₃ ≫ X.δ n₀ n₁ hn₁ f₁ f₂₃ =
      X.δFromOpcycles n₀ n₁ hn₁ f₁ f₂ f₃ := by
  rw [← cancel_epi (X.pOpcycles n₀ f₂ f₃),
    p_fromOpcycles_assoc, pOpcycles_δFromOpcycles,
    X.δ_naturality n₀ n₁ hn₁ f₁ f₂ f₁ f₂₃ (𝟙 _) (twoδ₂Toδ₁ f₂ f₃ f₂₃ h₂₃) rfl,
=======
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
      X.δFromOpcycles f₁ f₂ f₃ n₀ n₁ hn₁  := by
  rw [← cancel_epi (X.pOpcycles f₂ f₃ n₀),
    p_fromOpcycles_assoc, pOpcycles_δFromOpcycles,
    X.δ_naturality f₁ f₂ f₁ f₂₃ (𝟙 _) (twoδ₂Toδ₁ f₂ f₃ f₂₃ h₂₃) n₀ n₁,
>>>>>>> origin
    Functor.map_id, Category.comp_id]

end

end SpectralObject

end Abelian

end CategoryTheory
