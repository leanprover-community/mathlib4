/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
## Smoothness of standard maps associated to the product of manifolds

This file contains results about smoothness of standard maps associated to products and sums
(disjoint unions) of smooth manifolds:
- if `f` and `g` are `C^n`, so is their point-wise product.
- the component projections from a product of manifolds are smooth.
- functions into a product (*pi type*) are `C^n` iff their components are
- if `M` and `N` are manifolds modelled over the same space, `Sum.inl` and `Sum.inr` are
  `C^n`, as are `Sum.elim`, `Sum.map` and `Sum.swap`.

-/

assert_not_exists mfderiv

public section

open Set Function Filter ChartedSpace

open scoped Topology Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a charted space `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  -- declare a charted space `M'` over the pair `(E', H')`.
  {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  -- declare a charted space `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  -- declare a charted space `N'` over the pair `(F', G')`.
  {F' : Type*}
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type*} [TopologicalSpace G']
  {J' : ModelWithCorners 𝕜 F' G'} {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  -- declare a few vector spaces
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  -- declare functions, sets, points and smoothness indices
  {f : M → M'} {s : Set M} {x : M} {n : WithTop ℕ∞}

section ProdMk

theorem ContMDiffWithinAt.prodMk {f : M → M'} {g : M → N'} (hf : ContMDiffWithinAt I I' n f s x)
    (hg : ContMDiffWithinAt I J' n g s x) :
    ContMDiffWithinAt I (I'.prod J') n (fun x => (f x, g x)) s x := by
  rw [contMDiffWithinAt_iff] at *
  exact ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

theorem ContMDiffWithinAt.prodMk_space {f : M → E'} {g : M → F'}
    (hf : ContMDiffWithinAt I 𝓘(𝕜, E') n f s x) (hg : ContMDiffWithinAt I 𝓘(𝕜, F') n g s x) :
    ContMDiffWithinAt I 𝓘(𝕜, E' × F') n (fun x => (f x, g x)) s x := by
  rw [contMDiffWithinAt_iff] at *
  exact ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

nonrec theorem ContMDiffAt.prodMk {f : M → M'} {g : M → N'} (hf : ContMDiffAt I I' n f x)
    (hg : ContMDiffAt I J' n g x) : ContMDiffAt I (I'.prod J') n (fun x => (f x, g x)) x :=
  hf.prodMk hg

nonrec theorem ContMDiffAt.prodMk_space {f : M → E'} {g : M → F'}
    (hf : ContMDiffAt I 𝓘(𝕜, E') n f x) (hg : ContMDiffAt I 𝓘(𝕜, F') n g x) :
    ContMDiffAt I 𝓘(𝕜, E' × F') n (fun x => (f x, g x)) x :=
  hf.prodMk_space hg

theorem ContMDiffOn.prodMk {f : M → M'} {g : M → N'} (hf : ContMDiffOn I I' n f s)
    (hg : ContMDiffOn I J' n g s) : ContMDiffOn I (I'.prod J') n (fun x => (f x, g x)) s :=
  fun x hx => (hf x hx).prodMk (hg x hx)

theorem ContMDiffOn.prodMk_space {f : M → E'} {g : M → F'} (hf : ContMDiffOn I 𝓘(𝕜, E') n f s)
    (hg : ContMDiffOn I 𝓘(𝕜, F') n g s) : ContMDiffOn I 𝓘(𝕜, E' × F') n (fun x => (f x, g x)) s :=
  fun x hx => (hf x hx).prodMk_space (hg x hx)

nonrec theorem ContMDiff.prodMk {f : M → M'} {g : M → N'} (hf : ContMDiff I I' n f)
    (hg : ContMDiff I J' n g) : ContMDiff I (I'.prod J') n fun x => (f x, g x) := fun x =>
  (hf x).prodMk (hg x)

theorem ContMDiff.prodMk_space {f : M → E'} {g : M → F'} (hf : ContMDiff I 𝓘(𝕜, E') n f)
    (hg : ContMDiff I 𝓘(𝕜, F') n g) : ContMDiff I 𝓘(𝕜, E' × F') n fun x => (f x, g x) := fun x =>
  (hf x).prodMk_space (hg x)

end ProdMk

section Projections

theorem contMDiffWithinAt_fst {s : Set (M × N)} {p : M × N} :
    ContMDiffWithinAt (I.prod J) I n Prod.fst s p := by
  /- porting note: `simp` fails to apply lemmas to `ModelProd`. Was
  rw [contMDiffWithinAt_iff']
  refine' ⟨continuousWithinAt_fst, _⟩
  refine' contDiffWithinAt_fst.congr (fun y hy => _) _
  · simp only [mfld_simps] at hy
    simp only [hy, mfld_simps]
  · simp only [mfld_simps]
  -/
  rw [contMDiffWithinAt_iff']
  refine ⟨continuousWithinAt_fst, contDiffWithinAt_fst.congr (fun y hy => ?_) ?_⟩
  · exact (extChartAt I p.1).right_inv ⟨hy.1.1.1, hy.1.2.1⟩
  · exact (extChartAt I p.1).right_inv <| (extChartAt I p.1).map_source (mem_extChartAt_source _)

theorem ContMDiffWithinAt.fst {f : N → M × M'} {s : Set N} {x : N}
    (hf : ContMDiffWithinAt J (I.prod I') n f s x) :
    ContMDiffWithinAt J I n (fun x => (f x).1) s x :=
  contMDiffWithinAt_fst.comp x hf (mapsTo_image f s)

theorem contMDiffAt_fst {p : M × N} : ContMDiffAt (I.prod J) I n Prod.fst p :=
  contMDiffWithinAt_fst

theorem contMDiffOn_fst {s : Set (M × N)} : ContMDiffOn (I.prod J) I n Prod.fst s := fun _ _ =>
  contMDiffWithinAt_fst

theorem contMDiff_fst : ContMDiff (I.prod J) I n (@Prod.fst M N) := fun _ => contMDiffAt_fst

theorem ContMDiffAt.fst {f : N → M × M'} {x : N} (hf : ContMDiffAt J (I.prod I') n f x) :
    ContMDiffAt J I n (fun x => (f x).1) x :=
  contMDiffAt_fst.comp x hf

theorem ContMDiff.fst {f : N → M × M'} (hf : ContMDiff J (I.prod I') n f) :
    ContMDiff J I n fun x => (f x).1 :=
  contMDiff_fst.comp hf

theorem contMDiffWithinAt_snd {s : Set (M × N)} {p : M × N} :
    ContMDiffWithinAt (I.prod J) J n Prod.snd s p := by
  /- porting note: `simp` fails to apply lemmas to `ModelProd`. Was
  rw [contMDiffWithinAt_iff']
  refine' ⟨continuousWithinAt_snd, _⟩
  refine' contDiffWithinAt_snd.congr (fun y hy => _) _
  · simp only [mfld_simps] at hy
    simp only [hy, mfld_simps]
  · simp only [mfld_simps]
  -/
  rw [contMDiffWithinAt_iff']
  refine ⟨continuousWithinAt_snd, contDiffWithinAt_snd.congr (fun y hy => ?_) ?_⟩
  · exact (extChartAt J p.2).right_inv ⟨hy.1.1.2, hy.1.2.2⟩
  · exact (extChartAt J p.2).right_inv <| (extChartAt J p.2).map_source (mem_extChartAt_source _)

theorem ContMDiffWithinAt.snd {f : N → M × M'} {s : Set N} {x : N}
    (hf : ContMDiffWithinAt J (I.prod I') n f s x) :
    ContMDiffWithinAt J I' n (fun x => (f x).2) s x :=
  contMDiffWithinAt_snd.comp x hf (mapsTo_image f s)

theorem contMDiffAt_snd {p : M × N} : ContMDiffAt (I.prod J) J n Prod.snd p :=
  contMDiffWithinAt_snd

theorem contMDiffOn_snd {s : Set (M × N)} : ContMDiffOn (I.prod J) J n Prod.snd s := fun _ _ =>
  contMDiffWithinAt_snd

theorem contMDiff_snd : ContMDiff (I.prod J) J n (@Prod.snd M N) := fun _ => contMDiffAt_snd

theorem ContMDiffAt.snd {f : N → M × M'} {x : N} (hf : ContMDiffAt J (I.prod I') n f x) :
    ContMDiffAt J I' n (fun x => (f x).2) x :=
  contMDiffAt_snd.comp x hf

theorem ContMDiff.snd {f : N → M × M'} (hf : ContMDiff J (I.prod I') n f) :
    ContMDiff J I' n fun x => (f x).2 :=
  contMDiff_snd.comp hf

end Projections

theorem contMDiffWithinAt_prod_iff (f : M → M' × N') :
    ContMDiffWithinAt I (I'.prod J') n f s x ↔
      ContMDiffWithinAt I I' n (Prod.fst ∘ f) s x ∧ ContMDiffWithinAt I J' n (Prod.snd ∘ f) s x :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prodMk h.2⟩

theorem contMDiffWithinAt_prod_module_iff (f : M → F₁ × F₂) :
    ContMDiffWithinAt I 𝓘(𝕜, F₁ × F₂) n f s x ↔
      ContMDiffWithinAt I 𝓘(𝕜, F₁) n (Prod.fst ∘ f) s x ∧
      ContMDiffWithinAt I 𝓘(𝕜, F₂) n (Prod.snd ∘ f) s x := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact contMDiffWithinAt_prod_iff f

theorem contMDiffAt_prod_iff (f : M → M' × N') :
    ContMDiffAt I (I'.prod J') n f x ↔
      ContMDiffAt I I' n (Prod.fst ∘ f) x ∧ ContMDiffAt I J' n (Prod.snd ∘ f) x := by
  simp_rw [← contMDiffWithinAt_univ]; exact contMDiffWithinAt_prod_iff f

theorem contMDiffAt_prod_module_iff (f : M → F₁ × F₂) :
    ContMDiffAt I 𝓘(𝕜, F₁ × F₂) n f x ↔
      ContMDiffAt I 𝓘(𝕜, F₁) n (Prod.fst ∘ f) x ∧ ContMDiffAt I 𝓘(𝕜, F₂) n (Prod.snd ∘ f) x := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact contMDiffAt_prod_iff f

theorem contMDiffOn_prod_iff (f : M → M' × N') :
    ContMDiffOn I (I'.prod J') n f s ↔
      ContMDiffOn I I' n (Prod.fst ∘ f) s ∧ ContMDiffOn I J' n (Prod.snd ∘ f) s :=
  ⟨fun h ↦ ⟨fun x hx ↦ ((contMDiffWithinAt_prod_iff f).1 (h x hx)).1,
      fun x hx ↦ ((contMDiffWithinAt_prod_iff f).1 (h x hx)).2⟩,
    fun h x hx ↦ (contMDiffWithinAt_prod_iff f).2 ⟨h.1 x hx, h.2 x hx⟩⟩

theorem contMDiffOn_prod_module_iff (f : M → F₁ × F₂) :
    ContMDiffOn I 𝓘(𝕜, F₁ × F₂) n f s ↔
      ContMDiffOn I 𝓘(𝕜, F₁) n (Prod.fst ∘ f) s ∧ ContMDiffOn I 𝓘(𝕜, F₂) n (Prod.snd ∘ f) s := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact contMDiffOn_prod_iff f

theorem contMDiff_prod_iff (f : M → M' × N') :
    ContMDiff I (I'.prod J') n f ↔
      ContMDiff I I' n (Prod.fst ∘ f) ∧ ContMDiff I J' n (Prod.snd ∘ f) :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => by convert h.1.prodMk h.2⟩

theorem contMDiff_prod_module_iff (f : M → F₁ × F₂) :
    ContMDiff I 𝓘(𝕜, F₁ × F₂) n f ↔
      ContMDiff I 𝓘(𝕜, F₁) n (Prod.fst ∘ f) ∧ ContMDiff I 𝓘(𝕜, F₂) n (Prod.snd ∘ f) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact contMDiff_prod_iff f

theorem contMDiff_prod_assoc :
    ContMDiff ((I.prod I').prod J) (I.prod (I'.prod J)) n
      fun x : (M × M') × N => (x.1.1, x.1.2, x.2) :=
  contMDiff_fst.fst.prodMk <| contMDiff_fst.snd.prodMk contMDiff_snd

/-- `ContMDiffWithinAt.comp` for a function of two arguments. -/
theorem ContMDiffWithinAt.comp₂ {h : M' × N' → N} {f : M → M'} {g : M → N'} {x : M}
    {t : Set (M' × N')} (ha : ContMDiffWithinAt (I'.prod J') J n h t (f x, g x))
    (fa : ContMDiffWithinAt I I' n f s x) (ga : ContMDiffWithinAt I J' n g s x)
    (st : MapsTo (fun x ↦ (f x, g x)) s t) :
    ContMDiffWithinAt I J n (fun x ↦ h (f x, g x)) s x :=
  ha.comp (f := fun x ↦ (f x, g x)) _ (fa.prodMk ga) st

/-- `ContMDiffWithinAt.comp₂`, with a separate argument for point equality. -/
theorem ContMDiffWithinAt.comp₂_of_eq {h : M' × N' → N} {f : M → M'} {g : M → N'} {x : M}
    {y : M' × N'} {t : Set (M' × N')} (ha : ContMDiffWithinAt (I'.prod J') J n h t y)
    (fa : ContMDiffWithinAt I I' n f s x) (ga : ContMDiffWithinAt I J' n g s x)
    (e : (f x, g x) = y) (st : MapsTo (fun x ↦ (f x, g x)) s t) :
    ContMDiffWithinAt I J n (fun x ↦ h (f x, g x)) s x := by
  rw [← e] at ha
  exact ha.comp₂ fa ga st

/-- `ContMDiffAt.comp` for a function of two arguments. -/
theorem ContMDiffAt.comp₂ {h : M' × N' → N} {f : M → M'} {g : M → N'} {x : M}
    (ha : ContMDiffAt (I'.prod J') J n h (f x, g x)) (fa : ContMDiffAt I I' n f x)
    (ga : ContMDiffAt I J' n g x) : ContMDiffAt I J n (fun x ↦ h (f x, g x)) x :=
  ha.comp (f := fun x ↦ (f x, g x)) _ (fa.prodMk ga)

/-- `ContMDiffAt.comp₂`, with a separate argument for point equality. -/
theorem ContMDiffAt.comp₂_of_eq {h : M' × N' → N} {f : M → M'} {g : M → N'} {x : M} {y : M' × N'}
    (ha : ContMDiffAt (I'.prod J') J n h y) (fa : ContMDiffAt I I' n f x)
    (ga : ContMDiffAt I J' n g x) (e : (f x, g x) = y) :
    ContMDiffAt I J n (fun x ↦ h (f x, g x)) x := by
  rw [← e] at ha
  exact ha.comp₂ fa ga

/-- Curried `C^n` functions are `C^n` in the first coordinate. -/
theorem ContMDiffWithinAt.curry_left {f : M → M' → N} {x : M} {y : M'} {s : Set (M × M')}
    (fa : ContMDiffWithinAt (I.prod I') J n (uncurry f) s (x, y)) :
    ContMDiffWithinAt I J n (fun x ↦ f x y) {x | (x, y) ∈ s} x :=
  fa.comp₂ contMDiffWithinAt_id contMDiffWithinAt_const (fun _ h ↦ h)
alias ContMDiffWithinAt.along_fst := ContMDiffWithinAt.curry_left

/-- Curried `C^n` functions are `C^n` in the second coordinate. -/
theorem ContMDiffWithinAt.curry_right {f : M → M' → N} {x : M} {y : M'} {s : Set (M × M')}
    (fa : ContMDiffWithinAt (I.prod I') J n (uncurry f) s (x, y)) :
    ContMDiffWithinAt I' J n (fun y ↦ f x y) {y | (x, y) ∈ s} y :=
  fa.comp₂ contMDiffWithinAt_const contMDiffWithinAt_id (fun _ h ↦ h)
alias ContMDiffWithinAt.along_snd := ContMDiffWithinAt.curry_right

/-- Curried `C^n` functions are `C^n` in the first coordinate. -/
theorem ContMDiffAt.curry_left {f : M → M' → N} {x : M} {y : M'}
    (fa : ContMDiffAt (I.prod I') J n (uncurry f) (x, y)) :
    ContMDiffAt I J n (fun x ↦ f x y) x :=
  fa.comp₂ contMDiffAt_id contMDiffAt_const
alias ContMDiffAt.along_fst := ContMDiffAt.curry_left

/-- Curried `C^n` functions are `C^n` in the second coordinate. -/
theorem ContMDiffAt.curry_right {f : M → M' → N} {x : M} {y : M'}
    (fa : ContMDiffAt (I.prod I') J n (uncurry f) (x, y)) :
    ContMDiffAt I' J n (fun y ↦ f x y) y :=
  fa.comp₂ contMDiffAt_const contMDiffAt_id
alias ContMDiffAt.along_snd := ContMDiffAt.curry_right

/-- Curried `C^n` functions are `C^n` in the first coordinate. -/
theorem ContMDiffOn.curry_left {f : M → M' → N} {s : Set (M × M')}
    (fa : ContMDiffOn (I.prod I') J n (uncurry f) s) {y : M'} :
    ContMDiffOn I J n (fun x ↦ f x y) {x | (x, y) ∈ s} :=
  fun x m ↦ (fa (x, y) m).along_fst
alias ContMDiffOn.along_fst := ContMDiffOn.curry_left

/-- Curried `C^n` functions are `C^n` in the second coordinate. -/
theorem ContMDiffOn.curry_right {f : M → M' → N} {x : M} {s : Set (M × M')}
    (fa : ContMDiffOn (I.prod I') J n (uncurry f) s) :
    ContMDiffOn I' J n (fun y ↦ f x y) {y | (x, y) ∈ s} :=
  fun y m ↦ (fa (x, y) m).along_snd
alias ContMDiffOn.along_snd := ContMDiffOn.curry_right

/-- Curried `C^n` functions are `C^n` in the first coordinate. -/
theorem ContMDiff.curry_left {f : M → M' → N}
    (fa : ContMDiff (I.prod I') J n (uncurry f)) {y : M'} :
    ContMDiff I J n (fun x ↦ f x y) :=
  fun _ ↦ (fa _).along_fst
alias ContMDiff.along_fst := ContMDiff.curry_left

/-- Curried `C^n` functions are `C^n` in the second coordinate. -/
theorem ContMDiff.curry_right {f : M → M' → N} {x : M}
    (fa : ContMDiff (I.prod I') J n (uncurry f)) :
    ContMDiff I' J n (fun y ↦ f x y) :=
  fun _ ↦ (fa _).along_snd
alias ContMDiff.along_snd := ContMDiff.curry_right

section prodMap

variable {g : N → N'} {r : Set N} {y : N}

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
theorem ContMDiffWithinAt.prodMap' {p : M × N} (hf : ContMDiffWithinAt I I' n f s p.1)
    (hg : ContMDiffWithinAt J J' n g r p.2) :
    ContMDiffWithinAt (I.prod J) (I'.prod J') n (Prod.map f g) (s ×ˢ r) p :=
  (hf.comp p contMDiffWithinAt_fst mapsTo_fst_prod).prodMk <|
    hg.comp p contMDiffWithinAt_snd mapsTo_snd_prod

theorem ContMDiffWithinAt.prodMap (hf : ContMDiffWithinAt I I' n f s x)
    (hg : ContMDiffWithinAt J J' n g r y) :
    ContMDiffWithinAt (I.prod J) (I'.prod J') n (Prod.map f g) (s ×ˢ r) (x, y) :=
  ContMDiffWithinAt.prodMap' hf hg

theorem ContMDiffAt.prodMap (hf : ContMDiffAt I I' n f x) (hg : ContMDiffAt J J' n g y) :
    ContMDiffAt (I.prod J) (I'.prod J') n (Prod.map f g) (x, y) := by
  simp only [← contMDiffWithinAt_univ, ← univ_prod_univ] at *
  exact hf.prodMap hg

theorem ContMDiffAt.prodMap' {p : M × N} (hf : ContMDiffAt I I' n f p.1)
    (hg : ContMDiffAt J J' n g p.2) : ContMDiffAt (I.prod J) (I'.prod J') n (Prod.map f g) p :=
  hf.prodMap hg

theorem ContMDiffOn.prodMap (hf : ContMDiffOn I I' n f s) (hg : ContMDiffOn J J' n g r) :
    ContMDiffOn (I.prod J) (I'.prod J') n (Prod.map f g) (s ×ˢ r) :=
  (hf.comp contMDiffOn_fst mapsTo_fst_prod).prodMk <| hg.comp contMDiffOn_snd mapsTo_snd_prod

theorem ContMDiff.prodMap (hf : ContMDiff I I' n f) (hg : ContMDiff J J' n g) :
    ContMDiff (I.prod J) (I'.prod J') n (Prod.map f g) := by
  intro p
  exact (hf p.1).prodMap' (hg p.2)

end prodMap

section PiSpace

/-!
### Regularity of functions with codomain `Π i, F i`

We have no `ModelWithCorners.pi` yet, so we prove lemmas about functions `f : M → Π i, F i` and
use `𝓘(𝕜, Π i, F i)` as the model space.
-/


variable {ι : Type*} [Fintype ι] {Fi : ι → Type*} [∀ i, NormedAddCommGroup (Fi i)]
  [∀ i, NormedSpace 𝕜 (Fi i)] {φ : M → ∀ i, Fi i}

theorem contMDiffWithinAt_pi_space :
    ContMDiffWithinAt I 𝓘(𝕜, ∀ i, Fi i) n φ s x ↔
      ∀ i, ContMDiffWithinAt I 𝓘(𝕜, Fi i) n (fun x => φ x i) s x := by
  simp only [contMDiffWithinAt_iff, continuousWithinAt_pi, contDiffWithinAt_pi, forall_and,
    extChartAt_model_space_eq_id, Function.comp_def, PartialEquiv.refl_coe, id]

theorem contMDiffOn_pi_space :
    ContMDiffOn I 𝓘(𝕜, ∀ i, Fi i) n φ s ↔ ∀ i, ContMDiffOn I 𝓘(𝕜, Fi i) n (fun x => φ x i) s :=
  ⟨fun h i x hx => contMDiffWithinAt_pi_space.1 (h x hx) i, fun h x hx =>
    contMDiffWithinAt_pi_space.2 fun i => h i x hx⟩

theorem contMDiffAt_pi_space :
    ContMDiffAt I 𝓘(𝕜, ∀ i, Fi i) n φ x ↔ ∀ i, ContMDiffAt I 𝓘(𝕜, Fi i) n (fun x => φ x i) x :=
  contMDiffWithinAt_pi_space

theorem contMDiff_pi_space :
    ContMDiff I 𝓘(𝕜, ∀ i, Fi i) n φ ↔ ∀ i, ContMDiff I 𝓘(𝕜, Fi i) n fun x => φ x i :=
  ⟨fun h i x => contMDiffAt_pi_space.1 (h x) i, fun h x => contMDiffAt_pi_space.2 fun i => h i x⟩

end PiSpace

section disjointUnion

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] {n : WithTop ℕ∞}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {J : Type*} {J : ModelWithCorners 𝕜 E' H'}
  {N N' : Type*} [TopologicalSpace N] [TopologicalSpace N'] [ChartedSpace H' N] [ChartedSpace H' N']

open Topology

-- The non-terminal simp has a large simp set
set_option linter.flexible false in
lemma ContMDiff.inl : ContMDiff I I n (@Sum.inl M M') := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨continuous_inl.continuousAt, ?_⟩
  -- In extended charts, .inl equals the identity (on the chart sources).
  apply contDiffWithinAt_id.congr_of_eventuallyEq; swap
  · simp [ChartedSpace.sum_chartAt_inl]
    congr
    apply Sum.inl_injective.extend_apply (chartAt _ x)
  set C := chartAt H x with hC
  have : I.symm ⁻¹' C.target ∩ range I ∈ 𝓝[range I] (extChartAt I x) x := by
    rw [← I.image_eq (chartAt H x).target]
    exact (chartAt H x).extend_image_target_mem_nhds (mem_chart_source _ x)
  filter_upwards [this] with y hy
  simp [extChartAt, sum_chartAt_inl, ← hC, Sum.inl_injective.extend_apply C, C.right_inv hy.1,
    I.right_inv hy.2]

lemma ContMDiff.inr : ContMDiff I I n (@Sum.inr M M') := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨continuous_inr.continuousAt, ?_⟩
  -- In extended charts, .inl equals the identity (on the chart sources).
  apply contDiffWithinAt_id.congr_of_eventuallyEq; swap
  · simp only [mfld_simps, sum_chartAt_inr]
    congr
    apply Sum.inr_injective.extend_apply (chartAt _ x)
  set C := chartAt H x with hC
  have : I.symm ⁻¹' (chartAt H x).target ∩ range I ∈ 𝓝[range I] (extChartAt I x) x := by
    rw [← I.image_eq (chartAt H x).target]
    exact (chartAt H x).extend_image_target_mem_nhds (mem_chart_source _ x)
  filter_upwards [this] with y hy
  simp [extChartAt, sum_chartAt_inr, ← hC, Sum.inr_injective.extend_apply C, C.right_inv hy.1,
    I.right_inv hy.2]

lemma extChartAt_inl_apply {x y : M} :
    (extChartAt I (.inl x : M ⊕ M')) (Sum.inl y) = (extChartAt I x) y := by simp

lemma extChartAt_inr_apply {x y : M'} :
    (extChartAt I (.inr x : M ⊕ M')) (Sum.inr y) = (extChartAt I x) y := by simp

lemma ContMDiff.sumElim {f : M → N} {g : M' → N}
    (hf : ContMDiff I J n f) (hg : ContMDiff I J n g) : ContMDiff I J n (Sum.elim f g) := by
  intro p
  rw [contMDiffAt_iff]
  refine ⟨(Continuous.sumElim hf.continuous hg.continuous).continuousAt, ?_⟩
  cases p with
  | inl x =>
    -- In charts around x : M, the map f ⊔ g looks like f.
    -- This is how they both look like in extended charts.
    have : ContDiffWithinAt 𝕜 n ((extChartAt J (f x)) ∘ f ∘ (extChartAt I x).symm)
        (range I) ((extChartAt I (.inl x : M ⊕ M')) (Sum.inl x)) := by
      let hf' := hf x
      rw [contMDiffAt_iff] at hf'
      simpa using hf'.2
    apply this.congr_of_eventuallyEq
    · simp only [extChartAt, Sum.elim_inl, ChartedSpace.sum_chartAt_inl]
      filter_upwards with a
      congr
    · -- They agree at the image of x.
      simp only [extChartAt, ChartedSpace.sum_chartAt_inl, Sum.elim_inl]
      congr
  | inr x =>
    -- In charts around x : M, the map f ⊔ g looks like g.
    -- This is how they both look like in extended charts.
    have : ContDiffWithinAt 𝕜 n ((extChartAt J (g x)) ∘ g ∘ (extChartAt I x).symm)
        (range I) ((extChartAt I (.inr x : M ⊕ M')) (Sum.inr x)) := by
      let hg' := hg x
      rw [contMDiffAt_iff] at hg'
      simpa using hg'.2
    apply this.congr_of_eventuallyEq
    · simp only [extChartAt, Sum.elim_inr, ChartedSpace.sum_chartAt_inr]
      filter_upwards with a
      congr
    · -- They agree at the image of x.
      simp only [extChartAt, ChartedSpace.sum_chartAt_inr, Sum.elim_inr]
      congr

lemma ContMDiff.sumMap {f : M → N} {g : M' → N'}
    (hf : ContMDiff I J n f) (hg : ContMDiff I J n g) : ContMDiff I J n (Sum.map f g) :=
  ContMDiff.sumElim (ContMDiff.inl.comp hf) (ContMDiff.inr.comp hg)

lemma contMDiff_of_contMDiff_inl {f : M → N}
    (h : ContMDiff I J n ((@Sum.inl N N') ∘ f)) : ContMDiff I J n f := by
  nontriviality N
  inhabit N
  let aux : N ⊕ N' → N := Sum.elim (@id N) (fun _ ↦ inhabited_h.default)
  have : aux ∘ (@Sum.inl N N') ∘ f = f := by ext; simp [aux]
  rw [← this]
  rw [← contMDiffOn_univ] at h ⊢
  apply (contMDiff_id.sumElim contMDiff_const).contMDiffOn (s := @Sum.inl N N' '' univ).comp h
  intro x _hx
  rw [mem_preimage, Function.comp_apply]
  use f x, trivial

lemma contMDiff_of_contMDiff_inr {g : M' → N'}
    (h : ContMDiff I J n ((@Sum.inr N N') ∘ g)) : ContMDiff I J n g := by
  nontriviality N'
  inhabit N'
  let aux : N ⊕ N' → N' := Sum.elim (fun _ ↦ inhabited_h.default) (@id N')
  have : aux ∘ (@Sum.inr N N') ∘ g = g := by ext; simp [aux]
  rw [← this]
  rw [← contMDiffOn_univ] at h ⊢
  apply ((contMDiff_const.sumElim contMDiff_id).contMDiffOn (s := Sum.inr '' univ)).comp h
  intro x _hx
  rw [mem_preimage, Function.comp_apply]
  use g x, trivial

lemma contMDiff_sum_map {f : M → N} {g : M' → N'} :
    ContMDiff I J n (Sum.map f g) ↔ ContMDiff I J n f ∧ ContMDiff I J n g :=
  ⟨fun h ↦ ⟨contMDiff_of_contMDiff_inl (h.comp ContMDiff.inl),
    contMDiff_of_contMDiff_inr (h.comp ContMDiff.inr)⟩,
   fun h ↦ ContMDiff.sumMap h.1 h.2⟩

lemma ContMDiff.swap : ContMDiff I I n (@Sum.swap M M') := ContMDiff.sumElim inr inl

end disjointUnion
