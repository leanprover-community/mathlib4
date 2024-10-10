/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Geometry.Manifold.MFDeriv.UniqueDifferential

/-!
## Smoothness of standard maps associated to the product of manifolds

This file contains results about smoothness of standard maps associated to products of manifolds
- if `f` and `g` are smooth, so is their point-wise product.
- the component projections from a product of manifolds are smooth.
- functions into a product (*pi type*) are smooth iff their components are

-/

open Set Function Filter ChartedSpace SmoothManifoldWithCorners

open scoped Topology Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a charted space `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  -- declare a charted space `M'` over the pair `(E', H')`.
  {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  (I' : ModelWithCorners 𝕜 E' H') {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  -- declare a charted space `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  -- declare a charted space `N'` over the pair `(F', G')`.
  {F' : Type*}
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type*} [TopologicalSpace G']
  {J' : ModelWithCorners 𝕜 F' G'} {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  -- F₁, F₂, F₃, F₄ are normed spaces
  {F₁ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {F₂ : Type*} [NormedAddCommGroup F₂]
  [NormedSpace 𝕜 F₂] {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] {F₄ : Type*}
  [NormedAddCommGroup F₄] [NormedSpace 𝕜 F₄]
  -- declare functions, sets, points and smoothness indices
  {e : PartialHomeomorph M H}
  {e' : PartialHomeomorph M' H'} {f f₁ : M → M'} {s s₁ t : Set M} {x : M} {m n : ℕ∞}
variable {I I'}

section Projections

#check ContMDiffWithinAt.fst


theorem MDifferentiableWithinAt.fst {f : N → M × M'} {s : Set N} {x : N}
    (hf : MDifferentiableWithinAt J (I.prod I') f s x) :
    MDifferentiableWithinAt J I (fun x => (f x).1) s x :=
  (mdifferentiableWithinAt_fst I I').comp x hf (mapsTo_image f s)

#check MDifferentiableWithinAt.comp

theorem mdifferentiableAt_fst {p : M × N} : MDifferentiableAt (I.prod J) I n Prod.fst p :=
  mdifferentiableWithinAt_fst

theorem mdifferentiableOn_fst {s : Set (M × N)} : MDifferentiableOn (I.prod J) I n Prod.fst s := fun _ _ =>
  mdifferentiableWithinAt_fst

theorem mdifferentiable_fst : MDifferentiable (I.prod J) I n (@Prod.fst M N) := fun _ => mdifferentiableAt_fst

theorem smoothWithinAt_fst {s : Set (M × N)} {p : M × N} :
    SmoothWithinAt (I.prod J) I Prod.fst s p :=
  mdifferentiableWithinAt_fst

theorem smoothAt_fst {p : M × N} : SmoothAt (I.prod J) I Prod.fst p :=
  mdifferentiableAt_fst

theorem smoothOn_fst {s : Set (M × N)} : SmoothOn (I.prod J) I Prod.fst s :=
  mdifferentiableOn_fst

theorem smooth_fst : Smooth (I.prod J) I (@Prod.fst M N) :=
  mdifferentiable_fst

theorem MDifferentiableAt.fst {f : N → M × M'} {x : N} (hf : MDifferentiableAt J (I.prod I') n f x) :
    MDifferentiableAt J I n (fun x => (f x).1) x :=
  mdifferentiableAt_fst.comp x hf

theorem MDifferentiable.fst {f : N → M × M'} (hf : MDifferentiable J (I.prod I') n f) :
    MDifferentiable J I n fun x => (f x).1 :=
  mdifferentiable_fst.comp hf

theorem SmoothAt.fst {f : N → M × M'} {x : N} (hf : SmoothAt J (I.prod I') f x) :
    SmoothAt J I (fun x => (f x).1) x :=
  smoothAt_fst.comp x hf

theorem Smooth.fst {f : N → M × M'} (hf : Smooth J (I.prod I') f) : Smooth J I fun x => (f x).1 :=
  smooth_fst.comp hf

theorem mdifferentiableWithinAt_snd {s : Set (M × N)} {p : M × N} :
    MDifferentiableWithinAt (I.prod J) J n Prod.snd s p := by
  /- porting note: `simp` fails to apply lemmas to `ModelProd`. Was
  rw [mdifferentiableWithinAt_iff']
  refine' ⟨continuousWithinAt_snd, _⟩
  refine' contDiffWithinAt_snd.congr (fun y hy => _) _
  · simp only [mfld_simps] at hy
    simp only [hy, mfld_simps]
  · simp only [mfld_simps]
  -/
  rw [mdifferentiableWithinAt_iff']
  refine ⟨continuousWithinAt_snd, contDiffWithinAt_snd.congr (fun y hy => ?_) ?_⟩
  · exact (extChartAt J p.2).right_inv ⟨hy.1.1.2, hy.1.2.2⟩
  · exact (extChartAt J p.2).right_inv <| (extChartAt J p.2).map_source (mem_extChartAt_source _ _)

theorem MDifferentiableWithinAt.snd {f : N → M × M'} {s : Set N} {x : N}
    (hf : MDifferentiableWithinAt J (I.prod I') n f s x) :
    MDifferentiableWithinAt J I' n (fun x => (f x).2) s x :=
  mdifferentiableWithinAt_snd.comp x hf (mapsTo_image f s)

theorem mdifferentiableAt_snd {p : M × N} : MDifferentiableAt (I.prod J) J n Prod.snd p :=
  mdifferentiableWithinAt_snd

theorem mdifferentiableOn_snd {s : Set (M × N)} : MDifferentiableOn (I.prod J) J n Prod.snd s := fun _ _ =>
  mdifferentiableWithinAt_snd

theorem mdifferentiable_snd : MDifferentiable (I.prod J) J n (@Prod.snd M N) := fun _ => mdifferentiableAt_snd

theorem smoothWithinAt_snd {s : Set (M × N)} {p : M × N} :
    SmoothWithinAt (I.prod J) J Prod.snd s p :=
  mdifferentiableWithinAt_snd

theorem smoothAt_snd {p : M × N} : SmoothAt (I.prod J) J Prod.snd p :=
  mdifferentiableAt_snd

theorem smoothOn_snd {s : Set (M × N)} : SmoothOn (I.prod J) J Prod.snd s :=
  mdifferentiableOn_snd

theorem smooth_snd : Smooth (I.prod J) J (@Prod.snd M N) :=
  mdifferentiable_snd

theorem MDifferentiableAt.snd {f : N → M × M'} {x : N} (hf : MDifferentiableAt J (I.prod I') n f x) :
    MDifferentiableAt J I' n (fun x => (f x).2) x :=
  mdifferentiableAt_snd.comp x hf

theorem MDifferentiable.snd {f : N → M × M'} (hf : MDifferentiable J (I.prod I') n f) :
    MDifferentiable J I' n fun x => (f x).2 :=
  mdifferentiable_snd.comp hf

theorem SmoothAt.snd {f : N → M × M'} {x : N} (hf : SmoothAt J (I.prod I') f x) :
    SmoothAt J I' (fun x => (f x).2) x :=
  smoothAt_snd.comp x hf

theorem Smooth.snd {f : N → M × M'} (hf : Smooth J (I.prod I') f) : Smooth J I' fun x => (f x).2 :=
  smooth_snd.comp hf

end Projections

theorem mdifferentiableWithinAt_prod_iff (f : M → M' × N') :
    MDifferentiableWithinAt I (I'.prod J') n f s x ↔
      MDifferentiableWithinAt I I' n (Prod.fst ∘ f) s x ∧ MDifferentiableWithinAt I J' n (Prod.snd ∘ f) s x :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prod_mk h.2⟩

theorem mdifferentiableWithinAt_prod_module_iff (f : M → F₁ × F₂) :
    MDifferentiableWithinAt I 𝓘(𝕜, F₁ × F₂) n f s x ↔
      MDifferentiableWithinAt I 𝓘(𝕜, F₁) n (Prod.fst ∘ f) s x ∧
      MDifferentiableWithinAt I 𝓘(𝕜, F₂) n (Prod.snd ∘ f) s x := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mdifferentiableWithinAt_prod_iff f

theorem mdifferentiableAt_prod_iff (f : M → M' × N') :
    MDifferentiableAt I (I'.prod J') n f x ↔
      MDifferentiableAt I I' n (Prod.fst ∘ f) x ∧ MDifferentiableAt I J' n (Prod.snd ∘ f) x := by
  simp_rw [← mdifferentiableWithinAt_univ]; exact mdifferentiableWithinAt_prod_iff f

theorem mdifferentiableAt_prod_module_iff (f : M → F₁ × F₂) :
    MDifferentiableAt I 𝓘(𝕜, F₁ × F₂) n f x ↔
      MDifferentiableAt I 𝓘(𝕜, F₁) n (Prod.fst ∘ f) x ∧ MDifferentiableAt I 𝓘(𝕜, F₂) n (Prod.snd ∘ f) x := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mdifferentiableAt_prod_iff f

theorem mdifferentiableOn_prod_iff (f : M → M' × N') :
    MDifferentiableOn I (I'.prod J') n f s ↔
      MDifferentiableOn I I' n (Prod.fst ∘ f) s ∧ MDifferentiableOn I J' n (Prod.snd ∘ f) s :=
  ⟨fun h ↦ ⟨fun x hx ↦ ((mdifferentiableWithinAt_prod_iff f).1 (h x hx)).1,
      fun x hx ↦ ((mdifferentiableWithinAt_prod_iff f).1 (h x hx)).2⟩ ,
    fun h x hx ↦ (mdifferentiableWithinAt_prod_iff f).2 ⟨h.1 x hx, h.2 x hx⟩⟩

theorem mdifferentiableOn_prod_module_iff (f : M → F₁ × F₂) :
    MDifferentiableOn I 𝓘(𝕜, F₁ × F₂) n f s ↔
      MDifferentiableOn I 𝓘(𝕜, F₁) n (Prod.fst ∘ f) s ∧ MDifferentiableOn I 𝓘(𝕜, F₂) n (Prod.snd ∘ f) s := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mdifferentiableOn_prod_iff f

theorem mdifferentiable_prod_iff (f : M → M' × N') :
    MDifferentiable I (I'.prod J') n f ↔
      MDifferentiable I I' n (Prod.fst ∘ f) ∧ MDifferentiable I J' n (Prod.snd ∘ f) :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => by convert h.1.prod_mk h.2⟩

theorem mdifferentiable_prod_module_iff (f : M → F₁ × F₂) :
    MDifferentiable I 𝓘(𝕜, F₁ × F₂) n f ↔
      MDifferentiable I 𝓘(𝕜, F₁) n (Prod.fst ∘ f) ∧ MDifferentiable I 𝓘(𝕜, F₂) n (Prod.snd ∘ f) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mdifferentiable_prod_iff f

theorem smoothAt_prod_iff (f : M → M' × N') {x : M} :
    SmoothAt I (I'.prod J') f x ↔ SmoothAt I I' (Prod.fst ∘ f) x ∧ SmoothAt I J' (Prod.snd ∘ f) x :=
  mdifferentiableAt_prod_iff f

theorem smooth_prod_iff (f : M → M' × N') :
    Smooth I (I'.prod J') f ↔ Smooth I I' (Prod.fst ∘ f) ∧ Smooth I J' (Prod.snd ∘ f) :=
  mdifferentiable_prod_iff f

theorem smooth_prod_assoc :
    Smooth ((I.prod I').prod J) (I.prod (I'.prod J)) fun x : (M × M') × N => (x.1.1, x.1.2, x.2) :=
  smooth_fst.fst.prod_mk <| smooth_fst.snd.prod_mk smooth_snd

section prodMap

variable {g : N → N'} {r : Set N} {y : N}

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
theorem MDifferentiableWithinAt.prod_map' {p : M × N} (hf : MDifferentiableWithinAt I I' n f s p.1)
    (hg : MDifferentiableWithinAt J J' n g r p.2) :
    MDifferentiableWithinAt (I.prod J) (I'.prod J') n (Prod.map f g) (s ×ˢ r) p :=
  (hf.comp p mdifferentiableWithinAt_fst (prod_subset_preimage_fst _ _)).prod_mk <|
    hg.comp p mdifferentiableWithinAt_snd (prod_subset_preimage_snd _ _)

theorem MDifferentiableWithinAt.prod_map (hf : MDifferentiableWithinAt I I' n f s x)
    (hg : MDifferentiableWithinAt J J' n g r y) :
    MDifferentiableWithinAt (I.prod J) (I'.prod J') n (Prod.map f g) (s ×ˢ r) (x, y) :=
  MDifferentiableWithinAt.prod_map' hf hg

theorem MDifferentiableAt.prod_map (hf : MDifferentiableAt I I' n f x) (hg : MDifferentiableAt J J' n g y) :
    MDifferentiableAt (I.prod J) (I'.prod J') n (Prod.map f g) (x, y) := by
  rw [← mdifferentiableWithinAt_univ] at *
  convert hf.prod_map hg
  exact univ_prod_univ.symm

theorem MDifferentiableAt.prod_map' {p : M × N} (hf : MDifferentiableAt I I' n f p.1)
    (hg : MDifferentiableAt J J' n g p.2) : MDifferentiableAt (I.prod J) (I'.prod J') n (Prod.map f g) p := by
  rcases p with ⟨⟩
  exact hf.prod_map hg

theorem MDifferentiableOn.prod_map (hf : MDifferentiableOn I I' n f s) (hg : MDifferentiableOn J J' n g r) :
    MDifferentiableOn (I.prod J) (I'.prod J') n (Prod.map f g) (s ×ˢ r) :=
  (hf.comp mdifferentiableOn_fst (prod_subset_preimage_fst _ _)).prod_mk <|
    hg.comp mdifferentiableOn_snd (prod_subset_preimage_snd _ _)

theorem MDifferentiable.prod_map (hf : MDifferentiable I I' n f) (hg : MDifferentiable J J' n g) :
    MDifferentiable (I.prod J) (I'.prod J') n (Prod.map f g) := by
  intro p
  exact (hf p.1).prod_map' (hg p.2)

nonrec theorem SmoothWithinAt.prod_map (hf : SmoothWithinAt I I' f s x)
    (hg : SmoothWithinAt J J' g r y) :
    SmoothWithinAt (I.prod J) (I'.prod J') (Prod.map f g) (s ×ˢ r) (x, y) :=
  hf.prod_map hg

nonrec theorem SmoothAt.prod_map (hf : SmoothAt I I' f x) (hg : SmoothAt J J' g y) :
    SmoothAt (I.prod J) (I'.prod J') (Prod.map f g) (x, y) :=
  hf.prod_map hg

nonrec theorem SmoothOn.prod_map (hf : SmoothOn I I' f s) (hg : SmoothOn J J' g r) :
    SmoothOn (I.prod J) (I'.prod J') (Prod.map f g) (s ×ˢ r) :=
  hf.prod_map hg

nonrec theorem Smooth.prod_map (hf : Smooth I I' f) (hg : Smooth J J' g) :
    Smooth (I.prod J) (I'.prod J') (Prod.map f g) :=
  hf.prod_map hg

end prodMap

section PiSpace

/-!
### Smoothness of functions with codomain `Π i, F i`

We have no `ModelWithCorners.pi` yet, so we prove lemmas about functions `f : M → Π i, F i` and
use `𝓘(𝕜, Π i, F i)` as the model space.
-/


variable {ι : Type*} [Fintype ι] {Fi : ι → Type*} [∀ i, NormedAddCommGroup (Fi i)]
  [∀ i, NormedSpace 𝕜 (Fi i)] {φ : M → ∀ i, Fi i}

theorem mdifferentiableWithinAt_pi_space :
    MDifferentiableWithinAt I 𝓘(𝕜, ∀ i, Fi i) n φ s x ↔
      ∀ i, MDifferentiableWithinAt I 𝓘(𝕜, Fi i) n (fun x => φ x i) s x := by
  simp only [mdifferentiableWithinAt_iff, continuousWithinAt_pi, contDiffWithinAt_pi, forall_and,
    writtenInExtChartAt, extChartAt_model_space_eq_id, Function.comp_def, PartialEquiv.refl_coe, id]

theorem mdifferentiableOn_pi_space :
    MDifferentiableOn I 𝓘(𝕜, ∀ i, Fi i) n φ s ↔ ∀ i, MDifferentiableOn I 𝓘(𝕜, Fi i) n (fun x => φ x i) s :=
  ⟨fun h i x hx => mdifferentiableWithinAt_pi_space.1 (h x hx) i, fun h x hx =>
    mdifferentiableWithinAt_pi_space.2 fun i => h i x hx⟩

theorem mdifferentiableAt_pi_space :
    MDifferentiableAt I 𝓘(𝕜, ∀ i, Fi i) n φ x ↔ ∀ i, MDifferentiableAt I 𝓘(𝕜, Fi i) n (fun x => φ x i) x :=
  mdifferentiableWithinAt_pi_space

theorem mdifferentiable_pi_space :
    MDifferentiable I 𝓘(𝕜, ∀ i, Fi i) n φ ↔ ∀ i, MDifferentiable I 𝓘(𝕜, Fi i) n fun x => φ x i :=
  ⟨fun h i x => mdifferentiableAt_pi_space.1 (h x) i, fun h x => mdifferentiableAt_pi_space.2 fun i => h i x⟩

theorem smoothWithinAt_pi_space :
    SmoothWithinAt I 𝓘(𝕜, ∀ i, Fi i) φ s x ↔
      ∀ i, SmoothWithinAt I 𝓘(𝕜, Fi i) (fun x => φ x i) s x :=
  mdifferentiableWithinAt_pi_space

theorem smoothOn_pi_space :
    SmoothOn I 𝓘(𝕜, ∀ i, Fi i) φ s ↔ ∀ i, SmoothOn I 𝓘(𝕜, Fi i) (fun x => φ x i) s :=
  mdifferentiableOn_pi_space

theorem smoothAt_pi_space :
    SmoothAt I 𝓘(𝕜, ∀ i, Fi i) φ x ↔ ∀ i, SmoothAt I 𝓘(𝕜, Fi i) (fun x => φ x i) x :=
  mdifferentiableAt_pi_space

theorem smooth_pi_space : Smooth I 𝓘(𝕜, ∀ i, Fi i) φ ↔ ∀ i, Smooth I 𝓘(𝕜, Fi i) fun x => φ x i :=
  mdifferentiable_pi_space

end PiSpace
