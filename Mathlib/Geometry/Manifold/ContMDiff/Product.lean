/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
## Smoothness of standard maps associated to the product of manifolds

This file contains results about smoothness of standard maps associated to products of manifolds
- if `f` and `g` are `C^n`, so is their point-wise product.
- the component projections from a product of manifolds are smooth.
- functions into a product (*pi type*) are `C^n` iff their components are

-/

open Set Function Filter ChartedSpace IsManifold

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

theorem ContMDiffWithinAt.prod_mk {f : M → M'} {g : M → N'} (hf : ContMDiffWithinAt I I' n f s x)
    (hg : ContMDiffWithinAt I J' n g s x) :
    ContMDiffWithinAt I (I'.prod J') n (fun x => (f x, g x)) s x := by
  rw [contMDiffWithinAt_iff] at *
  exact ⟨hf.1.prod hg.1, hf.2.prod hg.2⟩

theorem ContMDiffWithinAt.prod_mk_space {f : M → E'} {g : M → F'}
    (hf : ContMDiffWithinAt I 𝓘(𝕜, E') n f s x) (hg : ContMDiffWithinAt I 𝓘(𝕜, F') n g s x) :
    ContMDiffWithinAt I 𝓘(𝕜, E' × F') n (fun x => (f x, g x)) s x := by
  rw [contMDiffWithinAt_iff] at *
  exact ⟨hf.1.prod hg.1, hf.2.prod hg.2⟩

nonrec theorem ContMDiffAt.prod_mk {f : M → M'} {g : M → N'} (hf : ContMDiffAt I I' n f x)
    (hg : ContMDiffAt I J' n g x) : ContMDiffAt I (I'.prod J') n (fun x => (f x, g x)) x :=
  hf.prod_mk hg

nonrec theorem ContMDiffAt.prod_mk_space {f : M → E'} {g : M → F'}
    (hf : ContMDiffAt I 𝓘(𝕜, E') n f x) (hg : ContMDiffAt I 𝓘(𝕜, F') n g x) :
    ContMDiffAt I 𝓘(𝕜, E' × F') n (fun x => (f x, g x)) x :=
  hf.prod_mk_space hg

theorem ContMDiffOn.prod_mk {f : M → M'} {g : M → N'} (hf : ContMDiffOn I I' n f s)
    (hg : ContMDiffOn I J' n g s) : ContMDiffOn I (I'.prod J') n (fun x => (f x, g x)) s :=
  fun x hx => (hf x hx).prod_mk (hg x hx)

theorem ContMDiffOn.prod_mk_space {f : M → E'} {g : M → F'} (hf : ContMDiffOn I 𝓘(𝕜, E') n f s)
    (hg : ContMDiffOn I 𝓘(𝕜, F') n g s) : ContMDiffOn I 𝓘(𝕜, E' × F') n (fun x => (f x, g x)) s :=
  fun x hx => (hf x hx).prod_mk_space (hg x hx)

nonrec theorem ContMDiff.prod_mk {f : M → M'} {g : M → N'} (hf : ContMDiff I I' n f)
    (hg : ContMDiff I J' n g) : ContMDiff I (I'.prod J') n fun x => (f x, g x) := fun x =>
  (hf x).prod_mk (hg x)

theorem ContMDiff.prod_mk_space {f : M → E'} {g : M → F'} (hf : ContMDiff I 𝓘(𝕜, E') n f)
    (hg : ContMDiff I 𝓘(𝕜, F') n g) : ContMDiff I 𝓘(𝕜, E' × F') n fun x => (f x, g x) := fun x =>
  (hf x).prod_mk_space (hg x)

@[deprecated (since := "2024-11-20")] alias SmoothWithinAt.prod_mk := ContMDiffWithinAt.prod_mk

@[deprecated (since := "2024-11-20")]
alias SmoothWithinAt.prod_mk_space := ContMDiffWithinAt.prod_mk_space

@[deprecated (since := "2024-11-20")] alias SmoothAt.prod_mk := ContMDiffAt.prod_mk

@[deprecated (since := "2024-11-20")] alias SmoothAt.prod_mk_space := ContMDiffAt.prod_mk_space

@[deprecated (since := "2024-11-20")] alias SmoothOn.prod_mk := ContMDiffOn.prod_mk

@[deprecated (since := "2024-11-20")] alias SmoothOn.prod_mk_space := ContMDiffOn.prod_mk_space

@[deprecated (since := "2024-11-20")] alias Smooth.prod_mk := ContMDiff.prod_mk

@[deprecated (since := "2024-11-20")] alias Smooth.prod_mk_space := ContMDiff.prod_mk_space

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

@[deprecated (since := "2024-11-20")] alias smoothWithinAt_fst := contMDiffWithinAt_fst

@[deprecated (since := "2024-11-20")] alias smoothAt_fst := contMDiffAt_fst

@[deprecated (since := "2024-11-20")] alias smoothOn_fst := contMDiffOn_fst

@[deprecated (since := "2024-11-20")] alias smooth_fst := contMDiff_fst

theorem ContMDiffAt.fst {f : N → M × M'} {x : N} (hf : ContMDiffAt J (I.prod I') n f x) :
    ContMDiffAt J I n (fun x => (f x).1) x :=
  contMDiffAt_fst.comp x hf

theorem ContMDiff.fst {f : N → M × M'} (hf : ContMDiff J (I.prod I') n f) :
    ContMDiff J I n fun x => (f x).1 :=
  contMDiff_fst.comp hf

@[deprecated (since := "2024-11-20")] alias SmoothAt.fst := ContMDiffAt.fst

@[deprecated (since := "2024-11-20")] alias Smooth.fst := ContMDiff.fst

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

@[deprecated (since := "2024-11-20")] alias smoothWithinAt_snd := contMDiffWithinAt_snd

@[deprecated (since := "2024-11-20")] alias smoothAt_snd := contMDiffAt_snd

@[deprecated (since := "2024-11-20")] alias smoothOn_snd := contMDiffOn_snd

@[deprecated (since := "2024-11-20")] alias smooth_snd := contMDiff_snd

theorem ContMDiffAt.snd {f : N → M × M'} {x : N} (hf : ContMDiffAt J (I.prod I') n f x) :
    ContMDiffAt J I' n (fun x => (f x).2) x :=
  contMDiffAt_snd.comp x hf

theorem ContMDiff.snd {f : N → M × M'} (hf : ContMDiff J (I.prod I') n f) :
    ContMDiff J I' n fun x => (f x).2 :=
  contMDiff_snd.comp hf

@[deprecated (since := "2024-11-20")] alias SmoothAt.snd := ContMDiffAt.snd

@[deprecated (since := "2024-11-20")] alias Smooth.snd := ContMDiff.snd

end Projections

theorem contMDiffWithinAt_prod_iff (f : M → M' × N') :
    ContMDiffWithinAt I (I'.prod J') n f s x ↔
      ContMDiffWithinAt I I' n (Prod.fst ∘ f) s x ∧ ContMDiffWithinAt I J' n (Prod.snd ∘ f) s x :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prod_mk h.2⟩

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
      fun x hx ↦ ((contMDiffWithinAt_prod_iff f).1 (h x hx)).2⟩ ,
    fun h x hx ↦ (contMDiffWithinAt_prod_iff f).2 ⟨h.1 x hx, h.2 x hx⟩⟩

theorem contMDiffOn_prod_module_iff (f : M → F₁ × F₂) :
    ContMDiffOn I 𝓘(𝕜, F₁ × F₂) n f s ↔
      ContMDiffOn I 𝓘(𝕜, F₁) n (Prod.fst ∘ f) s ∧ ContMDiffOn I 𝓘(𝕜, F₂) n (Prod.snd ∘ f) s := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact contMDiffOn_prod_iff f

theorem contMDiff_prod_iff (f : M → M' × N') :
    ContMDiff I (I'.prod J') n f ↔
      ContMDiff I I' n (Prod.fst ∘ f) ∧ ContMDiff I J' n (Prod.snd ∘ f) :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => by convert h.1.prod_mk h.2⟩

theorem contMDiff_prod_module_iff (f : M → F₁ × F₂) :
    ContMDiff I 𝓘(𝕜, F₁ × F₂) n f ↔
      ContMDiff I 𝓘(𝕜, F₁) n (Prod.fst ∘ f) ∧ ContMDiff I 𝓘(𝕜, F₂) n (Prod.snd ∘ f) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact contMDiff_prod_iff f

theorem contMDiff_prod_assoc :
    ContMDiff ((I.prod I').prod J) (I.prod (I'.prod J)) n
      fun x : (M × M') × N => (x.1.1, x.1.2, x.2) :=
  contMDiff_fst.fst.prod_mk <| contMDiff_fst.snd.prod_mk contMDiff_snd

@[deprecated (since := "2024-11-20")] alias smoothAt_prod_iff := contMDiffAt_prod_iff

@[deprecated (since := "2024-11-20")] alias smooth_prod_iff := contMDiff_prod_iff

@[deprecated (since := "2024-11-20")] alias smooth_prod_assoc := contMDiff_prod_assoc

section prodMap

variable {g : N → N'} {r : Set N} {y : N}

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
theorem ContMDiffWithinAt.prod_map' {p : M × N} (hf : ContMDiffWithinAt I I' n f s p.1)
    (hg : ContMDiffWithinAt J J' n g r p.2) :
    ContMDiffWithinAt (I.prod J) (I'.prod J') n (Prod.map f g) (s ×ˢ r) p :=
  (hf.comp p contMDiffWithinAt_fst (prod_subset_preimage_fst _ _)).prod_mk <|
    hg.comp p contMDiffWithinAt_snd (prod_subset_preimage_snd _ _)

theorem ContMDiffWithinAt.prod_map (hf : ContMDiffWithinAt I I' n f s x)
    (hg : ContMDiffWithinAt J J' n g r y) :
    ContMDiffWithinAt (I.prod J) (I'.prod J') n (Prod.map f g) (s ×ˢ r) (x, y) :=
  ContMDiffWithinAt.prod_map' hf hg

theorem ContMDiffAt.prod_map (hf : ContMDiffAt I I' n f x) (hg : ContMDiffAt J J' n g y) :
    ContMDiffAt (I.prod J) (I'.prod J') n (Prod.map f g) (x, y) := by
  rw [← contMDiffWithinAt_univ] at *
  convert hf.prod_map hg
  exact univ_prod_univ.symm

theorem ContMDiffAt.prod_map' {p : M × N} (hf : ContMDiffAt I I' n f p.1)
    (hg : ContMDiffAt J J' n g p.2) : ContMDiffAt (I.prod J) (I'.prod J') n (Prod.map f g) p := by
  rcases p with ⟨⟩
  exact hf.prod_map hg

theorem ContMDiffOn.prod_map (hf : ContMDiffOn I I' n f s) (hg : ContMDiffOn J J' n g r) :
    ContMDiffOn (I.prod J) (I'.prod J') n (Prod.map f g) (s ×ˢ r) :=
  (hf.comp contMDiffOn_fst (prod_subset_preimage_fst _ _)).prod_mk <|
    hg.comp contMDiffOn_snd (prod_subset_preimage_snd _ _)

theorem ContMDiff.prod_map (hf : ContMDiff I I' n f) (hg : ContMDiff J J' n g) :
    ContMDiff (I.prod J) (I'.prod J') n (Prod.map f g) := by
  intro p
  exact (hf p.1).prod_map' (hg p.2)

@[deprecated (since := "2024-11-20")] alias SmoothWithinAt.prod_map := ContMDiffWithinAt.prod_map

@[deprecated (since := "2024-11-20")] alias SmoothAt.prod_map := ContMDiffAt.prod_map

@[deprecated (since := "2024-11-20")] alias SmoothOn.prod_map := ContMDiffOn.prod_map

@[deprecated (since := "2024-11-20")] alias Smooth.prod_map := ContMDiff.prod_map

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
    writtenInExtChartAt, extChartAt_model_space_eq_id, Function.comp_def, PartialEquiv.refl_coe, id]

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

@[deprecated (since := "2024-11-20")] alias smoothWithinAt_pi_space := contMDiffWithinAt_pi_space

@[deprecated (since := "2024-11-20")] alias smoothAt_pi_space := contMDiffAt_pi_space

@[deprecated (since := "2024-11-20")] alias smoothOn_pi_space := contMDiffOn_pi_space

@[deprecated (since := "2024-11-20")] alias smooth_pi_space := contMDiff_pi_space

end PiSpace

section disjointUnion

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] {n : WithTop ℕ∞} [Nonempty H]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {J : Type*} {J : ModelWithCorners 𝕜 E' H'}
  {N N' : Type*} [TopologicalSpace N] [TopologicalSpace N'] [ChartedSpace H' N] [ChartedSpace H' N']
  [IsManifold J n N] [IsManifold J n N'] [Nonempty H']

open Topology

lemma ContMDiff.inl : ContMDiff I I n (@Sum.inl M M') := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨continuous_inl.continuousAt, ?_⟩
  -- In extended charts, .inl equals the identity (on the chart sources).
  apply contDiffWithinAt_id.congr_of_eventuallyEq; swap
  · simp [ChartedSpace.sum_chartAt_inl]
    congr
    apply Sum.inl_injective.extend_apply (chartAt _ x)
  set C := chartAt H x
  have aux : ∀ x ∈ I.symm ⁻¹' C.target ∩ range I,
      (((C.lift_openEmbedding (IsOpenEmbedding.inl (Y := M'))).extend I)
        ∘ Sum.inl ∘ (C.extend I).symm) x = x := by
    intro x ⟨hx1, hx2⟩
    simp [Sum.inl_injective.extend_apply C, C.right_inv hx1, I.right_inv hx2]
  apply Filter.mem_of_superset ?_ aux
  rw [← I.image_eq (chartAt H x).target]
  exact (chartAt H x).extend_image_target_mem_nhds (mem_chart_source _ x)

lemma ContMDiff.inr : ContMDiff I I n (@Sum.inr M M') := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨continuous_inr.continuousAt, ?_⟩
  -- In extended charts, .inl equals the identity (on the chart sources).
  apply contDiffWithinAt_id.congr_of_eventuallyEq; swap
  · simp [ChartedSpace.sum_chartAt_inr]
    congr
    apply Sum.inr_injective.extend_apply (chartAt _ x)
  set C := chartAt H x
  have aux : ∀ e ∈ I.symm ⁻¹' (chartAt H x).target ∩ range I,
      (((C.lift_openEmbedding (IsOpenEmbedding.inr (X := M))).extend I)
        ∘ Sum.inr ∘ (C.extend I).symm) e = e := by
    intro x ⟨hx1, hx2⟩
    simp [Sum.inr_injective.extend_apply C, C.right_inv hx1, I.right_inv hx2]
  apply Filter.mem_of_superset ?_ aux
  rw [← I.image_eq (chartAt H x).target]
  exact (chartAt H x).extend_image_target_mem_nhds (mem_chart_source _ x)

-- TODO: move to ChartedSpace, sum section
-- make some of these simp?
lemma sum_chartAt_inl_apply {x : M} :
    ((chartAt H (.inl x : M ⊕ M')) (Sum.inl x)) = (chartAt H x) x := by
  rw [ChartedSpace.sum_chartAt_inl]
  exact PartialHomeomorph.lift_openEmbedding_apply _ _

lemma sum_chartAt_inr_apply {x : M'} :
    ((chartAt H (.inr x : M ⊕ M')) (Sum.inr x)) = (chartAt H x) x := by
  rw [ChartedSpace.sum_chartAt_inr]
  exact PartialHomeomorph.lift_openEmbedding_apply _ _

lemma extChartAt_inl_apply {x : M} :
    ((extChartAt I (.inl x : M ⊕ M')) (Sum.inl x)) = (extChartAt I x) x := by
  simp [sum_chartAt_inl_apply]

lemma extChartAt_inr_apply {x : M'} :
    ((extChartAt I (.inr x : M ⊕ M')) (Sum.inr x)) = (extChartAt I x) x := by
  simp [sum_chartAt_inr_apply]

lemma ContMDiff.sum_elim {f : M → N} {g : M' → N}
    (hf : ContMDiff I J n f) (hg : ContMDiff I J n g) : ContMDiff I J n (Sum.elim f g) := by
  intro p
  rw [contMDiffAt_iff]
  refine ⟨(Continuous.sum_elim hf.continuous hg.continuous).continuousAt, ?_⟩
  cases p with
  | inl x =>
    -- In charts around x : M, the map f ⊔ g looks like f.
    -- This is how they both look like in extended charts.
    have : ContDiffWithinAt 𝕜 n ((extChartAt J (f x)) ∘ f ∘ (extChartAt I x).symm)
        (range I) ((extChartAt I (.inl x : M ⊕ M')) (Sum.inl x)) := by
      let hf' := hf x
      rw [contMDiffAt_iff] at hf'
      simpa only [extChartAt_inl_apply] using hf'.2
    apply this.congr_of_eventuallyEq
    · simp only [extChartAt, Sum.elim_inl, ChartedSpace.sum_chartAt_inl,
        Sum.inl_injective.extend_apply]
      filter_upwards with a
      congr
    · -- They agree at the image of x.
      simp only [extChartAt, ChartedSpace.sum_chartAt_inl, Sum.elim_inl]
      congr
  | inr x => sorry -- should be analogous

end disjointUnion
