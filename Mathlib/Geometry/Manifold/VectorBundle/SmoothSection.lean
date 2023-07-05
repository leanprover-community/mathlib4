/-
Copyright © 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Floris van Doorn

! This file was ported from Lean 3 source module geometry.manifold.vector_bundle.smooth_section
! leanprover-community/mathlib commit e473c3198bb41f68560cab68a0529c854b618833
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Geometry.Manifold.ContMdiffMfderiv
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Smooth sections

In this file we define the type `cont_mdiff_section` of `n` times continuously differentiable
sections of a smooth vector bundle over a manifold `M` and prove that it's a module.
-/


open Bundle Filter Function

open scoped Bundle Manifold

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type _} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type _}
  [TopologicalSpace H] {H' : Type _} [TopologicalSpace H'] (I : ModelWithCorners 𝕜 E H)
  (I' : ModelWithCorners 𝕜 E' H') {M : Type _} [TopologicalSpace M] [ChartedSpace H M] {M' : Type _}
  [TopologicalSpace M'] [ChartedSpace H' M'] {E'' : Type _} [NormedAddCommGroup E'']
  [NormedSpace 𝕜 E''] {H'' : Type _} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type _} [TopologicalSpace M''] [ChartedSpace H'' M''] [SmoothManifoldWithCorners I M]

variable (F : Type _) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : ℕ∞)
  (V : M → Type _) [TopologicalSpace (TotalSpace F V)]
  -- `V` vector bundle
  [∀ x, AddCommGroup (V x)]
  [∀ x, Module 𝕜 (V x)]

variable [∀ x : M, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [SmoothVectorBundle F V I]

/-- Bundled `n` times continuously differentiable sections of a vector bundle. -/
@[protect_proj]
structure ContMdiffSection where
  toFun : ∀ x, V x
  contMDiff_toFun : ContMDiff I (I.Prod 𝓘(𝕜, F)) n fun x => (total_space.mk' F) x (to_fun x)
#align cont_mdiff_section ContMdiffSection

/-- Bundled smooth sections of a vector bundle. -/
@[reducible]
def SmoothSection :=
  ContMdiffSection I F ⊤ V
#align smooth_section SmoothSection

scoped[Manifold] notation "Cₛ^" n "⟮" I "; " F ", " V "⟯" => ContMdiffSection I F n V

namespace ContMdiffSection

variable {I} {I'} {n} {F} {V}

instance : CoeFun Cₛ^n⟮I; F, V⟯ fun s => ∀ x, V x :=
  ⟨ContMdiffSection.toFun⟩

variable {s t : Cₛ^n⟮I; F, V⟯}

@[simp]
theorem coeFn_mk (s : ∀ x, V x)
    (hs : ContMDiff I (I.Prod 𝓘(𝕜, F)) n fun x => TotalSpace.mk x (s x)) :
    (mk s hs : ∀ x, V x) = s :=
  rfl
#align cont_mdiff_section.coe_fn_mk ContMdiffSection.coeFn_mk

protected theorem contMDiff (s : Cₛ^n⟮I; F, V⟯) :
    ContMDiff I (I.Prod 𝓘(𝕜, F)) n fun x => (total_space.mk' F) x (s x : V x) :=
  s.contMDiff_toFun
#align cont_mdiff_section.cont_mdiff ContMdiffSection.contMDiff

protected theorem smooth (s : Cₛ^∞⟮I; F, V⟯) :
    Smooth I (I.Prod 𝓘(𝕜, F)) fun x => (total_space.mk' F) x (s x : V x) :=
  s.contMDiff_toFun
#align cont_mdiff_section.smooth ContMdiffSection.smooth

protected theorem mdifferentiable' (s : Cₛ^n⟮I; F, V⟯) (hn : 1 ≤ n) :
    MDifferentiable I (I.Prod 𝓘(𝕜, F)) fun x => (total_space.mk' F) x (s x : V x) :=
  s.ContMDiff.MDifferentiable hn
#align cont_mdiff_section.mdifferentiable' ContMdiffSection.mdifferentiable'

protected theorem mDifferentiable (s : Cₛ^∞⟮I; F, V⟯) :
    MDifferentiable I (I.Prod 𝓘(𝕜, F)) fun x => (total_space.mk' F) x (s x : V x) :=
  s.ContMDiff.MDifferentiable le_top
#align cont_mdiff_section.mdifferentiable ContMdiffSection.mDifferentiable

protected theorem mDifferentiableAt (s : Cₛ^∞⟮I; F, V⟯) {x} :
    MDifferentiableAt I (I.Prod 𝓘(𝕜, F)) (fun x => (total_space.mk' F) x (s x : V x)) x :=
  s.MDifferentiable x
#align cont_mdiff_section.mdifferentiable_at ContMdiffSection.mDifferentiableAt

theorem coe_inj ⦃s t : Cₛ^n⟮I; F, V⟯⦄ (h : (s : ∀ x, V x) = t) : s = t := by
  cases s <;> cases t <;> cases h <;> rfl
#align cont_mdiff_section.coe_inj ContMdiffSection.coe_inj

theorem coe_injective : Injective (coeFn : Cₛ^n⟮I; F, V⟯ → ∀ x, V x) :=
  coe_inj
#align cont_mdiff_section.coe_injective ContMdiffSection.coe_injective

@[ext]
theorem ext (h : ∀ x, s x = t x) : s = t := by cases s <;> cases t <;> congr <;> exact funext h
#align cont_mdiff_section.ext ContMdiffSection.ext

instance hasAdd : Add Cₛ^n⟮I; F, V⟯ := by
  refine' ⟨fun s t => ⟨s + t, _⟩⟩
  intro x₀
  have hs := s.cont_mdiff x₀
  have ht := t.cont_mdiff x₀
  rw [cont_mdiff_at_section] at hs ht ⊢
  set e := trivialization_at F V x₀
  refine' (hs.add ht).congr_of_eventuallyEq _
  refine' eventually_of_mem (e.open_base_set.mem_nhds <| mem_base_set_trivialization_at F V x₀) _
  intro x hx
  apply (e.linear 𝕜 hx).1
#align cont_mdiff_section.has_add ContMdiffSection.hasAdd

@[simp]
theorem coe_add (s t : Cₛ^n⟮I; F, V⟯) : ⇑(s + t) = s + t :=
  rfl
#align cont_mdiff_section.coe_add ContMdiffSection.coe_add

instance hasSub : Sub Cₛ^n⟮I; F, V⟯ := by
  refine' ⟨fun s t => ⟨s - t, _⟩⟩
  intro x₀
  have hs := s.cont_mdiff x₀
  have ht := t.cont_mdiff x₀
  rw [cont_mdiff_at_section] at hs ht ⊢
  set e := trivialization_at F V x₀
  refine' (hs.sub ht).congr_of_eventuallyEq _
  refine' eventually_of_mem (e.open_base_set.mem_nhds <| mem_base_set_trivialization_at F V x₀) _
  intro x hx
  apply (e.linear 𝕜 hx).map_sub
#align cont_mdiff_section.has_sub ContMdiffSection.hasSub

@[simp]
theorem coe_sub (s t : Cₛ^n⟮I; F, V⟯) : ⇑(s - t) = s - t :=
  rfl
#align cont_mdiff_section.coe_sub ContMdiffSection.coe_sub

instance hasZero : Zero Cₛ^n⟮I; F, V⟯ :=
  ⟨⟨fun x => 0, (smooth_zeroSection 𝕜 V).of_le le_top⟩⟩
#align cont_mdiff_section.has_zero ContMdiffSection.hasZero

instance inhabited : Inhabited Cₛ^n⟮I; F, V⟯ :=
  ⟨0⟩
#align cont_mdiff_section.inhabited ContMdiffSection.inhabited

@[simp]
theorem coe_zero : ⇑(0 : Cₛ^n⟮I; F, V⟯) = 0 :=
  rfl
#align cont_mdiff_section.coe_zero ContMdiffSection.coe_zero

instance hasSmul : SMul 𝕜 Cₛ^n⟮I; F, V⟯ := by
  refine' ⟨fun c s => ⟨c • s, _⟩⟩
  intro x₀
  have hs := s.cont_mdiff x₀
  rw [cont_mdiff_at_section] at hs ⊢
  set e := trivialization_at F V x₀
  refine' (cont_mdiff_at_const.smul hs).congr_of_eventuallyEq _
  · exact c
  refine' eventually_of_mem (e.open_base_set.mem_nhds <| mem_base_set_trivialization_at F V x₀) _
  intro x hx
  apply (e.linear 𝕜 hx).2
#align cont_mdiff_section.has_smul ContMdiffSection.hasSmul

@[simp]
theorem coe_smul (r : 𝕜) (s : Cₛ^n⟮I; F, V⟯) : ⇑(r • s : Cₛ^n⟮I; F, V⟯) = r • s :=
  rfl
#align cont_mdiff_section.coe_smul ContMdiffSection.coe_smul

instance hasNeg : Neg Cₛ^n⟮I; F, V⟯ := by
  refine' ⟨fun s => ⟨-s, _⟩⟩
  intro x₀
  have hs := s.cont_mdiff x₀
  rw [cont_mdiff_at_section] at hs ⊢
  set e := trivialization_at F V x₀
  refine' hs.neg.congr_of_eventually_eq _
  refine' eventually_of_mem (e.open_base_set.mem_nhds <| mem_base_set_trivialization_at F V x₀) _
  intro x hx
  apply (e.linear 𝕜 hx).map_neg
#align cont_mdiff_section.has_neg ContMdiffSection.hasNeg

@[simp]
theorem coe_neg (s : Cₛ^n⟮I; F, V⟯) : ⇑(-s : Cₛ^n⟮I; F, V⟯) = -s :=
  rfl
#align cont_mdiff_section.coe_neg ContMdiffSection.coe_neg

instance hasNsmul : SMul ℕ Cₛ^n⟮I; F, V⟯ :=
  ⟨nsmulRec⟩
#align cont_mdiff_section.has_nsmul ContMdiffSection.hasNsmul

@[simp]
theorem coe_nsmul (s : Cₛ^n⟮I; F, V⟯) (k : ℕ) : ⇑(k • s : Cₛ^n⟮I; F, V⟯) = k • s := by
  induction' k with k ih
  · simp_rw [zero_smul]; rfl
  simp_rw [succ_nsmul, ← ih]; rfl
#align cont_mdiff_section.coe_nsmul ContMdiffSection.coe_nsmul

instance hasZsmul : SMul ℤ Cₛ^n⟮I; F, V⟯ :=
  ⟨zsmulRec⟩
#align cont_mdiff_section.has_zsmul ContMdiffSection.hasZsmul

@[simp]
theorem coe_zsmul (s : Cₛ^n⟮I; F, V⟯) (z : ℤ) : ⇑(z • s : Cₛ^n⟮I; F, V⟯) = z • s := by
  cases' z with n n
  refine' (coe_nsmul s n).trans _
  simp only [Int.ofNat_eq_coe, coe_nat_zsmul]
  refine' (congr_arg Neg.neg (coe_nsmul s (n + 1))).trans _
  simp only [negSucc_zsmul, neg_inj]
#align cont_mdiff_section.coe_zsmul ContMdiffSection.coe_zsmul

instance addCommGroup : AddCommGroup Cₛ^n⟮I; F, V⟯ :=
  coe_injective.AddCommGroup _ coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul
#align cont_mdiff_section.add_comm_group ContMdiffSection.addCommGroup

variable (I F V n)

/-- The additive morphism from smooth sections to dependent maps. -/
def coeAddHom : Cₛ^n⟮I; F, V⟯ →+ ∀ x, V x where
  toFun := coeFn
  map_zero' := coe_zero
  map_add' := coe_add
#align cont_mdiff_section.coe_add_hom ContMdiffSection.coeAddHom

variable {I F V n}

instance module : Module 𝕜 Cₛ^n⟮I; F, V⟯ :=
  coe_injective.Module 𝕜 (coeAddHom I F n V) coe_smul
#align cont_mdiff_section.module ContMdiffSection.module

end ContMdiffSection

