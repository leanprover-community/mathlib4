/-
Copyright © 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Floris van Doorn
-/
import Mathlib.Geometry.Manifold.MFDeriv
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Geometry.Manifold.Algebra.LieGroup

#align_import geometry.manifold.vector_bundle.smooth_section from "leanprover-community/mathlib"@"e473c3198bb41f68560cab68a0529c854b618833"

/-!
# Smooth sections

In this file we define the type `ContMDiffSection` of `n` times continuously differentiable
sections of a smooth vector bundle over a manifold `M` and prove that it's a module.
-/


open Bundle Filter Function

open scoped Bundle Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type*}
  [TopologicalSpace H] {H' : Type*} [TopologicalSpace H'] (I : ModelWithCorners 𝕜 E H)
  (I' : ModelWithCorners 𝕜 E' H') {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {M' : Type*}
  [TopologicalSpace M'] [ChartedSpace H' M'] {E'' : Type*} [NormedAddCommGroup E'']
  [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M''] [SmoothManifoldWithCorners I M]

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : ℕ∞)
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  -- `V` vector bundle
  [∀ x, AddCommGroup (V x)]
  [∀ x, Module 𝕜 (V x)]

variable [∀ x : M, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [SmoothVectorBundle F V I]

/-- Bundled `n` times continuously differentiable sections of a vector bundle. -/
structure ContMDiffSection where
  protected toFun : ∀ x, V x
  protected contMDiff_toFun : ContMDiff I (I.prod 𝓘(𝕜, F)) n fun x ↦
    TotalSpace.mk' F x (toFun x)
#align cont_mdiff_section ContMDiffSection

/-- Bundled smooth sections of a vector bundle. -/
@[reducible]
def SmoothSection :=
  ContMDiffSection I F ⊤ V
#align smooth_section SmoothSection

scoped[Manifold] notation "Cₛ^" n "⟮" I "; " F ", " V "⟯" => ContMDiffSection I F n V

namespace ContMDiffSection

variable {I} {I'} {n} {F} {V}

instance : FunLike Cₛ^n⟮I; F, V⟯ M V where
  coe := ContMDiffSection.toFun
  coe_injective' := by rintro ⟨⟩ ⟨⟩ h; congr
                       -- ⊢ { toFun := toFun✝¹, contMDiff_toFun := contMDiff_toFun✝¹ } = { toFun := toFu …
                                       -- 🎉 no goals

variable {s t : Cₛ^n⟮I; F, V⟯}

@[simp]
theorem coeFn_mk (s : ∀ x, V x)
    (hs : ContMDiff I (I.prod 𝓘(𝕜, F)) n fun x => TotalSpace.mk x (s x)) :
    (mk s hs : ∀ x, V x) = s :=
  rfl
#align cont_mdiff_section.coe_fn_mk ContMDiffSection.coeFn_mk

protected theorem contMDiff (s : Cₛ^n⟮I; F, V⟯) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n fun x => TotalSpace.mk' F x (s x : V x) :=
  s.contMDiff_toFun
#align cont_mdiff_section.cont_mdiff ContMDiffSection.contMDiff

protected theorem smooth (s : Cₛ^∞⟮I; F, V⟯) :
    Smooth I (I.prod 𝓘(𝕜, F)) fun x => TotalSpace.mk' F x (s x : V x) :=
  s.contMDiff_toFun
#align cont_mdiff_section.smooth ContMDiffSection.smooth

protected theorem mdifferentiable' (s : Cₛ^n⟮I; F, V⟯) (hn : 1 ≤ n) :
    MDifferentiable I (I.prod 𝓘(𝕜, F)) fun x => TotalSpace.mk' F x (s x : V x) :=
  s.contMDiff.mdifferentiable hn
#align cont_mdiff_section.mdifferentiable' ContMDiffSection.mdifferentiable'

protected theorem mdifferentiable (s : Cₛ^∞⟮I; F, V⟯) :
    MDifferentiable I (I.prod 𝓘(𝕜, F)) fun x => TotalSpace.mk' F x (s x : V x) :=
  s.contMDiff.mdifferentiable le_top
#align cont_mdiff_section.mdifferentiable ContMDiffSection.mdifferentiable

protected theorem mdifferentiableAt (s : Cₛ^∞⟮I; F, V⟯) {x} :
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x => TotalSpace.mk' F x (s x : V x)) x :=
  s.mdifferentiable x
#align cont_mdiff_section.mdifferentiable_at ContMDiffSection.mdifferentiableAt

theorem coe_inj ⦃s t : Cₛ^n⟮I; F, V⟯⦄ (h : (s : ∀ x, V x) = t) : s = t :=
  FunLike.ext' h
#align cont_mdiff_section.coe_inj ContMDiffSection.coe_inj

theorem coe_injective : Injective ((↑) : Cₛ^n⟮I; F, V⟯ → ∀ x, V x) :=
  coe_inj
#align cont_mdiff_section.coe_injective ContMDiffSection.coe_injective

@[ext]
theorem ext (h : ∀ x, s x = t x) : s = t := FunLike.ext _ _ h
#align cont_mdiff_section.ext ContMDiffSection.ext

instance instAdd : Add Cₛ^n⟮I; F, V⟯ := by
  refine' ⟨fun s t => ⟨s + t, _⟩⟩
  -- ⊢ ContMDiff I (ModelWithCorners.prod I 𝓘(𝕜, F)) n fun x => TotalSpace.mk' F x  …
  intro x₀
  -- ⊢ ContMDiffAt I (ModelWithCorners.prod I 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F …
  have hs := s.contMDiff x₀
  -- ⊢ ContMDiffAt I (ModelWithCorners.prod I 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F …
  have ht := t.contMDiff x₀
  -- ⊢ ContMDiffAt I (ModelWithCorners.prod I 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F …
  rw [contMDiffAt_section] at hs ht ⊢
  -- ⊢ ContMDiffAt I 𝓘(𝕜, F) n (fun x => (↑(trivializationAt F V x₀) { proj := x, s …
  set e := trivializationAt F V x₀
  -- ⊢ ContMDiffAt I 𝓘(𝕜, F) n (fun x => (↑e { proj := x, snd := (↑s + ↑t) x }).snd …
  refine' (hs.add ht).congr_of_eventuallyEq _
  -- ⊢ (fun x => (↑e { proj := x, snd := (↑s + ↑t) x }).snd) =ᶠ[nhds x₀] (fun x =>  …
  refine' eventually_of_mem (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀) _
  -- ⊢ ∀ (x : M), x ∈ e.baseSet → (fun x => (↑e { proj := x, snd := (↑s + ↑t) x }). …
  intro x hx
  -- ⊢ (fun x => (↑e { proj := x, snd := (↑s + ↑t) x }).snd) x = ((fun x => (↑e { p …
  apply (e.linear 𝕜 hx).1
  -- 🎉 no goals
#align cont_mdiff_section.has_add ContMDiffSection.instAdd

@[simp]
theorem coe_add (s t : Cₛ^n⟮I; F, V⟯) : ⇑(s + t) = ⇑s + t :=
  rfl
#align cont_mdiff_section.coe_add ContMDiffSection.coe_add

instance instSub : Sub Cₛ^n⟮I; F, V⟯ := by
  refine' ⟨fun s t => ⟨s - t, _⟩⟩
  -- ⊢ ContMDiff I (ModelWithCorners.prod I 𝓘(𝕜, F)) n fun x => TotalSpace.mk' F x  …
  intro x₀
  -- ⊢ ContMDiffAt I (ModelWithCorners.prod I 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F …
  have hs := s.contMDiff x₀
  -- ⊢ ContMDiffAt I (ModelWithCorners.prod I 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F …
  have ht := t.contMDiff x₀
  -- ⊢ ContMDiffAt I (ModelWithCorners.prod I 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F …
  rw [contMDiffAt_section] at hs ht ⊢
  -- ⊢ ContMDiffAt I 𝓘(𝕜, F) n (fun x => (↑(trivializationAt F V x₀) { proj := x, s …
  set e := trivializationAt F V x₀
  -- ⊢ ContMDiffAt I 𝓘(𝕜, F) n (fun x => (↑e { proj := x, snd := (↑s - ↑t) x }).snd …
  refine' (hs.sub ht).congr_of_eventuallyEq _
  -- ⊢ (fun x => (↑e { proj := x, snd := (↑s - ↑t) x }).snd) =ᶠ[nhds x₀] fun x => ( …
  refine' eventually_of_mem (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀) _
  -- ⊢ ∀ (x : M), x ∈ e.baseSet → (fun x => (↑e { proj := x, snd := (↑s - ↑t) x }). …
  intro x hx
  -- ⊢ (fun x => (↑e { proj := x, snd := (↑s - ↑t) x }).snd) x = (fun x => (↑e { pr …
  apply (e.linear 𝕜 hx).map_sub
  -- 🎉 no goals
#align cont_mdiff_section.has_sub ContMDiffSection.instSub

@[simp]
theorem coe_sub (s t : Cₛ^n⟮I; F, V⟯) : ⇑(s - t) = s - t :=
  rfl
#align cont_mdiff_section.coe_sub ContMDiffSection.coe_sub

instance instZero : Zero Cₛ^n⟮I; F, V⟯ :=
  ⟨⟨fun _ => 0, (smooth_zeroSection 𝕜 V).of_le le_top⟩⟩
#align cont_mdiff_section.has_zero ContMDiffSection.instZero

instance inhabited : Inhabited Cₛ^n⟮I; F, V⟯ :=
  ⟨0⟩
#align cont_mdiff_section.inhabited ContMDiffSection.inhabited

@[simp]
theorem coe_zero : ⇑(0 : Cₛ^n⟮I; F, V⟯) = 0 :=
  rfl
#align cont_mdiff_section.coe_zero ContMDiffSection.coe_zero

instance instSMul : SMul 𝕜 Cₛ^n⟮I; F, V⟯ := by
  refine' ⟨fun c s => ⟨c • ⇑s, _⟩⟩
  -- ⊢ ContMDiff I (ModelWithCorners.prod I 𝓘(𝕜, F)) n fun x => TotalSpace.mk' F x  …
  intro x₀
  -- ⊢ ContMDiffAt I (ModelWithCorners.prod I 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F …
  have hs := s.contMDiff x₀
  -- ⊢ ContMDiffAt I (ModelWithCorners.prod I 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F …
  rw [contMDiffAt_section] at hs ⊢
  -- ⊢ ContMDiffAt I 𝓘(𝕜, F) n (fun x => (↑(trivializationAt F V x₀) { proj := x, s …
  set e := trivializationAt F V x₀
  -- ⊢ ContMDiffAt I 𝓘(𝕜, F) n (fun x => (↑e { proj := x, snd := (c • ↑s) x }).snd) …
  refine' (contMDiffAt_const.smul hs).congr_of_eventuallyEq _
  -- ⊢ 𝕜
  · exact c
    -- 🎉 no goals
  refine' eventually_of_mem (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀) _
  -- ⊢ ∀ (x : M), x ∈ e.baseSet → (fun x => (↑e { proj := x, snd := (c • ↑s) x }).s …
  intro x hx
  -- ⊢ (fun x => (↑e { proj := x, snd := (c • ↑s) x }).snd) x = (fun p => c • (↑e { …
  apply (e.linear 𝕜 hx).2
  -- 🎉 no goals
#align cont_mdiff_section.has_smul ContMDiffSection.instSMul

@[simp]
theorem coe_smul (r : 𝕜) (s : Cₛ^n⟮I; F, V⟯) : ⇑(r • s : Cₛ^n⟮I; F, V⟯) = r • ⇑s :=
  rfl
#align cont_mdiff_section.coe_smul ContMDiffSection.coe_smul

instance instNeg : Neg Cₛ^n⟮I; F, V⟯ := by
  refine' ⟨fun s => ⟨-s, _⟩⟩
  -- ⊢ ContMDiff I (ModelWithCorners.prod I 𝓘(𝕜, F)) n fun x => TotalSpace.mk' F x  …
  intro x₀
  -- ⊢ ContMDiffAt I (ModelWithCorners.prod I 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F …
  have hs := s.contMDiff x₀
  -- ⊢ ContMDiffAt I (ModelWithCorners.prod I 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F …
  rw [contMDiffAt_section] at hs ⊢
  -- ⊢ ContMDiffAt I 𝓘(𝕜, F) n (fun x => (↑(trivializationAt F V x₀) { proj := x, s …
  set e := trivializationAt F V x₀
  -- ⊢ ContMDiffAt I 𝓘(𝕜, F) n (fun x => (↑e { proj := x, snd := (-↑s) x }).snd) x₀
  refine' hs.neg.congr_of_eventuallyEq _
  -- ⊢ (fun x => (↑e { proj := x, snd := (-↑s) x }).snd) =ᶠ[nhds x₀] fun x => -(↑e  …
  refine' eventually_of_mem (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀) _
  -- ⊢ ∀ (x : M), x ∈ e.baseSet → (fun x => (↑e { proj := x, snd := (-↑s) x }).snd) …
  intro x hx
  -- ⊢ (fun x => (↑e { proj := x, snd := (-↑s) x }).snd) x = (fun x => -(↑e { proj  …
  apply (e.linear 𝕜 hx).map_neg
  -- 🎉 no goals
#align cont_mdiff_section.has_neg ContMDiffSection.instNeg

@[simp]
theorem coe_neg (s : Cₛ^n⟮I; F, V⟯) : ⇑(-s : Cₛ^n⟮I; F, V⟯) = -s :=
  rfl
#align cont_mdiff_section.coe_neg ContMDiffSection.coe_neg

instance instNSMul : SMul ℕ Cₛ^n⟮I; F, V⟯ :=
  ⟨nsmulRec⟩
#align cont_mdiff_section.has_nsmul ContMDiffSection.instNSMul

@[simp]
theorem coe_nsmul (s : Cₛ^n⟮I; F, V⟯) (k : ℕ) : ⇑(k • s : Cₛ^n⟮I; F, V⟯) = k • ⇑s := by
  induction' k with k ih
  -- ⊢ ↑(Nat.zero • s) = Nat.zero • ↑s
  · simp_rw [Nat.zero_eq, zero_smul]; rfl
    -- ⊢ ↑(0 • s) = 0
                                      -- 🎉 no goals
  simp_rw [succ_nsmul, ← ih]; rfl
  -- ⊢ ↑(Nat.succ k • s) = ↑s + ↑(k • s)
                              -- 🎉 no goals
#align cont_mdiff_section.coe_nsmul ContMDiffSection.coe_nsmul

instance instZSMul : SMul ℤ Cₛ^n⟮I; F, V⟯ :=
  ⟨zsmulRec⟩
#align cont_mdiff_section.has_zsmul ContMDiffSection.instZSMul

@[simp]
theorem coe_zsmul (s : Cₛ^n⟮I; F, V⟯) (z : ℤ) : ⇑(z • s : Cₛ^n⟮I; F, V⟯) = z • ⇑s := by
  cases' z with n n
  -- ⊢ ↑(Int.ofNat n • s) = Int.ofNat n • ↑s
  refine' (coe_nsmul s n).trans _
  -- ⊢ n • ↑s = Int.ofNat n • ↑s
  simp only [Int.ofNat_eq_coe, coe_nat_zsmul]
  -- ⊢ ↑(Int.negSucc n • s) = Int.negSucc n • ↑s
  refine' (congr_arg Neg.neg (coe_nsmul s (n + 1))).trans _
  -- ⊢ -((n + 1) • ↑s) = Int.negSucc n • ↑s
  simp only [negSucc_zsmul, neg_inj]
  -- 🎉 no goals
#align cont_mdiff_section.coe_zsmul ContMDiffSection.coe_zsmul

instance instAddCommGroup : AddCommGroup Cₛ^n⟮I; F, V⟯ :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul
#align cont_mdiff_section.add_comm_group ContMDiffSection.instAddCommGroup

variable (I F V n)

/-- The additive morphism from smooth sections to dependent maps. -/
def coeAddHom : Cₛ^n⟮I; F, V⟯ →+ ∀ x, V x where
  toFun := (↑)
  map_zero' := coe_zero
  map_add' := coe_add
#align cont_mdiff_section.coe_add_hom ContMDiffSection.coeAddHom

variable {I F V n}

instance instModule : Module 𝕜 Cₛ^n⟮I; F, V⟯ :=
  coe_injective.module 𝕜 (coeAddHom I F n V) coe_smul
#align cont_mdiff_section.module ContMDiffSection.instModule

end ContMDiffSection
