/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Floris van Doorn
-/
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# `C^n` sections

In this file we define the type `ContMDiffSection` of `n` times continuously differentiable
sections of a vector bundle over a manifold `M` and prove that it's a module.
-/


open Bundle Filter Function

open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  -- `V` vector bundle
  [∀ x : M, TopologicalSpace (V x)] [FiberBundle F V]

-- Binary and finite sums and scalar products of smooth sections are smooth
-- XXX: also add nsmul and zsmul lemmas (re-using proofs later in this file)
section operations

-- Let V be a vector bundle
variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

variable {I F n V}

variable {f : M → 𝕜} {a : 𝕜} {s t : Π x : M, V x} {u : Set M} {x₀ : M}

lemma contMDiffWithinAt_add_section
    (hs : ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) u x₀)
    (ht : ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t x)) u x₀) :
    ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x ((s + t) x)) u x₀ := by
  rw [contMDiffWithinAt_section] at hs ht ⊢
  set e := trivializationAt F V x₀
  refine (hs.add ht).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
    · exact mem_nhdsWithin_of_mem_nhds <|
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀)
    · intro x hx
      apply (e.linear 𝕜 hx).1
  · apply (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).1

lemma contMDiffAt_add_section
    (hs : ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) x₀)
    (ht : ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t x)) x₀) :
    ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x ((s + t) x)) x₀ := by
  rw [contMDiffAt_section] at hs ht ⊢
  set e := trivializationAt F V x₀
  refine (hs.add ht).congr_of_eventuallyEq ?_
  refine eventually_of_mem (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀) ?_
  intro x hx
  apply (e.linear 𝕜 hx).1

lemma contMDiffOn_add_section
    (hs : ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) u)
    (ht : ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t x)) u) :
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x ((s + t) x)) u :=
  fun x₀ hx₀ ↦ contMDiffWithinAt_add_section (hs x₀ hx₀) (ht x₀ hx₀)

lemma contMDiff_add_section
    (hs : ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)))
    (ht : ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t x))) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x ((s + t) x)) :=
  fun x₀ ↦ contMDiffAt_add_section (hs x₀) (ht x₀)

lemma contMDiffWithinAt_neg_section
    (hs : ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) u x₀) :
    ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (- s x)) u x₀ := by
  rw [contMDiffWithinAt_section] at hs ⊢
  set e := trivializationAt F V x₀
  refine hs.neg.congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
    · exact mem_nhdsWithin_of_mem_nhds <|
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀)
    · intro x hx
      apply (e.linear 𝕜 hx).map_neg
  · apply (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).map_neg

lemma contMDiffAt_neg_section
    (hs : ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) x₀) :
    ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (- s x)) x₀ :=
  contMDiffWithinAt_neg_section hs

lemma contMDiffOn_neg_section
    (hs : ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) u) :
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (-s x)) u :=
  fun x₀ hx₀ ↦ contMDiffWithinAt_neg_section (hs x₀ hx₀)

lemma contMDiff_neg_section
    (hs : ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x))) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (-s x)) :=
  fun x₀ ↦ contMDiffAt_neg_section (hs x₀)

lemma contMDiffWithinAt_sub_section
    (hs : ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) u x₀)
    (ht : ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t x)) u x₀) :
    ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x ((s - t) x)) u x₀ := by
  rw [sub_eq_add_neg]
  apply contMDiffWithinAt_add_section hs <| contMDiffWithinAt_neg_section ht

lemma contMDiffAt_sub_section
    (hs : ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) x₀)
    (ht : ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t x)) x₀) :
    ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x ((s - t) x)) x₀ := by
  rw [sub_eq_add_neg]
  apply contMDiffAt_add_section hs <| contMDiffAt_neg_section ht

lemma contMDiffOn_sub_section
    (hs : ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) u)
    (ht : ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t x)) u) :
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x ((s - t) x)) u :=
  fun x₀ hx₀ ↦ contMDiffWithinAt_sub_section (hs x₀ hx₀) (ht x₀ hx₀)

lemma contMDiff_sub_section
    (hs : ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)))
    (ht : ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t x))) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x ((s - t) x)) :=
  fun x₀ ↦ contMDiffAt_sub_section (hs x₀) (ht x₀)

lemma contMDiffWithinAt_smul_section
    (hs : ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) u x₀)
    (hf : ContMDiffWithinAt I 𝓘(𝕜) n f u x₀) :
    ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (f x • s x)) u x₀ := by
  rw [contMDiffWithinAt_section] at hs ⊢
  set e := trivializationAt F V x₀
  refine (hf.smul hs).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
    · exact mem_nhdsWithin_of_mem_nhds <|
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀)
    · intro x hx
      apply (e.linear 𝕜 hx).2
  · apply (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).2

lemma contMDiffAt_smul_section
    (hs : ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) x₀)
    (hf : ContMDiffAt I 𝓘(𝕜) n f x₀) :
    ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (f x • s x)) x₀ := by
  rw [contMDiffAt_section] at hs ⊢
  set e := trivializationAt F V x₀
  refine (hf.smul hs).congr_of_eventuallyEq ?_
  refine eventually_of_mem (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀) ?_
  intro x hx
  apply (e.linear 𝕜 hx).2

lemma contMDiffOn_smul_section
    (hs : ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) u)
    (hf : ContMDiffOn I 𝓘(𝕜) n f u) :
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (f x • s x)) u :=
  fun x₀ hx₀ ↦ contMDiffWithinAt_smul_section (hs x₀ hx₀) (hf x₀ hx₀)

lemma contMDiff_smul_section
    (hs : ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)))
    (hf : ContMDiff I 𝓘(𝕜) n f) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (f x • s x)) :=
  fun x₀ ↦ contMDiffAt_smul_section (hs x₀) (hf x₀)

lemma contMDiffWithinAt_smul_const_section
    (hs : ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) u x₀) :
    ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (a • s x)) u x₀ :=
  contMDiffWithinAt_smul_section hs contMDiffWithinAt_const

lemma contMDiffAt_smul_const_section
    (hs : ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) x₀) :
    ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (a • s x)) x₀ :=
  contMDiffAt_smul_section hs contMDiffAt_const

lemma contMDiffOn_smul_const_section
    (hs : ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) u) :
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (a • s x)) u :=
  contMDiffOn_smul_section hs contMDiffOn_const

lemma contMDiff_smul_const_section
    (hs : ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x))) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (a • s x)) :=
  fun x₀ ↦ contMDiffAt_smul_const_section (hs x₀)

lemma contMDiffWithinAt_finsum_section {ι : Type*} {s : Finset ι} {t : ι → (x : M) → V x}
    (hs : ∀ i, ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t i x)) u x₀) :
    ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n
      (fun x ↦ TotalSpace.mk' F x (∑ i ∈ s, (t i x))) u x₀ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty] using contMDiffWithinAt_zeroSection ..
  | insert i s hi h => simpa [Finset.sum_insert hi] using contMDiffWithinAt_add_section (hs i) h

lemma contMDiffAt_finsum_section {ι : Type*} {s : Finset ι} {t : ι → (x : M) → V x} {x₀ : M}
    (hs : ∀ i, ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t i x)) x₀) :
    ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (∑ i ∈ s, (t i x))) x₀ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using contMDiff_zeroSection ..
  | insert i s hi h => simpa [Finset.sum_insert hi] using contMDiffWithinAt_add_section (hs i) h

lemma contMDiffOn_finsum_section {ι : Type*} {s : Finset ι} {t : ι → (x : M) → V x}
    (hs : ∀ i, ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t i x)) u) :
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (∑ i ∈ s, (t i x))) u :=
  fun x₀ hx₀ ↦ contMDiffWithinAt_finsum_section fun i ↦ hs i x₀ hx₀

lemma contMDiff_finsum_section {ι : Type*} {s : Finset ι} {t : ι → (x : M) → V x}
    (hs : ∀ i, ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t i x))) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (∑ i ∈ s, (t i x))) :=
  fun x₀ ↦ contMDiffAt_finsum_section fun i ↦ (hs i) x₀

end operations

/-- Bundled `n` times continuously differentiable sections of a vector bundle.
Denoted as `Cₛ^n⟮I; F, V⟯` within the `Manifold` namespace. -/
structure ContMDiffSection where
  /-- the underlying function of this section -/
  protected toFun : ∀ x, V x
  /-- proof that this section is `C^n` -/
  protected contMDiff_toFun : ContMDiff I (I.prod 𝓘(𝕜, F)) n fun x ↦
    TotalSpace.mk' F x (toFun x)

@[inherit_doc] scoped[Manifold] notation "Cₛ^" n "⟮" I "; " F ", " V "⟯" => ContMDiffSection I F n V

namespace ContMDiffSection

variable {I} {n} {F} {V}

instance : DFunLike Cₛ^n⟮I; F, V⟯ M V where
  coe := ContMDiffSection.toFun
  coe_injective' := by rintro ⟨⟩ ⟨⟩ h; congr

variable {s t : Cₛ^n⟮I; F, V⟯}

@[simp]
theorem coeFn_mk (s : ∀ x, V x)
    (hs : ContMDiff I (I.prod 𝓘(𝕜, F)) n fun x => TotalSpace.mk x (s x)) :
    (mk s hs : ∀ x, V x) = s :=
  rfl

protected theorem contMDiff (s : Cₛ^n⟮I; F, V⟯) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n fun x => TotalSpace.mk' F x (s x : V x) :=
  s.contMDiff_toFun

theorem coe_inj ⦃s t : Cₛ^n⟮I; F, V⟯⦄ (h : (s : ∀ x, V x) = t) : s = t :=
  DFunLike.ext' h

theorem coe_injective : Injective ((↑) : Cₛ^n⟮I; F, V⟯ → ∀ x, V x) :=
  coe_inj

@[ext]
theorem ext (h : ∀ x, s x = t x) : s = t := DFunLike.ext _ _ h

section
variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

instance instAdd : Add Cₛ^n⟮I; F, V⟯ :=
  ⟨fun s t ↦ ⟨s + t, contMDiff_add_section s.contMDiff t.contMDiff⟩⟩

@[simp]
theorem coe_add (s t : Cₛ^n⟮I; F, V⟯) : ⇑(s + t) = ⇑s + t :=
  rfl

instance instSub : Sub Cₛ^n⟮I; F, V⟯ :=
  ⟨fun s t ↦ ⟨s - t, contMDiff_sub_section s.contMDiff t.contMDiff⟩⟩

@[simp]
theorem coe_sub (s t : Cₛ^n⟮I; F, V⟯) : ⇑(s - t) = s - t :=
  rfl

instance instZero : Zero Cₛ^n⟮I; F, V⟯ :=
  ⟨⟨fun _ => 0, (contMDiff_zeroSection 𝕜 V).of_le le_top⟩⟩

instance inhabited : Inhabited Cₛ^n⟮I; F, V⟯ :=
  ⟨0⟩

@[simp]
theorem coe_zero : ⇑(0 : Cₛ^n⟮I; F, V⟯) = 0 :=
  rfl

instance instNeg : Neg Cₛ^n⟮I; F, V⟯ :=
  ⟨fun s ↦ ⟨-s, contMDiff_neg_section s.contMDiff⟩⟩

@[simp]
theorem coe_neg (s : Cₛ^n⟮I; F, V⟯) : ⇑(-s : Cₛ^n⟮I; F, V⟯) = -s :=
  rfl

instance instNSMul : SMul ℕ Cₛ^n⟮I; F, V⟯ :=
  ⟨nsmulRec⟩

@[simp]
theorem coe_nsmul (s : Cₛ^n⟮I; F, V⟯) (k : ℕ) : ⇑(k • s : Cₛ^n⟮I; F, V⟯) = k • ⇑s := by
  induction k with
  | zero => simp_rw [zero_smul]; rfl
  | succ k ih => simp_rw [succ_nsmul, ← ih]; rfl

instance instZSMul : SMul ℤ Cₛ^n⟮I; F, V⟯ :=
  ⟨zsmulRec⟩

@[simp]
theorem coe_zsmul (s : Cₛ^n⟮I; F, V⟯) (z : ℤ) : ⇑(z • s : Cₛ^n⟮I; F, V⟯) = z • ⇑s := by
  rcases z with n | n
  · refine (coe_nsmul s n).trans ?_
    simp only [Int.ofNat_eq_coe, natCast_zsmul]
  · refine (congr_arg Neg.neg (coe_nsmul s (n + 1))).trans ?_
    simp only [negSucc_zsmul]

instance instAddCommGroup : AddCommGroup Cₛ^n⟮I; F, V⟯ :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

instance instSMul : SMul 𝕜 Cₛ^n⟮I; F, V⟯ :=
  ⟨fun c s ↦ ⟨c • ⇑s, contMDiff_smul_const_section s.contMDiff⟩⟩

@[simp]
theorem coe_smul (r : 𝕜) (s : Cₛ^n⟮I; F, V⟯) : ⇑(r • s : Cₛ^n⟮I; F, V⟯) = r • ⇑s :=
  rfl

variable (I F V n) in
/-- The additive morphism from `C^n` sections to dependent maps. -/
def coeAddHom : Cₛ^n⟮I; F, V⟯ →+ ∀ x, V x where
  toFun := (↑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
theorem coeAddHom_apply (s : Cₛ^n⟮I; F, V⟯) : coeAddHom I F n V s = s := rfl

instance instModule : Module 𝕜 Cₛ^n⟮I; F, V⟯ :=
  coe_injective.module 𝕜 (coeAddHom I F n V) coe_smul

end

protected theorem mdifferentiable' (s : Cₛ^n⟮I; F, V⟯) (hn : 1 ≤ n) :
    MDifferentiable I (I.prod 𝓘(𝕜, F)) fun x => TotalSpace.mk' F x (s x : V x) :=
  s.contMDiff.mdifferentiable hn

protected theorem mdifferentiable (s : Cₛ^∞⟮I; F, V⟯) :
    MDifferentiable I (I.prod 𝓘(𝕜, F)) fun x => TotalSpace.mk' F x (s x : V x) :=
  s.contMDiff.mdifferentiable (mod_cast le_top)

protected theorem mdifferentiableAt (s : Cₛ^∞⟮I; F, V⟯) {x} :
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x => TotalSpace.mk' F x (s x : V x)) x :=
  s.mdifferentiable x

end ContMDiffSection
