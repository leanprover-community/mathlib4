/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.CategoryTheory.PUnit
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.PUnit

/-!
# Simply connected spaces
This file defines simply connected spaces.
A topological space is simply connected if its fundamental groupoid is equivalent to `Unit`.

We also define the corresponding predicate for sets.

## Main theorems
  - `simply_connected_iff_unique_homotopic` - A space is simply connected if and only if it is
    nonempty and there is a unique path up to homotopy between any two points

  - `SimplyConnectedSpace.ofContractible` - A contractible space is simply connected
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A simply connected space is one whose fundamental groupoid is equivalent to `Discrete Unit` -/
@[mk_iff]
class SimplyConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  equiv_unit : Nonempty (FundamentalGroupoid X ≌ Discrete Unit)

@[deprecated (since := "2026-01-08")]
alias simply_connected_def := simplyConnectedSpace_iff

theorem simply_connected_iff_unique_homotopic (X : Type*) [TopologicalSpace X] :
    SimplyConnectedSpace X ↔
      Nonempty X ∧ ∀ x y : X, Nonempty (Unique (Path.Homotopic.Quotient x y)) := by
  simp only [simplyConnectedSpace_iff, equiv_punit_iff_unique,
    FundamentalGroupoid.nonempty_iff X, and_congr_right_iff, Nonempty.forall]
  intros
  exact ⟨fun h _ _ => h _ _, fun h _ _ => h _ _⟩

theorem ContinuousMap.HomotopyEquiv.simplyConnectedSpace [hY : SimplyConnectedSpace Y]
    (e : X ≃ₕ Y) : SimplyConnectedSpace X :=
  ⟨hY.1.map (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).trans⟩

theorem ContinuousMap.HomotopyEquiv.simplyConnectedSpace_iff (e : X ≃ₕ Y) :
    SimplyConnectedSpace X ↔ SimplyConnectedSpace Y :=
  ⟨fun _ ↦ e.symm.simplyConnectedSpace, fun _ ↦ e.simplyConnectedSpace⟩

namespace SimplyConnectedSpace

variable {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]

instance (x y : X) : Subsingleton (Path.Homotopic.Quotient x y) :=
  @Unique.instSubsingleton _ (Nonempty.some (by
    rw [simply_connected_iff_unique_homotopic] at *; tauto))

instance (priority := 100) : PathConnectedSpace X :=
  let unique_homotopic := (simply_connected_iff_unique_homotopic X).mp inferInstance
  { nonempty := unique_homotopic.1
    joined := fun x y => ⟨(unique_homotopic.2 x y).some.default.out⟩ }

/-- In a simply connected space, any two paths are homotopic -/
theorem paths_homotopic {x y : X} (p₁ p₂ : Path x y) : Path.Homotopic p₁ p₂ :=
  Quotient.eq.mp (@Subsingleton.elim (Path.Homotopic.Quotient x y) _ _ _)

instance (priority := 100) ofContractible (Y : Type*) [TopologicalSpace Y] [ContractibleSpace Y] :
    SimplyConnectedSpace Y :=
  haveI : SimplyConnectedSpace Unit := ⟨⟨FundamentalGroupoid.punitEquivDiscretePUnit⟩⟩
  (ContractibleSpace.hequiv Y Unit).some.simplyConnectedSpace

end SimplyConnectedSpace

/-- A space is simply connected iff it is path connected, and there is at most one path
  up to homotopy between any two points. -/
theorem simply_connected_iff_paths_homotopic :
    SimplyConnectedSpace Y ↔
      PathConnectedSpace Y ∧ ∀ x y : Y, Subsingleton (Path.Homotopic.Quotient x y) :=
  ⟨by intro; constructor <;> infer_instance, fun h => by
    cases h; rw [simply_connected_iff_unique_homotopic]
    exact ⟨inferInstance, fun x y => ⟨uniqueOfSubsingleton ⟦PathConnectedSpace.somePath x y⟧⟩⟩⟩

/-- Another version of `simply_connected_iff_paths_homotopic` -/
theorem simply_connected_iff_paths_homotopic' :
    SimplyConnectedSpace Y ↔
      PathConnectedSpace Y ∧ ∀ {x y : Y} (p₁ p₂ : Path x y), Path.Homotopic p₁ p₂ := by
  convert simply_connected_iff_paths_homotopic (Y := Y)
  simp [Path.Homotopic.Quotient, Setoid.eq_top_iff]; rfl

open Path.Homotopic.Quotient in
/-- A space is simply connected if and only if it is path-connected and every loop
    at any basepoint is null-homotopic (i.e., homotopic to the constant loop). -/
theorem simply_connected_iff_loops_nullhomotopic :
    SimplyConnectedSpace Y ↔
      PathConnectedSpace Y ∧ ∀ (x : Y) (γ : Path x x), Path.Homotopic γ (Path.refl x) := by
  rw [simply_connected_iff_paths_homotopic']
  constructor
  · -- Forward: all paths homotopic implies all loops null-homotopic
    intro ⟨hpc, hall⟩
    exact ⟨hpc, fun x γ => hall γ (Path.refl x)⟩
  · -- Backward: all loops null-homotopic implies all paths homotopic
    intro ⟨hpc, hloops⟩
    refine ⟨hpc, fun {x y} p₁ p₂ => ?_⟩
    -- Work in the quotient where structural steps can be done by simp
    rw [← eq]
    replace hloops : ∀ (x : Y) (γ : Path x x),
        (⟦γ⟧ : Path.Homotopic.Quotient x x) = ⟦Path.refl x⟧ :=
      fun x γ => Quotient.sound (hloops x γ)
    have h : trans ⟦p₁⟧ (symm ⟦p₂⟧) = refl x := by
      simpa using hloops x (p₁.trans p₂.symm)
    calc ⟦p₁⟧
      _ = trans (trans ⟦p₁⟧ (symm ⟦p₂⟧)) ⟦p₂⟧ := by simp
      _ = ⟦p₂⟧ := by grind

/-!
### Simply connected sets
-/

/-- We say that a set is simply connected if it's a simply connected topological space
in the induced topology. -/
def IsSimplyConnected (s : Set X) : Prop := SimplyConnectedSpace s

theorem IsSimplyConnected.simplyConnectedSpace {s : Set X} (hs : IsSimplyConnected s) :
    SimplyConnectedSpace s := hs

theorem IsSimplyConnected.isPathConnected {s : Set X} (hs : IsSimplyConnected s) :
    IsPathConnected s :=
  have := hs.simplyConnectedSpace
  isPathConnected_iff_pathConnectedSpace.mpr inferInstance

theorem IsSimplyConnected.nonempty {s : Set X} (hs : IsSimplyConnected s) : s.Nonempty :=
  hs.isPathConnected.nonempty

theorem Topology.IsEmbedding.isSimplyConnected_image {f : X → Y} (hf : Topology.IsEmbedding f)
    {s : Set X} :
    IsSimplyConnected (f '' s) ↔ IsSimplyConnected s :=
  hf.homeomorphImage s |>.toHomotopyEquiv |>.simplyConnectedSpace_iff |>.symm

@[simp]
theorem Homeomorph.isSimplyConnected_image (f : X ≃ₜ Y) {s : Set X} :
    IsSimplyConnected (f '' s) ↔ IsSimplyConnected s :=
  f.isEmbedding.isSimplyConnected_image

@[simp]
theorem Homeomorph.isSimplyConnected_preimage (f : X ≃ₜ Y) {s : Set Y} :
    IsSimplyConnected (f ⁻¹' s) ↔ IsSimplyConnected s := by
  rw [← image_symm, isSimplyConnected_image]

/-- A set is simply connected iff it's path connected
and any loop is homotopic to the constant path within `s`. -/
theorem isSimplyConnected_iff_exists_homotopy_refl_forall_mem {s : Set X} :
    IsSimplyConnected s ↔ IsPathConnected s ∧ ∀ x, ∀ p : Path x x, (∀ t, p t ∈ s) →
      ∃ F : p.Homotopy (.refl x), ∀ t, F t ∈ s := by
  rw [IsSimplyConnected, simply_connected_iff_loops_nullhomotopic,
    ← isPathConnected_iff_pathConnectedSpace]
  refine .and .rfl ⟨fun h x p hp ↦ ?_, fun h x p ↦ ?_⟩
  · lift x to s using by simpa using hp 0
    rcases h x {
      toFun := fun t ↦ ⟨p t, hp t⟩
      source' := by simp
      target' := by simp
    } with ⟨F⟩
    exact ⟨F.map (.restrict s (.id _)), fun t ↦ (F t).2⟩
  · rcases h x (p.map continuous_subtype_val) (fun t ↦ (p t).2) with ⟨F, hF⟩
    exact ⟨{
      toFun t := ⟨F t, hF t⟩
      map_zero_left := by simp
      map_one_left := by simp
      prop' := by simp
    }⟩

open scoped Pointwise

@[to_additive (attr := simp)]
theorem isSimplyConnected_smul_set_iff {G : Type*} [Group G]
    [MulAction G X] [ContinuousConstSMul G X] {c : G} {s : Set X} :
    IsSimplyConnected (c • s) ↔ IsSimplyConnected s :=
  Homeomorph.smul c |>.isSimplyConnected_image

@[simp]
theorem isSimplyConnected_smul_set₀_iff {G : Type*} [GroupWithZero G] [MulAction G X]
    [ContinuousConstSMul G X] {c : G} {s : Set X} (hc : c ≠ 0) :
    IsSimplyConnected (c • s) ↔ IsSimplyConnected s :=
  isSimplyConnected_smul_set_iff (c := Units.mk0 c hc)
