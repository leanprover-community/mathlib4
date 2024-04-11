/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Analysis.Filter
import Mathlib.Topology.Bases
import Mathlib.Topology.LocallyFinite

#align_import data.analysis.topology from "leanprover-community/mathlib"@"55d771df074d0dd020139ee1cd4b95521422df9f"

/-!
# Computational realization of topological spaces (experimental)

This file provides infrastructure to compute with topological spaces.

## Main declarations

* `Ctop`: Realization of a topology basis.
* `Ctop.Realizer`: Realization of a topological space. `Ctop` that generates the given topology.
* `LocallyFinite.Realizer`: Realization of the local finiteness of an indexed family of sets.
* `Compact.Realizer`: Realization of the compactness of a set.
-/


open Set

open Filter hiding Realizer

open Topology

/-- A `Ctop α σ` is a realization of a topology (basis) on `α`,
  represented by a type `σ` together with operations for the top element and
  the intersection operation. -/
structure Ctop (α σ : Type*) where
  f : σ → Set α
  top : α → σ
  top_mem : ∀ x : α, x ∈ f (top x)
  inter : ∀ (a b) (x : α), x ∈ f a ∩ f b → σ
  inter_mem : ∀ a b x h, x ∈ f (inter a b x h)
  inter_sub : ∀ a b x h, f (inter a b x h) ⊆ f a ∩ f b
#align ctop Ctop

variable {α : Type*} {β : Type*} {σ : Type*} {τ : Type*}

instance : Inhabited (Ctop α (Set α)) :=
  ⟨{  f := id
      top := singleton
      top_mem := mem_singleton
      inter := fun s t _ _ ↦ s ∩ t
      inter_mem := fun _s _t _a ↦ id
      inter_sub := fun _s _t _a _ha ↦ Subset.rfl }⟩

namespace Ctop

section

variable (F : Ctop α σ)

instance : CoeFun (Ctop α σ) fun _ ↦ σ → Set α :=
  ⟨Ctop.f⟩

-- @[simp] -- Porting note (#10685): dsimp can prove this
theorem coe_mk (f T h₁ I h₂ h₃ a) : (@Ctop.mk α σ f T h₁ I h₂ h₃) a = f a := rfl
#align ctop.coe_mk Ctop.coe_mk

/-- Map a Ctop to an equivalent representation type. -/
def ofEquiv (E : σ ≃ τ) : Ctop α σ → Ctop α τ
  | ⟨f, T, h₁, I, h₂, h₃⟩ =>
    { f := fun a ↦ f (E.symm a)
      top := fun x ↦ E (T x)
      top_mem := fun x ↦ by simpa using h₁ x
      inter := fun a b x h ↦ E (I (E.symm a) (E.symm b) x h)
      inter_mem := fun a b x h ↦ by simpa using h₂ (E.symm a) (E.symm b) x h
      inter_sub := fun a b x h ↦ by simpa using h₃ (E.symm a) (E.symm b) x h }
#align ctop.of_equiv Ctop.ofEquiv

@[simp]
theorem ofEquiv_val (E : σ ≃ τ) (F : Ctop α σ) (a : τ) : F.ofEquiv E a = F (E.symm a) := by
  cases F; rfl
#align ctop.of_equiv_val Ctop.ofEquiv_val

end

/-- Every `Ctop` is a topological space. -/
def toTopsp (F : Ctop α σ) : TopologicalSpace α := TopologicalSpace.generateFrom (Set.range F.f)
#align ctop.to_topsp Ctop.toTopsp

theorem toTopsp_isTopologicalBasis (F : Ctop α σ) :
    @TopologicalSpace.IsTopologicalBasis _ F.toTopsp (Set.range F.f) :=
  letI := F.toTopsp
  ⟨fun _u ⟨a, e₁⟩ _v ⟨b, e₂⟩ ↦
    e₁ ▸ e₂ ▸ fun x h ↦ ⟨_, ⟨_, rfl⟩, F.inter_mem a b x h, F.inter_sub a b x h⟩,
    eq_univ_iff_forall.2 fun x ↦ ⟨_, ⟨_, rfl⟩, F.top_mem x⟩, rfl⟩
#align ctop.to_topsp_is_topological_basis Ctop.toTopsp_isTopologicalBasis

@[simp]
theorem mem_nhds_toTopsp (F : Ctop α σ) {s : Set α} {a : α} :
    s ∈ @nhds _ F.toTopsp a ↔ ∃ b, a ∈ F b ∧ F b ⊆ s :=
  (@TopologicalSpace.IsTopologicalBasis.mem_nhds_iff _ F.toTopsp _ _ _
        F.toTopsp_isTopologicalBasis).trans <|
    ⟨fun ⟨_, ⟨x, rfl⟩, h⟩ ↦ ⟨x, h⟩, fun ⟨x, h⟩ ↦ ⟨_, ⟨x, rfl⟩, h⟩⟩
#align ctop.mem_nhds_to_topsp Ctop.mem_nhds_toTopsp

end Ctop

/-- A `Ctop` realizer for the topological space `T` is a `Ctop`
  which generates `T`. -/
structure Ctop.Realizer (α) [T : TopologicalSpace α] where
  σ : Type*
  F : Ctop α σ
  eq : F.toTopsp = T
#align ctop.realizer Ctop.Realizer

open Ctop

/-- A `Ctop` realizes the topological space it generates. -/
protected def Ctop.toRealizer (F : Ctop α σ) : @Ctop.Realizer _ F.toTopsp :=
  @Ctop.Realizer.mk _ F.toTopsp σ F rfl
#align ctop.to_realizer Ctop.toRealizer

instance (F : Ctop α σ) : Inhabited (@Ctop.Realizer _ F.toTopsp) :=
  ⟨F.toRealizer⟩

namespace Ctop.Realizer

protected theorem is_basis [T : TopologicalSpace α] (F : Realizer α) :
    TopologicalSpace.IsTopologicalBasis (Set.range F.F.f) := by
  have := toTopsp_isTopologicalBasis F.F; rwa [F.eq] at this
#align ctop.realizer.is_basis Ctop.Realizer.is_basis

protected theorem mem_nhds [T : TopologicalSpace α] (F : Realizer α) {s : Set α} {a : α} :
    s ∈ 𝓝 a ↔ ∃ b, a ∈ F.F b ∧ F.F b ⊆ s := by
  have := @mem_nhds_toTopsp _ _ F.F s a; rwa [F.eq] at this
#align ctop.realizer.mem_nhds Ctop.Realizer.mem_nhds

theorem isOpen_iff [TopologicalSpace α] (F : Realizer α) {s : Set α} :
    IsOpen s ↔ ∀ a ∈ s, ∃ b, a ∈ F.F b ∧ F.F b ⊆ s :=
  isOpen_iff_mem_nhds.trans <| forall₂_congr fun _a _h ↦ F.mem_nhds
#align ctop.realizer.is_open_iff Ctop.Realizer.isOpen_iff

theorem isClosed_iff [TopologicalSpace α] (F : Realizer α) {s : Set α} :
    IsClosed s ↔ ∀ a, (∀ b, a ∈ F.F b → ∃ z, z ∈ F.F b ∩ s) → a ∈ s :=
  isOpen_compl_iff.symm.trans <|
    F.isOpen_iff.trans <|
      forall_congr' fun a ↦
        show (a ∉ s → ∃ b : F.σ, a ∈ F.F b ∧ ∀ z ∈ F.F b, z ∉ s) ↔ _ by
          haveI := Classical.propDecidable; rw [not_imp_comm]
          simp [not_exists, not_and, not_forall, and_comm]
#align ctop.realizer.is_closed_iff Ctop.Realizer.isClosed_iff

theorem mem_interior_iff [TopologicalSpace α] (F : Realizer α) {s : Set α} {a : α} :
    a ∈ interior s ↔ ∃ b, a ∈ F.F b ∧ F.F b ⊆ s :=
  mem_interior_iff_mem_nhds.trans F.mem_nhds
#align ctop.realizer.mem_interior_iff Ctop.Realizer.mem_interior_iff

protected theorem isOpen [TopologicalSpace α] (F : Realizer α) (s : F.σ) : IsOpen (F.F s) :=
  isOpen_iff_nhds.2 fun a m ↦ by simpa using F.mem_nhds.2 ⟨s, m, Subset.refl _⟩
#align ctop.realizer.is_open Ctop.Realizer.isOpen

theorem ext' [T : TopologicalSpace α] {σ : Type*} {F : Ctop α σ}
    (H : ∀ a s, s ∈ 𝓝 a ↔ ∃ b, a ∈ F b ∧ F b ⊆ s) : F.toTopsp = T := by
  refine TopologicalSpace.ext_nhds fun x ↦ ?_
  ext s
  rw [mem_nhds_toTopsp, H]
#align ctop.realizer.ext' Ctop.Realizer.ext'

theorem ext [T : TopologicalSpace α] {σ : Type*} {F : Ctop α σ} (H₁ : ∀ a, IsOpen (F a))
    (H₂ : ∀ a s, s ∈ 𝓝 a → ∃ b, a ∈ F b ∧ F b ⊆ s) : F.toTopsp = T :=
  ext' fun a s ↦ ⟨H₂ a s, fun ⟨_b, h₁, h₂⟩ ↦ mem_nhds_iff.2 ⟨_, h₂, H₁ _, h₁⟩⟩
#align ctop.realizer.ext Ctop.Realizer.ext

variable [TopologicalSpace α]

-- Porting note: add non-computable : because
-- > ... it depends on `Inter.inter`, and it does not have executable code.
/-- The topological space realizer made of the open sets. -/
protected noncomputable def id : Realizer α :=
  ⟨{ x : Set α // IsOpen x },
    { f := Subtype.val
      top := fun _ ↦ ⟨univ, isOpen_univ⟩
      top_mem := mem_univ
      inter := fun ⟨_x, h₁⟩ ⟨_y, h₂⟩ _a _h₃ ↦ ⟨_, h₁.inter h₂⟩
      inter_mem := fun ⟨_x, _h₁⟩ ⟨_y, _h₂⟩ _a ↦ id
      inter_sub := fun ⟨_x, _h₁⟩ ⟨_y, _h₂⟩ _a _h₃ ↦ Subset.refl _ },
    ext Subtype.property fun _x _s h ↦
      let ⟨t, h, o, m⟩ := mem_nhds_iff.1 h
      ⟨⟨t, o⟩, m, h⟩⟩
#align ctop.realizer.id Ctop.Realizer.id

/-- Replace the representation type of a `Ctop` realizer. -/
def ofEquiv (F : Realizer α) (E : F.σ ≃ τ) : Realizer α :=
  ⟨τ, F.F.ofEquiv E,
    ext' fun a s ↦
      F.mem_nhds.trans <|
        ⟨fun ⟨s, h⟩ ↦ ⟨E s, by simpa using h⟩, fun ⟨t, h⟩ ↦ ⟨E.symm t, by simpa using h⟩⟩⟩
#align ctop.realizer.of_equiv Ctop.Realizer.ofEquiv

@[simp]
theorem ofEquiv_σ (F : Realizer α) (E : F.σ ≃ τ) : (F.ofEquiv E).σ = τ := rfl
#align ctop.realizer.of_equiv_σ Ctop.Realizer.ofEquiv_σ

@[simp]
theorem ofEquiv_F (F : Realizer α) (E : F.σ ≃ τ) (s : τ) : (F.ofEquiv E).F s = F.F (E.symm s) := by
  delta ofEquiv; simp
set_option linter.uppercaseLean3 false in
#align ctop.realizer.of_equiv_F Ctop.Realizer.ofEquiv_F

/-- A realizer of the neighborhood of a point. -/
protected def nhds (F : Realizer α) (a : α) : (𝓝 a).Realizer :=
  ⟨{ s : F.σ // a ∈ F.F s },
    { f := fun s ↦ F.F s.1
      pt := ⟨_, F.F.top_mem a⟩
      inf := fun ⟨x, h₁⟩ ⟨y, h₂⟩ ↦ ⟨_, F.F.inter_mem x y a ⟨h₁, h₂⟩⟩
      inf_le_left := fun ⟨x, h₁⟩ ⟨y, h₂⟩ _z h ↦ (F.F.inter_sub x y a ⟨h₁, h₂⟩ h).1
      inf_le_right := fun ⟨x, h₁⟩ ⟨y, h₂⟩ _z h ↦ (F.F.inter_sub x y a ⟨h₁, h₂⟩ h).2 },
    filter_eq <|
      Set.ext fun _x ↦
        ⟨fun ⟨⟨_s, as⟩, h⟩ ↦ mem_nhds_iff.2 ⟨_, h, F.isOpen _, as⟩, fun h ↦
          let ⟨s, h, as⟩ := F.mem_nhds.1 h
          ⟨⟨s, h⟩, as⟩⟩⟩
#align ctop.realizer.nhds Ctop.Realizer.nhds

@[simp]
theorem nhds_σ (F : Realizer α) (a : α) : (F.nhds a).σ = { s : F.σ // a ∈ F.F s } := rfl
#align ctop.realizer.nhds_σ Ctop.Realizer.nhds_σ

@[simp]
theorem nhds_F (F : Realizer α) (a : α) (s) : (F.nhds a).F s = F.F s.1 := rfl
set_option linter.uppercaseLean3 false in
#align ctop.realizer.nhds_F Ctop.Realizer.nhds_F

theorem tendsto_nhds_iff {m : β → α} {f : Filter β} (F : f.Realizer) (R : Realizer α) {a : α} :
    Tendsto m f (𝓝 a) ↔ ∀ t, a ∈ R.F t → ∃ s, ∀ x ∈ F.F s, m x ∈ R.F t :=
  (F.tendsto_iff _ (R.nhds a)).trans Subtype.forall
#align ctop.realizer.tendsto_nhds_iff Ctop.Realizer.tendsto_nhds_iff

end Ctop.Realizer

/-- A `LocallyFinite.Realizer F f` is a realization that `f` is locally finite, namely it is a
choice of open sets from the basis of `F` such that they intersect only finitely many of the values
of `f`.  -/
structure LocallyFinite.Realizer [TopologicalSpace α] (F : Ctop.Realizer α) (f : β → Set α) where
  bas : ∀ a, { s // a ∈ F.F s }
  sets : ∀ x : α, Fintype { i | (f i ∩ F.F (bas x)).Nonempty }
#align locally_finite.realizer LocallyFinite.Realizer

theorem LocallyFinite.Realizer.to_locallyFinite [TopologicalSpace α] {F : Ctop.Realizer α}
    {f : β → Set α} (R : LocallyFinite.Realizer F f) : LocallyFinite f := fun a ↦
  ⟨_, F.mem_nhds.2 ⟨(R.bas a).1, (R.bas a).2, Subset.rfl⟩, have := R.sets a; Set.toFinite _⟩
#align locally_finite.realizer.to_locally_finite LocallyFinite.Realizer.to_locallyFinite

theorem locallyFinite_iff_exists_realizer [TopologicalSpace α] (F : Ctop.Realizer α)
    {f : β → Set α} : LocallyFinite f ↔ Nonempty (LocallyFinite.Realizer F f) :=
  ⟨fun h ↦
    let ⟨g, h₁⟩ := Classical.axiom_of_choice h
    let ⟨g₂, h₂⟩ :=
      Classical.axiom_of_choice fun x ↦
        show ∃ b : F.σ, x ∈ F.F b ∧ F.F b ⊆ g x from
          let ⟨h, _h'⟩ := h₁ x
          F.mem_nhds.1 h
    ⟨⟨fun x ↦ ⟨g₂ x, (h₂ x).1⟩, fun x ↦
        Finite.fintype <|
          let ⟨_h, h'⟩ := h₁ x
          h'.subset fun _i hi ↦ hi.mono (inter_subset_inter_right _ (h₂ x).2)⟩⟩,
    fun ⟨R⟩ ↦ R.to_locallyFinite⟩
#align locally_finite_iff_exists_realizer locallyFinite_iff_exists_realizer

instance [TopologicalSpace α] [Finite β] (F : Ctop.Realizer α) (f : β → Set α) :
    Nonempty (LocallyFinite.Realizer F f) :=
  (locallyFinite_iff_exists_realizer _).1 <| locallyFinite_of_finite _

/-- A `Compact.Realizer s` is a realization that `s` is compact, namely it is a
choice of finite open covers for each set family covering `s`.  -/
def Compact.Realizer [TopologicalSpace α] (s : Set α) :=
  ∀ {f : Filter α} (F : f.Realizer) (x : F.σ), f ≠ ⊥ → F.F x ⊆ s → { a // a ∈ s ∧ 𝓝 a ⊓ f ≠ ⊥ }
#align compact.realizer Compact.Realizer

instance [TopologicalSpace α] : Inhabited (Compact.Realizer (∅ : Set α)) :=
  ⟨fun {f} F x h hF ↦ by
    suffices f = ⊥ from absurd this h
    rw [← F.eq, eq_bot_iff]
    exact fun s _ ↦ ⟨x, hF.trans s.empty_subset⟩⟩
