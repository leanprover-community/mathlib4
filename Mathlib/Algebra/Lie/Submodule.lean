/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.LinearAlgebra.Finsupp.Span

/-!
# Lie submodules of a Lie algebra

In this file we define Lie submodules, we construct the lattice structure on Lie submodules and we
use it to define various important operations, notably the Lie span of a subset of a Lie module.

## Main definitions

  * `LieSubmodule`
  * `LieSubmodule.wellFounded_of_noetherian`
  * `LieSubmodule.lieSpan`
  * `LieSubmodule.map`
  * `LieSubmodule.comap`

## Tags

lie algebra, lie submodule, lie ideal, lattice structure
-/


universe u v w w₁ w₂

section LieSubmodule

variable (R : Type u) (L : Type v) (M : Type w)
variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]
variable [LieRingModule L M]

/-- A Lie submodule of a Lie module is a submodule that is closed under the Lie bracket.
This is a sufficient condition for the subset itself to form a Lie module. -/
structure LieSubmodule extends Submodule R M where
  lie_mem : ∀ {x : L} {m : M}, m ∈ carrier → ⁅x, m⁆ ∈ carrier

attribute [nolint docBlame] LieSubmodule.toSubmodule
attribute [coe] LieSubmodule.toSubmodule

namespace LieSubmodule

variable {R L M}
variable (N N' : LieSubmodule R L M)

instance : SetLike (LieSubmodule R L M) M where
  coe s := s.carrier
  coe_injective' N O h := by cases N; cases O; congr; exact SetLike.coe_injective' h

instance : AddSubgroupClass (LieSubmodule R L M) M where
  add_mem {N} _ _ := N.add_mem'
  zero_mem N := N.zero_mem'
  neg_mem {N} x hx := show -x ∈ N.toSubmodule from neg_mem hx

instance instSMulMemClass : SMulMemClass (LieSubmodule R L M) R M where
  smul_mem {s} c _ h := s.smul_mem'  c h

/-- The zero module is a Lie submodule of any Lie module. -/
instance : Zero (LieSubmodule R L M) :=
  ⟨{ (0 : Submodule R M) with
      lie_mem := fun {x m} h ↦ by rw [(Submodule.mem_bot R).1 h]; apply lie_zero }⟩

instance : Inhabited (LieSubmodule R L M) :=
  ⟨0⟩

instance (priority := high) coeSort : CoeSort (LieSubmodule R L M) (Type w) where
  coe N := { x : M // x ∈ N }

instance (priority := mid) coeSubmodule : CoeOut (LieSubmodule R L M) (Submodule R M) :=
  ⟨toSubmodule⟩

instance : CanLift (Submodule R M) (LieSubmodule R L M) (·)
    (fun N ↦ ∀ {x : L} {m : M}, m ∈ N → ⁅x, m⁆ ∈ N) where
  prf N hN := ⟨⟨N, hN⟩, rfl⟩

@[norm_cast]
theorem coe_toSubmodule : ((N : Submodule R M) : Set M) = N :=
  rfl

theorem mem_carrier {x : M} : x ∈ N.carrier ↔ x ∈ (N : Set M) :=
  Iff.rfl

theorem mem_mk_iff (S : Set M) (h₁ h₂ h₃ h₄) {x : M} :
    x ∈ (⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩, h₄⟩ : LieSubmodule R L M) ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem mem_mk_iff' (p : Submodule R M) (h) {x : M} :
    x ∈ (⟨p, h⟩ : LieSubmodule R L M) ↔ x ∈ p :=
  Iff.rfl

@[simp]
theorem mem_toSubmodule {x : M} : x ∈ (N : Submodule R M) ↔ x ∈ N :=
  Iff.rfl

theorem mem_coe {x : M} : x ∈ (N : Set M) ↔ x ∈ N :=
  Iff.rfl

protected theorem zero_mem : (0 : M) ∈ N :=
  zero_mem N

@[simp]
theorem mk_eq_zero {x} (h : x ∈ N) : (⟨x, h⟩ : N) = 0 ↔ x = 0 :=
  Subtype.ext_iff

@[simp]
theorem coe_toSet_mk (S : Set M) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩, h₄⟩ : LieSubmodule R L M) : Set M) = S :=
  rfl

theorem toSubmodule_mk (p : Submodule R M) (h) :
    (({ p with lie_mem := h } : LieSubmodule R L M) : Submodule R M) = p := by cases p; rfl

theorem toSubmodule_injective :
    Function.Injective (toSubmodule : LieSubmodule R L M → Submodule R M) := fun x y h ↦ by
  cases x; cases y; congr

@[ext]
theorem ext (h : ∀ m, m ∈ N ↔ m ∈ N') : N = N' :=
  SetLike.ext h

@[simp]
theorem toSubmodule_inj : (N : Submodule R M) = (N' : Submodule R M) ↔ N = N' :=
  toSubmodule_injective.eq_iff

/-- Copy of a `LieSubmodule` with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (s : Set M) (hs : s = ↑N) : LieSubmodule R L M where
  carrier := s
  zero_mem' := by simp [hs]
  add_mem' x y := by rw [hs] at x y ⊢; exact N.add_mem' x y
  smul_mem' := by exact hs.symm ▸ N.smul_mem'
  lie_mem := by exact hs.symm ▸ N.lie_mem

@[simp, norm_cast]
theorem coe_copy (S : LieSubmodule R L M) (s : Set M) (hs : s = ↑S) : (S.copy s hs : Set M) = s :=
  rfl

theorem copy_eq (S : LieSubmodule R L M) (s : Set M) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

instance : LieRingModule L N where
  bracket (x : L) (m : N) := ⟨⁅x, m.val⁆, N.lie_mem m.property⟩
  add_lie := by intro x y m; apply SetCoe.ext; apply add_lie
  lie_add := by intro x m n; apply SetCoe.ext; apply lie_add
  leibniz_lie := by intro x y m; apply SetCoe.ext; apply leibniz_lie

@[simp, norm_cast]
theorem coe_zero : ((0 : N) : M) = (0 : M) :=
  rfl

@[simp, norm_cast]
theorem coe_add (m m' : N) : (↑(m + m') : M) = (m : M) + (m' : M) :=
  rfl

@[simp, norm_cast]
theorem coe_neg (m : N) : (↑(-m) : M) = -(m : M) :=
  rfl

@[simp, norm_cast]
theorem coe_sub (m m' : N) : (↑(m - m') : M) = (m : M) - (m' : M) :=
  rfl

@[simp, norm_cast]
theorem coe_smul (t : R) (m : N) : (↑(t • m) : M) = t • (m : M) :=
  rfl

@[simp, norm_cast]
theorem coe_bracket (x : L) (m : N) :
    (↑⁅x, m⁆ : M) = ⁅x, ↑m⁆ :=
  rfl

-- Copying instances from `Submodule` for correct discrimination keys
instance [IsNoetherian R M] (N : LieSubmodule R L M) : IsNoetherian R N :=
  inferInstanceAs <| IsNoetherian R N.toSubmodule

instance [IsArtinian R M] (N : LieSubmodule R L M) : IsArtinian R N :=
  inferInstanceAs <| IsArtinian R N.toSubmodule

instance [NoZeroSMulDivisors R M] : NoZeroSMulDivisors R N :=
  inferInstanceAs <| NoZeroSMulDivisors R N.toSubmodule

variable [LieAlgebra R L] [LieModule R L M]

instance instLieModule : LieModule R L N where
  lie_smul := by intro t x y; apply SetCoe.ext; apply lie_smul
  smul_lie := by intro t x y; apply SetCoe.ext; apply smul_lie

instance [Subsingleton M] : Unique (LieSubmodule R L M) :=
  ⟨⟨0⟩, fun _ ↦ (toSubmodule_inj _ _).mp (Subsingleton.elim _ _)⟩

end LieSubmodule

variable {R M}

theorem Submodule.exists_lieSubmodule_coe_eq_iff (p : Submodule R M) :
    (∃ N : LieSubmodule R L M, ↑N = p) ↔ ∀ (x : L) (m : M), m ∈ p → ⁅x, m⁆ ∈ p := by
  constructor
  · rintro ⟨N, rfl⟩ _ _; exact N.lie_mem
  · intro h; use { p with lie_mem := @h }

namespace LieSubalgebra

variable {L}
variable [LieAlgebra R L]
variable (K : LieSubalgebra R L)

/-- Given a Lie subalgebra `K ⊆ L`, if we view `L` as a `K`-module by restriction, it contains
a distinguished Lie submodule for the action of `K`, namely `K` itself. -/
def toLieSubmodule : LieSubmodule R K L :=
  { (K : Submodule R L) with lie_mem := fun {x _} hy ↦ K.lie_mem x.property hy }

@[simp]
theorem coe_toLieSubmodule : (K.toLieSubmodule : Submodule R L) = K := rfl

variable {K}

@[simp]
theorem mem_toLieSubmodule (x : L) : x ∈ K.toLieSubmodule ↔ x ∈ K :=
  Iff.rfl

end LieSubalgebra

end LieSubmodule

namespace LieSubmodule

variable {R : Type u} {L : Type v} {M : Type w}
variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]
variable [LieRingModule L M]
variable (N N' : LieSubmodule R L M)

section LatticeStructure

open Set

theorem coe_injective : Function.Injective ((↑) : LieSubmodule R L M → Set M) :=
  SetLike.coe_injective

@[simp, norm_cast]
theorem toSubmodule_le_toSubmodule : (N : Submodule R M) ≤ N' ↔ N ≤ N' :=
  Iff.rfl

instance : Bot (LieSubmodule R L M) :=
  ⟨0⟩

instance instUniqueBot : Unique (⊥ : LieSubmodule R L M) :=
  inferInstanceAs <| Unique (⊥ : Submodule R M)

@[simp]
theorem bot_coe : ((⊥ : LieSubmodule R L M) : Set M) = {0} :=
  rfl

@[simp]
theorem bot_toSubmodule : ((⊥ : LieSubmodule R L M) : Submodule R M) = ⊥ :=
  rfl

@[simp]
theorem toSubmodule_eq_bot : (N : Submodule R M) = ⊥ ↔ N = ⊥ := by
  rw [← toSubmodule_inj, bot_toSubmodule]

@[simp] theorem mk_eq_bot_iff {N : Submodule R M} {h} :
    (⟨N, h⟩ : LieSubmodule R L M) = ⊥ ↔ N = ⊥ := by
  rw [← toSubmodule_inj, bot_toSubmodule]

@[simp]
theorem mem_bot (x : M) : x ∈ (⊥ : LieSubmodule R L M) ↔ x = 0 :=
  mem_singleton_iff

instance : Top (LieSubmodule R L M) :=
  ⟨{ (⊤ : Submodule R M) with lie_mem := fun {x m} _ ↦ mem_univ ⁅x, m⁆ }⟩

@[simp]
theorem top_coe : ((⊤ : LieSubmodule R L M) : Set M) = univ :=
  rfl

@[simp]
theorem top_toSubmodule : ((⊤ : LieSubmodule R L M) : Submodule R M) = ⊤ :=
  rfl

@[simp]
theorem toSubmodule_eq_top : (N : Submodule R M) = ⊤ ↔ N = ⊤ := by
  rw [← toSubmodule_inj, top_toSubmodule]

@[simp] theorem mk_eq_top_iff {N : Submodule R M} {h} :
    (⟨N, h⟩ : LieSubmodule R L M) = ⊤ ↔ N = ⊤ := by
  rw [← toSubmodule_inj, top_toSubmodule]

@[simp]
theorem mem_top (x : M) : x ∈ (⊤ : LieSubmodule R L M) :=
  mem_univ x

instance : Min (LieSubmodule R L M) :=
  ⟨fun N N' ↦
    { (N ⊓ N' : Submodule R M) with
      lie_mem := fun h ↦ mem_inter (N.lie_mem h.1) (N'.lie_mem h.2) }⟩

instance : InfSet (LieSubmodule R L M) :=
  ⟨fun S ↦
    { toSubmodule := sInf {(s : Submodule R M) | s ∈ S}
      lie_mem := fun {x m} h ↦ by
        simp only [Submodule.mem_carrier, mem_iInter, Submodule.coe_sInf, mem_setOf_eq,
          forall_apply_eq_imp_iff₂, forall_exists_index, and_imp] at h ⊢
        intro N hN; apply N.lie_mem (h N hN) }⟩

@[simp]
theorem coe_inf : (↑(N ⊓ N') : Set M) = ↑N ∩ ↑N' :=
  rfl

@[deprecated (since := "2025-08-31")] alias inf_coe := coe_inf

@[norm_cast, simp]
theorem inf_toSubmodule :
    (↑(N ⊓ N') : Submodule R M) = (N : Submodule R M) ⊓ (N' : Submodule R M) :=
  rfl

@[simp]
theorem sInf_toSubmodule (S : Set (LieSubmodule R L M)) :
    (↑(sInf S) : Submodule R M) = sInf {(s : Submodule R M) | s ∈ S} :=
  rfl

theorem sInf_toSubmodule_eq_iInf (S : Set (LieSubmodule R L M)) :
    (↑(sInf S) : Submodule R M) = ⨅ N ∈ S, (N : Submodule R M) := by
  rw [sInf_toSubmodule, ← Set.image, sInf_image]

@[simp]
theorem iInf_toSubmodule {ι} (p : ι → LieSubmodule R L M) :
    (↑(⨅ i, p i) : Submodule R M) = ⨅ i, (p i : Submodule R M) := by
  rw [iInf, sInf_toSubmodule]; ext; simp

@[simp]
theorem coe_sInf (S : Set (LieSubmodule R L M)) : (↑(sInf S) : Set M) = ⋂ s ∈ S, (s : Set M) := by
  rw [← LieSubmodule.coe_toSubmodule, sInf_toSubmodule, Submodule.coe_sInf]
  ext m
  simp only [mem_iInter, mem_setOf_eq, forall_apply_eq_imp_iff₂, exists_imp,
    and_imp, SetLike.mem_coe, mem_toSubmodule]

@[deprecated (since := "2025-08-31")] alias sInf_coe := coe_sInf

@[simp]
theorem coe_iInf {ι} (p : ι → LieSubmodule R L M) : (↑(⨅ i, p i) : Set M) = ⋂ i, ↑(p i) := by
  rw [iInf, coe_sInf]; simp only [Set.mem_range, Set.iInter_exists, Set.iInter_iInter_eq']

@[deprecated (since := "2025-08-31")] alias iInf_coe := coe_iInf

@[simp]
theorem mem_iInf {ι} (p : ι → LieSubmodule R L M) {x} : (x ∈ ⨅ i, p i) ↔ ∀ i, x ∈ p i := by
  rw [← SetLike.mem_coe, coe_iInf, Set.mem_iInter]; rfl

instance : Max (LieSubmodule R L M) where
  max N N' :=
    { toSubmodule := (N : Submodule R M) ⊔ (N' : Submodule R M)
      lie_mem := by
        rintro x m (hm : m ∈ (N : Submodule R M) ⊔ (N' : Submodule R M))
        change ⁅x, m⁆ ∈ (N : Submodule R M) ⊔ (N' : Submodule R M)
        rw [Submodule.mem_sup] at hm ⊢
        obtain ⟨y, hy, z, hz, rfl⟩ := hm
        exact ⟨⁅x, y⁆, N.lie_mem hy, ⁅x, z⁆, N'.lie_mem hz, (lie_add _ _ _).symm⟩ }

instance : SupSet (LieSubmodule R L M) where
  sSup S :=
    { toSubmodule := sSup {(p : Submodule R M) | p ∈ S}
      lie_mem := by
        intro x m (hm : m ∈ sSup {(p : Submodule R M) | p ∈ S})
        change ⁅x, m⁆ ∈ sSup {(p : Submodule R M) | p ∈ S}
        obtain ⟨s, hs, hsm⟩ := Submodule.mem_sSup_iff_exists_finset.mp hm
        clear hm
        classical
        induction s using Finset.induction_on generalizing m with
        | empty =>
          replace hsm : m = 0 := by simpa using hsm
          simp [hsm]
        | insert q t hqt ih =>
          rw [Finset.iSup_insert] at hsm
          obtain ⟨m', hm', u, hu, rfl⟩ := Submodule.mem_sup.mp hsm
          rw [lie_add]
          refine add_mem ?_ (ih (Subset.trans (by simp) hs) hu)
          obtain ⟨p, hp, rfl⟩ : ∃ p ∈ S, ↑p = q := hs (Finset.mem_insert_self q t)
          suffices p ≤ sSup {(p : Submodule R M) | p ∈ S} by exact this (p.lie_mem hm')
          exact le_sSup ⟨p, hp, rfl⟩ }

@[norm_cast, simp]
theorem sup_toSubmodule :
    (↑(N ⊔ N') : Submodule R M) = (N : Submodule R M) ⊔ (N' : Submodule R M) := by
  rfl

@[simp]
theorem sSup_toSubmodule (S : Set (LieSubmodule R L M)) :
    (↑(sSup S) : Submodule R M) = sSup {(s : Submodule R M) | s ∈ S} :=
  rfl

theorem sSup_toSubmodule_eq_iSup (S : Set (LieSubmodule R L M)) :
    (↑(sSup S) : Submodule R M) = ⨆ N ∈ S, (N : Submodule R M) := by
  rw [sSup_toSubmodule, ← Set.image, sSup_image]

@[simp]
theorem iSup_toSubmodule {ι} (p : ι → LieSubmodule R L M) :
    (↑(⨆ i, p i) : Submodule R M) = ⨆ i, (p i : Submodule R M) := by
  rw [iSup, sSup_toSubmodule]; ext; simp [Submodule.mem_sSup, Submodule.mem_iSup]

/-- The set of Lie submodules of a Lie module form a complete lattice. -/
instance : CompleteLattice (LieSubmodule R L M) :=
  toSubmodule_injective.completeLattice toSubmodule .rfl .rfl sup_toSubmodule inf_toSubmodule
    sSup_toSubmodule_eq_iSup sInf_toSubmodule_eq_iInf rfl rfl

theorem mem_iSup_of_mem {ι} {b : M} {N : ι → LieSubmodule R L M} (i : ι) (h : b ∈ N i) :
    b ∈ ⨆ i, N i :=
  (le_iSup N i) h

@[elab_as_elim]
lemma iSup_induction {ι} (N : ι → LieSubmodule R L M) {motive : M → Prop} {x : M}
    (hx : x ∈ ⨆ i, N i) (mem : ∀ i, ∀ y ∈ N i, motive y) (zero : motive 0)
    (add : ∀ y z, motive y → motive z → motive (y + z)) : motive x := by
  rw [← LieSubmodule.mem_toSubmodule, LieSubmodule.iSup_toSubmodule] at hx
  exact Submodule.iSup_induction (motive := motive) (fun i ↦ (N i : Submodule R M)) hx mem zero add

@[elab_as_elim]
theorem iSup_induction' {ι} (N : ι → LieSubmodule R L M) {motive : (x : M) → (x ∈ ⨆ i, N i) → Prop}
    (mem : ∀ (i) (x) (hx : x ∈ N i), motive x (mem_iSup_of_mem i hx)) (zero : motive 0 (zero_mem _))
    (add : ∀ x y hx hy, motive x hx → motive y hy → motive (x + y) (add_mem ‹_› ‹_›)) {x : M}
    (hx : x ∈ ⨆ i, N i) : motive x hx := by
  refine Exists.elim ?_ fun (hx : x ∈ ⨆ i, N i) (hc : motive x hx) => hc
  refine iSup_induction N (motive := fun x : M ↦ ∃ (hx : x ∈ ⨆ i, N i), motive x hx) hx
    (fun i x hx => ?_) ?_ fun x y => ?_
  · exact ⟨_, mem _ _ hx⟩
  · exact ⟨_, zero⟩
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    exact ⟨_, add _ _ _ _ Cx Cy⟩

variable {N N'}

@[simp] lemma disjoint_toSubmodule :
    Disjoint (N : Submodule R M) (N' : Submodule R M) ↔ Disjoint N N' := by
  rw [disjoint_iff, disjoint_iff, ← toSubmodule_inj, inf_toSubmodule, bot_toSubmodule,
    ← disjoint_iff]

@[deprecated disjoint_toSubmodule (since := "2025-04-03")]
theorem disjoint_iff_toSubmodule :
    Disjoint N N' ↔ Disjoint (N : Submodule R M) (N' : Submodule R M) := disjoint_toSubmodule.symm

@[simp] lemma codisjoint_toSubmodule :
    Codisjoint (N : Submodule R M) (N' : Submodule R M) ↔ Codisjoint N N' := by
  rw [codisjoint_iff, codisjoint_iff, ← toSubmodule_inj, sup_toSubmodule,
    top_toSubmodule, ← codisjoint_iff]

@[deprecated codisjoint_toSubmodule (since := "2025-04-03")]
theorem codisjoint_iff_toSubmodule :
    Codisjoint N N' ↔ Codisjoint (N : Submodule R M) (N' : Submodule R M) :=
  codisjoint_toSubmodule.symm

@[simp] lemma isCompl_toSubmodule :
    IsCompl (N : Submodule R M) (N' : Submodule R M) ↔ IsCompl N N' := by
  simp [isCompl_iff]

@[deprecated isCompl_toSubmodule (since := "2025-04-03")]
theorem isCompl_iff_toSubmodule :
    IsCompl N N' ↔ IsCompl (N : Submodule R M) (N' : Submodule R M) := isCompl_toSubmodule.symm

@[simp] lemma iSupIndep_toSubmodule {ι : Type*} {N : ι → LieSubmodule R L M} :
    iSupIndep (fun i ↦ (N i : Submodule R M)) ↔ iSupIndep N := by
  simp [iSupIndep_def, ← disjoint_toSubmodule]

@[deprecated iSupIndep_toSubmodule (since := "2025-04-03")]
theorem iSupIndep_iff_toSubmodule {ι : Type*} {N : ι → LieSubmodule R L M} :
    iSupIndep N ↔ iSupIndep fun i ↦ (N i : Submodule R M) := iSupIndep_toSubmodule.symm

@[simp] lemma iSup_toSubmodule_eq_top {ι : Sort*} {N : ι → LieSubmodule R L M} :
    ⨆ i, (N i : Submodule R M) = ⊤ ↔ ⨆ i, N i = ⊤ := by
  rw [← iSup_toSubmodule, ← top_toSubmodule (L := L), toSubmodule_inj]

@[deprecated iSup_toSubmodule_eq_top (since := "2025-04-03")]
theorem iSup_eq_top_iff_toSubmodule {ι : Sort*} {N : ι → LieSubmodule R L M} :
    ⨆ i, N i = ⊤ ↔ ⨆ i, (N i : Submodule R M) = ⊤ := iSup_toSubmodule_eq_top.symm

instance : Add (LieSubmodule R L M) where add := max

instance : Zero (LieSubmodule R L M) where zero := ⊥

instance : AddCommMonoid (LieSubmodule R L M) where
  add_assoc := sup_assoc
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  nsmul := nsmulRec

variable (N N')

@[simp]
theorem add_eq_sup : N + N' = N ⊔ N' :=
  rfl

@[simp]
theorem mem_inf (x : M) : x ∈ N ⊓ N' ↔ x ∈ N ∧ x ∈ N' := by
  rw [← mem_toSubmodule, ← mem_toSubmodule, ← mem_toSubmodule, inf_toSubmodule,
    Submodule.mem_inf]

theorem mem_sup (x : M) : x ∈ N ⊔ N' ↔ ∃ y ∈ N, ∃ z ∈ N', y + z = x := by
  rw [← mem_toSubmodule, sup_toSubmodule, Submodule.mem_sup]; exact Iff.rfl

nonrec theorem eq_bot_iff : N = ⊥ ↔ ∀ m : M, m ∈ N → m = 0 := by rw [eq_bot_iff]; exact Iff.rfl

instance subsingleton_of_bot : Subsingleton (LieSubmodule R L (⊥ : LieSubmodule R L M)) := by
  apply subsingleton_of_bot_eq_top
  subsingleton

instance : IsModularLattice (LieSubmodule R L M) where
  sup_inf_le_assoc_of_le _ _ := by
    simp only [← toSubmodule_le_toSubmodule, sup_toSubmodule, inf_toSubmodule]
    exact IsModularLattice.sup_inf_le_assoc_of_le _

variable (R L M)

/-- The natural functor that forgets the action of `L` as an order embedding. -/
@[simps] def toSubmodule_orderEmbedding : LieSubmodule R L M ↪o Submodule R M :=
  { toFun := (↑)
    inj' := toSubmodule_injective
    map_rel_iff' := Iff.rfl }

instance wellFoundedGT_of_noetherian [IsNoetherian R M] : WellFoundedGT (LieSubmodule R L M) :=
  RelHomClass.isWellFounded (toSubmodule_orderEmbedding R L M).dual.ltEmbedding

theorem wellFoundedLT_of_isArtinian [IsArtinian R M] : WellFoundedLT (LieSubmodule R L M) :=
  RelHomClass.isWellFounded (toSubmodule_orderEmbedding R L M).ltEmbedding

instance [IsArtinian R M] : IsAtomic (LieSubmodule R L M) :=
  isAtomic_of_orderBot_wellFounded_lt <| (wellFoundedLT_of_isArtinian R L M).wf

@[simp]
theorem subsingleton_iff : Subsingleton (LieSubmodule R L M) ↔ Subsingleton M :=
  have h : Subsingleton (LieSubmodule R L M) ↔ Subsingleton (Submodule R M) := by
    rw [← subsingleton_iff_bot_eq_top, ← subsingleton_iff_bot_eq_top, ← toSubmodule_inj,
      top_toSubmodule, bot_toSubmodule]
  h.trans <| Submodule.subsingleton_iff R

@[simp]
theorem nontrivial_iff : Nontrivial (LieSubmodule R L M) ↔ Nontrivial M :=
  not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans <| subsingleton_iff R L M).trans
      not_nontrivial_iff_subsingleton.symm)

instance [Nontrivial M] : Nontrivial (LieSubmodule R L M) :=
  (nontrivial_iff R L M).mpr ‹_›

theorem nontrivial_iff_ne_bot {N : LieSubmodule R L M} : Nontrivial N ↔ N ≠ ⊥ := by
  constructor <;> contrapose!
  · rintro rfl
    by_contra! h; rcases h with
      ⟨⟨m₁, h₁ : m₁ ∈ (⊥ : LieSubmodule R L M)⟩, ⟨m₂, h₂ : m₂ ∈ (⊥ : LieSubmodule R L M)⟩, h₁₂⟩
    simp [(LieSubmodule.mem_bot _).mp h₁, (LieSubmodule.mem_bot _).mp h₂] at h₁₂
  · rw [LieSubmodule.eq_bot_iff]
    rintro ⟨h⟩ m hm
    simpa using h ⟨m, hm⟩ ⟨_, N.zero_mem⟩

variable {R L M}

section InclusionMaps

/-- The inclusion of a Lie submodule into its ambient space is a morphism of Lie modules. -/
def incl : N →ₗ⁅R,L⁆ M :=
  { Submodule.subtype (N : Submodule R M) with map_lie' := fun {_ _} ↦ rfl }

@[simp]
theorem incl_coe : (N.incl : N →ₗ[R] M) = (N : Submodule R M).subtype :=
  rfl

@[simp]
theorem incl_apply (m : N) : N.incl m = m :=
  rfl

theorem incl_eq_val : (N.incl : N → M) = Subtype.val :=
  rfl

theorem injective_incl : Function.Injective N.incl := Subtype.coe_injective

variable {N N'}
variable (h : N ≤ N')

/-- Given two nested Lie submodules `N ⊆ N'`,
the inclusion `N ↪ N'` is a morphism of Lie modules. -/
def inclusion : N →ₗ⁅R,L⁆ N' where
  __ := Submodule.inclusion (show N.toSubmodule ≤ N'.toSubmodule from h)
  map_lie' := rfl

@[simp]
theorem coe_inclusion (m : N) : (inclusion h m : M) = m :=
  rfl

theorem inclusion_apply (m : N) : inclusion h m = ⟨m.1, h m.2⟩ :=
  rfl

theorem inclusion_injective : Function.Injective (inclusion h) := fun x y ↦ by
  simp only [inclusion_apply, imp_self, Subtype.mk_eq_mk, SetLike.coe_eq_coe]

end InclusionMaps

section LieSpan

variable (R L) (s : Set M)

/-- The `lieSpan` of a set `s ⊆ M` is the smallest Lie submodule of `M` that contains `s`. -/
def lieSpan : LieSubmodule R L M :=
  sInf { N | s ⊆ N }

variable {R L s}

theorem mem_lieSpan {x : M} : x ∈ lieSpan R L s ↔ ∀ N : LieSubmodule R L M, s ⊆ N → x ∈ N := by
  rw [← SetLike.mem_coe, lieSpan, coe_sInf]
  exact mem_iInter₂

theorem subset_lieSpan : s ⊆ lieSpan R L s := by
  intro m hm
  rw [SetLike.mem_coe, mem_lieSpan]
  intro N hN
  exact hN hm

theorem submodule_span_le_lieSpan : Submodule.span R s ≤ lieSpan R L s := by
  rw [Submodule.span_le]
  apply subset_lieSpan

@[simp]
theorem lieSpan_le {N} : lieSpan R L s ≤ N ↔ s ⊆ N := by
  constructor
  · exact Subset.trans subset_lieSpan
  · intro hs m hm; rw [mem_lieSpan] at hm; exact hm _ hs

@[gcongr]
theorem lieSpan_mono {t : Set M} (h : s ⊆ t) : lieSpan R L s ≤ lieSpan R L t := by
  rw [lieSpan_le]
  exact Subset.trans h subset_lieSpan

theorem lieSpan_eq (N : LieSubmodule R L M) : lieSpan R L (N : Set M) = N :=
  le_antisymm (lieSpan_le.mpr rfl.subset) subset_lieSpan

theorem coe_lieSpan_submodule_eq_iff {p : Submodule R M} :
    (lieSpan R L (p : Set M) : Submodule R M) = p ↔ ∃ N : LieSubmodule R L M, ↑N = p := by
  rw [p.exists_lieSubmodule_coe_eq_iff L]; constructor <;> intro h
  · intro x m hm; rw [← h, mem_toSubmodule]; exact lie_mem _ (subset_lieSpan hm)
  · rw [← toSubmodule_mk p @h, coe_toSubmodule, toSubmodule_inj, lieSpan_eq]

variable (R L M)

/-- `lieSpan` forms a Galois insertion with the coercion from `LieSubmodule` to `Set`. -/
protected def gi : GaloisInsertion (lieSpan R L : Set M → LieSubmodule R L M) (↑) where
  choice s _ := lieSpan R L s
  gc _ _ := lieSpan_le
  le_l_u _ := subset_lieSpan
  choice_eq _ _ := rfl

@[simp]
theorem span_empty : lieSpan R L (∅ : Set M) = ⊥ :=
  (LieSubmodule.gi R L M).gc.l_bot

@[simp]
theorem span_univ : lieSpan R L (Set.univ : Set M) = ⊤ :=
  eq_top_iff.2 <| SetLike.le_def.2 <| subset_lieSpan

theorem lieSpan_eq_bot_iff : lieSpan R L s = ⊥ ↔ ∀ m ∈ s, m = (0 : M) := by
  rw [_root_.eq_bot_iff, lieSpan_le, bot_coe, subset_singleton_iff]

variable {M}

theorem span_union (s t : Set M) : lieSpan R L (s ∪ t) = lieSpan R L s ⊔ lieSpan R L t :=
  (LieSubmodule.gi R L M).gc.l_sup

theorem span_iUnion {ι} (s : ι → Set M) : lieSpan R L (⋃ i, s i) = ⨆ i, lieSpan R L (s i) :=
  (LieSubmodule.gi R L M).gc.l_iSup

/-- An induction principle for span membership. If `p` holds for 0 and all elements of `s`, and is
preserved under addition, scalar multiplication and the Lie bracket, then `p` holds for all
elements of the Lie submodule spanned by `s`. -/
@[elab_as_elim]
theorem lieSpan_induction {p : (x : M) → x ∈ lieSpan R L s → Prop}
    (mem : ∀ (x) (h : x ∈ s), p x (subset_lieSpan h))
    (zero : p 0 (LieSubmodule.zero_mem _))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem ‹_› ‹_›))
    (smul : ∀ (a : R) (x hx), p x hx → p (a • x) (SMulMemClass.smul_mem _ hx)) {x}
    (lie : ∀ (x : L) (y hy), p y hy → p (⁅x, y⁆) (LieSubmodule.lie_mem _ ‹_›))
    (hx : x ∈ lieSpan R L s) : p x hx := by
  let p : LieSubmodule R L M :=
    { carrier := { x | ∃ hx, p x hx }
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, add _ _ _ _ hpx hpy⟩
      zero_mem' := ⟨_, zero⟩
      smul_mem' := fun r ↦ fun ⟨_, hpx⟩ ↦ ⟨_, smul r _ _ hpx⟩
      lie_mem := fun ⟨_, hpy⟩ ↦ ⟨_, lie _ _ _ hpy⟩ }
  exact lieSpan_le (N := p) |>.mpr (fun y hy ↦ ⟨subset_lieSpan hy, mem y hy⟩) hx |>.elim fun _ ↦ id

lemma isCompactElement_lieSpan_singleton (m : M) :
    CompleteLattice.IsCompactElement (lieSpan R L {m}) := by
  rw [CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le]
  intro s hne hdir hsup
  replace hsup : m ∈ (↑(sSup s) : Set M) := (SetLike.le_def.mp hsup) (subset_lieSpan rfl)
  suffices (↑(sSup s) : Set M) = ⋃ N ∈ s, ↑N by simp_all
  replace hne : Nonempty s := Set.nonempty_coe_sort.mpr hne
  have := Submodule.coe_iSup_of_directed _ hdir.directed_val
  simp_rw [← iSup_toSubmodule, Set.iUnion_coe_set, coe_toSubmodule] at this
  rw [← this, SetLike.coe_set_eq, sSup_eq_iSup, iSup_subtype]

@[simp]
lemma sSup_image_lieSpan_singleton : sSup ((fun x ↦ lieSpan R L {x}) '' N) = N := by
  refine le_antisymm (sSup_le <| by simp) ?_
  simp_rw [← toSubmodule_le_toSubmodule, sSup_toSubmodule, Set.mem_image, SetLike.mem_coe]
  refine fun m hm ↦ Submodule.mem_sSup.mpr fun N' hN' ↦ ?_
  replace hN' : ∀ m ∈ N, lieSpan R L {m} ≤ N' := by simpa using hN'
  exact hN' _ hm (subset_lieSpan rfl)

instance instIsCompactlyGenerated : IsCompactlyGenerated (LieSubmodule R L M) :=
  ⟨fun N ↦ ⟨(fun x ↦ lieSpan R L {x}) '' N, fun _ ⟨m, _, hm⟩ ↦
    hm ▸ isCompactElement_lieSpan_singleton R L m, N.sSup_image_lieSpan_singleton⟩⟩

end LieSpan

end LatticeStructure

end LieSubmodule

section LieSubmoduleMapAndComap

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}
variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']
variable [AddCommGroup M] [Module R M] [LieRingModule L M]
variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

namespace LieSubmodule

variable (f : M →ₗ⁅R,L⁆ M') (N N₂ : LieSubmodule R L M) (N' : LieSubmodule R L M')

/-- A morphism of Lie modules `f : M → M'` pushes forward Lie submodules of `M` to Lie submodules
of `M'`. -/
def map : LieSubmodule R L M' :=
  { (N : Submodule R M).map (f : M →ₗ[R] M') with
    lie_mem := fun {x m'} h ↦ by
      rcases h with ⟨m, hm, hfm⟩; use ⁅x, m⁆; constructor
      · apply N.lie_mem hm
      · norm_cast at hfm; simp [hfm] }

@[simp] theorem coe_map : (N.map f : Set M') = f '' N := rfl

@[simp]
theorem toSubmodule_map : (N.map f : Submodule R M') = (N : Submodule R M).map (f : M →ₗ[R] M') :=
  rfl

/-- A morphism of Lie modules `f : M → M'` pulls back Lie submodules of `M'` to Lie submodules of
`M`. -/
def comap : LieSubmodule R L M :=
  { (N' : Submodule R M').comap (f : M →ₗ[R] M') with
    lie_mem := fun {x m} h ↦ by
      suffices ⁅x, f m⁆ ∈ N' by simp [this]
      apply N'.lie_mem h }

@[simp]
theorem toSubmodule_comap :
    (N'.comap f : Submodule R M) = (N' : Submodule R M').comap (f : M →ₗ[R] M') :=
  rfl

variable {f N N₂ N'}

theorem map_le_iff_le_comap : map f N ≤ N' ↔ N ≤ comap f N' :=
  Set.image_subset_iff

variable (f) in
theorem gc_map_comap : GaloisConnection (map f) (comap f) := fun _ _ ↦ map_le_iff_le_comap

theorem map_inf_le : (N ⊓ N₂).map f ≤ N.map f ⊓ N₂.map f :=
  Set.image_inter_subset f N N₂

theorem map_inf (hf : Function.Injective f) :
    (N ⊓ N₂).map f = N.map f ⊓ N₂.map f :=
  SetLike.coe_injective <| Set.image_inter hf

@[simp]
theorem map_sup : (N ⊔ N₂).map f = N.map f ⊔ N₂.map f :=
  (gc_map_comap f).l_sup

@[simp]
theorem comap_inf {N₂' : LieSubmodule R L M'} :
    (N' ⊓ N₂').comap f = N'.comap f ⊓ N₂'.comap f :=
  rfl

@[simp]
theorem map_iSup {ι : Sort*} (N : ι → LieSubmodule R L M) :
    (⨆ i, N i).map f = ⨆ i, (N i).map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_iSup

@[simp]
theorem mem_map (m' : M') : m' ∈ N.map f ↔ ∃ m, m ∈ N ∧ f m = m' :=
  Submodule.mem_map

theorem mem_map_of_mem {m : M} (h : m ∈ N) : f m ∈ N.map f :=
  Set.mem_image_of_mem _ h

@[simp]
theorem mem_comap {m : M} : m ∈ comap f N' ↔ f m ∈ N' :=
  Iff.rfl

theorem comap_incl_eq_top : N₂.comap N.incl = ⊤ ↔ N ≤ N₂ := by
  rw [← LieSubmodule.toSubmodule_inj, LieSubmodule.toSubmodule_comap, LieSubmodule.incl_coe,
    LieSubmodule.top_toSubmodule, Submodule.comap_subtype_eq_top, toSubmodule_le_toSubmodule]

theorem comap_incl_eq_bot : N₂.comap N.incl = ⊥ ↔ N ⊓ N₂ = ⊥ := by
  simp only [← toSubmodule_inj, toSubmodule_comap, incl_coe, bot_toSubmodule,
    inf_toSubmodule]
  rw [← Submodule.disjoint_iff_comap_eq_bot, disjoint_iff]

@[gcongr, mono]
theorem map_mono (h : N ≤ N₂) : N.map f ≤ N₂.map f :=
  Set.image_mono h

theorem map_comp
    {M'' : Type*} [AddCommGroup M''] [Module R M''] [LieRingModule L M''] {g : M' →ₗ⁅R,L⁆ M''} :
    N.map (g.comp f) = (N.map f).map g :=
  SetLike.coe_injective <| by
    simp only [← Set.image_comp, coe_map, LieModuleHom.coe_comp]

@[simp]
theorem map_id : N.map LieModuleHom.id = N := by ext; simp

@[simp] theorem map_bot :
    (⊥ : LieSubmodule R L M).map f = ⊥ := by
  ext m; simp [eq_comm]

lemma map_le_map_iff (hf : Function.Injective f) :
    N.map f ≤ N₂.map f ↔ N ≤ N₂ :=
  Set.image_subset_image_iff hf

lemma map_injective_of_injective (hf : Function.Injective f) :
    Function.Injective (map f) := fun {N N'} h ↦
  SetLike.coe_injective <| hf.image_injective <| by simp only [← coe_map, h]

/-- An injective morphism of Lie modules embeds the lattice of submodules of the domain into that
of the target. -/
@[simps] def mapOrderEmbedding {f : M →ₗ⁅R,L⁆ M'} (hf : Function.Injective f) :
    LieSubmodule R L M ↪o LieSubmodule R L M' where
  toFun := LieSubmodule.map f
  inj' := map_injective_of_injective hf
  map_rel_iff' := Set.image_subset_image_iff hf

variable (N) in
/-- For an injective morphism of Lie modules, any Lie submodule is equivalent to its image. -/
noncomputable def equivMapOfInjective (hf : Function.Injective f) :
    N ≃ₗ⁅R,L⁆ N.map f :=
  { Submodule.equivMapOfInjective (f : M →ₗ[R] M') hf N with
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specify `invFun` explicitly this way, otherwise we'd get a type mismatch
    invFun := by exact DFunLike.coe (Submodule.equivMapOfInjective (f : M →ₗ[R] M') hf N).symm
    map_lie' := by rintro x ⟨m, hm : m ∈ N⟩; ext; exact f.map_lie x m }

/-- An equivalence of Lie modules yields an order-preserving equivalence of their lattices of Lie
Submodules. -/
@[simps] def orderIsoMapComap (e : M ≃ₗ⁅R,L⁆ M') :
    LieSubmodule R L M ≃o LieSubmodule R L M' where
  toFun := map e
  invFun := comap e
  left_inv := fun N ↦ by ext; simp
  right_inv := fun N ↦ by ext; simp [e.apply_eq_iff_eq_symm_apply]
  map_rel_iff' := fun {_ _} ↦ Set.image_subset_image_iff e.injective

end LieSubmodule


end LieSubmoduleMapAndComap

namespace LieModuleHom

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}
variable [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]
variable [AddCommGroup N] [Module R N] [LieRingModule L N]
variable (f : M →ₗ⁅R,L⁆ N)

/-- The kernel of a morphism of Lie algebras, as an ideal in the domain. -/
def ker : LieSubmodule R L M :=
  LieSubmodule.comap f ⊥

@[simp]
theorem ker_toSubmodule : (f.ker : Submodule R M) = LinearMap.ker (f : M →ₗ[R] N) :=
  rfl

theorem ker_eq_bot : f.ker = ⊥ ↔ Function.Injective f := by
  rw [← LieSubmodule.toSubmodule_inj, ker_toSubmodule, LieSubmodule.bot_toSubmodule,
    LinearMap.ker_eq_bot, coe_toLinearMap]

variable {f}

@[simp]
theorem mem_ker {m : M} : m ∈ f.ker ↔ f m = 0 :=
  Iff.rfl

@[simp]
theorem ker_id : (LieModuleHom.id : M →ₗ⁅R,L⁆ M).ker = ⊥ :=
  rfl

@[simp]
theorem comp_ker_incl : f.comp f.ker.incl = 0 := by ext ⟨m, hm⟩; exact mem_ker.mp hm

theorem le_ker_iff_map (M' : LieSubmodule R L M) : M' ≤ f.ker ↔ LieSubmodule.map f M' = ⊥ := by
  rw [ker, eq_bot_iff, LieSubmodule.map_le_iff_le_comap]

variable (f)

/-- The range of a morphism of Lie modules `f : M → N` is a Lie submodule of `N`.
See Note [range copy pattern]. -/
def range : LieSubmodule R L N :=
  (LieSubmodule.map f ⊤).copy (Set.range f) Set.image_univ.symm

@[simp]
theorem coe_range : f.range = Set.range f :=
  rfl

@[simp]
theorem toSubmodule_range : f.range = LinearMap.range (f : M →ₗ[R] N) :=
  rfl

@[simp]
theorem mem_range (n : N) : n ∈ f.range ↔ ∃ m, f m = n :=
  Iff.rfl

@[simp]
theorem map_top : LieSubmodule.map f ⊤ = f.range := by ext; simp [LieSubmodule.mem_map]

theorem range_eq_top : f.range = ⊤ ↔ Function.Surjective f := by
  rw [SetLike.ext'_iff, coe_range, LieSubmodule.top_coe, Set.range_eq_univ]

/-- A morphism of Lie modules `f : M → N` whose values lie in a Lie submodule `P ⊆ N` can be
restricted to a morphism of Lie modules `M → P`. -/
def codRestrict (P : LieSubmodule R L N) (f : M →ₗ⁅R,L⁆ N) (h : ∀ m, f m ∈ P) :
    M →ₗ⁅R,L⁆ P where
  toFun := f.toLinearMap.codRestrict P h
  __ := f.toLinearMap.codRestrict P h
  map_lie' {x m} := by ext; simp

@[simp]
lemma codRestrict_apply (P : LieSubmodule R L N) (f : M →ₗ⁅R,L⁆ N) (h : ∀ m, f m ∈ P) (m : M) :
    (f.codRestrict P h m : N) = f m :=
  rfl

end LieModuleHom

namespace LieSubmodule

variable {R : Type u} {L : Type v} {M : Type w}
variable [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]
variable (N : LieSubmodule R L M)

@[simp]
theorem ker_incl : N.incl.ker = ⊥ := (LieModuleHom.ker_eq_bot N.incl).mpr <| injective_incl N

@[simp]
theorem range_incl : N.incl.range = N := by
  simp only [← toSubmodule_inj, LieModuleHom.toSubmodule_range, incl_coe]
  rw [Submodule.range_subtype]

@[simp]
theorem comap_incl_self : comap N.incl N = ⊤ := by
  simp only [← toSubmodule_inj, toSubmodule_comap, incl_coe, top_toSubmodule]
  rw [Submodule.comap_subtype_self]

theorem map_incl_top : (⊤ : LieSubmodule R L N).map N.incl = N := by simp

variable {N}

@[simp]
lemma map_le_range {M' : Type*}
    [AddCommGroup M'] [Module R M'] [LieRingModule L M'] (f : M →ₗ⁅R,L⁆ M') :
    N.map f ≤ f.range := by
  rw [← LieModuleHom.map_top]
  exact LieSubmodule.map_mono le_top

@[simp]
lemma map_incl_lt_iff_lt_top {N' : LieSubmodule R L N} :
    N'.map (LieSubmodule.incl N) < N ↔ N' < ⊤ := by
  convert (LieSubmodule.mapOrderEmbedding (f := N.incl) Subtype.coe_injective).lt_iff_lt
  simp

@[simp]
lemma map_incl_le {N' : LieSubmodule R L N} :
    N'.map N.incl ≤ N := by
  conv_rhs => rw [← N.map_incl_top]
  exact LieSubmodule.map_mono le_top

end LieSubmodule

section TopEquiv

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L]

variable (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M]

/-- The natural equivalence between the 'top' Lie submodule and the enclosing Lie module. -/
def LieModuleEquiv.ofTop : (⊤ : LieSubmodule R L M) ≃ₗ⁅R,L⁆ M :=
  { LinearEquiv.ofTop ⊤ rfl with
    map_lie' := rfl }

variable {R L}

lemma LieModuleEquiv.ofTop_apply (x : (⊤ : LieSubmodule R L M)) :
    LieModuleEquiv.ofTop R L M x = x :=
  rfl

@[simp] lemma LieModuleEquiv.range_coe {M' : Type*}
    [AddCommGroup M'] [Module R M'] [LieRingModule L M'] (e : M ≃ₗ⁅R,L⁆ M') :
    LieModuleHom.range (e : M →ₗ⁅R,L⁆ M') = ⊤ := by
  rw [LieModuleHom.range_eq_top]
  exact e.surjective

variable [LieAlgebra R L] [LieModule R L M]

/-- The natural equivalence between the 'top' Lie subalgebra and the enclosing Lie algebra.

This is the Lie subalgebra version of `Submodule.topEquiv`. -/
def LieSubalgebra.topEquiv : (⊤ : LieSubalgebra R L) ≃ₗ⁅R⁆ L :=
  { (⊤ : LieSubalgebra R L).incl with
    invFun := fun x ↦ ⟨x, Set.mem_univ x⟩ }

@[simp]
theorem LieSubalgebra.topEquiv_apply (x : (⊤ : LieSubalgebra R L)) : LieSubalgebra.topEquiv x = x :=
  rfl

end TopEquiv
