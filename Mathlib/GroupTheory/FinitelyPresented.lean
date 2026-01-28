/-
Copyright (c) 2025 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero, Riccardo Brasca, Stefano Francaviglia, Hang Lu Su,
Francesco Milizia, Valerio Proietti, Lawrence Wu
-/
module

public import Mathlib.GroupTheory.Presentation
public import Mathlib.GroupTheory.Finiteness

/-!
# Finitely presented groups

This file defines `Group.FinitelyPresented` by requiring a presentation on `Fin n` for some `n : ℕ`.
It connects to the `Group.Presentation` structure and the `PresentedGroup` constructions.

Main definitions:
* `Group.Presentation.IsFinite` asserts that a presentation has a finite type of generators
  and a finite set of relators.
* `Group.FinitelyPresented` is the property that a group admits a presentation on `Fin n`
  with finitely many relators.
* `Group.finitelyPresented_congr` shows that being finitely presented is invariant
  under group isomorphism.
* `Group.fg_of_finitelyPresented` shows that every finitely presented group is
  finitely generated.
-/

@[expose] public section

namespace Group

universe u

namespace Presentation

variable {G : Type u} [Group G] {ι : Type*}

/-- A presentation is finite if the generators and relators are finite. -/
def IsFinite (P : Group.Presentation G ι) : Prop :=
  Finite ι ∧ P.rels.Finite

end Presentation

/--
A group is finitely presented if it admits a presentation with generators indexed by `Fin n`
for some `n : ℕ`, and with finitely many relators (a `Finset` of relators).
-/
def FinitelyPresented (G : Type u) [Group G] : Prop :=
  ∃ (n : ℕ) (val : Fin n → G) (rels : Finset (FreeGroup (Fin n))),
    Subgroup.closure (Set.range val) = ⊤ ∧
      (FreeGroup.lift val).ker = Subgroup.normalClosure (rels : Set (FreeGroup (Fin n)))

section

variable {G : Type u} [Group G]

/--
From the definition of `FinitelyPresented`, we can package the data
into an actual `Group.Presentation` (on `Fin n`) which is `IsFinite`.
-/
theorem exists_isFinite_presentation_of_finitelyPresented :
    Group.FinitelyPresented (G := G) →
      ∃ (ι : Type) (P : Group.Presentation G ι), P.IsFinite := by
  rintro ⟨n, val, rels, hcl, hker⟩
  let P : Group.Presentation G (Fin n) :=
    { val := val
      closure_range_val := hcl
      rels := (rels : Set (FreeGroup (Fin n)))
      ker_eq_normalClosure := by simpa using hker }
  refine ⟨Fin n, P, ?_⟩
  constructor
  · infer_instance
  · -- `rels` is a finset, hence finite as a set
    simp [P]

/-- A finite presentation yields finite relators and an isomorphism with a `PresentedGroup`. -/
theorem finitelyPresented_exists_presentedGroup :
    Group.FinitelyPresented (G := G) →
      ∃ (α : Type) (rels : Set (FreeGroup α)),
        Finite α ∧ rels.Finite ∧ Nonempty (PresentedGroup rels ≃* G) := by
  rintro ⟨n, val, rels, hcl, hker⟩
  let P : Group.Presentation G (Fin n) :=
    { val := val
      closure_range_val := hcl
      rels := (rels : Set (FreeGroup (Fin n)))
      ker_eq_normalClosure := by simpa using hker }
  refine ⟨Fin n, (rels : Set (FreeGroup (Fin n))), ?_, ?_, ?_⟩
  · infer_instance
  · simp only [Finset.finite_toSet]
  · refine ⟨?_⟩
    simpa [Presentation.presentedGroup] using (P.equivPresentedGroup)

/-- Finitely presented groups are finitely generated. -/
theorem fg_of_finitelyPresented :
    Group.FinitelyPresented (G := G) → Group.FG G := by
  rintro ⟨n, val, rels, hcl, -⟩
  refine (Group.fg_iff).2 ?_
  refine ⟨Set.range val, ?_, ?_⟩
  · simpa using hcl
  · simpa using (Set.finite_range val)

/-- `FinitelyPresented` is invariant under group isomorphism. -/
theorem finitelyPresented_congr {H : Type _} [Group H] (e : G ≃* H) :
    Group.FinitelyPresented (G := G) ↔ Group.FinitelyPresented (G := H) := by
  constructor
  · rintro ⟨n, val, rels, hcl, hker⟩
    let P : Group.Presentation G (Fin n) :=
      { val := val
        closure_range_val := hcl
        rels := (rels : Set (FreeGroup (Fin n)))
        ker_eq_normalClosure := by simpa using hker }
    let P' := Group.Presentation.mapMulEquiv (P := P) e
    refine ⟨n, P'.val, rels, ?_, ?_⟩
    · simpa [P', P, Group.Presentation.mapMulEquiv] using P'.closure_range_val
    · simpa [P', P, Group.Presentation.mapMulEquiv] using P'.ker_eq_normalClosure
  · intro h
    rcases h with ⟨n, val, rels, hcl, hker⟩
    let P : Group.Presentation H (Fin n) :=
      { val := val
        closure_range_val := hcl
        rels := (rels : Set (FreeGroup (Fin n)))
        ker_eq_normalClosure := by simpa using hker }
    let P' := Group.Presentation.mapMulEquiv (P := P) e.symm
    refine ⟨n, P'.val, rels, ?_, ?_⟩
    · simpa [P', P, Group.Presentation.mapMulEquiv] using P'.closure_range_val
    · simpa [P', P, Group.Presentation.mapMulEquiv] using P'.ker_eq_normalClosure

end

namespace PresentedGroup

universe v

variable {α : Type v} (rels : Set (FreeGroup α))

/-- If `α` and `rels` are finite, then `PresentedGroup rels` is finitely presented. -/
theorem finitelyPresented_of_finite
    [Finite α] (hrels : rels.Finite) :
    Group.FinitelyPresented (G := PresentedGroup rels) := by
  -- Choose `Fin n` equivalent to `α`.
  rcases Finite.exists_equiv_fin α with ⟨n, ⟨eα⟩⟩
  let e : Fin n ≃ α := eα.symm
  let E : FreeGroup (Fin n) ≃* FreeGroup α := FreeGroup.freeGroupCongr e
  -- Transport relators along `E.symm`.
  let rels' : Set (FreeGroup (Fin n)) := (fun r => E.symm r) '' rels
  have hrels' : rels'.Finite := hrels.image (fun r => E.symm r)
  let relsFin : Finset (FreeGroup (Fin n)) := hrels'.toFinset
  have hrelsFin_coe : (relsFin : Set (FreeGroup (Fin n))) = rels' := by
    ext x
    simp [relsFin]
  refine ⟨n, (fun i : Fin n => PresentedGroup.of (rels := rels) (e i)), relsFin, ?_, ?_⟩
  · -- closure of the generator images
    have hrange :
        Set.range (fun i : Fin n => PresentedGroup.of (rels := rels) (e i)) =
          Set.range (PresentedGroup.of (rels := rels) : α → PresentedGroup rels) := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e i, rfl⟩
      · rintro ⟨a, rfl⟩
        rcases e.surjective a with ⟨i, rfl⟩
        exact ⟨i, rfl⟩
    simp [hrange]
  · -- kernel computation
    have hlift :
        FreeGroup.lift (fun i : Fin n => PresentedGroup.of (rels := rels) (e i))
          = (PresentedGroup.mk rels).comp E.toMonoidHom := by
      ext i
      simp [PresentedGroup.of, E]
    have hker_mk : (PresentedGroup.mk rels).ker = Subgroup.normalClosure rels := by
      ext x
      simp [MonoidHom.mem_ker, PresentedGroup.mk_eq_one_iff]
    -- Identify the preimage of `rels` under `E` with the image under `E.symm` (i.e. `rels'`).
    have hpre :
        ((fun x : FreeGroup (Fin n) => (E : FreeGroup (Fin n) → FreeGroup α) x) ⁻¹' rels) =
          rels' := by
      ext x
      constructor
      · intro hx
        refine ⟨(E : FreeGroup (Fin n) → FreeGroup α) x, hx, ?_⟩
        simp only [MulEquiv.symm_apply_apply]
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    calc
      (FreeGroup.lift (fun i : Fin n => PresentedGroup.of (rels := rels) (e i))).ker
          = ((PresentedGroup.mk rels).comp E.toMonoidHom).ker := by
              simp [hlift]
      _ = Subgroup.comap E.toMonoidHom (PresentedGroup.mk rels).ker := by
              ext x
              simp [MonoidHom.mem_ker, MonoidHom.comp_apply]
      _ = Subgroup.comap E.toMonoidHom (Subgroup.normalClosure rels) := by
              simp [hker_mk]
      _ = Subgroup.normalClosure
            ((fun x : FreeGroup (Fin n) => (E : FreeGroup (Fin n) → FreeGroup α) x) ⁻¹' rels) := by
              simpa using (Subgroup.comap_normalClosure (s := rels) E).symm
      _ = Subgroup.normalClosure rels' := by
              simp [hpre]
      _ = Subgroup.normalClosure (relsFin : Set (FreeGroup (Fin n))) := by
              simp [hrelsFin_coe]

end PresentedGroup

section

universe v

variable {G : Type u} [Group G]

/-- An isomorphism from a finitely presented `PresentedGroup` makes `G` finitely presented. -/
theorem finitelyPresented_of_exists_presentedGroup :
    (∃ (α : Type v) (rels : Set (FreeGroup α)),
        Finite α ∧ rels.Finite ∧ Nonempty (PresentedGroup rels ≃* G)) →
      Group.FinitelyPresented (G := G) := by
  rintro ⟨α, rels, hα, hrels, ⟨e⟩⟩
  haveI : Finite α := hα
  have hPG : Group.FinitelyPresented (G := PresentedGroup rels) :=
    PresentedGroup.finitelyPresented_of_finite (rels := rels) hrels
  exact (Group.finitelyPresented_congr (G := PresentedGroup rels) (H := G) e).1 hPG

/-- Characterization via isomorphism with a `PresentedGroup` with finite generators and relators. -/
theorem finitelyPresented_iff_exists_presentedGroup :
    Group.FinitelyPresented (G := G) ↔
      ∃ (α : Type) (rels : Set (FreeGroup α)),
        Finite α ∧ rels.Finite ∧ Nonempty (PresentedGroup rels ≃* G) := by
  constructor
  · intro h
    simpa using (finitelyPresented_exists_presentedGroup (G := G) h)
  · exact finitelyPresented_of_exists_presentedGroup (G := G)

/--
If `G` admits *some* finite presentation (on a finite generator type),
then `G` is finitely presented in the `Fin n` sense of `Group.FinitelyPresented`.
-/
theorem finitelyPresented_of_exists_isFinite_presentation :
    (∃ (ι : Type v) (P : Group.Presentation G ι), P.IsFinite) →
      Group.FinitelyPresented (G := G) := by
  rintro ⟨ι, P, hP⟩
  refine finitelyPresented_of_exists_presentedGroup (G := G) ?_
  refine ⟨ι, P.rels, ?_, ?_, ?_⟩
  · exact hP.1
  · exact hP.2
  · refine ⟨?_⟩
    simpa [Presentation.presentedGroup] using P.equivPresentedGroup

/--
Characterization: `G` is finitely presented iff it admits a presentation
which is `IsFinite`.
-/
theorem finitelyPresented_iff_exists_isFinite_presentation :
    Group.FinitelyPresented (G := G) ↔
      ∃ (ι : Type) (P : Group.Presentation G ι), P.IsFinite := by
  constructor
  · intro h
    simpa using (exists_isFinite_presentation_of_finitelyPresented (G := G) h)
  · intro h
    exact finitelyPresented_of_exists_isFinite_presentation (G := G) h

end

end Group
