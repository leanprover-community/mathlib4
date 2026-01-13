/-
Copyright (c) 2025 Valerio Proietti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero, Riccardo Brasca, Stefano Francaviglia,
Francesco Milizia, Valerio Proietti, Hang Lu Su, Lawrence Wu
-/
module

public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Presentation of a group
This file introduces the notion of 'Presentation' of a group, aligned with
`Mathlib.GroupTheory.PresentedGroup`.

Main definitions:
* `Group.GeneratingSet` packages a type of generators with a map to the group whose range
  generates it.
* `Group.Presentation` extends a generating set with relators and the usual kernel condition.
* `Group.Presentation.toGroup` is the canonical map `PresentedGroup P.rels →* G`.
* `Group.Presentation.mapMulEquiv` transports a presentation along a group isomorphism.
* `Group.Presentation.equivPresentedGroup` identifies `PresentedGroup P.rels` with `G`.
-/

@[expose] public section

namespace Group

/-- A generating system for a group `G` indexed by `ι`. -/
-- direct presentation, don't do it in two steps
structure GeneratingSet (G : Type*) [Group G] (ι : Type*) where
  /-- The assignment of each abstract generator to an element of `G`. -/
  val : ι → G
  /-- The images of the generators generate `G`. -/
  closure_range_val : Subgroup.closure (Set.range val) = ⊤

/-- A presentation of a group `G` with generators indexed by `ι`. -/
structure Presentation (G : Type*) [Group G] (ι : Type*)
    extends GeneratingSet G ι where
  /-- The relations (relators). -/
  rels : Set (FreeGroup ι)
  /-- Kernel of the induced map is the normal closure of the relators. -/
  ker_eq_normalClosure : (FreeGroup.lift val).ker = Subgroup.normalClosure rels

namespace GeneratingSet

variable {G : Type*} [Group G] {ι : Type*}

/-- If the range of `X.val` generates `G`, then `FreeGroup.lift X.val` is surjective. -/
theorem lift_surjective (X : GeneratingSet G ι) :
    Function.Surjective (FreeGroup.lift X.val) := by
  have hrange : (FreeGroup.lift X.val).range = ⊤ := by
    simp [FreeGroup.range_lift_eq_closure, X.closure_range_val]
  exact MonoidHom.range_eq_top.mp hrange

end GeneratingSet

namespace Presentation

variable {G : Type*} [Group G] {ι : Type*}

/-- The `PresentedGroup` attached to a `Group.Presentation`. -/
abbrev presentedGroup (P : Presentation G ι) : Type _ :=
  PresentedGroup P.rels

@[simp]
lemma presentedGroup_def (P : Presentation G ι) :
    P.presentedGroup = PresentedGroup P.rels := rfl

/-- Each relator maps to `1` under the induced map `FreeGroup ι →* G`. -/
theorem lift_eq_one_of_mem_rels (P : Presentation G ι) {r : FreeGroup ι}
    (hr : r ∈ P.rels) :
    FreeGroup.lift P.val r = 1 := by
  have : r ∈ (FreeGroup.lift P.val).ker := by
    simpa [P.ker_eq_normalClosure] using
      (Subgroup.subset_normalClosure hr :
        r ∈ Subgroup.normalClosure P.rels)
  simpa [MonoidHom.mem_ker] using this

/--
Given a `Group.Presentation G ι`, we obtain the canonical map
`PresentedGroup P.rels →* G` (sending generators to `P.val`).
-/
def toGroup (P : Presentation G ι) :
    P.presentedGroup →* G :=
  PresentedGroup.toGroup (rels := P.rels)
    (f := P.val) (by
      intro r hr
      simpa using (P.lift_eq_one_of_mem_rels (r := r) hr))

@[simp]
theorem toGroup_of (P : Presentation G ι) (x : ι) :
    P.toGroup (PresentedGroup.of (rels := P.rels) x) = P.val x := by
  simp [Presentation.toGroup]

/--
Transport a presentation across a group isomorphism.
If `P` is a presentation of `G` and `e : G ≃* H`, we get a presentation of `H`
with the same generators/relators and generator map composed with `e`.
-/
def mapMulEquiv {G : Type*} [Group G] {H : Type*} [Group H]
    {ι : Type*} (P : Presentation G ι) (e : G ≃* H) :
    Presentation H ι :=
{ val := fun i => e (P.val i)
  closure_range_val := by
    -- express the new range as the image of the old range
    have hrange :
        Set.range (fun i : ι => e (P.val i)) = e '' Set.range P.val := by
      simpa [Function.comp] using
        (Set.range_comp (f := P.val) (g := fun x : G => e x))
    -- map closure along `e`
    have hcl :
        Subgroup.closure (Set.range fun i : ι => e (P.val i))
          = Subgroup.map e.toMonoidHom (Subgroup.closure (Set.range P.val)) := by
      simpa [hrange] using
        (MonoidHom.map_closure (e.toMonoidHom) (Set.range P.val)).symm
    simp [hcl, P.closure_range_val]
  rels := P.rels
  ker_eq_normalClosure := by
    -- identify the lift as a composition
    have hlift :
        FreeGroup.lift (fun i : ι => e (P.val i))
          = e.toMonoidHom.comp (FreeGroup.lift P.val) := by
      ext i
      simp
    -- kernel unchanged because `e` is injective
    have hker :
        (FreeGroup.lift (fun i : ι => e (P.val i))).ker
          = (FreeGroup.lift P.val).ker := by
      apply le_antisymm
      · intro x hx
        -- `x ∈ ker (e ∘ φ)` implies `φ x = 1` by injectivity
        have : e (FreeGroup.lift P.val x) = 1 := by
          -- `hx : (e ∘ φ) x = 1`
          simpa [hlift, MonoidHom.mem_ker] using hx
        have : FreeGroup.lift P.val x = 1 := e.injective (by simpa using this)
        simpa [MonoidHom.mem_ker] using this
      · intro x hx
        -- `x ∈ ker φ` implies `x ∈ ker (e ∘ φ)`
        have : FreeGroup.lift P.val x = 1 := by
          simpa [MonoidHom.mem_ker] using hx
        simp [hlift, MonoidHom.mem_ker, this]
    simpa [hker] using P.ker_eq_normalClosure }

/--
From a `Group.Presentation G ι`, build a group isomorphism
`PresentedGroup P.rels ≃* G`.
-/
noncomputable def equivPresentedGroup {G : Type*} [Group G] {ι : Type*}
    (P : Presentation G ι) : P.presentedGroup ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq P.ker_eq_normalClosure.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (FreeGroup.lift P.val)
      P.toGeneratingSet.lift_surjective)

/-!
Any two presentations of the same group present isomorphic groups.
-/
-- better name for this?
noncomputable def equivPresentedGroups {G : Type*} [Group G]
    {ι κ : Type*} (P : Presentation G ι) (Q : Presentation G κ) :
    P.presentedGroup ≃* Q.presentedGroup :=
  P.equivPresentedGroup.trans Q.equivPresentedGroup.symm

end Presentation

namespace PresentedGroup

variable {α : Type*} (rels : Set (FreeGroup α))

@[simp]
theorem lift_of_eq_mk :
    FreeGroup.lift (PresentedGroup.of (rels := rels)) = PresentedGroup.mk rels := by
  ext a
  simp [PresentedGroup.of]

/-- The canonical `Group.Presentation` of `PresentedGroup rels`. -/
def toPresentation : Group.Presentation (PresentedGroup rels) α where
  val := PresentedGroup.of (rels := rels)
  closure_range_val := by
    simp [PresentedGroup.closure_range_of]
  rels := rels
  ker_eq_normalClosure := by
    ext x
    simp [MonoidHom.mem_ker, PresentedGroup.mk_eq_one_iff, lift_of_eq_mk (rels := rels)]

end PresentedGroup

/-!
## Tietze transformations

This section records the four standard Tietze moves for group presentations.
-/

namespace Tietze

variable {G : Type*} [Group G] {ι : Type*}

-- Local aliases to keep the added generator clearly distinguished.
local notation "ι'" => Option ι
local notation "newGen" => (none : ι')
local notation "old" => Option.some

/-!
### Equal normal closures give isomorphic presented groups
-/

noncomputable def equiv_of_normalClosure_eq
    (rels₁ rels₂ : Set (FreeGroup ι))
    (h : Subgroup.normalClosure rels₁ = Subgroup.normalClosure rels₂) :
    PresentedGroup rels₁ ≃* PresentedGroup rels₂ := by
  simpa [PresentedGroup] using
    (QuotientGroup.quotientMulEquivOfEq (G := FreeGroup ι)
      (M := Subgroup.normalClosure rels₁) (N := Subgroup.normalClosure rels₂) h)

/-- Adding a relator already in the normal closure does not change the normal closure. -/
lemma normalClosure_union_singleton_eq_of_mem
    (rels : Set (FreeGroup ι)) (r : FreeGroup ι)
    (hr : r ∈ Subgroup.normalClosure rels) :
    Subgroup.normalClosure (rels ∪ {r}) = Subgroup.normalClosure rels := by
  apply le_antisymm
  · refine Subgroup.normalClosure_le_normal
      (s := rels ∪ {r}) (N := Subgroup.normalClosure rels) ?_
    intro x hx
    rcases hx with hx | hx
    · exact Subgroup.subset_normalClosure hx
    · rcases Set.mem_singleton_iff.mp hx with rfl
      simpa using hr
  · exact Subgroup.normalClosure_mono (Set.subset_union_left)

/-!
### (1) Add a derived relation
-/

/--
Given `P : Group.Presentation G ι`, if `r` lies in the normal closure of `P.rels`,
we can add `r` as a relator and still get a presentation of `G`.
-/
def addRelator (P : Group.Presentation G ι) (r : FreeGroup ι)
    (hr : r ∈ Subgroup.normalClosure P.rels) :
    Group.Presentation G ι where
  val := P.val
  closure_range_val := P.closure_range_val
  rels := Set.insert r P.rels
  ker_eq_normalClosure := by
    -- use that the normal closure does not change after inserting a derived relator
    have hN :
        Subgroup.normalClosure (Set.insert r P.rels) =
          Subgroup.normalClosure P.rels := by
      simpa [Set.insert, Set.union_comm] using
        (normalClosure_union_singleton_eq_of_mem (ι := ι) (rels := P.rels) (r := r) hr)
    -- rewrite `P.ker_eq_normalClosure` along `hN`
    simpa [hN] using P.ker_eq_normalClosure

/--
Tietze (1), at the level of presented groups: adding a derived relator gives an isomorphic
presented group.
-/
noncomputable def add_relator_equiv
    (P : Group.Presentation G ι) (r : FreeGroup ι)
    (hr : r ∈ Subgroup.normalClosure P.rels) :
    P.presentedGroup ≃* (addRelator (G := G) (ι := ι) P r hr).presentedGroup := by
  simpa using
    (Presentation.equivPresentedGroups (G := G) (P := P)
      (Q := addRelator (G := G) (ι := ι) P r hr))

/-!
### (2) Remove a derived relation
-/

/--
Given `P : Group.Presentation G ι`, if a relator `r` is derivable from the other relators
(i.e. `r ∈ normalClosure (P.rels \ {r})`),
then we may remove it and still get a presentation of `G`.
-/
def removeRelator (P : Group.Presentation G ι) (r : FreeGroup ι)
    (hr : r ∈ Subgroup.normalClosure (P.rels \ {r})) :
    Group.Presentation G ι where
  val := P.val
  closure_range_val := P.closure_range_val
  rels := P.rels \ {r}
  ker_eq_normalClosure := by
    -- Show that every relator of `P` lies in the normal closure of `P.rels \\ {r}`.
    have hsubset :
        P.rels ⊆ Subgroup.normalClosure (P.rels \ {r}) := by
      intro x hx
      by_cases hxr : x = r
      · -- the removed relator is in the normal closure by assumption
        simpa [hxr] using hr
      · -- the others are already in the subset
        have hx' : x ∈ P.rels \ {r} := ⟨hx, by simp [Set.mem_singleton_iff, hxr]⟩
        exact Subgroup.subset_normalClosure hx'
    -- so the normal closure of `P.rels` is contained in that of `P.rels \\ {r}`
    have hle :
        Subgroup.normalClosure P.rels ≤
          Subgroup.normalClosure (P.rels \ {r}) :=
      Subgroup.normalClosure_le_normal
        (s := P.rels) (N := Subgroup.normalClosure (P.rels \ {r})) hsubset
    have hge :
        Subgroup.normalClosure (P.rels \ {r}) ≤
          Subgroup.normalClosure P.rels :=
      Subgroup.normalClosure_mono (by intro x hx; exact hx.1)
    have hN :
        Subgroup.normalClosure (P.rels \ {r}) =
          Subgroup.normalClosure P.rels :=
      le_antisymm hge hle
    simpa [hN] using P.ker_eq_normalClosure

/--
Tietze (2), at the level of presented groups: removing a derivable relator gives an isomorphic
presented group.
-/
noncomputable def remove_relator_equiv
    (P : Group.Presentation G ι) (r : FreeGroup ι)
    (hr : r ∈ Subgroup.normalClosure (P.rels \ {r})) :
    P.presentedGroup ≃* (removeRelator (G := G) (ι := ι) P r hr).presentedGroup := by
  simpa using
    (Presentation.equivPresentedGroups (G := G) (P := P)
      (Q := removeRelator (G := G) (ι := ι) P r hr))

/-!
### Helper Lemmas
-/

/--
A technical lemma for Tietze (3):
If we map `none` to `w` and `some i` to `some i`, the kernel is exactly the normal closure
of the defining relation `none * w⁻¹`.
-/
theorem ker_lift_option_eq_normalClosure_defined {w : FreeGroup ι} :
    (FreeGroup.lift (Option.rec w (FreeGroup.of)) : FreeGroup ι' →* FreeGroup ι).ker =
    Subgroup.normalClosure {FreeGroup.of newGen * (FreeGroup.map old w)⁻¹} := by
  -- Notation for the map and the relator.
  let ρ : FreeGroup ι' →* FreeGroup ι :=
    FreeGroup.lift (Option.rec w FreeGroup.of)
  let r : FreeGroup ι' :=
    FreeGroup.of newGen * (FreeGroup.map old w)⁻¹
  -- `r` is killed by `ρ`.
  have hr : ρ r = 1 := by
    have hmap : ρ (FreeGroup.map old w) = w := by
      -- `ρ ∘ map some = id`.
      have hcomp : ρ.comp (FreeGroup.map old) = MonoidHom.id _ := by
        ext i; simp [ρ]
      have hmap' := congrArg (fun f => f w) hcomp
      simpa [MonoidHom.comp_apply] using hmap'
    simp [r, ρ, hmap]
  -- One inclusion: the kernel is a normal subgroup containing `r`.
  have h_sub : Subgroup.normalClosure ({r} : Set (FreeGroup ι')) ≤ ρ.ker :=
    Subgroup.normalClosure_le_normal (s := {r}) (N := ρ.ker) (by
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      simp [MonoidHom.mem_ker, hr])
  -- Factor through the quotient by the normal closure of `r`.
  let R : Subgroup (FreeGroup ι') :=
    Subgroup.normalClosure ({r} : Set (FreeGroup ι'))
  let q : FreeGroup ι' →* _ := QuotientGroup.mk' R
  have hq : q.ker = R := QuotientGroup.ker_mk' _
  let ρ' : FreeGroup ι' ⧸ R →* FreeGroup ι :=
    QuotientGroup.lift R ρ (by
      intro x hx
      exact h_sub hx)
  -- A section sending `i` to `some i`.
  let σ : FreeGroup ι →* FreeGroup ι' ⧸ R :=
    q.comp (FreeGroup.map old)
  have hρσ : ρ'.comp σ = MonoidHom.id _ := by
    ext i
    simp [ρ', σ, ρ, q]
  -- Also `σ` is a left inverse of `ρ'` (it fixes the generators in the quotient).
  have hσρ : (σ.comp ρ').comp q = q := by
    ext i
    cases i with
    | some i =>
        simp [σ, ρ', q, ρ]
    | none =>
        -- In the quotient, `of none = map some w`.
        have hrel : q (FreeGroup.of newGen) = q (FreeGroup.map old w) := by
          -- `((map some w)⁻¹) * r⁻¹ * (map some w)` lies in `R`.
          have hrR : r ∈ R := Subgroup.subset_normalClosure (by simp [r])
          have hrR_inv : r⁻¹ ∈ R := Subgroup.inv_mem _ hrR
          have hconj :
              (FreeGroup.map old w)⁻¹ * r⁻¹ * (FreeGroup.map old w) ∈ R := by
            -- normality of `R` gives closure under conjugation
            simpa using
              (inferInstance : Subgroup.Normal R).conj_mem
                (n := r⁻¹) hrR_inv (FreeGroup.map old w)⁻¹
          have hconj' :
              (FreeGroup.of newGen)⁻¹ * FreeGroup.map old w ∈ R := by
            have : (FreeGroup.map old w)⁻¹ * r⁻¹ * (FreeGroup.map old w)
                = (FreeGroup.of newGen)⁻¹ * FreeGroup.map old w := by
              simp [r]
            simpa [this] using hconj
          -- equality in the quotient
          apply QuotientGroup.eq.mpr
          simpa using hconj'
        simp [σ, ρ', q, ρ, hrel]
  -- Use surjectivity of `q` to conclude `σ ∘ ρ' = id`.
  have hσρ' : σ.comp ρ' = MonoidHom.id _ := by
    -- Two homs out of the quotient are equal if they agree after precomposing with `q`.
    refine MonoidHom.ext ?_
    intro x
    rcases Quot.exists_rep x with ⟨y, rfl⟩
    simpa [MonoidHom.comp_apply] using congrArg (fun f => f y) hσρ
  -- `ρ'` is injective, hence has trivial kernel.
  have hkerρ' : ρ'.ker = ⊥ := by
    have hlinv : Function.LeftInverse σ ρ' := by
      intro x
      have := congrArg (fun f => f x) hσρ'
      simpa [MonoidHom.comp_apply] using this
    exact (ρ'.ker_eq_bot_iff).2 hlinv.injective
  -- Pull back the trivial kernel along `q`.
  refine le_antisymm ?_ h_sub
  intro x hx
  have hx' : q x ∈ ρ'.ker := by
    -- `ρ x = 1` implies `ρ' (q x) = 1`.
    simpa [ρ', MonoidHom.mem_ker, MonoidHom.comp_apply] using hx
  have : q x = 1 := by
    simpa [hkerρ', Subgroup.mem_bot] using hx'
  -- If `q x = 1`, then `x ∈ ker q = R`.
  have hxR : x ∈ q.ker := by simpa [MonoidHom.mem_ker] using this
  simpa [hq, R] using hxR

/-!
### (3) Add a generator
-/

/--
Tietze (3): Add a new generator `none` and a defining relation `none = w`.
-/
def addGenerator (P : Presentation G ι) (w : FreeGroup ι) :
    Presentation G ι' where
  val := Option.rec (FreeGroup.lift P.val w) P.val
  closure_range_val := by
    -- The range of `P.val` embeds via `Option.some`, so its closure is still `⊤`.
    have hsubset :
        Set.range P.val ⊆ Set.range (Option.rec (FreeGroup.lift P.val w) P.val) := by
      intro g hg
      rcases hg with ⟨i, rfl⟩
      exact ⟨some i, rfl⟩
    have hmono := Subgroup.closure_mono hsubset
    simpa [P.closure_range_val] using hmono
  rels := (FreeGroup.map old) '' P.rels ∪
          {FreeGroup.of newGen * (FreeGroup.map old w)⁻¹}
  ker_eq_normalClosure := by
    -- abbreviations
    let φ : FreeGroup ι →* G := FreeGroup.lift P.val
    let ψ : FreeGroup ι' →* G :=
      FreeGroup.lift (Option.rec (φ w) P.val)
    let ρ : FreeGroup ι' →* FreeGroup ι :=
      FreeGroup.lift (Option.rec w FreeGroup.of)
    let s : FreeGroup ι →* FreeGroup ι' := FreeGroup.map old
    have hcomp : ψ = φ.comp ρ := by
      ext t ; cases t <;> simp [ψ, φ, ρ]
    have hcompρ : ρ.comp s = MonoidHom.id _ := by
      ext i; simp [ρ, s]
    have hψs : ψ.comp s = φ := by
      ext i; simp [ψ, φ, s]
    have hkerρ :
        ρ.ker =
          Subgroup.normalClosure
            ({FreeGroup.of newGen * (s w)⁻¹} :
              Set (FreeGroup ι')) :=
      ker_lift_option_eq_normalClosure_defined (ι := ι) (w := w)
    let relsNew :
        Set (FreeGroup ι') :=
      s '' P.rels ∪ {FreeGroup.of newGen * (s w)⁻¹}
    -- First inclusion: `ker ψ ≤ normalClosure relsNew`
    refine le_antisymm ?_ ?_
    · intro x hx
      have hxψ : ψ x = 1 := by simpa [MonoidHom.mem_ker] using hx
      have hxρ : ρ x ∈ Subgroup.normalClosure P.rels := by
        have hφ : φ (ρ x) = 1 := by simpa [hcomp] using hxψ
        have : ρ x ∈ φ.ker := by simpa [MonoidHom.mem_ker] using hφ
        simpa [φ, P.ker_eq_normalClosure] using this
      -- map old relators
      have hmap_le :
          (Subgroup.normalClosure P.rels).map s ≤
            Subgroup.normalClosure (s '' P.rels) := by
        refine Subgroup.map_le_iff_le_comap.mpr ?_
        refine Subgroup.normalClosure_le_normal ?_
        intro r hr
        change s r ∈ Subgroup.normalClosure (s '' P.rels)
        exact Subgroup.subset_normalClosure (Set.mem_image_of_mem _ hr)
      have hx_old :
          s (ρ x) ∈ Subgroup.normalClosure (s '' P.rels) := by
        have hxρmap :
            s (ρ x) ∈ (Subgroup.normalClosure P.rels).map s :=
          ⟨ρ x, hxρ, rfl⟩
        exact hmap_le hxρmap
      -- new relator from kernel of `ρ`
      have hx_rel :
          x * (s (ρ x))⁻¹ ∈
            Subgroup.normalClosure ({FreeGroup.of newGen * (s w)⁻¹} :
              Set (FreeGroup ι')) := by
        have hxkerρ : x * (s (ρ x))⁻¹ ∈ ρ.ker := by
          have hmap : ρ (s (ρ x)) = ρ x := by
            have := congrArg (fun f => f (ρ x)) hcompρ
            simpa [MonoidHom.comp_apply] using this
          have : ρ (x * (s (ρ x))⁻¹) = (1 : FreeGroup ι) := by
            simp [MonoidHom.map_mul, hmap]
          simpa [MonoidHom.mem_ker] using this
        simpa [hkerρ] using hxkerρ
      -- assemble memberships in the target normal closure
      have hx_old' : s (ρ x) ∈ Subgroup.normalClosure relsNew :=
        Subgroup.normalClosure_mono (by intro r hr; exact Or.inl hr) hx_old
      have hx_rel' :
          x * (s (ρ x))⁻¹ ∈ Subgroup.normalClosure relsNew :=
        Subgroup.normalClosure_mono (by intro r hr; exact Or.inr hr) hx_rel
      have hx_eq : x = x * (s (ρ x))⁻¹ * s (ρ x) := by
        have : (s (ρ x))⁻¹ * s (ρ x) = (1 : FreeGroup ι') := by simp
        calc
          x = x * 1 := by simp
          _ = x * ((s (ρ x))⁻¹ * s (ρ x)) := by simp [this]
          _ = x * (s (ρ x))⁻¹ * s (ρ x) := by simp [mul_assoc]
      have hxN :
          x * (s (ρ x))⁻¹ * s (ρ x) ∈ Subgroup.normalClosure relsNew :=
        Subgroup.mul_mem _ hx_rel' hx_old'
      have hxN' : x ∈ Subgroup.normalClosure relsNew := by
        refine hx_eq ▸ ?_
        simpa using hxN
      exact hxN'
    · -- Reverse inclusion: relators map to `1`, and the kernel is normal.
      refine
        Subgroup.normalClosure_le_normal
          (s := relsNew) (N := ψ.ker) ?_
      intro r hr
      rcases hr with hr | hr
      · -- old relators
        rcases hr with ⟨u, hu, rfl⟩
        have hφu : φ u = 1 := by
          have : u ∈ φ.ker := by
            have : u ∈ Subgroup.normalClosure P.rels :=
              Subgroup.subset_normalClosure hu
            simpa [φ, P.ker_eq_normalClosure] using this
          simpa [MonoidHom.mem_ker] using this
        have hcomp' := congrArg (fun f => f u) hψs
        have hψu : ψ (s u) = 1 := hcomp'.trans hφu
        simpa [MonoidHom.mem_ker] using hψu
      · -- defining relator
        rcases Set.mem_singleton_iff.mp hr with rfl
        have hψnone : ψ (FreeGroup.of newGen) = φ w := by simp [ψ, φ]
        have hψsw : ψ (s w) = φ w := by
          have hcomp' := congrArg (fun f => f w) hψs
          simpa [MonoidHom.comp_apply] using hcomp'
        have : ψ (FreeGroup.of newGen * (s w)⁻¹) = 1 := by
          calc
            ψ (FreeGroup.of newGen * (s w)⁻¹)
                = ψ (FreeGroup.of newGen) * (ψ (s w))⁻¹ := by
                  simp [MonoidHom.map_mul, MonoidHom.map_inv]
            _ = φ w * (φ w)⁻¹ := by
                  simp [hψnone, hψsw]
            _ = 1 := by simp
        simpa [MonoidHom.mem_ker] using this

noncomputable def addGeneratorEquiv (P : Presentation G ι) (w : FreeGroup ι) :
    P.presentedGroup ≃* (addGenerator P w).presentedGroup :=
  Presentation.equivPresentedGroups P (addGenerator P w)

/-!
### (4) Remove a generator
-/

/-- Helper for Tietze (4): substitute `none` with `w`. -/
def substitute (w : FreeGroup ι) : FreeGroup ι' →* FreeGroup ι :=
  FreeGroup.lift (Option.rec w FreeGroup.of)

/--
Tietze (4): Remove a generator `none` if `none = w` is a relation.
-/
def removeGenerator (P : Presentation G ι') (w : FreeGroup ι)
    (h_rel : FreeGroup.of newGen * (FreeGroup.map old w)⁻¹ ∈ P.rels) :
    Presentation G ι where
  val := P.val ∘ old
  closure_range_val := by
    sorry
  rels := (substitute w) '' P.rels
  ker_eq_normalClosure := by
    sorry

noncomputable def removeGeneratorEquiv (P : Presentation G ι') (w : FreeGroup ι)
    (h_rel : FreeGroup.of newGen * (FreeGroup.map old w)⁻¹ ∈ P.rels) :
    P.presentedGroup ≃* (removeGenerator P w h_rel).presentedGroup :=
  Presentation.equivPresentedGroups P (removeGenerator P w h_rel)

end Tietze

end Group
