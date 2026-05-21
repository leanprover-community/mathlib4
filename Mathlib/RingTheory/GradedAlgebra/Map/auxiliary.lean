module

public import Mathlib.Algebra.Ring.Submonoid.Pointwise
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Ring.Submonoid.Pointwise
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

section CongrLeft -- DONE
namespace DirectSum

open Function

universe u v w u₁

variable {ι : Type v} {β : ι → Type w} [∀ i, AddCommMonoid (β i)] {κ : Type*}
@[simp]
theorem equivCongrLeft_of -- DONE
    [DecidableEq ι] [DecidableEq κ] (h : ι ≃ κ) (k : κ) (x : β (h.symm k)) :
    equivCongrLeft h (of β (h.symm k) x) = of (fun k ↦ β (h.symm k)) k x
  := DFinsupp.comapDomain'_single (⇑h.symm) h.right_inv _ _

def equivCongrLeft' -- DONE
  (h : κ ≃ ι) : (⨁ i, β i) ≃+ ⨁ i, β (h i) :=
  { DFinsupp.equivCongrLeft h.symm with map_add' := DFinsupp.comapDomain'_add _ h.left_inv }

@[simp]
theorem equivCongrLeft'_apply -- DONE
  (h : κ ≃ ι) (f : ⨁ i, β i) (k : κ) :
    equivCongrLeft' h f k = f (h k) :=
  DFinsupp.comapDomain'_apply _ h.left_inv _ _

@[simp]
theorem equivCongrLeft'_of -- DONE
    [DecidableEq ι] [DecidableEq κ] (h : κ ≃ ι) (k : κ) (m : β (h k)) :
    equivCongrLeft' h (of β (h k) m) = of (fun k ↦ β (h k)) k m
  := DFinsupp.comapDomain'_single _ h.left_inv' _ _

end DirectSum
end CongrLeft


section Sigma -- DONE
namespace DirectSum

open Function

universe u v w u₁

variable {ι : Type v} {β : ι → Type w} [∀ i, AddCommMonoid (β i)] [DecidableEq ι] {α : ι → Type u}
  {δ : ∀ i, α i → Type w} [∀ i j, AddCommMonoid (δ i j)]

theorem sigmaCurry_of [∀ i : ι, DecidableEq (α i)] (k : (i : ι) × α i)(x : δ k.1 k.2) :
    sigmaCurry (of (fun k ↦ δ k.1 k.2) k x) =
    of (fun i' ↦ ⨁ (j' : α i'), δ i' j') k.1 (of (fun j' ↦ δ k.1 j') k.2 x) := by
  exact DFinsupp.sigmaCurry_single k x

/-
theorem sigmaCurry_of [∀ i : ι, DecidableEq (α i)] (i : ι) (j : α i) (m : δ i j) :
    (sigmaCurry) ((of (fun (k : (i' : ι) × α i') ↦ δ k.1 k.2) ⟨i,j⟩ ) m)
    = (of (fun i' ↦ ⨁ (j' : α i'), δ i' j') i) ((of (fun j' ↦ δ i j') j ) m)
  := by
  exact DFinsupp.sigmaCurry_single ⟨i,j⟩ m
-/
end DirectSum
end Sigma




/-
1. Definition of `sigmaFiberAddEquiv`< :
   as composition of two isos:
     iso₁ :=  lequivCongrLeft
     iso₂ := sigmaLcurryEquiv
   Each of (iso₁) and (iso₂) are defined in Mathlib,
   and we prove an …_of lemma for each of these.
2. `sigmaFiberLinearAdd_of` lemma, proved from the …_of lemmas for iso₁ and iso₂.
   This is all still very messy and probably not done the correct way.
-/
section SigmaFiber
namespace DirectSum
open Function
universe v w
variable {ι₁ ι₂ : Type v} [DecidableEq ι₂] (f : ι₁ → ι₂)
variable {β : ι₁ → Type w} [∀ i : ι₁, AddCommMonoid (β i)]

/-- The equivalence between a direct sum indexed by a type `ι₁` and the
    double sum indexed by a type `ι₂` and the fibres of a map `f : ι₁ → ι₂`. -/
def sigmaFiberAddEquiv [DecidableEq ι₂] :
    (⨁ i, β i) ≃+ ⨁ (j : ι₂) (i : { i : ι₁ // f i = j}), β ↑i :=
  (equivCongrLeft' (Equiv.sigmaFiberEquiv f)).trans
    (sigmaCurryEquiv (δ := fun j ↦ (fun (i : { i : ι₁ // f i = j}) ↦ β i)))

theorem sigmaFiberAddEquiv_apply' (x : ⨁ i, β i) :
    sigmaFiberAddEquiv f x = sigmaCurry (equivCongrLeft' (Equiv.sigmaFiberEquiv f) x) := by
  simp only [DirectSum.sigmaFiberAddEquiv,AddEquiv.trans_apply]
  rfl

@[simp]
theorem sigmaFiberAddEquiv_apply (x : ⨁ i, β i) (j : ι₂) (i' : { i : ι₁ // f i = j}) :
    sigmaFiberAddEquiv f x j i'=  x i' := by
  rw [DirectSum.sigmaFiberAddEquiv_apply']
  rfl

@[simp]
theorem sigmaFiberAddEquiv_of [DecidableEq ι₁] (i : ι₁) (x : β i) :
  sigmaFiberAddEquiv f (of _ i x) = of _ (f i) (of _ ⟨i, rfl⟩ x) := by
  let h := Equiv.sigmaFiberEquiv f
  let k : (j : ι₂) × {i₁ : ι₁ // f i₁ = j} := ⟨f i, ⟨i, rfl⟩⟩
  calc sigmaFiberAddEquiv f (of β (h k) x)
  _ = sigmaCurry (of (fun k : (j' : ι₂) × {i // f i = j'} ↦ β (h k)) k x) := by
      simp only [sigmaFiberAddEquiv_apply',h,equivCongrLeft'_of]
  _ = sigmaCurry (of (fun k : (j' : ι₂) × {i // f i = j'} ↦ β k.2) k x) := by
      rfl
  _ = of _ k.1 (of _ k.2 x) := by
      simp only [sigmaCurry_of]
/-
  -- Alternative proof using `sigmaFiberAddEquiv_apply` instead of `sigmaFiberAddEquiv_apply'`:
  ext j' i'
  simp only [sigmaFiberAddEquiv_apply,of_apply]
  split_ifs with hi hj hj'
  · subst hj
    have : i' = ⟨i, rfl⟩ := by grind
    subst this
    rw [of_eq_same]
  · have : f i = j' := by grind
    contradiction
  · subst hj'
    rw [of_eq_of_ne]
    grind
  · rfl
-/
end DirectSum
end SigmaFiber


open Pointwise in
/-- A lemma that exists for `Submodule`s in Mathlib but not for `AddSubmonoid`s: -/
lemma AddSubmonoid.one_le {A : Type*} [AddMonoidWithOne A] {P : AddSubmonoid A} :
  (1 : AddSubmonoid A) ≤ P ↔ (1 : A) ∈ P := by
  rw [AddSubmonoid.one_eq_closure, AddSubmonoid.closure_le, Set.singleton_subset_iff]
  rfl

/- An analogue of Mathlib's `Submodule.iSup_toAddSubmonoid` --/
theorem Subgroup.iSup_toAddSubmonoid {ι M : Type*} [AddCommGroup M]
  (p : ι → AddSubgroup M) :
  (⨆ i, p i).toAddSubmonoid = ⨆ i, (p i).toAddSubmonoid
  := by
  refine le_antisymm
    (fun x hx ↦ ?_)
    (iSup_le fun i x hx ↦ (le_iSup p i) hx)
  -- Now induct on x ∈ ⨆ i, f i.
  induction hx using AddSubgroup.iSup_induction' with
  | hp i y hy           => exact AddSubmonoid.mem_iSup_of_mem i hy
  | h1                  => exact zero_mem _
  | hadd y z _ _ hy hz  => exact add_mem hy hz

@[simp]
/- An analogue of Mathlib's `Submodule.toAddSubmonoid_sSup` --/
theorem Subgroup.toAddSubmonoid_sSup {M : Type*} [AddCommGroup M]
  (s : Set (AddSubgroup M)) :
  (sSup s).toAddSubmonoid = sSup (AddSubgroup.toAddSubmonoid '' s)
  := by
    rw [sSup_image',sSup_eq_iSup']
    exact (Subgroup.iSup_toAddSubmonoid _)

-- #check Submodule.toAddSubmonoid_sSup -- simp lemma
-- #check Submodule.iSup_toAddSubmonoid -- not a simp lemma
