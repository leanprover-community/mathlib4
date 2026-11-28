/-
Copyright (c) 2026 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
module

public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Data.FinEnum
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Automorphisms acting on morphisms, and enumerating them

* `(Aut X)ᵐᵒᵖ` and `Aut Y` act on `X ⟶ Y` by pre- and postcomposition (as `(End X)ᵐᵒᵖ` and
  `End Y` do), and so does their product.
* When `X ⟶ X` is a `FinEnum`, so are `Aut X` and `(Aut X)ᵐᵒᵖ` (and they are `Fintype`s). The
  automorphisms are listed by `Aut.list`, which looks for the inverse of each endomorphism `f`
  among its powers (`Aut.powInv?`), stopping at the first idempotent: this takes as many steps as
  the powers of `f` take to cycle, rather than a search through all of `X ⟶ X`, and keeps the
  enumeration cheap to evaluate by `decide`.
-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C] (X Y : C)

instance autMulActionLeft : MulAction (Aut X)ᵐᵒᵖ (X ⟶ Y) where
  smul α₁ φ := α₁.unop.asIso.hom ≫ φ
  mul_smul := by simp [HSMul.hSMul]
  one_smul := by simp [HSMul.hSMul]

@[simp] lemma aut_left_smul_def (α : (Aut X)ᵐᵒᵖ) (φ : X ⟶ Y) :
    α • φ = α.unop.asIso.hom ≫ φ := rfl

instance autMulActionRight : MulAction (Aut Y) (X ⟶ Y) where
  smul α₂ φ := φ ≫ α₂.asIso.hom
  mul_smul := by simp [HSMul.hSMul]
  one_smul := by simp [HSMul.hSMul]

@[simp] lemma aut_right_smul_def (α : Aut Y) (φ : X ⟶ Y) :
    α • φ = φ ≫ α.asIso.hom := rfl

instance : SMulCommClass (Aut X)ᵐᵒᵖ (Aut Y) (X ⟶ Y) where
  smul_comm α₁ α₂ φ := by simp

instance autMulAction : MulAction ((Aut X)ᵐᵒᵖ × Aut Y) (X ⟶ Y) := .prodOfSMulCommClass ..

@[simp]
lemma aut_smul_def (α : (Aut X)ᵐᵒᵖ × Aut Y) (φ : X ⟶ Y) :
    α • φ = α.1.unop.asIso.hom ≫ φ ≫ α.2.asIso.hom := rfl

namespace Aut

instance [DecidableEq (X ⟶ X)] : DecidableEq (Aut X) :=
  fun φ ψ ↦ decidable_of_iff (φ.asIso.hom = ψ.asIso.hom) (by simp [Aut.ext_iff, Iso.ext_iff])


lemma pow_succ_asIso_hom (φ : Aut X) (j : ℕ) :
    (φ ^ (j + 1)).asIso.hom = φ.asIso.hom ≫ (φ ^ j).asIso.hom := by
  rw [pow_succ]; rfl

variable [FinEnum (X ⟶ X)]

/-- Searches the powers of `f` for `𝟙 X`, where `p = f ^ j` and `q = f ^ (j - 1)`, returning
`f ^ (j - 1)` (the inverse of `f`) if it finds it. It stops at an idempotent other than `𝟙 X`,
which no power of an isomorphism is, and as every power of `f` is eventually idempotent, this takes
only as many steps as the powers of `f` take to cycle. -/
def powInv? (f : X ⟶ X) : ℕ → (p q : X ⟶ X) → Option (X ⟶ X)
  | 0, _, _ => none
  | n + 1, p, q => if p = 𝟙 X then some q else if p ≫ p = p then none else powInv? f n (f ≫ p) p

/-- The automorphism with underlying morphism `f`, if `f` has an inverse. -/
def ofHom? (f : X ⟶ X) : Option (Aut X) :=
  match powInv? X f (FinEnum.card (X ⟶ X) + 1) f (𝟙 X) with
  | some g => if h : f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 X then some (of ⟨f, g, h.1, h.2⟩) else none
  | none => none

lemma asIso_hom_of_mem_ofHom? {f : X ⟶ X} {φ : Aut X} (h : φ ∈ ofHom? X f) :
    φ.asIso.hom = f := by
  unfold ofHom? at h
  split at h
  · split at h <;> cases h; rfl
  · cases h

lemma powInv?_pow (φ : Aut X) : ∀ (n j : ℕ), 1 ≤ j → j ≤ orderOf φ → orderOf φ - j < n →
    powInv? X φ.asIso.hom n (φ ^ j).asIso.hom (φ ^ (j - 1)).asIso.hom =
      some (φ ^ (orderOf φ - 1)).asIso.hom
  | 0, _, _, _, h => by omega
  | n + 1, j, hj, hk, h => by
    have hφ : (φ ^ j).asIso.hom = 𝟙 X ↔ j = orderOf φ := by
      rw [show (φ ^ j).asIso.hom = 𝟙 X ↔ φ ^ j = 1 by rw [Aut.ext_iff, Iso.ext_iff]; rfl,
        ← orderOf_dvd_iff_pow_eq_one]
      exact ⟨fun h ↦ Nat.le_antisymm hk (Nat.le_of_dvd (by omega) h), fun h ↦ h ▸ dvd_rfl⟩
    rw [powInv?]
    by_cases hjk : j = orderOf φ
    · subst hjk; simp
    have hp : ¬(φ ^ j).asIso.hom ≫ (φ ^ j).asIso.hom = (φ ^ j).asIso.hom := fun hp ↦
      hφ.not.2 hjk <| by simpa using (cancel_mono (φ ^ j).asIso.hom).1 (hp.trans (by simp))
    simp only [hφ, hjk, hp, ↓reduceIte]
    have := powInv?_pow φ n (j + 1) (by omega) (by omega) (by omega)
    rwa [pow_succ_asIso_hom, Nat.add_sub_cancel] at this

lemma ofHom?_asIso_hom (φ : Aut X) : ofHom? X φ.asIso.hom = some φ := by
  have hinj : Function.Injective fun φ : Aut X ↦ φ.asIso.hom := fun φ ψ h ↦ by
    ext1; exact Iso.ext h
  have : Finite (Aut X) := .of_injective _ hinj
  have hk := orderOf_pos φ
  have hcard : orderOf φ ≤ FinEnum.card (X ⟶ X) := by
    refine orderOf_le_card.trans ((Nat.card_le_card_of_injective _ hinj).trans ?_)
    rw [Nat.card_eq_fintype_card, FinEnum.card_eq_fintypeCard]
  have := powInv?_pow X φ (FinEnum.card (X ⟶ X) + 1) 1 le_rfl hk (by omega)
  rw [pow_one, Nat.sub_self, pow_zero] at this
  change powInv? X _ _ _ (𝟙 X) = _ at this
  rw [ofHom?, this]
  have h₁ : φ.asIso.hom ≫ (φ ^ (orderOf φ - 1)).asIso.hom = 𝟙 X := by
    rw [← pow_succ_asIso_hom, Nat.sub_add_cancel hk, pow_orderOf_eq_one]; rfl
  have h₂ : (φ ^ (orderOf φ - 1)).asIso.hom ≫ φ.asIso.hom = 𝟙 X := by
    rw [show _ ≫ _ = (φ * φ ^ (orderOf φ - 1)).asIso.hom from rfl, ← pow_succ',
      Nat.sub_add_cancel hk, pow_orderOf_eq_one]; rfl
  dsimp only
  rw [dite_eq_left_of_eq_true (eq_true ⟨h₁, h₂⟩)]
  congr 1; ext1; exact Iso.ext rfl

/-- The automorphisms of `X`, in the order of their underlying morphisms. -/
def list : List (Aut X) := (FinEnum.toList (X ⟶ X)).filterMap (ofHom? X)

lemma mem_list (φ : Aut X) : φ ∈ list X :=
  List.mem_filterMap.2 ⟨_, FinEnum.mem_toList _, ofHom?_asIso_hom X φ⟩

lemma nodup_list : (list X).Nodup :=
  FinEnum.nodup_toList.filterMap fun _ _ _ h h' ↦
    (asIso_hom_of_mem_ofHom? X h).symm.trans (asIso_hom_of_mem_ofHom? X h')

instance : Fintype (Aut X) := ⟨⟨list X, nodup_list X⟩, fun φ ↦ mem_list X φ⟩
instance : FinEnum (Aut X) := .ofNodupList (list X) (mem_list X) (nodup_list X)

instance : Fintype (Aut X)ᵐᵒᵖ :=
  ⟨⟨(list X).map MulOpposite.op, (nodup_list X).map MulOpposite.op_injective⟩,
    fun φ ↦ List.mem_map.2 ⟨φ.unop, mem_list X _, rfl⟩⟩
instance : FinEnum (Aut X)ᵐᵒᵖ :=
  .ofNodupList ((list X).map MulOpposite.op) (fun φ ↦ List.mem_map.2 ⟨φ.unop, mem_list X _, rfl⟩)
    ((nodup_list X).map MulOpposite.op_injective)

end Aut

end CategoryTheory
