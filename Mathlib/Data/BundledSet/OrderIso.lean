import Mathlib.Data.BundledSet.Weaken
import Mathlib.Data.BundledSet.CompleteLattice.Basic
import Mathlib.Logic.Equiv.Set
import Mathlib.Order.Hom.Basic

open BundledSet

/-- `BundledSet.weaken` as an `OrderEmbedding`. -/
@[simps! (config := .asFn) apply]
def BundledSet.weakenEmbedding (α : Type*) (p q : Set α → Prop) [Implies p q] :
    BundledSet α p ↪o BundledSet α q := 
  .ofMapLEIff weaken fun _ _ ↦ .rfl

namespace Equiv

variable {α β : Type*}

@[simps! apply_carrier]
def bundledSetCongr (e : α ≃ β) (p : Set α → Prop) (q : Set β → Prop)
    (h : ∀ t, p (e ⁻¹' t) ↔ q t) : BundledSet α p ≃o BundledSet β q where
  toFun s := ⟨e.symm ⁻¹' s, by rw [← h, e.preimage_symm_preimage]; exact s.2⟩
  invFun t := ⟨e ⁻¹' t, (h t).2 t.2⟩
  left_inv s := carrier_injective <| e.preimage_symm_preimage s
  right_inv t := carrier_injective <| e.symm_preimage_preimage t
  map_rel_iff' := e.symm.preimage_subset _ _

variable {e : α ≃ β} {p : Set α → Prop} {q : Set β → Prop} (h : ∀ t, p (e ⁻¹' t) ↔ q t)

@[simp]
lemma bundledSetCongr_symm :
    (bundledSetCongr e p q h).symm = e.symm.bundledSetCongr q p fun s ↦
      by rw [← h, e.preimage_symm_preimage] := rfl

lemma bundledSetCongr_symm_apply_carrier (t : BundledSet β q) :
    ((bundledSetCongr e p q h).symm t).1 = e ⁻¹' t := rfl

@[simp]
lemma mem_bundledSetCongr_apply {s : BundledSet α p} {y : β} :
    y ∈ e.bundledSetCongr p q h s ↔ e.symm y ∈ s := .rfl

lemma mem_bundledSetCongr_symm_apply {t : BundledSet β q} {x : α} :
    x ∈ (e.bundledSetCongr p q h).symm t ↔ e x ∈ t := .rfl

@[simp]
lemma bundledSetCongr_closure [SetInterPred α p] [SetInterPred β q] (s : Set α) :
    bundledSetCongr e p q h (.closure p s) = .closure q (e.symm ⁻¹' s) :=
  eq_of_forall_ge_iff fun _ ↦ by simp [← OrderIso.le_symm_apply, ← e.image_eq_preimage]

lemma bundledSetCongr_symm_closure [SetInterPred α p] [SetInterPred β q] (s : Set β) :
    (bundledSetCongr e p q h).symm (.closure q s) = .closure p (e ⁻¹' s) := by simp
