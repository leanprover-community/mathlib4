import Mathlib.ModelTheory.Field.CharP
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.FreeCommRing

namespace FirstOrder

namespace Language

variable {K : Type _} [Field K]

/-- We make the `FreeCommRing` a Structure for the language of fields by
sending `inv` to the identity. -/
def fieldStructureFreeCommRing (α : Type _) :

theorem exists_term_realize_eq_freeCommRing_lift (p : FreeCommRing α) :
    ∃ t : Language.field.Term α, ∀ v : α → K, (t.realize v : K) =
      FreeCommRing.lift v p :=
  FreeCommRing.induction_on p
    ⟨-1, fun v => by simp [Term.realize]⟩
    (fun a => ⟨Term.var a, by simp [Term.realize]⟩)
    (fun x y ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ =>
      ⟨t₁ + t₂, by simp_all [Term.realize]⟩)
    (fun x y ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ =>
      ⟨t₁ * t₂, by simp_all [Term.realize]⟩)

-- def termOfFreeCommRing (p : FreeCommRing α) : Language.field.Term α :=
--   Classical.choose (exists_term_realize_eq_freeCommRing_lift p)

end Language

end FirstOrder
