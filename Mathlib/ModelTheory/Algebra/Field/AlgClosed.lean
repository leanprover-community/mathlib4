import Mathlib.ModelTheory.Algebra.Field.CharP
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.FreeCommRing

namespace FirstOrder

namespace Language

variable {K : Type _} [Field K]

/-- We make the `FreeCommRing` a Structure for the language of fields by
sending `inv` to the identity. -/
@[simp]
def fieldStructureFreeCommRing (α : Type _) :
    Language.field.Structure (FreeCommRing α) :=
  { RelMap := Empty.elim,
    funMap := fun {n} f =>
      match n, f with
      | _, .add => fun x => x 0 + x 1
      | _, .mul => fun x => x 0 * x 1
      | _, .neg => fun x => - x 0
      | _, .inv => fun x => x 0
      | _, .zero => fun _ => 0
      | _, .one => fun _ => 1 }

section

attribute [local instance] fieldStructureFreeCommRing

theorem exists_term_realize_eq_freeCommRing (p : FreeCommRing α) :
    ∃ t : Language.field.Term α,
      (t.realize FreeCommRing.of : FreeCommRing α) = p :=
  FreeCommRing.induction_on p
    ⟨-1, by simp [Term.realize]⟩
    (fun a => ⟨Term.var a, by simp [Term.realize]⟩)
    (fun x y ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ =>
      ⟨t₁ + t₂, by simp_all [Term.realize]⟩)
    (fun x y ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ =>
      ⟨t₁ * t₂, by simp_all [Term.realize]⟩)
#print Term
noncomputable def termOfFreeCommRing (p : FreeCommRing α) : Language.field.Term α :=
  Classical.choose (exists_term_realize_eq_freeCommRing p)

theorem realize_termOfFreeCommRing (p : FreeCommRing α) (v : α → K) :
    (termOfFreeCommRing p).realize v = FreeCommRing.lift v p := by
  have : (termOfFreeCommRing p).realize FreeCommRing.of = p :=
    Classical.choose_spec (exists_term_realize_eq_freeCommRing p)
  conv_rhs => rw [← this]
  induction termOfFreeCommRing p with
  | var _ => simp
  | func f _ ih =>
    cases f
    case inv => simp_all [ih 0]




end

end Language

end FirstOrder
