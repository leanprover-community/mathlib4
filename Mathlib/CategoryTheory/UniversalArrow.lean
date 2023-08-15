import Mathlib.CategoryTheory.StructuredArrow

namespace CategoryTheory

open Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {c : C} {G : D ⥤ C}

/-- A universal arrow `t` consists of a family of morphisms
`t.desc : ∀ s : StructuredArrow c G, t.right ⟶ s.right` together with the
fact that such a family of morphisms is unique.-/
abbrev StructuredArrow.IsUniversal (s : StructuredArrow c G) := Limits.IsInitial s

abbrev CostructuredArrow.IsUniversal (s : CostructuredArrow G c) := Limits.IsTerminal s

namespace StructuredArrow.IsUniversal
variable {s t : StructuredArrow c G}

-- Todo: put this in the `IsColimit` file
/-- The underlying morphisms out of a left Kan extension. -/
theorem uniq (h : IsUniversal t) {s : StructuredArrow c G} (f : t ⟶ s) : f = h.to s :=
  h.hom_ext f (h.to s)

/-- The family of morphisms out of a universal arrow. -/
def desc (h : IsUniversal t) (s : StructuredArrow c G) : t.right ⟶ s.right :=
  (h.to s).right

@[reassoc (attr := simp)]
theorem fac (h : IsUniversal t) (s : StructuredArrow c G) :
    t.hom ≫ G.map (h.desc s) = s.hom :=
  Category.id_comp s.hom ▸ (h.to s).w.symm

theorem hom_desc (h : IsUniversal t) {d : D} (f : t.right ⟶ d) :
    f = h.desc (mk <| t.hom ≫ G.map f) :=
  let s := mk <| t.hom ≫ G.map f
  congrArg CommaMorphism.right (h.hom_ext (homMk f rfl : t ⟶ s) (h.to s))

/-- Two morphisms out of an universal arrow are equal if their compositions with
  each unit morphism are equal. -/
theorem hom_ext (h : IsUniversal t) {d : D} {f f' : t.right ⟶ d}
    (w : t.hom ≫ G.map f = t.hom ≫ G.map f') : f = f' := by
  rw [h.hom_desc f, h.hom_desc f', w]

theorem existsUnique (h : IsUniversal t) (s : StructuredArrow c G) :
    ∃! f : t.right ⟶ s.right, t.hom ≫ G.map f = s.hom :=
  ⟨h.desc s, h.fac s, fun f w ↦ h.hom_ext <| by simp [w]⟩

end StructuredArrow.IsUniversal

namespace CostructuredArrow.IsUniversal

variable {s t : CostructuredArrow G c}

/-- The underlying morphisms out of a left Kan extension. -/
theorem uniq (h : IsUniversal t) {s : CostructuredArrow G c} (f : s ⟶ t) : f = h.from s :=
  h.hom_ext f (h.from s)

/-- The family of morphisms out of a universal arrow. -/
def desc (h : IsUniversal t) (s : CostructuredArrow G c) : s.left ⟶ t.left :=
  (h.from s).left

@[reassoc (attr := simp)]
theorem fac (h : IsUniversal t) (s : CostructuredArrow G c) :
    G.map (h.desc s) ≫ t.hom = s.hom :=
  (Category.comp_id s.hom) ▸ (h.from s).w

theorem hom_desc (h : IsUniversal t) {d : D} (f : d ⟶ t.left) :
    f = h.desc (mk <| G.map f ≫ t.hom) :=
  let s := mk <| G.map f ≫ t.hom
  congrArg CommaMorphism.left (h.hom_ext (homMk f rfl : s ⟶ t) (h.from s))

/-- Two morphisms out of an universal arrow are equal if their compositions with
  each counit morphism are equal. -/
theorem hom_ext (h : IsUniversal t) {d : D} {f f' : d ⟶ t.left}
    (w : G.map f ≫ t.hom = G.map f' ≫ t.hom) : f = f' := by
  rw [h.hom_desc f, h.hom_desc f', w]

theorem existsUnique (h : IsUniversal t) (s : CostructuredArrow G c) :
    ∃! f : s.left ⟶ t.left, G.map f ≫ t.hom = s.hom :=
  ⟨h.desc s, h.fac s, fun f w ↦ h.hom_ext <| by simp [w]⟩

end CostructuredArrow.IsUniversal
end CategoryTheory
