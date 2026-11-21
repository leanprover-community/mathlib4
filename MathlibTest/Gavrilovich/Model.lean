import Mathlib.Tactic.Gavrilovich

open Gavrilovich CategoryTheory TopCat

/-! ### `Prop` -/

/-- info: Model.instPropStringConsListNilProdNatMkOfNat -/
#guard_msgs in #synth Model Prop _ _

example : (pt(T) : Prop) = True := rfl
example : (pt(F) : Prop) = False := rfl

example : Model.homeo True = (pt(T) : ⌜T → F⌟) := by simp
example : Model.homeo False = (pt(F) : ⌜T → F⌟) := by simp
example : (Model.homeo (X := Prop)).symm pt(T) = True := by simp
example (p : Prop) : (Model.homeo (X := Prop)).symm (Model.homeo p) = p := by simp

example (p : Prop → Prop) : (∀ q : Prop, p q) ↔ p False ∧ p True := by simp [Model.forallPts]
example (p : Prop → Prop) : (∃ q : Prop, p q) ↔ p False ∨ p True := by simp [Model.existsPts]

/-! ### Morphisms to and from models -/

/-- The map from `Prop` to the point. -/
noncomputable def toPt : of Prop ⟶ of PUnit := ⌜T → F⌟ ⇢ ⌜T=F⌟

example : toPt True = PUnit.unit := by simp [toPt]

/-- The identity of `Prop`, drawn. -/
noncomputable def idProp : of Prop ⟶ of Prop := ⌜T → F⌟ ⇢ ⌜T → F⌟

example : idProp True = True := by simp [idProp]
example : idProp False = False := by simp [idProp]

/-- The open point of `⌜a → b⌟`, as a map to `Prop`. -/
noncomputable def isA : ⌜a → b⌟ ⟶ of Prop := ⌜a → b⌟ ⇢ ⌜a(=T) → b(=F)⌟

example : isA pt(a) = True := by simp [isA]
example : isA pt(b) = False := by simp [isA]

/-- A map out of `Prop`, relabelled to names local to the morphism. -/
noncomputable def fromProp : of Prop ⟶ ⌜x → y⌟ := ⌜x(=T) → y(=F)⌟ ⇢ ⌜x → y⌟

example : fromProp True = pt(x) := by simp [fromProp]

/-- error: not continuous: F → T in the source, but no F → T in the target -/
#guard_msgs (error, drop warning) in
noncomputable example : of Prop ⟶ of Prop := ⌜T ← F⌟ ⇢ ⌜T → F⌟

/-! ### `ULift` and `PUnit` -/

example : (pt(T) : ULift.{1} Prop) = ⟨True⟩ := rfl
example : Model.homeo (ULift.up.{1} False) = (pt(F) : ⌜T → F⌟) := by simp
example : (pt("*") : PUnit.{1}) = PUnit.unit := rfl

/-! ### A computable model -/

/-- Three points, with `l` and `r` specializing to `z`. -/
inductive Three | l | z | r
  deriving DecidableEq

namespace Three

instance : Fintype Three where
  elems := {l, z, r}
  complete x := by cases x <;> decide

instance : Preorder Three where
  le a b := a = b ∨ a = z
  le_refl _ := .inl rfl
  le_trans a b c := by rintro (rfl | rfl) (rfl | rfl) <;> simp

instance : DecidableLE Three := fun a b => inferInstanceAs (Decidable (a = b ∨ a = z))
instance : TopologicalSpace Three := Topology.upperSet Three
instance : Topology.IsUpperSet Three := ⟨rfl⟩

instance : Model Three [["l"], ["r"], ["z"]] [(0, 2), (1, 2)] :=
  .ofList [l, r, z] rfl (by decide) (by decide)
    (by simp only [Topology.IsUpperSet.specializes_iff_le]; decide)

end Three

example : ⌜l → z ← r⌟ = Space [["l"], ["r"], ["z"]] [(0, 2), (1, 2)] := rfl

example : (pt(r) : Three) = .r := rfl
example : Model.homeo Three.z = (pt(z) : ⌜l → z ← r⌟) := by simp

/-- The constant map at `z`. (The points of the target box other than `z` are left unnamed by the
map, so it doesn't matter how they are relabelled.) -/
def constZ : of Three ⟶ of Three := ⌜l → z ← r⌟ ⇢ ⌜x → l=r=z(=z) ← y⌟

example : constZ .l = .z := by simp [constZ]
example : constZ ≫ constZ = constZ := by decide
example : constZ ≠ 𝟙 _ := by decide
example : Fintype.card (of Three ⟶ of PUnit) = 1 := by decide
example : Fintype.card (of Three ⟶ of Three) = 11 := by decide

/-- The open points of `Three`, as a map to `Prop`. -/
noncomputable def isOpenPt : of Three ⟶ of Prop := ⌜l → z ← r⌟ ⇢ ⌜l=r(=T) → z(=F)⌟

example : isOpenPt .r = True := by simp [isOpenPt]
example : ∀ x : Three, isOpenPt x ↔ x ≠ .z := by simp [Model.forallPts, isOpenPt]

/-! ### Errors -/

/-- error: no point named 'Q' in this space (its points are F, T) -/
#guard_msgs in
example : (pt(Q) : Prop) = True := rfl

/--
error: this box doesn't have the shape of
  ↧Prop
so the morphism can't be relabelled to have type
  ↧Prop ⟶ ↧Prop
-/
#guard_msgs in
noncomputable example : of Prop ⟶ of Prop := ⌜a → b → c⌟ ⇢ ⌜a=b=c⌟
