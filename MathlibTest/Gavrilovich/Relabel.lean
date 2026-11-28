import Mathlib.Tactic.Gavrilovich
import Mathlib.CategoryTheory.LiftingProperties.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Tactic.ApplyFun

open Gavrilovich CategoryTheory Limits

universe u v

/-! ## `Space.relabel` -/

/-- info: Space.relabel : ⌜o → c⌟ ⟶ ⌜T → F⌟ -/
#guard_msgs in
#check (Space.relabel : ⌜o → c⌟ ⟶ ⌜T → F⌟)

-- the points are sorted by name, so the indices differ, but `relabel` follows the shape
example : (Space.relabel : ⌜a → b⌟ ⟶ ⌜T → F⌟) pt(a) = pt(T) := by simp
example : (Space.relabel : ⌜a → b ← c⌟ ⟶ ⌜x → y ← z⌟) pt(c) = pt(z) := by simp
example : (Space.relabelIso : ⌜a → b ← c⌟ ≅ ⌜x → y ← z⌟).inv pt(y) = pt(b) := by simp

-- points with the same names are kept, where possible
example : (Space.relabel : ⌜a  b⌟ ⟶ ⌜b  c⌟) pt(b) = pt(b) := by simp

-- like `eqToHom`
example : (Space.relabel : ⌜a → b⌟ ⟶ ⌜a → b⌟) = 𝟙 _ := by simp
example : (Space.relabel : ⌜a → b⌟ ⟶ ⌜x → y⌟) ≫ (Space.relabel : _ ⟶ ⌜p → q⌟) =
    Space.relabel := by simp
example : (Space.relabel : ⌜a → b⌟ ⟶ ⌜x → y⌟) ≫ Space.relabel = 𝟙 ⌜a → b⌟ := by simp
example {X : TopCat} (f : ⌜a → b⌟ ⟶ X) :
    (Space.relabel : ⌜x → y⌟ ⟶ ⌜p → q⌟) ≫ (Space.relabel : _ ⟶ ⌜a → b⌟) ≫ f =
      Space.relabel ≫ f := by
  simp
example : inv (Space.relabel : ⌜a → b⌟ ⟶ ⌜x → y⌟) = Space.relabel := by simp
example {X : TopCat} (f : ⌜a → b⌟ ⟶ X) :
    (Space.relabelIso : ⌜a → b⌟ ≅ ⌜x → y⌟).inv ≫ f = Space.relabel ≫ f := by
  simp
example {X : TopCat} (χ : ⌜T ↔ F⌟ ⟶ X) :
    ((Space.relabel : ⌜o ↔ c⌟ ⟶ _) ≫ χ) pt(o) = χ pt(T) := by
  simp

-- morphisms between spaces have decidable equality
example : Space.relabel ≫ (⌜T → F⌟ ⇢ ⌜T ↔ F⌟) = (⌜o → c⌟ ⇢ ⌜o ↔ c⌟) ≫ Space.relabel := by
  decide

/--
error: could not synthesize default value for parameter 'σ' using tactics
---
error: gav_relabel: the spaces
  ⌜a → b⌟
and
  ⌜F ↔ T⌟
aren't isomorphic
-/
#guard_msgs in
example : ⌜a → b⌟ ⟶ ⌜T ↔ F⌟ := Space.relabel

/-! ## Homeomorphisms, which can change universes -/

def h : (⌜a → b ← c⌟ : TopCat.{u}) ≃ₜ (⌜x → y ← z⌟ : TopCat.{v}) := Space.relabelHomeo
example : h pt(a) = pt(x) := by simp [h]
example : h.symm pt(z) = pt(c) := by simp [h]

/-! ## Isomorphisms given by bijections -/

def i : ⌜a  b⌟ ≅ ⌜T  F⌟ := Space.iso fun | pt(a) => pt(F) | pt(b) => pt(T)
example : i.hom pt(a) = pt(F) := by simp [i]
example : i.inv pt(F) = pt(a) := by simp [i]

def j : (⌜a → b⌟ : TopCat.{u}) ≃ₜ (⌜T → F⌟ : TopCat.{v}) :=
  Space.homeo fun | pt(a) => pt(T) | pt(b) => pt(F)
example : j pt(a) = pt(T) := by simp [j]
example : j.symm pt(F) = pt(b) := by simp [j]

-- an automorphism
def sw : ⌜a  b⌟ ≅ ⌜a  b⌟ := Space.iso fun | pt(a) => pt(b) | pt(b) => pt(a)
example : sw.hom ≫ sw.hom = 𝟙 _ := by simp [sw]

/--
error: could not synthesize default value for parameter 'σ' using tactics
---
error: gav_relabel_of: not injective: a and b both map to F
-/
#guard_msgs in
example : ⌜a  b⌟ ≅ ⌜T  F⌟ := Space.iso fun | pt(a) => pt(F) | pt(b) => pt(F)

/--
error: could not synthesize default value for parameter 'σ' using tactics
---
error: gav_relabel_of:
  fun x =>
    match x with
    | pt(a) => pt(F)
    | pt(b) => pt(T)
isn't continuous
-/
#guard_msgs in
example : ⌜a → b⌟ ≅ ⌜T  F⌟ := Space.iso fun | pt(a) => pt(F) | pt(b) => pt(T)

/--
error: could not synthesize default value for parameter 'σ' using tactics
---
error: gav_relabel_of: the inverse of
  fun x =>
    match x with
    | pt(a) => pt(F)
    | pt(b) => pt(T)
isn't continuous
-/
#guard_msgs in
example : ⌜a  b⌟ ≅ ⌜T → F⌟ := Space.iso fun | pt(a) => pt(F) | pt(b) => pt(T)

/-! ## Isomorphisms of arrows, and transporting lifting properties -/

example : Arrow.mk (⌜o → c⌟ ⇢ ⌜o ↔ c⌟) ≅ Arrow.mk (⌜T → F⌟ ⇢ ⌜T ↔ F⌟) := Space.arrowIso
-- this needs the right one of the two automorphisms of `⌜x  y⌟`
example : Arrow.mk (⌜a  b⌟ ⇢ ⌜a=b⌟) ≅ Arrow.mk (⌜x  y⌟ ⇢ ⌜x=y⌟) := Space.arrowIso
noncomputable example : Arrow.mk (terminal.from ⌜o ↔ c⌟) ≅ Arrow.mk (terminal.from ⌜T ↔ F⌟) :=
  Space.arrowIso

example {X : TopCat.{u}} : HasLiftingProperty (terminal.from.{u} ⌜o ↔ c⌟) (terminal.from X) ↔
    HasLiftingProperty (terminal.from.{u} ⌜T ↔ F⌟) (terminal.from X) :=
  HasLiftingProperty.iff_of_arrow_iso_left Space.arrowIso _

example {X : TopCat} [HasLiftingProperty (⌜o → c⌟ ⇢ ⌜o ↔ c⌟) (terminal.from X)] :
    HasLiftingProperty (⌜T → F⌟ ⇢ ⌜T ↔ F⌟) (terminal.from X) :=
  .of_arrow_iso_left (i := ⌜o → c⌟ ⇢ ⌜o ↔ c⌟) Space.arrowIso _

/--
error: could not synthesize default value for parameter 'e' using tactics
---
error: gav_arrow_iso: ⌜o → c⌟ and ⌜F ↔ T⌟ aren't isomorphic
-/
#guard_msgs in
example : Arrow.mk (⌜o → c⌟ ⇢ ⌜o ↔ c⌟) ≅ Arrow.mk (⌜T ↔ F⌟ ⇢ ⌜T ↔ F⌟) := Space.arrowIso

/-! ## Choosing the relabelling: `relabel[x ↦ o, …]` -/

example : (relabel[a ↦ y, b ↦ x] : ⌜a  b⌟ ⟶ ⌜x  y⌟) pt(a) = pt(y) := by simp
-- the points not mentioned are chosen as by `Space.relabel`
example : (relabel[a ↦ y] : ⌜a  b⌟ ⟶ ⌜x  y⌟) pt(b) = pt(x) := by simp

/-- info: relabel[a ↦ y, b ↦ x] : ⌜a  b⌟ ⟶ ⌜x  y⌟ -/
#guard_msgs in
#check (relabel[a ↦ y] : ⌜a  b⌟ ⟶ ⌜x  y⌟)

-- the canonical relabelling is printed as plain `Space.relabel`
/-- info: Space.relabel : ⌜a  b⌟ ⟶ ⌜x  y⌟ -/
#guard_msgs in
#check (relabel[a ↦ x] : ⌜a  b⌟ ⟶ ⌜x  y⌟)

/-- info: relabelIso[a ↦ y, b ↦ x] : ⌜a  b⌟ ≅ ⌜x  y⌟ -/
#guard_msgs in
#check (relabelIso[a ↦ y] : ⌜a  b⌟ ≅ ⌜x  y⌟)

/-- info: relabelHomeo[a ↦ y, b ↦ x] : ⌜a  b⌟ ≃ₜ ⌜x  y⌟ -/
#guard_msgs in
#check (relabelHomeo[a ↦ y] : ⌜a  b⌟ ≃ₜ ⌜x  y⌟)

example : (relabel[a ↦ y] : ⌜a  b⌟ ⟶ ⌜x  y⌟) ≫ (relabel[y ↦ a] : _ ⟶ ⌜a  b⌟) = 𝟙 _ := by simp

/--
error: unsolved goals
⊢ relabel[a ↦ b, b ↦ a] = 𝟙 ⌜a  b⌟
-/
#guard_msgs in
example : (relabel[a ↦ y] : ⌜a  b⌟ ⟶ ⌜x  y⌟) ≫ (relabel[y ↦ b] : _ ⟶ ⌜a  b⌟) = 𝟙 _ := by simp

/--
error: gav_relabel: no isomorphism from
  ⌜x → y⌟
to
  ⌜o → c⌟
sends x ↦ c
-/
#guard_msgs in
example := (relabel[x ↦ c] : ⌜x → y⌟ ⟶ ⌜o → c⌟)

/--
error: gav_relabel: no point named 'q' in
  ⌜o → c⌟
-/
#guard_msgs in
example := (relabel[x ↦ q] : ⌜x → y⌟ ⟶ ⌜o → c⌟)

/-- error: gav_relabel: 'x' is already sent elsewhere -/
#guard_msgs in
example := (relabel[x ↦ o, x ↦ c] : ⌜x → y⌟ ⟶ ⌜o → c⌟)

-- a renaming of every point determines the other space
/-- info: (⌜o → c⌟ ⇢ ⌜c ↔ o⌟) ≫ relabel[c ↦ y, o ↦ x] : ⌜o → c⌟ ⟶ ⌜x ↔ y⌟ -/
#guard_msgs in
#check (⌜o → c⌟ ⇢ ⌜o ↔ c⌟) ≫ relabel[o ↦ x, c ↦ y]

/-- info: Space.relabel ≫ (⌜o → c⌟ ⇢ ⌜c ↔ o⌟) : ⌜x → y⌟ ⟶ ⌜c ↔ o⌟ -/
#guard_msgs in
#check relabel[x ↦ o, y ↦ c] ≫ (⌜o → c⌟ ⇢ ⌜o ↔ c⌟)

-- a partial renaming waits for the other space, and then keeps the names of the other points...
/-- info: (⌜o → c⌟ ⇢ ⌜c ↔ o⌟) ≫ Space.relabel : ⌜o → c⌟ ⟶ ⌜c ↔ x⌟ -/
#guard_msgs in
#check (⌜o → c⌟ ⇢ ⌜o ↔ c⌟) ≫ relabel[o ↦ x]

/-- info: Space.relabel ≫ (⌜o → c⌟ ⇢ ⌜c ↔ o⌟) : ⌜x → c⌟ ⟶ ⌜c ↔ o⌟ -/
#guard_msgs in
#check relabel[x ↦ o] ≫ (⌜o → c⌟ ⇢ ⌜o ↔ c⌟)

/--
info: fun g => (⌜o → c⌟ ⇢ ⌜c ↔ o⌟) ≫ relabel[c ↦ q, o ↦ p] ≫ g : (⌜p ↔ q⌟ ⟶ ⌜p ↔ q⌟) → (⌜o → c⌟ ⟶ ⌜p ↔ q⌟)
-/
#guard_msgs in
#check fun (g : ⌜p ↔ q⌟ ⟶ ⌜p ↔ q⌟) => (⌜o → c⌟ ⇢ ⌜o ↔ c⌟) ≫ relabel[o ↦ p] ≫ g

-- ... or, if it only uses the names of the known space, is an automorphism of it
/--
info: (⌜o₁ → c ← o₂⌟ ⇢ ⌜o₁ → c ← o₂⌟) ≫ relabel[c ↦ c, o₁ ↦ o₂, o₂ ↦ o₁] : ⌜o₁ → c ← o₂⌟ ⟶ ⌜o₁ → c ← o₂⌟
-/
#guard_msgs in
#check (⌜o₁ → c ← o₂⌟ ⇢ ⌜o₁ → c ← o₂⌟) ≫ relabel[o₁ ↦ o₂]

/-- info: (⌜o → c⌟ ⇢ ⌜c ↔ o⌟) ≫ relabel[c ↦ o, o ↦ c] : ⌜o → c⌟ ⟶ ⌜c ↔ o⌟ -/
#guard_msgs in
#check (⌜o → c⌟ ⇢ ⌜o ↔ c⌟) ≫ relabel[o ↦ c]

/--
error: gav_relabel: no isomorphism from
  ⌜o₁ → c ← o₂⌟
to
  ⌜o₁ → c ← o₂⌟
sends o₁ ↦ c
-/
#guard_msgs in
example := (⌜o₁ → c ← o₂⌟ ⇢ ⌜o₁ → c ← o₂⌟) ≫ relabel[o₁ ↦ c]

/--
error: gav_relabel: no point named 'x' in
  ⌜o → c⌟
-/
#guard_msgs in
example := relabel[o ↦ x] ≫ (⌜o → c⌟ ⇢ ⌜o ↔ c⌟)

/--
error: gav_relabel: the names of the target space (the points not mentioned keep their names) aren't distinct; give the name of every point in it, or use a type ascription
-/
#guard_msgs in
example := (⌜o₁ → c ← o₂⌟ ⇢ ⌜o₁ → c ← o₂⌟) ≫ relabel[o₁ ↦ o₂, c ↦ x]

-- it needs no expected type, as long as the space can be found in the end
example {X : TopCat.{u}} (ι : X ⟶ ⌜o₁ → c ← o₂⌟) (z : X) (hz : ι z = pt(o₁)) :
    (ι ≫ relabel[o₁ ↦ o₂]) z = pt(o₂) := by
  apply_fun relabel[o₁ ↦ o₂] at hz
  simpa using hz

example {X : TopCat.{u}} (ι : X ⟶ ⌜o₁ → c ← o₂⌟) (z : X) (hz : ι z = pt(o₁)) :
    (ι ≫ relabel[o₁ ↦ o₂]) z = pt(o₂) := by
  have := congrArg relabel[o₁ ↦ o₂] hz
  simpa using this

/-! ## Composing relabellings with diagram morphisms -/

example : (⌜o → c⌟ ⇢ ⌜o ↔ c⌟) ≫ relabel[o ↦ x, c ↦ y] =
    (⌜x(=o) → y(=c)⌟ ⇢ ⌜x(=x) ↔ y(=y)⌟ : ⌜o → c⌟ ⟶ _) := by
  simp
example : relabel[x ↦ o, y ↦ c] ≫ (⌜o → c⌟ ⇢ ⌜o ↔ c⌟) ≫ relabel[o ↦ x, c ↦ y] =
    ⌜x → y⌟ ⇢ ⌜x ↔ y⌟ := by
  simp
example : (⌜o → c⌟ ⇢ ⌜o ↔ c⌟) ≫ (⌜o ↔ c⌟ ⇢ ⌜o=c⌟) = ⌜o → c⌟ ⇢ ⌜o=c⌟ := by simp
example : relabel[x ↦ o, y ↦ c] ≫ (⌜o → c⌟ ⇢ ⌜o → c⌟) ≫ relabel[o ↦ x, c ↦ y] = 𝟙 _ := by simp
example {X : TopCat} (h : ⌜o ↔ c⌟ ⟶ X) :
    relabel[x ↦ o, y ↦ c] ≫ (⌜o → c⌟ ⇢ ⌜o ↔ c⌟) ≫ h =
      (⌜o(=x) → c(=y)⌟ ⇢ ⌜o(=o) ↔ c(=c)⌟ : ⌜x → y⌟ ⟶ _) ≫ h := by
  simp

-- with a partial expected type, only the side whose space is known is relabelled
example : (⌜x(=o) → y(=c)⌟ ⇢ ⌜x(=x) ↔ y(=y)⌟ : ⌜o → c⌟ ⟶ _) =
    (⌜o → c⌟ ⇢ ⌜o ↔ c⌟) ≫ relabel[o ↦ x, c ↦ y] := by
  decide

/-! ## Two-point spaces: `￢` -/

example : ￢(pt(o) : ⌜o → c⌟) = pt(c) := by simp
example : ￢(pt(c) : ⌜o ↔ c⌟) = pt(o) := by simp
example (x : ⌜a  b⌟) : ￢￢x = x := by simp
example (x : ⌜a  b⌟) : ￢x ≠ x := by simp
example (x y : ⌜a  b⌟) : ￢x = ￢y ↔ x = y := by simp
example (x : ⌜a  b⌟) (h : ￢x = pt(a)) : x = pt(b) := by pt_cases x <;> simp_all
example (x y : ⌜a  b⌟) : x = y ∨ x = ￢y := Space.hnot_total y x

-- `￢` is a morphism exactly when it is continuous
def hnotHom : ⌜o ↔ c⌟ ⟶ ⌜o ↔ c⌟ := Space.hom (￢·)
example : hnotHom pt(o) = pt(c) := by simp [hnotHom]
example : hnotHom ≫ hnotHom = 𝟙 _ := by decide

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: not continuous: o → c in the source, but no c → o in the target
-/
#guard_msgs in
example : ⌜o → c⌟ ⟶ ⌜o → c⌟ := Space.hom (￢·)

-- only two-point spaces have one
/--
error: failed to synthesize instance of type class
  HNot ⌜a  b  c⌟

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (x : ⌜a  b  c⌟) := ￢x

-- `relabel[…]` is computed as soon as a space is known, so `simpa using` sees it
example {S : TopCat} (φ₁ φ₂ : S ⟶ ⌜T → F₁ ↔ F₂⌟)
    (hφ : φ₁ ≫ (⌜T → F₁ ↔ F₂⌟ ⇢ ⌜T(=x) ↔ F₁(=y) ↔ F₂⌟ : _ ⟶ ⌜x ↔ y ↔ z⌟) =
      φ₂ ≫ (⌜T → F₁ ↔ F₂⌟ ⇢ ⌜T(=z) ↔ F₁(=y) ↔ F₂⌟ : _ ⟶ ⌜x ↔ y ↔ z⌟)) :
    φ₁ ≫ (⌜T → F₁ ↔ F₂⌟ ⇢ ⌜T(=z) ↔ F₁(=y) ↔ F₂⌟ : _ ⟶ ⌜x ↔ y ↔ z⌟) =
      φ₂ ≫ (⌜T → F₁ ↔ F₂⌟ ⇢ ⌜T(=x) ↔ F₁(=y) ↔ F₂⌟ : _ ⟶ ⌜x ↔ y ↔ z⌟) := by
  simpa using hφ =≫ relabel[x ↦ z, y ↦ y, z ↦ x]

/-! ## Applying morphisms given by tables -/

-- at points
example : (⌜o → c⌟ ⇢ ⌜o ↔ c⌟) pt(o) = pt(o) := by simp
example : relabel[x ↦ o, y ↦ c] (pt(y) : ⌜x → y⌟) = pt(c) := by simp
example : ((⌜x → y⌟ ⇢ ⌜x ↔ y⌟) ≫ relabel[x ↦ o, y ↦ c]) pt(y) = pt(c) := by simp

-- elsewhere, they are left as they are, rather than unfolded
/--
trace: X : TopCat
f : X ⟶ ⌜x → y⌟
z : ↑X
⊢ (ConcreteCategory.hom Space.relabel) ((ConcreteCategory.hom f) z) = pt(o)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example {X : TopCat.{u}} (f : X ⟶ ⌜x → y⌟) (z : X) : relabel[x ↦ o, y ↦ c] (f z) = pt(o) := by
  simp
  trace_state
  sorry

/--
trace: z : ⌜o → c⌟
⊢ (ConcreteCategory.hom (⌜o → c⌟ ⇢ ⌜c ↔ o⌟)) z = pt(o)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (z : ⌜o → c⌟) : (⌜o → c⌟ ⇢ ⌜o ↔ c⌟) z = pt(o) := by
  fail_if_success simp
  trace_state
  sorry

-- ... except for maps to a single point
example (z : ⌜x → y⌟) : ((⌜x → y⌟ ⇢ ⌜x ↔ y⌟) ≫ (⌜x ↔ y⌟ ⇢ ⌜x=y⌟)) z = pt(x) := by simp

-- and they compose, as `≫` does
example (z : ⌜a  b⌟) :
    (relabel[y ↦ a] : ⌜x  y⌟ ⟶ ⌜a  b⌟) ((relabel[a ↦ y] : ⌜a  b⌟ ⟶ ⌜x  y⌟) z) = z := by
  simp
example (z : ⌜a  b⌟) :
    (relabel[a ↦ b] : ⌜a  b⌟ ⟶ ⌜a  b⌟) ((relabel[a ↦ b] : ⌜a  b⌟ ⟶ ⌜a  b⌟) z) = z := by
  simp
example (z : ⌜x → y⌟) : (⌜o → c⌟ ⇢ ⌜o ↔ c⌟) (relabel[x ↦ o, y ↦ c] z) =
    ((⌜x → y⌟ ⇢ ⌜x ↔ y⌟) ≫ relabel[x ↦ o, y ↦ c]) z := by
  simp
example (z : ⌜o → c⌟) :
    (⌜o ↔ c⌟ ⇢ ⌜o=c⌟) ((⌜o → c⌟ ⇢ ⌜o ↔ c⌟) z) = (⌜o → c⌟ ⇢ ⌜o=c⌟) z := by
  simp
example {X : TopCat.{u}} (f : X ⟶ ⌜o → c⌟) (z : X) :
    (f ≫ ⌜o → c⌟ ⇢ ⌜o ↔ c⌟) z = (⌜o → c⌟ ⇢ ⌜o ↔ c⌟) (f z) := by
  simp
example (z : ⌜a → b⌟) : (Space.relabel : ⌜a → b⌟ ⟶ ⌜a → b⌟) z = z := by simp
example (z : ⌜a → b⌟) :
    inv (Space.relabel : ⌜a → b⌟ ⟶ ⌜x → y⌟) ((Space.relabel : ⌜a → b⌟ ⟶ ⌜x → y⌟) z) = z := by
  simp
example (z : ⌜a → b⌟) :
    (Space.relabelIso : ⌜a → b⌟ ≅ ⌜x → y⌟).inv ((Space.relabelIso : ⌜a → b⌟ ≅ ⌜x → y⌟).hom z) =
      z := by
  simp

-- homeomorphisms too, also with morphisms
example (z : ⌜a → b⌟) :
    (Space.relabelHomeo : ⌜a → b⌟ ≃ₜ ⌜x → y⌟).symm ((Space.relabelHomeo : ⌜a → b⌟ ≃ₜ ⌜x → y⌟) z) =
      z := by
  simp
example (z : ⌜a → b⌟) :
    (Space.relabel : ⌜x → y⌟ ⟶ ⌜a → b⌟) ((Space.relabelHomeo : ⌜a → b⌟ ≃ₜ ⌜x → y⌟) z) = z := by
  simp

/-! ## Enumerating morphisms

Morphisms between spaces are a `Fintype` (and `FinEnum`), enumerated as diagram morphisms, so
`fin_cases f` (or `pt_cases f`) splits into the possible `f`, printed as diagrams. -/

/--
trace: case «0»
P : (⌜a → b⌟ ⟶ ⌜x → y⌟) → Prop
⊢ P (⌜a → b⌟ ⇢ ⌜a=b(=x) → y⌟)

case «1»
P : (⌜a → b⌟ ⟶ ⌜x → y⌟) → Prop
⊢ P (⌜a → b⌟ ⇢ ⌜a(=x) → b(=y)⌟)

case «2»
P : (⌜a → b⌟ ⟶ ⌜x → y⌟) → Prop
⊢ P (⌜a → b⌟ ⇢ ⌜x → a=b(=y)⌟)
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (P : (⌜a → b⌟ ⟶ ⌜x → y⌟) → Prop) (f : ⌜a → b⌟ ⟶ ⌜x → y⌟) : P f := by
  fin_cases f
  trace_state
  all_goals sorry

-- `simp` evaluates the cases at points
example (f : Space [["a"], ["b"], ["c"], ["d"]] [(0, 1), (0, 2), (0, 3), (1, 3), (2, 3)] ⟶ ⌜T → F⌟)
    (h : f pt(a) = pt(F)) : f = Space.homOfTable [0, 0, 0, 0] (by decide) (by decide) := by
  pt_cases f <;> simp at h
  decide

example : Fintype.card (⌜a → b⌟ ⟶ ⌜x → y⌟) = 3 := by decide
example : FinEnum.card (⌜a  b⌟ ⟶ ⌜x → y⌟) = 4 := by decide
example : ∀ f : ⌜a → b⌟ ⟶ ⌜x → y⌟, f pt(a) = pt(x) ∨ f pt(b) = pt(y) := by decide

-- spaces without points
example : Fintype.card (Space.{0} ([] : List (List String)) [] ⟶ ⌜a⌟) = 1 := by decide
example : Fintype.card (⌜a⌟ ⟶ Space.{0} ([] : List (List String)) []) = 0 := by decide

/-! ## `grind`

`grind` preprocesses with the `seval` simprocs, which include the ones that canonicalize points and
evaluate morphisms given by tables, and it uses the lemmas tagged for it. -/

-- points
example : (pt(a) : ⌜a  b⌟) ≠ pt(b) := by grind
example : ￢(pt(a) : ⌜a  b⌟) = pt(b) := by grind
example (x : ⌜a  b⌟) : ￢￢x = x := by grind
example (x y : ⌜a  b⌟) (h : ￢x = ￢y) : x = y := by grind
example (x : ⌜a  b⌟) : ￢x ≠ x := by grind

-- morphisms at points
example : (relabel[a ↦ y] : ⌜a  b⌟ ⟶ ⌜x  y⌟) pt(a) = pt(y) := by grind
example : (⌜o → c⌟ ⇢ ⌜o ↔ c⌟) pt(o) = pt(o) := by grind
example (z : ⌜o → c⌟) : ((⌜o → c⌟ ⇢ ⌜o ↔ c⌟) ≫ (⌜o ↔ c⌟ ⇢ ⌜o=c⌟)) z = pt(c) := by grind
def swapOC : ⌜o ↔ c⌟ ⟶ ⌜o ↔ c⌟ := Space.hom fun | pt(o) => pt(c) | pt(c) => pt(o)
example : swapOC pt(o) = pt(c) := by grind [swapOC]

-- relabellings that aren't literal
example (σ : Space.Relabelling [["a"], ["b"]] [] [["x"], ["y"]] []) (z : Space.{0} [["a"], ["b"]] []) :
    (Space.relabelIso σ).inv ((Space.relabelIso σ).hom z) = z := by grind

-- open sets
example (x y : ⌜o → c⌟) (h : x ≤ y) : x ∈ Space.down y := by grind
