import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

set_option autoImplicit false

universe u

open CategoryTheory

-- 3.1. Let C be a category. Consider a structure Cᵒᵖ with Obj(Cᵒᵖ) := Obj(C);
-- for A, B objects of Cᵒᵖ (hence objects of C), Hom_Cᵒᵖ(A, B) := Hom_C(B, A).
-- Show how to make this into a category (that is, define composition of morphisms in Cᵒᵖ
-- and verify the properties listed in §3.1).
-- Intuitively, the 'opposite' category Cᵒᵖ is simply obtained by `reversing all thearrows' in C.
-- [5.1, §VIII.1.1, §IX.1.2, IX.1.10]
example {C : Type _} [hC : Category C] : Category (Cᵒᵖ) where
  Hom a b := (hC.Hom b.unop a.unop)
  id X := 𝟙 X.unop
  comp f g := g ≫ f
  id_comp f := hC.comp_id f
  comp_id f := hC.id_comp f
  assoc f g h := (hC.assoc h g f).symm

example {C : Type _} [hC : Category C] : Category (Cᵒᵖ) where
  Hom a b := (hC.Hom b.unop a.unop)ᵒᵖ
  id X := (𝟙 X.unop).op
  comp f g := (g.unop ≫ f.unop).op
  id_comp f := Opposite.unop_injective (hC.comp_id f.unop)
  comp_id f := Opposite.unop_injective (hC.id_comp f.unop)
  assoc f g h := Opposite.unop_injective (hC.assoc h.unop g.unop f.unop).symm

-- 3.2. If A is a finite set, how large is End_Set(A)?
-- this is like applying 2.10
example (A : Type _) [Fintype A] [DecidableEq A] :
    Fintype.card (A → A) = Fintype.card A ^ Fintype.card A := by
  simp

-- 3.3. Formulate precisely what it means to say that `𝟙` is an identity with respect
-- to composition in Example 3.3, and prove this assertion. [§3.2]
inductive example33Hom {S : Type u} (r : S → S → Prop) (a b : S)
| ofRel : r a b → example33Hom r a b

-- I also tried `if r a b then Σ (a : S) (b : S), Unit else PEmpty`
-- and `if r a b then (({(a, b)} : Set (S × S)) : Type u) else PEmpty`

def example33 (S : Type u) (r : S → S → Prop) [IsRefl S r] [IsTrans S r] : Category S where
  Hom a b := example33Hom r a b
  id a := .ofRel (refl a)
  comp := λ ⟨f⟩ ⟨g⟩ => .ofRel (_root_.trans f g)
  id_comp := by
    rintro a b ⟨f⟩
    -- there is no `.ofRel.inj`??
    exact congrArg example33Hom.ofRel (rfl : _root_.trans (refl a) f = f)
  comp_id := by
    rintro a b ⟨f⟩
    exact congrArg example33Hom.ofRel (rfl : f = _root_.trans f (refl b))
  assoc := by
    rintro a b c d ⟨f⟩ ⟨g⟩ ⟨h⟩
    have : _root_.trans (_root_.trans f g) h = _root_.trans f (_root_.trans g h) := rfl
    dsimp
    exact congrArg example33Hom.ofRel this

-- 3.4. Can we define a category in the style of Example 3.3 using the relation < onthe set ℤ?
-- No, because `<` is not reflexive, so we do not have identity morphisms.

-- 3.5. Explain in what sense Example 3.4 is an instance of the categories considered in Example
-- 3.3. [§3.2]
def example34 (S : Type _) : Category (Set S) :=
  example33 _ (· ⊆ ·)

-- 3.6 (Assuming some familiarity with linear algebra.) Define a category V by taking Obj(V) = N and
-- letting Hom_V(n, m) = the set of m x n matrices with real entries, for all n, m ∈ N.
-- (We will leave the reader the task of making sense of a matrix with 0 rows or columns.)
-- Use product of matrices to define composition.
-- Does this category `feel' familiar? [§VI.2.1, §VIII.I.3]
example : Category ℕ where
  Hom m n := Matrix (Fin m) (Fin n) ℝ
  id n := (1 : Matrix (Fin n) (Fin n) ℝ)
  comp := Matrix.mul
  id_comp := Matrix.one_mul
  comp_id := Matrix.mul_one
  assoc := Matrix.mul_assoc

-- 3.7 Define carefully objects and morphisms in Example 3.7,
-- and draw the diagram corresponding to composition. [§3.2]
-- An entirely similar example to the one explored in Example 3.5 maybe obtained by considering
-- morphisms in a category C from a fixed object A to all objects in C, again with morphisms
-- defined by suitable commutative diagrams. This leads to coslice categories.
--        A
-- ↓f    ↓g   ↓h
-- Z₁ →σ Z₂ →τ Z₃
example {X : Type _} [C : Category X] (A : X) : Category (Σ (Z : X), C.Hom A Z)  where
  Hom := λ ⟨Z₁, f₁⟩ ⟨Z₂, f₂⟩ => {σ : C.Hom Z₁ Z₂ // f₁ ≫ σ = f₂}
  id := λ ⟨Z, f⟩ => ⟨𝟙 Z, C.comp_id _⟩
  comp := λ ⟨f, hf⟩ ⟨g, hg⟩ => by
    refine' ⟨f ≫ g, _⟩
    rw [←C.assoc, hf, hg]
  id_comp f := by exact Subtype.ext (C.id_comp _)
  comp_id f := by exact Subtype.ext (C.comp_id _)
  assoc f g h := by exact Subtype.ext (C.assoc _ _ _)

-- 3.8. A subcategory C' of a category C consists of a collection of objects of C, with morphisms
-- Hom_C'(A, B) ⊆ Hom_C(A, B) for all objects A, B in Obj(C'), such that
-- identities and compositions in C make C' into a category. A subcategory C' is _full_ if
-- Hom_C'(A, B) = Hom_C(A, B) for all A, B in Obj(C'). Construct a category of infinite sets and
-- explain how it may be viewed as a full subcategory of Set. [4.4, §VI.1.1, §VIII.1.3]
def exercise38 {X : Type _} [C : Category X] (S : Set X) : Category S where
  Hom a b := C.Hom a b
  id a := 𝟙 a.val
  comp f g := f ≫ g
  id_comp := C.id_comp
  comp_id := C.comp_id
  assoc := C.assoc

instance exercise38' {X : Type _} [C : Category X] (S : Set X) (P : ∀ a b, C.Hom a b → Prop)
  (hrefl : ∀ a, P a a (𝟙 a)) (htrans : ∀ a b c f g, P a b f → P b c g → P a c (f ≫ g)) :
    Category S where
  Hom a b := {f : C.Hom a b // P a b f}
  id a := ⟨𝟙 a.val, hrefl a⟩
  comp f g := ⟨f.val ≫ g.val, htrans _ _ _ _ _ f.prop g.prop⟩
  id_comp := by
    intros
    exact Subtype.ext (C.id_comp _)
  comp_id := by
    intros
    exact Subtype.ext (C.comp_id _)
  assoc := by
    intros
    exact Subtype.ext (C.assoc _ _ _)

-- def exercise38full {X : Type _} [Category X] (S : Set X) : Prop :=
--   ∀ a b : S, (a ⟶ b) = (a.val ⟶ b.val)

def exercise38full' {X : Type _} [C : Category X] (S : Set X) (P : ∀ a b, C.Hom a b → Prop)
  (_hrefl : ∀ a, P a a (𝟙 a)) (_htrans : ∀ a b c f g, P a b f → P b c g → P a c (f ≫ g))
  : Prop :=
  ∀ a b : S, (C.Hom a b) = (a.val ⟶ b.val)

instance : Category (Type u) where
  Hom X Y := X → Y
  id _ := id
  comp f g := g ∘ f
  id_comp := Function.comp.right_id
  comp_id := Function.comp.left_id
  assoc _ _ _ := Function.comp.assoc _ _ _

instance exercise38infinite : Category ({X : Type u | Infinite X}) :=
  exercise38' ({X : Type u | Infinite X}) (λ _ _ _ => True) (λ _ => trivial)
    (λ _ _ _ _ _ _ _ => trivial)

-- this is somehow too easy -- it's because I defined subcategories to have the same Hom
-- instead of some predicate on Hom
-- example : exercise38full {X : Type u | Infinite X} := λ _ _ => rfl
-- and after setting to `exercise38full'`, it's obvious that they're "equal",
-- it's the subtype by True

-- 3.9 An alternative to the notion of multiset introduced in §2.2 is obtained by considering sets
-- endowed with equivalence relations; equivalent elements are taken to be multiple instances of
-- elements 'of the same kind'. Define a notion of morphism between such enhanced sets,
-- obtaining a category MSet containing (a 'copy' of) Set as a full subcategory. (There may be more
-- than one reasonable way to do this! This is intentionally an open-ended exercise.)
-- Which objects in MSet determine ordinary multisets as defined in §2.2 and how?
-- Spell out what a morphism of multisets would be from this point of view.
-- (There are several natural notions of morphisms of multisets. Try to define morphisms in MSet so
-- that the notion you obtain for ordinary multisets captures your intuitive understanding of these
-- objects.) 1§2.2, §3.2, 4.5]

instance exercise39 : Category (Σ X : Type u, {r : X → X → Prop // Equivalence r}) where
  Hom := λ ⟨X, r, _⟩ ⟨Y, s, _⟩ => {f : X → Y // ∀ ⦃a b : X⦄, r a b → s (f a) (f b)}
  id := λ ⟨X, r, _⟩ => ⟨id, λ _ _ h => h⟩
  comp := λ ⟨f, hf⟩ ⟨g, hg⟩ => ⟨g ∘ f, λ _ _ h => hg (hf h)⟩
  id_comp := by
    intros
    exact Subtype.ext (Function.comp.right_id _)
  comp_id := by
    intros
    exact Subtype.ext (Function.comp.left_id _)
  assoc := by
    intros
    exact Subtype.ext (Function.comp.assoc _ _ _)

-- Type is a subcategory because `Eq` is an Equivalence
-- Not sure about which objects in MSet determine ordinary multisets

-- 3.10. Since the objects of a category C are not (necessarily) sets, it is not clear how to make
-- sense of a notion of 'subobject' in general. In some situations it does make sense to talk about
-- subobjects, and the subobjects of any given object A in C are in one-to-one correspondence with
-- the morphisms A ⟶ Ω for a fixed, special object Ω of C, called a subobject classifier.
-- Show that Set has a subobject classifier.
example : ∃ Ω : Type u, ∀ A : Type u, Nonempty (Set A ≃ (A ⟶ Ω)) := by
  refine' ⟨ULift Prop, _⟩
  intros A
  refine' ⟨_⟩
  classical
  refine' {
    toFun := λ s x => ULift.up (x ∈ s)
    invFun := λ f => {a : A | ULift.down (f a)}
    left_inv := ?_
    right_inv := ?_
  }
  · intro
    simp
  · intro
    simp

-- 3.11. Draw the relevant diagrams and define composition and identities for the category C^A,B
-- mentioned in Example 3.9. Do the same for the category C^α,β mentioned in Example 3.10.
-- [§5.5, 5.12]
def example39_up {C : Type _} [hC : Category C] (A B : C) :
    Category (Σ (Z : C), hC.Hom A Z × hC.Hom B Z) where
  Hom := λ ⟨Z₁, f₁⟩ ⟨Z₂, f₂⟩ => {σ : Z₁ ⟶ Z₂ // f₁.fst ≫ σ = f₂.fst ∧ f₁.snd ≫ σ = f₂.snd}
  id  _ := ⟨𝟙 _, hC.comp_id _, hC.comp_id _⟩
  comp := λ ⟨f, hf⟩ ⟨g, hg⟩ => ⟨f ≫ g,
    by rw [←hC.assoc, ←hg.left, ←hf.left],
    by rw [←hC.assoc, ←hg.right, ←hf.right]⟩
  id_comp := by
    intros
    exact Subtype.ext (hC.id_comp _)
  comp_id := by
    intros
    exact Subtype.ext (hC.comp_id _)
  assoc := by
    intros
    exact Subtype.ext (hC.assoc _ _ _)

def example310_up {D : Type _} [hD : Category D] {A B C : D} (α : C ⟶ A) (β : C ⟶ B) :
    Category (Σ (Z : D), {fg : hD.Hom A Z × hD.Hom B Z // α ≫ fg.fst = β ≫ fg.snd}) where
  Hom := λ ⟨Z₁, ⟨f₁, g₁⟩, _⟩ ⟨Z₂, ⟨f₂, g₂⟩, _⟩ => {σ : Z₁ ⟶ Z₂ // f₁ ≫ σ = f₂ ∧ g₁ ≫ σ = g₂}
  id _ := ⟨𝟙 _, hD.comp_id _, hD.comp_id _⟩
  comp := λ ⟨f, hf⟩ ⟨g, hg⟩ => ⟨f ≫ g,
    by rw [←hD.assoc, ←hg.left, ←hf.left],
    by rw [←hD.assoc, ←hg.right, ←hf.right]⟩
  id_comp := by
    intros
    exact Subtype.ext (hD.id_comp _)
  comp_id := by
    intros
    exact Subtype.ext (hD.comp_id _)
  assoc := by
    intros
    exact Subtype.ext (hD.assoc _ _ _)


example {S : Type u} (r : S → S → Prop) (a b : S) : Subsingleton (example33Hom r a b) := by
  constructor
  rintro ⟨⟩ ⟨⟩
  exact congrArg _ rfl
