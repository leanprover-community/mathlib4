import Mathlib.CategoryTheory.Groupoid
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Data.Setoid.Basic

set_option autoImplicit false

universe u v

open CategoryTheory

-- 4.2. In Example 3.3 we have seen how to construct a category from a set endowed with a relation,
-- provided this latter is reflexive and transitive. For what types of relations is the
-- corresponding category a groupoid (cf. Example 4.6)? [§4.11]

inductive example33Hom {S : Type u} (r : S → S → Prop) (a b : S)
| ofRel : r a b → example33Hom r a b

def example33Hom.rel {S : Type u} {r : S → S → Prop} {a b : S} (R : example33Hom r a b) :
    r a b := by
  cases R with
  | ofRel h => exact h

set_option synthInstance.checkSynthOrder false in
instance example33 (S : Type u) (r : S → S → Prop) [IsRefl S r] [IsTrans S r] : Category S where
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

def exercise42 (S : Type u) (r : S → S → Prop) [IsRefl S r] [IsSymm S r] [IsTrans S r] :
    Groupoid S where
  -- How do you inherit from `example33 S r`?
  Hom a b := example33Hom r a b
  id a := .ofRel (refl a)
  comp := λ ⟨f⟩ ⟨g⟩ => .ofRel (_root_.trans f g)
  id_comp := by
    rintro a b ⟨f⟩
    exact congrArg example33Hom.ofRel (rfl : _root_.trans (refl a) f = f)
  comp_id := by
    rintro a b ⟨f⟩
    exact congrArg example33Hom.ofRel (rfl : f = _root_.trans f (refl b))
  assoc := by
    rintro a b c d ⟨f⟩ ⟨g⟩ ⟨h⟩
    have : _root_.trans (_root_.trans f g) h = _root_.trans f (_root_.trans g h) := rfl
    dsimp
    exact congrArg example33Hom.ofRel this
  inv := λ f => .ofRel (symm f.rel) -- using destruction here causes metavariables, #2071
  inv_comp := by
    rintro a b ⟨f⟩
    exact congrArg example33Hom.ofRel (rfl : _root_.trans (symm f) f = refl b)
  comp_inv := by
    rintro a b ⟨f⟩
    exact congrArg example33Hom.ofRel (rfl : _root_.trans f (symm f) = refl a)

-- 4.3. Let A, B be objects of a category C, and let f ∈ Hom_C(A, B) be a morphism.
-- - Prove that if f has a right-inverse, then f is an epimorphism.
-- - Show that the converse does not hold, by giving an explicit example of a category and an
-- epimorphism without a right-inverse.
example {C : Type _} [hC : Category C] (A B : C) (f : A ⟶ B) (hf : ∃ g, g ≫ f = 𝟙 _) :
    Epi f where
  left_cancellation g h H := by
    obtain ⟨u, hu⟩ := hf
    rw [←hC.id_comp g, ←hu, hC.assoc, H, ←hC.assoc, hu, hC.id_comp]

-- Porting note: I think this is now redundant.
@[simp]
theorem RingCat.ofHom_apply {R S : Type u} [Ring R] [Ring S] (f : R →+* S) (x : R) :
    RingCat.ofHom f x = f x := rfl
set_option linter.uppercaseLean3 false in
#align Ring.of_hom_apply RingCat.ofHom_apply

theorem exercise43epi : Epi (RingCat.ofHom (Int.castRingHom ℚ)) where
  left_cancellation := by
    intros X g h H
    have hc : ∀ z : ℤ, g z = h z
    · intro z
      have : (z : ℚ) = Int.castRingHom ℚ z := rfl
      rw [this, ←RingCat.ofHom_apply, ←Function.comp_apply (f := g),
          ←RingCat.coe_comp (g := g) (f := RingCat.ofHom (Int.castRingHom ℚ)), H,
          RingCat.coe_comp, Function.comp_apply, RingCat.ofHom_apply]
    have hc' : ∀ z : ℕ, g z = h z
    · intro z
      exact_mod_cast hc z
    ext a
    rcases a with ⟨num, den, hden, hcoprime⟩
    dsimp only [RingCat.forget_map, RingCat.coe_of]
    have : Rat.mk' num den hden hcoprime = num * (↑den)⁻¹
    · rw [←div_eq_mul_inv, Rat.div_num_den]
      simp [Rat.normalize_eq_mkRat, ←Rat.normalize_eq_mk']
    have hd : (den : ℚ) ≠ 0 := by exact_mod_cast hden
    rw [this, map_mul, map_mul, hc, ←div_mul_cancel (num : ℚ) hd, map_mul, ←hc', mul_assoc,
        ←map_mul, hc', mul_assoc, ←map_mul, mul_inv_cancel hd, map_one, mul_one, map_one, mul_one]

@[simp]
theorem Rat.ratCast_eq (x : ℚ) : Rat.cast x = x := rfl

theorem exercise43not_inv : ∀ g, ¬ g ≫ (RingCat.ofHom (Int.castRingHom ℚ)) = 𝟙 _ := by
  intro g H
  have hg : ∀ x : ℚ, Int.castRingHom ℚ (g x) = x
  · intro x
    rw [←RingCat.ofHom_apply (Int.castRingHom ℚ),
        ←Function.comp_apply (f := RingCat.ofHom _) (g := g),
        ←RingCat.coe_comp (f := g) (g := RingCat.ofHom (Int.castRingHom ℚ)), H]
    simp
  have hinj : ∀ x y, Int.castRingHom ℚ x = Int.castRingHom ℚ y → x = y
  · intros x y h
    exact Int.cast_injective h
  have hg : ∀ n : ℕ, 0 < n → n * g (1 / n : ℚ) = g 1
  · intro n hn
    simp only [RingCat.coe_of, one_div]
    apply hinj
    rw [map_mul, hg, hg]
    simp only [map_natCast, ne_eq, Nat.cast_eq_zero]
    rw [mul_inv_cancel]
    exact_mod_cast hn.ne'
  replace hg : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ 1
  · intros n hn
    specialize hg n hn
    rw [map_one] at hg
    rw [←hg]
    simp
  specialize hg 2 zero_lt_two
  simpa using Int.eq_one_of_dvd_one zero_le_two hg

-- 4.4. Prove that the composition of two monomorphisms is a monomorphism.
-- Deduce that one can define a subcategory C_mono of a category C by taking the same objects as in
-- C and defining Hom_C_mono(A, B) to be the subset of Hom_C(A, B) consisting of monomorphisms,
-- for all objects A, B. (Cf. Exercise 3.8; of course, in general C_mono is not full in C.)
-- Do the same for epimorphisms. Can you define a subcategory C_nonmono of C by restricting to
-- morphisms that are not monomorphisms?
theorem exercise44mono {C : Type _} [Category C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Mono f) (hg : Mono g) : Mono (f ≫ g) where
  right_cancellation := by
    intros W u v H
    rw [←Category.assoc, ←Category.assoc] at H
    replace hg := hg.right_cancellation _ _ H
    exact hf.right_cancellation _ _ hg

def exercise44monocat {C : Type _} [hC : Category C] : Category C where
  Hom a b := {f : a ⟶ b // Mono f}
  id a := ⟨𝟙 a, ⟨by
    intros
    simp_all [Category.comp_id]⟩⟩
  comp f g := ⟨f.val ≫ g.val, exercise44mono f.val g.val f.prop g.prop⟩
  id_comp f := Subtype.ext (Category.id_comp _)
  comp_id f := Subtype.ext (Category.comp_id _)
  assoc _ _ _ := Subtype.ext (Category.assoc _ _ _)

theorem exercise44epi {C : Type _} [Category C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Epi f) (hg : Epi g) : Epi (f ≫ g) where
  left_cancellation := by
    intros W u v H
    rw [Category.assoc, Category.assoc] at H
    replace hf := hf.left_cancellation _ _ H
    exact hg.left_cancellation _ _ hf

def exercise44epicat {C : Type _} [hC : Category C] : Category C where
  Hom a b := {f : a ⟶ b // Epi f}
  id a := ⟨𝟙 a, ⟨by
    intros
    simp_all [Category.comp_id]⟩⟩
  comp f g := ⟨f.val ≫ g.val, exercise44epi f.val g.val f.prop g.prop⟩
  id_comp f := Subtype.ext (Category.id_comp _)
  comp_id f := Subtype.ext (Category.comp_id _)
  assoc _ _ _ := Subtype.ext (Category.assoc _ _ _)

-- Can't define a category C_nonmono of not monomorphisms because then we wouldn't have
-- identity morphisms, which are necessary monomorphisms

-- 4.5. Give a concrete description of monomorphisms and epimorphisms in the category MSet you
-- constructed in Exercise 3.9.
-- (Your answer will depend on the notion of morphism you defined in that exercise!)

instance exercise39 : Category (Σ X : Type u, Setoid X) where
  Hom := λ ⟨X, X'⟩ ⟨Y, Y'⟩ => {f : X ⟶ Y // ∀ ⦃a b : X⦄, a ≈ b → (f a) ≈ (f b)}
  id := λ ⟨X, X'⟩ => ⟨id, λ _ _ h => h⟩
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

theorem exercise45mono {A B : (Σ X : Type u, Setoid X)} (f : A ⟶ B) :
    Mono f ↔ Mono f.val := by
  constructor <;> intro h <;> constructor
  · intros Z u v H
    let Z' : (Σ X : Type u, Setoid X) := ⟨Z, ⊥⟩
    let u' : Z' ⟶ A := ⟨u, λ _ _ H => by rw [H]; exact A.2.2.1 _⟩
    let v' : Z' ⟶ A := ⟨v, λ _ _ H => by rw [H]; exact A.2.2.1 _⟩
    change u'.val = v'.val
    rw [←Subtype.ext_iff]
    refine' h.right_cancellation _ _ _
    exact Subtype.ext H
  · intros Z u v H
    rw [Subtype.ext_iff] at H ⊢
    exact h.right_cancellation _ _ H

theorem exercise45epi {A B : (Σ X : Type u, Setoid X)} (f : A ⟶ B) :
    Epi f ↔ Epi f.val := by
  constructor <;> intro h <;> constructor
  · intros Z u v H
    let Z' : (Σ X : Type u, Setoid X) := ⟨Z, ⊤⟩
    let u' : B ⟶ Z' := ⟨u, λ _ _ _ => by simp; trivial⟩
    let v' : B ⟶ Z' := ⟨v, λ a _ _ => by simp; trivial⟩
    change u'.val = v'.val
    rw [←Subtype.ext_iff]
    refine' h.left_cancellation _ _ _
    exact Subtype.ext H
  · intros Z u v H
    rw [Subtype.ext_iff] at H ⊢
    exact h.left_cancellation _ _ H
