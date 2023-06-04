import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Opposites
import Mathlib.Data.Int.GCD

set_option autoImplicit false

universe u v w

open CategoryTheory Opposite

-- 5.1. Prove that a final object in a category C is initial in the opposite category Cᵒᵖ
-- Setting up my own API because I don't understand the mathlib IsInitial yet (what are cocones?)
def Initial {C : Type _} [Category C] (I : C) :=
    ∀ A : C, Unique (I ⟶ A)

instance {C : Type _} [Category C] (I : C) : Subsingleton (Initial I) where
  allEq := by
    intros
    funext
    simp

def Final {C : Type _} [Category C] (F : C) :=
    ∀ A : C, Unique (A ⟶ F)

instance {C : Type _} [Category C] (F : C) : Subsingleton (Final F) where
  allEq := by
    intros
    funext
    simp

nonrec
def Final.op {C : Type _} [Category C] {F : C} (hF : Final F) : Initial (op F) :=
    λ A => ⟨⟨op (hF (unop A)).default⟩, λ _ => unop_injective ((hF (unop A)).uniq _)⟩

-- 5.2. Prove that 0 is the unique initial object in Set. [§5.1]
def PEmpty_Initial : Initial PEmpty :=
  λ _ => ⟨⟨λ x => x.elim⟩, λ _ => funext (λ x => x.elim)⟩

-- universes needed so that universes aren't constrained unnecessarily and proofs can't be found
-- cf. https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Failure.20of.20TC.20search.20in.20.60simp.60.20with.20.60etaExperiment.60.2E
def Initial.Iso {C : Type _} [Category.{u, v} C] {X Y : C} (hX : Initial X) (hY : Initial Y) : X ≅ Y where
  hom := (hX Y).default
  inv := (hY X).default
  hom_inv_id := by have := hX X; simp
  inv_hom_id := by have := hY Y; simp

def Iso.Equiv {X Y : Type _} (f : X ≅ Y) : X ≃ Y where
  toFun := f.hom
  invFun := f.inv
  left_inv := congrFun f.hom_inv_id
  right_inv := congrFun f.inv_hom_id

-- can't prove uniqueness in Lean because no type extensionality
-- because I can define my own empty inductive `MyEmpty`

def Initial.IsoPEmpty {X : Type _} (hX : Initial X) : X ≅ PEmpty := hX.Iso PEmpty_Initial

-- 5.3. Prove that final objects are unique up to isomorphism. [§5.1]
def Final.Iso {C : Type _} [Category.{u, v} C] {X Y : C} (hX : Final X) (hY : Final Y) : X ≅ Y where
  hom := (hY X).default
  inv := (hX Y).default
  hom_inv_id := by have := hX X; simp
  inv_hom_id := by have := hY Y; simp

-- 5.4. What are initial and final objects in the category of `pointed sets' (Example 3.8)?
-- Are they unique?
def PointedPunit_Initial : Initial (Pointed.of PUnit.unit) :=
    λ A => ⟨⟨⟨λ _ => A.point, rfl⟩⟩, by
      intro f
      refine' Pointed.Hom.ext _ _ _
      funext
      exact f.map_point⟩

def PointedPunit_Final : Final (Pointed.of PUnit.unit) :=
    λ A => ⟨⟨⟨λ _ => PUnit.unit, rfl⟩⟩, by
      intro f
      refine' Pointed.Hom.ext _ _ _
      funext
      exact f.map_point⟩
-- not unique, any singleton set is isomorphic to PUnit

-- 5.5. What are the final objects in the category considered in §5.3? [§5.3]
-- Section 5.3: "The quotient A/~ is universal with respect to the property of mapping A to a
-- set in such a way that equivalent elements have the same image."
variable {A : Type _}

instance section53 (r : A → A → Prop) :
    Category (Σ' Z : Type _, {f : A → Z // ∀ ⦃a b : A⦄, r a b → f a = f b}) where
  Hom := λ ⟨Z, f⟩ ⟨Z', g⟩ => {σ : Z → Z' // σ ∘ f.1 = g.1}
  id _ := ⟨id, Function.comp.left_id _⟩
  comp f g := ⟨g.1 ∘ f.1, by rw [Function.comp.assoc, f.2, g.2]⟩
  id_comp _ := Subtype.ext (Function.comp.left_id _)
  comp_id _ := Subtype.ext (Function.comp.right_id _)
  assoc _ _ _ := Subtype.ext (Function.comp.assoc _ _ _)

def Quot_Initial (r : A → A → Prop) :
    Initial (⟨_, Quot.mk r, λ _ _ h => Quot.sound h⟩ :
      (Σ' Z : Type _, {f : A → Z // ∀ ⦃a b : A⦄, r a b → f a = f b})) :=
  λ ⟨Z, f⟩ => ⟨⟨⟨Quot.lift f.1 f.2, funext λ x => Quot.lift_mk f.1 f.2 x⟩⟩,
    λ ⟨f', hf⟩ => by
      refine' Subtype.ext _
      ext ⟨x⟩
      dsimp
      simp_rw [←hf]
      rfl⟩

def PUnit_Final (r : A → A → Prop) :
    Final (⟨PUnit, λ _ => PUnit.unit, λ _ _ _ => rfl⟩ :
      (Σ' Z : Type _, {f : A → Z // ∀ ⦃a b : A⦄, r a b → f a = f b})) :=
  λ _ => ⟨⟨⟨λ _ => PUnit.unit, funext λ _ => rfl⟩⟩, λ _ => rfl⟩

-- 5.6. Consider the category corresponding to endowing (as in Example 3.3) theset Z+ of
-- positive integers with the divisibility relation. Thus there is exactly one morphism d -> m in
-- this category if and only if d divides m without remainder; there is no morphism between d and m
-- otherwise. Show that this category has products and coproducts.
-- What are their `conventional' names? [§VII.5.1]

-- Redefining products and coproducts because I don't yet understand Limits and functors

instance example39_down {C : Type _} [hC : Category C] (A B : C) :
    Category (Σ (Z : C), hC.Hom Z A × hC.Hom Z B) where
  Hom := λ ⟨Z₁, f₁⟩ ⟨Z₂, f₂⟩ => {σ : Z₁ ⟶ Z₂ // σ ≫ f₂.fst = f₁.fst ∧ σ ≫ f₂.snd = f₁.snd}
  id  _ := ⟨𝟙 _, hC.id_comp _, hC.id_comp _⟩
  comp := λ ⟨f, hf⟩ ⟨g, hg⟩ => ⟨f ≫ g,
    by rw [hC.assoc, hg.left, hf.left],
    by rw [hC.assoc, hg.right, hf.right]⟩
  id_comp := by
    intros
    exact Subtype.ext (hC.id_comp _)
  comp_id := by
    intros
    exact Subtype.ext (hC.comp_id _)
  assoc := by
    intros
    exact Subtype.ext (hC.assoc _ _ _)

instance example39_up {C : Type _} [hC : Category C] (A B : C) :
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

class HasFiniteProducts (C : Type _) [hC : Category C] : Prop where
  hasFinal : ∀ A B : C, ∃ F : (Σ (Z : C), hC.Hom Z A × hC.Hom Z B), Nonempty (Final F)

class HasFiniteCoproducts (C : Type _) [hC : Category C] : Prop where
  hasInitial : ∀ A B : C, ∃ I : (Σ (Z : C), hC.Hom A Z × hC.Hom B Z), Nonempty (Initial I)

namespace exercise56
inductive obj | of : (d : ℤ) → obj

def obj.un : obj → ℤ | of d => d

inductive hom (d m : obj)
| of : d.un ∣ m.un → hom d m

def hom.un {d m : obj} : hom d m → d.un ∣ m.un | of h => h
def hom.ext {d m : obj} (h h' : d.un ∣ m.un) : hom.of h = hom.of h' := rfl

instance : Category obj where
  Hom := hom
  id _ := .of (Int.dvd_refl _)
  comp f g := .of (Int.dvd_trans f.un g.un)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

instance : HasFiniteProducts obj where
  hasFinal d m := ⟨
    ⟨.of (Int.gcd d.un m.un), .of (Int.gcd_dvd_left _ _), .of (Int.gcd_dvd_right _ _)⟩,
    ⟨λ ⟨_, hkd, hkm⟩ => ⟨⟨.of (Int.dvd_gcd hkd.un hkm.un), rfl, rfl⟩, λ _ => rfl⟩⟩⟩

instance : HasFiniteCoproducts obj where
  hasInitial d m := ⟨
    ⟨.of (Int.lcm d.un m.un), .of (Int.dvd_lcm_left _ _), .of (Int.dvd_lcm_right _ _)⟩,
    ⟨λ ⟨_, hkd, hkm⟩ => ⟨⟨.of (Int.lcm_dvd hkd.un hkm.un), rfl, rfl⟩, λ _ => rfl⟩⟩⟩

end exercise56

-- 5.7. Redo Exercise 2.9, this time using Proposition 5.4.
-- 2.9
-- Show that if A' ≅ A" and B' ≅ B" and further A' ∩ B' = 0 and A" ∩ B" = 0, then A' ∪ B' ≅ A" ∪ B".
-- Conclude that the operation A ⨆ B (as described in §1.4) is well-defined up to isomorphism
-- (cf. §2.9). [§2.9, 5.7]

def Initial.Iso_unique {C : Type _} [Category.{u, v} C] {X Y : C} (hX : Initial X) (hY : Initial Y) :
    Unique (X ≅ Y) where
  default := hX.Iso hY
  uniq e := Iso.ext $ by
    have : Unique (X ⟶ Y) := hX Y
    exact Subsingleton.elim _ _

def Final.Iso_unique {C : Type _} [Category.{u, v} C] {X Y : C} (hX : Final X) (hY : Final Y) :
    Unique (X ≅ Y) where
  default := hX.Iso hY
  uniq e := Iso.ext $ by
    have : Unique (X ⟶ Y) := hY X
    exact Subsingleton.elim _ _

instance category57 {X : Type _} : Category (Set X) where
  Hom s t := s → t
  id s := id
  comp f g := g ∘ f

noncomputable
def category57.Initial_Union {X : Type _} (A B : Set X) (hAB : A ∩ B = ∅) :
  @Initial (Σ (Z : Set X), (A ⟶ Z) × (B ⟶ Z)) _ ⟨A ∪ B, λ x => ⟨x, by simp⟩, λ x => ⟨x, by simp⟩⟩ :=
  λ ⟨Z, f, g⟩ => by
    classical
    exact {
      default := ⟨λ x => if hx : (x : X) ∈ A then f ⟨x, hx⟩ else g ⟨x, by simpa [hx] using x.prop⟩,
        funext <| λ x => by
        change (_ ∘ _) x = f x
        simp [x.prop], funext <| λ x => by
        change (_ ∘ _) x = g x
        have hx : (x : X) ∉ A := λ H => by simpa using hAB.le (Set.mem_inter H x.prop)
        simp [x.prop, hx]⟩
      uniq := λ h => by
        refine' Subtype.ext _
        funext x
        dsimp
        cases' x.prop with hx hx
        · simpa [hx] using congrFun h.2.1 ⟨x, hx⟩
        · have hx' : (x : X) ∉ A := λ H => by simpa using hAB.le (Set.mem_inter H hx)
          simpa [hx, hx'] using congrFun h.2.2 ⟨x, hx⟩ }

noncomputable
def category57.Initial_Union' {X : Type _} (A B A' B' : Set X)
    (_ : A ∩ B = ∅) (hAB' : A' ∩ B' = ∅) (e : A ≅ A') (e' : B ≅ B') :
  @Initial (Σ (Z : Set X), (A ⟶ Z) × (B ⟶ Z)) _ ⟨A' ∪ B', e.hom ≫ (λ x => ⟨x, by simp⟩), e'.hom ≫ (λ x => ⟨x, by simp⟩)⟩ :=
  λ ⟨Z, f, g⟩ => by
    classical
    exact {
      default := ⟨λ x => if hx : (x : X) ∈ A' then f (e.inv ⟨x, hx⟩) else g (e'.inv ⟨x, by simpa [hx] using x.prop⟩),
        funext <| λ x => by
        change (_ ∘ _) x = f x
        dsimp
        split
        · change (e.hom ≫ e.inv ≫ f) x = f x
          rw [←Category.assoc, e.hom_inv_id, Category.id_comp]
        · rename_i hx
          change (e.hom x : X) ∉ A' at hx
          simp at hx,
        funext <| λ x => by
        change (_ ∘ _) x = g x
        dsimp
        split
        · rename_i hx
          simpa using hAB'.le (Set.mem_inter hx (e'.hom x).prop)
        · change (e'.hom ≫ e'.inv ≫ g) x = g x
          rw [←Category.assoc, e'.hom_inv_id, Category.id_comp] ⟩
      uniq := λ h => by
        refine' Subtype.ext _
        funext x
        dsimp
        cases' x.prop with hx hx
        · have := h.2.1
          simp only [hx, dite_true]
          dsimp only at this
          simp_rw [←this]
          refine' congr_arg _ (Subtype.ext _)
          dsimp
          change _ = Subtype.val ((e.inv ≫ e.hom) _)
          simp only [e.inv_hom_id]
          rfl
        · have hx' : (x : X) ∉ A' := λ H => by simpa using hAB'.le (Set.mem_inter H hx)
          have := h.2.2
          dsimp only at this
          simp only [←this, hx', Category.assoc, dite_false]
          refine' congr_arg _ (Subtype.ext _)
          dsimp
          change _ = Subtype.val ((e'.inv ≫ e'.hom) _)
          simp only [e'.inv_hom_id]
          rfl }

noncomputable
def category57.disjoint_union_iso {X : Type _} (A B A' B' : Set X)
    (hAB : A ∩ B = ∅) (hAB' : A' ∩ B' = ∅) (e : A ≅ A') (e' : B ≅ B') :
    (⟨A ∪ B, λ x => ⟨x, by simp⟩, λ x => ⟨x, by simp⟩⟩ : (Σ (Z : Set X), (A ⟶ Z) × (B ⟶ Z))) ≅
    (⟨A' ∪ B', e.hom ≫ (λ x => ⟨x, by simp⟩), e'.hom ≫ (λ x => ⟨x, by simp⟩)⟩) :=
  Initial.Iso (category57.Initial_Union _ _ hAB) (category57.Initial_Union' _ _ _ _ hAB hAB' _ _)

-- 5.8. Show that in every category C the products A x B and B x A are isomorphic,
-- if they exist. (Hint: Observe that they both satisfy the universal property for
-- the product of A and B; then use Proposition 5.4.)

noncomputable
def AProd {C : Type _} [Category C] [hp : HasFiniteProducts C] (A B : C) : C :=
  (hp.hasFinal A B).choose.fst

local notation A:80 " ×_C " B:80 => AProd A B

noncomputable
def AProd.fstHom {C : Type _} [Category C] [hp : HasFiniteProducts C]
    {A B : C} : A ×_C B ⟶ A :=
  (hp.hasFinal A B).choose.snd.fst

noncomputable
def AProd.sndHom {C : Type _} [Category C] [hp : HasFiniteProducts C]
    {A B : C} : A ×_C B ⟶ B :=
  (hp.hasFinal A B).choose.snd.snd

lemma AProd_Final_sigma {C : Type _} [hC : Category C] [hp : HasFiniteProducts C] (A B : C) :
    Nonempty (Final (⟨A ×_C B, AProd.fstHom, AProd.sndHom⟩
      : (Σ (Z : C), hC.Hom Z A × hC.Hom Z B))) :=
  (hp.hasFinal A B).choose_spec

lemma AProd_Final_sigma' {C : Type _} [hC : Category C] [hp : HasFiniteProducts C] (A B : C) :
    Nonempty (Final (⟨B ×_C A, AProd.sndHom, AProd.fstHom⟩
      : (Σ (Z : C), hC.Hom Z A × hC.Hom Z B))) := by
  let ⟨F⟩ := AProd_Final_sigma B A
  refine' ⟨λ Z => _⟩
  obtain ⟨⟨σ⟩, hσ⟩ := F ⟨Z.fst, Z.snd.snd, Z.snd.fst⟩
  refine' ⟨⟨σ.val, σ.prop.symm⟩, λ f => Subtype.ext _⟩
  specialize hσ ⟨f.val, f.prop.symm⟩
  rw [Subtype.ext_iff.mp hσ]
  rfl

lemma AProd.Iso {C : Type _} [hC : Category C] [hp : HasFiniteProducts C] (A B : C) :
    Nonempty (A ×_C B ≅ B ×_C A) := by
  obtain ⟨F⟩ := (AProd_Final_sigma A B)
  obtain ⟨F'⟩ := (AProd_Final_sigma' A B)
  let e := F.Iso F'
  exact ⟨e.hom.val, e.inv.val,
    congr_arg Subtype.val e.hom_inv_id, congr_arg Subtype.val e.inv_hom_id⟩

-- 5.9. Let C be a category with products. Find a reasonable candidate for the universal property
-- that the product A x B x C of three objects of C ought to satisfy, and prove that both
-- (A x B) x C and A x (B x C) satisfy this universal property.
-- Deduce that (A x B) x C and A x (B x C) are necessarily isomorphic

instance exercise59_down {C : Type _} [hC : Category C] (I J K : C) :
    Category (Σ (Z : C), (Z ⟶ I) × (Z ⟶ J) × (Z ⟶ K)) where
  Hom := λ ⟨Z₁, f₁⟩ ⟨Z₂, f₂⟩ => {σ : Z₁ ⟶ Z₂ // σ ≫ f₂.fst = f₁.fst ∧ σ ≫ f₂.snd.fst = f₁.snd.fst ∧ σ ≫ f₂.snd.snd = f₁.snd.snd}
  id  _ := ⟨𝟙 _, hC.id_comp _, hC.id_comp _, hC.id_comp _⟩
  comp := λ ⟨f, hf⟩ ⟨g, hg⟩ => ⟨f ≫ g,
    by rw [hC.assoc, hg.left, hf.left],
    by rw [hC.assoc, hg.right.left, hf.right.left],
    by rw [hC.assoc, hg.right.right, hf.right.right]⟩
  id_comp := by
    intros
    exact Subtype.ext (hC.id_comp _)
  comp_id := by
    intros
    exact Subtype.ext (hC.comp_id _)
  assoc := by
    intros
    exact Subtype.ext (hC.assoc _ _ _)

class HasFiniteTripleProducts (C : Type _) [Category C] : Prop where
  hasFinal : ∀ I J K : C, ∃ F : (Σ (Z : C), (Z ⟶ I) × (Z ⟶ J) × (Z ⟶ K)), Nonempty (Final F)

open AProd in
lemma TripleProduct_Final {C : Type _} [Category C] [hp : HasFiniteProducts C] (I J K : C) :
    Nonempty (Final (⟨I ×_C J ×_C K, fstHom, sndHom ≫ fstHom, sndHom ≫ sndHom⟩
      : (Σ (Z : C), (Z ⟶ I) × (Z ⟶ J) × (Z ⟶ K)))) := by
  let ⟨G⟩ := AProd_Final_sigma J K
  let ⟨H⟩ := AProd_Final_sigma I (J ×_C K)
  refine' ⟨_⟩
  intro ⟨Z, f, g, h⟩
  obtain ⟨⟨τ⟩, hτ⟩ := G ⟨Z, g, h⟩
  obtain ⟨⟨φ⟩, hφ⟩ := H ⟨Z, f, τ.val⟩
  refine' ⟨⟨φ.val, φ.prop.left, _, _⟩, _⟩
  · dsimp
    rw [←Category.assoc, φ.prop.right]
    exact τ.prop.left
  · dsimp
    rw [←Category.assoc, φ.prop.right]
    exact τ.prop.right
  · intro ψ
    refine' Subtype.ext _
    specialize hτ ⟨ψ.val ≫ sndHom, _, _⟩
    · simpa [Category.assoc] using ψ.prop.right.left
    · simpa [Category.assoc] using ψ.prop.right.right
    specialize hφ ⟨ψ.val, ψ.prop.left, _⟩
    · exact Subtype.ext_iff.mp hτ
    · dsimp
      exact Subtype.ext_iff.mp hφ

open AProd in
lemma TripleProduct_Final' {C : Type _} [Category C] [hp : HasFiniteProducts C] (I J K : C) :
    Nonempty (Final (⟨(I ×_C J) ×_C K, fstHom ≫ fstHom, fstHom ≫ sndHom, sndHom⟩
      : (Σ (Z : C), (Z ⟶ I) × (Z ⟶ J) × (Z ⟶ K)))) := by
  let ⟨G⟩ := AProd_Final_sigma I J
  let ⟨H⟩ := AProd_Final_sigma (I ×_C J) K
  refine' ⟨_⟩
  intro ⟨Z, f, g, h⟩
  obtain ⟨⟨τ⟩, hτ⟩ := G ⟨Z, f, g⟩
  obtain ⟨⟨φ⟩, hφ⟩ := H ⟨Z, τ.val, h⟩
  refine' ⟨⟨φ.val, _, _, φ.prop.right⟩, _⟩
  · dsimp
    rw [←Category.assoc, φ.prop.left]
    exact τ.prop.left
  · dsimp
    rw [←Category.assoc, φ.prop.left]
    exact τ.prop.right
  · intro ψ
    refine' Subtype.ext _
    specialize hτ ⟨ψ.val ≫ fstHom, _, _⟩
    · simpa [Category.assoc] using ψ.prop.left
    · simpa [Category.assoc] using ψ.prop.right.left
    specialize hφ ⟨ψ.val, _, ψ.prop.right.right⟩
    · exact Subtype.ext_iff.mp hτ
    · dsimp
      exact Subtype.ext_iff.mp hφ

lemma TripleProduct.Iso {C : Type _} [hC : Category C] [hp : HasFiniteProducts C] (I J K : C) :
    Nonempty (I ×_C J ×_C K ≅ (I ×_C J) ×_C K) := by
  obtain ⟨F⟩ := (TripleProduct_Final I J K)
  obtain ⟨F'⟩ := (TripleProduct_Final' I J K)
  let e := F.Iso F'
  exact ⟨e.hom.val, e.inv.val,
    congr_arg Subtype.val e.hom_inv_id, congr_arg Subtype.val e.inv_hom_id⟩

-- 5.10. Push the envelope a little further still, and define products and coproducts for families
-- (i.e., indexed sets) of objects of a category.  Do these exist in Set?

instance exercise510_down (C : Type u) [Category.{v} C] (I : Type w) (ι : I → C) :
    Category (Σ (Z : C), ∀ i : I, Z ⟶ ι i) where
  Hom := λ ⟨X, f⟩ ⟨Y, g⟩ => {σ : X ⟶ Y // ∀ i, σ ≫ g i = f i}
  id _ := ⟨𝟙 _, λ _ => Category.id_comp _⟩
  comp := λ ⟨f, hf⟩ ⟨g, hg⟩ => ⟨f ≫ g, λ _ => by rw [Category.assoc, hg, hf]⟩
  id_comp := by
    intros
    exact Subtype.ext (Category.id_comp _)
  comp_id := by
    intros
    exact Subtype.ext (Category.comp_id _)
  assoc := by
    intros
    exact Subtype.ext (Category.assoc _ _ _)

instance exercise510_up (C : Type u) [Category.{v} C] (I : Type w) (ι : I → C) :
    Category (Σ (Z : C), ∀ i : I, ι i ⟶ Z) where
  Hom := λ ⟨X, f⟩ ⟨Y, g⟩ => {σ : X ⟶ Y // ∀ i, f i ≫ σ = g i}
  id _ := ⟨𝟙 _, λ _ => Category.comp_id _⟩
  comp := λ ⟨f, hf⟩ ⟨g, hg⟩ => ⟨f ≫ g, λ _ => by rw [←Category.assoc, hf, hg]⟩
  id_comp := by
    intros
    exact Subtype.ext (Category.id_comp _)
  comp_id := by
    intros
    exact Subtype.ext (Category.comp_id _)
  assoc := by
    intros
    exact Subtype.ext (Category.assoc _ _ _)

class HasIndexedProducts (C : Type u) [Category.{v} C] (I : Type w) : Prop where
  hasFinal : ∀ ι : I → C, ∃ F : (Σ (Z : C), ∀ i : I, Z ⟶ ι i), Nonempty (Final F)

class HasIndexedCoproducts (C : Type u) [Category.{v} C] (I : Type w) : Prop where
  hasFinal : ∀ ι : I → C, ∃ F : (Σ (Z : C), ∀ i : I, ι i ⟶ Z), Nonempty (Initial F)


-- Set (Type 0) has indexed products, which are Pi types
instance (I : Type u) : HasIndexedProducts (Type u) I where
  hasFinal ι := ⟨⟨∀ i : I, ι i, λ i f => f i⟩, ⟨λ ⟨Z, f⟩ => ⟨⟨λ z i => f i z, λ _ => rfl⟩, λ ι => by
    refine' Subtype.ext _
    funext i z
    exact congr_fun (ι.prop z) i⟩⟩⟩

-- Set (Type 0) has indexed coproducts, which are Sigma types
instance (I : Type u) : HasIndexedCoproducts (Type u) I where
  hasFinal ι := ⟨⟨Σ i : I, ι i, Sigma.mk⟩, ⟨λ ⟨Z, f⟩ => ⟨⟨λ z => f z.fst z.snd, λ _ => rfl⟩,
    λ ι => by
      refine' Subtype.ext _
      funext i
      exact congr_fun (ι.prop i.fst) i.snd⟩⟩⟩

-- 5.11. Let A, resp. B, be a set, endowed with an equivalence relation ~A, resp. ~B.
-- Define a relation ~ on A x B by setting
-- (a₁, b₁) ~ (a₂, b₂) ↔ a₁ ~A a₂ and b₁ ~B b₂.
-- (This is immediately seen to be an equivalence relation.)
-- Use the universal property for quotients (§5.3) to establish that there are functions
-- (A x B)/~ -> A/-A, (A x B)/~ -> B/-B. Prove that (A x B)/~, with these two functions,
-- satisfies the universal property for the product of A/~A and B/~B.
-- Conclude (without further work) that (A x B)/~ ≅ (A/~A) X (B/~B).

section exercise511

variable {A B : Type u} (r : Setoid A) (s : Setoid B)

def Setoid.prod : Setoid (A × B) where
  r x y := r.r x.fst y.fst ∧ s.r x.snd y.snd
  iseqv := ⟨λ _ => And.intro (r.refl _) (s.refl _), And.imp r.symm s.symm,
    λ ⟨hr, hs⟩ ⟨hr', hs'⟩ => And.intro (r.trans hr hr') (s.trans hs hs')⟩

def concreteProd :
    Final (⟨A × B, Prod.fst, Prod.snd⟩ : (Σ (Z : Type u), (Z ⟶ A) × (Z ⟶ B))) :=
  λ ⟨_, f, g⟩ => ⟨⟨λ z => ⟨f z, g z⟩, rfl, rfl⟩,
    λ ⟨_, hf, hf'⟩ => Subtype.ext (funext λ _ => Prod.ext (congr_fun hf _) (congr_fun hf' _))⟩

instance concreteHasProd : HasFiniteProducts (Type u) where
  hasFinal A B := ⟨_, ⟨concreteProd (A := A) (B := B)⟩⟩

noncomputable
def HomAProd {C : Type u} [Category C] [hp : HasFiniteProducts C] {Z A B : C}
    (f : Z ⟶ A) (g : Z ⟶ B) : Z ⟶ A ×_C B :=
  (Classical.choice (hp.hasFinal A B).choose_spec ⟨Z, f, g⟩).default.val

@[simp]
lemma HomAProd_comp_fst {C : Type u} [Category C] [hp : HasFiniteProducts C] {Z A B : C}
      (f : Z ⟶ A) (g : Z ⟶ B) : HomAProd f g ≫ AProd.fstHom = f :=
  (Classical.choice (hp.hasFinal A B).choose_spec ⟨Z, f, g⟩).default.prop.left

@[simp]
lemma HomAProd_comp_snd {C : Type u} [Category C] [hp : HasFiniteProducts C] {Z A B : C}
      (f : Z ⟶ A) (g : Z ⟶ B) : HomAProd f g ≫ AProd.sndHom = g :=
  (Classical.choice (hp.hasFinal A B).choose_spec ⟨Z, f, g⟩).default.prop.right

def QuotHom {Z : Type _} (r : Z → Z → Prop) : Z ⟶ Quot r := Quot.mk _

@[simp]
lemma QuotHom_apply {Z : Type _} (r : Z → Z → Prop) (a : Z) : QuotHom r a = Quot.mk r a := rfl

def QuotLift {A Z : Type _} (f : A ⟶ Z) (r : A → A → Prop) (hf : ∀ a b, r a b → f a = f b) :
    Quot r ⟶ Z := ((Quot_Initial r) ⟨Z, f, hf⟩).default.val

lemma QuotLift_prop {A Z : Type _} (f : A ⟶ Z) (r : A → A → Prop) (hf : ∀ a b, r a b → f a = f b) :
  QuotHom r ≫ QuotLift f r hf = f := ((Quot_Initial r) ⟨Z, f, hf⟩).default.prop

lemma QuotLift_unique {A Z : Type _} (f : A ⟶ Z) (r : A → A → Prop) (hf : ∀ a b, r a b → f a = f b)
    (g : Quot r ⟶ Z) (hg : QuotHom r ≫ g = f) : g = QuotLift f r hf := by
  rw [←QuotLift_prop f r hf] at hg
  have := ((Quot_Initial r) ⟨Z, f, hf⟩).uniq ⟨g, hg⟩
  exact Subtype.ext_iff.mp this

@[simp]
lemma QuotLift_apply {A Z : Type _} (f : A ⟶ Z) (r : A → A → Prop) (hf : ∀ a b, r a b → f a = f b)
    (a : A) : QuotLift f r hf (Quot.mk r a) = f a := rfl

def QuotMap {A Z : Type u} (r : A → A → Prop) (s : Z → Z → Prop) (f : A ⟶ Z)
    (hf : ∀ a b, r a b → s (f a) (f b)) : Quot r ⟶ Quot s :=
  Quot.lift (f ≫ QuotHom _) (λ a b h => Quot.sound (hf a b h))

@[simp] lemma QuotMap_apply {A Z : Type u} (r : A → A → Prop) (s : Z → Z → Prop) (f : A ⟶ Z)
    (hf : ∀ a b, r a b → s (f a) (f b)) (a : A) :
    QuotMap r s f hf (Quot.mk r a) = Quot.mk s (f a) :=
  rfl

def QuotFst : Quot (r.prod s).r ⟶ Quot r.r := QuotMap _ _ (Prod.fst (α := A)) $ by
  rintro ⟨a, b⟩ ⟨x, y⟩ ⟨h, -⟩
  exact h

def QuotSnd : Quot (r.prod s).r ⟶ Quot s.r := QuotMap _ _ (Prod.snd (β := B)) $ by
  rintro ⟨a, b⟩ ⟨x, y⟩ ⟨-, h⟩
  exact h

lemma ProdQuot_Final :
    Final (⟨Quot (r.prod s).r, QuotFst _ _, QuotSnd _ _⟩ :
      (Σ (Z : Type u), (Z ⟶ Quot r.r) × (Z ⟶ Quot s.r))) :=
  λ ⟨Z, f, g⟩ => ⟨⟨
    λ z => Quot.lift₂ (λ a b => Quot.mk _ ⟨a, b⟩)
    (λ _ _ _' h => Quot.sound ⟨r.refl _, h⟩) (λ _ _ _ h => Quot.sound ⟨h, s.refl _⟩) (f z) (g z),
    by
      funext a
      simp only [QuotFst, types_comp_apply]
      induction' f a using Quot.induction_on
      induction' g a using Quot.induction_on
      simp
    , by
      funext a
      simp only [QuotSnd, types_comp_apply]
      induction' f a using Quot.induction_on
      induction' g a using Quot.induction_on
      simp⟩,
    λ ⟨w, hw, hw'⟩ => by
      refine' Subtype.ext _
      dsimp only at hw hw'
      funext z
      simp only [←hw, ←hw', types_comp_apply]
      induction' w z using Quot.induction_on with z
      rcases z with ⟨a, b⟩
      simp [QuotFst, QuotSnd]⟩

end exercise511

-- 5.12. Define the notions of fibered products and fibered coproducts, as terminal objects of the
-- categories C_α,β, C^α,β considered in Example 3.10 (cf. also Exercise 3.11),
-- by stating carefully the corresponding universal properties.
-- As it happens, Set has both fibered products and coproducts.
-- Define these objects `concretely', in terms of naive yet theory. [III.6.10, III.6.11]

instance example310_down {D : Type _} [hD : Category D] {A B C : D} (α : A ⟶ C) (β : B ⟶ C) :
    Category (Σ (Z : D), {fg : hD.Hom Z A × hD.Hom Z B // fg.fst ≫ α = fg.snd ≫ β}) where
  Hom := λ ⟨Z₁, ⟨f₁, g₁⟩, _⟩ ⟨Z₂, ⟨f₂, g₂⟩, _⟩ => {σ : Z₁ ⟶ Z₂ // σ ≫ f₂ = f₁ ∧ σ ≫ g₂ = g₁}
  id _ := ⟨𝟙 _, hD.id_comp _, hD.id_comp _⟩
  comp := λ ⟨f, hf⟩ ⟨g, hg⟩ => ⟨f ≫ g,
    by rw [hD.assoc, hg.left, ←hf.left],
    by rw [hD.assoc, hg.right, ←hf.right]⟩
  id_comp := by
    intros
    exact Subtype.ext (hD.id_comp _)
  comp_id := by
    intros
    exact Subtype.ext (hD.comp_id _)
  assoc := by
    intros
    exact Subtype.ext (hD.assoc _ _ _)

instance example310_up {D : Type _} [hD : Category D] {A B C : D} (α : C ⟶ A) (β : C ⟶ B) :
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

class HasFiberedProducts {D : Type _} [hD : Category D] {A B C : D} (α : A ⟶ C) (β : B ⟶ C) where
  HasFinal : ∃ (F : (Σ (Z : D), {fg : hD.Hom Z A × hD.Hom Z B // fg.fst ≫ α = fg.snd ≫ β})), Nonempty (Final F)

class HasFiberedCoproducts {D : Type _} [hD : Category D] {A B C : D} (α : C ⟶ A) (β : C ⟶ B) where
  hasInitial : ∃ (I : (Σ (Z : D), {fg : hD.Hom A Z × hD.Hom B Z // α ≫ fg.fst = β ≫ fg.snd})), Nonempty (Initial I)

def FProd_Final {A B C : Type u} (f : A ⟶ C) (g : B ⟶ C) :
    Final (C := (Σ (Z : Type u), {fg : (Z ⟶ A) × (Z ⟶ B) // fg.fst ≫ f = fg.snd ≫ g}))
    ⟨{xy : A × B // f xy.fst = g xy.snd}, ⟨Subtype.val ≫ Prod.fst, Subtype.val ≫ Prod.snd⟩,
    funext $ λ x => x.prop⟩ :=
  λ ⟨_, ⟨f', g'⟩, h⟩ => ⟨⟨λ z => ⟨⟨f' z, g' z⟩, congr_fun h z⟩, funext λ _ => rfl,
    funext λ _ => rfl⟩, λ ⟨_, hu, hu'⟩ =>
    Subtype.ext (funext λ _ => Subtype.ext (Prod.ext (congr_fun hu _) (congr_fun hu' _)))⟩

instance exercise512_down {A B C : Type u} (f : A ⟶ C) (g : B ⟶ C) :
    HasFiberedProducts f g where
  HasFinal := ⟨_, ⟨FProd_Final f g⟩⟩

noncomputable -- needs Sum.rec to be computable
def FCoprod_Initial {A B C : Type u} (f : C ⟶ A) (g : C ⟶ B) :
    Initial (C := (Σ (Z : Type u), {fg : (A ⟶ Z) × (B ⟶ Z) // f ≫ fg.fst = g ≫ fg.snd}))
    ⟨Quot (λ (a b : A ⊕ B) => a = b ∨ ∃ c : C, (a= Sum.inl (f c) ∧ b = Sum.inr (g c)) ∨
        (a = Sum.inr (g c) ∧ b = Sum.inl (f c))),
    ⟨Sum.inl ≫ Quot.mk _, Sum.inr ≫ Quot.mk _⟩,
     funext λ z => Quot.sound (Or.inr ⟨z, Or.inl ⟨rfl, rfl⟩⟩)⟩ :=
  λ ⟨Z, ⟨u, v⟩, h⟩ => ⟨⟨Quot.lift (Sum.rec u v) $ by
      rintro ab ab' (rfl|⟨c, (⟨rfl, rfl⟩|⟨rfl, rfl⟩)⟩)
      · rfl
      · exact congr_fun h _
      · exact congr_fun h.symm _,
    funext λ _ => by rfl,
    funext λ _ => by rfl⟩,
  λ w => Subtype.ext (funext λ c => Quot.inductionOn c $ by
    rintro (a|b)
    · exact congr_fun w.prop.left a
    · exact congr_fun w.prop.right b)⟩

instance exercise512_up {A B C : Type u} (f : C ⟶ A) (g : C ⟶ B) :
    HasFiberedCoproducts f g where
  hasInitial := ⟨_, ⟨FCoprod_Initial f g⟩⟩
