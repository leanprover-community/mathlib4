module

public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.RepresentationTheory.Action
public import Mathlib.CategoryTheory.Action.Monoidal

@[expose] public section

universe w w' u u' v v'

open CategoryTheory

set_option backward.privateInPublic true in
structure Rep (k : Type u) (G : Type v) [Semiring k] [Monoid G] where
  private mk ::
  V : Type w
  [hV1 : AddCommGroup V]
  [hV2 : Module k V]
  ρ : Representation k G V

namespace Rep

noncomputable section

section semiring

variable {k : Type u} {G : Type v} [Semiring k] [Monoid G]

attribute [instance] hV1 hV2

initialize_simps_projections Rep (-hV1, -hV2)

instance : CoeSort (Rep k G) (Type w) := ⟨Rep.V⟩

attribute [coe] V

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
abbrev of {X : Type w} [AddCommGroup X] [Module k X] (ρ : Representation k G X) :
  Rep.{w} k G := ⟨X, ρ⟩

lemma of_V (X : Type w) [AddCommGroup X] [Module k X] (ρ : Representation k G X) :
  (of ρ).V = X := by with_reducible rfl

lemma of_ρ (X : Type w) [AddCommGroup X] [Module k X] (ρ : Representation k G X) :
  (of ρ).ρ = ρ := by with_reducible rfl

set_option backward.privateInPublic true in
/-- The type of morphisms in `Rep.{w} k G`. -/
@[ext]
structure Hom (A B : Rep.{w} k G) where
  private mk ::
  /-- The underlying algebra map. -/
  hom' : A.ρ.IntertwiningMap B.ρ

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : Category (Rep.{w} k G) where
  Hom A B := Hom A B
  id A := ⟨.id A.ρ⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : ConcreteCategory (Rep k G) (fun A B ↦ A.ρ.IntertwiningMap B.ρ) where
  hom := Hom.hom'
  ofHom := Hom.mk

variable (A B C : Rep.{w} k G)

variable {A B} in
/-- Turn a morphism in `CommAlgCat` back into an `AlgHom`. -/
abbrev Hom.hom (f : Hom A B) := ConcreteCategory.hom (C := Rep k G) f

variable {A B} in
/-- Typecheck an `AlgHom` as a morphism in `CommAlgCat`. -/
abbrev ofHom {X Y : Type w} [AddCommGroup X] [AddCommGroup Y] [Module k X] [Module k Y]
  {σ : Representation k G X} {ρ : Representation k G Y}
  (f : σ.IntertwiningMap ρ) : of σ ⟶ of ρ :=
  ConcreteCategory.ofHom (C := Rep.{w} k G) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (A B : Rep.{w} k G) (f : Hom A B) := f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp] lemma hom_id : (𝟙 A : A ⟶ A).hom = .id A.ρ := rfl

/- Provided for rewriting. -/
lemma id_apply (A : Rep k G) (a : A) : (𝟙 A : A ⟶ A) a = a := by
  simp [Representation.IntertwiningMap.id]

@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
variable {A B C} in
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp

variable {A B} in
@[ext] lemma hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g := Hom.ext hf

variable {A B} in
lemma hom_comm_apply (f : A ⟶ B) (g : G) (a : A) : f.hom (A.ρ g a) = B.ρ g (f.hom a) := by
  simpa using congr($(f.hom.2 g) a)

variable {X Y Z : Type w} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [Module k X]
  [Module k Y] [Module k Z] {σ : Representation k G X} {ρ : Representation k G Y}
  {τ : Representation k G Z}

@[simp] lemma hom_ofHom (f : σ.IntertwiningMap ρ) : (ofHom f).hom = f := rfl
@[simp] lemma ofHom_hom (f : A ⟶ B) : ofHom f.hom = f := rfl

@[simp] lemma ofHom_id : ofHom (.id σ) = 𝟙 (of σ) := rfl

@[simp]
lemma ofHom_comp (f : σ.IntertwiningMap ρ) (g : ρ.IntertwiningMap τ) :
  ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

lemma ofHom_apply (f : σ.IntertwiningMap ρ) (x : X) : ofHom f x = f x := rfl

lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv.hom (e.hom.hom x) = x := by simp

lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom.hom (e.inv.hom x) = x := by simp

instance : Inhabited (Rep.{u} k G) := ⟨of (Representation.trivial k G PUnit)⟩

lemma forget_obj (A : Rep.{w} k G) : (forget (Rep.{w} k G)).obj A = A := rfl

lemma forget_map (f : A ⟶ B) : (forget (Rep.{w} k G)).map f = (f : _ → _) := rfl

open LinearMap in
def mkIso {X Y : Type w} [AddCommGroup X] [AddCommGroup Y] [Module k X] [Module k Y]
    {σ : Representation k G X} {ρ : Representation k G Y} (e : σ.Equiv ρ) : of σ ≅ of ρ where
  hom := ofHom e.toIntertwiningMap
  inv := ofHom e.symm.toIntertwiningMap

@[simp]
lemma mkIso_hom_hom_apply {X Y : Type w} [AddCommGroup X] [AddCommGroup Y] [Module k X] [Module k Y]
    {σ : Representation k G X} {ρ : Representation k G Y} (e : σ.Equiv ρ) (x : X) :
    (mkIso e).hom.hom x = e.toLinearMap x := rfl

@[simp]
lemma mkIso_hom_hom_toLinearMap {X Y : Type w} [AddCommGroup X] [AddCommGroup Y] [Module k X]
    [Module k Y] {σ : Representation k G X} {ρ : Representation k G Y} (e : σ.Equiv ρ) :
    (mkIso e).hom.hom.toLinearMap = e.toLinearMap := rfl

@[simp]
lemma mkIso_inv_hom_toLinearMap {X Y : Type w} [AddCommGroup X] [AddCommGroup Y] [Module k X]
    [Module k Y] {σ : Representation k G X} {ρ : Representation k G Y} (e : σ.Equiv ρ) :
    (mkIso e).inv.hom.toLinearMap = e.symm.toIntertwiningMap.toLinearMap := rfl

@[simp]
lemma mkIso_hom_hom {X Y : Type w} [AddCommGroup X] [AddCommGroup Y] [Module k X] [Module k Y]
    {σ : Representation k G X} {ρ : Representation k G Y} (e : σ.Equiv ρ) :
    (mkIso e).hom.hom = e.toIntertwiningMap := rfl

abbrev mkIso' {X Y : Rep.{w} k G} (e : X.ρ.Equiv Y.ρ) : X ≅ Y := mkIso e

variable {A B} in
@[simps]
def _root_.Representation.equivOfIso (i : A ≅ B) : A.ρ.Equiv B.ρ where
  __ := i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

@[simps]
def isoEquivRepEquiv : (of A.ρ ≅ of B.ρ) ≃ (A.ρ.Equiv B.ρ) where
  toFun := Representation.equivOfIso
  invFun e := mkIso e

instance reflectsIsomorphisms_forget : (forget (Rep.{w} k G)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (Rep.{w} k G)).map f)
    let e : X.ρ.Equiv Y.ρ := { f.hom, i.toEquiv with }
    exact (mkIso e).isIso_hom

lemma hom_bijective {M N : Rep k G} :
    Function.Bijective (Rep.Hom.hom : (M ⟶ N) → (M.ρ.IntertwiningMap N.ρ)) where
  left _ _ h := Rep.hom_ext h
  right f := ⟨Rep.ofHom f, Rep.hom_ofHom f⟩

/-- Convenience shortcut for `ModuleCat.hom_bijective.injective`. -/
lemma hom_injective {M N : Rep k G} :
    Function.Injective (Hom.hom : (M ⟶ N) → (M.ρ.IntertwiningMap N.ρ)) :=
  hom_bijective.injective

/-- Convenience shortcut for `ModuleCat.hom_bijective.surjective`. -/
lemma hom_surjective {M N : Rep k G} :
    Function.Surjective (Hom.hom : (M ⟶ N) → (M.ρ.IntertwiningMap N.ρ)) :=
  hom_bijective.surjective

@[simps]
def homEquiv {M N : Rep k G} : (M ⟶ N) ≃ (M.ρ.IntertwiningMap N.ρ) where
  toFun := Hom.hom
  invFun := ofHom

instance {M N : Rep k G} : Add (M ⟶ N) where
  add f g := ofHom (f.hom + g.hom)

lemma ofHom_add {M N : Type w} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
    {σ : Representation k G M} {ρ : Representation k G N} (f g : σ.IntertwiningMap ρ) :
    ofHom (f + g) = ofHom f + ofHom g := rfl

lemma add_hom {M N : Rep k G} (f g : M ⟶ N) : (f + g).hom = f.hom + g.hom := rfl

lemma hom_comp_toLinearMap {M N O : Rep k G} (f : M ⟶ N) (g : N ⟶ O) :
    (f ≫ g).hom.toLinearMap = g.hom.toLinearMap ∘ₗ f.hom.toLinearMap := rfl

lemma add_comp {M N O : Rep k G} (f₁ f₂ : M ⟶ N) (g : N ⟶ O) :
    (f₁ + f₂) ≫ g = f₁ ≫ g + f₂ ≫ g := by
  ext1
  simp [add_hom, Representation.IntertwiningMap.add_comp]

lemma comp_add {M N O : Rep k G} (f : M ⟶ N) (g₁ g₂ : N ⟶ O) :
    f ≫ (g₁ + g₂) = f ≫ g₁ + f ≫ g₂ := by
  ext1
  simp [add_hom, Representation.IntertwiningMap.comp_add]

instance {M N : Rep k G} : Zero (M ⟶ N) where
  zero := ofHom (0 : M.ρ.IntertwiningMap N.ρ)

@[simp]
lemma ofHom_zero {M N : Type w} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
    {σ : Representation k G M} {ρ : Representation k G N} :
    ofHom (0 : σ.IntertwiningMap ρ) = 0 := rfl

@[simp]
lemma zero_hom {M N : Rep k G} : (0 : M ⟶ N).hom = 0 := rfl

instance {M N : Rep k G} : SMul ℕ (M ⟶ N) where
  smul n f := ofHom (n • f.hom)

lemma ofHom_nsmul {M N : Type w} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
    {σ : Representation k G M} {ρ : Representation k G N} (f : σ.IntertwiningMap ρ) (n : ℕ) :
    ofHom (n • f) = n • ofHom f := rfl

lemma nsmul_hom {M N : Rep k G} (f : M ⟶ N) (n : ℕ) : (n • f).hom = n • f.hom := rfl

instance {M N : Rep k G} : Neg (M ⟶ N) where
  neg f := ofHom (-f.hom)

lemma ofHom_neg {M N : Type w} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
    {σ : Representation k G M} {ρ : Representation k G N} (f : σ.IntertwiningMap ρ) :
    ofHom (-f) = -ofHom f := rfl

lemma neg_hom {M N : Rep k G} (f : M ⟶ N) : (-f).hom = -f.hom := rfl

instance {M N : Rep k G} : Sub (M ⟶ N) where
  sub f g := ofHom (f.hom - g.hom)

lemma ofHom_sub {M N : Type w} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
    {σ : Representation k G M} {ρ : Representation k G N} (f g : σ.IntertwiningMap ρ) :
    ofHom (f - g) = ofHom f - ofHom g := rfl

lemma sub_hom {M N : Rep k G} (f g : M ⟶ N) : (f - g).hom = f.hom - g.hom := rfl

instance {M N : Rep k G} : SMul ℤ (M ⟶ N) where
  smul n f := ofHom (n • f.hom)

lemma ofHom_zsmul {M N : Type w} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
    {σ : Representation k G M} {ρ : Representation k G N} (f : σ.IntertwiningMap ρ) (n : ℤ) :
    ofHom (n • f) = n • ofHom f := rfl

lemma zsmul_hom {M N : Rep k G} (f : M ⟶ N) (n : ℤ) : (n • f).hom = n • f.hom := rfl

instance : Preadditive (Rep k G) where
  homGroup A B :=
    -- hom_injective.addCommGroup _ zero_hom add_hom neg_hom sub_hom nsmul_hom zsmul_hom
    @Function.Injective.addCommGroup (A ⟶ B) (A.ρ.IntertwiningMap B.ρ) _ _ _ _ _ _ _
      Rep.Hom.hom hom_injective zero_hom add_hom neg_hom sub_hom nsmul_hom zsmul_hom
    -- sorry
  add_comp _ _ _ := add_comp
  comp_add _ _ _ := comp_add

lemma sum_hom {ι : Type u'} {M N : Rep.{w} k G} (f : ι → (M ⟶ N)) (s : Finset ι) :
    (∑ i ∈ s, f i).hom = ∑ i ∈ s, (f i).hom := by
  classical induction s using Finset.induction with
  | empty => simp
  | insert a s ha h => simp [Finset.sum_insert ha, add_hom, h]

lemma ofHom_sum {ι : Type u'} {M N : Type v'} [AddCommGroup M] [AddCommGroup N] [Module k M]
    [Module k N] {σ : Representation k G M} {ρ : Representation k G N} (f : ι → σ.IntertwiningMap ρ)
    (s : Finset ι) :
    ofHom (∑ i ∈ s, f i) = ∑ i ∈ s, ofHom (f i) := by
  classical induction s using Finset.induction with
  | empty => simp
  | insert a s ha h => simp [Finset.sum_insert ha, ofHom_add, h]

variable (k G) in
/-- The trivial `k`-linear `G`-representation on a `k`-module `V.` -/
abbrev trivial (V : Type w) [AddCommGroup V] [Module k V] : Rep k G :=
  Rep.of (Representation.trivial k G V)

-- @[simp]
lemma trivial_V {V : Type w} [AddCommGroup V] [Module k V] : (trivial k G V).V = V := rfl

lemma trivial_ρ {V : Type w} [AddCommGroup V] [Module k V] (g : G) :
    (trivial k G V).ρ g = LinearMap.id := rfl

@[simp]
lemma trivial_ρ_apply {V : Type w} [AddCommGroup V] [Module k V] (g : G) (v : V) :
    (trivial k G V).ρ g v = v := rfl

lemma ρ_mul (g1 g2 : G) : A.ρ (g1 * g2) = A.ρ g1 ∘ₗ A.ρ g2 := by ext; simp

section Commutative

variable {G : Type v} [CommMonoid G]
variable (A : Rep k G)

/-- Given a representation `A` of a commutative monoid `G`, the map `ρ_A(g)` is a representation
morphism `A ⟶ A` for any `g : G`. -/
def applyAsHom (g : G) : A ⟶ A := Rep.ofHom ⟨A.ρ g, by simp [← ρ_mul, mul_comm]⟩

@[simp]
lemma applyAsHom_apply {A : Rep k G} (g : G) (x : A) : (A.applyAsHom g).hom x = A.ρ g x := rfl

@[reassoc, elementwise]
lemma applyAsHom_comm {A B : Rep k G} (f : A ⟶ B) (g : G) :
    A.applyAsHom g ≫ f = f ≫ B.applyAsHom g := by
  ext; simp [hom_comm_apply, Representation.IntertwiningMap.toLinearMap_apply]

end Commutative


end semiring

section ring

variable {k : Type u} {G : Type v} [Ring k] [Monoid G]

section setup

variable (k G)

/-- Given a `G`-action on `H`, this is `k[H]` bundled with the natural representation
`G →* End(k[H])` as a term of type `Rep k G`. -/
abbrev ofMulAction (H : Type w') [MulAction G H] : Rep k G :=
  of <| Representation.ofMulAction k G H

-- def ofMulAction.equivFinsupp (H : Type w') [MulAction G H] :
--   ofMulAction k G H ≃ₗ[k] (H →₀ k) := .refl _ _

-- variable {k} in
-- def ofMulAction.single {H : Type w'} [MulAction G H] (g : H) :
--     k →ₗ[k] ofMulAction k G H := Finsupp.lsingle g

-- lemma ofMulAction.single_def {H : Type w'} [MulAction G H] (g : H) (x : k) :
--     ofMulAction.single G g x = Finsupp.single g x := rfl

-- set_option backward.isDefEq.respectTransparency false in
-- @[simp]
-- lemma ofMulAction.ρ_single (H : Type w') [MulAction G H] (g : G) (h : H) (x : k) :
--     (ofMulAction k G H).ρ g (ofMulAction.single G h x) = ofMulAction.single G (g • h) x := by
--   simp [ofMulAction, ofMulAction.single]

-- @[simp]
-- lemma ofMulAction.ρ_comp_single (H : Type w') [MulAction G H] (g : G) (h : H) :
--     (ofMulAction k G H).ρ g ∘ₗ ofMulAction.single G h = ofMulAction.single G (g • h) :=
--   LinearMap.ext (by simp)

-- @[simp]
-- lemma ofMulAction.equivFinsupp_single (H : Type w') [MulAction G H] (h : H) (x : k) :
--     ofMulAction.equivFinsupp k G H (ofMulAction.single G h x) = .single h x := rfl

-- @[simp]
-- lemma ofMulAction.equivFinsupp_symm_single (H : Type w') [MulAction G H] (h : H) (x : k) :
--     (ofMulAction.equivFinsupp k G H).symm (.single h x) = ofMulAction.single G h x := rfl

-- @[ext high]
-- lemma ofMulAction.hom_ext {H : Type w'} [MulAction G H]
--     {M : Type*} [AddCommGroup M] [Module k M]
--     (l₁ l₂ : ofMulAction k G H →ₗ[k] M) (heq : ∀ g, l₁ ∘ₗ single G g = l₂ ∘ₗ single G g) :
--     l₁ = l₂ := Finsupp.lhom_ext' heq

/-- The `k`-linear `G`-representation on `k[G]`, induced by left multiplication. -/
abbrev leftRegular : Rep k G :=
  ofMulAction k G G

/-- The `k`-linear `G`-representation on `k[Gⁿ]`, induced by left multiplication. -/
abbrev diagonal (n : ℕ) : Rep k G :=
  ofMulAction k G (Fin n → G)

/-- The natural isomorphism between the representations on `k[G¹]` and `k[G]` induced by left
multiplication in `G`. -/
abbrev diagonalOneIsoLeftRegular :
    diagonal k G 1 ≅ leftRegular k G := Rep.mkIso (Representation.diagonalOneEquivLeftRegular k G)
  -- .mk' (ofMulAction.equivFinsupp _ _ _ ≪≫ₗ Finsupp.domLCongr (Equiv.funUnique (Fin 1) G) ≪≫ₗ
  --   (ofMulAction.equivFinsupp _ _ _).symm) fun g ↦ by ext; simp


set_option backward.isDefEq.respectTransparency false in
/-- When `H = {1}`, the `G`-representation on `k[H]` induced by an action of `G` on `H` is
isomorphic to the trivial representation on `k`. -/
abbrev ofMulActionSubsingletonIsoTrivial
    (H : Type u) [Subsingleton H] [MulOneClass H] [MulAction G H] :
    ofMulAction k G H ≅ trivial k G k :=
  mkIso <| Representation.ofMulActionSubsingletonEquivTrivial k G H
  -- letI : Unique H := uniqueOfSubsingleton 1
  -- mkIso' <| .mk' (ofMulAction.equivFinsupp _ _ _ ≪≫ₗ Finsupp.LinearEquiv.finsuppUnique _ _ _)
  --   fun g ↦ by ext x; simp [Subsingleton.elim (g • x) x]

section

variable (A : Type w') [AddCommGroup A] [Module k A] [DistribMulAction G A] [SMulCommClass G k A]

/-- Turns a `k`-module `A` with a compatible `DistribMulAction` of a monoid `G` into a
`k`-linear `G`-representation on `A`. -/
def ofDistribMulAction : Rep k G := Rep.of (Representation.ofDistribMulAction k G A)

@[simp] theorem ofDistribMulAction_ρ_apply_apply (g : G) (a : A) :
    (ofDistribMulAction k G A).ρ g a = g • a := rfl

/-- Given an `R`-algebra `S`, the `ℤ`-linear representation associated to the natural action of
`S ≃ₐ[R] S` on `S`. -/
@[simp] def ofAlgebraAut (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    Rep ℤ (S ≃ₐ[R] S) := ofDistribMulAction ℤ (S ≃ₐ[R] S) S

end

section
variable (M G : Type*) [Monoid M] [CommGroup G] [MulDistribMulAction M G]

/-- Turns a `CommGroup` `G` with a `MulDistribMulAction` of a monoid `M` into a
`ℤ`-linear `M`-representation on `Additive G`. -/
def ofMulDistribMulAction : Rep ℤ M := Rep.of (Representation.ofMulDistribMulAction M G)

variable {G M}

/-- Unfolds `ofMulDistribMulAction`; useful to keep track of additivity. -/
@[simps!]
def toAdditive : ofMulDistribMulAction M G ≃+ Additive G := AddEquiv.refl _

@[simp] theorem ofMulDistribMulAction_ρ_apply_apply (g : M) (a : Additive G) :
    (ofMulDistribMulAction M G).ρ g a = Additive.ofMul (g • a.toMul) := rfl

/-- Given an `R`-algebra `S`, the `ℤ`-linear representation associated to the natural action of
`S ≃ₐ[R] S` on `Sˣ`. -/
@[simp] def ofAlgebraAutOnUnits (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    Rep ℤ (S ≃ₐ[R] S) := Rep.ofMulDistribMulAction (S ≃ₐ[R] S) Sˣ

end

variable {k G}

-- set_option backward.isDefEq.respectTransparency false in
-- /-- Given an element `x : A`, there is a natural morphism of representations `k[G] ⟶ A` sending
-- `g ↦ A.ρ(g)(x).` -/
-- def leftRegularHom (A : Rep k G) (x : A) : leftRegular k G ⟶ A :=
--   Rep.ofHom (σ := (leftRegular k G).ρ) (ρ := A.ρ) ⟨(Finsupp.lift A k G fun g ↦ A.ρ g x) ∘ₗ
--     (ofMulAction.equivFinsupp k G G).toLinearMap, fun g ↦ by ext; simp⟩

-- set_option backward.isDefEq.respectTransparency false in
-- @[simp]
-- theorem leftRegularHom_hom_single {A : Rep k G} (g : G) (x : A) (r : k) :
--     (leftRegularHom A x).hom (ofMulAction.single G g r) = r • A.ρ g x := by
--   simp [leftRegularHom]


end setup

section Commutative

variable {G : Type v} [CommMonoid G]
variable (A : Rep k G)

/-- Given a `k`-linear `G`-representation `(V, ρ)`, this is the representation defined by
restricting `ρ` to a `G`-invariant `k`-submodule of `V`. -/
abbrev subrepresentation (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    Rep k G := Rep.of (A.ρ.subrepresentation W le_comap)

/-- The natural inclusion of a subrepresentation into the ambient representation. -/
@[simps!]
def subtype (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    subrepresentation A W le_comap ⟶ A := Rep.ofHom ⟨W.subtype, fun _ ↦ rfl⟩

/-- Given a `k`-linear `G`-representation `(V, ρ)` and a `G`-invariant `k`-submodule `W ≤ V`, this
is the representation induced on `V ⧸ W` by `ρ`. -/
abbrev quotient (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    Rep k G := Rep.of (A.ρ.quotient W le_comap)

/-- The natural projection from a representation to its quotient by a subrepresentation. -/
@[simps!]
def mkQ (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    A ⟶ quotient A W le_comap := Rep.ofHom ⟨W.mkQ, fun _ ↦ rfl⟩

end Commutative

variable (k G) in
/-- The functor equipping a module with the trivial representation. -/
@[simps! obj_V map_hom]
def trivialFunctor : ModuleCat k ⥤ Rep k G where
  obj V := trivial k G V
  map f := ofHom ⟨f.hom, fun _ ↦ rfl⟩

/-- A predicate for representations that fix every element. -/
abbrev IsTrivial (A : Rep k G) := A.ρ.IsTrivial

instance (X : ModuleCat k) : ((trivialFunctor k G).obj X).IsTrivial where

instance {V : Type u} [AddCommGroup V] [Module k V] :
    IsTrivial (Rep.trivial k G V) where

instance {V : Type u} [AddCommGroup V] [Module k V] (ρ : Representation k G V) [ρ.IsTrivial] :
    IsTrivial (Rep.of ρ) where
  out := Representation.isTrivial_def ρ

instance {H V : Type u} [Group H] [AddCommGroup V] [Module k V] (ρ : Representation k H V)
    (f : G →* H) [Representation.IsTrivial (ρ.comp f)] :
    Representation.IsTrivial ((Rep.of ρ).ρ.comp f) := ‹_›

variable {A B C : Rep.{w} k G}

instance hasForgetToModuleCat :
    HasForget₂ (Rep.{w} k G) (ModuleCat.{w} k) where
  forget₂.obj A := .of k A
  forget₂.map f := ModuleCat.ofHom f.hom.toLinearMap

abbrev Hom.toModuleCatHom (f : A ⟶ B) : ModuleCat.of k A.V ⟶ ModuleCat.of k B.V :=
  ModuleCat.ofHom f.hom.toLinearMap

@[simp] lemma forget₂_moduleCat_obj (A : Rep.{w} k G) :
    (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)).obj A = .of k A := rfl

@[simp] lemma forget₂_moduleCat_map (f : A ⟶ B) :
    (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)).map f = ModuleCat.ofHom f.hom.toLinearMap := rfl

instance : (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)).Faithful := inferInstance

section Action

variable (k G)

@[simps]
def RepToAction : Rep.{w} k G ⥤ Action (ModuleCat.{w} k) G where
  obj X := ⟨.of k X, (ModuleCat.endRingEquiv (.of k X)).symm.toMonoidHom.comp X.ρ⟩
  map f := ⟨ModuleCat.ofHom f.hom.toLinearMap, fun g ↦ ModuleCat.hom_ext <| by
    simp [ModuleCat.endRingEquiv, f.hom.2]⟩

lemma RepToAction_obj (X : Rep.{w} k G) : (RepToAction k G).obj X =
  ⟨.of k X, (ModuleCat.endRingEquiv (.of k X)).symm.toMonoidHom.comp X.ρ⟩ := rfl

@[simps]
def ActionToRep : Action (ModuleCat.{w} k) G ⥤ Rep.{w} k G where
  obj X := of <| (ModuleCat.endRingEquiv X.V).toMonoidHom.comp X.ρ
  map f := ofHom ⟨f.hom.hom, fun g ↦ by simpa using ModuleCat.hom_ext_iff.1 (f.comm g)⟩

set_option backward.isDefEq.respectTransparency false in
def RepToAction_ActionToRep (A : Action (ModuleCat.{w} k) G) :
    (RepToAction k G).obj ((ActionToRep k G).obj A) ≅ A where
  hom := ⟨𝟙 _, fun g ↦ by rfl⟩
  inv := ⟨𝟙 _, fun g ↦ by rfl⟩

def ActionToRep_RepToAction (X : Rep.{w} k G) :
    (ActionToRep k G).obj ((RepToAction k G).obj X) ≅ X where
  hom := ofHom ⟨LinearMap.id, fun g ↦ by
    simp only [RepToAction_obj_V_carrier, RepToAction_obj_V_isModule, RingHom.toMonoidHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, RepToAction_obj_ρ]
    convert_to LinearMap.id ∘ₗ X.ρ g = X.ρ g ∘ₗ LinearMap.id
    simp⟩
  inv := ofHom ⟨LinearMap.id, fun g ↦ by
    simp only [RepToAction_obj_V_carrier, RepToAction_obj_V_isModule, RingHom.toMonoidHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, RepToAction_obj_ρ]
    convert_to LinearMap.id ∘ₗ X.ρ g = X.ρ g ∘ₗ LinearMap.id
    simp⟩

def repIsoAction : Rep.{w} k G ≌ Action (ModuleCat.{w} k) G where
  functor := RepToAction k G
  inverse := ActionToRep k G
  unitIso := NatIso.ofComponents (ActionToRep_RepToAction k G)
  counitIso := NatIso.ofComponents (RepToAction_ActionToRep k G)

instance : (RepToAction k G).IsEquivalence :=
  repIsoAction k G|>.isEquivalence_functor

instance : (ActionToRep k G).IsEquivalence :=
  repIsoAction k G|>.isEquivalence_inverse

instance : (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)).Additive where
  map_add {X Y} f g := by ext1; simp [add_hom]

abbrev forgetNatIsoActionForget : forget₂ (Rep.{w} k G) (ModuleCat k) ≅ (RepToAction k G) ⋙
    Action.forget (ModuleCat k) G := .refl _

instance preservesLimits_forget :
    Limits.PreservesLimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (ModuleCat k)) :=
  Limits.preservesLimits_of_natIso (forgetNatIsoActionForget k G).symm

instance preservesColimits_forget :
    Limits.PreservesColimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (ModuleCat k)) :=
  Limits.preservesColimits_of_natIso (forgetNatIsoActionForget k G).symm

theorem epi_iff_surjective {A B : Rep k G} (f : A ⟶ B) : Epi f ↔ Function.Surjective f.hom :=
  ⟨fun _ => (ModuleCat.epi_iff_surjective ((forget₂ _ _).map f)).1 inferInstance,
  fun h => (forget₂ _ _).epi_of_epi_map ((ModuleCat.epi_iff_surjective <|
    (forget₂ _ _).map f).2 h)⟩

theorem mono_iff_injective {A B : Rep k G} (f : A ⟶ B) : Mono f ↔ Function.Injective f.hom :=
  ⟨fun _ => (ModuleCat.mono_iff_injective ((forget₂ _ _).map f)).1 inferInstance,
  fun h => (forget₂ _ _).mono_of_mono_map ((ModuleCat.mono_iff_injective <|
    (forget₂ _ _).map f).2 h)⟩

instance {A B : Rep k G} (f : A ⟶ B) [Mono f] : Mono f.toModuleCatHom :=
  inferInstanceAs <| Mono ((forget₂ _ _).map f)

instance {A B : Rep k G} (f : A ⟶ B) [Epi f] : Epi f.toModuleCatHom :=
  inferInstanceAs <| Epi ((forget₂ _ _).map f)

end Action

end ring

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

instance {M N : Rep k G} : SMul k (M ⟶ N) where
  smul r f := ofHom (r • f.hom)

lemma ofHom_smul {M N : Type w} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
    {σ : Representation k G M} {ρ : Representation k G N} (f : σ.IntertwiningMap ρ) (r : k) :
    ofHom (r • f) = r • ofHom f := rfl

lemma smul_hom {M N : Rep k G} (f : M ⟶ N) (r : k) : (r • f).hom = r • f.hom := rfl

lemma smul_comp {M N O : Rep k G} (r : k) (f : M ⟶ N) (g : N ⟶ O) :
    (r • f) ≫ g = r • (f ≫ g) := by
  ext1
  simp [smul_hom, Representation.IntertwiningMap.comp_smul]

lemma comp_smul {M N O : Rep k G} (f : M ⟶ N) (r : k) (g : N ⟶ O) :
    f ≫ (r • g) = r • (f ≫ g) := by
  ext1
  simp [smul_hom, Representation.IntertwiningMap.smul_comp]

instance : Linear k (Rep k G) where
  homModule X Y := hom_injective.module _ ⟨⟨_, zero_hom⟩, add_hom⟩ <| by simp [smul_hom]
  smul_comp _ _ _ := smul_comp
  comp_smul _ _ _ := comp_smul

set_option backward.isDefEq.respectTransparency false in
instance : Functor.Linear k (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)) where
  map_smul {X Y} f r := by
    ext1;
    simp [smul_hom]

abbrev homLinearEquiv (X Y : Rep k G) : (X ⟶ Y) ≃ₗ[k] (X.ρ.IntertwiningMap Y.ρ) where
  __ := homEquiv
  map_add' := add_hom
  map_smul' _ _ := smul_hom _ _

section monoidal

open MonoidalCategory CategoryTheory Representation.IntertwiningMap
  Representation.TensorProduct

set_option backward.isDefEq.respectTransparency false in
instance : MonoidalCategory (Rep.{u} k G) where
  tensorObj X Y := of (X.ρ.tprod Y.ρ)
  whiskerLeft X _ _ f := ofHom (lTensor X.ρ f.hom)
  whiskerRight f Z := ofHom (rTensor Z.ρ f.hom)
  tensorUnit := Rep.trivial k G k
  tensorHom f g := ofHom (f.hom.tensor g.hom)
  associator X Y Z := Rep.mkIso (assoc X.ρ Y.ρ Z.ρ)
  leftUnitor X := Rep.mkIso (lid k X.ρ)
  rightUnitor X := Rep.mkIso (rid k X.ρ)
  associator_naturality _ _ _ := by ext; simp
  leftUnitor_naturality _ := by ext; simp [trivial_V]
  rightUnitor_naturality _ := by ext; simp [trivial_V]
  pentagon _ _ _ _ := by ext; simp
  triangle X Y := by ext; simp
  -- __ := Monoidal.transport (repIsoAction k G).symm

@[simp]
lemma tensorUnit_V : (𝟙_ (Rep.{u} k G)).V = k := rfl

@[simp]
lemma tensorUnit_ρ : (𝟙_ (Rep.{u} k G)).ρ = Representation.trivial k G k := rfl

@[simp]
lemma tensor_V {X Y : Rep k G} : (X ⊗ Y).V = TensorProduct k X.V Y.V := rfl

@[simp]
lemma tensor_ρ {X Y : Rep k G} : (X ⊗ Y).ρ = X.ρ.tprod Y.ρ := rfl

@[simp]
lemma hom_whiskerRight {X₁ X₂ Y : Rep k G} (f : X₁ ⟶ X₂) :
    (f ▷ Y).hom = .rTensor _ f.hom := rfl

@[simp]
lemma hom_whiskerLeft {X Y₁ Y₂ : Rep k G} (f : Y₁ ⟶ Y₂) :
    (X ◁ f).hom = .lTensor _ f.hom := rfl

@[simp]
lemma hom_tensorHom {X₁ X₂ Y₁ Y₂ : Rep k G} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g).hom = f.hom.tensor g.hom := rfl

@[simp]
lemma of_tensor {X Y : Type u} [AddCommGroup X] [AddCommGroup Y] [Module k X] [Module k Y]
    (σ : Representation k G X) (ρ : Representation k G Y) :
    of (σ.tprod ρ) = of σ ⊗ of ρ := rfl

@[simp]
lemma hom_hom_associator {X Y Z : Rep k G} : (α_ X Y Z).hom.hom =
    (Representation.TensorProduct.assoc X.ρ Y.ρ Z.ρ).toIntertwiningMap := by
  ext1
  refine TensorProduct.ext_threefold fun x y z ↦ by rfl

@[simp]
lemma hom_inv_associator {X Y Z : Rep k G} : (α_ X Y Z).inv.hom =
    (Representation.TensorProduct.assoc X.ρ Y.ρ Z.ρ).symm.toIntertwiningMap := rfl

@[simp]
lemma hom_hom_leftUnitor {X : Rep k G} : (λ_ X).hom.hom =
    (Representation.TensorProduct.lid k X.ρ).toIntertwiningMap :=
  rfl

@[simp]
lemma hom_inv_leftUnitor {X : Rep k G} : (λ_ X).inv.hom =
    (Representation.TensorProduct.lid k X.ρ).symm.toIntertwiningMap := rfl

@[simp]
lemma hom_hom_rightUnitor {X : Rep k G} : (ρ_ X).hom.hom =
    (Representation.TensorProduct.rid k X.ρ).toIntertwiningMap :=
  rfl

@[simp]
lemma hom_inv_rightUnitor {X : Rep k G} : (ρ_ X).inv.hom =
    (Representation.TensorProduct.rid k X.ρ).symm.toIntertwiningMap := rfl

instance : MonoidalPreadditive (Rep.{u} k G) where
  whiskerLeft_zero {_ _ _} := by ext1; simp
  zero_whiskerRight {_ _ _} := by ext1; simp
  whiskerLeft_add _ _ := by ext1; simp [add_hom]
  add_whiskerRight _ _ := by ext1; simp [add_hom]

instance : MonoidalLinear k (Rep.{u} k G) where
  whiskerLeft_smul _ _ _ _ _ := by ext1; simp [smul_hom]
  smul_whiskerRight _ _ _ _ _ := by ext1; simp [smul_hom]

-- instance : (repIsoAction k G).functor.Monoidal :=
--   Monoidal.instMonoidalTransportedInverseEquivalenceTransported (e := (repIsoAction k G).symm) ..

-- -- set_option maxHeartbeats 4000000 in
-- set_option backward.isDefEq.respectTransparency false in
-- instance : (repIsoAction k G).inverse.Monoidal :=
--   Monoidal.instMonoidalTransportedFunctorEquivalenceTransported (e := (repIsoAction k G).symm) ..

-- lemma repIsoAction_δ (X Y) : Functor.OplaxMonoidal.δ (repIsoAction k G).functor X Y = 𝟙 _ := rfl


instance : BraidedCategory (Rep.{u} k G) where
  braiding X Y := Rep.mkIso (Representation.TensorProduct.comm X.ρ Y.ρ)
  braiding_naturality_right _ _ _ _ := by ext1; simp [comm_comp_lTensor]
  braiding_naturality_left _ _ := by ext1; simp [comm_comp_rTensor]
  hexagon_forward _ _ _ := by
    ext : 2
    simp only [tensor_V, tensor_ρ, hom_comp, hom_hom_associator, mkIso_hom_hom, comp_toLinearMap,
      toLinearMap_assoc, toLinearMap_comm, LinearEquiv.comp_coe, hom_whiskerLeft, hom_whiskerRight,
      toLinearMap_lTensor, toLinearMap_rTensor]
    ext; simp
  hexagon_reverse X Y Z := by
    ext : 2
    simp only [tensor_V, tensor_ρ, hom_comp, hom_inv_associator, mkIso_hom_hom, comp_toLinearMap,
      assoc_symm_toLinearMap, toLinearMap_comm, LinearEquiv.comp_coe, hom_whiskerRight,
      hom_whiskerLeft, toLinearMap_rTensor, toLinearMap_lTensor, LinearMap.comp_assoc]
      -- why doesn't lTensor_toLinearMap work here?
    ext
    simp

@[simp]
lemma hom_braiding {X Y : Rep k G} : (β_ X Y).hom.hom =
    (Representation.TensorProduct.comm X.ρ Y.ρ).toIntertwiningMap := rfl

open Representation.Equiv in
instance : SymmetricCategory (Rep.{u} k G) where
  symmetry X Y := by ext1; simp [← comm_symm Y.ρ X.ρ, ← toIntertwiningMap_trans,
    trans_symm, toIntertwiningMap_refl]



end monoidal

section MonoidalClosed
open MonoidalCategory Action

variable {G : Type v} [Group G] (A B C : Rep.{w} k G)

set_option backward.isDefEq.respectTransparency false in
/-- Given a `k`-linear `G`-representation `(A, ρ₁)`, this is the 'internal Hom' functor sending
`(B, ρ₂)` to the representation `Homₖ(A, B)` that maps `g : G` and `f : A →ₗ[k] B` to
`(ρ₂ g) ∘ₗ f ∘ₗ (ρ₁ g⁻¹)`. -/
@[simps]
protected noncomputable def ihom (A : Rep k G) : Rep k G ⥤ Rep k G where
  obj B := Rep.of (Representation.linHom A.ρ B.ρ)
  map {X} {Y} f := Rep.ofHom ⟨LinearMap.llcomp k _ _ _ f.hom.toLinearMap, fun g ↦ by
    ext; simp [Representation.IntertwiningMap.toLinearMap_apply, ← hom_comm_apply]⟩
  map_id := fun _ => by ext; rfl
  map_comp := fun _ _ => by ext; rfl

@[simp] theorem ihom_obj_ρ_apply {A B : Rep k G} (g : G) (x : A →ₗ[k] B) :
    -- Hint to put this lemma into `simp`-normal form.
    DFunLike.coe (F := (Representation k G (↑A.V →ₗ[k] ↑B.V)))
    ((Rep.ihom A).obj B).ρ g x = B.ρ g ∘ₗ x ∘ₗ A.ρ g⁻¹ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Given a `k`-linear `G`-representation `A`, this is the Hom-set bijection in the adjunction
`A ⊗ - ⊣ ihom(A, -)`. It sends `f : A ⊗ B ⟶ C` to a `Rep k G` morphism defined by currying the
`k`-linear map underlying `f`, giving a map `A →ₗ[k] B →ₗ[k] C`, then flipping the arguments. -/
@[simps]
def tensorHomEquiv (A B C : Rep.{u} k G) : (A ⊗ B ⟶ C) ≃ (B ⟶ (Rep.ihom A).obj C) where
  toFun f := Rep.ofHom ⟨(TensorProduct.curry f.hom.toLinearMap).flip, fun g ↦ by
    ext x y
    simp only [tensor_V, tensor_ρ, LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
      TensorProduct.curry_apply, Representation.IntertwiningMap.toLinearMap_apply,
      Representation.linHom_apply]
    have := by simpa using (hom_comm_apply f g (A.ρ g⁻¹ y ⊗ₜ[k] x)).symm
    simp [this]⟩
  invFun f := Rep.ofHom (σ := (A ⊗ B).ρ) (ρ := C.ρ) ⟨TensorProduct.uncurry (.id k) _ _ _
    f.hom.toLinearMap.flip, fun g ↦ TensorProduct.ext' fun x y => by
    simpa using LinearMap.ext_iff.1 (hom_comm_apply f g y) (A.ρ g x)⟩
  left_inv _ := Rep.Hom.ext <| Representation.IntertwiningMap.ext <|
    TensorProduct.ext' fun _ _ => rfl

variable {A B C}

noncomputable instance : MonoidalClosed (Rep k G) where
  closed A :=
    { rightAdj := Rep.ihom A
      adj := Adjunction.mkOfHomEquiv ({
        homEquiv := Rep.tensorHomEquiv A
        homEquiv_naturality_left_symm := fun _ _ => Rep.hom_ext <|
          Representation.IntertwiningMap.ext <| TensorProduct.ext' fun _ _ => rfl
        homEquiv_naturality_right := fun _ _ => Rep.hom_ext <|
          Representation.IntertwiningMap.ext <| LinearMap.ext fun _ => LinearMap.ext fun _ => rfl})}

@[simp]
theorem ihom_obj_ρ_def (A B : Rep k G) : ((ihom A).obj B).ρ = ((Rep.ihom A).obj B).ρ :=
  rfl

@[simp]
theorem homEquiv_def (A B C : Rep k G) : (ihom.adjunction A).homEquiv B C =
    Rep.tensorHomEquiv A B C :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) _) _

@[simp]
theorem ihom_ev_app_hom (A B : Rep k G) :
    ((ihom.ev A).app B).hom.toLinearMap = (TensorProduct.uncurry (.id k) A (A →ₗ[k] B) B
      LinearMap.id.flip) := by
  ext; rfl

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem ihom_coev_app_hom (A B : Rep k G) :
    ((ihom.coev A).app B).hom.toLinearMap = (TensorProduct.mk k _ _).flip :=
  LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

/-- There is a `k`-linear isomorphism between the sets of representation morphisms `Hom(A ⊗ B, C)`
and `Hom(B, Homₖ(A, C))`. -/
def MonoidalClosed.linearHomEquiv (A B C : Rep.{u} k G) : (A ⊗ B ⟶ C) ≃ₗ[k] B ⟶ A ⟶[Rep k G] C :=
  { (ihom.adjunction A).homEquiv _ _ with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- There is a `k`-linear isomorphism between the sets of representation morphisms `Hom(A ⊗ B, C)`
and `Hom(A, Homₖ(B, C))`. -/
def MonoidalClosed.linearHomEquivComm (A B C : Rep.{u} k G) : (A ⊗ B ⟶ C) ≃ₗ[k] A ⟶ B
    ⟶[Rep k G] C :=
  Linear.homCongr k (β_ A B) (Iso.refl _) ≪≫ₗ MonoidalClosed.linearHomEquiv _ _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem MonoidalClosed.linearHomEquiv_hom (A B C : Rep.{u} k G) (f : A ⊗ B ⟶ C) :
    (MonoidalClosed.linearHomEquiv A B C f).hom.toLinearMap =
    (TensorProduct.curry f.hom.toLinearMap).flip :=
  rfl

@[simp]
theorem MonoidalClosed.linearHomEquivComm_hom (A B C : Rep.{u} k G) (f : A ⊗ B ⟶ C) :
    (MonoidalClosed.linearHomEquivComm A B C f).hom.toLinearMap =
    TensorProduct.curry f.hom.toLinearMap :=
  rfl

theorem MonoidalClosed.linearHomEquiv_symm_hom (A B C : Rep.{u} k G) (f : B ⟶ A ⟶[Rep k G] C) :
    ((MonoidalClosed.linearHomEquiv A B C).symm f).hom.toLinearMap =
      TensorProduct.uncurry (.id k) A B C f.hom.toLinearMap.flip := by
  simp [linearHomEquiv]
  rfl

theorem MonoidalClosed.linearHomEquivComm_symm_hom (A B C : Rep.{u} k G) (f : A ⟶ B ⟶[Rep k G] C) :
    ((MonoidalClosed.linearHomEquivComm A B C).symm f).hom.toLinearMap =
      TensorProduct.uncurry (.id k) A B C f.hom.toLinearMap :=
  TensorProduct.ext' fun _ _ => rfl

end MonoidalClosed

section

variable {G : Type v} [Group G] [Fintype G] (A : Rep.{w} k G)

set_option backward.isDefEq.respectTransparency false in
/-- Given a representation `A` of a finite group `G`, `norm A` is the representation morphism
`A ⟶ A` defined by `x ↦ ∑ A.ρ g x` for `g` in `G`. -/
def norm : End A := Rep.ofHom (σ := A.ρ) (ρ := A.ρ) ⟨Representation.norm A.ρ,
    fun g ↦ by ext; simp⟩

@[simp]
lemma norm_apply {x : A} : (norm A).hom x = A.ρ.norm x := rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc, elementwise]
lemma norm_comm {A B : Rep k G} (f : A ⟶ B) : f ≫ norm B = norm A ≫ f := by
  ext
  simp [Representation.IntertwiningMap.toLinearMap_apply, Representation.norm, hom_comm_apply]

/-- Given a representation `A` of a finite group `G`, the norm map `A ⟶ A` defined by
`x ↦ ∑ A.ρ g x` for `g` in `G` defines a natural endomorphism of the identity functor. -/
@[simps]
def normNatTrans : End (𝟭 (Rep k G)) where
  app := norm
  naturality _ _ := norm_comm

end

noncomputable section Linearization

variable (k G)

noncomputable section Finsupp

open Finsupp

variable (α : Type u') (A : Rep k G)

variable {k G} in
/-- The representation on `α →₀ A` defined pointwise by a representation on `A`. -/
abbrev finsupp : Rep k G :=
  Rep.of (Representation.finsupp A.ρ α)

@[simp] lemma finsupp_V : (finsupp α A).V = (α →₀ A.V) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The representation on `α →₀ k[G]` defined pointwise by the left regular representation on
`k[G]`. -/
abbrev free : Rep k G :=
  Rep.of (Representation.free k G α)

-- def free.single (i : α) : (G →₀ k) →ₗ[k] free k G α := Finsupp.lsingle i

-- lemma free.single_def (i : α) (f : G →₀ k) :
--     free.single α i f = Finsupp.single i f := rfl

-- variable (k G) in
-- def freeEquivFinsupp : free k G α ≃ₗ[k] (α →₀ G →₀ k) := .refl _ _

-- @[simp]
-- lemma freeEquivFinsupp_single (i : α) (g : G) (r : k) :
--     freeEquivFinsupp k G α (free.single α i (Finsupp.single g r)) =
--     Finsupp.single i (Finsupp.single g r) := rfl

-- @[simp]
-- lemma freeEquivFinsupp_symm_single (i : α) (g : G) (r : k) :
--     (freeEquivFinsupp k G α).symm (Finsupp.single i (Finsupp.single g r)) =
--     free.single α i (Finsupp.single g r) := rfl

-- set_option backward.isDefEq.respectTransparency false in
-- @[simp]
-- lemma free.ρ_single (i : α) (g g' : G) (r : k) :
--     (free k G α).ρ g' (free.single α i (Finsupp.single g r)) =
--     free.single α i (Finsupp.single (g' * g) r) := by
--   simp [free, free.single]

-- lemma free.single_single (i : α) (g : G) (r : k) :
--     free.single α i (Finsupp.single g r) = (freeEquivFinsupp k G α).symm
--     (Finsupp.single i (Finsupp.single g r)) := rfl

-- lemma freeEquivFinsupp_comp_single (i : α) :
--     (freeEquivFinsupp k G α).toLinearMap ∘ₗ free.single α i = Finsupp.lsingle i := by
--   ext; simp

-- @[ext high]
-- lemma free_ext {M : Type*} [AddCommGroup M] [Module k M] {f1 f2 : free k G α →ₗ[k] M}
--     (h : ∀ i, f1 ∘ₗ (free.single α i) = f2 ∘ₗ (free.single α i)) : f1 = f2 :=
--   Finsupp.lhom_ext' h

variable {α}

/-- Given `f : α → A`, the natural representation morphism `(α →₀ k[G]) ⟶ A` sending
`single a (single g r) ↦ r • A.ρ g (f a)`. -/
abbrev freeLift (f : α → A) :
    free k G α ⟶ A := Rep.ofHom (Representation.freeLift A.ρ f)

variable (α) in
/-- The natural linear equivalence between functions `α → A` and representation morphisms
`(α →₀ k[G]) ⟶ A`. -/
abbrev freeLiftLEquiv :
    (free k G α ⟶ A) ≃ₗ[k] (α → A) :=
  homLinearEquiv _ _ ≪≫ₗ Representation.freeLiftLEquiv A.ρ α

lemma free_ext (f g : free k G α ⟶ A)
    (h : ∀ i : α, f.hom (single i (single 1 1)) = g.hom (single i (single 1 1))) : f = g := by
  classical exact (freeLiftLEquiv k G α A).injective (funext_iff.2 h)

variable {A}
section

open MonoidalCategory

variable (A B : Rep.{u} k G) (α : Type u) [DecidableEq α]

open ModuleCat.MonoidalCategory

set_option backward.isDefEq.respectTransparency false in
-- set_option pp.all true in
open TensorProduct in
-- the proof below can be simplified after https://github.com/leanprover-community/mathlib4/issues/24823 is merged
/-- Given representations `A, B` and a type `α`, this is the natural representation isomorphism
`(α →₀ A) ⊗ B ≅ (A ⊗ B) →₀ α` sending `single x a ⊗ₜ b ↦ single x (a ⊗ₜ b)`. -/
abbrev finsuppTensorLeft : A.finsupp α ⊗ B ≅ (A ⊗ B).finsupp α :=
  mkIso (Representation.finsuppTensorLeft A.ρ B.ρ α)

set_option backward.isDefEq.respectTransparency false in
/-- Given representations `A, B` and a type `α`, this is the natural representation isomorphism
`A ⊗ (α →₀ B) ≅ (A ⊗ B) →₀ α` sending `a ⊗ₜ single x b ↦ single x (a ⊗ₜ b)`. -/
abbrev finsuppTensorRight : A ⊗ B.finsupp α ≅ (A ⊗ B).finsupp α :=
  mkIso (Representation.finsuppTensorRight A.ρ B.ρ α)
  -- Rep.mkIso _ _ (TensorProduct.finsuppRight k _ A B α) fun _ => by
  --   dsimp
  --   ext
  --   simp


section

variable (k G α : Type u) [DecidableEq α] [CommRing k] [Monoid G]

-- set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism sending `single g r₁ ⊗ single a r₂ ↦ single a (single g r₁r₂)`. -/
abbrev leftRegularTensorTrivialIsoFree :
    leftRegular k G ⊗ trivial k G (α →₀ k) ≅ free k G α :=
  mkIso (Representation.leftRegularTensorTrivialIsoFree α)


  -- Rep.mkIso _ _ (TensorProduct.congr (ofMulAction.equivFinsupp k G G) (.refl k _) ≪≫ₗ
  --   finsuppTensorFinsupp' k G α ≪≫ₗ Finsupp.domLCongr (Equiv.prodComm G α) ≪≫ₗ
  --   curryLinearEquiv k ≪≫ₗ (freeEquivFinsupp k G α).symm) fun g ↦ by
  -- dsimp; ext; simp

variable {α}

-- omit [DecidableEq α]

-- set_option backward.isDefEq.respectTransparency false in
-- @[simp]
-- lemma leftRegularTensorTrivialIsoFree_hom_hom_single_tmul_single (i : α) (g : G) (r s : k) :
--     (leftRegularTensorTrivialIsoFree k G α).hom.hom.toLinearMap
--       (ofMulAction.single G g r ⊗ₜ[k] single i s) =
--       free.single α i (single g (r * s)) := by
--   simp [leftRegularTensorTrivialIsoFree]

-- set_option backward.isDefEq.respectTransparency false in
-- @[simp]
-- lemma leftRegularTensorTrivialIsoFree_inv_hom_single_single (i : α) (g : G) (r : k) :
--     (leftRegularTensorTrivialIsoFree k G α).inv.hom.toLinearMap (free.single α i (single g r)) =
--       ofMulAction.single G g r ⊗ₜ[k] single i 1 := by
--   dsimp
--   suffices ofMulAction.single G g 1 ⊗ₜ[k] single i r = ofMulAction.single G g r ⊗ₜ[k] single i 1 by
--     simpa [leftRegularTensorTrivialIsoFree, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]
--   rw [← mul_one r, ← smul_eq_mul, ← Finsupp.smul_single, ← TensorProduct.smul_tmul]
--   simp [ofMulAction.single_def, (Finsupp.smul_single)]

end
end
end Finsupp

/-- The monoidal functor sending a type `H` with a `G`-action to the induced `k`-linear
`G`-representation on `k[H].` -/
@[simps]
abbrev linearization : (Action (Type w) G) ⥤ (Rep.{max w u} k G) where
  obj X := Rep.of (X := X.V →₀ k) <| Representation.linearize k G X
  map f := Rep.ofHom <| Representation.linearizeMap f
  -- Functor.mapAction (ModuleCat.free k) G


-- unif_hint (X : Action (Type u) G) (Y : Type u) where
--   X.V ≟ Y ⊢ ((linearization k G).obj X).V ≟ Y →₀ k

-- def _root_.ModuleCat.freeObjIso (X : Type u) : (ModuleCat.free k).obj X ≃ₗ[k] (X →₀ k) :=
-- LinearEquiv.refl _ _

-- @[simp]
-- lemma _root_.ModuleCat.freeObjIso_freeMk {X : Type u} (x : X) :
--     (ModuleCat.freeObjIso k X) (ModuleCat.freeMk x) = Finsupp.single x 1 := rfl

-- @[simp]
-- lemma _root_.ModuleCat.freeObjIso_symm_single {X : Type u} (x : X) :
--     (ModuleCat.freeObjIso k X).symm (Finsupp.single x 1) = ModuleCat.freeMk x := rfl

-- set_option backward.isDefEq.respectTransparency false in
-- def foo : linearization k G ≅ Functor.mapAction (ModuleCat.free k) G ⋙
--    (repIsoAction _ _).inverse := .refl _

-- lemma : foo.app _ = (ModuleCat.freeObjIso k X.V).symm _

  -- NatIso.ofComponents (fun X => Rep.mkIso (.mk' (ModuleCat.freeObjIso k X.V).symm (fun g ↦ by
  --   ext : 2; simp))) fun f ↦ by
  --   ext
  --   simp
  --   rfl
    -- simp only [linearization_obj_V, Functor.comp_obj, linearization_obj_ρ, linearization_map,
    --   Functor.mapAction_obj_V, RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, hom_comp,
    --   mkIso_hom_hom, hom_ofHom, Functor.comp_map]
    -- ext x
    -- simp only [Representation.IntertwiningMap.comp_toLinearMap, linearization_obj_V,
    --   Representation.Equiv.mk'_toLinearMap, LinearMap.coe_comp, LinearEquiv.coe_coe,
    --   Function.comp_apply, Finsupp.lsingle_apply,
    --   Representation.IntertwiningMap.toLinearMap_apply,
    --   Representation.linearize_map_toFun, Finsupp.mapDomain_single]
    -- erw? [ModuleCat.freeObjIso_symm_single]
    -- sorry

-- instance : (linearization k G).Monoidal :=
--   inferInstanceAs (Functor.mapAction (ModuleCat.free k) G ⋙ (repIsoAction _ _).inverse).Monoidal

-- example : (MonoidalCategoryStruct.tensorUnit (Action (Type u) G)) = Action.trivial G PUnit := by
--    with_reducible rfl
-- #check LinearEquiv.comp_coe

-- #check MulEquiv.coe_trans
-- #exit

open MonoidalCategory Representation.LinearizeMonoidal in
instance : (linearization k G).Monoidal where
  ε := ofHom (ε k G)
  μ X Y := ofHom (μ X Y)
  μ_natural_left f Z := hom_ext <| μ_comp_rTensor f Z
  μ_natural_right Z f := by ext1; simp [μ_comp_lTensor _]
  associativity X Y Z := by ext1; simp [μ_comp_assoc _]
  left_unitality X := hom_ext <| μ_leftUnitor X
  right_unitality X := hom_ext <| μ_rightUnitor X
  η := ofHom (η k G)
  δ X Y := ofHom (δ X Y)
  δ_natural_left f Z := hom_ext <| rTensor_comp_δ f Z
  δ_natural_right Z f := hom_ext <| lTensor_comp_δ f Z
  oplax_associativity X Y Z := hom_ext <| assoc_comp_δ X Y Z
  oplax_left_unitality X := hom_ext <| leftUnitor_δ X
  oplax_right_unitality X := hom_ext <| rightUnitor_δ X
  ε_η := hom_ext <| η_ε k G
  η_ε := hom_ext <| ε_η k G
  μ_δ X Y := hom_ext <| δ_μ (k := k) X Y
  δ_μ X Y := hom_ext <| μ_δ (k := k) X Y

variable {k G}

-- def linearizationSingle (X : Action (Type u) G) (x : X.V) :
--     k →ₗ[k] (linearization k G).obj X := Finsupp.lsingle x

-- def linearizationObjEquiv (X : Action (Type u) G) :
--     ((linearization k G).obj X).V ≃ₗ[k] (X.V →₀ k) := .refl _ _

-- @[simp]
-- lemma linearizationObjEquiv_single (X : Action (Type u) G) (x : X.V) (r : k) :
--     linearizationObjEquiv X (linearizationSingle X x r) = Finsupp.single x r := rfl

-- @[simp]
-- lemma linearizationObjEquiv_symm_single (X : Action (Type u) G) (x : X.V) (r : k) :
--     (linearizationObjEquiv X).symm (Finsupp.single x r) = linearizationSingle X x r := rfl

-- @[ext high]
-- lemma linearizationObj_ext {M : Type*} [AddCommGroup M] [Module k M] (X : Action (Type u) G)
--     {f1 f2 : (linearization k G).obj X →ₗ[k] M} (h : ∀ x, f1 ∘ₗ linearizationSingle X x =
--     f2 ∘ₗ linearizationSingle X x) : f1 = f2 :=
--   Finsupp.lhom_ext' h

-- -- theorem linearization_obj_ρ (X : Action (Type u) G) (g : G) :
-- --     ((linearization k G).obj X).ρ g = Finsupp.lmapDomain k k (X.ρ g) :=
-- --   rfl

-- @[simp]
-- theorem coe_linearization_obj_ρ (X : Action (Type u) G) (g : G) :
--     @DFunLike.coe (no_index G →* ((X.V →₀ k) →ₗ[k] (X.V →₀ k))) _
--       (fun _ => (X.V →₀ k) →ₗ[k] (X.V →₀ k)) _
--       ((linearization k G).obj X).ρ g = Finsupp.lmapDomain k k (X.ρ g) := rfl

-- @[simp]
-- theorem linearization_single (X : Action (Type u) G) (g : G) (x : X.V) (y : k) :
--     ((linearization k G).obj X).ρ g (linearizationSingle X x y) =
--       linearizationSingle X (X.ρ g x) y :=
--   Finsupp.mapDomain_single ..

-- set_option backward.isDefEq.respectTransparency false in
-- -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): helps fixing `linearizationTrivialIso` since change in behaviour of `ext`.
-- theorem linearization_comp_single (X : Action (Type u) G) (g : G) (x : X.V) :
--     (((linearization k G).obj X).ρ g) ∘ₗ (linearizationSingle X x) =
--       linearizationSingle X (X.ρ g x) :=
--   LinearMap.ext <| linearization_single X g x

-- variable {X Y : Action (Type u) G} (f : X ⟶ Y)

-- -- @[simp]
-- theorem linearization_map_hom : ((linearization k G).map f).hom.toLinearMap =
--     Finsupp.lmapDomain k k f.hom :=
--   rfl

-- @[simp]
-- lemma linearization_map_hom_single (x : X.V) (r : k) :
--     ((linearization k G).map f).hom (linearizationSingle _ x r) =
--     linearizationSingle _ (f.hom x) r :=
--   Finsupp.mapDomain_single

open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

open scoped MonoidalCategory

-- set_option backward.isDefEq.respectTransparency false in
-- @[simp]
-- theorem linearization_μ_hom (X Y : Action (Type u) G) :
--     (μ (linearization k G) X Y).hom.toLinearMap =
--       ((TensorProduct.congr (linearizationObjEquiv X) (linearizationObjEquiv Y)) ≪≫ₗ
--       finsuppTensorFinsupp' k X.V Y.V ≪≫ₗ
--       (linearizationObjEquiv (X ⊗ Y)).symm).toLinearMap :=
--   rfl

-- open TensorProduct in
-- @[simp]
-- lemma linearization_μ_apply (X Y : Action (Type u) G)
--     (x : ((linearization k G).obj X).V ⊗[k] ((linearization k G).obj Y).V) :
--     (μ (linearization k G) X Y).hom x =
--       (linearizationObjEquiv _).symm
--       (finsuppTensorFinsupp' k X.V Y.V (TensorProduct.congr (linearizationObjEquiv X)
--         (linearizationObjEquiv Y) x)) := rfl

-- set_option backward.isDefEq.respectTransparency false in
-- example (X Y : Action (Type u) G) : (X.V × Y.V) = (X.V ⊗ Y.V) := by
--    with_reducible_and_instances rfl
-- example (X Y : Action (Type u) G) : (linearization k G).obj (X ⊗ Y) = (X.V × Y.V →₀ k) := by
--   with_reducible rfl

-- set_option backward.isDefEq.respectTransparency false in
-- @[simp]
-- theorem linearization_δ_hom (X Y : Action (Type u) G) :
--     (δ (linearization k G) X Y).hom.toLinearMap =
--       (TensorProduct.congr (linearizationObjEquiv _)
--       (linearizationObjEquiv _)).symm.toLinearMap ∘ₗ
--       (finsuppTensorFinsupp' k X.V Y.V).symm.toLinearMap ∘ₗ
--       (linearizationObjEquiv _).toLinearMap := by
--   apply LinearMap.ext
--   intro x
--   apply ((TensorProduct.congr (linearizationObjEquiv X) (linearizationObjEquiv Y)) ≪≫ₗ
--       finsuppTensorFinsupp' k X.V Y.V ≪≫ₗ
--       (linearizationObjEquiv (X ⊗ Y)).symm).injective
--   simp? [-EmbeddingLike.apply_eq_iff_eq, LinearEquiv.comp_coe, -linearization_obj_V,
--     types_tensorObj_def, Action.tensorObj_V, ← (linearization_μ_apply)]
--   -- exact Iso.inv_hom_id_apply _
--   -- simp only [Action.tensorObj_V, tensor_V, linearization_obj_ρ, tensor_ρ]
--   -- exact?

--   -- refine TensorProduct.ext' fun x y ↦ ?_

--   -- apply Finsupp.linearMap_ext
--   -- apply LinearMap.ext
--   -- intro x
--   -- apply ((forget₂ _ (ModuleCat _)).mapIso <|
--   --    μIso (linearization k G) X Y).toLinearEquiv.injective
--   sorry


-- @[simp]
-- theorem linearization_δ_apply (X Y : Action (Type u) G) (x) :
--     (δ (linearization k G) X Y).hom x =
--       (TensorProduct.congr (linearizationObjEquiv _) (linearizationObjEquiv _)).symm.toLinearMap
--       ((finsuppTensorFinsupp' k X.V Y.V).symm.toLinearMap ((linearizationObjEquiv _ x))) :=
--   congr($(linearization_δ_hom X Y) x)

-- @[simp]
-- theorem linearization_ε_hom : (ε (linearization k G)).hom.toLinearMap =
--     linearizationSingle _ PUnit.unit :=
--   rfl

-- theorem linearization_η_hom_apply (r : k) :
--     (η (linearization k G)).hom (Finsupp.single PUnit.unit r) = r :=
--   (εIso (linearization k G)).hom_inv_id_apply r

variable (k G) in
/-- The linearization of a type `X` on which `G` acts trivially is the trivial `G`-representation
on `k[X]`. -/
abbrev linearizationTrivialIso (X : Type u) :
    (linearization k G).obj (Action.trivial _ X) ≅ trivial k G (X →₀ k) :=
  Rep.mkIso (Representation.linearizeTrivialIso k G X)

-- #exit
-- @[simp]
-- lemma linearizationTrivialIso_hom_single (X : Type u) (x : X) (r : k) :
--     (linearizationTrivialIso k G X).hom.hom (linearizationSingle _ x r) =
--     Finsupp.single x r := rfl

-- @[simp]
-- lemma linearizationTrivialIso_inv_single (X : Type u) (x : X) (r : k) :
--     (linearizationTrivialIso k G X).inv.hom (Finsupp.single x r) =
--     linearizationSingle _ x r := rfl

variable (k G) in
/-- The linearization of a type `H` with a `G`-action is definitionally isomorphic to the
`k`-linear `G`-representation on `k[H]` induced by the `G`-action on `H`. -/
abbrev linearizationOfMulActionIso (H : Type u) [MulAction G H] :
    (linearization k G).obj (Action.ofMulAction G H) ≅ ofMulAction k G H :=
  Rep.mkIso (Representation.linearizeOfMulActionIso k G H)

set_option backward.isDefEq.respectTransparency false in
/-- Given a `k`-linear `G`-representation `A`, there is a `k`-linear isomorphism between
representation morphisms `Hom(k[G], A)` and `A`. -/
abbrev leftRegularHomEquiv (A : Rep k G) : (leftRegular k G ⟶ A) ≃ₗ[k] A :=
  homLinearEquiv _ _ ≪≫ₗ Representation.leftRegularMapEquiv A.ρ

-- set_option backward.isDefEq.respectTransparency false in
-- theorem leftRegularHomEquiv_symm_single {A : Rep k G} (x : A) (g : G) :
--     ((leftRegularHomEquiv A).symm x).hom (ofMulAction.single G g 1) = A.ρ g x := by
--   simp

variable (k G) in
abbrev linearizationObjOfMulAction (n : ℕ) : diagonal k G n ≅ (linearization k G).obj
    (Action.diagonal G n) :=
  mkIso (Representation.linearizeDiagonalEquiv k G n)

end Linearization

end

end Rep
