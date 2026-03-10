/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.DepRewrite
public import Mathlib.Topology.Sheaves.LocalPredicate

/-!
# The structure sheaf on `PrimeSpectrum R`.

We define the structure sheaf on `TopCat.of (PrimeSpectrum R)`, for an `R`-module `M` and prove
basic properties about it. We define this as a subsheaf of the sheaf of dependent functions into the
localizations, cut out by the condition that the function must be locally equal to a quotient of
an element of `M` by an element of `R`.

Because the condition "is equal to a fraction" passes to smaller open subsets,
the subset of functions satisfying this condition is automatically a subpresheaf.
Because the condition "is locally equal to a fraction" is local,
it is also a subsheaf.

(It may be helpful to refer back to `Mathlib/Topology/Sheaves/SheafOfFunctions.lean`,
where we show that dependent functions into any type family form a sheaf,
and also `Mathlib/Topology/Sheaves/LocalPredicate.lean`, where we characterise the predicates
which pick out sub-presheaves and sub-sheaves of these sheaves.)

When `M = R`, the structure sheaf is furthermore a sheaf of commutative rings, which we bundle as
`structureSheaf : Sheaf CommRingCat (PrimeSpectrum.Top R)`.

We then obtain two key descriptions of the structure sheaf. We show that the stalks `Mₓ` is the
localization of `M` at the prime corresponding to `x`, and we show that the sections `Γ(M, D(f))`
is the localization of `M` away from `f`.

Note that the results of this file are packaged into schemes and sheaf of modules in later files,
and one usually should not directly use the results in this file to respect the abstraction
boundaries.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/


universe u

noncomputable section

variable {R M A : Type u} [CommRing R] [AddCommGroup M] [Module R M] [CommRing A] [Algebra R A]

open TopCat

open TopologicalSpace CategoryTheory Opposite

open PrimeSpectrum (basicOpen)

namespace AlgebraicGeometry

@[expose] public section Public

variable (R) in
/-- The prime spectrum as an object of `TopCat`. -/
public def PrimeSpectrum.Top : TopCat := TopCat.of (PrimeSpectrum R)

namespace StructureSheaf

variable {P : PrimeSpectrum.Top R}

variable (M P) in
/-- The type family over `PrimeSpectrum R` consisting of the localization over each point. -/
abbrev Localizations : Type u := LocalizedModule P.asIdeal.primeCompl M

/-- The predicate saying that a dependent function on an open `U` is realised as a fixed fraction
`r / s` in each of the stalks (which are localizations at various prime ideals).
-/
def IsFraction {U : Opens (PrimeSpectrum.Top R)} (f : Π x : U, Localizations M x.1) : Prop :=
  ∃ r s, ∀ x : U, ∃ hs : s ∉ x.1.asIdeal, f x = LocalizedModule.mk r ⟨s, hs⟩

variable (R M) in
/-- The predicate `IsFraction` is "prelocal",
in the sense that if it holds on `U` it holds on any open subset `V` of `U`.
-/
def isFractionPrelocal : PrelocalPredicate (Localizations (R := R) M) where
  pred {_} f := IsFraction f
  res := by rintro V U i f ⟨r, s, w⟩; exact ⟨r, s, fun x => w (i x)⟩

variable (R M) in
/-- We will define the structure sheaf as
the subsheaf of all dependent functions in `Π x : U, Localizations R x`
consisting of those functions which can locally be expressed as a ratio of
(the images in the localization of) elements of `R`.

Quoting Hartshorne:

For an open set $U ⊆ Spec A$, we define $𝒪(U)$ to be the set of functions
$s : U → ⨆_{𝔭 ∈ U} A_𝔭$, such that $s(𝔭) ∈ A_𝔭$ for each $𝔭$,
and such that $s$ is locally a quotient of elements of $A$:
to be precise, we require that for each $𝔭 ∈ U$, there is a neighborhood $V$ of $𝔭$,
contained in $U$, and elements $a, f ∈ A$, such that for each $𝔮 ∈ V, f ∉ 𝔮$,
and $s(𝔮) = a/f$ in $A_𝔮$.

Now Hartshorne had the disadvantage of not knowing about dependent functions,
so we replace his circumlocution about functions into a disjoint union with
`Π x : U, Localizations x`.
-/
def isLocallyFraction : LocalPredicate (Localizations (R := R) M) :=
  (isFractionPrelocal R M).sheafify

variable (M) in
/-- The functions satisfying `isLocallyFraction` form a submodule. -/
def sectionsSubmodule (U : (Opens (PrimeSpectrum.Top R))) :
    Submodule R (Π x : U, Localizations M x.1) where
  carrier := { f | (isLocallyFraction R M).pred f }
  add_mem' {a b} ha hb x := by
    obtain ⟨Va, ma, ia, ra, sa, wa⟩ := ha x
    obtain ⟨Vb, mb, ib, rb, sb, wb⟩ := hb x
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, sb • ra + sa • rb, sa * sb, fun x ↦ ?_⟩
    obtain ⟨hsax, hsa⟩ := wa ⟨x.1, x.2.1⟩
    obtain ⟨hsbx, hsb⟩ := wb ⟨x.1, x.2.2⟩
    exact ⟨x.1.asIdeal.primeCompl.mul_mem hsax hsbx,
      congr($hsa + $hsb).trans (LocalizedModule.mk_add_mk ..)⟩
  zero_mem' x := ⟨U, x.2, 𝟙 _, 0, 1, fun y ↦ by simp [Ideal.IsPrime.one_notMem]⟩
  smul_mem' r {a} ha x := by
    obtain ⟨V, m, i, ra, sa, wa⟩ := ha x
    exact ⟨V, m, i, r • ra, sa, fun x ↦ ⟨(wa x).1,
      congr(r • $((wa x).2)).trans (LocalizedModule.smul'_mk ..)⟩⟩

variable (A) in
/-- The functions satisfying `isLocallyFraction` form a subalgebra. -/
def sectionsSubalgebra (U : (Opens (PrimeSpectrum.Top R))) :
    Subalgebra R (Π x : U, Localizations A x.1) where
  __ := sectionsSubmodule A U
  mul_mem' {a b} ha hb x := by
    obtain ⟨Va, ma, ia, ra, sa, wa⟩ := ha x
    obtain ⟨Vb, mb, ib, rb, sb, wb⟩ := hb x
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ra * rb, sa * sb, fun x ↦ ?_⟩
    obtain ⟨hsax, hsa⟩ := wa ⟨x.1, x.2.1⟩
    obtain ⟨hsbx, hsb⟩ := wb ⟨x.1, x.2.2⟩
    exact ⟨x.1.asIdeal.primeCompl.mul_mem hsax hsbx,
      congr($hsa * $hsb).trans (LocalizedModule.mk_mul_mk ..)⟩
  algebraMap_mem' r x :=
    ⟨U, x.2, 𝟙 _, algebraMap R A r, 1, fun y ↦ ⟨by simp [Ideal.IsPrime.one_notMem], rfl⟩⟩

set_option backward.isDefEq.respectTransparency false in
variable (M) in
/-- The functions satisfying `isLocallyFraction` form a submodule. -/
def sectionsSubalgebraSubmodule (U : (Opens (PrimeSpectrum.Top R))) :
    Submodule (sectionsSubalgebra R U) (Π x : U, Localizations M x.1) where
  __ := sectionsSubmodule M U
  smul_mem' r {a} ha x := by
    obtain ⟨V, hxV, hVU, rx, rs, hr⟩ := r.2 x
    obtain ⟨W, hxW, hWU, ax, as, ha⟩ := ha x
    refine ⟨V ⊓ W, ⟨hxV, hxW⟩, homOfLE (inf_le_left.trans hVU.le), rx • ax, as * rs, fun y ↦ ?_⟩
    obtain ⟨hrsy, hry⟩ := hr ⟨y.1, y.2.1⟩
    obtain ⟨hasy, hay⟩ := ha ⟨y.1, y.2.2⟩
    exact ⟨y.1.asIdeal.primeCompl.mul_mem hasy hrsy, congr($hry • $hay)⟩

end StructureSheaf

open StructureSheaf

variable (R M) in
/-- The structure sheaf (valued in `Type`, not yet `CommRingCat`) is the subsheaf consisting of
functions satisfying `isLocallyFraction`. -/
def structureSheafInType : Sheaf (Type u) (PrimeSpectrum.Top R) :=
  subsheafToTypes (isLocallyFraction R M)

instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    AddCommGroup ((structureSheafInType R M).obj.obj U) :=
  (sectionsSubmodule M U.unop).toAddSubgroup.toAddCommGroup

instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    Module R ((structureSheafInType R M).obj.obj U) :=
  (sectionsSubmodule M U.unop).module

instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    CommRing ((structureSheafInType R A).obj.obj U) :=
  (sectionsSubalgebra A U.unop).toCommRing

instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    Algebra R ((structureSheafInType R A).obj.obj U) :=
  (sectionsSubalgebra A U.unop).algebra

local notation "Γ(" M ", " U ")" =>
  (Functor.obj (ObjectProperty.FullSubcategory.obj (structureSheafInType _ M))) (Opposite.op U)

@[simp]
lemma structureSheafInType.add_apply {U : Opens (PrimeSpectrum.Top R)} (s t : Γ(M, U)) (x : U) :
  (s + t).1 x = s.1 x + t.1 x := rfl

@[simp]
lemma structureSheafInType.mul_apply {U : Opens (PrimeSpectrum.Top R)} (s t : Γ(A, U)) (x : U) :
  (s * t).1 x = s.1 x * t.1 x := rfl

@[simp]
lemma structureSheafInType.smul_apply {U : Opens (PrimeSpectrum.Top R)}
    (r : R) (s : Γ(M, U)) (x : U) :
  (r • s).1 x = r • s.1 x := rfl

variable (R M) in
/-- The structure presheaf, valued in `ModuleCat`, constructed by dressing up the `Type`-valued
structure presheaf. -/
@[simps obj_carrier]
def structurePresheafInModuleCat : Presheaf (ModuleCat R) (PrimeSpectrum.Top R) where
  obj U := ModuleCat.of R ((structureSheafInType R M).1.obj U)
  map i := ModuleCat.ofHom
    { toFun := (structureSheafInType R M).1.map i
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

variable (R) in
/-- The structure presheaf, valued in `CommRingCat`, constructed by dressing up the `Type`-valued
structure presheaf. -/
@[simps obj_carrier]
def structurePresheafInCommRingCat : Presheaf CommRingCat (PrimeSpectrum.Top R) where
  obj U := .of ((structureSheafInType R R).1.obj U)
  map i := CommRingCat.ofHom
    { toFun := (structureSheafInType R R).1.map i
      map_add' _ _ := rfl
      map_mul' _ _ := rfl
      map_one' := rfl
      map_zero' := rfl }

set_option backward.isDefEq.respectTransparency false in
instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    Module ((structureSheafInType R R).obj.obj U) ((structureSheafInType R M).obj.obj U) :=
  inferInstanceAs (Module (sectionsSubalgebra R _) (sectionsSubalgebraSubmodule M _))

instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    IsScalarTower R ((structureSheafInType R R).obj.obj U) ((structureSheafInType R M).obj.obj U) :=
  .of_algebraMap_smul fun r m ↦ Subtype.ext <| funext fun x ↦
    IsScalarTower.algebraMap_smul (Localizations R x.1) r (m.1 x)

set_option backward.isDefEq.respectTransparency false in
variable (R M) in
/-- The structure sheaf of a module as a presheaf of modules on `Spec R`.
We will later package this into a `Scheme.Modules` in `Tilde.lean`. -/
def moduleStructurePresheaf : PresheafOfModules (structurePresheafInCommRingCat R ⋙ forget₂ _ _) :=
  letI (X : (Opens ↑(PrimeSpectrum.Top R))ᵒᵖ) :
    Module ↑((structurePresheafInCommRingCat R ⋙ forget₂ CommRingCat RingCat).obj X)
      ↑((structurePresheafInModuleCat R M ⋙ forget₂ (ModuleCat R) Ab).obj X) := by
    dsimp; infer_instance
  .ofPresheaf (structurePresheafInModuleCat R M ⋙ forget₂ _ _) fun X Y f r m ↦ rfl

variable (R) in
/-- Some glue, verifying that the structure presheaf valued in `CommRingCat` agrees
with the `Type`-valued structure presheaf. -/
def structurePresheafCompForget :
    structurePresheafInCommRingCat R ⋙ forget CommRingCat ≅ (structureSheafInType R R).1 :=
  NatIso.ofComponents fun _ => Iso.refl _

open TopCat.Presheaf

open PrimeSpectrum

open TopCat.Presheaf

namespace StructureSheaf

@[simp]
theorem res_apply (U V : Opens (PrimeSpectrum.Top R)) (i : V ⟶ U)
    (s : Γ(M, U)) (x : V) : ((structureSheafInType R M).1.map i.op s).1 x = s.1 (i x) :=
  rfl

/-- The section of `structureSheaf R` on an open `U` sending each `x ∈ U` to the element
`f/g` in the localization of `R` at `x`. -/
def const (f : M) (g : R) (U : Opens (PrimeSpectrum.Top R))
    (hu : U ≤ basicOpen g) :
    Γ(M, U) :=
  ⟨fun x => .mk f ⟨g, hu x.2⟩, fun x ↦ ⟨U, x.2, 𝟙 _, f, g, fun y ↦ ⟨hu y.2, rfl⟩⟩⟩

@[simp]
theorem const_apply (f : M) (g : R) (U : Opens (PrimeSpectrum.Top R))
    (hu : ∀ x ∈ U, g ∈ (x : PrimeSpectrum.Top R).asIdeal.primeCompl) (x : U) :
    (const f g U hu).1 x = .mk f ⟨g, hu x x.2⟩ :=
  rfl

theorem exists_const (U) (s : Γ(M, U)) (x : PrimeSpectrum.Top R)
    (hx : x ∈ U) :
    ∃ (g : R) (_ : x ∈ basicOpen g) (i : basicOpen g ≤ U) (f : M),
      const f g _ le_rfl = (structureSheafInType R M).1.map i.hom.op s := by
  obtain ⟨V, hxV, iVU, f, g, hfg⟩ := s.2 ⟨x, hx⟩
  obtain ⟨_, ⟨_, ⟨g', rfl⟩, rfl⟩, hxg', hg'U⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxV V.2
  refine ⟨g' * g, ?_, ?_, g' • f, Subtype.ext <| funext fun ⟨y, hy⟩ ↦ ?_⟩ <;>
    simp only [PrimeSpectrum.basicOpen_mul]
  · exact ⟨hxg', (hfg ⟨x, hxV⟩).1⟩
  · exact inf_le_left.trans (hg'U.trans iVU.le)
  · rw [PrimeSpectrum.basicOpen_mul] at hy
    obtain ⟨hgy, H⟩ := hfg ⟨y, hg'U hy.1⟩
    refine (LocalizedModule.mk_eq.mpr ⟨1, ?_⟩).trans H.symm
    simp [Submonoid.smul_def, ← smul_assoc]; ring_nf

@[simp]
theorem res_const (f : M) (g : R) (U hu V hv i) :
    (structureSheafInType R M).1.map i (const f g U hu) = const f g V hv :=
  rfl

@[simp]
theorem const_zero (f : R) (U hu) : const (0 : M) f U hu = 0 :=
  Subtype.ext <| funext fun x ↦ by simp; rfl

@[simp]
theorem const_algebraMap (f : R) (U hu) : const (algebraMap R A f) f U hu = 1 :=
  Subtype.ext <| funext fun _ ↦ (LocalizedModule.mk_eq.mpr
      ⟨1, by simp [Algebra.smul_def, Submonoid.smul_def]⟩).trans
    OreLocalization.one_def.symm

@[simp]
theorem const_self (f : R) (U hu) : const f f U hu = 1 :=
  const_algebraMap ..

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem const_one (U) : const (1 : A) (1 : R) U (by simp) = 1 := by
  simpa using const_algebraMap 1 (A := A) U

set_option backward.isDefEq.respectTransparency false in
theorem const_add (f₁ f₂ : M) (g₁ g₂ : R) (U hu₁ hu₂) :
    const f₁ g₁ U hu₁ + const f₂ g₂ U hu₂ =
      const (g₂ • f₁ + g₁ • f₂) (g₁ * g₂) U (by simp [*, PrimeSpectrum.basicOpen_mul]) :=
  Subtype.ext <| funext fun _ ↦ LocalizedModule.mk_add_mk

theorem smul_const (f : M) (r g : R) (U hu) :
    r • const f g U hu = const (r • f) g U hu :=
  Subtype.ext <| funext fun _ ↦ LocalizedModule.smul'_mk _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem const_mul (f₁ f₂ : A) (g₁ g₂ : R) (U hu₁ hu₂) :
    const f₁ g₁ U hu₁ * const f₂ g₂ U hu₂ =
      const (f₁ * f₂) (g₁ * g₂) U (by simp [*, PrimeSpectrum.basicOpen_mul]) :=
  Subtype.ext <| funext fun _ ↦ LocalizedModule.mk_mul_mk

theorem const_ext {f₁ f₂ : M} {g₁ g₂ : R} {U hu₁ hu₂} (h : g₂ • f₁ = g₁ • f₂) :
    const f₁ g₁ U hu₁ = const f₂ g₂ U hu₂ :=
  Subtype.ext <| funext fun x ↦ LocalizedModule.mk_eq.mpr (by simp [h, Submonoid.smul_def])

theorem const_congr {f₁ f₂ : M} {g₁ g₂ : R} {U hu} (hf : f₁ = f₂) (hg : g₁ = g₂) :
    const f₁ g₁ U hu = const f₂ g₂ U (hg ▸ hu) := by substs hf hg; rfl

theorem const_mul_rev (f g : R) (U hu₁ hu₂) : const f g U hu₁ * const g f U hu₂ = 1 := by
  rw [const_mul, const_congr rfl (mul_comm g f), const_self]

theorem const_mul_cancel (f g₁ g₂ : R) (U hu₁ hu₂) :
    const f g₁ U hu₁ * const g₁ g₂ U hu₂ = const f g₂ U hu₂ := by
  rw [const_mul, const_ext]; simp; ring

theorem const_mul_cancel' (f g₁ g₂ : R) (U hu₁ hu₂) :
    const g₁ g₂ U hu₂ * const f g₁ U hu₁ = const f g₂ U hu₂ := by
  rw [mul_comm, const_mul_cancel]

theorem const_eq_const_of_smul_eq_smul (f₁ f₂ : M) (g₁ g₂ : R) (U hu₁ hu₂) (H : g₁ • f₂ = g₂ • f₁) :
    const f₁ g₁ U hu₁ = const f₂ g₂ U hu₂ :=
  Subtype.ext (funext fun x ↦ by
    simp [LocalizedModule.mk_eq, Localizations, Submonoid.smul_def, H])

set_option backward.isDefEq.respectTransparency false in
variable (R M) in
/-- The canonical linear map interpreting an element of `M` as
a section of the structure sheaf. -/
def toOpenₗ (U : Opens (PrimeSpectrum.Top R)) :
    M →ₗ[R] Γ(M, U) where
  toFun m := const m 1 U (by simp)
  map_add' _ _ := by simp [const_add]
  map_smul' _ _ := by simp [smul_const]

set_option backward.isDefEq.respectTransparency false in
theorem toOpenₗ_eq_const (U : Opens (PrimeSpectrum.Top R)) (f : M) :
    toOpenₗ R M U f = const f 1 U (by simp) := rfl

end StructureSheaf

end Public

local notation "Γ(" M ", " U ")" =>
  (Functor.obj (ObjectProperty.FullSubcategory.obj (structureSheafInType _ M))) (Opposite.op U)

namespace StructureSheaf

section basicOpen

set_option backward.isDefEq.respectTransparency false in
lemma isUnit_basicOpen (f : R) :
    IsUnit ((algebraMap R Γ(R, basicOpen f)) f) :=
  isUnit_iff_exists_inv.mpr ⟨const 1 f _ le_rfl, const_mul_rev _ _ _ (by simp) _⟩

lemma isUnit_basicOpen_end (f : R) :
    IsUnit ((algebraMap R (Module.End R Γ(M, basicOpen f))) f) := by
  have := (isUnit_basicOpen f).map
    (algebraMap _ (Module.End Γ(R, basicOpen f) Γ(M, basicOpen f)))
  rw [Module.End.isUnit_iff] at this ⊢
  convert this
  ext a
  simp

variable (R M) in
/-- The canonical linear map interpreting `s ∈ M_f` as a section of the structure sheaf
on the basic open defined by `f ∈ R`. -/
def toBasicOpenₗ (f : R) :
    LocalizedModule (.powers f) M →ₗ[R] Γ(M, PrimeSpectrum.basicOpen f) :=
  IsLocalizedModule.lift (.powers f) (LocalizedModule.mkLinearMap ..) (toOpenₗ R M _) <| by
    simp only [Subtype.forall]
    exact Submonoid.powers_le (P := (IsUnit.submonoid _).comap (algebraMap R _)).mpr
      (isUnit_basicOpen_end ..)

@[simp]
theorem toBasicOpenₗ_mk (s : R) (f : M) (g : Submonoid.powers s) :
    toBasicOpenₗ R M s (.mk f g) = const f g.1 (basicOpen s) (by
    have := PrimeSpectrum.le_basicOpen_pow s; aesop (add simp [Submonoid.mem_powers_iff])) := by
  obtain ⟨_, n, rfl⟩ := g
  apply ((Module.End.isUnit_iff _).mp ((isUnit_basicOpen_end ..).pow n)).1 ?_
  rw [← map_pow]
  dsimp [toBasicOpenₗ]
  rw [← map_smul, LocalizedModule.smul'_mk, ← Submonoid.mk_smul (S := .powers s) _ ⟨n, rfl⟩,
    LocalizedModule.mk_cancel, ← LocalizedModule.mkLinearMap_apply, IsLocalizedModule.lift_apply,
    smul_const]
  dsimp [toOpenₗ]
  exact const_eq_const_of_smul_eq_smul (H := by simp) ..

theorem toBasicOpenₗ_injective (f : R) : Function.Injective (toBasicOpenₗ R M f) := by
  intro s t h_eq
  induction s using LocalizedModule.induction_on with | h a b =>
  induction t using LocalizedModule.induction_on with | h c d =>
  suffices f ∈ ((⊥ : Submodule R M).colon {d • a - b • c}).radical by
    rw [LocalizedModule.mk_eq]
    obtain ⟨n, hn⟩ := this
    exact ⟨⟨f ^ n, n, rfl⟩, by simpa [sub_eq_zero, smul_sub] using Submodule.mem_colon.mp hn _ rfl⟩
  simp only [toBasicOpenₗ_mk] at h_eq
  rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, PrimeSpectrum.mem_vanishingIdeal]
  intro p hfp
  contrapose hfp
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp congr(($h_eq).1 ⟨p, hfp⟩)
  rw [PrimeSpectrum.mem_zeroLocus, Set.not_subset]
  exact ⟨u.1, by simpa [sub_eq_zero, smul_sub], u.2⟩

set_option backward.isDefEq.respectTransparency false in
/-
Auxiliary lemma for surjectivity of `toBasicOpen`.
A local representation of a section `s` as fractions `a i / h i` on finitely many basic opens
`basicOpen (h i)` can be "normalized" in such a way that `a i * h j = h i * a j` for all `i, j`
-/
theorem exists_le_iSup_basicOpen_and_smul_eq_smul_and_eq_const
    (U : Opens (PrimeSpectrum.Top R)) (hU : IsCompact (U : Set (PrimeSpectrum.Top R)))
    (s : Γ(M, U)) :
    ∃ (ι : Type u) (_ : Fintype ι) (a : ι → M) (b : ι → R) (ibU : ∀ i, basicOpen (b i) ≤ U),
      (U ≤ ⨆ i, basicOpen (b i)) ∧ (∀ i j, b j • a i = b i • a j) ∧
          ∀ i, (structureSheafInType R M).presheaf.map (ibU i).hom.op s =
              const (a i) (b i) _ le_rfl := by
  choose g hxg igU f H using fun x : U ↦ exists_const U s x.1 x.2
  have (i j : _) : LocalizedModule.mk (g i • f j) ⟨g i * g j, Submonoid.mem_powers _⟩ =
      LocalizedModule.mk (g j • f i) ⟨g i * g j, Submonoid.mem_powers _⟩ := by
    refine toBasicOpenₗ_injective (g i * g j) ?_
    simp only [toBasicOpenₗ_mk]
    have := H i
    trans (structureSheafInType R M).obj.map (homOfLE ?_).op s
    · refine .trans (Subtype.ext <| funext fun a ↦ ?_) congr((structureSheafInType R M).obj.map
        (homOfLE ((PrimeSpectrum.basicOpen_mul (g i) (g j)).trans_le inf_le_right)).op $(H j))
      exact LocalizedModule.mk_eq.mpr ⟨1, by simp [Submonoid.smul_def, ← smul_assoc]; ring_nf⟩
    · refine congr((structureSheafInType R M).obj.map (homOfLE ((PrimeSpectrum.basicOpen_mul (g i)
        (g j)).trans_le inf_le_left)).op $(H i)).symm.trans (Subtype.ext <| funext fun a ↦ ?_)
      exact LocalizedModule.mk_eq.mpr ⟨1, by simp [Submonoid.smul_def, ← smul_assoc]⟩
    · exact ((PrimeSpectrum.basicOpen_mul (g i) (g j)).trans_le inf_le_right).trans (igU _)
  simp only [LocalizedModule.mk_eq, Submonoid.smul_def, Subtype.exists, Submonoid.mem_powers_iff,
    exists_prop, exists_exists_eq_and, ← mul_smul, ← pow_succ, ← mul_assoc _ (_ * _)] at this
  choose n hn using this
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun i ↦ (basicOpen (g i) : Set (PrimeSpectrum R)))
    (fun _ ↦ (basicOpen _).2) (fun x hx ↦ Set.mem_iUnion_of_mem ⟨x, hx⟩ (hxg _))
  let N := (t ×ˢ t).sup fun x ↦ n x.1 x.2 + 1
  refine ⟨t, inferInstance, fun i ↦ g i ^ N • f i, fun i ↦ (g i) ^ (N + 1),
    fun x ↦ by simpa using igU x.1, fun x hx ↦ by simpa using ht hx, fun i j ↦ ?_, fun i ↦ ?_⟩
  · dsimp
    convert_to (g i * g ↑j) ^ N • g j • f i = (g i * g ↑j) ^ N • g i • f j
    · module
    · module
    have : n i j + 1 ≤ N := (t ×ˢ t).le_sup (f := fun x ↦ n x.1 x.2 + 1) (b := ⟨_, _⟩) (by simp)
    rw [← Nat.sub_add_cancel this, pow_add, mul_smul, mul_smul]
    congr 1
    convert (hn i j).symm using 1 <;> module
  · convert congr((structureSheafInType R M).presheaf.map (homOfLE ?_).op $((H i).symm)) using 1
    · refine Subtype.ext <| funext fun x ↦ LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
      simp [Submonoid.smul_def, pow_succ', mul_smul]
    · simp

set_option backward.isDefEq.respectTransparency false in
theorem toBasicOpenₗ_surjective (f : R) : Function.Surjective (toBasicOpenₗ R M f) := by
  intro s
  obtain ⟨ι, _, a, b, ibU, iU, hab, H⟩ := exists_le_iSup_basicOpen_and_smul_eq_smul_and_eq_const _
    (PrimeSpectrum.isCompact_basicOpen _) s
  obtain ⟨n, hn⟩ : f ∈ (Ideal.span (Set.range b)).radical := by
    have : PrimeSpectrum.zeroLocus (Set.range b) ⊆ PrimeSpectrum.zeroLocus {f} := by
      simpa [← SetLike.coe_subset_coe, ← Set.compl_iInter,
        ← PrimeSpectrum.zeroLocus_iUnion, PrimeSpectrum.Top] using iU
    rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, PrimeSpectrum.zeroLocus_span,
      PrimeSpectrum.mem_vanishingIdeal]
    exact fun x hx ↦ by simpa using this hx
  replace hn := Ideal.mul_mem_right f _ hn
  rw [← pow_succ, Ideal.span, Finsupp.mem_span_range_iff_exists_finsupp] at hn
  obtain ⟨c, hc⟩ := hn
  rw [Finsupp.sum_fintype _ _ (by simp)] at hc
  refine ⟨LocalizedModule.mk (∑ i, c i • a i) ⟨f ^ (n + 1), _, rfl⟩, ?_⟩
  refine (structureSheafInType R M).eq_of_locally_eq' (fun i ↦ basicOpen (b i)) _
    (fun i ↦ (ibU _).hom) iU _ _ fun i ↦ (Subtype.ext (funext fun x ↦ ?_)).trans (H _).symm
  rw [toBasicOpenₗ_mk]
  refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
  simp_rw [one_smul, Finset.smul_sum, Submonoid.smul_def, smul_comm (b i), hab _ i, ← smul_assoc,
    ← Finset.sum_smul, hc]

public instance (f : R) : IsLocalizedModule (.powers f) (toOpenₗ R M (basicOpen f)) := by
  convert IsLocalizedModule.of_linearEquiv (.powers f) (LocalizedModule.mkLinearMap (.powers f) M)
    (.ofBijective _ ⟨toBasicOpenₗ_injective _, toBasicOpenₗ_surjective _⟩)
  ext x
  simp [toOpenₗ]

instance isIso_toBasicOpenₗ (f : R) :
    IsIso (ModuleCat.ofHom (toBasicOpenₗ R M f)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr ⟨toBasicOpenₗ_injective _, toBasicOpenₗ_surjective _⟩

set_option backward.isDefEq.respectTransparency false in
public lemma toOpenₗ_top_bijective : Function.Bijective (toOpenₗ R M ⊤) := by
  have : IsLocalizedModule ⊥ (toOpenₗ R M ⊤) := by
    convert inferInstanceAs (IsLocalizedModule (.powers 1) (toOpenₗ R M (basicOpen 1)))
    rw [PrimeSpectrum.basicOpen_one, Submonoid.powers_one]
  refine ⟨fun x y e ↦ by simpa using (IsLocalizedModule.eq_iff_exists ⊥ _).mp e, fun x ↦ ?_⟩
  obtain ⟨⟨x, _, rfl⟩, rfl⟩ := IsLocalizedModule.mk'_surjective ⊥ (toOpenₗ R M ⊤) x
  exact ⟨x, (IsLocalizedModule.mk'_one ..).symm⟩

public lemma algebraMap_obj_top_bijective :
    Function.Bijective (algebraMap R Γ(R, (⊤ : Opens (PrimeSpectrum.Top R)))) :=
  toOpenₗ_top_bijective

public instance (f : R) : IsLocalization.Away f Γ(R, basicOpen f) :=
  (isLocalizedModule_iff_isLocalization' _ _).mp <|
    inferInstanceAs (IsLocalizedModule (.powers f) (toOpenₗ R R (basicOpen f)))

end basicOpen

section Stalk

variable (R) in
/-- The canonical ring homomorphism interpreting an element of `R` as an element of
the stalk of `structureSheaf R` at `x`. -/
@[expose] public def toStalk (x : PrimeSpectrum.Top R) :
    CommRingCat.of R ⟶ (structurePresheafInCommRingCat R).stalk x :=
  CommRingCat.ofHom (algebraMap _ _) ≫ (structurePresheafInCommRingCat R).germ ⊤ x trivial

set_option backward.isDefEq.respectTransparency false in
@[elementwise, reassoc]
public lemma algebraMap_germ
    (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hxU : x ∈ U) :
    CommRingCat.ofHom (algebraMap R Γ(R, U)) ≫ (structurePresheafInCommRingCat R).germ U x hxU =
      toStalk R x := by
  dsimp [toStalk]
  rw [← (structurePresheafInCommRingCat R).germ_res (homOfLE (le_top : U ≤ ⊤)) _ hxU]
  rfl

@[deprecated (since := "2026-02-10")] public alias toOpen_germ := algebraMap_germ

@[expose] public
instance (x : PrimeSpectrum.Top R) : Algebra R ((structurePresheafInCommRingCat R).stalk x) :=
  (toStalk R x).hom.toAlgebra

@[expose] public
instance (x : PrimeSpectrum.Top R) :
    Module R ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x) :=
  .compHom _ (toStalk R x).hom

variable (M) in
def germₗ (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hxU : x ∈ U) :
    Γ(M, U) →ₗ[R] ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x) where
  __ := (TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf U x hxU).hom
  map_smul' r m := by
    change _ = toStalk R x _ • TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf _ _ _ _
    rw [← algebraMap_germ_apply U x hxU]
    refine .trans ?_ (PresheafOfModules.germ_smul ..)
    congr 1
    exact (IsScalarTower.algebraMap_smul Γ(R, U) r m).symm

public
instance (x : PrimeSpectrum.Top R) :
    IsScalarTower R ((structurePresheafInCommRingCat R).stalk x)
      ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x) :=
  .of_algebraMap_smul fun _ _ ↦ rfl

variable (R M) in
def modulePresheafStalkIso (x : PrimeSpectrum.Top R) :
    ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x) ≃ₗ[R]
      (structurePresheafInModuleCat R M).stalk x where
  __ := (Limits.colimit.isoColimitCocone ⟨_, Limits.isColimitOfPreserves (forget₂ (ModuleCat R) Ab)
    (Limits.colimit.isColimit ((OpenNhds.inclusion x).op ⋙
      structurePresheafInModuleCat R M))⟩:).addCommGroupIsoToAddEquiv
  map_smul' r m := by
    let α : TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x ≅
      (forget₂ _ _).obj ((structurePresheafInModuleCat R M).stalk x) :=
      Limits.colimit.isoColimitCocone ⟨_, Limits.isColimitOfPreserves (forget₂ (ModuleCat R) Ab)
      (Limits.colimit.isColimit ((OpenNhds.inclusion x).op ⋙
        structurePresheafInModuleCat R M))⟩
    obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.germ_exist _ _ m
    have : TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf U x hxU ≫ α.hom =
        (forget₂ _ _).map ((structurePresheafInModuleCat R M).germ U x hxU) :=
      Limits.colimit.isoColimitCocone_ι_hom (C := Ab) ..
    have (m : _) : α.hom (TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf U x hxU m) =
        (structurePresheafInModuleCat R M).germ U x hxU m := congr($this m)
    change α.hom (r • germₗ M U x hxU _) =
      r • (show (structurePresheafInModuleCat R M).stalk x from _)
    rw [← map_smul]
    refine (this _).trans ?_
    dsimp [toStalk]
    erw [this]
    exact ((structurePresheafInModuleCat R M).germ U x hxU).hom.map_smul _ _

instance (x : PrimeSpectrum.Top R) :
    Module ((structurePresheafInCommRingCat R).stalk x)
      ((structurePresheafInModuleCat R M).stalk x) :=
  (modulePresheafStalkIso R M x).toAddEquiv.symm.module _

lemma toStalk_smul (x : PrimeSpectrum.Top R) (r : R)
    (m : (structurePresheafInModuleCat R M).stalk x) :
    toStalk R x r • m = r • m := by
  change modulePresheafStalkIso R M x (toStalk R x r • (modulePresheafStalkIso R M x).symm m) = _
  rw [← (modulePresheafStalkIso R M x).eq_symm_apply, map_smul]
  rfl

variable (R M) in
/-- The canonical ring homomorphism interpreting an element of `R` as an element of
the stalk of `structureSheaf R` at `x`. -/
def toStalkₗ' (x : PrimeSpectrum.Top R) :
    ModuleCat.of R M ⟶ (structurePresheafInModuleCat R M).stalk x :=
  ModuleCat.ofHom (toOpenₗ R M ⊤) ≫ (structurePresheafInModuleCat R M).germ _ x trivial

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem toOpenₗ_germ (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hx : x ∈ U) :
    ModuleCat.ofHom (toOpenₗ R M U) ≫
      (structurePresheafInModuleCat R M).germ U x hx = toStalkₗ' R M x := by
  rw [toStalkₗ', ← Presheaf.germ_res _ (homOfLE le_top) _ hx, ← Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem isUnit_toStalk (x : PrimeSpectrum.Top R) (f : R) (hf : x ∈ basicOpen f) :
    IsUnit (toStalk R x f) := by
  convert (isUnit_basicOpen f).map ((structurePresheafInCommRingCat R).germ _ x hf).hom
  exact ((structurePresheafInCommRingCat R).germ_res_apply (homOfLE (le_top : basicOpen f ≤ ⊤))
    x hf (algebraMap R Γ(R, ⊤) f)).symm

theorem isUnit_toStalkₗ' (x : PrimeSpectrum.Top R) (f : R) (hf : x ∈ basicOpen f) :
    IsUnit (algebraMap R (Module.End R ((structurePresheafInModuleCat R M).stalk x)) f) := by
  have := (isUnit_toStalk x f hf).map (algebraMap _
    (Module.End ((structurePresheafInCommRingCat R).stalk x)
      ((structurePresheafInModuleCat R M).stalk x)))
  rw [Module.End.isUnit_iff] at this ⊢
  convert this
  ext a
  simp only [Module.algebraMap_end_apply]
  rw [toStalk_smul]

variable (R M) in
/-- The canonical ring homomorphism from the localization of `R` at `p` to the stalk
of the structure sheaf at the point `p`. -/
def localizationtoStalkₗ (x : PrimeSpectrum.Top R) :
    ModuleCat.of R (LocalizedModule x.asIdeal.primeCompl M) ⟶
      (structurePresheafInModuleCat R M).stalk x :=
  ModuleCat.ofHom (IsLocalizedModule.lift x.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (toStalkₗ' R M x).hom fun f ↦ isUnit_toStalkₗ' x f.1 f.2 :)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem localizationtoStalkₗ_mk (x : PrimeSpectrum.Top R) (f : M) (s) :
    localizationtoStalkₗ R M x (.mk f s) = (structurePresheafInModuleCat R M).germ
      (PrimeSpectrum.basicOpen (s : R)) x s.2 (const f (s : R) _ fun _ ↦ id) := by
  apply ((Module.End.isUnit_iff _).mp (isUnit_toStalkₗ' _ s.1 s.2)).1 ?_
  dsimp [localizationtoStalkₗ]
  rw [← map_smul, LocalizedModule.smul'_mk, ← Submonoid.smul_def, LocalizedModule.mk_cancel,
    ← LocalizedModule.mkLinearMap_apply, IsLocalizedModule.lift_apply, ← map_smul,
    ← toOpenₗ_germ (basicOpen ↑s) _ s.2, smul_const]
  dsimp [toOpenₗ]
  congr 1
  exact const_eq_const_of_smul_eq_smul (H := by simp) ..

variable (R M) in
/-- The ring homomorphism that takes a section of the structure sheaf of `R` on the open set `U`,
implemented as a subtype of dependent functions to localizations at prime ideals, and evaluates
the section on the point corresponding to a given prime ideal. -/
def openToLocalizationₗ (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hx : x ∈ U) :
    (structurePresheafInModuleCat R M).obj (op U) ⟶
      .of R (LocalizedModule x.asIdeal.primeCompl M) :=
  ModuleCat.ofHom
  { toFun s := s.1 ⟨x, hx⟩
    map_smul' _ _ := rfl
    map_add' _ _ := rfl }

variable (R M) in
/-- The ring homomorphism from the stalk of the structure sheaf of `R` at a point corresponding to
a prime ideal `p` to the localization of `R` at `p`,
formed by gluing the `openToLocalization` maps. -/
def stalkToLocalizationₗ (x : PrimeSpectrum.Top R) :
    (structurePresheafInModuleCat R M).stalk x ⟶ .of R (LocalizedModule x.asIdeal.primeCompl M) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ structurePresheafInModuleCat R M)
    { pt := _
      ι.app U := openToLocalizationₗ R M ((OpenNhds.inclusion _).obj (unop U)) x (unop U).2 }

@[reassoc (attr := simp)]
theorem germ_stalkToLocalizationₗ
    (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hx : x ∈ U) :
    (structurePresheafInModuleCat R M).germ U x hx ≫ stalkToLocalizationₗ R M x =
      openToLocalizationₗ R M U x hx :=
  Limits.colimit.ι_desc _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem toStalkₗ'_stalkToFiberRingHom (x : PrimeSpectrum.Top R) :
    toStalkₗ' R M x ≫ stalkToLocalizationₗ R M x =
      ModuleCat.ofHom (LocalizedModule.mkLinearMap _ _) := by
  rw [toStalkₗ', Category.assoc, germ_stalkToLocalizationₗ]; rfl

open TopCat.Presheaf

set_option backward.isDefEq.respectTransparency false in
variable (R M) in
/-- The ring isomorphism between the stalk of the structure sheaf of `R` at a point `p`
corresponding to a prime ideal in `R` and the localization of `R` at `p`. -/
@[simps]
def stalkIsoₗ (x : PrimeSpectrum.Top R) :
    (structurePresheafInModuleCat R M).stalk x ≅
      .of R (LocalizedModule x.asIdeal.primeCompl M) where
  hom := stalkToLocalizationₗ R M x
  inv := localizationtoStalkₗ R M x
  hom_inv_id := by
    apply stalk_hom_ext
    intro U hxU
    ext s
    obtain ⟨g, hxg, igU, f, hs⟩ :=
      exists_const _ s x hxU
    rw [germ_stalkToLocalizationₗ_assoc, Category.comp_id, ← germ_res_apply _ igU.hom _ hxg]
    refine congr(localizationtoStalkₗ R M x (openToLocalizationₗ R M _ x hxg $hs)).symm.trans ?_
    refine (localizationtoStalkₗ_mk ..).trans
      congr((structurePresheafInModuleCat R M).germ _ x hxg $hs)
  inv_hom_id := by
    ext1
    refine IsLocalizedModule.ext x.asIdeal.primeCompl (LocalizedModule.mkLinearMap ..)
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap ..)) ?_
    ext
    dsimp [localizationtoStalkₗ]
    rw [← LocalizedModule.mkLinearMap_apply, IsLocalizedModule.lift_apply,
      elementwise_of% toStalkₗ'_stalkToFiberRingHom (M := M) x]
    simp

instance (x : PrimeSpectrum R) : IsIso (stalkToLocalizationₗ R M x) :=
  (stalkIsoₗ R M x).isIso_hom

instance (x : PrimeSpectrum R) : IsIso (localizationtoStalkₗ R M x) :=
  (stalkIsoₗ R M x).isIso_inv

@[simp, reassoc]
theorem stalkToFiberRingHom_localizationToStalk (x : PrimeSpectrum.Top R) :
    stalkToLocalizationₗ R M x ≫ localizationtoStalkₗ R M x = 𝟙 _ :=
  (stalkIsoₗ R M x).hom_inv_id

@[simp, reassoc]
theorem localizationToStalk_stalkToFiberRingHom (x : PrimeSpectrum.Top R) :
    localizationtoStalkₗ R M x ≫ stalkToLocalizationₗ R M x = 𝟙 _ :=
  (stalkIsoₗ R M x).inv_hom_id

instance (x : PrimeSpectrum.Top R) :
    IsLocalizedModule x.asIdeal.primeCompl (toStalkₗ' R M x).hom := by
  convert IsLocalizedModule.of_linearEquiv x.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M) (stalkIsoₗ R M x).toLinearEquiv.symm
  ext m
  refine .trans ?_ (localizationtoStalkₗ_mk ..).symm
  dsimp +instances [toStalkₗ', toOpenₗ]
  rw! [PrimeSpectrum.basicOpen_one]
  rfl

set_option backward.isDefEq.respectTransparency false in
variable (R M) in
/-- The canonical ring homomorphism interpreting an element of `R` as an element of
the stalk of `structureSheaf R` at `x`. -/
@[expose] public
def toStalkₗ (x : PrimeSpectrum.Top R) :
    M →ₗ[R] ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x) where
  toFun m :=
    TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf ⊤ x (by simp) (toOpenₗ R M ⊤ m)
  map_add' := by simp
  map_smul' r m := by
    change _ = toStalk R x r • TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf _ _ _ _
    rw [map_smul]
    refine .trans ?_ ((moduleStructurePresheaf R M).germ_smul ..)
    congr 1
    exact (IsScalarTower.algebraMap_smul Γ(R, _) (M := Γ(M, _)) _ _).symm

public
instance (x : PrimeSpectrum.Top R) : IsLocalizedModule x.asIdeal.primeCompl (toStalkₗ R M x) := by
  convert IsLocalizedModule.of_linearEquiv x.asIdeal.primeCompl
    (toStalkₗ' R M x).hom (modulePresheafStalkIso R M x).symm
  ext m
  let α : TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x ≅
    (forget₂ _ _).obj ((structurePresheafInModuleCat R M).stalk x) :=
    Limits.colimit.isoColimitCocone ⟨_, Limits.isColimitOfPreserves (forget₂ (ModuleCat R) Ab)
    (Limits.colimit.isColimit ((OpenNhds.inclusion x).op ⋙
      structurePresheafInModuleCat R M))⟩
  refine α.addCommGroupIsoToAddEquiv.eq_symm_apply.mpr ?_
  change α.hom _ = _
  have : TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf ⊤ x (by simp) ≫ α.hom =
      (forget₂ _ _).map ((structurePresheafInModuleCat R M).germ ⊤ x (by simp)) :=
    Limits.colimit.isoColimitCocone_ι_hom (C := Ab) ..
  exact congr($this _)

set_option backward.isDefEq.respectTransparency false in
variable (R) in
/-- The stalk of `Spec R` at `x` is isomorphic to the stalk of `R^~` at `x`. -/
@[expose] public
def commRingCatStalkEquivModuleStalk (x : PrimeSpectrum.Top R) :
    ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R R).presheaf x) ≃ₗ[R]
      (structurePresheafInCommRingCat R).stalk x where
  __ := (Limits.colimit.isoColimitCocone ⟨_, Limits.isColimitOfPreserves
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
    (Limits.colimit.isColimit ((OpenNhds.inclusion x).op ⋙
      structurePresheafInCommRingCat R))⟩).addCommGroupIsoToAddEquiv
  map_smul' r m := by
    let α : TopCat.Presheaf.stalk (moduleStructurePresheaf R R).presheaf x ≅
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj
        ((structurePresheafInCommRingCat R).stalk x) :=
      (Limits.colimit.isoColimitCocone ⟨_, Limits.isColimitOfPreserves
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
      (Limits.colimit.isColimit ((OpenNhds.inclusion x).op ⋙
        structurePresheafInCommRingCat R))⟩)
    obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.germ_exist _ _ m
    have : (TopCat.Presheaf.germ (moduleStructurePresheaf R R).presheaf U x hxU) ≫ α.hom =
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
          ((structurePresheafInCommRingCat R).germ U x hxU) :=
      Limits.colimit.isoColimitCocone_ι_hom ..
    change α.hom (r • germₗ R U x hxU _) = toStalk R _ _ * _
    rw [← map_smul, Algebra.smul_def]
    refine congr($this _).trans ?_
    refine (((structurePresheafInCommRingCat R).germ U x hxU).hom.map_mul _ _).trans ?_
    congr 1
    · dsimp [toStalk]
      erw [← (structurePresheafInCommRingCat R).germ_res_apply (homOfLE (le_top : U ≤ ⊤)) _ hxU]
      rfl
    · exact congr($this _).symm

public instance (x : PrimeSpectrum.Top R) :
    IsLocalization.AtPrime ((structurePresheafInCommRingCat R).stalk x) x.asIdeal := by
  refine (isLocalizedModule_iff_isLocalization' _ _).mp ?_
  convert IsLocalizedModule.of_linearEquiv x.asIdeal.primeCompl (toStalkₗ R R x)
    (commRingCatStalkEquivModuleStalk R x)
  let α : TopCat.Presheaf.stalk (moduleStructurePresheaf R R).presheaf x ≅
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj
      ((structurePresheafInCommRingCat R).stalk x) :=
    (Limits.colimit.isoColimitCocone ⟨_, Limits.isColimitOfPreserves
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
    (Limits.colimit.isColimit ((OpenNhds.inclusion x).op ⋙
      structurePresheafInCommRingCat R))⟩)
  have : (TopCat.Presheaf.germ (moduleStructurePresheaf R R).presheaf ⊤ x (by simp)) ≫ α.hom =
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
        ((structurePresheafInCommRingCat R).germ ⊤ x (by simp)) :=
    Limits.colimit.isoColimitCocone_ι_hom ..
  ext
  dsimp [toStalkₗ]
  simp only [map_one]
  refine .trans ?_ congr($this _).symm
  exact (((structurePresheafInCommRingCat R).germ ⊤ x (by simp)).hom.comp
    (algebraMap R Γ(R, _))).map_one.symm

variable (R) in
/-- The stalk of `Spec R` at `x` is isomorphic to `Rₚ`,
where `p` is the prime corresponding to `x`. -/
public abbrev stalkIso (x : PrimeSpectrum R) :
    Localization.AtPrime x.asIdeal ≃ₐ[R] (structurePresheafInCommRingCat R).stalk x :=
  IsLocalization.algEquiv x.asIdeal.primeCompl _ _

end Stalk

@[expose] public section StructureSheaf

variable (R)

/-- The structure sheaf on $Spec R$, valued in `CommRingCat`.

This is provided as a bundled `SheafedSpace` as `Spec.SheafedSpace R` later. -/
def _root_.AlgebraicGeometry.Spec.structureSheaf : Sheaf CommRingCat (PrimeSpectrum.Top R) :=
  ⟨structurePresheafInCommRingCat R,
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp _ _).mpr (TopCat.Presheaf.isSheaf_of_iso
      (structurePresheafCompForget R).symm (structureSheafInType R R).property)⟩

open Spec (structureSheaf)

/-- The canonical ring homomorphism interpreting an element of `R` as
a section of the structure sheaf. -/
@[deprecated "algebraMap" (since := "2026-02-10")]
def toOpen (U : Opens (PrimeSpectrum.Top R)) :
    CommRingCat.of R ⟶ (structureSheaf R).1.obj (op U) := CommRingCat.ofHom (algebraMap _ _)

@[simp]
theorem algebraMap_self_map (U V : (Opens (PrimeSpectrum.Top R))ᵒᵖ) (i : V ⟶ U) :
    CommRingCat.ofHom (algebraMap R _) ≫ (Spec.structureSheaf R).1.map i =
      CommRingCat.ofHom (algebraMap R _) :=
  rfl

@[deprecated (since := "2026-02-10")] alias toOpen_res := algebraMap_self_map

instance stalkAlgebra (p : PrimeSpectrum R) : Algebra R ((structureSheaf R).presheaf.stalk p) :=
  (toStalk R p).hom.toAlgebra

@[simp]
theorem stalkAlgebra_map (p : PrimeSpectrum R) (r : R) :
    algebraMap R ((structureSheaf R).presheaf.stalk p) r = toStalk R p r :=
  rfl

/-- Stalk of the structure sheaf at a prime p as localization of R -/
instance IsLocalization.to_stalk (p : PrimeSpectrum R) :
    IsLocalization.AtPrime ((structureSheaf R).presheaf.stalk p) p.asIdeal :=
  inferInstanceAs (IsLocalization.AtPrime ((structurePresheafInCommRingCat R).stalk p) p.asIdeal)

instance openAlgebra (U : (Opens (PrimeSpectrum R))ᵒᵖ) : Algebra R ((structureSheaf R).obj.obj U) :=
  inferInstanceAs (Algebra R ((structureSheafInType R R).presheaf.obj _))

/-- Sections of the structure sheaf of Spec R on a basic open as localization of R -/
instance IsLocalization.to_basicOpen (r : R) :
    IsLocalization.Away r ((structureSheaf R).obj.obj (op <| basicOpen r)) :=
  inferInstanceAs (IsLocalization.Away r Γ(R, basicOpen r))

instance to_basicOpen_epi (r : R) :
    Epi (CommRingCat.ofHom <|
      algebraMap R ((structureSheaf R).obj.obj (op <| basicOpen r))) :=
  ⟨fun _ _ h => CommRingCat.hom_ext (IsLocalization.ringHom_ext (Submonoid.powers r)
    (CommRingCat.hom_ext_iff.mp h))⟩

/-- The ring isomorphism between the ring `R` and the global sections `Γ(X, 𝒪ₓ)`. -/
@[simps! inv]
def globalSectionsIso : CommRingCat.of R ≅ (structureSheaf R).1.obj (op ⊤) :=
  RingEquiv.toCommRingCatIso (.ofBijective _ algebraMap_obj_top_bijective)

theorem globalSectionsIso_hom (R : CommRingCat) :
    (globalSectionsIso R).hom = CommRingCat.ofHom (algebraMap _ _) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc, elementwise nosimp]
theorem toStalk_stalkSpecializes {R : Type*} [CommRing R] {x y : PrimeSpectrum R} (h : x ⤳ y) :
    toStalk R y ≫ (structureSheaf R).presheaf.stalkSpecializes h = toStalk R x := by
  dsimp [toStalk]
  simp [structureSheaf]

end StructureSheaf

@[expose] public section Comap

variable {S : Type u} [CommRing S] {N : Type u} [AddCommGroup N] [Module S N]
  {σ : R →+* S} (f : M →ₛₗ[σ] N)

set_option backward.isDefEq.respectTransparency false in
/-- The map `M_{f y} ⟶ N_{y}` used to build maps between structure sheaves. -/
def Localizations.comapFun (y : PrimeSpectrum.Top S) :
    Localizations M (y.comap σ) →ₛₗ[σ] Localizations N y :=
  letI := Module.compHom N σ
  letI := σ.toAlgebra
  haveI : IsScalarTower R S N := .of_algebraMap_smul fun _ _ ↦ rfl
  letI f' : M →ₗ[R] N := { __ := f }
  letI g : LocalizedModule (y.comap σ).asIdeal.primeCompl M →ₗ[R]
      LocalizedModule y.asIdeal.primeCompl N :=
    IsLocalizedModule.lift (y.comap σ).asIdeal.primeCompl (LocalizedModule.mkLinearMap _ _)
      ((LocalizedModule.mkLinearMap _ _).restrictScalars R ∘ₗ f') (by
      intro x
      have := IsLocalizedModule.map_units (S := y.asIdeal.primeCompl)
        (LocalizedModule.mkLinearMap y.asIdeal.primeCompl N) ⟨σ x, x.2⟩
      rw [Module.End.isUnit_iff] at this ⊢
      convert this using 2 with a
      exact (IsScalarTower.algebraMap_smul ..).symm)
  { __ := g,
    map_smul' r x := by simpa [Localizations] using (IsScalarTower.algebraMap_smul ..).symm }

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma Localizations.comapFun_mk (y : PrimeSpectrum.Top S)
    (a : M) (b : (y.comap σ).asIdeal.primeCompl) :
    Localizations.comapFun f y (.mk a b) = .mk (f a) ⟨σ b.1, b.2⟩ := by
  letI := Module.compHom N σ
  letI := σ.toAlgebra
  haveI : IsScalarTower R S N := .of_algebraMap_smul fun _ _ ↦ rfl
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units (S := y.asIdeal.primeCompl)
    (LocalizedModule.mkLinearMap y.asIdeal.primeCompl N) ⟨σ b, b.2⟩)).1
  dsimp
  rw [← (comapFun f y).map_smulₛₗ, LocalizedModule.smul'_mk, ← Submonoid.smul_def,
    LocalizedModule.mk_cancel, ← LocalizedModule.mkLinearMap_apply]
  dsimp [comapFun, Localizations]
  refine (IsLocalizedModule.lift_apply ..).trans ?_
  dsimp
  rw [← LocalizedModule.mk_cancel ⟨σ b.1, b.2⟩, LocalizedModule.smul'_mk]
  rfl

/--
Given a ring homomorphism `f : R →+* S`, an open set `U` of the prime spectrum of `R` and an open
set `V` of the prime spectrum of `S`, such that `V ⊆ (comap f) ⁻¹' U`, we can push a section `s`
on `U` to a section on `V`, by composing with `Localization.localRingHom _ _ f` from the left and
`comap f` from the right. Explicitly, if `s` evaluates on `comap f p` to `a / b`, its image on `V`
evaluates on `p` to `f(a) / f(b)`.

At the moment, we work with arbitrary dependent functions `s : Π x : U, Localizations R x`. Below,
we prove the predicate `isLocallyFraction` is preserved by this map, hence it can be extended to
a morphism between the structure sheaves of `R` and `S`.
-/
def comapFun (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
    (hUV : V.1 ⊆ PrimeSpectrum.comap σ ⁻¹' U.1) (s : ∀ x : U, Localizations M x.1) (y : V) :
    Localizations N y.1 :=
  Localizations.comapFun f _ (s ⟨y.1.comap σ, hUV y.2⟩)

set_option backward.isDefEq.respectTransparency false in
theorem isLocallyFraction_comapFun (U : Opens (PrimeSpectrum.Top R))
    (V : Opens (PrimeSpectrum.Top S)) (hUV : V.1 ⊆ PrimeSpectrum.comap σ ⁻¹' U.1)
    (s : ∀ x : U, Localizations M x.1) (hs : (isLocallyFraction R M).toPrelocalPredicate.pred s) :
    (isLocallyFraction S N).toPrelocalPredicate.pred (comapFun f U V hUV s) := by
  letI := Module.compHom N σ
  letI := σ.toAlgebra
  haveI : IsScalarTower R S N := .of_algebraMap_smul fun _ _ ↦ rfl
  rintro ⟨p, hpV⟩
  obtain ⟨W, m, iWU, a, b, h_frac⟩ := hs ⟨PrimeSpectrum.comap σ p, hUV hpV⟩
  refine ⟨⟨_, (PrimeSpectrum.continuous_comap σ).isOpen_preimage _ W.2⟩ ⊓ V,
    ⟨m, hpV⟩, Opens.infLERight _ _, f a, σ b, ?_⟩
  rintro ⟨q, ⟨hqW, hqV⟩⟩
  obtain ⟨hs, H⟩ := h_frac ⟨PrimeSpectrum.comap σ q, hqW⟩
  refine ⟨hs, ?_⟩
  dsimp [comapFun] at H ⊢
  rw [H]
  simp

/-- For a ring homomorphism `f : R →+* S` and open sets `U` and `V` of the prime spectra of `R` and
`S` such that `V ⊆ (comap f) ⁻¹ U`, the induced ring homomorphism from the structure sheaf of `R`
at `U` to the structure sheaf of `S` at `V`.

Explicitly, this map is given as follows: For a point `p : V`, if the section `s` evaluates on `p`
to the fraction `a / b`, its image on `V` evaluates on `p` to the fraction `f(a) / f(b)`.
-/
def comapₗ (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
    (hUV : V.1 ⊆ PrimeSpectrum.comap σ ⁻¹' U.1) :
    Γ(M, U) →ₛₗ[σ] Γ(N, V) where
  toFun s := ⟨comapFun f U V hUV s.1, isLocallyFraction_comapFun f U V hUV s.1 s.2⟩
  map_add' s t := Subtype.ext <| funext fun _ ↦ by dsimp [comapFun]; rw [map_add]
  map_smul' r m := Subtype.ext <| funext fun _ ↦ by
    dsimp [comapFun]
    rw [map_smulₛₗ, ← IsScalarTower.algebraMap_smul S]

set_option backward.isDefEq.respectTransparency false in
theorem comapₗ_const (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
    (hUV : V.1 ⊆ PrimeSpectrum.comap σ ⁻¹' U.1) (a : M) (b : R) (hb : U ≤ basicOpen b) :
    comapₗ f U V hUV (const a b U hb) = const (f a) (σ b) V (hUV.trans (Set.preimage_mono hb)) :=
  Subtype.ext <| funext fun _ ↦ by simp [comapₗ, comapFun]

section Ring

open Spec (structureSheaf)

variable {S : Type u} [CommRing S] {P : Type u} [CommRing P]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem comapₗ_eq_localRingHom (f : R →+* S) (U : Opens (PrimeSpectrum.Top R))
    (V : Opens (PrimeSpectrum.Top S)) (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1)
    (s : (structureSheaf R).1.obj (op U)) (p : V) :
    (comapₗ f.toSemilinearMap U V hUV s).1 p =
      Localization.localRingHom (PrimeSpectrum.comap f p.1).asIdeal _ f rfl
        (s.1 ⟨PrimeSpectrum.comap f p.1, hUV p.2⟩) := by
  dsimp [comapₗ, comapFun]
  suffices ⇑(Localizations.comapFun f.toSemilinearMap p.1) =
      ⇑(Localization.localRingHom (PrimeSpectrum.comap f p.1).asIdeal _ f rfl) from
    congr($this _)
  ext m
  induction m using LocalizedModule.induction_on with | h m s =>
  trans LocalizedModule.mk (f m) ⟨f ↑s, s.2⟩
  · simp
  convert_to Localization.mk _ _ = Localization.localRingHom _ _ _ _ (Localization.mk _ _)
  simp [Localization.mk_eq_mk']

/-- For a ring homomorphism `f : R →+* S` and open sets `U` and `V` of the prime spectra of `R` and
`S` such that `V ⊆ (comap f) ⁻¹ U`, the induced ring homomorphism from the structure sheaf of `R`
at `U` to the structure sheaf of `S` at `V`.

Explicitly, this map is given as follows: For a point `p : V`, if the section `s` evaluates on `p`
to the fraction `a / b`, its image on `V` evaluates on `p` to the fraction `f(a) / f(b)`.
-/
def comap (f : R →+* S) (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
    (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1) :
    (structureSheaf R).1.obj (op U) →+* (structureSheaf S).1.obj (op V) where
  __ := comapₗ f.toSemilinearMap U V hUV
  map_one' := Subtype.ext <| funext fun _ ↦ by
    dsimp
    simp only [comapₗ_eq_localRingHom, PrimeSpectrum.comap_asIdeal]
    exact (Localization.localRingHom ..).map_one
  map_mul' r s := Subtype.ext <| funext fun p ↦ by
    dsimp
    change _ = (comapₗ f.toSemilinearMap U V hUV r).1 p * (comapₗ f.toSemilinearMap U V hUV s).1 p
    simp only [comapₗ_eq_localRingHom, PrimeSpectrum.comap_asIdeal]
    exact (Localization.localRingHom ..).map_mul _ _
  map_zero' := Subtype.ext <| funext fun _ ↦ by
    dsimp
    simp only [comapₗ_eq_localRingHom, PrimeSpectrum.comap_asIdeal]
    exact (Localization.localRingHom ..).map_zero

@[simp]
theorem comap_apply (f : R →+* S) (U : Opens (PrimeSpectrum.Top R))
    (V : Opens (PrimeSpectrum.Top S)) (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1)
    (s : (structureSheaf R).1.obj (op U)) (p : V) :
    (comap f U V hUV s).1 p =
      Localization.localRingHom (PrimeSpectrum.comap f p.1).asIdeal _ f rfl
        (s.1 ⟨PrimeSpectrum.comap f p.1, hUV p.2⟩) :=
  comapₗ_eq_localRingHom ..

set_option backward.isDefEq.respectTransparency false in
theorem comap_const (f : R →+* S) (U : Opens (PrimeSpectrum.Top R))
    (V : Opens (PrimeSpectrum.Top S)) (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1) (a b : R)
    (hb : ∀ x : PrimeSpectrum R, x ∈ U → b ∈ x.asIdeal.primeCompl) :
    comap f U V hUV (const a b U hb) =
      const (f a) (f b) V fun p hpV => hb (PrimeSpectrum.comap f p) (hUV hpV) :=
  Subtype.ext <| funext fun p => by
    rw [comap_apply, const_apply, const_apply]
    convert_to Localization.localRingHom _ _ _ _ (Localization.mk _ _) = Localization.mk _ _
    simp [Localization.mk_eq_mk']

/-- For an inclusion `i : V ⟶ U` between open sets of the prime spectrum of `R`, the comap of the
identity from OO_X(U) to OO_X(V) equals as the restriction map of the structure sheaf.

This is a generalization of the fact that, for fixed `U`, the comap of the identity from OO_X(U)
to OO_X(U) is the identity.
-/
theorem comap_id_eq_map (U V : Opens (PrimeSpectrum.Top R)) (iVU : V ⟶ U) :
    (comap (RingHom.id R) U V fun _ hpV => leOfHom iVU <| hpV) =
      ((structureSheaf R).1.map iVU.op).hom :=
  RingHom.ext fun s => Subtype.ext <| funext fun p => by
    rw [comap_apply]
    exact congr($(Localization.localRingHom_id ..) _)

/--
The comap of the identity is the identity. In this variant of the lemma, two open subsets `U` and
`V` are given as arguments, together with a proof that `U = V`. This is useful when `U` and `V`
are not definitionally equal.
-/
theorem comap_id {U V : Opens (PrimeSpectrum.Top R)} (hUV : U = V) :
    (comap (RingHom.id R) U V fun p hpV => by rwa [hUV, PrimeSpectrum.comap_id]) =
      (eqToHom (show (structureSheaf R).1.obj (op U) = _ by rw [hUV])).hom := by
  rw [comap_id_eq_map U V (eqToHom hUV.symm), eqToHom_op, eqToHom_map]

@[simp]
theorem comap_id' (U : Opens (PrimeSpectrum.Top R)) :
    (comap (RingHom.id R) U U fun p hpU => by rwa [PrimeSpectrum.comap_id]) = RingHom.id _ := by
  rw [comap_id rfl]; rfl

set_option backward.isDefEq.respectTransparency false in
theorem comap_comp (f : R →+* S) (g : S →+* P) (U : Opens (PrimeSpectrum.Top R))
    (V : Opens (PrimeSpectrum.Top S)) (W : Opens (PrimeSpectrum.Top P))
    (hUV : ∀ p ∈ V, PrimeSpectrum.comap f p ∈ U) (hVW : ∀ p ∈ W, PrimeSpectrum.comap g p ∈ V) :
    (comap (g.comp f) U W fun p hpW => hUV (PrimeSpectrum.comap g p) (hVW p hpW)) =
      (comap g V W hVW).comp (comap f U V hUV) :=
  RingHom.ext fun s =>
    Subtype.ext <|
      funext fun p => by
        rw [comap_apply, Localization.localRingHom_comp _ (PrimeSpectrum.comap g p.1).asIdeal] <;>
        simp

@[elementwise, reassoc]
theorem toOpen_comp_comap (f : R →+* S) (U : Opens (PrimeSpectrum.Top R)) :
    CommRingCat.ofHom (algebraMap _ _) ≫
      CommRingCat.ofHom (comap f U (Opens.comap ⟨_, PrimeSpectrum.continuous_comap f⟩ U)
        fun _ ↦ id) =
      CommRingCat.ofHom f ≫ CommRingCat.ofHom (algebraMap _ _) :=
  CommRingCat.hom_ext <| RingHom.ext fun _ ↦ Subtype.ext <| funext fun x ↦ by
    dsimp
    rw [comap_apply]
    exact Localization.localRingHom_to_map _ _ _ _ _

lemma comap_basicOpen (f : R →+* S) (x : R) :
    comap f (PrimeSpectrum.basicOpen x) (PrimeSpectrum.basicOpen (f x))
        (PrimeSpectrum.comap_basicOpen f x).le =
      IsLocalization.map (M := .powers x) (T := .powers (f x)) _ f
        (Submonoid.powers_le.mpr (Submonoid.mem_powers _)) :=
  IsLocalization.ringHom_ext (.powers x) <| by
    simpa [CommRingCat.hom_ext_iff] using toOpen_comp_comap f _

end Ring

end Comap

end StructureSheaf

end AlgebraicGeometry
