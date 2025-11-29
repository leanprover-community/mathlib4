import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Sites.IsSheafFor

universe v v' u u' w

open CategoryTheory Limits Category

variable {C : Type u} [Category.{v} C] {X : C}

namespace CategoryTheory.Presieve

/-- An auxiliary structure, used to define `S.index`. -/
@[ext]
structure Arrow (S : Presieve X) where
  /-- The source of the arrow. -/
  Y : C
  /-- The arrow itself. -/
  f : Y ⟶ X
  /-- The given arrow is contained in the given sieve. -/
  hf : S f

/-- Relation between two elements in `S.arrow`, the data of which
involves a commutative square. -/
@[ext]
structure Arrow.Relation {S : Presieve X} (I₁ I₂ : S.Arrow) where
  /-- The source of the arrows defining the relation. -/
  Z : C
  /-- The first arrow defining the relation. -/
  g₁ : Z ⟶ I₁.Y
  /-- The second arrow defining the relation. -/
  g₂ : Z ⟶ I₂.Y
  /-- The relation itself. -/
  w : g₁ ≫ I₁.f = g₂ ≫ I₂.f := by cat_disch

/-- An auxiliary structure, used to define `S.index`. -/
@[ext]
structure Relation (S : Presieve X) where
  /-- The first arrow. -/
  {fst : S.Arrow}
  /-- The second arrow. -/
  {snd : S.Arrow}
  /-- The relation between the two arrows. -/
  r : fst.Relation snd

/-- The shape of the multiequalizer diagrams associated to `S : J.Cover X`. -/
@[simps]
def shape (S : Presieve X) : Limits.MulticospanShape where
  L := S.Arrow
  R := S.Relation
  fst I := I.fst
  snd I := I.snd

/-- To every `S : J.Cover X` and presheaf `P`, associate a `MulticospanIndex`. -/
@[simps]
def index {D : Type u'} [Category.{v'} D] (S : Presieve X) (P : Cᵒᵖ ⥤ D) :
    Limits.MulticospanIndex S.shape D where
  left I := P.obj (Opposite.op I.Y)
  right I := P.obj (Opposite.op I.r.Z)
  fst I := P.map I.r.g₁.op
  snd I := P.map I.r.g₂.op

abbrev multifork {D : Type u'} [Category.{v'} D] (S : Presieve X) (P : Cᵒᵖ ⥤ D) :
    Limits.Multifork (S.index P) :=
  Limits.Multifork.ofι _ (P.obj (Opposite.op X)) (fun I => P.map I.f.op)
    (by intro I; simp [← P.map_comp, ← op_comp, I.r.w])

/-- When `P` is a sheaf and `S` is a cover, the associated multifork is a limit. -/
noncomputable def isLimitOfIsSheaf (P : Cᵒᵖ ⥤ Type w) {X : C} (S : Presieve X)
    (hP : IsSheafFor P S) : IsLimit (S.multifork P) where
  lift := fun (E : Multifork _) x ↦
    hP.amalgamate (fun _ _ hf ↦ (E.ι ⟨_, _, hf⟩ x)) fun {_ _ Z} g₁ g₂ _ _ hf₁ hf₂ w ↦
      congrFun (E.condition ⟨(⟨Z, g₁, g₂, w⟩ : Arrow.Relation ⟨_, _, hf₁⟩ ⟨_, _, hf₂⟩)⟩) _
  fac := by
    rintro (E : Multifork _) (_ | b)
    · ext
      apply hP.valid_glue
    · rw [← E.w (WalkingMulticospan.Hom.fst b),
        ← (S.multifork P).w (WalkingMulticospan.Hom.fst b), ← assoc]
      congr 1
      ext
      apply hP.valid_glue
  uniq := by
    intro (E : Multifork _) m hm
    ext x
    apply hP.isSeparatedFor.ext
    intro Y f hf
    have := congrFun (hm (WalkingMulticospan.left ⟨Y, f, hf⟩)) x
    dsimp at this
    rw [this]
    symm
    apply hP.valid_glue

theorem isSheaf_iff_multifork (P : Cᵒᵖ ⥤ Type max u v w) {X : C} (S : Presieve X) :
    IsSheafFor P S ↔ Nonempty (IsLimit (S.multifork P)) := by
  refine ⟨fun hP => ⟨isLimitOfIsSheaf _ _ hP⟩, fun ⟨h⟩ x hx ↦ ?_⟩
  let K : Multifork (S.index P) :=
    Multifork.ofι (S.index P) (∀ ⦃Y : C⦄ (f : Y ⟶ X), S f → P.obj (Opposite.op Y))
      (fun I _ ↦ x I.f I.hf)
      (fun I => by ext; simpa using hx _ _ I.fst.hf I.snd.hf I.r.w)
  refine ⟨h.lift K x, ?_, ?_⟩
  · intro Y f hf
    exact congrFun (h.fac K (WalkingMulticospan.left ⟨Y, f, hf⟩)) _
  · intro e he
    refine congrFun (h.uniq K (fun hf ↦ e) ?_) x
    rintro (a | b)
    · ext
      apply he
    · ext
      simp [he _ b.fst.hf]
      rfl

end CategoryTheory.Presieve
