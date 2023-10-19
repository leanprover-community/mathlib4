structure Poly where 
  pos : Type 
  dir : pos -> Type

def monomial (P D : Type) : Poly :=
  {
    pos := P
    dir := λ _ ↦ D 
  }

notation:50 A:50 " y^" B:50 => monomial A B  

def const (P : Type) : Poly := P y^Empty  -- monomial P Empty
def linear (P : Type) : Poly := P y^Unit
def poly1 : Poly := const Unit
def poly0 : Poly := const Empty
def y : Poly := linear Unit

def representable (D : Type) : Poly := monomial Unit D

def bang1 {T : Type} : T -> Unit := λ _ ↦ Unit.unit 
def ident {T : Type} : T -> T := λ t ↦ t

def applyFun : Poly -> Type -> Type:= 
  λ p T ↦ (P : p.pos) × ((p.dir P) -> T)

------------- Maps ------------

def polymap (p q: Poly) : Type :=
  Σ (onPos : p.pos -> q.pos), 
  (P : p.pos) -> q.dir (onPos P) -> p.dir P

notation:50 p "⇒" q => polymap p q 

def polymap2 (p q : Poly) : Type :=
  (P : p.pos) -> Σ (Q : q.pos), q.dir Q -> p.dir P

def cast12 {p q : Poly}: polymap p q -> polymap2 p q :=
  λ f P ↦
  (Sigma.mk (f.fst P) (f.snd P))

def cast21 {p q : Poly}: polymap2 p q -> polymap p q :=
  λ f ↦ 
  (Sigma.mk (λ P ↦ (f P).fst) (λ P ↦ (f P).snd))

def constantMap {T T' : Type} : 
  (T -> T') -> (const T) ⇒ (const T') :=
  λ f ↦ (Sigma.mk f λ _ ↦ Empty.rec ) 

def linearMap {T T' : Type} : (T -> T') ->  (linear T) ⇒ (linear T') :=
  λ f ↦ (Sigma.mk f λ _ _ ↦ Unit.unit)

def representableMap {T T' : Type} : (T -> T') -> polymap (representable T') (representable T) :=
  λ f ↦ (Sigma.mk bang1 λ _ ↦ f)

def polyid {p : Poly} : p ⇒ p :=
  (Sigma.mk (ident) λ _ ↦ ident)

def bang0poly {p : Poly} : poly0 ⇒ p  := 
  (Sigma.mk Empty.rec Empty.rec) 

def bang1poly {P : Poly} : P ⇒ poly1 := (Sigma.mk bang1 λ _ ↦ Empty.rec)

def composemap {p q r : Poly} : (p ⇒ q) -> (q ⇒ r) -> (p ⇒ r) :=
  λ f g ↦ 
  let onPos : p.pos -> r.pos := g.fst ∘ f.fst
  let onDir : (P : p.pos) -> (r.dir $ onPos P) -> (p.dir P) := λ P rd ↦ (f.snd P $ g.snd (f.fst P) rd)
  (Sigma.mk onPos onDir)

notation:50 f:50 ";" g:50  => composemap f g

theorem assoc {p q r s : Poly} : 
  (f : p ⇒ q) -> (g : q ⇒ r) -> (h : r ⇒ s) -> 
  (f ; (g ; h)) = ((f ; g) ; h) := by
  intros
  rfl

theorem unitl {p q : Poly} : (f : p ⇒ q) -> f = (f ; polyid) := by
  intros
  rfl

theorem unitr {p q : Poly} : (f : p ⇒ q) -> f = (polyid ; f) := by
  intros
  rfl

def toTransformation {p q : Poly} : (f : p ⇒ q) -> (T : Type) -> 
  (applyFun p T) -> (applyFun q T) := 
  λ f _ Pt ↦ 
  let P := Pt.fst
  let Q := Pt.snd
  (Sigma.mk (f.fst P) (Q ∘ f.snd P))

-------- Substitution product ----------

def subst : Poly -> Poly -> Poly := 
  λ p q ↦ 
  {
    pos := applyFun p q.pos
    dir := λ x ↦ 
      let P := x.fst 
      let Q := x.snd  
    (d : p.dir P) × (q.dir (Q d))  
  }

notation:60 p "◁" q => subst p q

def unitSubstRight {p : Poly} : (p ◁ y) ⇒ p :=
  λ p ↦ 
  (Sigma.mk (λ P ↦ P.fst) (λ P d ↦ (Sigma.mk d Unit)))

structure Comonad where
  carrier : Poly
  counit  : carrier ⇒ y
  comult  : carrier ⇒ carrier ◁ carrier
