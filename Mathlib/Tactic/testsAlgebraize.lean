import Mathlib.Tactic.Algebraize

example {A B C D : Type*}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B)
    (g : B →+* C) (h : C →+* D)
    (hf : f.FiniteType) (hf' : f.Finite) (hhg : (h.comp g).FiniteType)
    (hh : (h.comp g).comp f |>.FiniteType) :
    True := by
  algebraize f (h.comp g) (h.comp (g.comp f))


  --g h (g.comp f) (h.comp g) (h.comp (g.comp f))
  trivial
