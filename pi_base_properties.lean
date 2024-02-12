import Mathlib

/- P1 : T0 space-/
#check T0Space

/- P2 : T1 space-/
#check T1Space

/- P3 : T2 space-/
#check T2Space

/- P4 : T2.5 space-/
#check T25Space

/- P5 : T3 space-/
#check T3Space

/- P6 : T3.5 space-/
#check T35Space

/- P7 : T4 space-/
#check T4Space

/- P8 : T5 space-/
#check T5Space

/- P9 : Functionally Hausdorff space-/
def FunctionallyHausdorffSpace (α : Type*) : Prop := sorry -- couldn't find this

/- P10 : Semiregular space-/
def SemiRegularSpace (α : Type*) : Prop := sorry -- couldn't find this

/- P11 : Regular space-/
#check RegularSpace

/- P12 : Completely regular space-/
#check CompletelyRegularSpace

/- P13 : Normal space-/
#check NormalSpace

/- P14 : Completely normal space-/
def CompletelyNormalSpace (α : Type*) : Prop := sorry -- couldn't find this

/- P15 : Perfectly Normal space-/
def PerfectlyNormalSpace (α : Type*) : Prop := sorry -- couldn't find this

/- P16 : Compact space-/
#check CompactSpace

/- P17 : σ-compact space-/
#check SigmaCompactSpace

/- P18 : Lindelöf space-/
#check LindelofSpace

/- P19 : Countably compact space-/
def CountablyCompactSpace (α : Type*) : Prop := sorry -- couldn't find this

/- P20 : Sequentially compact space-/
def SequentiallyCompactSpace (α : Type*) : Prop := sorry -- couldn't find this

/- P21 : Weakly countable compact-/
def WeaklyCountablyCompactSpace (α : Type*) : Prop := sorry -- couldn't find this

/- P22 : Pseudocompact space-/
def PseudoCompactSpace (α : Type*) : Prop := sorry -- couldn't find this

/- P23 : Weakly locally compact-/
#check WeaklyLocallyCompactSpace

/- P24 : Weakly locally compact-/
def LocallyRelativelyCompactSpace (α : Type*) : Prop := sorry -- couldn't find this

/- P25 : Exhaustible by compacts-/
def ExhaustibleByCompactsSpace (α : Type*) : Prop := sorry -- couldn't find this

/- P26 : Separable space-/
#check TopologicalSpace.SeparableSpace

/- P27 : Second countable space-/
#check SecondCountableTopology

/- P28 : Separable space-/
#check FirstCountableTopology

/- P29 : Countable chain condition -/
def CountableChainConditionSpace (α : Type*) : Prop := sorry -- couldn't find this

/- P30 : Paracompact space-/
#check ParacompactSpace

/- P31 : Metacompact space-/
def MetacompactSpace (α : Type*) : Prop := sorry -- couldn't find this

/- P32 : Countably paracompact -/
def CountableParacompactSpace (α : Type*) : Prop := sorry -- couldn't find this

/- P33 : Countably metacompact -/
def CountableMetaompactSpace (α : Type*) : Prop := sorry -- couldn't find this

/- P34 : Fully normal -/
def FullyNormalSpace (α : Type*) : Prop := sorry -- couldn't find this

/- P35 : Fully T4 space-/
def FullyT4Space (α : Type*) : Prop := sorry -- couldn't find this

/- P36 : Connected space-/
#check ConnectedSpace

/- P37 : Path connected space-/
#check PathConnectedSpace

/- P38 : Arc connected space-/
def ArcConnectedSpace (α : Type*) : Prop := sorry -- couldn't find this

/- P39 : Hyperconnected space-/
def HyperConnectedSpace (α : Type*) : Prop := sorry -- couldn't find this

/- P40 : Ultraconnected space-/
def UltraConnectedSpace (α : Type*) : Prop := sorry -- couldn't find this

/- P41 : Locally connected space-/
#check LocallyConnectedSpace

/- P42 : Locally path-connected space-/
#check LocPathConnectedSpace

/- P43 : Locally arc-connected space-/
def LocArcConnectedSpace (α : Type*) : Prop := sorry -- couldn't find this

/- P44 : Biconnected space-/
def BiconnectedSpace (α : Type*) : Prop := sorry -- couldn't find this

/- P45 : Dispersion point space-/
def DispersionPointSpace (α : Type*) : Prop := sorry -- couldn't find this

/- P46 : Totally path disconnected-/
def TotallyPathDisconnectedSpace (α : Type*) : Prop := sorry -- couldn't find this

/- P47 : Totally path disconnected-/
#check TotallyDisconnectedSpace

/- P48 : Totally separated-/
#check TotallySeparatedSpace

/- P49 : Extremally disconnected-/
#check ExtremallyDisconnected

/- P50 : Zero dimensional space-/
def ZeroDimensionalSpace (α : Type*) : Prop := sorry -- couldn't find this
