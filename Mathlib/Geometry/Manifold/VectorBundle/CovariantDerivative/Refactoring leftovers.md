next PRs to merge
- rename extFunDeriv to mvfderiv (and deprecate lemmas; just a few)               PRed
- merge typo fix to MDiffAt delaborator                                           PRed and borsed
- add delaborators (by Patrick, self-merge?) --> add tests myself
- add aux. lemmas for this stuff
- tweak vector bundle lie bracket stuff accordingly --- and update metric.lean. fold all in one
- after the mfderivWithin lemmas PR: add mvfderivWithin versions of stuff, with elaborators etc.

missing API lemma: mvfderivWithin_univ, and use that in LieBracket instead!



rename `extFunDeriv` to `mvfderiv`            done

`mvfDerivWithin`, with supporting lemmas and elaborators etc.       future, low priority            done
fix LieBracket.lean accordingly                                     same; not quite it

make all fromNOrmedSpace things private; replace yb lemmas about mvfderivWithin instead!


=> copy notation in Metric.lean and make LeviCivita use it!
(if we use it at all; to be checked!)



TODO revisit: do we want LeviCivitaConnection and a predicate "IsLeviCivitaConnection"?


TODO: inner_bundle' and investigate why!

better: in the one public lemma with this formula, inline that term instead


inline the lemma `aux` in the `LeviCivitaConnection.uniqueness` lemma

LeviCivita: why did we have the various `aux` declarations? trying to see if we can remove some of them...
remove lcAux\_0, done
lcAux0 (the tensorial version): should also remove; leave as-is for now

rewrites left: line 174, will be inlined
line 380 and a few places after: still need the rewrite to force down a certain path


-> Patrick is fighting the instance stuff at the beginning
(update: has a minimal example now, where things fail
  Sébastien was also confused; perhaps still lean4#9077?)



Refactoring leftovers
- more library to refactor accordingly?
- remaining defeq abuse in Levi-Civita



do we want all the pre-exiting versions in SpecificFunctions?
