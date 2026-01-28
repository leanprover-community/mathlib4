Last updated: September 18, 2025

already suggest to Newell Jansen: compute the mfderiv of Sum.inl and Sum.inr

Another option: finish the proof in #29589
The remaining sorry is of the form "this terms solves the goal, except that you need to prove some sets are equal first"

#22059: deduce mfderiv_sumMap_at_{inl,inr} from the mfderiv_{inl,inr} lemmas you will have proven

use my product computation to conclude 26085 (except for the IFT sorry)

prove the sorry in #22784 (Diffeomorph.sumSumSumComm): write the inverse function also as a composition of diffeomorphisms, then the rest should be easy
not hard, but an exercise in keeping all the details straight!
