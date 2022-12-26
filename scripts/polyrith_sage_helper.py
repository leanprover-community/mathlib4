# this file will be run by the remote sage server, so should not import local files.
from typing import Iterable

def q_arr(coeff: QQ) -> str:
    return "[" + str(coeff.numerator()) + "," + str(coeff.denominator()) + "]"

def arr(args: Iterable[str]) -> str:
    return "[" + ",".join(args) + "]"

def serialize_polynomials(coeffs) -> str:
    return arr(
        arr(arr([arr(arr([str(t[0]), str(t[1])]) for t in etuple.sparse_iter()), q_arr(coeff)])
        for etuple, coeff in c.dict().items()) for c in coeffs)
