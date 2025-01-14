# this file will be run by the remote sage server, so should not import local files.
import json

def q_arr(coeff: QQ) -> list[int]:
    return [int(coeff.numerator()), int(coeff.denominator())]

def serialize_polynomials(power, coeffs) -> str:
    return json.dumps({'power': int(power), 'coeffs': [
        [[[[int(t[0]), int(t[1])] for t in etuple.sparse_iter()], q_arr(coeff)]
        for etuple, coeff in c.dict().items()] for c in coeffs
    ]})
