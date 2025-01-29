# this file will be run by the remote sage server, so should not import local files.
import json

def q_arr(coeff: QQ) -> list[int]:
    return [int(coeff.numerator()), int(coeff.denominator())]

def serialize_polynomials(power, coeffs) -> str:
    return json.dumps({'power': int(power), 'coeffs': [
        [[[[int(t[0]), int(t[1])] for t in etuple.sparse_iter()], q_arr(coeff)]
        for etuple, coeff in c.dict().items()] for c in coeffs
    ]})

def main(base_ring, atoms: int, make_hyps, make_target):
    if atoms != 0:
        vars_str = ['var' + str(i) for i in range(atoms)] + ['aux']
        P = PolynomialRing(base_ring, vars_str)
        *vars, aux = P.gens()
        hyps = make_hyps(vars)
        p = P(make_target(vars))
        if p == 0:
            # The 'radicalization trick' implemented below does not work if
            # the target polynomial p is 0 since it requires substituting 1/p.
            print(serialize_polynomials(1, len(hyps)*[P(0)]))
        else:
            # Implements the trick described in 2.2 of arxiv.org/pdf/1007.3615.pdf
            # for testing membership in the radical.
            gens = hyps + [1 - p*aux]
            I = P.ideal(gens)
            coeffs = P(1).lift(I)
            power = max(cf.degree(aux) for cf in coeffs)
            coeffs = [P(cf.subs(aux = 1/p)*p^power) for cf in coeffs[:int(-1)]]
            print(serialize_polynomials(power, coeffs))
    else:
        # workaround for a Sage shortcoming with `atoms = 0`,
        # `TypeError: no conversion of this ring to a Singular ring defined`
        # In this case, there is no need to look for membership in the *radical*;
        # we just check for membership in the ideal, and return exponent 1
        # if coefficients are found.
        P = PolynomialRing(base_ring, 'var', 1)
        hyps = make_hyps([])
        p = P(make_target([]))
        I = P.ideal(hyps)
        coeffs = p.lift(I)
        print(serialize_polynomials(1, coeffs))
