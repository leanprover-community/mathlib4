import fractions
import typing
import mpmath
import math

def artanh(x: fractions.Fraction, N: int) -> fractions.Fraction:
    """
    x := m / n
    term := fun k => 1 / (2 * k + 1) * x ^ (2 * k + 1)
    p k / q k = term (k + 1) / term k
    ===> p := fun k => (2 * k + 1) * m ^ 2
         q := fun k => (2 * k + 3) * n ^ 2
    P a b := ∏ k ∈ [a, b), p k
    Q a b := ∏ k ∈ [a, b), q k
    R a b := Σ i ∈ [a, b), ∏ j ∈ [a, i), p j * ∏ j ∈ [i, b), q j
    then we have `term a * R a b / Q a b = Σ k ∈ [a, b) term k`
    so `Σ k ∈ [0, N), term k = term 0 * R 0 N / Q 0 N`
    and
        P a b = P a m * P m b
        Q a b = Q a m * Q m b
        R a b =
          = Σ i ∈ [a, b), ∏ j ∈ [a, i), p j * ∏ j ∈ [i, b), q j
          = Σ i ∈ [a, m), ∏ j ∈ [a, i), p j * ∏ j ∈ [i, b), q j + Σ i ∈ [m, b), ∏ j ∈ [a, i), p j * ∏ j ∈ [i, b), q j
          = Σ i ∈ [a, m), ∏ j ∈ [a, i), p j * ∏ j ∈ [i, m), q j * ∏ j ∈ [m, b), q j + Σ i ∈ [m, b), ∏ j ∈ [a, m), p j * ∏ j ∈ [m, i), p j * ∏ j ∈ [i, b), q j
          = ∏ j ∈ [m, b), q j * Σ i ∈ [a, m), ∏ j ∈ [a, i), p j * ∏ j ∈ [i, m), q j + ∏ j ∈ [a, m), p j * Σ i ∈ [m, b), ∏ j ∈ [m, i), p j * ∏ j ∈ [i, b), q j
          = Q m b * R a m + P a m * R m b
        R k (k + 1) =
          = Σ i ∈ [k, k + 1), ∏ j ∈ [k, i), p j * ∏ j ∈ [i, k + 1), q j
          = ∏ j ∈ [k, k), p j * ∏ j ∈ [k, k + 1), q j
          = ∏ j ∈ [k, k + 1), q j
          = q k
    :param x: |x| < 1
    :param N: terms
    :return:
    """
    def go(a: int, b: int) -> typing.Tuple[int, int, int]:
        if a == b: return 1, 1, 0
        elif b - a == 1: return (2 * a + 1) * x.numerator ** 2, (2 * a + 3) * x.denominator ** 2, (2 * a + 3) * x.denominator ** 2
        m = (a + b) // 2
        Pl, Ql, Rl = go(a, m)
        Pr, Qr, Rr = go(m, b)
        return Pl * Pr, Ql * Qr, Rl * Qr + Rr * Pl
    _, Q, R = go(0, N)
    return x * fractions.Fraction(R, Q)

print(
  float(
    6 * artanh(fractions.Fraction(1, 17), 20) +
    4 * artanh(fractions.Fraction(1, 19), 20) +
    4 * artanh(fractions.Fraction(1, 31), 20)
  ), math.log(2), mpmath.log(2)
)
