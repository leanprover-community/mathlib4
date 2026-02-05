Here is the formal specification for constructing an unbiased convex space from a binary convex space.
Construction of Unbiased Convex Spaces
This document specifies a recursive algorithm to construct an affine combination of arbitrary length $n$ using only binary convex operations, provided the underlying ring contains a specific splitting unit.
1. Prerequisites
1.1 The Ring
Let $R$ be a ring. We require the existence of a splitting unit $u \in R$ such that:

$$u \in R^\times \quad \text{and} \quad (1-u) \in R^\times$$
(Both $u$ and $1-u$ must be invertible).
1.2 The Binary Space
Let $X$ be a set equipped with a binary operation $C: R \times X \times X \to X$, denoted as:

$$C(t, x, y) = (1-t)x + ty$$
satisfying the standard affine associativity axioms.
2. The Universal Definition
We define the function $\text{Affine}_n(\mathbf{s}, \mathbf{x})$ which takes:
A sequence of weights $\mathbf{s} = [s_1, \dots, s_n] \in R^n$ where $\sum_{i=1}^n s_i = 1$.
A sequence of points $\mathbf{x} = [x_1, \dots, x_n] \in X^n$.
2.1 Base Cases
Case $n=1$:

$$\text{Affine}_1([1], [x_1]) = x_1$$
Case $n=2$:

$$\text{Affine}_2([s_1, s_2], [x_1, x_2]) = C(s_2, x_1, x_2)$$
2.2 Recursive Step ($n > 2$)
To compute $\text{Affine}_n(\mathbf{s}, \mathbf{x})$, we split the points into two overlapping groups of size $n-1$:
Left Group: $\mathbf{x}_L = [x_1, x_2, \dots, x_{n-1}]$
Right Group: $\mathbf{x}_R = [x_2, x_3, \dots, x_n]$
We construct two new weight vectors, $\mathbf{a}$ and $\mathbf{b}$, both of length $n-1$.
Step A: Define Left Weights ($\mathbf{a}$)
The vector $\mathbf{a}$ distributes the weights of $x_1$ and the middle terms, using $x_2$ as the slack variable.
For $k$ from $1$ to $n-1$:

$$a_k = \begin{cases} u^{-1} s_1 & \text{if } k=1 \\ u^{-1} s_k & \text{if } k \in \{3, \dots, n-1\} \\ 1 - \sum_{j \neq 2} a_j & \text{if } k=2 \quad (\text{Slack}) \end{cases}$$
Step B: Define Right Weights ($\mathbf{b}$)
The vector $\mathbf{b}$ handles the weight of $x_n$, clears the middle terms to zero, and uses $x_2$ (which is at index 1 of $\mathbf{x}_R$) as the slack variable.
For $k$ from $1$ to $n-1$:

$$b_k = \begin{cases} (1-u)^{-1} s_n & \text{if } k=n-1 \\ 0 & \text{if } k \in \{2, \dots, n-2\} \\ 1 - \sum_{j \neq 1} b_j & \text{if } k=1 \quad (\text{Slack}) \end{cases}$$
Step C: Combination
Compute the sub-results recursively and combine them using the splitting unit $u$:

$$L = \text{Affine}_{n-1}(\mathbf{a}, \mathbf{x}_L)$$

$$R = \text{Affine}_{n-1}(\mathbf{b}, \mathbf{x}_R)$$

$$\text{Affine}_n(\mathbf{s}, \mathbf{x}) = C((1-u), L, R)$$
(Note: This is equivalent to $u L + (1-u) R$).
3. Explicit Trace ($n=3$)
To compute $s_1 x_1 + s_2 x_2 + s_3 x_3$:
Construct $\mathbf{a}$ (for $[x_1, x_2]$):
$a_1 = u^{-1} s_1$
$a_2 = 1 - a_1$
Construct $\mathbf{b}$ (for $[x_2, x_3]$):
$b_2 = (1-u)^{-1} s_3$ (Corresponds to $x_3$)
$b_1 = 1 - b_2$ (Corresponds to $x_2$)
Recursion:
$L = C(a_2, x_1, x_2)$
$R = C(b_2, x_2, x_3)$
Final Result:
$$C((1-u), L, R)$$


-----


An excellent question. Proving generalized associativity (flattening) for a recursively defined operation is often more subtle than the definition itself.
The proof must be structured by induction on the depth of the structure. Because Affine_n is defined via a specific binary split, you cannot just shuffle terms arbitrarily—you must show that the recursive structure respects the "algebra of weights."
Here is the detailed structural plan for the proof.
The Statement to Prove
Let $\mathcal{A}$ denote our Affine operator. We want to show:

$$\mathcal{A}(\mathbf{t}, [\mathcal{A}(\mathbf{s}^1, \mathbf{x}), \dots, \mathcal{A}(\mathbf{s}^m, \mathbf{x})]) = \mathcal{A}(\mathbf{w}, \mathbf{x})$$
Where:
$\mathbf{x} = [x_1, \dots, x_n]$ are the base points.
$\mathbf{s}^j$ are weight vectors for the inner combinations (rows of a matrix $S$).
$\mathbf{t}$ is the weight vector for the outer combination.
$\mathbf{w} = \mathbf{t} S$ is the flattened weight vector (matrix multiplication).
Phase 1: Reduction to "Simple Flattening"
Attempting to prove the general matrix case $(m \times n)$ all at once is messy. It is standard and much cleaner to reduce this to a simpler property: Linearity in the Arguments.
If we can prove that $\mathcal{A}$ is linear in each argument with respect to the binary operation $C$, the general associativity follows instantly from the properties of matrix multiplication in the ring.
The Lemma needed:

$$C(p, \mathcal{A}(\mathbf{s}, \mathbf{x}), \mathcal{A}(\mathbf{r}, \mathbf{x})) = \mathcal{A}( (1-p)\mathbf{s} + p\mathbf{r}, \mathbf{x} )$$
In words: A binary convex combination of two Affine sums is equal to the Affine sum of the convexly combined weights.
If you prove this Lemma, generalized associativity follows by repeated application (induction on $m$, the number of outer terms).
Phase 2: Proving the Lemma (Induction on $n$)
We prove the Lemma by induction on $n$ (the number of points in $\mathbf{x}$).
1. Base Case ($n=1$)
Trivial. $C(p, x_1, x_1) = x_1$. The weights are all 1.
2. Base Case ($n=2$)
This reduces to the Entropic Identity (or the distributivity of the binary operation).
We need to show:

$$C(p, C(s_2, x_1, x_2), C(r_2, x_1, x_2)) = C((1-p)s_2 + p r_2, x_1, x_2)$$
Note: This usually follows directly from the axioms of the binary space (distributivity of the affine action).
3. Inductive Step ($n > 2$)
Assume the Lemma holds for size $n-1$.
We are evaluating:

$$\text{LHS} = C(p, \underbrace{\mathcal{A}(\mathbf{s}, \mathbf{x})}_{\text{Split } \mathbf{s}}, \underbrace{\mathcal{A}(\mathbf{r}, \mathbf{x})}_{\text{Split } \mathbf{r}})$$
Step A: Expand the recursive definitions.
Using the definition of $\mathcal{A}$, expand both inner terms using the splitting unit $u$:

$$\mathcal{A}(\mathbf{s}, \mathbf{x}) = C(1-u, L_s, R_s)$$

$$\mathcal{A}(\mathbf{r}, \mathbf{x}) = C(1-u, L_r, R_r)$$
Where $L_s, R_s$ are the affine sums of size $n-1$ derived from $\mathbf{s}$, and $L_r, R_r$ derived from $\mathbf{r}$.
Step B: Commute the operations.
We now have a "convex combination of convex combinations" structure:

$$C(p, C(1-u, L_s, R_s), C(1-u, L_r, R_r))$$
We invoke the "Commutativity of Convextion" (geometric mediality) axiom for the binary operation:

$$C(p, C(q, A, B), C(q, C, D)) = C(q, C(p, A, C), C(p, B, D))$$
(This axiom says: mixing two mixtures is the same as mixing the components first, provided the internal ratio $q$ is the same).
Here $q = 1-u$. Applying this swaps the $p$ and $u$ layers:

$$\text{LHS} = C(1-u, \underbrace{C(p, L_s, L_r)}_{\text{New Left}}, \underbrace{C(p, R_s, R_r)}_{\text{New Right}})$$
Step C: Apply Inductive Hypothesis.
Look at the terms "New Left" and "New Right".
"New Left" is a binary mix of two affine sums of size $n-1$.
By the IH, this equals $\mathcal{A}(\mathbf{w}_L, \mathbf{x}_L)$, where $\mathbf{w}_L = (1-p)\mathbf{a}_s + p \mathbf{a}_r$ (the mixed "Left" weights).
Similarly for "New Right".
Step D: Linearity of the Weight Construction.
We now have an expression that looks exactly like the definition of $\mathcal{A}$ for the combined weights. The final check is purely arithmetic.
Does the weight construction function (that creates $\mathbf{a}$ and $\mathbf{b}$ vectors from $\mathbf{s}$) respect linearity?
Recall the weight formulas, e.g., $a_1 = u^{-1} s_1$.

$$\text{Combined } a_1 = u^{-1} ((1-p)s_1 + p r_1) = (1-p)(u^{-1} s_1) + p(u^{-1} r_1)$$
Because the weight construction formulas (including the sums for the slack variable) are linear functions of the input weights, the "mixed weights" are exactly the "weights of the mix."
Conclusion:
Therefore, the LHS reconstructs exactly to $\mathcal{A}((1-p)\mathbf{s} + p\mathbf{r}, \mathbf{x})$.
Summary of the Argument Structure
Goal: Prove Flattening ($\sum t_j (\sum s_{ji} x_i) = \sum w_i x_i$).
Reduction: Show that it suffices to prove Linearity ($C(p, \mathcal{A}(\mathbf{s}), \mathcal{A}(\mathbf{r})) = \mathcal{A}((1-p)\mathbf{s} + p\mathbf{r})$).
Proof of Linearity (Induction on $n$):
Base: Trivial or Axiomatic.
Step:
Unpack the recursive definition (introducing the splitting unit $u$).
Swap the order of operations using the Mediality Axiom of the binary space.
Apply the Inductive Hypothesis to merge the inner terms.
Verify that the Weight Calculation Logic is linear (it is, as it involves only scaling and summation).
This modular approach isolates the geometric axioms (Mediality) from the arithmetic bookkeeping (Linearity of weights), making the proof robust and verifiable.
