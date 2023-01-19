# Formal verification of a manuscript "On the Erdős-Tuza-Valtr Conjecture" 
This is a formal verification of the manuscript "[On the Erdős-Tuza-Valtr Conjecture](https://arxiv.org/abs/2206.04260)" in Lean 3.

## The theorem
For any $n \geq 2$, let $E(n)$ be the minimum number with the property that any $E(n)$ points on a plane with no three on a line contains $n$ points 
forming the vertices of a convex $n$-gon.
The _Erdős-Szekeres conjecture_ asserts the equality $E(n) = 2^{n−2}$. 
Despite decades of serious attempts and substantial progresses, the exact equality remains open as of January 18, 2022.
Erdős and Szekeres showed the lower bound $E(n) \geq 2^{n−2}$ by construction, and 
the best upper bound known so far is of magnitude $E(n) \leq 2^{n + o(n)}$ (see the manuscript for references).

The _Erdős-Tuza-Valtr conjecture_ is a generalization of the Erdős-Szekeres conjecture.
For any $n, a, b \geq 2$, let $E(n, a, b)$ be the minimum number with the property that any $E(n, a, b)$ points on a plane with no three on a line
contains one of 1. the vertices a convex n-gon, 2. a-cap (a points on a concave downward curve), or 3. b-cup (b points on a concave upward curve).
Erdős, Tuza, and Valtr conjectured the exact value of $E(n, a, b)$ and
also showed that their generalization is actually equivalent to (thus, also a consequence of) the original Erdős-Szekeres conjecture.

The case $a, b \geq 2$ and $n \geq a + b - 3$ of the Erdős-Tuza-Valtr conjecture is actually a direct consequence of the _cups-caps theorem_ 
shown in the original 1935 paper of Erdős and Szekeres.
This is because for any $n \geq a + b - 3$, either the upper or lower part of a convex $n$-gon contains an $a$-cap or a $b$-cup, 
so the case where a convex $n$-gon exists reduces to the existence of either an $a$-cap or a $b$-cup.
Define $E(a, b)$ as the minimum number such that any $E(a, b)$ points on a plane with no three on a line
always contain either an $a$-cap or a $b$-cup.
The cups-caps theorem shows the exact value $E(a, b) = \binom{a+b-4}{a-2}+1$,
and this agrees with the value $E(n, a, b)$ for $n \geq a + b - 3 suggested by the Erdős-Tuza-Valtr conjecture$.
So far this was the only case of the Erdős-Tuza-Valtr conjecture known in the literature.

In our manuscript, we show the first new case $a = 4, b = n$ of the Erdős-Tuza-Valtr conjecture.
That is, we show the equality $E(n, 4, n) = \binom{n-1}{2} + 2$, 
putting the Erdős-Szekeres conjecture $E(n) = 2^{n-2}$ slightly in more affirmative side.
Observe that $n < a + b - 3$ in this case, so it is not a direct consequence of the cups-caps theorem.
Our proof also generalizes to a purely combinatorial model of convexity.

## Formalization
