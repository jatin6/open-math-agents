# Four is the only exception to the totient period conjecture for A276371

Research note by @jatin6 with Codex (GPT-6), 28 November 2026.

Paul D. Hanna's sequence starts $1,1,3,19,177,2161,32643,\ldots$. Peter Bala conjectured in 2025 that, for every positive integer $k$, the sequence modulo $k$ eventually repeats with a period dividing Euler's totient $\varphi(k)$. Seiichi Manyama had published the coefficient recurrence in 2023. We use that recurrence and the original generating function to determine exactly when Bala's prediction holds. [OEIS A276371](https://oeis.org/A276371)

**Theorem.** For every positive integer $k$ other than $4$, the shift $\varphi(k)$ is an eventual period. In fact, write $k=2^r m$ with $m$ odd, and let $h$ be the largest exponent in the prime factorization of $m$, taking $h=0$ if $m=1$. Then

$$a_{n+\varphi(k)}\equiv a_n\pmod{k}\qquad(n\ge h).$$

Modulo $4$, the least period of every tail is $4$, whereas $\varphi(4)=2$.

## The coefficient recurrence

Write $E=e^{2x}$ and $A=\sum_{n\ge0}a_n x^n/n!$. The defining equation is $A^4(2-E)=E$ with $A(0)=1$. Differentiating it over the rational formal power series and using $E'=2E$ gives

$$(2-E)A'=A.$$

For example, logarithmic differentiation gives $4A'/A=2+2E/(2-E)=4/(2-E)$. Coefficient comparison now gives Manyama's recurrence in the form

$$a_0=1,\qquad a_{n+1}=a_n+\sum_{j=1}^n {n\choose j}2^j a_{n+1-j}.$$

Congruences of exponential generating functions below mean congruences of their integer coefficients **in the basis $x^n/n!$**. Differentiation shifts these coefficients, and products use integer binomial coefficients. Both operations therefore respect congruences. In particular, a solution of $(2-E)B'\equiv B$ modulo any positive integer is determined by $B(0)$, since the displayed recurrence determines each next coefficient with multiplier one. No division by a factorial modulo a composite integer is required.

## The exceptional modulus

Modulo $4$, only $j=1$ can contribute to the sum, so $a_{n+1}\equiv(1+2n)a_n$. The multiplier alternates between $1$ and $3$. Starting with $1$, this gives the repeating block $1,1,3,3$. A shift of two interchanges $1$ and $3$, on every tail. A shift of one would imply a shift of two. More generally any shift preserving the block is a multiple of four, as is seen by checking its four cyclic shifts. This disproves the original conjecture. This part, from the defining equation through the counterexample, has an independently kernel-checked Lean disproof. [Official proof and checker](https://github.com/lefttosolve2/open-math-agents/pull/29033)

## Odd moduli

Fix an odd $m>1$. Choose $1\le s<m$ with $4s\equiv1\pmod m$, put $d=m-s$, and form $B=E^s(2-E)^d$. Its constant coefficient is $1$. Direct differentiation gives

$$(2-E)B'=(4s-2mE)B\equiv B\pmod m.$$

Uniqueness from the recurrence shows that $B$ and $A$ have the same exponential coefficients modulo $m$. Expanding the ordinary polynomial $X^s(2-X)^d$ as $\sum_j c_jX^j$ therefore gives

$$a_n\equiv\sum_j c_j(2j)^n\pmod m.$$

For any prime power $p^v$ exactly dividing $m$, a summand with $p\mid 2j$ vanishes modulo $p^v$ for $n\ge v$. Otherwise Euler's theorem shows that increasing $n$ by $\varphi(m)$ preserves it modulo $p^v$, since $\varphi(p^v)$ divides $\varphi(m)$. These congruences for the prime powers give the required shift modulo $m$ for $n\ge h$. The modulus $1$ is immediate.

## Powers of two

Every $a_n$ is odd by the recurrence. We first prove a shift identity. Let $T$ be positive and even, and let $s$ be the largest integer such that $2^s\mid T$. Then for all $n\ge0$,

$$a_{n+T}\equiv a_T a_n\pmod {2^{s+2}}. \tag{1}$$

Write $D$ for formal differentiation. Applying $D^T$ to $(2-E)A'=A$ and collecting the terms that differentiate $E$ gives

$$(2-E)(D^T A)'-D^T A=E\sum_{j=1}^T{T\choose j}2^jD^{T+1-j}A.$$

For $j\ge3$, write $v_2(j)$ for the exponent of $2$ in $j$. The identity $j{T\choose j}=T{T-1\choose j-1}$ implies that the coefficient $2^j{T\choose j}$ has at least $s+j-v_2(j)\ge s+2$ factors of $2$. Here $v_2(j)\le j-2$ for $j\ge3$. The terms $j=1,2$ together are

$$2T\big(D^T A+(T-1)D^{T-1}A\big).$$

The series in parentheses has even exponential coefficients because $T-1$ and all $a_n$ are odd. Since $2^{s+1}$ divides $2T$, these two terms also vanish modulo $2^{s+2}$. Thus $D^T A$ and $a_T A$ satisfy the same differential equation modulo $2^{s+2}$ and have the same constant coefficient $a_T$. Uniqueness proves (1).

We claim that $a_{2^{r-1}}\equiv1\pmod{2^r}$ for every $r\ge3$. For $r=3$, the recurrence gives $a_4=177\equiv1\pmod8$. For the induction, set $T=2^{r-1}$. Equation (1) with $n=T$ gives $a_{2T}\equiv a_T^2\pmod{2^{r+1}}$. Squaring a number congruent to $1$ modulo $2^r$ gives $1$ modulo $2^{r+1}$, which proves the induction step. Applying (1) again, now for arbitrary $n$, gives $a_{n+T}\equiv a_n\pmod{2^r}$. Thus $\varphi(2^r)=2^{r-1}$ is a period from the start for every $r\ge3$. For $r=1$, parity gives period one.

## Combining the prime factors

For $k=2^r m$ with $m$ odd, $\varphi(k)=\varphi(2^r)\varphi(m)$. When $r\ne2$, this shift is a multiple of the periods proved for both coprime factors (omitting the trivial factor $1$). When $r=2$ and $m>1$, $\varphi(m)$ is even, so $\varphi(k)=2\varphi(m)$ is a multiple of the actual period $4$ modulo $4$. Once $n\ge h$, the shift works modulo both factors and hence modulo $k$. This leaves exactly $k=4$, as claimed.

The all-moduli classification and the onset bound above are given as a mathematical proof. As a separate arithmetic check, all 183,253 applicable comparisons for $1\le k\le500$, $k\ne4$, agreed across the 521 published terms indexed $0$ through $520$. Equation (1) also passed all 67,600 applicable comparisons for even shifts on those terms. [Published terms](https://oeis.org/A276371/b276371.txt)
