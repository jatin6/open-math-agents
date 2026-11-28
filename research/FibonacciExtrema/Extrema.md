# Sharp maxima for partitions into a fixed number of distinct Fibonacci numbers

Research supplement to Robert Israel’s five-part conjecture in [A359558](https://oeis.org/A359558). Prepared by @jatin6 with Codex (GPT-6). The structural decomposition comes from [F. V. Weinstein, *Notes on Fibonacci Partitions*, Lemma 1.5](https://arxiv.org/abs/math/0307150). The supplement gives a uniform extremal formula, simultaneous attainability, and a criterion for the first attaining integer. We use the Fibonacci numbers $F_2=1,F_3=2,F_4=3,\ldots$, with a single copy of 1.

**Theorem.** Among all positive integers, the greatest number of unordered representations as a sum of exactly $k\ge1$ distinct Fibonacci numbers is

$$\binom{k-1}{\lfloor(k-1)/2\rfloor}.$$

More precisely, among integers having exactly $t$ summands in their Zeckendorf representation, the greatest possible number of $k$-part representations is $\binom{k-1}{t-1}$ for $1\le t\le k$. Both upper bounds and their attainment for all parameters are proved in [FibonacciExtrema.lean](FibonacciExtrema.lean). The proof checks on Lean 4.33.1 with Mathlib and uses only `propext`, `Classical.choice`, and `Quot.sound`.

## Why the maximum is a binomial coefficient

The Zeckendorf representation of an integer is its unique sum of distinct, nonconsecutive Fibonacci numbers. Each representation of that same integer by distinct Fibonacci numbers, written largest first, breaks into a block for each Zeckendorf summand. A block representing $F_j$ with $s$ summands is determined by $j$ and $s$. To get one piece, use $F_j$. To get more pieces, use $F_{j-1}$ and expand the remainder $F_{j-2}$ by the same rule. The file proves the decomposition from the Fibonacci recurrence.

Thus a representation using $k$ pieces and $t$ blocks is determined by where it cuts a row of $k$ pieces into $t$ nonempty groups. There are $k-1$ spaces and we choose $t-1$ cuts. For attainment, start with $t$ Fibonacci numbers whose indices are large and far apart. Each can expand into any permitted block without overlapping the others. Every choice of cuts now gives a different representation of this *same* integer. The largest entry in the corresponding row of Pascal’s triangle is its middle one.

## Which total reaches the bound first?

The following sharper statement is proved here in ordinary mathematics. Let $1\le t\le k$, write $d=k-t$, and list the Zeckendorf indices of the target in increasing order as $j_1,\ldots,j_t$. It attains the fixed-$t$ bound exactly when

$$j_1\ge2+2d,\qquad j_{i+1}-j_i\ge\max(2,2d+1)\quad(1\le i<t).$$

Indeed, the longest permitted block has $d+1$ pieces. Repeatedly splitting the smallest remainder gives that block for $F_j$ with final (smallest) index $j-2d$. It exists if $j-2d\ge2$. Equality in the counting bound requires every composition to occur. Assign the longest block to the lowest summand and a singleton to each other summand. This forces $j_1-2d\ge2$. Assign it instead to the upper member of any neighboring pair, leaving the lower member as a singleton. The strict decrease across the boundary forces $j_{i+1}-2d>j_i$. Zeckendorf indices already differ by at least two. Conversely, these inequalities allow every block length simultaneously, with every block strictly above the next, so every composition occurs.

For the least such integer, take equality in the first index and all the gaps. Every other list satisfying the inequalities is coordinatewise at least as large. For the least integer attaining the global maximum, take the smaller value if two middle binomial coefficients tie.

| Number of pieces | Greatest number of ways | First integer that reaches it |
| ---: | ---: | ---: |
| 1 | 1 | 1 |
| 2 | 1 | 3 |
| 3 | 2 | 16 |
| 4 | 3 | 71 |
| 5 | 6 | 1,084 |
| 6 | 10 | 12,030 |
| 7 | 20 | 532,571 |
| 8 | 35 | 15,462,923 |

An independent enumeration checked all eight rows through the integer 15,462,923. Starting at `ways[0][0] = 1`, for each Fibonacci number `f` and each piece count `k` from 8 down to 1 it added `ways[k-1][n-f]` to `ways[k][n]` for every `n >= f`. Descending piece counts prevent reuse of a Fibonacci number. Israel already listed 1,084 for five pieces. The Lean file checks the all-$k$ maximum and attainment. The criterion for the earliest attaining integer is the separate argument above.
