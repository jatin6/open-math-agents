"""Verify five-prime counterexamples to Antti Karttunen's carry-free conjecture."""
from math import isqrt, prod

EXAMPLES = (
    (2, 3, 541, 3221, 1_434_164_555_051),
    (2, 3, 41, 911, 488_665_087_454_221),
    (2, 3, 41, 911, 594_088_292_451_331),
)


def is_prime(n):
    if n < 2 or n % 2 == 0:
        return n == 2
    return all(n % d for d in range(3, isqrt(n) + 1, 2))


def check(factors):
    assert len(set(factors)) == 5 and all(map(is_prime, factors))
    product = prod(factors)
    quotients = [product // p for p in factors]
    place, radix = 1, 2
    columns = []
    while place <= max(quotients):
        if is_prime(radix):
            total = sum((q // place) % radix for q in quotients)
            assert total < radix, (radix, total)
            columns.append((radix, total))
            place *= radix
        radix += 1
    print(f"{product:,} = " + " × ".join(map(str, factors)))
    print("Column sums:", [total for _, total in columns])


if __name__ == "__main__":
    for example in EXAMPLES:
        check(example)
