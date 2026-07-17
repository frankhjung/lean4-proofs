# Lean 4 Proofs

This directory contains example proofs in Lean 4.

## Irrationals

The [Irrational](./Irrational) directory contains proofs of the existence of
irrational numbers.

### [Proof that log₃(2) is irrational](Irrational/Log3.lean)

We proceed by contradiction.

Assume $\log_{2}(3)$ is rational. Then there exist positive integers $a$ and $b$
such that:

$$\log_{2}(3) = \frac{a}{b}$$

By the definition of [logarithms](https://mathinsight.org/logarithm_basics), we
can rewrite this as an exponent:

$$2^{\frac{a}{b}} = 3$$

Raise both sides to the power of $b$:

$$2^{a} = 3^{b}$$

Because $a$ is a positive integer, $2^{a}$ is $2$ multiplied by itself $a$
times, meaning the left side is an even number.

Because $b$ is a positive integer, $3^{b}$ is $3$ multiplied by itself $b$
times, meaning the right side is an odd number.

An even number cannot equal an odd number. We have reached a contradiction.

Therefore, $\log_{2}(3)$ is irrational. $\square$

### [Proof that √2 is irrational](Irrational/Sqrt2.lean)

We proceed by contradiction.

Assume that $\sqrt{2}$ is a rational number. By the definition of rationality,
it can be expressed as an irreducible fraction of two coprime natural numbers,
$a$ and $b$ (where $b \neq 0$):

$$\sqrt{2} = \frac{a}{b}$$

Squaring both sides of the equation yields:

$$ 2 = \frac{a^2}{b^2} $$

Multiplying both sides by $b^2$, we obtain:

$$ a^2 = 2b^2 $$

Because $a^2$ is expressed as $2$ times an integer, $a^2$ must be an even
number. By Euclid's Lemma, if a prime number ($2$) divides a perfect square
($a^2$), it must also divide its root. Therefore, $a$ must also be even.

Since $a$ is even, there exists some integer $k$ such that $a = 2k$.

Substituting $2k$ into our previous equation gives:

$$ (2k)^2 = 2b^2 $$ $$ 4k^2 = 2b^2 $$

Dividing both sides by $2$ yields:

$$2k^2 = b^2$$

By the exact same logic as before, this implies that $b^2$ is even, which means
$b$ must also be even.

If both $a$ and $b$ are even, they share a common divisor of $2$.

This directly contradicts our initial assumption that the fraction $\frac{a}{b}$
is irreducible (i.e., that $a$ and $b$ are coprime and share no common divisors
greater than $1$).

Therefore, our initial assumption must be false. $\sqrt{2}$ cannot be expressed
as a rational fraction, meaning it is irrational. $\square$

## Update Project Dependencies

To upgrade to a new stable version of the Lean prover (e.g. v4.32.0):

1. Find the latest stable release at
   <https://github.com/leanprover/lean4/releases>

2. Install the toolchain:

   ```bash
   elan toolchain install leanprover/lean4:v4.32.0
   elan default leanprover/lean4:v4.32.0
   ```

3. Update `lean-toolchain` files:

   ```bash
   echo 'leanprover/lean4:v4.32.0' > lean-toolchain
   cp lean-toolchain docbuild/lean-toolchain
   ```

4. Update `rev` pins in lakefiles to match:
   * `lakefile.toml` — set Mathlib `rev = "v4.32.0"`
   * `docbuild/lakefile.toml` — set doc-gen4 `rev = "v4.32.0"`

5. Delete stale manifests and regenerate:

   ```bash
   rm -f lake-manifest.json docbuild/lake-manifest.json
   make update
   ```

## References

* [Lean 4](https://lean-lang.org)
* [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
* [Mathlib](https://lean-lang.org/use-cases/mathlib/)
* [Theorem Proving in Lean 4](http://leanprover.github.io/theorem_proving_in_lean4/)
