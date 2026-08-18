# From Lean 4 to LaTeX

## General Prompt for Converting Lean 4 Code to LaTeX

A general prompt for converting Lean 4 code to LaTeX is:

```text
Rewrite the following Lean 4 argument as a polished mathematical proof in

LaTeX for a human reader.

Do not output Lean code, tactic blocks, or proof scripts. Do not preserve
names like `have`, `exact`, `show`, `intro`, `simp`, or any other Lean proof
syntax. Instead, express the same argument as a clean, elegant proof in
standard mathematical prose.

Your output should: - maintain the original mathematical logic and structure;

- simplify or restate intermediate steps in natural language;
- use standard LaTeX math notation and conventional proof formatting;
- be readable, concise, and mathematically natural;
- omit implementation details specific to Lean or theorem proving.

Return only valid LaTeX.
```

## Euclid's Infinite Primes

I used the following prompt in Gemini to render the Lean 4 code as LaTeX:

> @Euclid.lean:line 17-38 Produce a LaTeX version of the Lean 4 argument that
> there are infinite primes. Make this a human readable math proof (rather than
> a machine readable Lean proof).

Then save the generated LaTeX document in this directory as
`docs/euclid-infinite-primes.tex`.

To render the [LaTeX] file to PDF, use the following command:

```bash
latexmk -pdf -synctex=1 euclid-infinite-primes.tex
```

This will generate a PDF document in this directory as
[euclid-infinite-primes.pdf](euclid-infinite-primes.pdf).

## The Derivative of Energy

```bash
latexmk -pdf -synctex=1 derivative-of-energy.tex
```

This will generate a PDF document in this directory as
[derivative-of-energy.pdf](derivative-of-energy.pdf).
