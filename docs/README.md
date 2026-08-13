# From Lean 4 to LaTeX

I used the following prompt in Gemini to render the Lean 4 code as LaTeX:

> @Euclid.lean:line 17-38 Produce a LaTeX version of the Lean 4 argument that
> there are infinite primes. Make this a human readable math proof (rather than
> a machine readabke Lean proof).

Then save the generated LaTeX document in this directory as docs/Euclid.tex.

To render the [LaTeX] file to PDF, use the following command:

```bash
latexmk -pdf -synctex=1 euclid-infinite-primes.tex
```

This will generate a PDF document in this directory as [euclid-infinite-primes.pdf](euclid-infinite-primes.pdf).
