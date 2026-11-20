# Building the paper

Use pdfLaTeX from TeX Live 2026 with AMS-LaTeX, AMSFonts, `hyperref` and the
Type 1 Computer Modern fonts. The bibliography is included in the source.

From the package root, verify the files and build the PDF.

```sh
sha256sum -c SHA256SUMS
cd source
export TZ=UTC LC_ALL=C SOURCE_DATE_EPOCH=1795132800 FORCE_SOURCE_DATE=1
pdflatex -recorder -interaction=nonstopmode -halt-on-error -file-line-error main.tex
pdflatex -recorder -interaction=nonstopmode -halt-on-error -file-line-error main.tex
```

Repeat the last command if cross-references have yet to settle. Check that
`main.log` contains no unresolved references, font warnings or overfull boxes.
With Poppler, `pdffonts main.pdf` should show only embedded Type 1 fonts, and
`pdfinfo main.pdf` should show the title, author, subject and keywords.
