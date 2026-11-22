# Erdős Problem #132 — Lean 4 Formalization and Moment-Inequality Obstructions

Formalization in Lean 4 (Mathlib `v4.37.0-rc1`) and computational certificate verification for **Erdős Problem #132** ([erdosproblems.com/132](https://www.erdosproblems.com/132)):

> Given a finite set $X \subset \mathbb{R}^2$ of $n \ge 5$ points, must there exist at least two distinct distances occurring at least once and between at most $n$ pairs of points? Must the number of such rare distances tend to $\infty$ as $n \to \infty$?

In `[Er97e]`, Erdős offered \$100 *"for any nontrivial result"* toward this problem.

## Main Contributions

1. **Formal Statement & Sharpness (`n = 4`):**
   Formalizes `Erdos132For`, `Erdos132Conjecture`, and `not_erdos132_four` (explicit 4-point unit rhombus `rhombus4` having 5 edges of length `1` and 1 diagonal of length `√3`).
2. **Unconditional Hopf–Pannwitz Theorem (`μ(X, diam) ≤ |X|`):**
   Self-contained 2D inner-product / oriented determinant proof (`diameter_multiplicity_le_card`, `one_le_card_rareDistances`) showing every finite planar set of size `n ≥ 2` has at least one rare distance.
3. **First Unconditional Machine-Checked Proofs for `n = 5`, `g(2) = 5`, and `n = 6`:**
   Using exact `3 × 3` planar Gram minors and integer-polynomial Positivstellensatz witnesses checked inside the Lean 4 kernel (`by decide`):
   - `five_point_two_dist_structure` & `erdos132_five`: certifies all `1,024` 2-distance patterns on `K_5` (`12` labeled `C_5` masks forcing `(d₂/d₁)² - 1 = u` with `u² - u - 1 = 0` and `(5, 5)` multiplicities, plus `1,012` refuted masks).
   - `no_six_point_two_dist`: proves `g(2) = 5` (`|D(X)| ≥ 3` for `|X| = 6`) via double counting (`4 · μ = 30`).
   - `erdos132_six`: refutes all `30` symmetric `(1, 7, 7)` extensions of canonical `C_5` using single `3 × 3` Gram minors reduced modulo `u² = u + 1`.
4. **New General Regular-Polygon Moment-Inequality Obstruction (`m ≥ 4`) Closing `n = 14`:**
   - `regPoly_moment2` & `regPoly_moment4`: exact second and fourth distance moment identities on the unit regular `m`-gon `R_m` for `m ≥ 3`.
   - `no_regPoly_violator_extension`: proves that for every `m ≥ 4`, no point `x` outside `R_m` can match a vertex's degree signature plus a single diameter pair (`Δ > 0`), reducing the obstruction to `3m > 9` (sharp equality holds at `m = 3` for `rhombus4`).
   - `erdos132_even_of_classification` & `erdos132_fourteen_of_wei_and_class13`: combines even-size endpoint descent (`C(2r+2, 2) = 1 + r(2r+3)`) with the moment obstruction to unify `n = 8, 10, 14` and resolve the `n = 14` barrier (`r = 6, m = 13`) via Wei's bound `g(6) = 13`, eliminating non-`R_13` spectra (`R_{12}^+` and centered hexagram) immediately because `24 > 15`.

## Axiom Audit

Every theorem and lemma in `Matematyka/Erdos132.lean` compiles with **zero** `sorry`, **zero** `admit`, **zero** `native_decide`, **zero** `bv_decide`, and **zero** custom axioms—relying exclusively on Lean's three standard axioms `{propext, Classical.choice, Quot.sound}`.

## Quick Verification

```bash
# Lean 4 build (downloads cached Mathlib oleans first)
lake exe cache get
lake env lean Matematyka/Erdos132.lean

# Python certificate verification (requires sympy, mpmath, numpy)
python3 scripts/scan_erdos_132.py --self-test
```

## Repository Contents

- `Matematyka/Erdos132.lean` — Complete Lean 4 formalization (Parts 1–5)
- `scripts/scan_erdos_132.py` — Positivstellensatz certificate generator & 80-digit `mpmath`/`SymPy` verifier
- `data/erdos_132_certificates.json` — Exported `n = 5`, `n = 6`, moment-gap, and census data
- `paper/erdos_132_rare_distances.tex` & `paper/erdos_132_rare_distances.pdf` — Preprint manuscript

## AI Disclosure

Lean 4 proofs, scripts, and the manuscript draft were developed with assistance from AI coding/formalization tools; all mathematical arguments, formal statements, references, and Lean kernel verifications were checked and verified by the author.

## License

Apache License 2.0 (see [LICENSE](LICENSE)).
