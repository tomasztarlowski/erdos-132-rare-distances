# Erdős Problem #132 — Lean 4 Formalization and Moment-Inequality Obstructions

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24442667.svg)](https://doi.org/10.5281/zenodo.24442667)

- **Palomar Registry:** [`PALOMAR-2026-11-22-000019`](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-22-000019&version=1) | **Zenodo DOI:** [`10.5281/zenodo.24442667`](https://doi.org/10.5281/zenodo.24442667)

Formalization in Lean 4 (Mathlib `v4.35.0`) and computational certificate verification for **Erdős Problem #132** ([erdosproblems.com/132](https://www.erdosproblems.com/132)):

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
4. **Compatibility Bridge for `google-deepmind/formal-conjectures` PR #4389 (`FormalConjecturesBridge`):**
   Defines `distanceMultiplicity` and `lowMultiplicityDistances` (`Set ℝ` / `Set.ncard`) matching PR #4389 verbatim, proves exact equivalence (`distanceMultiplicity_eq_distMult`, `lowMultiplicityDistances_ncard`), and provides unconditional kernel-verified proofs of `fc_hopf_pannwitz`, `fc_four_points`, and `fc_erdos_fishburn` (`n = 5, 6`), together with the conditional `n = 14` reduction `fc_fourteen_of_wei_and_class13` (which depends on the explicit Wei hypothesis `hwei` and the unproved 13-point classification hypothesis `hclass13`).
5. **Unconditional Regular-Polygon Moment Obstruction (`m ≥ 4`) and Conditional Reduction for `n = 14`:**
   - `regPoly_moment2` & `regPoly_moment4`: exact second and fourth distance moment identities on the unit regular `m`-gon `R_m` for `m ≥ 3`.
   - `no_regPoly_violator_extension`: proves unconditionally that for every `m ≥ 4`, no point `x` outside `R_m` can match a vertex's degree signature plus a single diameter pair (`Δ > 0`), reducing the obstruction to `3m > 9` (sharp equality holds at `m = 3` for `rhombus4`).
   - `erdos132_even_of_classification` & `erdos132_fourteen_of_wei_and_class13`: combines even-size endpoint descent (`C(2r+2, 2) = 1 + r(2r+3)`) with the unconditional `m ≥ 4` moment obstruction to establish a **conditional** reduction for `n = 14` (`r = 6, m = 13`) depending on two explicit hypotheses not proved here: Wei's bound `g(6) = 13` (`hwei`) and the unproved `13`-point `≤ 6`-distance classification restricted to multiplicities `≤ 15` (`hclass13`). Known non-`R_13` `13`-point `6`-distance constructions (`R_{12}^+` and the centered hexagram) exceed the ceiling `15` (`24 > 15`), and `R_13` is ruled out unconditionally by `no_regPoly_violator_extension`, but an unconditional proof of `n = 14` remains open pending `hwei` and a proof of `hclass13`.

## Axiom Audit

Every theorem and lemma in `Matematyka/Erdos132.lean` compiles with **zero** `sorry`, **zero** `admit`, **zero** `native_decide`, **zero** `bv_decide`, and **zero** custom axioms—relying exclusively on Lean's three standard axioms `{propext, Classical.choice, Quot.sound}`.

## Quick Verification

```bash
# Lean 4 build (downloads cached Mathlib oleans first)
lake exe cache get
lake build Matematyka Challenge Solution

# Python certificate verification (requires sympy, mpmath, numpy)
python3 scripts/scan_erdos_132.py --self-test
```

## Repository Contents

- `Matematyka/Erdos132.lean` — Complete Lean 4 formalization (Parts 1–6)
- `scripts/scan_erdos_132.py` — Positivstellensatz certificate generator & 80-digit `mpmath`/`SymPy` verifier
- `data/erdos_132_certificates.json` — Exported `n = 5`, `n = 6`, moment-gap, and census data
- `paper/erdos_132_rare_distances.tex` & `paper/erdos_132_rare_distances.pdf` — Preprint manuscript

## AI Disclosure

Lean 4 proofs, scripts, and the manuscript draft were developed with assistance from AI coding/formalization tools; all mathematical arguments, formal statements, references, and Lean kernel verifications were checked and verified by the author.

## License

Apache License 2.0 (see [LICENSE](LICENSE)).
