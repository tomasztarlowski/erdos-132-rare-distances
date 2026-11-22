module

public import Mathlib

@[expose] public section

/-!
# Challenge: Erdős Problem #132 — Formal Proofs and Moment Obstruction Closing `n = 14`

This lightweight Challenge module declares the planar distance definitions and the six compared
theorems on **Erdős Problem #132** (`https://www.erdosproblems.com/132`). Proofs are supplied in
`Solution.lean` (importing `Matematyka.Erdos132`) and audited by Comparator using strictly the
standard axioms `{propext, Quot.sound, Classical.choice}`.

## Scope of Claims
- `fc_hopf_pannwitz`, `fc_four_points`, `no_six_point_two_dist`, `fc_erdos_fishburn`, and
  `no_regPoly_violator_extension` are **unconditional** theorems.
- `fc_fourteen_of_wei_and_class13` establishes the `n = 14` case **conditional** on two explicit
  literature hypotheses passed as arguments: Wei's bound `g(6) = 13` (`hwei`) and the regular
  `13`-gon classification for `13`-point `≤ 6`-distance sets with all multiplicities `≤ 15`
  (`hclass13`).
- The full Erdős Problem #132 conjecture for arbitrary `n ≥ 5` (and its growth question) remains
  **open**.

## Sources
- Erdős, *Some of my favourite unsolved problems*, Math. Japon. 46 (1997), 527–537 (`[Er97e]`).
- Hopf & Pannwitz, *Aufgabe 167*, Jber. Deutsch. Math. Verein. 43 (1934), 114 (`[HoPa34]`).
- Erdős & Fishburn, *Discrete Appl. Math.* 60 (1995), 141–147 (`[ErFi95]`).
- Wei, *Electron. J. Combin.* 19 (2012) (`[We12]`, `g(6) = 13`).
- Companion preprint: `paper/erdos_132_rare_distances.pdf`.
-/

namespace Matematyka.Erdos132

open scoped Classical
open Real Finset

/-- Planar Euclidean space `ℝ²`. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- Explicit constructor for a planar point `(x, y) ∈ ℝ²`. -/
noncomputable def mkPt (x y : ℝ) : Pt := !₂[x, y]

/-- Set of distinct positive distances determined by a finite planar point set `X`. -/
noncomputable def distSet (X : Finset Pt) : Finset ℝ :=
  X.offDiag.image (fun pq => dist pq.1 pq.2)

/-- Predicate asserting that an unordered 2-element subset `s` realizes distance `d`. -/
def PairHasDist (d : ℝ) (s : Finset Pt) : Prop :=
  ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ dist p q = d

/-- Unordered-pair multiplicity `μ(X, d)` of distance `d` in `X`. -/
noncomputable def distMult (X : Finset Pt) (d : ℝ) : ℕ :=
  ((X.powersetCard 2).filter (PairHasDist d)).card

/-- Vertices of the unit regular `m`-gon `R_m`. -/
noncomputable def regPolyPt (m : ℕ) (j : Fin m) : Pt :=
  mkPt (Real.cos (2 * Real.pi * (j.val : ℝ) / m)) (Real.sin (2 * Real.pi * (j.val : ℝ) / m))

/-- Similarity transformation `ℝ² → ℝ²` with positive scale factor `R > 0`. -/
def IsEuclideanSimilarity (R : ℝ) (f : Pt → Pt) : Prop :=
  0 < R ∧ Function.Surjective f ∧ ∀ a b : Pt, dist (f a) (f b) = R * dist a b

/-- `Y` is a finite planar set similar to the regular `m`-gon `R_m`. -/
def IsSimilarRegPoly (m : ℕ) (Y : Finset Pt) : Prop :=
  ∃ (R : ℝ) (f : Pt → Pt), IsEuclideanSimilarity R f ∧
    Finset.univ.image (fun j : Fin m => f (regPolyPt m j)) = Y

/-- Number of unordered pairs of distinct points of `P` at distance `d` (matching the definition
in `google-deepmind/formal-conjectures` PR #4389). -/
noncomputable def distanceMultiplicity (P : Finset Pt) (d : ℝ) : ℕ :=
  (P.offDiag.filter fun p => dist p.1 p.2 = d).card / 2

/-- Set of distances occurring in `P` at least once and between at most `P.card` pairs (matching
the definition in `google-deepmind/formal-conjectures` PR #4389). -/
noncomputable def lowMultiplicityDistances (P : Finset Pt) : Set ℝ :=
  {d | 0 < distanceMultiplicity P d ∧ distanceMultiplicity P d ≤ P.card}

/-- Hopf–Pannwitz theorem: the diameter of a nonempty finite planar point set `P` occurs between
at most `P.card` pairs of points. -/
theorem fc_hopf_pannwitz (P : Finset Pt) (hP : P.Nonempty) :
    distanceMultiplicity P (Metric.diam (P : Set Pt)) ≤ P.card := by
  sorry

/-- Sharpness at `n = 4`: the 4-point 60° unit rhombus determines fewer than two low-multiplicity
distances (`1` occurs 5 times, only `√3` occurs at most 4 times). -/
theorem fc_four_points :
    ∃ P : Finset Pt, P.card = 4 ∧ (lowMultiplicityDistances P).ncard < 2 := by
  sorry

/-- Exact `g(2) = 5` lower bound: every 6-point planar set determines at least 3 distinct
positive distances (no 6-point 2-distance set exists). -/
theorem no_six_point_two_dist {X : Finset Pt} (hcard : X.card = 6) :
    3 ≤ (distSet X).card := by
  sorry

/-- Erdős Problem #132 for `n = 5` and `n = 6`: every 5-point or 6-point planar set determines
at least two distances occurring between 1 and `P.card` pairs. -/
theorem fc_erdos_fishburn (P : Finset Pt) (hP : P.card = 5 ∨ P.card = 6) :
    2 ≤ (lowMultiplicityDistances P).ncard := by
  sorry

/-- Regular-polygon 2nd/4th-moment obstruction (`m ≥ 4`): no point `x ∈ ℝ²` outside the unit
regular `m`-gon `R_m` at positive distance `Δ` from `R_m(j₀)` can realize the vertex-shifted
second and fourth distance moments. -/
theorem no_regPoly_violator_extension {m : ℕ} (hm : 4 ≤ m) (x : Pt) (j₀ : Fin m)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hdist : dist x (regPolyPt m j₀) = Δ)
    (hm2 : ∑ j : Fin m, dist x (regPolyPt m j) ^ 2 =
      (∑ j : Fin m, dist (regPolyPt m ⟨0, Nat.lt_of_lt_of_le (Nat.zero_lt_succ 3) hm⟩) (regPolyPt m j) ^ 2) + Δ ^ 2)
    (hm4 : ∑ j : Fin m, dist x (regPolyPt m j) ^ 4 =
      (∑ j : Fin m, dist (regPolyPt m ⟨0, Nat.lt_of_lt_of_le (Nat.zero_lt_succ 3) hm⟩) (regPolyPt m j) ^ 4) + Δ ^ 4) :
    False := by
  sorry

/-- Resolution of the `n = 14` barrier via the `m = 13` moment obstruction and even-size
endpoint descent, conditional on Wei's `g(6) = 13` bound (`hwei`) and the regular `13`-gon
classification (`hclass13`). -/
theorem fc_fourteen_of_wei_and_class13 (P : Finset Pt) (hP : P.card = 14)
    (hwei : ∀ X : Finset Pt, X.card = 14 → 7 ≤ (distSet X).card)
    (hclass13 : ∀ Y : Finset Pt, Y.card = 13 → (distSet Y).card ≤ 6 →
      (∀ d ∈ distSet Y, distMult Y d ≤ 15) → IsSimilarRegPoly 13 Y) :
    2 ≤ (lowMultiplicityDistances P).ncard := by
  sorry

end Matematyka.Erdos132
