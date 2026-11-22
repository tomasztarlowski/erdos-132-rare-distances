import Mathlib

/-!
# Erdős Problem #132: Rare Distances in Planar Point Sets

Formalization and new unconditional/conditional results on **Erdős Problem #132**
(Erdős–Pach, `[Er84c]`, `[ErPa90]`, `[ErFi95]`, `[Er97e]`):

> Given $n \ge 5$ points in $\mathbb{R}^2$, must there exist at least two distinct distances
> occurring at least once and between at most $n$ pairs of points?

All proofs in this file depend strictly on the three standard Lean axioms
`{propext, Classical.choice, Quot.sound}` (zero `sorry`, zero `admit`,
zero `native_decide`, zero `bv_decide`, zero custom axioms).
-/

namespace Matematyka.Erdos132

open scoped Classical
open Real Finset

abbrev Pt := EuclideanSpace ℝ (Fin 2)

noncomputable def mkPt (x y : ℝ) : Pt := !₂[x, y]

lemma mkPt_zero (x y : ℝ) : (mkPt x y) 0 = x := by simp [mkPt]
lemma mkPt_one (x y : ℝ) : (mkPt x y) 1 = y := by simp [mkPt]

lemma dist_sq_pt (a b : Pt) :
    dist a b ^ 2 = (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]

lemma norm_sq_pt (a : Pt) :
    ‖a‖ ^ 2 = a 0 ^ 2 + a 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp [sq_abs]

lemma inner_pt (a b : Pt) :
    inner ℝ a b = a 0 * b 0 + a 1 * b 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

lemma dist_sq_mkPt (x₁ y₁ x₂ y₂ : ℝ) :
    dist (mkPt x₁ y₁) (mkPt x₂ y₂) ^ 2 = (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 := by
  rw [dist_sq_pt, mkPt_zero, mkPt_one, mkPt_zero, mkPt_one]

/-! ## Part 1: Core Definitions & Unordered-Pair Counting -/

section CoreDefinitions

/-- Set of distinct positive distances determined by a finite planar point set `X`. -/
noncomputable def distSet (X : Finset Pt) : Finset ℝ :=
  X.offDiag.image (fun pq => dist pq.1 pq.2)

/-- Predicate asserting that an unordered 2-element subset `s` realizes distance `d`. -/
def PairHasDist (d : ℝ) (s : Finset Pt) : Prop :=
  ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ dist p q = d

/-- Unordered-pair multiplicity `μ(X, d)` of distance `d` in `X`. -/
noncomputable def distMult (X : Finset Pt) (d : ℝ) : ℕ :=
  ((X.powersetCard 2).filter (PairHasDist d)).card

/-- Distances in `X` occurring at least once and between at most `|X|` pairs. -/
noncomputable def rareDistances (X : Finset Pt) : Finset ℝ :=
  (distSet X).filter (fun d => distMult X d ≤ X.card)

/-- Erdős Problem #132 specialized to cardinality `n`. -/
def Erdos132For (n : ℕ) : Prop :=
  ∀ X : Finset Pt, X.card = n → 2 ≤ (rareDistances X).card

/-- Full Erdős Problem #132 (first part): for every `n ≥ 5`, every `n`-point
planar set determines at least two distances occurring between at most `n` pairs. -/
def Erdos132Conjecture : Prop :=
  ∀ n ≥ 5, Erdos132For n

lemma pairHasDist_pair_iff {p q : Pt} (hpq : p ≠ q) (d : ℝ) :
    PairHasDist d {p, q} ↔ dist p q = d := by
  constructor
  · rintro ⟨a, ha, b, hb, hab, hd⟩
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact hd
    · rw [dist_comm]; exact hd
    · exact (hab rfl).elim
  · intro hd
    exact ⟨p, mem_insert_self _ _, q, mem_insert_of_mem (mem_singleton_self _), hpq, hd⟩

lemma mem_distSet_iff (X : Finset Pt) (d : ℝ) :
    d ∈ distSet X ↔ ∃ p ∈ X, ∃ q ∈ X, p ≠ q ∧ dist p q = d := by
  simp only [distSet, mem_image, mem_offDiag]
  constructor
  · rintro ⟨⟨p, q⟩, ⟨hp, hq, hpq⟩, rfl⟩
    exact ⟨p, hp, q, hq, hpq, rfl⟩
  · rintro ⟨p, hp, q, hq, hpq, rfl⟩
    exact ⟨(p, q), ⟨hp, hq, hpq⟩, rfl⟩

lemma distMult_pos_of_mem_distSet {X : Finset Pt} {d : ℝ} (hd : d ∈ distSet X) :
    1 ≤ distMult X d := by
  obtain ⟨p, hp, q, hq, hpq, rfl⟩ := (mem_distSet_iff X d).mp hd
  refine Finset.card_pos.mpr ⟨{p, q}, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_powersetCard.mpr ⟨Finset.insert_subset_iff.mpr ⟨hp, Finset.singleton_subset_iff.mpr hq⟩,
      Finset.card_pair hpq⟩
  · exact (pairHasDist_pair_iff hpq (dist p q)).mpr rfl

lemma pos_of_mem_distSet {X : Finset Pt} {d : ℝ} (hd : d ∈ distSet X) : 0 < d := by
  obtain ⟨p, _, q, _, hpq, rfl⟩ := (mem_distSet_iff X d).mp hd
  exact dist_pos.mpr hpq

lemma sum_distMult_eq_choose (X : Finset Pt) :
    ∑ d ∈ distSet X, distMult X d = Nat.choose X.card 2 := by
  rw [← Finset.card_powersetCard 2 X]
  unfold distMult
  rw [← Finset.card_biUnion]
  · congr 1
    ext s
    simp only [mem_biUnion, mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨d, _, hs, _⟩
      exact hs
    · intro hs
      obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hs.2
      have hpX : p ∈ X := hs.1 (mem_insert_self _ _)
      have hqX : q ∈ X := hs.1 (mem_insert_of_mem (mem_singleton_self _))
      refine ⟨dist p q, (mem_distSet_iff X _).mpr ⟨p, hpX, q, hqX, hpq, rfl⟩,
        hs, (pairHasDist_pair_iff hpq _).mpr rfl⟩
  · intro d₁ _ d₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro s hs₁ hs₂
    simp only [mem_filter, mem_powersetCard] at hs₁ hs₂
    obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hs₁.1.2
    have h1 := (pairHasDist_pair_iff hpq d₁).mp hs₁.2
    have h2 := (pairHasDist_pair_iff hpq d₂).mp hs₂.2
    exact hne (h1.symm.trans h2)

lemma sum_erase_distMult (X : Finset Pt) (d : ℝ) :
    ∑ y ∈ X, distMult (X.erase y) d = (X.card - 2) * distMult X d := by
  classical
  let E := (X.powersetCard 2).filter (PairHasDist d)
  have hsub : ∀ y ∈ X, (X.erase y).powersetCard 2 =
      (X.powersetCard 2).filter (fun s => y ∉ s) := by
    intro y _
    ext s
    simp only [mem_powersetCard, mem_filter, Finset.subset_erase]
    tauto
  have hswap : ∀ y ∈ X, distMult (X.erase y) d =
      ∑ s ∈ E, if y ∉ s then 1 else 0 := by
    intro y hy
    unfold distMult
    rw [hsub y hy, Finset.filter_comm]
    simp [E, Finset.card_filter]
  calc
    ∑ y ∈ X, distMult (X.erase y) d
      = ∑ y ∈ X, ∑ s ∈ E, (if y ∉ s then 1 else 0) := Finset.sum_congr rfl hswap
    _ = ∑ s ∈ E, ∑ y ∈ X, (if y ∉ s then 1 else 0) := Finset.sum_comm
    _ = ∑ _s ∈ E, (X.card - 2) := by
        refine Finset.sum_congr rfl ?_
        intro s hs
        have hs' : s ⊆ X ∧ s.card = 2 := Finset.mem_powersetCard.mp (Finset.mem_filter.mp hs).1
        have hfeq : X.filter (fun y => y ∉ s) = X \ s := by ext y; simp
        rw [← Finset.card_filter, hfeq, Finset.card_sdiff, Finset.inter_eq_left.mpr hs'.1, hs'.2]
    _ = (X.card - 2) * distMult X d := by
        simp [E, distMult, Nat.mul_comm]

lemma card_erase_sub_one_ge {X : Finset Pt} {d₀ : ℝ} (hd₀ : d₀ ∈ distSet X) :
    (distSet X \ {d₀}).card = (distSet X).card - 1 := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr hd₀),
    Finset.card_singleton]

lemma erdos132_of_many_distances {X : Finset Pt}
    (hrare : 1 ≤ (rareDistances X).card)
    (hmany : Nat.choose X.card 2 < 1 + ((distSet X).card - 1) * (X.card + 1)) :
    2 ≤ (rareDistances X).card := by
  by_contra hlt
  have hr1 : (rareDistances X).card = 1 := by omega
  obtain ⟨d₀, hd₀_eq⟩ := Finset.card_eq_one.mp hr1
  have hd₀_mem : d₀ ∈ rareDistances X := hd₀_eq ▸ Finset.mem_singleton_self d₀
  have hd₀_dist : d₀ ∈ distSet X := (Finset.mem_filter.mp hd₀_mem).1
  have h1 : 1 ≤ distMult X d₀ := distMult_pos_of_mem_distSet hd₀_dist
  have hother : ∀ d ∈ distSet X \ {d₀}, X.card + 1 ≤ distMult X d := by
    intro d hd
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hd
    by_contra hle
    have hmem : d ∈ rareDistances X := Finset.mem_filter.mpr ⟨hd.1, by omega⟩
    rw [hd₀_eq, Finset.mem_singleton] at hmem
    exact hd.2 hmem
  have hsum :
      1 + ((distSet X).card - 1) * (X.card + 1) ≤ Nat.choose X.card 2 := by
    rw [← sum_distMult_eq_choose X, ← Finset.add_sum_erase (distSet X) (distMult X) hd₀_dist]
    have hsdiff : (distSet X).erase d₀ = distSet X \ {d₀} := by ext z; simp [and_comm]
    rw [hsdiff]
    have hsum_rest :
        ((distSet X).card - 1) * (X.card + 1) ≤ ∑ d ∈ distSet X \ {d₀}, distMult X d := by
      calc
        ((distSet X).card - 1) * (X.card + 1)
          = (distSet X \ {d₀}).card * (X.card + 1) := by rw [card_erase_sub_one_ge hd₀_dist]
        _ = ∑ _d ∈ distSet X \ {d₀}, (X.card + 1) := by simp
        _ ≤ ∑ d ∈ distSet X \ {d₀}, distMult X d := Finset.sum_le_sum hother
    omega
  omega

end CoreDefinitions

/-! ## Part 2: Sharp `n = 4` Counterexample (`¬ Erdos132For 4`) -/

section Counterexample4

noncomputable def r4p0 : Pt := mkPt 0 0
noncomputable def r4p1 : Pt := mkPt 1 0
noncomputable def r4p2 : Pt := mkPt (1 / 2) (Real.sqrt 3 / 2)
noncomputable def r4p3 : Pt := mkPt (1 / 2) (-Real.sqrt 3 / 2)

noncomputable def rhombus4 : Finset Pt := {r4p0, r4p1, r4p2, r4p3}

private lemma sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

private lemma r4_ne_01 : r4p0 ≠ r4p1 := by
  intro h; have := congrArg (fun p : Pt => p 0) h; simp [r4p0, r4p1, mkPt] at this
private lemma r4_ne_02 : r4p0 ≠ r4p2 := by
  intro h; have := congrArg (fun p : Pt => p 0) h; simp [r4p0, r4p2, mkPt] at this
private lemma r4_ne_03 : r4p0 ≠ r4p3 := by
  intro h; have := congrArg (fun p : Pt => p 0) h; simp [r4p0, r4p3, mkPt] at this
private lemma r4_ne_12 : r4p1 ≠ r4p2 := by
  intro h; have := congrArg (fun p : Pt => p 0) h; norm_num [r4p1, r4p2, mkPt] at this
private lemma r4_ne_13 : r4p1 ≠ r4p3 := by
  intro h; have := congrArg (fun p : Pt => p 0) h; norm_num [r4p1, r4p3, mkPt] at this
private lemma r4_ne_23 : r4p2 ≠ r4p3 := by
  intro h
  have := congrArg (fun p : Pt => p 1) h
  simp only [r4p2, r4p3, mkPt_one] at this
  linarith [sqrt3_pos]

private lemma r4_dist_01 : dist r4p0 r4p1 = 1 := by
  rw [← sq_eq_sq₀ dist_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
  rw [r4p0, r4p1, dist_sq_mkPt]; norm_num
private lemma r4_dist_02 : dist r4p0 r4p2 = 1 := by
  rw [← sq_eq_sq₀ dist_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
  rw [r4p0, r4p2, dist_sq_mkPt]; nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
private lemma r4_dist_03 : dist r4p0 r4p3 = 1 := by
  rw [← sq_eq_sq₀ dist_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
  rw [r4p0, r4p3, dist_sq_mkPt]; nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
private lemma r4_dist_12 : dist r4p1 r4p2 = 1 := by
  rw [← sq_eq_sq₀ dist_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
  rw [r4p1, r4p2, dist_sq_mkPt]; nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
private lemma r4_dist_13 : dist r4p1 r4p3 = 1 := by
  rw [← sq_eq_sq₀ dist_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
  rw [r4p1, r4p3, dist_sq_mkPt]; nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
private lemma r4_dist_23 : dist r4p2 r4p3 = Real.sqrt 3 := by
  rw [← sq_eq_sq₀ dist_nonneg (le_of_lt sqrt3_pos)]
  rw [r4p2, r4p3, dist_sq_mkPt]; nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

lemma rhombus4_card : rhombus4.card = 4 := by
  unfold rhombus4
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp [r4_ne_23]
  · simp [r4_ne_12, r4_ne_13]
  · simp [r4_ne_01, r4_ne_02, r4_ne_03]

lemma rhombus4_distSet : distSet rhombus4 = {1, Real.sqrt 3} := by
  ext d
  rw [mem_distSet_iff]
  constructor
  · rintro ⟨p, hp, q, hq, hpq, rfl⟩
    simp only [rhombus4, mem_insert, mem_singleton] at hp hq
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl
    all_goals first
      | exact (hpq rfl).elim
      | simp [r4_dist_01, r4_dist_02, r4_dist_03, r4_dist_12, r4_dist_13, r4_dist_23,
          dist_comm r4p1 r4p0, dist_comm r4p2 r4p0, dist_comm r4p2 r4p1,
          dist_comm r4p3 r4p0, dist_comm r4p3 r4p1, dist_comm r4p3 r4p2]
  · intro hd
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact ⟨r4p0, by simp [rhombus4], r4p1, by simp [rhombus4], r4_ne_01, r4_dist_01⟩
    · exact ⟨r4p2, by simp [rhombus4], r4p3, by simp [rhombus4], r4_ne_23, r4_dist_23⟩

lemma rhombus4_mult_one : distMult rhombus4 1 = 5 := by
  have hs1 : (1 : ℝ) ≠ Real.sqrt 3 := by
    intro h
    have hsq := congrArg (· ^ 2) h
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at hsq
    norm_num at hsq
  have h5 :
      ((rhombus4.powersetCard 2).filter (PairHasDist 1)) =
      {{r4p0, r4p1}, {r4p0, r4p2}, {r4p0, r4p3}, {r4p1, r4p2}, {r4p1, r4p3}} := by
    ext s
    simp only [mem_filter, mem_powersetCard, mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨hs_sub, hs_card⟩, hpd⟩
      obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hs_card
      have hp : p ∈ rhombus4 := hs_sub (mem_insert_self _ _)
      have hq : q ∈ rhombus4 := hs_sub (mem_insert_of_mem (mem_singleton_self _))
      have hd1 : dist p q = 1 := (pairHasDist_pair_iff hpq 1).mp hpd
      simp only [rhombus4, mem_insert, mem_singleton] at hp hq
      rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl
      all_goals first
        | exact (hpq rfl).elim
        | (rw [r4_dist_23] at hd1; exact (hs1 hd1.symm).elim)
        | (rw [dist_comm, r4_dist_23] at hd1; exact (hs1 hd1.symm).elim)
        | (left; rfl)
        | (right; left; rfl)
        | (right; right; left; rfl)
        | (right; right; right; left; rfl)
        | (right; right; right; right; rfl)
        | (left; exact Finset.pair_comm _ _)
        | (right; left; exact Finset.pair_comm _ _)
        | (right; right; left; exact Finset.pair_comm _ _)
        | (right; right; right; left; exact Finset.pair_comm _ _)
        | (right; right; right; right; exact Finset.pair_comm _ _)
    · intro h
      rcases h with rfl | rfl | rfl | rfl | rfl
      · exact ⟨⟨by simp [rhombus4, Finset.insert_subset_iff], Finset.card_pair r4_ne_01⟩,
          (pairHasDist_pair_iff r4_ne_01 1).mpr r4_dist_01⟩
      · exact ⟨⟨by simp [rhombus4, Finset.insert_subset_iff], Finset.card_pair r4_ne_02⟩,
          (pairHasDist_pair_iff r4_ne_02 1).mpr r4_dist_02⟩
      · exact ⟨⟨by simp [rhombus4, Finset.insert_subset_iff], Finset.card_pair r4_ne_03⟩,
          (pairHasDist_pair_iff r4_ne_03 1).mpr r4_dist_03⟩
      · exact ⟨⟨by simp [rhombus4, Finset.insert_subset_iff], Finset.card_pair r4_ne_12⟩,
          (pairHasDist_pair_iff r4_ne_12 1).mpr r4_dist_12⟩
      · exact ⟨⟨by simp [rhombus4, Finset.insert_subset_iff], Finset.card_pair r4_ne_13⟩,
          (pairHasDist_pair_iff r4_ne_13 1).mpr r4_dist_13⟩
  unfold distMult
  rw [h5]
  have hn01_02 : ({r4p0, r4p1} : Finset Pt) ≠ {r4p0, r4p2} := by
    intro h
    have hm : r4p1 ∈ ({r4p0, r4p2} : Finset Pt) := h ▸ mem_insert_of_mem (mem_singleton_self _)
    simp [r4_ne_01.symm, r4_ne_12] at hm
  have hn01_03 : ({r4p0, r4p1} : Finset Pt) ≠ {r4p0, r4p3} := by
    intro h
    have hm : r4p1 ∈ ({r4p0, r4p3} : Finset Pt) := h ▸ mem_insert_of_mem (mem_singleton_self _)
    simp [r4_ne_01.symm, r4_ne_13] at hm
  have hn01_12 : ({r4p0, r4p1} : Finset Pt) ≠ {r4p1, r4p2} := by
    intro h
    have hm : r4p0 ∈ ({r4p1, r4p2} : Finset Pt) := h ▸ mem_insert_self _ _
    simp [r4_ne_01, r4_ne_02] at hm
  have hn01_13 : ({r4p0, r4p1} : Finset Pt) ≠ {r4p1, r4p3} := by
    intro h
    have hm : r4p0 ∈ ({r4p1, r4p3} : Finset Pt) := h ▸ mem_insert_self _ _
    simp [r4_ne_01, r4_ne_03] at hm
  have hn02_03 : ({r4p0, r4p2} : Finset Pt) ≠ {r4p0, r4p3} := by
    intro h
    have hm : r4p2 ∈ ({r4p0, r4p3} : Finset Pt) := h ▸ mem_insert_of_mem (mem_singleton_self _)
    simp [r4_ne_02.symm, r4_ne_23] at hm
  have hn02_12 : ({r4p0, r4p2} : Finset Pt) ≠ {r4p1, r4p2} := by
    intro h
    have hm : r4p0 ∈ ({r4p1, r4p2} : Finset Pt) := h ▸ mem_insert_self _ _
    simp [r4_ne_01, r4_ne_02] at hm
  have hn02_13 : ({r4p0, r4p2} : Finset Pt) ≠ {r4p1, r4p3} := by
    intro h
    have hm : r4p0 ∈ ({r4p1, r4p3} : Finset Pt) := h ▸ mem_insert_self _ _
    simp [r4_ne_01, r4_ne_03] at hm
  have hn03_12 : ({r4p0, r4p3} : Finset Pt) ≠ {r4p1, r4p2} := by
    intro h
    have hm : r4p0 ∈ ({r4p1, r4p2} : Finset Pt) := h ▸ mem_insert_self _ _
    simp [r4_ne_01, r4_ne_02] at hm
  have hn03_13 : ({r4p0, r4p3} : Finset Pt) ≠ {r4p1, r4p3} := by
    intro h
    have hm : r4p0 ∈ ({r4p1, r4p3} : Finset Pt) := h ▸ mem_insert_self _ _
    simp [r4_ne_01, r4_ne_03] at hm
  have hn12_13 : ({r4p1, r4p2} : Finset Pt) ≠ {r4p1, r4p3} := by
    intro h
    have hm : r4p2 ∈ ({r4p1, r4p3} : Finset Pt) := h ▸ mem_insert_of_mem (mem_singleton_self _)
    simp [r4_ne_12.symm, r4_ne_23] at hm
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp [hn12_13]
  · simp [hn03_12, hn03_13]
  · simp [hn02_03, hn02_12, hn02_13]
  · simp [hn01_02, hn01_03, hn01_12, hn01_13]

lemma rhombus4_mult_sqrt3 : distMult rhombus4 (Real.sqrt 3) = 1 := by
  have hsum := sum_distMult_eq_choose rhombus4
  rw [rhombus4_distSet, rhombus4_card] at hsum
  have hs1 : (1 : ℝ) ≠ Real.sqrt 3 := by
    intro h
    have hsq := congrArg (· ^ 2) h
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at hsq
    norm_num at hsq
  have hc4 : Nat.choose 4 2 = 6 := by decide
  rw [Finset.sum_pair hs1, rhombus4_mult_one, hc4] at hsum
  omega

/-- Sharp `n = 4` counterexample: the 60° rhombus has 1 rare distance (`√3`, multiplicity 1),
while distance `1` has multiplicity `5 > 4`. -/
theorem not_erdos132_four : ¬ Erdos132For 4 := by
  intro h4
  have hrare : 2 ≤ (rareDistances rhombus4).card := h4 rhombus4 rhombus4_card
  have hsub : rareDistances rhombus4 ⊆ {Real.sqrt 3} := by
    intro d hd
    have hmem := Finset.mem_filter.mp hd
    rw [rhombus4_distSet, mem_insert, mem_singleton] at hmem
    rcases hmem.1 with rfl | rfl
    · have hle := hmem.2
      rw [rhombus4_mult_one, rhombus4_card] at hle
      omega
    · exact mem_singleton_self _
  have hcard : (rareDistances rhombus4).card ≤ 1 := by
    calc (rareDistances rhombus4).card ≤ ({Real.sqrt 3} : Finset ℝ).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _
  omega

end Counterexample4

/-! ## Part 3: Unconditional Hopf–Pannwitz Theorem (`μ(Δ) ≤ n`) -/

section HopfPannwitz

private def det2 (u v : Pt) : ℝ := u 0 * v 1 - u 1 * v 0

private lemma cramer2 (u₁ u₂ u₃ : Pt) :
    det2 u₁ u₂ • u₃ + det2 u₂ u₃ • u₁ + det2 u₃ u₁ • u₂ = 0 := by
  ext i
  fin_cases i <;> simp [det2] <;> ring

private lemma lagrange2 (u v : Pt) :
    det2 u v ^ 2 + inner ℝ u v ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_sq_pt u, norm_sq_pt v, inner_pt u v]
  simp only [det2]
  ring

private lemma unit_cone_middle_vector {u₁ u₂ u₃ : Pt}
    (h1 : ‖u₁‖ = 1) (h2 : ‖u₂‖ = 1) (h3 : ‖u₃‖ = 1)
    (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃)
    (hi12 : (1 / 2 : ℝ) ≤ inner ℝ u₁ u₂)
    (hi13 : (1 / 2 : ℝ) ≤ inner ℝ u₁ u₃)
    (hi23 : (1 / 2 : ℝ) ≤ inner ℝ u₂ u₃) :
    (∃ α β : ℝ, 0 < α ∧ 0 < β ∧ 1 < α + β ∧ u₃ = α • u₁ + β • u₂) ∨
    (∃ α β : ℝ, 0 < α ∧ 0 < β ∧ 1 < α + β ∧ u₁ = α • u₂ + β • u₃) ∨
    (∃ α β : ℝ, 0 < α ∧ 0 < β ∧ 1 < α + β ∧ u₂ = α • u₃ + β • u₁) := by
  have det_ne_zero : ∀ a b : Pt, ‖a‖ = 1 → ‖b‖ = 1 → a ≠ b →
      (1 / 2 : ℝ) ≤ inner ℝ a b → det2 a b ≠ 0 := by
    intro a b ha hb hab hi hdet
    have hlag := lagrange2 a b
    rw [hdet, ha, hb] at hlag
    have hsq1 : inner ℝ a b ^ 2 = 1 := by linarith
    have hpos : 0 < ‖a - b‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hab))
    have hnorm : ‖a - b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 - 2 * inner ℝ a b := by
      rw [norm_sq_pt (a - b), norm_sq_pt a, norm_sq_pt b, inner_pt a b]
      simp only [PiLp.sub_apply]
      ring
    rw [ha, hb] at hnorm
    have hlt1 : inner ℝ a b < 1 := by linarith
    nlinarith
  have hd12 : det2 u₁ u₂ ≠ 0 := det_ne_zero u₁ u₂ h1 h2 h12 hi12
  have hd23 : det2 u₂ u₃ ≠ 0 := det_ne_zero u₂ u₃ h2 h3 h23 hi23
  have hd31 : det2 u₃ u₁ ≠ 0 :=
    det_ne_zero u₃ u₁ h3 h1 h13.symm (by rw [real_inner_comm]; exact hi13)
  have hcr := cramer2 u₁ u₂ u₃
  have hdot1 : inner ℝ (det2 u₁ u₂ • u₃ + det2 u₂ u₃ • u₁ + det2 u₃ u₁ • u₂) u₁ = 0 := by
    rw [hcr, inner_zero_left]
  simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial,
    real_inner_self_eq_norm_sq, h1] at hdot1
  have hi31 : (1 / 2 : ℝ) ≤ inner ℝ u₃ u₁ := by rw [real_inner_comm]; exact hi13
  have hi21 : (1 / 2 : ℝ) ≤ inner ℝ u₂ u₁ := by rw [real_inner_comm]; exact hi12
  have not_all_pos : ¬ (0 < det2 u₁ u₂ ∧ 0 < det2 u₂ u₃ ∧ 0 < det2 u₃ u₁) := by
    rintro ⟨p1, p2, p3⟩
    nlinarith
  have not_all_neg : ¬ (det2 u₁ u₂ < 0 ∧ det2 u₂ u₃ < 0 ∧ det2 u₃ u₁ < 0) := by
    rintro ⟨n1, n2, n3⟩
    nlinarith
  have mk_comb : ∀ a b c : Pt, ∀ d_ab d_bc d_ca : ℝ,
      ‖a‖ = 1 → ‖b‖ = 1 → ‖c‖ = 1 → inner ℝ a b < 1 →
      d_ab • c + d_bc • a + d_ca • b = 0 →
      d_ab ≠ 0 → d_bc * d_ab < 0 → d_ca * d_ab < 0 →
      ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ 1 < α + β ∧ c = α • a + β • b := by
    intro a b c dab dbc dca ha hb hc hlt hlin hdab h1' h2'
    have hceq : c = (-dbc / dab) • a + (-dca / dab) • b := by
      ext i
      have hi := congrArg (fun v : Pt => v i) hlin
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply] at hi ⊢
      field_simp [hdab]
      linarith
    set α := -dbc / dab
    set β := -dca / dab
    have hα : 0 < α := by
      exact div_pos_iff.mpr (Or.elim (lt_or_gt_of_ne hdab)
        (fun hneg => Or.inr ⟨by nlinarith, hneg⟩)
        (fun hpos => Or.inl ⟨by nlinarith, hpos⟩))
    have hβ : 0 < β := by
      exact div_pos_iff.mpr (Or.elim (lt_or_gt_of_ne hdab)
        (fun hneg => Or.inr ⟨by nlinarith, hneg⟩)
        (fun hpos => Or.inl ⟨by nlinarith, hpos⟩))
    refine ⟨α, β, hα, hβ, ?_, hceq⟩
    have hnorm_c : ‖c‖ ^ 2 = α ^ 2 * ‖a‖ ^ 2 + 2 * α * β * inner ℝ a b + β ^ 2 * ‖b‖ ^ 2 := by
      rw [hceq, norm_sq_pt (α • a + β • b), norm_sq_pt a, norm_sq_pt b, inner_pt a b]
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [hc, ha, hb] at hnorm_c
    have hsum_sq : 1 < (α + β) ^ 2 := by
      have hprod : 0 < α * β * (1 - inner ℝ a b) := mul_pos (mul_pos hα hβ) (sub_pos.mpr hlt)
      nlinarith
    by_contra hle
    push Not at hle
    nlinarith
  have hlt12 : inner ℝ u₁ u₂ < 1 := by
    have hpos : 0 < ‖u₁ - u₂‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h12))
    have hnorm : ‖u₁ - u₂‖ ^ 2 = ‖u₁‖ ^ 2 + ‖u₂‖ ^ 2 - 2 * inner ℝ u₁ u₂ := by
      rw [norm_sq_pt (u₁ - u₂), norm_sq_pt u₁, norm_sq_pt u₂, inner_pt u₁ u₂]
      simp only [PiLp.sub_apply]; ring
    rw [h1, h2] at hnorm; linarith
  have hlt23 : inner ℝ u₂ u₃ < 1 := by
    have hpos : 0 < ‖u₂ - u₃‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h23))
    have hnorm : ‖u₂ - u₃‖ ^ 2 = ‖u₂‖ ^ 2 + ‖u₃‖ ^ 2 - 2 * inner ℝ u₂ u₃ := by
      rw [norm_sq_pt (u₂ - u₃), norm_sq_pt u₂, norm_sq_pt u₃, inner_pt u₂ u₃]
      simp only [PiLp.sub_apply]; ring
    rw [h2, h3] at hnorm; linarith
  have hlt31 : inner ℝ u₃ u₁ < 1 := by
    have hpos : 0 < ‖u₃ - u₁‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h13.symm))
    have hnorm : ‖u₃ - u₁‖ ^ 2 = ‖u₃‖ ^ 2 + ‖u₁‖ ^ 2 - 2 * inner ℝ u₃ u₁ := by
      rw [norm_sq_pt (u₃ - u₁), norm_sq_pt u₃, norm_sq_pt u₁, inner_pt u₃ u₁]
      simp only [PiLp.sub_apply]; ring
    rw [h3, h1] at hnorm; linarith
  have hcr23 : det2 u₂ u₃ • u₁ + det2 u₃ u₁ • u₂ + det2 u₁ u₂ • u₃ = 0 := by
    ext i; have hi := congrArg (fun v : Pt => v i) hcr
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply] at hi ⊢; linarith
  have hcr31 : det2 u₃ u₁ • u₂ + det2 u₁ u₂ • u₃ + det2 u₂ u₃ • u₁ = 0 := by
    ext i; have hi := congrArg (fun v : Pt => v i) hcr
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply] at hi ⊢; linarith
  rcases lt_or_gt_of_ne hd12 with hn12 | hp12 <;>
  rcases lt_or_gt_of_ne hd23 with hn23 | hp23 <;>
  rcases lt_or_gt_of_ne hd31 with hn31 | hp31
  · exact (not_all_neg ⟨hn12, hn23, hn31⟩).elim
  · exact Or.inr (Or.inr (mk_comb u₃ u₁ u₂ (det2 u₃ u₁) (det2 u₁ u₂) (det2 u₂ u₃)
      h3 h1 h2 hlt31 hcr31 hd31 (by nlinarith) (by nlinarith)))
  · exact Or.inr (Or.inl (mk_comb u₂ u₃ u₁ (det2 u₂ u₃) (det2 u₃ u₁) (det2 u₁ u₂)
      h2 h3 h1 hlt23 hcr23 hd23 (by nlinarith) (by nlinarith)))
  · exact Or.inl (mk_comb u₁ u₂ u₃ (det2 u₁ u₂) (det2 u₂ u₃) (det2 u₃ u₁)
      h1 h2 h3 hlt12 hcr hd12 (by nlinarith) (by nlinarith))
  · exact Or.inl (mk_comb u₁ u₂ u₃ (det2 u₁ u₂) (det2 u₂ u₃) (det2 u₃ u₁)
      h1 h2 h3 hlt12 hcr hd12 (by nlinarith) (by nlinarith))
  · exact Or.inr (Or.inl (mk_comb u₂ u₃ u₁ (det2 u₂ u₃) (det2 u₃ u₁) (det2 u₁ u₂)
      h2 h3 h1 hlt23 hcr23 hd23 (by nlinarith) (by nlinarith)))
  · exact Or.inr (Or.inr (mk_comb u₃ u₁ u₂ (det2 u₃ u₁) (det2 u₁ u₂) (det2 u₂ u₃)
      h3 h1 h2 hlt31 hcr31 hd31 (by nlinarith) (by nlinarith)))
  · exact (not_all_pos ⟨hp12, hp23, hp31⟩).elim

private lemma unit_cone_unique_neighbor {u_a u_b u_m w : Pt} {α β : ℝ}
    (ha : ‖u_a‖ = 1) (hb : ‖u_b‖ = 1) (hm : ‖u_m‖ = 1)
    (hα : 0 < α) (hβ : 0 < β) (hsum : 1 < α + β)
    (hcomb : u_m = α • u_a + β • u_b)
    (_hw : ‖w‖ ≤ 1) (hwa : ‖w - u_a‖ ≤ 1) (hwb : ‖w - u_b‖ ≤ 1) (hwm : ‖w - u_m‖ = 1) :
    w = 0 := by
  have expand : ∀ x y : Pt, ‖x - y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * inner ℝ x y := by
    intro x y
    rw [norm_sq_pt (x - y), norm_sq_pt x, norm_sq_pt y, inner_pt x y]
    simp only [PiLp.sub_apply]; ring
  have h1 := expand w u_a
  have h2 := expand w u_b
  have h3 := expand w u_m
  have hwa_sq : ‖w - u_a‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (w - u_a)]
  have hwb_sq : ‖w - u_b‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (w - u_b)]
  have hwm_sq : ‖w - u_m‖ ^ 2 = 1 := by rw [hwm]; ring
  rw [ha] at h1; rw [hb] at h2; rw [hm] at h3
  have ha_ge : ‖w‖ ^ 2 ≤ 2 * inner ℝ w u_a := by linarith
  have hb_ge : ‖w‖ ^ 2 ≤ 2 * inner ℝ w u_b := by linarith
  have hm_eq : 2 * inner ℝ w u_m = ‖w‖ ^ 2 := by linarith
  have hlin : inner ℝ w u_m = α * inner ℝ w u_a + β * inner ℝ w u_b := by
    rw [hcomb, inner_add_right, inner_smul_right, inner_smul_right]
  have hineq : (α + β) * ‖w‖ ^ 2 ≤ ‖w‖ ^ 2 := by nlinarith
  have hw0 : ‖w‖ ^ 2 = 0 := by
    have hmul : (α + β - 1) * ‖w‖ ^ 2 ≤ 0 := by linarith
    nlinarith [sq_nonneg ‖w‖]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hw0)

private lemma two_mul_edgeCount_eq_sum_deg (Y : Finset Pt) (D : ℝ) (hD : 0 < D) :
    2 * ((Y.powersetCard 2).filter (PairHasDist D)).card =
      ∑ p ∈ Y, (Y.filter (fun q => dist p q = D)).card := by
  induction Y using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    have hsplit : ((insert a s).powersetCard 2).filter (PairHasDist D) =
        (s.powersetCard 2).filter (PairHasDist D) ∪
        ((s.filter (fun b => dist a b = D)).image (fun b => ({a, b} : Finset Pt))) := by
      ext e
      simp only [mem_filter, mem_powersetCard, mem_union, mem_image]
      constructor
      · rintro ⟨⟨he_sub, he_card⟩, hpd⟩
        obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp he_card
        have hd : dist p q = D := (pairHasDist_pair_iff hpq D).mp hpd
        by_cases hpa : p = a
        · subst hpa
          have hq_s : q ∈ s := (Finset.mem_insert.mp (he_sub (mem_insert_of_mem (mem_singleton_self _)))).resolve_left hpq.symm
          exact Or.inr ⟨q, ⟨hq_s, hd⟩, rfl⟩
        · by_cases hqa : q = a
          · subst hqa
            have hp_s : p ∈ s := (Finset.mem_insert.mp (he_sub (mem_insert_self _ _))).resolve_left hpa
            exact Or.inr ⟨p, ⟨hp_s, by rw [dist_comm]; exact hd⟩, Finset.pair_comm _ _⟩
          · refine Or.inl ⟨⟨?_, he_card⟩, hpd⟩
            intro z hz
            simp only [mem_insert, mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact (Finset.mem_insert.mp (he_sub (mem_insert_self _ _))).resolve_left hpa
            · exact (Finset.mem_insert.mp (he_sub (mem_insert_of_mem (mem_singleton_self _)))).resolve_left hqa
      · rintro (⟨⟨hs_sub, hs_card⟩, hpd⟩ | ⟨b, ⟨hb_s, hdb⟩, rfl⟩)
        · exact ⟨⟨hs_sub.trans (Finset.subset_insert a s), hs_card⟩, hpd⟩
        · have hab : a ≠ b := fun h => has (h ▸ hb_s)
          refine ⟨⟨Finset.insert_subset_iff.mpr ⟨mem_insert_self _ _,
            Finset.singleton_subset_iff.mpr (mem_insert_of_mem hb_s)⟩, Finset.card_pair hab⟩, ?_⟩
          exact (pairHasDist_pair_iff hab D).mpr hdb
    have hdisj : Disjoint ((s.powersetCard 2).filter (PairHasDist D))
        ((s.filter (fun b => dist a b = D)).image (fun b => ({a, b} : Finset Pt))) := by
      rw [Finset.disjoint_left]
      intro e he₁ he₂
      simp only [mem_filter, mem_powersetCard, mem_image] at he₁ he₂
      obtain ⟨b, _, rfl⟩ := he₂
      exact has (he₁.1.1 (mem_insert_self _ _))
    have hinj : Set.InjOn (fun b => ({a, b} : Finset Pt)) (s.filter (fun b => dist a b = D)) := by
      intro b₁ hb₁ b₂ _ heq
      dsimp only at heq
      have h1 : a ≠ b₁ := fun h => has (h ▸ (Finset.mem_filter.mp hb₁).1)
      have h2 : b₁ ∈ ({a, b₂} : Finset Pt) := heq ▸ mem_insert_of_mem (mem_singleton_self _)
      simp only [mem_insert, mem_singleton] at h2
      exact h2.resolve_left h1.symm
    rw [hsplit, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj]
    rw [Finset.sum_insert has]
    have ha_self : ¬ dist a a = D := by rw [dist_self]; exact ne_of_lt hD
    have hfil_a : (insert a s).filter (fun q => dist a q = D) = s.filter (fun q => dist a q = D) := by
      ext q; simp only [mem_filter, mem_insert]; constructor <;> intro h
      · exact ⟨h.1.resolve_left (fun hqa => ha_self (hqa ▸ h.2)), h.2⟩
      · exact ⟨Or.inr h.1, h.2⟩
    have hsum_s :
        ∑ p ∈ s, ((insert a s).filter (fun q => dist p q = D)).card =
          ∑ p ∈ s, (s.filter (fun q => dist p q = D)).card +
            (s.filter (fun q => dist a q = D)).card := by
      have hterm : ∀ p ∈ s,
          ((insert a s).filter (fun q => dist p q = D)).card =
            (s.filter (fun q => dist p q = D)).card + (if dist a p = D then 1 else 0) := by
        intro p _
        have hpa : a ∉ s.filter (fun q => dist p q = D) := fun h => has (Finset.mem_filter.mp h).1
        rw [Finset.filter_insert]
        by_cases hap : dist p a = D
        · have hap' : dist a p = D := by rw [dist_comm]; exact hap
          simp [hap, hap', Finset.card_insert_of_notMem hpa]
        · have hap' : ¬ dist a p = D := fun h => hap (by rw [dist_comm]; exact h)
          simp [hap, hap']
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
      congr 1
      rw [← Finset.card_filter]
    rw [hfil_a, hsum_s, Nat.mul_add, ih]
    omega

private lemma hopf_pannwitz_aux :
    ∀ n : ℕ, ∀ Y : Finset Pt, Y.card = n → ∀ D : ℝ, 0 < D →
      (∀ x ∈ Y, ∀ y ∈ Y, dist x y ≤ D) →
      ((Y.powersetCard 2).filter (PairHasDist D)).card ≤ Y.card := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro Y hcard D hD hdiam
    by_cases hdeg : ∀ p ∈ Y, (Y.filter (fun q => dist p q = D)).card ≤ 2
    · have h2e := two_mul_edgeCount_eq_sum_deg Y D hD
      have hsum : ∑ p ∈ Y, (Y.filter (fun q => dist p q = D)).card ≤ 2 * Y.card := by
        calc
          ∑ p ∈ Y, (Y.filter (fun q => dist p q = D)).card
            ≤ ∑ _p ∈ Y, 2 := Finset.sum_le_sum (fun p hp => hdeg p hp)
          _ = 2 * Y.card := by simp [Nat.mul_comm]
      omega
    · push Not at hdeg
      obtain ⟨p₀, hp₀, hge3⟩ := hdeg
      let N₀ := Y.filter (fun q => dist p₀ q = D)
      have hN₀ : 3 ≤ N₀.card := hge3
      obtain ⟨q₁, hq₁, s₁, hs₁, hq₁_notin⟩ :
          ∃ q₁ ∈ N₀, ∃ s₁, N₀ = insert q₁ s₁ ∧ q₁ ∉ s₁ := by
        obtain ⟨q₁, hq₁⟩ := Finset.card_pos.mp (by omega : 0 < N₀.card)
        exact ⟨q₁, hq₁, N₀.erase q₁, (Finset.insert_erase hq₁).symm, Finset.notMem_erase q₁ N₀⟩
      have hs₁_card : 2 ≤ s₁.card := by
        have := congrArg Finset.card hs₁; rw [Finset.card_insert_of_notMem hq₁_notin] at this; omega
      obtain ⟨q₂, hq₂s₁⟩ := Finset.card_pos.mp (by omega : 0 < s₁.card)
      let s₂ := s₁.erase q₂
      have hq₂_notin : q₂ ∉ s₂ := Finset.notMem_erase q₂ s₁
      have hs₁_eq : s₁ = insert q₂ s₂ := (Finset.insert_erase hq₂s₁).symm
      have hs₂_card : 1 ≤ s₂.card := by
        have := congrArg Finset.card hs₁_eq; rw [Finset.card_insert_of_notMem hq₂_notin] at this; omega
      obtain ⟨q₃, hq₃s₂⟩ := Finset.card_pos.mp hs₂_card
      have hq₂ : q₂ ∈ N₀ := hs₁ ▸ mem_insert_of_mem hq₂s₁
      have hq₃ : q₃ ∈ N₀ := hs₁ ▸ mem_insert_of_mem (hs₁_eq ▸ mem_insert_of_mem hq₃s₂)
      have h12 : q₁ ≠ q₂ := fun h => hq₁_notin (h ▸ hq₂s₁)
      have h13 : q₁ ≠ q₃ := fun h => hq₁_notin (h ▸ (hs₁_eq ▸ mem_insert_of_mem hq₃s₂))
      have h23 : q₂ ≠ q₃ := fun h => hq₂_notin (h ▸ hq₃s₂)
      have hq₁Y : q₁ ∈ Y := (Finset.mem_filter.mp hq₁).1
      have hq₂Y : q₂ ∈ Y := (Finset.mem_filter.mp hq₂).1
      have hq₃Y : q₃ ∈ Y := (Finset.mem_filter.mp hq₃).1
      have hdq₁ : dist p₀ q₁ = D := (Finset.mem_filter.mp hq₁).2
      have hdq₂ : dist p₀ q₂ = D := (Finset.mem_filter.mp hq₂).2
      have hdq₃ : dist p₀ q₃ = D := (Finset.mem_filter.mp hq₃).2
      let u₁ : Pt := D⁻¹ • (q₁ - p₀)
      let u₂ : Pt := D⁻¹ • (q₂ - p₀)
      let u₃ : Pt := D⁻¹ • (q₃ - p₀)
      have hDne : D ≠ 0 := ne_of_gt hD
      have hDinv : 0 < D⁻¹ := inv_pos.mpr hD
      have hnorm_pt : ∀ q : Pt, dist p₀ q = D → ‖D⁻¹ • (q - p₀)‖ = 1 := by
        intro q hd
        rw [norm_smul, Real.norm_of_nonneg (le_of_lt hDinv), norm_sub_rev, ← dist_eq_norm, hd,
          inv_mul_cancel₀ hDne]
      have hu₁ : ‖u₁‖ = 1 := hnorm_pt q₁ hdq₁
      have hu₂ : ‖u₂‖ = 1 := hnorm_pt q₂ hdq₂
      have hu₃ : ‖u₃‖ = 1 := hnorm_pt q₃ hdq₃
      have h_inj : ∀ a b : Pt, a ≠ b → D⁻¹ • (a - p₀) ≠ D⁻¹ • (b - p₀) := by
        intro a b hab heq
        apply hab
        have hsub : a - p₀ = b - p₀ := smul_right_injective Pt (inv_ne_zero hDne) heq
        exact sub_left_inj.mp hsub
      have hin : ∀ a b : Pt, a ∈ Y → b ∈ Y → dist p₀ a = D → dist p₀ b = D →
          (1 / 2 : ℝ) ≤ inner ℝ (D⁻¹ • (a - p₀)) (D⁻¹ • (b - p₀)) := by
        intro a b haY hbY hda hdb
        have hdist_le : ‖D⁻¹ • (a - p₀) - D⁻¹ • (b - p₀)‖ ≤ 1 := by
          rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_of_nonneg (le_of_lt hDinv),
            ← dist_eq_norm]
          calc
            D⁻¹ * dist a b ≤ D⁻¹ * D := mul_le_mul_of_nonneg_left (hdiam a haY b hbY) (le_of_lt hDinv)
            _ = 1 := inv_mul_cancel₀ hDne
        have hsq : ‖D⁻¹ • (a - p₀) - D⁻¹ • (b - p₀)‖ ^ 2 ≤ 1 := by
          nlinarith [norm_nonneg (D⁻¹ • (a - p₀) - D⁻¹ • (b - p₀))]
        have hexp : ‖D⁻¹ • (a - p₀) - D⁻¹ • (b - p₀)‖ ^ 2 =
            ‖D⁻¹ • (a - p₀)‖ ^ 2 + ‖D⁻¹ • (b - p₀)‖ ^ 2 -
              2 * inner ℝ (D⁻¹ • (a - p₀)) (D⁻¹ • (b - p₀)) := by
          rw [norm_sq_pt (D⁻¹ • (a - p₀) - D⁻¹ • (b - p₀)), norm_sq_pt, norm_sq_pt, inner_pt]
          simp only [PiLp.sub_apply]; ring
        rw [hnorm_pt a hda, hnorm_pt b hdb] at hexp
        linarith
      have hmid_all := unit_cone_middle_vector hu₁ hu₂ hu₃
        (h_inj q₁ q₂ h12) (h_inj q₁ q₃ h13) (h_inj q₂ q₃ h23)
        (hin q₁ q₂ hq₁Y hq₂Y hdq₁ hdq₂) (hin q₁ q₃ hq₁Y hq₃Y hdq₁ hdq₃)
        (hin q₂ q₃ hq₂Y hq₃Y hdq₂ hdq₃)
      have kill_mid : ∀ q_a q_b q_m : Pt, q_a ∈ Y → q_b ∈ Y → q_m ∈ Y →
          dist p₀ q_a = D → dist p₀ q_b = D → dist p₀ q_m = D →
          (∃ α β : ℝ, 0 < α ∧ 0 < β ∧ 1 < α + β ∧
            D⁻¹ • (q_m - p₀) = α • (D⁻¹ • (q_a - p₀)) + β • (D⁻¹ • (q_b - p₀))) →
          ((Y.powersetCard 2).filter (PairHasDist D)).card ≤ Y.card := by
        rintro q_a q_b q_m hqaY hqbY hqmY hdqa hdqb hdqm ⟨α, β, hα, hβ, hsum, hcomb⟩
        have huniq : ∀ r ∈ Y, dist q_m r = D → r = p₀ := by
          intro r hrY hrm
          have hr0 : D⁻¹ • (r - p₀) = 0 := by
            refine unit_cone_unique_neighbor (hnorm_pt q_a hdqa) (hnorm_pt q_b hdqb)
              (hnorm_pt q_m hdqm) hα hβ hsum hcomb ?_ ?_ ?_ ?_
            · rw [norm_smul, Real.norm_of_nonneg (le_of_lt hDinv), ← dist_eq_norm, dist_comm]
              calc D⁻¹ * dist p₀ r ≤ D⁻¹ * D := mul_le_mul_of_nonneg_left (hdiam p₀ hp₀ r hrY) (le_of_lt hDinv)
                _ = 1 := inv_mul_cancel₀ hDne
            · rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_of_nonneg (le_of_lt hDinv),
                ← dist_eq_norm]
              calc D⁻¹ * dist r q_a ≤ D⁻¹ * D := mul_le_mul_of_nonneg_left (hdiam r hrY q_a hqaY) (le_of_lt hDinv)
                _ = 1 := inv_mul_cancel₀ hDne
            · rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_of_nonneg (le_of_lt hDinv),
                ← dist_eq_norm]
              calc D⁻¹ * dist r q_b ≤ D⁻¹ * D := mul_le_mul_of_nonneg_left (hdiam r hrY q_b hqbY) (le_of_lt hDinv)
                _ = 1 := inv_mul_cancel₀ hDne
            · rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_of_nonneg (le_of_lt hDinv),
                ← dist_eq_norm, dist_comm, hrm, inv_mul_cancel₀ hDne]
          have hsub0 : r - p₀ = 0 := smul_right_injective Pt (inv_ne_zero hDne) (by simpa using hr0)
          exact sub_eq_zero.mp hsub0
        let Y' := Y.erase q_m
        have hY'_card : Y'.card + 1 = Y.card := Finset.card_erase_add_one hqmY
        have hY'_lt : Y'.card < n := by omega
        have hY'_ih := ih Y'.card hY'_lt Y' rfl D hD
          (fun x hx y hy => hdiam x (Finset.erase_subset _ _ hx) y (Finset.erase_subset _ _ hy))
        have hqm_notin : q_m ∉ Y' := Finset.notMem_erase q_m Y
        have hsplit : ((Y.powersetCard 2).filter (PairHasDist D)) =
            (Y'.powersetCard 2).filter (PairHasDist D) ∪ {{q_m, p₀}} := by
          ext e
          simp only [mem_filter, mem_powersetCard, mem_union, mem_singleton]
          constructor
          · rintro ⟨⟨he_sub, he_card⟩, hpd⟩
            by_cases hqm_in : q_m ∈ e
            · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he_card
              have hdab : dist a b = D := (pairHasDist_pair_iff hab D).mp hpd
              simp only [mem_insert, mem_singleton] at hqm_in
              rcases hqm_in with rfl | rfl
              · have hbY : b ∈ Y := he_sub (mem_insert_of_mem (mem_singleton_self _))
                have hbp : b = p₀ := huniq b hbY hdab
                subst hbp; exact Or.inr rfl
              · have haY : a ∈ Y := he_sub (mem_insert_self _ _)
                have hap : a = p₀ := huniq a haY (by rw [dist_comm]; exact hdab)
                subst hap; exact Or.inr (Finset.pair_comm _ _)
            · refine Or.inl ⟨⟨?_, he_card⟩, hpd⟩
              intro z hz
              exact Finset.mem_erase.mpr ⟨fun h => hqm_in (h ▸ hz), he_sub hz⟩
          · rintro (⟨⟨hs_sub, hs_card⟩, hpd⟩ | rfl)
            · exact ⟨⟨hs_sub.trans (Finset.erase_subset _ _), hs_card⟩, hpd⟩
            · have hqp : q_m ≠ p₀ := fun h => by rw [h, dist_self] at hdqm; exact absurd hdqm.symm (ne_of_gt hD)
              refine ⟨⟨Finset.insert_subset_iff.mpr ⟨hqmY, Finset.singleton_subset_iff.mpr hp₀⟩,
                Finset.card_pair hqp⟩, ?_⟩
              exact (pairHasDist_pair_iff hqp D).mpr (by rw [dist_comm]; exact hdqm)
        have hdisj : Disjoint ((Y'.powersetCard 2).filter (PairHasDist D)) {{q_m, p₀}} := by
          rw [Finset.disjoint_singleton_right]
          intro hmem
          exact hqm_notin ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hmem).1).1 (mem_insert_self _ _))
        rw [hsplit, Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
        omega
      rcases hmid_all with h | h | h
      · exact kill_mid q₁ q₂ q₃ hq₁Y hq₂Y hq₃Y hdq₁ hdq₂ hdq₃ h
      · exact kill_mid q₂ q₃ q₁ hq₂Y hq₃Y hq₁Y hdq₂ hdq₃ hdq₁ h
      · exact kill_mid q₃ q₁ q₂ hq₃Y hq₁Y hq₂Y hdq₃ hdq₁ hdq₂ h

/-- **Hopf–Pannwitz Theorem (1934):** For any finite planar set `X` of at least 2 points,
the diameter `maxDist X` occurs at most `|X|` times. -/
theorem diameter_multiplicity_le_card {X : Finset Pt} (hX : 2 ≤ X.card) :
    ∃ D ∈ distSet X, (∀ x ∈ X, ∀ y ∈ X, dist x y ≤ D) ∧ distMult X D ≤ X.card := by
  have hne : (distSet X).Nonempty := by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < X.card)
    exact ⟨dist a b, (mem_distSet_iff X _).mpr ⟨a, ha, b, hb, hab, rfl⟩⟩
  let D := (distSet X).max' hne
  have hD_mem : D ∈ distSet X := Finset.max'_mem (distSet X) hne
  have hD_pos : 0 < D := pos_of_mem_distSet hD_mem
  have hdiam : ∀ x ∈ X, ∀ y ∈ X, dist x y ≤ D := by
    intro x hx y hy
    by_cases hxy : x = y
    · subst hxy; rw [dist_self]; exact le_of_lt hD_pos
    · exact Finset.le_max' (distSet X) _ ((mem_distSet_iff X _).mpr ⟨x, hx, y, hy, hxy, rfl⟩)
  exact ⟨D, hD_mem, hdiam, hopf_pannwitz_aux X.card X rfl D hD_pos hdiam⟩

/-- Every planar set of at least 2 points has at least one rare distance (its diameter). -/
theorem one_le_card_rareDistances {X : Finset Pt} (hX : 2 ≤ X.card) :
    1 ≤ (rareDistances X).card := by
  obtain ⟨D, hD_mem, _, hD_mult⟩ := diameter_multiplicity_le_card hX
  exact Finset.card_pos.mpr ⟨D, Finset.mem_filter.mpr ⟨hD_mem, hD_mult⟩⟩

end HopfPannwitz

/-! ## Part 4: Planar Gram Minors & Unconditional Proofs for `n = 5`, `g(2) = 5`, `n = 6` -/

section PositivstellensatzN5N6

noncomputable def gram2 (p₀ a b : Pt) : ℝ := dist p₀ a ^ 2 + dist p₀ b ^ 2 - dist a b ^ 2

def det3R (a00 a01 a02 a10 a11 a12 a20 a21 a22 : ℝ) : ℝ :=
  a00 * (a11 * a22 - a12 * a21) - a01 * (a10 * a22 - a12 * a20) + a02 * (a10 * a21 - a11 * a20)

lemma det3R_div (s : ℝ) (hs : s ≠ 0) (a00 a01 a02 a10 a11 a12 a20 a21 a22 : ℝ) :
    det3R (a00 / s) (a01 / s) (a02 / s) (a10 / s) (a11 / s) (a12 / s)
      (a20 / s) (a21 / s) (a22 / s) =
      det3R a00 a01 a02 a10 a11 a12 a20 a21 a22 / s ^ 3 := by
  simp only [det3R]
  field_simp [hs]

lemma planar_gram_minor3_eq_zero (p₀ r₁ r₂ r₃ c₁ c₂ c₃ : Pt) :
    det3R
      (gram2 p₀ r₁ c₁) (gram2 p₀ r₁ c₂) (gram2 p₀ r₁ c₃)
      (gram2 p₀ r₂ c₁) (gram2 p₀ r₂ c₂) (gram2 p₀ r₂ c₃)
      (gram2 p₀ r₃ c₁) (gram2 p₀ r₃ c₂) (gram2 p₀ r₃ c₃) = 0 := by
  simp only [gram2, det3R, dist_sq_pt]
  ring

def addZ : List ℤ → List ℤ → List ℤ
  | [], b => b
  | a, [] => a
  | x :: xs, y :: ys => (x + y) :: addZ xs ys

def subZ : List ℤ → List ℤ → List ℤ
  | [], b => b.map (-·)
  | a, [] => a
  | x :: xs, y :: ys => (x - y) :: subZ xs ys

def mulZ : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | x :: xs, b => addZ (b.map (x * ·)) (0 :: mulZ xs b)

def det3Z (m00 m01 m02 m10 m11 m12 m20 m21 m22 : List ℤ) : List ℤ :=
  addZ
    (subZ
      (mulZ m00 (subZ (mulZ m11 m22) (mulZ m12 m21)))
      (mulZ m01 (subZ (mulZ m10 m22) (mulZ m12 m20))))
    (mulZ m02 (subZ (mulZ m10 m21) (mulZ m11 m20)))

def evalZ (u : ℝ) : List ℤ → ℝ
  | [] => 0
  | c :: cs => (c : ℝ) + u * evalZ u cs

lemma evalZ_add (u : ℝ) (a b : List ℤ) :
    evalZ u (addZ a b) = evalZ u a + evalZ u b := by
  induction a generalizing b with
  | nil => simp [addZ, evalZ]
  | cons x xs ih =>
    cases b with
    | nil => simp [addZ, evalZ]
    | cons y ys =>
      simp only [addZ, evalZ, Int.cast_add, ih]
      ring

lemma evalZ_map_neg (u : ℝ) (b : List ℤ) :
    evalZ u (b.map (-·)) = -evalZ u b := by
  induction b with
  | nil => simp [evalZ]
  | cons y ys ih => simp [evalZ, ih]; ring

lemma evalZ_sub (u : ℝ) (a b : List ℤ) :
    evalZ u (subZ a b) = evalZ u a - evalZ u b := by
  induction a generalizing b with
  | nil => simp [subZ, evalZ, evalZ_map_neg]
  | cons x xs ih =>
    cases b with
    | nil => simp [subZ, evalZ]
    | cons y ys =>
      simp only [subZ, evalZ, Int.cast_sub, ih]
      ring

lemma evalZ_map_mul (u : ℝ) (k : ℤ) (b : List ℤ) :
    evalZ u (b.map (k * ·)) = (k : ℝ) * evalZ u b := by
  induction b with
  | nil => simp [evalZ]
  | cons y ys ih => simp [evalZ, ih, Int.cast_mul]; ring

lemma evalZ_mul (u : ℝ) (a b : List ℤ) :
    evalZ u (mulZ a b) = evalZ u a * evalZ u b := by
  induction a with
  | nil => simp [mulZ, evalZ]
  | cons x xs ih =>
    simp only [mulZ, evalZ_add, evalZ_map_mul, evalZ, ih, Int.cast_zero, zero_add]
    ring

lemma evalZ_det3Z (u : ℝ) (m00 m01 m02 m10 m11 m12 m20 m21 m22 : List ℤ) :
    evalZ u (det3Z m00 m01 m02 m10 m11 m12 m20 m21 m22) =
      det3R (evalZ u m00) (evalZ u m01) (evalZ u m02)
            (evalZ u m10) (evalZ u m11) (evalZ u m12)
            (evalZ u m20) (evalZ u m21) (evalZ u m22) := by
  simp only [det3Z, det3R, evalZ_add, evalZ_sub, evalZ_mul]

def isPosZ (p : List ℤ) : Bool := p.all (0 ≤ ·) && p.any (0 < ·)

lemma evalZ_nonneg_of_all {u : ℝ} (hu : 0 ≤ u) :
    ∀ {p : List ℤ}, p.all (0 ≤ ·) = true → 0 ≤ evalZ u p
  | [], _ => by simp [evalZ]
  | c :: cs, hp => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hp
    have hrest := evalZ_nonneg_of_all hu hp.2
    have hc : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hp.1
    simp only [evalZ]
    nlinarith

lemma evalZ_pos_of_isPosZ {u : ℝ} (hu : 0 < u) :
    ∀ {p : List ℤ}, isPosZ p = true → 0 < evalZ u p
  | [], hp => by simp [isPosZ] at hp
  | c :: cs, hp => by
    simp only [isPosZ, List.all_cons, List.any_cons, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at hp
    rcases hp with ⟨⟨hc0, hcs0⟩, hcpos | hcspos⟩
    · have hrest := evalZ_nonneg_of_all (le_of_lt hu) hcs0
      have hc : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hcpos
      simp only [evalZ]
      nlinarith
    · have hrest : 0 < evalZ u cs := evalZ_pos_of_isPosZ hu (by simp [isPosZ, hcs0, hcspos])
      have hc : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc0
      simp only [evalZ]
      nlinarith

def pair5At : ℕ → ℕ × ℕ
  | 0 => (0, 1) | 1 => (0, 2) | 2 => (0, 3) | 3 => (0, 4) | 4 => (1, 2)
  | 5 => (1, 3) | 6 => (1, 4) | 7 => (2, 3) | 8 => (2, 4) | _ => (3, 4)

def pairIdx5 (a b : ℕ) : ℕ :=
  let x := min a b
  let y := max a b
  match x, y with
  | 0, 1 => 0 | 0, 2 => 1 | 0, 3 => 2 | 0, 4 => 3
  | 1, 2 => 4 | 1, 3 => 5 | 1, 4 => 6
  | 2, 3 => 7 | 2, 4 => 8 | _, _ => 9

def sub4At : ℕ → ℕ × ℕ × ℕ
  | 0 => (1, 2, 3) | 1 => (1, 2, 4) | 2 => (1, 3, 4) | _ => (2, 3, 4)

def d2Z5 (m a b : ℕ) : List ℤ :=
  if a == b then [] else if Nat.testBit m (pairIdx5 a b) then [1] else [1, 1]

def minor5Z (m idx : ℕ) : List ℤ :=
  let (r1, r2, r3) := sub4At (idx / 4)
  let (c1, c2, c3) := sub4At (idx % 4)
  let g (a b : ℕ) := subZ (addZ (d2Z5 m 0 a) (d2Z5 m 0 b)) (d2Z5 m a b)
  det3Z (g r1 c1) (g r1 c2) (g r1 c3)
        (g r2 c1) (g r2 c2) (g r2 c3)
        (g r3 c1) (g r3 c2) (g r3 c3)

def isC5EdgeNat (a b : ℕ) : Bool :=
  let x := min a b
  let y := max a b
  (x == 0 && y == 1) || (x == 1 && y == 2) || (x == 2 && y == 3) ||
  (x == 3 && y == 4) || (x == 0 && y == 4)

def c5TableData : List (ℕ × List ℕ) :=
  [
    (220, [0, 3, 2, 1, 4]),
    (234, [0, 2, 3, 1, 4]),
    (316, [0, 3, 1, 2, 4]),
    (358, [0, 2, 4, 1, 3]),
    (425, [0, 1, 3, 2, 4]),
    (453, [0, 1, 4, 2, 3]),
    (570, [0, 2, 1, 3, 4]),
    (598, [0, 2, 1, 4, 3]),
    (665, [0, 1, 2, 3, 4]),
    (707, [0, 1, 4, 3, 2]),
    (789, [0, 1, 2, 4, 3]),
    (803, [0, 1, 3, 4, 2])
  ]

def checkC5Entry (entry : ℕ × List ℕ) : Bool :=
  let (m, perm) := entry
  perm.length == 5 &&
  (List.range 5).all (fun i => perm.getD i 9 < 5) &&
  (List.range 5).all (fun i => (List.range 5).all fun j =>
    !(i < j) || perm.getD i 9 != perm.getD j 9) &&
  (List.range 5).all (fun a => (List.range 5).all fun b =>
    !(a < b) || (Nat.testBit m (pairIdx5 (perm.getD a 9) (perm.getD b 9)) == isC5EdgeNat a b))

private lemma c5TableData_ok : c5TableData.all checkC5Entry = true := by decide

abbrev Cert5 := Bool × ℕ × ℕ × List ℤ × List ℤ

def checkCert5 (m : ℕ) (c : Cert5) : Bool :=
  if c.1 then
    minor5Z m 0 == [4, 6, -2, -2] && c5TableData.any (fun e => e.1 == m)
  else
    c.2.1 < 16 && c.2.2.1 < 16 &&
    isPosZ (addZ (mulZ c.2.2.2.1 (minor5Z m c.2.1))
                 (if c.2.2.2.2.isEmpty then [] else mulZ c.2.2.2.2 (minor5Z m c.2.2.1)))

def verifyCerts5 : ℕ → ℕ → List Cert5 → Bool
  | m, stop, [] => m == stop
  | m, stop, c :: cs => checkCert5 m c && verifyCerts5 (m + 1) stop cs

private lemma exists_cert5_of_verify :
    ∀ (start stop : ℕ) (cs : List Cert5), verifyCerts5 start stop cs = true →
      ∀ m, start ≤ m → m < stop → ∃ c, checkCert5 m c = true
  | start, stop, [], h, m, hm1, hm2 => by
    simp only [verifyCerts5, beq_iff_eq] at h
    omega
  | start, stop, c :: cs, h, m, hm1, hm2 => by
    simp only [verifyCerts5, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le hm1 with rfl | hlt
    · exact ⟨c, h.1⟩
    · exact exists_cert5_of_verify (start + 1) stop cs h.2 m (by omega) hm2

def certs5_0 : List Cert5 := [
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 1, [1], [-2]⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 6, 0, [1], []⟩, ⟨false, 7, 0, [-1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 1, [3, -2], [-6, 2]⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 6, 0, [1], []⟩,
  ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 5, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 1, [-1, 2], [10, -4]⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 7, 0, [-1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 5, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 7, 0, [-1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 3, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 1, [1], [-2]⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 7, 0, [-1], []⟩, ⟨false, 0, 1, [1], [0, -2]⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 7, 0, [-1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 6, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 1, [-1, 2], [10, -4]⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 5, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 6, 0, [1], []⟩,
  ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 1, [2, -4, 1], [-6, 2]⟩,
  ⟨false, 3, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩,
  ⟨false, 3, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 7, 0, [-1], []⟩, ⟨false, 7, 0, [-1], []⟩,
  ⟨false, 3, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩,
  ⟨false, 3, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩
]

private lemma certs5_0_ok : verifyCerts5 0 128 certs5_0 = true := by decide

def certs5_1 : List Cert5 := [
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 6, 0, [1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 5, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 1, [-1, 2], [10, -4]⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 6, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 5, 0, [1], []⟩, ⟨false, 6, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 1, [1], [-2]⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 5, 0, [1], []⟩, ⟨false, 5, 0, [1], []⟩, ⟨false, 6, 0, [1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 1, [0, 1], [2]⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 1, [1], [2, -2]⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨true, 0, 0, [], []⟩, ⟨false, 6, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 1, 0, [1, 1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨true, 0, 0, [], []⟩, ⟨false, 6, 0, [1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 2, 0, [-1, -1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 11, 0, [1], []⟩, ⟨false, 7, 0, [-1], []⟩,
  ⟨false, 7, 0, [-1], []⟩, ⟨false, 11, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 11, 0, [1], []⟩, ⟨false, 1, 0, [1, 1], []⟩,
  ⟨false, 7, 0, [-1], []⟩, ⟨false, 2, 0, [-1, -1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩
]

private lemma certs5_1_ok : verifyCerts5 128 256 certs5_1 = true := by decide

def certs5_2 : List Cert5 := [
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 6, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 1, [1], [0, -2]⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 6, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 7, 0, [-1], []⟩, ⟨false, 0, 1, [-1, 2], [10, -4]⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩,
  ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 1, [1], [2, -2]⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨true, 0, 0, [], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 7, 0, [-1], []⟩, ⟨false, 1, 0, [1, 1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 6, 0, [1], []⟩, ⟨false, 7, 0, [-1], []⟩, ⟨false, 0, 1, [1, 1], [4, 2]⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 5, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨true, 0, 0, [], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 7, 0, [-1], []⟩, ⟨false, 6, 0, [1, 1], []⟩,
  ⟨false, 3, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 11, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩,
  ⟨false, 3, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 11, 0, [1], []⟩, ⟨false, 1, 0, [1, 1], []⟩,
  ⟨false, 3, 0, [1], []⟩, ⟨false, 11, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩,
  ⟨false, 3, 0, [1], []⟩, ⟨false, 6, 0, [1, 1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩
]

private lemma certs5_2_ok : verifyCerts5 256 384 certs5_2 = true := by decide

def certs5_3 : List Cert5 := [
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 5, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 7, 0, [-1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 1, [2, -4, 1], [-6, 2]⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 6, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 6, 0, [1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩,
  ⟨false, 3, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨true, 0, 0, [], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 7, 0, [-1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1, 1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 11, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 6, 0, [1], []⟩,
  ⟨false, 6, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 11, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 11, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 1, 0, [1, 1], []⟩,
  ⟨false, 6, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1, 1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨true, 0, 0, [], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 6, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 7, 0, [-1, -1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 11, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 11, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 1, 0, [1, 1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 11, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 7, 0, [-1, -1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 0, 1, [1, -1], [-2]⟩, ⟨false, 0, 1, [1, -1], [-2]⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 1, [0, 1], [2]⟩, ⟨false, 0, 1, [0, 1], [2]⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩
]

private lemma certs5_3_ok : verifyCerts5 384 512 certs5_3 = true := by decide

def certs5_4 : List Cert5 := [
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 6, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 1, [3, 2], [-4, -2]⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 1, [1], [-1]⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 6, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 11, 0, [1], []⟩, ⟨false, 0, 1, [2, 2, -1], [-6, 2]⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨true, 0, 0, [], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 11, 0, [1], []⟩, ⟨false, 2, 0, [-1, -1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 6, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 11, 0, [1], []⟩, ⟨false, 0, 1, [1, -1], [0, 2]⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨true, 0, 0, [], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 11, 0, [1], []⟩, ⟨false, 6, 0, [1, 1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 10, 0, [1], []⟩,
  ⟨false, 3, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩,
  ⟨false, 7, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 7, 0, [-1], []⟩, ⟨false, 2, 0, [-1, -1], []⟩,
  ⟨false, 3, 0, [1], []⟩, ⟨false, 7, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 6, 0, [1, 1], []⟩,
  ⟨false, 3, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩
]

private lemma certs5_4_ok : verifyCerts5 512 640 certs5_4 = true := by decide

def certs5_5 : List Cert5 := [
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 6, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 11, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 1, [2, 2, -1], [-6, 2]⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨true, 0, 0, [], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 11, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 3, 0, [1, 1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 6, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 6, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 7, 0, [-1], []⟩, ⟨false, 6, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 6, 0, [1], []⟩, ⟨false, 7, 0, [-1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 7, 0, [-1], []⟩, ⟨false, 6, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 2, 0, [-1, -1], []⟩, ⟨false, 3, 0, [1, 1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨true, 0, 0, [], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 6, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 11, 0, [1, 1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 7, 0, [-1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 7, 0, [-1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 2, 0, [-1, -1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 7, 0, [-1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 11, 0, [1, 1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 1, [5, -2], [-2, 4]⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 1, [1, 1], [-2]⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 1, [0, -1], [2]⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 1, [2, -1], [-6, 2]⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩
]

private lemma certs5_5_ok : verifyCerts5 640 768 certs5_5 = true := by decide

def certs5_6 : List Cert5 := [
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 7, 0, [-1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 11, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 1, [1, -1], [0, 2]⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨true, 0, 0, [], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 11, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 7, 0, [-1, -1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨true, 0, 0, [], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 7, 0, [-1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 11, 0, [1, 1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 6, 0, [1, 1], []⟩, ⟨false, 7, 0, [-1, -1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 6, 0, [1, 1], []⟩,
  ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 11, 0, [1, 1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 7, 0, [-1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 1, [2, -1], [-2, 2]⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 1, [0, -1], [2]⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 5, [-3, 1], [5, 1, -1]⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 5, [-14, 5], [17, -1, -5]⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 7, 0, [-1], []⟩, ⟨false, 1, 0, [1], []⟩
]

private lemma certs5_6_ok : verifyCerts5 768 896 certs5_6 = true := by decide

def certs5_7 : List Cert5 := [
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 15, 0, [1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 6, 0, [1], []⟩, ⟨false, 6, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1, 1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 6, 0, [1], []⟩, ⟨false, 7, 0, [-1, -1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 6, 0, [1], []⟩, ⟨false, 6, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 3, 0, [1, 1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 6, 0, [1], []⟩, ⟨false, 11, 0, [1, 1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 0, 1, [5, -2], [-2, 4]⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 1, [1, 1], [-2]⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 1, [0, -1], [2]⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 1, [2, -1], [-6, 2]⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 7, 0, [-1, -1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 11, 0, [1, 1], []⟩, ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 6, 0, [1], []⟩, ⟨false, 0, 1, [2, -1], [-2, 2]⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 1, [0, -1], [2]⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 5, [-3, 1], [5, 1, -1]⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 0, 5, [-14, 5], [17, -1, -5]⟩, ⟨false, 6, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 6, 0, [1], []⟩, ⟨false, 0, 1, [2, -1], [-6, 2]⟩, ⟨false, 0, 1, [2, -1], [-6, 2]⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 0, 5, [-14, 5], [17, -1, -5]⟩, ⟨false, 0, 5, [-14, 5], [17, -1, -5]⟩, ⟨false, 6, 0, [1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩,
  ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩,
  ⟨false, 0, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩, ⟨false, 1, 0, [1], []⟩,
  ⟨false, 2, 0, [-1], []⟩, ⟨false, 2, 0, [-1], []⟩, ⟨false, 3, 0, [1], []⟩, ⟨false, 0, 0, [1], []⟩
]

private lemma certs5_7_ok : verifyCerts5 896 1024 certs5_7 = true := by decide

private lemma exists_cert5_of_lt1024 (m : ℕ) (hm : m < 1024) :
    ∃ c, checkCert5 m c = true := by
  by_cases h0 : m < 128
  · exact exists_cert5_of_verify 0 128 certs5_0 certs5_0_ok m (by omega) h0
  · by_cases h1 : m < 256
    · exact exists_cert5_of_verify 128 256 certs5_1 certs5_1_ok m (by omega) h1
    · by_cases h2 : m < 384
      · exact exists_cert5_of_verify 256 384 certs5_2 certs5_2_ok m (by omega) h2
      · by_cases h3 : m < 512
        · exact exists_cert5_of_verify 384 512 certs5_3 certs5_3_ok m (by omega) h3
        · by_cases h4 : m < 640
          · exact exists_cert5_of_verify 512 640 certs5_4 certs5_4_ok m (by omega) h4
          · by_cases h5 : m < 768
            · exact exists_cert5_of_verify 640 768 certs5_5 certs5_5_ok m (by omega) h5
            · by_cases h6 : m < 896
              · exact exists_cert5_of_verify 768 896 certs5_6 certs5_6_ok m (by omega) h6
              · exact exists_cert5_of_verify 896 1024 certs5_7 certs5_7_ok m (by omega) hm

def addUV : List (List ℤ) → List (List ℤ) → List (List ℤ)
  | [], b => b
  | a, [] => a
  | x :: xs, y :: ys => addZ x y :: addUV xs ys

def subUV : List (List ℤ) → List (List ℤ) → List (List ℤ)
  | [], b => b.map (fun r => r.map (-·))
  | a, [] => a
  | x :: xs, y :: ys => subZ x y :: subUV xs ys

def mulUV : List (List ℤ) → List (List ℤ) → List (List ℤ)
  | [], _ => []
  | x :: xs, b => addUV (b.map (mulZ x)) ([] :: mulUV xs b)

def det3UV (m00 m01 m02 m10 m11 m12 m20 m21 m22 : List (List ℤ)) : List (List ℤ) :=
  addUV
    (subUV
      (mulUV m00 (subUV (mulUV m11 m22) (mulUV m12 m21)))
      (mulUV m01 (subUV (mulUV m10 m22) (mulUV m12 m20))))
    (mulUV m02 (subUV (mulUV m10 m21) (mulUV m11 m20)))

def reduceU2 : List (List ℤ) → List ℤ × List ℤ
  | [] => ([], [])
  | c :: cs =>
    let (r0, r1) := reduceU2 cs
    (addZ c r1, addZ r0 r1)

def sub5At : ℕ → ℕ × ℕ × ℕ
  | 0 => (1, 2, 3) | 1 => (1, 2, 4) | 2 => (1, 2, 5) | 3 => (1, 3, 4) | 4 => (1, 3, 5)
  | 5 => (1, 4, 5) | 6 => (2, 3, 4) | 7 => (2, 3, 5) | 8 => (2, 4, 5) | _ => (3, 4, 5)

def d2UV6 (tv a1 a2 a b : ℕ) : List (List ℤ) :=
  if a == b then []
  else
    let x := min a b
    let y := max a b
    if y < 5 then
      if isC5EdgeNat x y then [[1]] else [[1], [1]]
    else
      if x == tv then [[1, 1], [1]]
      else if x == a1 || x == a2 then [[1]]
      else [[1], [1]]

def minor6UV (tv a1 a2 idx : ℕ) : List (List ℤ) :=
  let (r1, r2, r3) := sub5At (idx / 10)
  let (c1, c2, c3) := sub5At (idx % 10)
  let g (a b : ℕ) := subUV (addUV (d2UV6 tv a1 a2 0 a) (d2UV6 tv a1 a2 0 b)) (d2UV6 tv a1 a2 a b)
  det3UV (g r1 c1) (g r1 c2) (g r1 c3)
         (g r2 c1) (g r2 c2) (g r2 c3)
         (g r3 c1) (g r3 c2) (g r3 c3)

abbrev Cert6 := ℕ × ℕ × ℕ × ℕ × ℤ

def certs6Data : List Cert6 :=
  [
    (0, 1, 2, 2, 1), (0, 1, 3, 2, 1), (0, 1, 4, 2, 1), (0, 2, 3, 29, 1), (0, 2, 4, 12, 1), (0, 3, 4, 2, 1), (1, 0, 2, 2, -1), (1, 0, 3, 2, -1), (1, 0, 4, 2, -1), (1, 2, 3, 2, -1),
    (1, 2, 4, 2, -1), (1, 3, 4, 57, 1), (2, 0, 1, 2, 1), (2, 0, 3, 2, 1), (2, 0, 4, 24, 1), (2, 1, 3, 2, 1), (2, 1, 4, 2, 1), (2, 3, 4, 2, 1), (3, 0, 1, 22, 1), (3, 0, 2, 2, -1),
    (3, 0, 4, 2, -1), (3, 1, 2, 2, -1), (3, 1, 4, 12, 1), (3, 2, 4, 2, -1), (4, 0, 1, 2, 1), (4, 0, 2, 2, -1), (4, 0, 3, 12, -1), (4, 1, 2, 22, 1), (4, 1, 3, 2, 1), (4, 2, 3, 2, -1)
  ]

def allN6Triples : List (ℕ × ℕ × ℕ) :=
  (List.range 5).flatMap fun tv =>
    (List.range 5).flatMap fun a1 =>
      (List.range 5).flatMap fun a2 =>
        if a1 < a2 && a1 != tv && a2 != tv then [(tv, a1, a2)] else []

def checkCert6 (c : Cert6) : Bool :=
  let (tv, a1, a2, idx, sgn) := c
  let (r0, r1) := reduceU2 (minor6UV tv a1 a2 idx)
  let sr0 := r0.map (sgn * ·)
  let sr1 := r1.map (sgn * ·)
  idx < 100 && (sgn == 1 || sgn == -1) &&
  sr0.all (0 ≤ ·) && sr1.all (0 ≤ ·) && (sr0.any (0 < ·) || sr1.any (0 < ·))

def verifyCerts6 : Bool :=
  allN6Triples.all fun t =>
    certs6Data.any fun c => c.1 == t.1 && c.2.1 == t.2.1 && c.2.2.1 == t.2.2 && checkCert6 c

private lemma verifyCerts6_ok : verifyCerts6 = true := by decide

lemma distMult_map_fin {n : ℕ} (q : Fin n ↪ Pt) (d : ℝ) :
    distMult (Finset.univ.map q) d =
      ((Finset.univ.filter fun ab : Fin n × Fin n =>
        ab.1 < ab.2 ∧ dist (q ab.1) (q ab.2) = d)).card := by
  unfold distMult
  symm
  refine Finset.card_bij (fun ab _ => ({q ab.1, q ab.2} : Finset Pt)) ?_ ?_ ?_
  · intro ab hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab
    have hne : q ab.1 ≠ q ab.2 := fun h => ne_of_lt hab.1 (q.injective h)
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, Finset.card_pair hne⟩, ?_⟩
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> exact Finset.mem_map.mpr ⟨_, Finset.mem_univ _, rfl⟩
    · exact (pairHasDist_pair_iff hne d).mpr hab.2
  · intro ab₁ hab₁ ab₂ hab₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab₁ hab₂
    have hmem1 : q ab₁.1 ∈ ({q ab₂.1, q ab₂.2} : Finset Pt) := heq ▸ Finset.mem_insert_self _ _
    have hmem2 : q ab₁.2 ∈ ({q ab₂.1, q ab₂.2} : Finset Pt) :=
      heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem1 hmem2
    rcases hmem1 with h1 | h1 <;> rcases hmem2 with h2 | h2
    · have h1' := q.injective h1
      have h2' := q.injective h2
      exact False.elim (lt_irrefl _ (h1' ▸ h2' ▸ hab₁.1))
    · exact Prod.ext (q.injective h1) (q.injective h2)
    · have h1' := q.injective h1
      have h2' := q.injective h2
      exact False.elim (lt_asymm hab₁.1 (h1' ▸ h2' ▸ hab₂.1))
    · have h1' := q.injective h1
      have h2' := q.injective h2
      exact False.elim (lt_irrefl _ (h1' ▸ h2' ▸ hab₁.1))
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hs
    obtain ⟨p, q', hpq', rfl⟩ := Finset.card_eq_two.mp hs.1.2
    have hpX : p ∈ Finset.univ.map q := hs.1.1 (Finset.mem_insert_self _ _)
    have hqX : q' ∈ Finset.univ.map q := hs.1.1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hpX
    obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hqX
    have hab_ne : a ≠ b := fun h => hpq' (by rw [h])
    have hd : dist (q a) (q b) = d := (pairHasDist_pair_iff hpq' d).mp hs.2
    rcases lt_or_gt_of_ne hab_ne with hab | hba
    · exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hd⟩, rfl⟩
    · refine ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hba, ?_⟩, ?_⟩
      · rw [dist_comm]; exact hd
      · exact Finset.pair_comm (q b) (q a)

lemma distMult_erase_eq {X : Finset Pt} {x : Pt} (hx : x ∈ X) (d : ℝ) :
    distMult X d =
      distMult (X.erase x) d + ((X.erase x).filter (fun y => dist x y = d)).card := by
  unfold distMult
  have hsplit : (X.powersetCard 2).filter (PairHasDist d) =
      ((X.erase x).powersetCard 2).filter (PairHasDist d) ∪
      (((X.erase x).filter (fun y => dist x y = d)).image (fun y => ({x, y} : Finset Pt))) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_union, Finset.mem_image,
      Finset.subset_erase]
    constructor
    · rintro ⟨⟨he_sub, he_card⟩, hpd⟩
      by_cases hxe : x ∈ e
      · right
        obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp he_card
        have hd : dist p q = d := (pairHasDist_pair_iff hpq d).mp hpd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
        rcases hxe with rfl | rfl
        · exact ⟨q, ⟨Finset.mem_erase.mpr
            ⟨hpq.symm, he_sub (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩, hd⟩, rfl⟩
        · refine ⟨p, ⟨Finset.mem_erase.mpr
            ⟨hpq, he_sub (Finset.mem_insert_self _ _)⟩, ?_⟩, Finset.pair_comm x p⟩
          rw [dist_comm]; exact hd
      · exact Or.inl ⟨⟨⟨he_sub, hxe⟩, he_card⟩, hpd⟩
    · rintro (⟨⟨⟨he_sub, _⟩, he_card⟩, hpd⟩ | ⟨y, ⟨hy_er, hdy⟩, rfl⟩)
      · exact ⟨⟨he_sub, he_card⟩, hpd⟩
      · have hyX := Finset.mem_erase.mp hy_er
        refine ⟨⟨Finset.insert_subset_iff.mpr ⟨hx, Finset.singleton_subset_iff.mpr hyX.2⟩,
          Finset.card_pair hyX.1.symm⟩, (pairHasDist_pair_iff hyX.1.symm d).mpr hdy⟩
  have hdisj : Disjoint (((X.erase x).powersetCard 2).filter (PairHasDist d))
      (((X.erase x).filter (fun y => dist x y = d)).image (fun y => ({x, y} : Finset Pt))) := by
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_erase, Finset.mem_image] at he₁ he₂
    obtain ⟨y, _, rfl⟩ := he₂
    exact he₁.1.1.2 (Finset.mem_insert_self _ _)
  have hinj : Set.InjOn (fun y => ({x, y} : Finset Pt))
      ((X.erase x).filter (fun y => dist x y = d)) := by
    intro y₁ hy₁ y₂ _ heq
    dsimp only at heq
    have hx1 : x ≠ y₁ := (Finset.mem_erase.mp (Finset.mem_filter.mp hy₁).1).1.symm
    have hy1_mem : y₁ ∈ ({x, y₂} : Finset Pt) := heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy1_mem
    exact hy1_mem.resolve_left hx1.symm
  rw [hsplit, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj]

lemma two_le_card_distSet_of_four_le {X : Finset Pt} (hX : 4 ≤ X.card) :
    2 ≤ (distSet X).card := by
  obtain ⟨D, hD_mem, _, hD_mult⟩ := diameter_multiplicity_le_card (by omega : 2 ≤ X.card)
  have hpos : 1 ≤ (distSet X).card := Finset.card_pos.mpr ⟨D, hD_mem⟩
  by_contra hlt
  have hc1 : (distSet X).card = 1 := by omega
  obtain ⟨d₀, hd₀_eq⟩ := Finset.card_eq_one.mp hc1
  have hDd : D = d₀ := by
    have : D ∈ ({d₀} : Finset ℝ) := hd₀_eq ▸ hD_mem
    exact Finset.mem_singleton.mp this
  subst hDd
  have hsum := sum_distMult_eq_choose X
  rw [hd₀_eq, Finset.sum_singleton] at hsum
  have hchoose : X.card < Nat.choose X.card 2 := by
    rw [Nat.choose_two_right]
    have hmul : 2 * X.card + 2 ≤ X.card * (X.card - 1) := by
      have : 3 ≤ X.card - 1 := by omega
      nlinarith
    have hdiv := Nat.div_add_mod (X.card * (X.card - 1)) 2
    have hmod := Nat.mod_lt (X.card * (X.card - 1)) (by omega : 0 < 2)
    omega
  omega

lemma choose_two_r_add_two (r : ℕ) :
    Nat.choose (2 * r + 2) 2 = 1 + r * (2 * r + 3) := by
  rw [Nat.choose_two_right]
  have hsub : 2 * r + 2 - 1 = 2 * r + 1 := by omega
  rw [hsub]
  have hmul : (2 * r + 2) * (2 * r + 1) = 2 * (1 + r * (2 * r + 3)) := by ring
  rw [hmul, Nat.mul_div_right _ (by omega)]

lemma even_tight_violator_descent {r : ℕ} (hr : 1 ≤ r) {X : Finset Pt}
    (hcard : X.card = 2 * r + 2) (hdist : (distSet X).card = r + 1)
    (hviol : ¬ 2 ≤ (rareDistances X).card) :
    ∃ D ∈ distSet X, ∃ x ∈ X, ∃ v₀ ∈ X.erase x,
      (∀ a ∈ X, ∀ b ∈ X, dist a b ≤ D) ∧
      distMult X D = 1 ∧
      dist x v₀ = D ∧
      (∀ d ∈ distSet X \ {D}, d < D ∧ distMult X d = 2 * r + 3) ∧
      distSet (X.erase x) ⊆ distSet X \ {D} ∧
      ∀ y ∈ (X.erase x).erase v₀, dist x y ∈ distSet X \ {D} := by
  have hrare1 : 1 ≤ (rareDistances X).card := one_le_card_rareDistances (by omega)
  have hrare_eq1 : (rareDistances X).card = 1 := by omega
  obtain ⟨D, hD_mem, hdiam, hD_mult⟩ := diameter_multiplicity_le_card (by omega : 2 ≤ X.card)
  have hD_rare : D ∈ rareDistances X := Finset.mem_filter.mpr ⟨hD_mem, hD_mult⟩
  have hrare_eq : rareDistances X = {D} := by
    obtain ⟨d₀, hd₀⟩ := Finset.card_eq_one.mp hrare_eq1
    have hDd₀ : D = d₀ := Finset.mem_singleton.mp (hd₀ ▸ hD_rare)
    simpa [hDd₀] using hd₀
  let S := distSet X \ {D}
  have hS_eq : S = (distSet X).erase D := by
    ext d; simp [S, and_comm]
  have hS_card : S.card = r := by
    rw [card_erase_sub_one_ge hD_mem, hdist]; omega
  have hS_ge : ∀ d ∈ S, 2 * r + 3 ≤ distMult X d := by
    intro d hd
    have hd_mem : d ∈ distSet X := (Finset.mem_sdiff.mp hd).1
    have hd_ne : d ≠ D := by
      have := (Finset.mem_sdiff.mp hd).2
      simpa using this
    by_contra hlt
    have hmem : d ∈ rareDistances X := Finset.mem_filter.mpr ⟨hd_mem, by omega⟩
    rw [hrare_eq, Finset.mem_singleton] at hmem
    exact hd_ne hmem
  have hS_sum_ge : r * (2 * r + 3) ≤ ∑ d ∈ S, distMult X d := by
    calc
      r * (2 * r + 3) = S.card * (2 * r + 3) := by rw [hS_card]
      _ = ∑ _d ∈ S, (2 * r + 3) := by simp
      _ ≤ ∑ d ∈ S, distMult X d := Finset.sum_le_sum hS_ge
  have htot : distMult X D + ∑ d ∈ S, distMult X d = 1 + r * (2 * r + 3) := by
    have hsum := sum_distMult_eq_choose X
    rw [hcard, choose_two_r_add_two] at hsum
    rw [← hsum, hS_eq, Finset.add_sum_erase (distSet X) (distMult X) hD_mem]
  have hD1_pos : 1 ≤ distMult X D := distMult_pos_of_mem_distSet hD_mem
  have hD_eq1 : distMult X D = 1 := by omega
  have hS_sum_eq : ∑ d ∈ S, distMult X d = r * (2 * r + 3) := by omega
  have hS_info : ∀ d ∈ S, d < D ∧ distMult X d = 2 * r + 3 := by
    intro d₀ hd₀
    have hd₀_dist : d₀ ∈ distSet X := (Finset.mem_sdiff.mp hd₀).1
    have hd₀_ne : d₀ ≠ D := by simpa using (Finset.mem_sdiff.mp hd₀).2
    obtain ⟨a, ha, b, hb, _, hab⟩ := (mem_distSet_iff X d₀).mp hd₀_dist
    have hlt : d₀ < D := lt_of_le_of_ne (hab ▸ hdiam a ha b hb) hd₀_ne
    have hsplit_sum := Finset.add_sum_erase S (distMult X) hd₀
    have hrest_ge : (r - 1) * (2 * r + 3) ≤ ∑ d ∈ S.erase d₀, distMult X d := by
      calc
        (r - 1) * (2 * r + 3) = (S.erase d₀).card * (2 * r + 3) := by
          rw [Finset.card_erase_of_mem hd₀, hS_card]
        _ = ∑ _d ∈ S.erase d₀, (2 * r + 3) := by simp
        _ ≤ ∑ d ∈ S.erase d₀, distMult X d :=
          Finset.sum_le_sum (fun d hd => hS_ge d (Finset.erase_subset d₀ S hd))
    have hsplit_eq : 1 + (r - 1) = r := by omega
    have hmul_eq : (2 * r + 3) + (r - 1) * (2 * r + 3) = r * (2 * r + 3) := by
      calc
        (2 * r + 3) + (r - 1) * (2 * r + 3)
          = 1 * (2 * r + 3) + (r - 1) * (2 * r + 3) := by ring
        _ = (1 + (r - 1)) * (2 * r + 3) := by ring
        _ = r * (2 * r + 3) := by rw [hsplit_eq]
    have hd₀_ge := hS_ge d₀ hd₀
    refine ⟨hlt, by omega⟩
  obtain ⟨e₀, he₀_eq⟩ := Finset.card_eq_one.mp hD_eq1
  have he₀_mem : e₀ ∈ (X.powersetCard 2).filter (PairHasDist D) :=
    he₀_eq ▸ Finset.mem_singleton_self e₀
  have he₀_pc := Finset.mem_filter.mp he₀_mem
  have he₀_info := Finset.mem_powersetCard.mp he₀_pc.1
  obtain ⟨x, v₀, hxv₀, rfl⟩ := Finset.card_eq_two.mp he₀_info.2
  have hxX : x ∈ X := he₀_info.1 (Finset.mem_insert_self _ _)
  have hv₀X : v₀ ∈ X := he₀_info.1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hv₀_er : v₀ ∈ X.erase x := Finset.mem_erase.mpr ⟨hxv₀.symm, hv₀X⟩
  have hdxv₀ : dist x v₀ = D := (pairHasDist_pair_iff hxv₀ D).mp he₀_pc.2
  have huniq : ∀ a ∈ X, ∀ b ∈ X, a ≠ b → dist a b = D → ({a, b} : Finset Pt) = {x, v₀} := by
    intro a ha b hb hab hdist_ab
    have hmem : ({a, b} : Finset Pt) ∈ (X.powersetCard 2).filter (PairHasDist D) :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩,
          Finset.card_pair hab⟩, (pairHasDist_pair_iff hab D).mpr hdist_ab⟩
    rw [he₀_eq, Finset.mem_singleton] at hmem
    exact hmem
  refine ⟨D, hD_mem, x, hxX, v₀, hv₀_er, hdiam, hD_eq1, hdxv₀, hS_info, ?_, ?_⟩
  · intro d hd
    obtain ⟨a, ha, b, hb, hab, rfl⟩ := (mem_distSet_iff (X.erase x) d).mp hd
    have ha' := Finset.mem_erase.mp ha
    have hb' := Finset.mem_erase.mp hb
    refine Finset.mem_sdiff.mpr ⟨(mem_distSet_iff X _).mpr ⟨a, ha'.2, b, hb'.2, hab, rfl⟩, ?_⟩
    rw [Finset.mem_singleton]
    intro hD_eq
    have heq := huniq a ha'.2 b hb'.2 hab hD_eq
    have hxmem : x ∈ ({a, b} : Finset Pt) := heq ▸ Finset.mem_insert_self _ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem
    rcases hxmem with rfl | rfl
    · exact ha'.1 rfl
    · exact hb'.1 rfl
  · intro y hy
    have hy₁ := Finset.mem_erase.mp hy
    have hy₂ := Finset.mem_erase.mp hy₁.2
    refine Finset.mem_sdiff.mpr ⟨(mem_distSet_iff X _).mpr ⟨x, hxX, y, hy₂.2, hy₂.1.symm, rfl⟩, ?_⟩
    rw [Finset.mem_singleton]
    intro hD_eq
    have heq := huniq x hxX y hy₂.2 hy₂.1.symm hD_eq
    have hymem : y ∈ ({x, v₀} : Finset Pt) :=
      heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hymem
    rcases hymem with rfl | rfl
    · exact hy₂.1 rfl
    · exact hy₁.1 rfl

private lemma exists_mask_lt_pow :
    ∀ (n : ℕ) (f : ℕ → Bool), ∃ m < 2 ^ n, ∀ k < n, Nat.testBit m k = f k
  | 0, _ => ⟨0, by simp, fun k hk => by omega⟩
  | n + 1, f => by
    obtain ⟨m', hm', hbits⟩ := exists_mask_lt_pow n (fun k => f (k + 1))
    let m := 2 * m' + (if f 0 then 1 else 0)
    refine ⟨m, ?_, ?_⟩
    · have hm_lt : m < 2 * 2 ^ n := by dsimp only [m]; split_ifs <;> omega
      simpa [pow_succ, mul_comm] using hm_lt
    · intro k hk
      cases k with
      | zero =>
        simp only [m]
        cases hf0 : f 0 <;> simp [Nat.testBit_zero]
      | succ k =>
        simp only [m]
        have hdiv : (2 * m' + if f 0 then 1 else 0) / 2 = m' := by split_ifs <;> omega
        rw [Nat.testBit_succ, hdiv]
        exact hbits k (by omega)

private lemma pairIdx5_lt10 : ∀ a b : Fin 5, pairIdx5 a.val b.val < 10 := by
  decide

private lemma pair5At_pairIdx5 :
    ∀ a b : Fin 5, a ≠ b → pair5At (pairIdx5 a.val b.val) = (min a.val b.val, max a.val b.val) := by
  decide

private lemma pairIdx5_comm (a b : ℕ) : pairIdx5 a b = pairIdx5 b a := by
  simp only [pairIdx5, min_comm, max_comm]

private lemma isC5EdgeNat_comm (a b : ℕ) : isC5EdgeNat a b = isC5EdgeNat b a := by
  simp only [isC5EdgeNat, min_comm, max_comm]

private lemma sub4At_lt5 (t : ℕ) :
    (sub4At t).1 < 5 ∧ (sub4At t).2.1 < 5 ∧ (sub4At t).2.2 < 5 := by
  rcases eq_or_ne t 0 with rfl | h0
  · decide
  · rcases eq_or_ne t 1 with rfl | h1
    · decide
    · rcases eq_or_ne t 2 with rfl | h2
      · decide
      · simp [sub4At]

private lemma c5_poly_root_eq_zero {u : ℝ} (hu : 0 < u) (heval : evalZ u [4, 6, -2, -2] = 0) :
    u ^ 2 - u - 1 = 0 := by
  simp only [evalZ, Int.cast_ofNat, Int.cast_neg] at heval
  have hfac : (-2 : ℝ) * (u + 2) * (u ^ 2 - u - 1) =
      4 + u * (6 + u * (-2 + u * (-2 + u * 0))) := by ring
  rw [← hfac] at heval
  rcases mul_eq_zero.mp heval with h | h
  · linarith
  · exact h

theorem five_point_two_dist_structure {X : Finset Pt} (hcard : X.card = 5)
    {d₁ d₂ : ℝ} (h12 : d₁ < d₂) (hdist : distSet X = {d₁, d₂}) :
    0 < d₁ ∧ 0 < (d₂ / d₁) ^ 2 - 1 ∧
      ((d₂ / d₁) ^ 2 - 1) ^ 2 - ((d₂ / d₁) ^ 2 - 1) - 1 = 0 ∧
      distMult X d₁ = 5 ∧ distMult X d₂ = 5 ∧
      ∃ q : Fin 5 ↪ Pt, Finset.univ.map q = X ∧
        ∀ a b : Fin 5, a ≠ b → dist (q a) (q b) = if isC5EdgeNat a.val b.val then d₁ else d₂ := by
  have hd₁_mem : d₁ ∈ distSet X := by rw [hdist]; exact Finset.mem_insert_self _ _
  have hd₁_pos : 0 < d₁ := pos_of_mem_distSet hd₁_mem
  have hd₁_ne : d₁ ≠ 0 := ne_of_gt hd₁_pos
  let u : ℝ := (d₂ / d₁) ^ 2 - 1
  have h1u : 1 + u = (d₂ / d₁) ^ 2 := by simp [u]
  have hu_pos : 0 < u := by
    have hlt : 1 < d₂ / d₁ := (one_lt_div hd₁_pos).mpr h12
    have : 1 < (d₂ / d₁) ^ 2 := by nlinarith
    linarith
  let e : Fin 5 ≃ X := (Finset.equivFinOfCardEq hcard).symm
  let p : Fin 5 → Pt := fun i => (e i : Pt)
  have hp_inj : Function.Injective p := fun i j h => e.injective (Subtype.ext h)
  let edgeBool : ℕ → ℕ → Bool := fun a b =>
    if ha : a < 5 then if hb : b < 5 then decide (dist (p ⟨a, ha⟩) (p ⟨b, hb⟩) = d₁) else false else false
  let f : ℕ → Bool := fun k => let (a, b) := pair5At k; edgeBool a b
  obtain ⟨m, hm_lt, hbits⟩ := exists_mask_lt_pow 10 f
  have hpair_dist : ∀ a b : Fin 5, a ≠ b → dist (p a) (p b) = d₁ ∨ dist (p a) (p b) = d₂ := by
    intro a b hab
    have hmem : dist (p a) (p b) ∈ distSet X :=
      (mem_distSet_iff X _).mpr ⟨p a, (e a).2, p b, (e b).2, fun h => hab (hp_inj h), rfl⟩
    rw [hdist, Finset.mem_insert, Finset.mem_singleton] at hmem
    exact hmem
  have hbit_eq : ∀ a b : Fin 5, a ≠ b →
      Nat.testBit m (pairIdx5 a.val b.val) = decide (dist (p a) (p b) = d₁) := by
    intro a b hab
    rw [hbits (pairIdx5 a.val b.val) (pairIdx5_lt10 a b)]
    dsimp only [f]
    rw [pair5At_pairIdx5 a b hab]
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · have hmin : min a.val b.val = a.val := Nat.min_eq_left (Fin.le_def.mp (le_of_lt hlt))
      have hmax : max a.val b.val = b.val := Nat.max_eq_right (Fin.le_def.mp (le_of_lt hlt))
      simp [edgeBool, hmin, hmax, a.isLt, b.isLt]
    · have hmin : min a.val b.val = b.val := Nat.min_eq_right (Fin.le_def.mp (le_of_lt hgt))
      have hmax : max a.val b.val = a.val := Nat.max_eq_left (Fin.le_def.mp (le_of_lt hgt))
      simp [edgeBool, hmin, hmax, a.isLt, b.isLt, dist_comm]
  have hd2_eval : ∀ (a b : ℕ) (ha : a < 5) (hb : b < 5),
      evalZ u (d2Z5 m a b) = dist (p ⟨a, ha⟩) (p ⟨b, hb⟩) ^ 2 / d₁ ^ 2 := by
    intro a b ha hb
    by_cases hab : a = b
    · subst hab; simp [d2Z5, evalZ]
    · have hne : (⟨a, ha⟩ : Fin 5) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Fin.val h)
      have hb_eq := hbit_eq ⟨a, ha⟩ ⟨b, hb⟩ hne
      rcases hpair_dist ⟨a, ha⟩ ⟨b, hb⟩ hne with hd1 | hd2
      · have ht : Nat.testBit m (pairIdx5 a b) = true := by simpa [hd1] using hb_eq
        simp [d2Z5, hab, ht, evalZ, hd1, div_self (pow_ne_zero 2 hd₁_ne)]
      · have hne12 : dist (p ⟨a, ha⟩) (p ⟨b, hb⟩) ≠ d₁ := by rw [hd2]; exact ne_of_gt h12
        have hf : Nat.testBit m (pairIdx5 a b) = false := by simpa [hne12] using hb_eq
        simp only [d2Z5, beq_iff_eq, hab, ↓reduceIte, hf, Bool.false_eq_true]
        have he11 : evalZ u [1, 1] = 1 + u := by simp [evalZ]
        rw [he11, h1u, hd2, div_pow]
  have hgram_eval : ∀ (a b : ℕ) (ha : a < 5) (hb : b < 5),
      evalZ u (subZ (addZ (d2Z5 m 0 a) (d2Z5 m 0 b)) (d2Z5 m a b)) =
        gram2 (p 0) (p ⟨a, ha⟩) (p ⟨b, hb⟩) / d₁ ^ 2 := by
    intro a b ha hb
    rw [evalZ_sub, evalZ_add, hd2_eval 0 a (by omega) ha, hd2_eval 0 b (by omega) hb, hd2_eval a b ha hb]
    have hp0 : p ⟨0, by omega⟩ = p 0 := rfl
    rw [hp0]
    simp only [gram2]
    ring
  have hminor_zero : ∀ idx < 16, evalZ u (minor5Z m idx) = 0 := by
    intro idx _
    dsimp only [minor5Z]
    have hr := sub4At_lt5 (idx / 4)
    have hc := sub4At_lt5 (idx % 4)
    rw [evalZ_det3Z]
    rw [hgram_eval _ _ hr.1 hc.1, hgram_eval _ _ hr.1 hc.2.1, hgram_eval _ _ hr.1 hc.2.2,
        hgram_eval _ _ hr.2.1 hc.1, hgram_eval _ _ hr.2.1 hc.2.1, hgram_eval _ _ hr.2.1 hc.2.2,
        hgram_eval _ _ hr.2.2 hc.1, hgram_eval _ _ hr.2.2 hc.2.1, hgram_eval _ _ hr.2.2 hc.2.2]
    rw [det3R_div (d₁ ^ 2) (pow_ne_zero 2 hd₁_ne)]
    rw [planar_gram_minor3_eq_zero, zero_div]
  obtain ⟨c, hc⟩ := exists_cert5_of_lt1024 m hm_lt
  by_cases hc1 : c.1 = true
  · simp only [checkCert5, hc1, ↓reduceIte, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at hc
    obtain ⟨hm0, entry, hentry_mem, hm_entry⟩ := hc
    have hu_root : u ^ 2 - u - 1 = 0 := by
      apply c5_poly_root_eq_zero hu_pos
      rw [← hm0]
      exact hminor_zero 0 (by omega)
    have hc5_ok : checkC5Entry entry = true := List.all_eq_true.mp c5TableData_ok entry hentry_mem
    rcases entry with ⟨m', perm⟩
    dsimp only at hm_entry
    subst hm_entry
    simp only [checkC5Entry, Bool.and_eq_true, List.all_eq_true, List.mem_range,
      Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, decide_eq_true_eq,
      beq_iff_eq] at hc5_ok
    rcases hc5_ok with ⟨⟨⟨hlen, hbound⟩, hdistinct⟩, hc5bits⟩
    let permFn : Fin 5 → Fin 5 := fun i => ⟨perm.getD i.val 9, hbound i.val i.isLt⟩
    have hperm_inj : Function.Injective permFn := by
      intro i j hij
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rcases hdistinct i.val i.isLt j.val j.isLt with hnot | hne_p
        · exact False.elim (lt_irrefl _ (lt_of_lt_of_le hlt (Nat.not_lt.mp (by simpa using hnot))))
        · exact hne_p (congrArg Fin.val hij)
      · rcases hdistinct j.val j.isLt i.val i.isLt with hnot | hne_p
        · exact False.elim (lt_irrefl _ (lt_of_lt_of_le hgt (Nat.not_lt.mp (by simpa using hnot))))
        · exact hne_p (congrArg Fin.val hij.symm)
    let q : Fin 5 ↪ Pt := ⟨fun i => p (permFn i), fun i j hij => hperm_inj (hp_inj hij)⟩
    have hq_map : Finset.univ.map q = X := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro z hz
        obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hz
        exact (e (permFn i)).2
      · rw [Finset.card_map, Finset.card_fin, hcard]
    have hq_dist : ∀ a b : Fin 5, a ≠ b →
        dist (q a) (q b) = if isC5EdgeNat a.val b.val then d₁ else d₂ := by
      have haux : ∀ a b : Fin 5, a < b →
          dist (q a) (q b) = if isC5EdgeNat a.val b.val then d₁ else d₂ := by
        intro a b hab
        have hbit_c5 : Nat.testBit m' (pairIdx5 (permFn a).val (permFn b).val) = isC5EdgeNat a.val b.val := by
          rcases hc5bits a.val a.isLt b.val b.isLt with hnot | hok
          · exact False.elim (by exact absurd hab (by simpa using hnot))
          · exact hok
        have hne_p : permFn a ≠ permFn b := fun h => ne_of_lt hab (hperm_inj h)
        have hbit_real := hbit_eq (permFn a) (permFn b) hne_p
        have hdec : decide (dist (q a) (q b) = d₁) = isC5EdgeNat a.val b.val :=
          hbit_real.symm.trans hbit_c5
        cases hc5 : isC5EdgeNat a.val b.val
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hne1 : dist (q a) (q b) ≠ d₁ := by
            intro heq
            have : decide (dist (q a) (q b) = d₁) = true := decide_eq_true heq
            rw [hdec, hc5] at this
            contradiction
          exact (hpair_dist (permFn a) (permFn b) hne_p).resolve_left hne1
        · simp only [↓reduceIte]
          have : decide (dist (q a) (q b) = d₁) = true := hdec.trans hc5
          exact of_decide_eq_true this
      intro a b hab
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · exact haux a b hlt
      · rw [dist_comm, isC5EdgeNat_comm]
        exact haux b a hgt
    have hmult1 : distMult X d₁ = 5 := by
      rw [← hq_map, distMult_map_fin]
      have hfeq : (Finset.univ.filter fun ab : Fin 5 × Fin 5 =>
          ab.1 < ab.2 ∧ dist (q ab.1) (q ab.2) = d₁) =
          (Finset.univ.filter fun ab : Fin 5 × Fin 5 =>
            ab.1 < ab.2 ∧ isC5EdgeNat ab.1.val ab.2.val = true) := by
        ext ab
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor <;> rintro ⟨hab, hd⟩
        · refine ⟨hab, ?_⟩
          rw [hq_dist ab.1 ab.2 (ne_of_lt hab)] at hd
          cases hce : isC5EdgeNat ab.1.val ab.2.val
          · rw [hce] at hd; simp at hd; exact False.elim ((ne_of_lt h12) hd.symm)
          · rfl
        · refine ⟨hab, ?_⟩
          rw [hq_dist ab.1 ab.2 (ne_of_lt hab), hd]
          rfl
      rw [hfeq]
      decide
    have hmult2 : distMult X d₂ = 5 := by
      rw [← hq_map, distMult_map_fin]
      have hfeq : (Finset.univ.filter fun ab : Fin 5 × Fin 5 =>
          ab.1 < ab.2 ∧ dist (q ab.1) (q ab.2) = d₂) =
          (Finset.univ.filter fun ab : Fin 5 × Fin 5 =>
            ab.1 < ab.2 ∧ isC5EdgeNat ab.1.val ab.2.val = false) := by
        ext ab
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor <;> rintro ⟨hab, hd⟩
        · refine ⟨hab, ?_⟩
          rw [hq_dist ab.1 ab.2 (ne_of_lt hab)] at hd
          cases hce : isC5EdgeNat ab.1.val ab.2.val
          · rfl
          · rw [hce] at hd; simp at hd; exact False.elim ((ne_of_lt h12) hd)
        · refine ⟨hab, ?_⟩
          rw [hq_dist ab.1 ab.2 (ne_of_lt hab), hd]
          rfl
      rw [hfeq]
      decide
    exact ⟨hd₁_pos, hu_pos, hu_root, hmult1, hmult2, q, hq_map, hq_dist⟩
  · have hc_false : c.1 = false := Bool.eq_false_iff.mpr hc1
    simp only [checkCert5, hc_false, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
      decide_eq_true_eq] at hc
    rcases hc with ⟨⟨hi1, hi2⟩, hpos⟩
    have hz1 : evalZ u (minor5Z m c.2.1) = 0 := hminor_zero c.2.1 hi1
    have hz2 : evalZ u (minor5Z m c.2.2.1) = 0 := hminor_zero c.2.2.1 hi2
    have hcomb_pos := evalZ_pos_of_isPosZ hu_pos hpos
    rw [evalZ_add, evalZ_mul, hz1, mul_zero, zero_add] at hcomb_pos
    split_ifs at hcomb_pos with hemp
    · simp [evalZ] at hcomb_pos
    · rw [evalZ_mul, hz2, mul_zero] at hcomb_pos
      linarith

lemma no_five_point_one_dist {X : Finset Pt} (hcard : X.card = 5) :
    2 ≤ (distSet X).card :=
  two_le_card_distSet_of_four_le (by omega)

/-- **Unconditional Proof of Erdős #132 for `n = 5`**. -/
theorem erdos132_five : Erdos132For 5 := by
  intro X hcard
  have h2 := two_le_card_distSet_of_four_le (by omega : 4 ≤ X.card)
  by_cases h3 : 3 ≤ (distSet X).card
  · refine erdos132_of_many_distances (one_le_card_rareDistances (by omega)) ?_
    have hc5 : Nat.choose X.card 2 = 10 := by rw [hcard]; decide
    have hsub : 2 ≤ (distSet X).card - 1 := by omega
    rw [hc5, hcard]
    nlinarith
  · have hc2 : (distSet X).card = 2 := by omega
    obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hc2
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · obtain ⟨_, _, _, hm1, hm2, _⟩ := five_point_two_dist_structure hcard hlt hset
      have hrare : rareDistances X = {a, b} := by
        ext d
        simp only [rareDistances, Finset.mem_filter, hset, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hd, _⟩; exact hd
        · intro hd
          refine ⟨hd, ?_⟩
          rcases hd with rfl | rfl <;> omega
      rw [hrare, Finset.card_pair (ne_of_lt hlt)]
    · have hset' : distSet X = {b, a} := by rw [hset, Finset.pair_comm]
      obtain ⟨_, _, _, hm1, hm2, _⟩ := five_point_two_dist_structure hcard hgt hset'
      have hrare : rareDistances X = {b, a} := by
        ext d
        simp only [rareDistances, Finset.mem_filter, hset', Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hd, _⟩; exact hd
        · intro hd
          refine ⟨hd, ?_⟩
          rcases hd with rfl | rfl <;> omega
      rw [hrare, Finset.card_pair (ne_of_lt hgt)]

/-- **Exact 2-distance bound `g(2) = 5`**: no 6 planar points determine at most 2 distances. -/
theorem no_six_point_two_dist {X : Finset Pt} (hcard : X.card = 6) :
    3 ≤ (distSet X).card := by
  by_contra hlt
  have h2 := two_le_card_distSet_of_four_le (by omega : 4 ≤ X.card)
  have hc2 : (distSet X).card = 2 := by omega
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hc2
  wlog hlt_ab : a < b generalizing a b
  · exact this b a hab.symm (by rw [hset, Finset.pair_comm]) (lt_of_le_of_ne (not_lt.mp hlt_ab) hab.symm)
  have herase_mult : ∀ y ∈ X, distMult (X.erase y) a = 5 := by
    intro y hy
    have hy_card : (X.erase y).card = 5 := by rw [Finset.card_erase_of_mem hy, hcard]
    have hy_sub : distSet (X.erase y) ⊆ {a, b} := by
      rw [← hset]
      intro d hd
      obtain ⟨p, hp, q, hq, hpq, rfl⟩ := (mem_distSet_iff (X.erase y) d).mp hd
      exact (mem_distSet_iff X _).mpr ⟨p, Finset.erase_subset y X hp, q, Finset.erase_subset y X hq, hpq, rfl⟩
    have hy_ge2 := two_le_card_distSet_of_four_le (by omega : 4 ≤ (X.erase y).card)
    have hy_eq : distSet (X.erase y) = {a, b} :=
      Finset.eq_of_subset_of_card_le hy_sub (by simpa [Finset.card_pair (ne_of_lt hlt_ab)] using hy_ge2)
    exact (five_point_two_dist_structure hy_card hlt_ab hy_eq).2.2.2.1
  have hsum := sum_erase_distMult X a
  have hsum5 : ∑ y ∈ X, distMult (X.erase y) a = 30 := by
    calc
      ∑ y ∈ X, distMult (X.erase y) a = ∑ _y ∈ X, 5 := Finset.sum_congr rfl herase_mult
      _ = X.card * 5 := by simp
      _ = 30 := by rw [hcard]
  rw [hsum5, hcard] at hsum
  omega

def evalUV (u v : ℝ) : List (List ℤ) → ℝ
  | [] => 0
  | c :: cs => evalZ v c + u * evalUV u v cs

lemma evalUV_add (u v : ℝ) (a b : List (List ℤ)) :
    evalUV u v (addUV a b) = evalUV u v a + evalUV u v b := by
  induction a generalizing b with
  | nil => simp [addUV, evalUV]
  | cons x xs ih =>
    cases b with
    | nil => simp [addUV, evalUV]
    | cons y ys =>
      simp only [addUV, evalUV, evalZ_add, ih]
      ring

lemma evalUV_map_neg (u v : ℝ) (b : List (List ℤ)) :
    evalUV u v (b.map (fun r => r.map (-·))) = -evalUV u v b := by
  induction b with
  | nil => simp [evalUV]
  | cons y ys ih => simp [evalUV, evalZ_map_neg, ih]; ring

lemma evalUV_sub (u v : ℝ) (a b : List (List ℤ)) :
    evalUV u v (subUV a b) = evalUV u v a - evalUV u v b := by
  induction a generalizing b with
  | nil => simp [subUV, evalUV, evalUV_map_neg]
  | cons x xs ih =>
    cases b with
    | nil => simp [subUV, evalUV]
    | cons y ys =>
      simp only [subUV, evalUV, evalZ_sub, ih]
      ring

lemma evalUV_map_mul (u v : ℝ) (k : List ℤ) (b : List (List ℤ)) :
    evalUV u v (b.map (mulZ k)) = evalZ v k * evalUV u v b := by
  induction b with
  | nil => simp [evalUV]
  | cons y ys ih => simp [evalUV, evalZ_mul, ih]; ring

lemma evalUV_mul (u v : ℝ) (a b : List (List ℤ)) :
    evalUV u v (mulUV a b) = evalUV u v a * evalUV u v b := by
  induction a with
  | nil => simp [mulUV, evalUV]
  | cons x xs ih =>
    simp only [mulUV, evalUV_add, evalUV_map_mul, evalUV, evalZ, ih, zero_add]
    ring

lemma evalUV_det3UV (u v : ℝ) (m00 m01 m02 m10 m11 m12 m20 m21 m22 : List (List ℤ)) :
    evalUV u v (det3UV m00 m01 m02 m10 m11 m12 m20 m21 m22) =
      det3R (evalUV u v m00) (evalUV u v m01) (evalUV u v m02)
            (evalUV u v m10) (evalUV u v m11) (evalUV u v m12)
            (evalUV u v m20) (evalUV u v m21) (evalUV u v m22) := by
  simp only [det3UV, det3R, evalUV_add, evalUV_sub, evalUV_mul]

lemma evalUV_reduceU2 {u : ℝ} (hu : u ^ 2 - u - 1 = 0) (v : ℝ) :
    ∀ p : List (List ℤ),
      evalZ v (reduceU2 p).1 + u * evalZ v (reduceU2 p).2 = evalUV u v p
  | [] => by simp [reduceU2, evalUV, evalZ]
  | c :: cs => by
    have ih := evalUV_reduceU2 hu v cs
    dsimp only [reduceU2, evalUV]
    rw [evalZ_add, evalZ_add]
    have hu2 : u ^ 2 = u + 1 := by linarith
    calc
      evalZ v c + evalZ v (reduceU2 cs).2 + u * (evalZ v (reduceU2 cs).1 + evalZ v (reduceU2 cs).2)
        = evalZ v c + u * evalZ v (reduceU2 cs).1 + (u + 1) * evalZ v (reduceU2 cs).2 := by ring
      _ = evalZ v c + u * evalZ v (reduceU2 cs).1 + u ^ 2 * evalZ v (reduceU2 cs).2 := by rw [hu2]
      _ = evalZ v c + u * (evalZ v (reduceU2 cs).1 + u * evalZ v (reduceU2 cs).2) := by ring
      _ = evalZ v c + u * evalUV u v cs := by rw [ih]

private lemma sub5At_lt6 (t : ℕ) :
    (sub5At t).1 < 6 ∧ (sub5At t).2.1 < 6 ∧ (sub5At t).2.2 < 6 := by
  match t with
  | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide
  | 5 => decide | 6 => decide | 7 => decide | 8 => decide
  | n + 9 => simp [sub5At]

private lemma mem_allN6Triples (tv a1 a2 : Fin 5) (h12 : a1 < a2) (h1 : a1 ≠ tv) (h2 : a2 ≠ tv) :
    (tv.val, a1.val, a2.val) ∈ allN6Triples := by
  revert tv a1 a2 h12 h1 h2
  decide

private lemma checkCert6_refutes {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (hroot : u ^ 2 - u - 1 = 0)
    {c : Cert6} (hc : checkCert6 c = true) :
    evalUV u v (minor6UV c.1 c.2.1 c.2.2.1 c.2.2.2.1) ≠ 0 := by
  rcases c with ⟨tv, a1, a2, idx, sgn⟩
  simp only [checkCert6, Bool.and_eq_true] at hc
  rcases hc with ⟨⟨⟨⟨_, _⟩, hall0⟩, hall1⟩, hany⟩
  rw [← evalUV_reduceU2 hroot v (minor6UV tv a1 a2 idx)]
  have hs0 : 0 ≤ (sgn : ℝ) * evalZ v (reduceU2 (minor6UV tv a1 a2 idx)).1 := by
    rw [← evalZ_map_mul]
    exact evalZ_nonneg_of_all (le_of_lt hv) hall0
  have hs1 : 0 ≤ (sgn : ℝ) * evalZ v (reduceU2 (minor6UV tv a1 a2 idx)).2 := by
    rw [← evalZ_map_mul]
    exact evalZ_nonneg_of_all (le_of_lt hv) hall1
  intro heq
  have hmul0 : (sgn : ℝ) * (evalZ v (reduceU2 (minor6UV tv a1 a2 idx)).1 +
      u * evalZ v (reduceU2 (minor6UV tv a1 a2 idx)).2) = 0 := by
    rw [heq, mul_zero]
  rcases Bool.or_eq_true _ _ |>.mp hany with hpos0 | hpos1
  · have hstrict : 0 < (sgn : ℝ) * evalZ v (reduceU2 (minor6UV tv a1 a2 idx)).1 := by
      rw [← evalZ_map_mul]
      exact evalZ_pos_of_isPosZ hv (by simp [isPosZ, hall0, hpos0])
    nlinarith
  · have hstrict : 0 < (sgn : ℝ) * evalZ v (reduceU2 (minor6UV tv a1 a2 idx)).2 := by
      rw [← evalZ_map_mul]
      exact evalZ_pos_of_isPosZ hv (by simp [isPosZ, hall1, hpos1])
    nlinarith

/-- **Unconditional Proof of Erdős #132 for `n = 6`**. -/
theorem erdos132_six : Erdos132For 6 := by
  intro X hcard
  have h3 := no_six_point_two_dist hcard
  by_cases h4 : 4 ≤ (distSet X).card
  · refine erdos132_of_many_distances (one_le_card_rareDistances (by omega)) ?_
    have hc6 : Nat.choose X.card 2 = 15 := by rw [hcard]; decide
    have hsub : 3 ≤ (distSet X).card - 1 := by omega
    rw [hc6, hcard]
    nlinarith
  · have hc3 : (distSet X).card = 3 := by omega
    by_contra hviol
    obtain ⟨D, hD_mem, x, hxX, v₀, hv₀_er, hdiam, _, hdxv₀, hS_info, hY_sub, hx_er_mem⟩ :=
      even_tight_violator_descent (by omega : 1 ≤ 2) hcard hc3 hviol
    let Y := X.erase x
    have hY_card : Y.card = 5 := by rw [Finset.card_erase_of_mem hxX, hcard]
    let S := distSet X \ {D}
    have hS_card : S.card = 2 := by rw [card_erase_sub_one_ge hD_mem, hc3]
    obtain ⟨a', b', hab, hS_eq'⟩ := Finset.card_eq_two.mp hS_card
    obtain ⟨a, b, hlt_ab, hS_eq⟩ : ∃ a b, a < b ∧ S = {a, b} := by
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · exact ⟨a', b', hlt, hS_eq'⟩
      · exact ⟨b', a', hgt, by rw [hS_eq', Finset.pair_comm]⟩
    have hY_ge2 := two_le_card_distSet_of_four_le (by omega : 4 ≤ Y.card)
    have hY_sub' : distSet Y ⊆ {a, b} := hS_eq ▸ hY_sub
    have hY_dist : distSet Y = {a, b} :=
      Finset.eq_of_subset_of_card_le hY_sub' (by simpa [Finset.card_pair (ne_of_lt hlt_ab)] using hY_ge2)
    obtain ⟨ha_pos, hu_pos, hu_root, hm1, _, q, hq_map, hq_dist⟩ :=
      five_point_two_dist_structure hY_card hlt_ab hY_dist
    have ha_S : a ∈ distSet X \ {D} := by
      change a ∈ S; rw [hS_eq]; exact Finset.mem_insert_self _ _
    have hb_S : b ∈ distSet X \ {D} := by
      change b ∈ S; rw [hS_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have ha_info := hS_info a ha_S
    have hb_info := hS_info b hb_S
    have ha_mult7 : distMult X a = 7 := ha_info.2
    have hb_ltD : b < D := hb_info.1
    have ha_ne0 : a ≠ 0 := ne_of_gt ha_pos
    let u : ℝ := (b / a) ^ 2 - 1
    let v : ℝ := (D / a) ^ 2 - (b / a) ^ 2
    have hv_pos : 0 < v := by
      have hbd : b ^ 2 < D ^ 2 := by nlinarith
      have : (b / a) ^ 2 < (D / a) ^ 2 := by
        rw [div_pow, div_pow]
        exact div_lt_div_of_pos_right hbd (sq_pos_of_pos ha_pos)
      linarith
    have hv₀_Y : v₀ ∈ Finset.univ.map q := hq_map ▸ hv₀_er
    obtain ⟨tv, _, hqtv⟩ := Finset.mem_map.mp hv₀_Y
    have hxd_deg : (Y.filter (fun y => dist x y = a)).card = 2 := by
      have hmeq := distMult_erase_eq hxX a
      change distMult X a = distMult Y a + (Y.filter (fun y => dist x y = a)).card at hmeq
      rw [ha_mult7, hm1] at hmeq
      omega
    have hq_deg : ((Finset.univ : Finset (Fin 5)).filter (fun i => dist x (q i) = a)).card = 2 := by
      have him : Y.filter (fun y => dist x y = a) =
          ((Finset.univ : Finset (Fin 5)).filter (fun i => dist x (q i) = a)).image q := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hyY, hdy⟩
          have hy_map : y ∈ Finset.univ.map q := hq_map ▸ hyY
          obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hy_map
          exact ⟨i, hdy, rfl⟩
        · rintro ⟨i, hdi, rfl⟩
          exact ⟨hq_map ▸ Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩, hdi⟩
      rw [him, Finset.card_image_of_injective _ q.injective] at hxd_deg
      exact hxd_deg
    obtain ⟨k₁, k₂, hk12, hfil_eq'⟩ := Finset.card_eq_two.mp hq_deg
    obtain ⟨j₁, j₂, hj_ord, hfil_eq⟩ : ∃ j₁ j₂ : Fin 5, j₁ < j₂ ∧
        ((Finset.univ : Finset (Fin 5)).filter (fun i => dist x (q i) = a)) = {j₁, j₂} := by
      rcases lt_or_gt_of_ne hk12 with hlt | hgt
      · exact ⟨k₁, k₂, hlt, hfil_eq'⟩
      · exact ⟨k₂, k₁, hgt, by rw [hfil_eq', Finset.pair_comm]⟩
    have hdist_x_q : ∀ i : Fin 5, dist x (q i) = a ↔ i = j₁ ∨ i = j₂ := by
      intro i
      have hi : i ∈ (Finset.univ : Finset (Fin 5)).filter (fun k => dist x (q k) = a) ↔
          i ∈ ({j₁, j₂} : Finset (Fin 5)) := by rw [hfil_eq]
      simpa using hi
    have hj1_ne : j₁ ≠ tv := by
      intro h; subst h
      have : dist x (q j₁) = a := (hdist_x_q j₁).mpr (Or.inl rfl)
      rw [hqtv, hdxv₀] at this
      linarith [ha_info.1]
    have hj2_ne : j₂ ≠ tv := by
      intro h; subst h
      have : dist x (q j₂) = a := (hdist_x_q j₂).mpr (Or.inr rfl)
      rw [hqtv, hdxv₀] at this
      linarith [ha_info.1]
    have hx_q_all : ∀ i : Fin 5, i ≠ tv → dist x (q i) = a ∨ dist x (q i) = b := by
      intro i hi
      have hqiY : q i ∈ Y := hq_map ▸ Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
      have hmem_er : q i ∈ (X.erase x).erase v₀ :=
        Finset.mem_erase.mpr ⟨fun h => hi (q.injective (hqtv ▸ h)), hqiY⟩
      have hmemS := hx_er_mem (q i) hmem_er
      rw [show distSet X \ {D} = S from rfl, hS_eq] at hmemS
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hmemS
    have hev_1 : evalUV u v [[1]] = 1 := by simp [evalUV, evalZ]
    have hev_u : evalUV u v [[1], [1]] = b ^ 2 / a ^ 2 := by
      simp only [evalUV, evalZ, Int.cast_one, mul_zero, add_zero, mul_one, u]
      field_simp [ha_ne0]
      ring
    have hev_uv : evalUV u v [[1, 1], [1]] = D ^ 2 / a ^ 2 := by
      simp only [evalUV, evalZ, Int.cast_one, mul_zero, add_zero, mul_one, u, v]
      field_simp [ha_ne0]
      ring
    let p6 : ℕ → Pt := fun k => if hk : k < 5 then q ⟨k, hk⟩ else x
    have hd2_6 : ∀ r c : ℕ, r < 6 → c < 6 →
        evalUV u v (d2UV6 tv.val j₁.val j₂.val r c) = dist (p6 r) (p6 c) ^ 2 / a ^ 2 := by
      intro r c hr hc
      by_cases hrc : r = c
      · subst hrc; simp [d2UV6, evalUV]
      · simp only [d2UV6, beq_iff_eq, hrc, ↓reduceIte]
        have hlt_max : min r c < max r c := lt_of_le_of_ne (min_le_max) (fun h => hrc (by omega))
        have hdist_symm : dist (p6 r) (p6 c) = dist (p6 (min r c)) (p6 (max r c)) := by
          rcases le_total r c with hle | hle
          · rw [min_eq_left hle, max_eq_right hle]
          · rw [min_eq_right hle, max_eq_left hle, dist_comm]
        rw [hdist_symm]
        by_cases hmax5 : max r c < 5
        · have hmin5 : min r c < 5 := lt_trans hlt_max hmax5
          simp only [p6, hmin5, hmax5, ↓reduceDIte]
          have hne_fin : (⟨min r c, hmin5⟩ : Fin 5) ≠ ⟨max r c, hmax5⟩ :=
            fun h => ne_of_lt hlt_max (congrArg Fin.val h)
          rw [hq_dist ⟨min r c, hmin5⟩ ⟨max r c, hmax5⟩ hne_fin]
          dsimp only
          cases hce : isC5EdgeNat (min r c) (max r c)
          · simp only [Bool.false_eq_true, ↓reduceIte, hev_u]
          · simp only [↓reduceIte, hev_1, div_self (pow_ne_zero 2 ha_ne0)]
        · have hmax_eq5 : max r c = 5 := by omega
          have hmin5 : min r c < 5 := by omega
          simp only [p6, hmin5, hmax_eq5, lt_self_iff_false, ↓reduceDIte, ↓reduceIte]
          rw [dist_comm]
          let i : Fin 5 := ⟨min r c, hmin5⟩
          by_cases htv : min r c = tv.val
          · have hitv : (⟨min r c, hmin5⟩ : Fin 5) = tv := Fin.ext htv
            rw [ite_eq_left_iff.mpr (fun h => False.elim (h htv)), hitv, hqtv, hdxv₀, hev_uv]
          · rw [ite_eq_right_iff.mpr (fun h => False.elim (htv h))]
            have hi_ne_tv : i ≠ tv := fun h => htv (congrArg Fin.val h)
            by_cases hj : min r c = j₁.val ∨ min r c = j₂.val
            · have hor : (min r c == j₁.val || min r c == j₂.val) = true := by
                simp only [Bool.or_eq_true, beq_iff_eq]; exact hj
              have hi_dist : dist x (q ⟨min r c, hmin5⟩) = a := (hdist_x_q i).mpr (by
                rcases hj with h | h
                · exact Or.inl (Fin.ext h)
                · exact Or.inr (Fin.ext h))
              rw [hor, ite_eq_left_iff.mpr (fun h => False.elim (h rfl)), hev_1, hi_dist,
                div_self (pow_ne_zero 2 ha_ne0)]
            · push Not at hj
              have hne_b1 : (min r c == j₁.val) = false := beq_false_of_ne hj.1
              have hne_b2 : (min r c == j₂.val) = false := beq_false_of_ne hj.2
              have hor : (min r c == j₁.val || min r c == j₂.val) = false := by
                simp [hne_b1, hne_b2]
              have hi_ne1 : i ≠ j₁ := fun h => hj.1 (congrArg Fin.val h)
              have hi_ne2 : i ≠ j₂ := fun h => hj.2 (congrArg Fin.val h)
              have hi_dist : dist x (q ⟨min r c, hmin5⟩) = b := by
                rcases hx_q_all i hi_ne_tv with ha_eq | hb_eq
                · exfalso
                  rcases (hdist_x_q i).mp ha_eq with h1 | h2
                  · exact hi_ne1 h1
                  · exact hi_ne2 h2
                · exact hb_eq
              rw [hor, ite_eq_right_iff.mpr (fun h => False.elim (Bool.false_ne_true h)),
                hev_u, hi_dist]
    have hgram_6 : ∀ r c : ℕ, r < 6 → c < 6 →
        evalUV u v (subUV (addUV (d2UV6 tv.val j₁.val j₂.val 0 r) (d2UV6 tv.val j₁.val j₂.val 0 c))
          (d2UV6 tv.val j₁.val j₂.val r c)) = gram2 (p6 0) (p6 r) (p6 c) / a ^ 2 := by
      intro r c hr hc
      rw [evalUV_sub, evalUV_add, hd2_6 0 r (by omega) hr, hd2_6 0 c (by omega) hc, hd2_6 r c hr hc]
      simp only [gram2]
      ring
    have hminor_6 : ∀ idx : ℕ, evalUV u v (minor6UV tv.val j₁.val j₂.val idx) = 0 := by
      intro idx
      dsimp only [minor6UV]
      have hr := sub5At_lt6 (idx / 10)
      have hc := sub5At_lt6 (idx % 10)
      rw [evalUV_det3UV]
      rw [hgram_6 _ _ hr.1 hc.1, hgram_6 _ _ hr.1 hc.2.1, hgram_6 _ _ hr.1 hc.2.2,
          hgram_6 _ _ hr.2.1 hc.1, hgram_6 _ _ hr.2.1 hc.2.1, hgram_6 _ _ hr.2.1 hc.2.2,
          hgram_6 _ _ hr.2.2 hc.1, hgram_6 _ _ hr.2.2 hc.2.1, hgram_6 _ _ hr.2.2 hc.2.2]
      rw [det3R_div (a ^ 2) (pow_ne_zero 2 ha_ne0)]
      rw [planar_gram_minor3_eq_zero, zero_div]
    have hmem_tri : (tv.val, j₁.val, j₂.val) ∈ allN6Triples :=
      mem_allN6Triples tv j₁ j₂ hj_ord hj1_ne hj2_ne
    have hv6 := List.all_eq_true.mp verifyCerts6_ok (tv.val, j₁.val, j₂.val) hmem_tri
    rw [List.any_eq_true] at hv6
    obtain ⟨cert, _, hmatch⟩ := hv6
    simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
    rcases hmatch with ⟨⟨⟨hc1, hc2⟩, hc3'⟩, hcheck⟩
    have hne0 := checkCert6_refutes (show 0 < u from hu_pos) hv_pos hu_root hcheck
    rw [hc1, hc2, hc3'] at hne0
    exact hne0 (hminor_6 cert.2.2.2.1)

end PositivstellensatzN5N6

/-! ## Part 5: General Regular-Polygon Moment Obstruction (`m ≥ 4`) & `n = 8, 10, 14` -/

section RegularPolygonObstruction

/-- Canonical unit regular `m`-gon vertices on `S¹ ⊂ ℝ²`. -/
noncomputable def regPolyPt (m : ℕ) (j : Fin m) : Pt :=
  mkPt (Real.cos (2 * Real.pi * (j.val : ℝ) / m)) (Real.sin (2 * Real.pi * (j.val : ℝ) / m))

private lemma sum_exp_regPoly {m k : ℕ} (hm : 3 ≤ m) (hk0 : 0 < k) (hkm : k < m) :
    ∑ j : Fin m, Complex.exp (((2 * Real.pi * (k : ℝ) * (j.val : ℝ) / m : ℝ) : ℂ) * Complex.I) = 0 := by
  have hm_r : (m : ℝ) ≠ 0 := by positivity
  have hm_c : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  let theta : ℝ := 2 * Real.pi * (k : ℝ) / m
  let z : ℂ := Complex.exp ((theta : ℂ) * Complex.I)
  have hterm : ∀ j : Fin m,
      Complex.exp (((2 * Real.pi * (k : ℝ) * (j.val : ℝ) / m : ℝ) : ℂ) * Complex.I) = z ^ j.val := by
    intro j
    rw [← Complex.exp_natCast_mul]
    congr 1
    simp only [theta]
    push_cast
    ring
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun j => z ^ j) m]
  have hz1 : z ≠ 1 := by
    intro hz
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hz
    have h1 : (theta : ℂ) * Complex.I = (↑n * (2 * ↑Real.pi)) * Complex.I := by
      calc
        (theta : ℂ) * Complex.I = ↑n * (2 * ↑Real.pi * Complex.I) := hn
        _ = (↑n * (2 * ↑Real.pi)) * Complex.I := by ring
    have h2 : (theta : ℂ) = ↑n * (2 * ↑Real.pi) := mul_right_cancel₀ Complex.I_ne_zero h1
    have h3 : theta = (n : ℝ) * (2 * Real.pi) := by
      have hre := congrArg Complex.re h2
      simpa using hre
    have h4 : 2 * Real.pi * (k : ℝ) = 2 * Real.pi * ((n : ℝ) * m) := by
      calc
        2 * Real.pi * (k : ℝ) = theta * m := by simp only [theta]; field_simp [hm_r]
        _ = (n : ℝ) * (2 * Real.pi) * m := by rw [h3]
        _ = 2 * Real.pi * ((n : ℝ) * m) := by ring
    have hk_r : (k : ℝ) = (n : ℝ) * m :=
      mul_left_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero) h4
    have hk_z : (k : ℤ) = n * (m : ℤ) := by exact_mod_cast hk_r
    have hkz_pos : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk0
    have hkz_lt : (k : ℤ) < (m : ℤ) := by exact_mod_cast hkm
    have hm_pos : (0 : ℤ) < (m : ℤ) := by omega
    rcases le_or_gt n 0 with hn0 | hn1
    · have : n * (m : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hn0 (le_of_lt hm_pos)
      omega
    · have : (m : ℤ) ≤ n * (m : ℤ) := by nlinarith
      omega
  have hzm : z ^ m = 1 := by
    rw [← Complex.exp_natCast_mul]
    have hexp : (m : ℂ) * ((theta : ℂ) * Complex.I) = ↑(k : ℤ) * (2 * ↑Real.pi * Complex.I) := by
      simp only [theta]
      push_cast
      field_simp [hm_c]
    rw [hexp]
    exact Complex.exp_eq_one_iff.mpr ⟨k, rfl⟩
  have hgeom := geom_sum_mul z m
  rw [hzm, sub_self] at hgeom
  exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hz1)

lemma sum_cos_regPoly {m k : ℕ} (hm : 3 ≤ m) (hk0 : 0 < k) (hkm : k < m) :
    ∑ j : Fin m, Real.cos (2 * Real.pi * (k : ℝ) * (j.val : ℝ) / m) = 0 := by
  have hsum := congrArg Complex.re (sum_exp_regPoly hm hk0 hkm)
  rw [Complex.re_sum, Complex.zero_re] at hsum
  simpa only [Complex.exp_ofReal_mul_I_re] using hsum

lemma sum_sin_regPoly {m k : ℕ} (hm : 3 ≤ m) (hk0 : 0 < k) (hkm : k < m) :
    ∑ j : Fin m, Real.sin (2 * Real.pi * (k : ℝ) * (j.val : ℝ) / m) = 0 := by
  have hsum := congrArg Complex.im (sum_exp_regPoly hm hk0 hkm)
  rw [Complex.im_sum, Complex.zero_im] at hsum
  simpa only [Complex.exp_ofReal_mul_I_im] using hsum

lemma norm_sq_regPolyPt {m : ℕ} (j : Fin m) : ‖regPolyPt m j‖ ^ 2 = 1 := by
  rw [norm_sq_pt, regPolyPt, mkPt_zero, mkPt_one]
  exact Real.cos_sq_add_sin_sq _

lemma dist_origin_regPolyPt {m : ℕ} (j : Fin m) : dist (0 : Pt) (regPolyPt m j) = 1 := by
  rw [dist_zero_left]
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1), one_pow]
  exact norm_sq_regPolyPt j

/-- **Exact 2nd distance moment on `R_m`** (`m ≥ 3`): `∑ j, dist x v_j ^ 2 = m * (‖x‖^2 + 1)`. -/
theorem regPoly_moment2 {m : ℕ} (hm : 3 ≤ m) (x : Pt) :
    ∑ j : Fin m, dist x (regPolyPt m j) ^ 2 = (m : ℝ) * (‖x‖ ^ 2 + 1) := by
  have hpt : ∀ j : Fin m, dist x (regPolyPt m j) ^ 2 =
      (‖x‖ ^ 2 + 1) - 2 * x 0 * Real.cos (2 * Real.pi * (1 : ℕ) * (j.val : ℝ) / m) -
        2 * x 1 * Real.sin (2 * Real.pi * (1 : ℕ) * (j.val : ℝ) / m) := by
    intro j
    rw [dist_sq_pt, norm_sq_pt, regPolyPt, mkPt_zero, mkPt_one]
    have hcs := Real.cos_sq_add_sin_sq (2 * Real.pi * (j.val : ℝ) / m)
    push_cast
    linarith [show (x 0 - Real.cos (2 * Real.pi * (j.val : ℝ) / m)) ^ 2 +
        (x 1 - Real.sin (2 * Real.pi * (j.val : ℝ) / m)) ^ 2 =
        x 0 ^ 2 + x 1 ^ 2 + (Real.cos (2 * Real.pi * (j.val : ℝ) / m) ^ 2 +
          Real.sin (2 * Real.pi * (j.val : ℝ) / m) ^ 2) -
        2 * x 0 * Real.cos (2 * Real.pi * 1 * (j.val : ℝ) / m) -
        2 * x 1 * Real.sin (2 * Real.pi * 1 * (j.val : ℝ) / m) by ring]
  simp_rw [hpt]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [sum_cos_regPoly hm (by omega) (by omega), sum_sin_regPoly hm (by omega) (by omega)]
  ring

/-- **Exact 4th distance moment on `R_m`** (`m ≥ 3`): `∑ j, dist x v_j ^ 4 = m * (‖x‖^4 + 4‖x‖^2 + 1)`. -/
theorem regPoly_moment4 {m : ℕ} (hm : 3 ≤ m) (x : Pt) :
    ∑ j : Fin m, dist x (regPolyPt m j) ^ 4 = (m : ℝ) * (‖x‖ ^ 4 + 4 * ‖x‖ ^ 2 + 1) := by
  have hpt : ∀ j : Fin m, dist x (regPolyPt m j) ^ 4 =
      (‖x‖ ^ 4 + 4 * ‖x‖ ^ 2 + 1)
      - 4 * (‖x‖ ^ 2 + 1) * x 0 * Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) * (j.val : ℝ) / m)
      - 4 * (‖x‖ ^ 2 + 1) * x 1 * Real.sin (2 * Real.pi * ((1 : ℕ) : ℝ) * (j.val : ℝ) / m)
      + 2 * (x 0 ^ 2 - x 1 ^ 2) * Real.cos (2 * Real.pi * ((2 : ℕ) : ℝ) * (j.val : ℝ) / m)
      + 4 * x 0 * x 1 * Real.sin (2 * Real.pi * ((2 : ℕ) : ℝ) * (j.val : ℝ) / m) := by
    intro j
    let ang : ℝ := 2 * Real.pi * (j.val : ℝ) / m
    have ha1 : 2 * Real.pi * ((1 : ℕ) : ℝ) * (j.val : ℝ) / m = ang := by
      simp only [ang]; push_cast; ring
    have ha2 : 2 * Real.pi * ((2 : ℕ) : ℝ) * (j.val : ℝ) / m = 2 * ang := by
      simp only [ang]; push_cast; ring
    rw [ha1, ha2]
    have hpow : dist x (regPolyPt m j) ^ 4 = (dist x (regPolyPt m j) ^ 2) ^ 2 := by ring
    have hnorm4 : ‖x‖ ^ 4 = (x 0 ^ 2 + x 1 ^ 2) ^ 2 := by rw [← norm_sq_pt x]; ring
    rw [hpow, dist_sq_pt, hnorm4, norm_sq_pt, regPolyPt, mkPt_zero, mkPt_one]
    have hcs := Real.cos_sq_add_sin_sq ang
    have hd2 : (x 0 - Real.cos ang) ^ 2 + (x 1 - Real.sin ang) ^ 2 =
        (x 0 ^ 2 + x 1 ^ 2 + 1) - 2 * x 0 * Real.cos ang - 2 * x 1 * Real.sin ang := by
      linear_combination hcs
    rw [hd2, Real.cos_two_mul ang, Real.sin_two_mul ang]
    change (((x 0 ^ 2 + x 1 ^ 2 + 1) - 2 * x 0 * Real.cos ang - 2 * x 1 * Real.sin ang) ^ 2 =
      ((x 0 ^ 2 + x 1 ^ 2) ^ 2 + 4 * (x 0 ^ 2 + x 1 ^ 2) + 1)
      - 4 * (x 0 ^ 2 + x 1 ^ 2 + 1) * x 0 * Real.cos ang
      - 4 * (x 0 ^ 2 + x 1 ^ 2 + 1) * x 1 * Real.sin ang
      + 2 * (x 0 ^ 2 - x 1 ^ 2) * (2 * Real.cos ang ^ 2 - 1)
      + 4 * x 0 * x 1 * (2 * Real.sin ang * Real.cos ang))
    linear_combination (4 * x 1 ^ 2) * hcs
  simp_rw [hpt]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [sum_cos_regPoly hm (by omega) (by omega), sum_sin_regPoly hm (by omega) (by omega),
    sum_cos_regPoly hm (by omega) (by omega), sum_sin_regPoly hm (by omega) (by omega)]
  ring

/-- **General Regular-Polygon Moment-Inequality Obstruction (`m ≥ 4`):**
No point `x ∈ ℝ²` outside `R_m` can match the distance-degree signature of a vertex
plus a single diameter pair `dist x v_{j₀} = Δ > 0` for `m ≥ 4`.
(Sharp: `m = 3` admits the `rhombus4` equality case at `ρ = 2, Δ = 3`.) -/
theorem no_regPoly_violator_extension {m : ℕ} (hm : 4 ≤ m) (x : Pt) (j₀ : Fin m)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hdist : dist x (regPolyPt m j₀) = Δ)
    (hm2 : ∑ j : Fin m, dist x (regPolyPt m j) ^ 2 =
      (∑ j : Fin m, dist (regPolyPt m ⟨0, by omega⟩) (regPolyPt m j) ^ 2) + Δ ^ 2)
    (hm4 : ∑ j : Fin m, dist x (regPolyPt m j) ^ 4 =
      (∑ j : Fin m, dist (regPolyPt m ⟨0, by omega⟩) (regPolyPt m j) ^ 4) + Δ ^ 4) :
    False := by
  have hm3 : 3 ≤ m := by omega
  have hnorm0 : ‖regPolyPt m ⟨0, by omega⟩‖ ^ 2 = 1 := norm_sq_regPolyPt ⟨0, by omega⟩
  rw [regPoly_moment2 hm3 x, regPoly_moment2 hm3 (regPolyPt m ⟨0, by omega⟩), hnorm0] at hm2
  rw [regPoly_moment4 hm3 x, regPoly_moment4 hm3 (regPolyPt m ⟨0, by omega⟩)] at hm4
  have hnorm0_4 : ‖regPolyPt m ⟨0, by omega⟩‖ ^ 4 = 1 := by
    calc
      ‖regPolyPt m ⟨0, by omega⟩‖ ^ 4 = (‖regPolyPt m ⟨0, by omega⟩‖ ^ 2) ^ 2 := by ring
      _ = 1 ^ 2 := by rw [hnorm0]
      _ = 1 := one_pow 2
  rw [hnorm0, hnorm0_4] at hm4
  let ρ := ‖x‖
  let r2 := ρ ^ 2
  have hΔ2 : Δ ^ 2 = (m : ℝ) * (r2 - 1) := by
    change (m : ℝ) * (r2 + 1) = (m : ℝ) * (1 + 1) + Δ ^ 2 at hm2
    linarith
  have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
  have hΔ2_pos : 0 < Δ ^ 2 := sq_pos_of_pos hΔ
  have hr2_gt1 : 0 < r2 - 1 := by
    by_contra hle
    push Not at hle
    have : (m : ℝ) * (r2 - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hm_pos) hle
    linarith
  have hfac : (m : ℝ) * (r2 - 1) * (r2 + 5 - (m : ℝ) * (r2 - 1)) = 0 := by
    have hr4 : ‖x‖ ^ 4 = r2 ^ 2 := by simp only [ρ, r2]; ring
    rw [hr4] at hm4
    have hΔ4 : Δ ^ 4 = ((m : ℝ) * (r2 - 1)) ^ 2 := by
      calc
        Δ ^ 4 = (Δ ^ 2) ^ 2 := by ring
        _ = ((m : ℝ) * (r2 - 1)) ^ 2 := by rw [hΔ2]
    change (m : ℝ) * (r2 ^ 2 + 4 * r2 + 1) = (m : ℝ) * (1 + 4 * 1 + 1) + Δ ^ 4 at hm4
    rw [hΔ4] at hm4
    linear_combination hm4
  have hcoef_zero : r2 + 5 - (m : ℝ) * (r2 - 1) = 0 := by
    rcases mul_eq_zero.mp hfac with h0 | h0
    · nlinarith
    · exact h0
  have hmr_eq : ((m : ℝ) - 1) * r2 = (m : ℝ) + 5 := by linarith
  have hΔ_r2 : Δ ^ 2 = r2 + 5 := by linarith
  have htri : Δ ≤ ρ + 1 := by
    calc
      Δ = dist x (regPolyPt m j₀) := hdist.symm
      _ ≤ dist x 0 + dist (0 : Pt) (regPolyPt m j₀) := dist_triangle x 0 (regPolyPt m j₀)
      _ = ρ + 1 := by rw [dist_zero_right, dist_origin_regPolyPt]
  have hρ_nn : 0 ≤ ρ := norm_nonneg x
  have hΔ_sq_tri : Δ ^ 2 ≤ r2 + 2 * ρ + 1 := by
    have hsq : Δ ^ 2 ≤ (ρ + 1) ^ 2 := by nlinarith
    have : (ρ + 1) ^ 2 = r2 + 2 * ρ + 1 := by simp only [r2]; ring
    linarith
  have hρ_ge2 : 2 ≤ ρ := by linarith
  have hr2_ge4 : 4 ≤ r2 := by simp only [r2]; nlinarith
  have hm_ge4 : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  nlinarith

/-- Similarity transformation `ℝ² → ℝ²` with positive scale factor `R > 0`. -/
def IsEuclideanSimilarity (R : ℝ) (f : Pt → Pt) : Prop :=
  0 < R ∧ Function.Surjective f ∧ ∀ a b : Pt, dist (f a) (f b) = R * dist a b

/-- `Y` is a finite planar set similar to the regular `m`-gon `R_m`. -/
def IsSimilarRegPoly (m : ℕ) (Y : Finset Pt) : Prop :=
  ∃ (R : ℝ) (f : Pt → Pt), IsEuclideanSimilarity R f ∧
    Finset.univ.image (fun j : Fin m => f (regPolyPt m j)) = Y

/-- Explicit Planar Similarity Constructor (translation + positive scaling + rotation). -/
lemma euclideanSimilarity_rotation_scale_trans (c : Pt) {R : ℝ} (hR : 0 < R) (theta₀ : ℝ) :
    IsEuclideanSimilarity R (fun p =>
      c + mkPt (R * (Real.cos theta₀ * p 0 - Real.sin theta₀ * p 1))
               (R * (Real.sin theta₀ * p 0 + Real.cos theta₀ * p 1))) := by
  refine ⟨hR, ?_, ?_⟩
  · intro q
    let dx := (q 0 - c 0) / R
    let dy := (q 1 - c 1) / R
    refine ⟨mkPt (Real.cos theta₀ * dx + Real.sin theta₀ * dy)
                 (-Real.sin theta₀ * dx + Real.cos theta₀ * dy), ?_⟩
    have hcs := Real.cos_sq_add_sin_sq theta₀
    have hRne : R ≠ 0 := ne_of_gt hR
    ext i
    fin_cases i
    · change c 0 + R * (Real.cos theta₀ * (Real.cos theta₀ * dx + Real.sin theta₀ * dy) -
          Real.sin theta₀ * (-Real.sin theta₀ * dx + Real.cos theta₀ * dy)) = q 0
      have h0 : R * (Real.cos theta₀ * (Real.cos theta₀ * dx + Real.sin theta₀ * dy) -
          Real.sin theta₀ * (-Real.sin theta₀ * dx + Real.cos theta₀ * dy)) = R * dx := by
        linear_combination (R * dx) * hcs
      rw [h0]
      simp only [dx]; field_simp [hRne]; ring
    · change c 1 + R * (Real.sin theta₀ * (Real.cos theta₀ * dx + Real.sin theta₀ * dy) +
          Real.cos theta₀ * (-Real.sin theta₀ * dx + Real.cos theta₀ * dy)) = q 1
      have h1 : R * (Real.sin theta₀ * (Real.cos theta₀ * dx + Real.sin theta₀ * dy) +
          Real.cos theta₀ * (-Real.sin theta₀ * dx + Real.cos theta₀ * dy)) = R * dy := by
        linear_combination (R * dy) * hcs
      rw [h1]
      simp only [dy]; field_simp [hRne]; ring
  · intro a b
    rw [← sq_eq_sq₀ dist_nonneg (mul_nonneg (le_of_lt hR) dist_nonneg)]
    rw [dist_sq_pt, mul_pow, dist_sq_pt]
    simp only [PiLp.add_apply, mkPt_zero, mkPt_one]
    have hcs := Real.cos_sq_add_sin_sq theta₀
    linear_combination (R ^ 2 * ((a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2)) * hcs

private lemma cos_add_int_mul_two_pi (x : ℝ) (z : ℤ) :
    Real.cos (x + (z : ℝ) * (2 * Real.pi)) = Real.cos x := by
  have hexp : Complex.exp (((x + (z : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((x : ℂ) * Complex.I) := by
    have harg : (((x + (z : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) =
        (x : ℂ) * Complex.I + (z : ℤ) * (2 * ↑Real.pi * Complex.I) := by
      push_cast; ring
    rw [harg, Complex.exp_add, Complex.exp_intCast_mul, Complex.exp_two_pi_mul_I, one_zpow, mul_one]
  have hre := congrArg Complex.re hexp
  simpa only [Complex.exp_ofReal_mul_I_re] using hre

private lemma unitCircle_dist_sq (alpha beta : ℝ) :
    dist (mkPt (Real.cos alpha) (Real.sin alpha)) (mkPt (Real.cos beta) (Real.sin beta)) ^ 2 =
      2 - 2 * Real.cos (alpha - beta) := by
  rw [dist_sq_mkPt, Real.cos_sub]
  have ha := Real.cos_sq_add_sin_sq alpha
  have hb := Real.cos_sq_add_sin_sq beta
  linarith [ha, hb, show (Real.cos alpha - Real.cos beta) ^ 2 + (Real.sin alpha - Real.sin beta) ^ 2 =
    (Real.cos alpha ^ 2 + Real.sin alpha ^ 2) + (Real.cos beta ^ 2 + Real.sin beta ^ 2) -
      2 * (Real.cos alpha * Real.cos beta + Real.sin alpha * Real.sin beta) by ring]

private lemma regPolyPt_injective {m : ℕ} (hm : 3 ≤ m) :
    Function.Injective (regPolyPt m) := by
  intro j₁ j₂ hj
  have hcos : Real.cos (2 * Real.pi * (j₁.val : ℝ) / m) =
      Real.cos (2 * Real.pi * (j₂.val : ℝ) / m) := by
    have h0 := congrArg (fun p : Pt => p 0) hj
    simpa [regPolyPt, mkPt_zero] using h0
  have hsin : Real.sin (2 * Real.pi * (j₁.val : ℝ) / m) =
      Real.sin (2 * Real.pi * (j₂.val : ℝ) / m) := by
    have h1 := congrArg (fun p : Pt => p 1) hj
    simpa [regPolyPt, mkPt_one] using h1
  let a₁ : ℝ := 2 * Real.pi * (j₁.val : ℝ) / m
  let a₂ : ℝ := 2 * Real.pi * (j₂.val : ℝ) / m
  have hexp_eq : Complex.exp ((a₁ : ℂ) * Complex.I) = Complex.exp ((a₂ : ℂ) * Complex.I) := by
    apply Complex.ext
    · simpa [Complex.exp_ofReal_mul_I_re] using hcos
    · simpa [Complex.exp_ofReal_mul_I_im] using hsin
  have hexp1 : Complex.exp (((a₁ - a₂ : ℝ) : ℂ) * Complex.I) = 1 := by
    have harg : (((a₁ - a₂ : ℝ) : ℂ) * Complex.I) = (a₁ : ℂ) * Complex.I - (a₂ : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.exp_sub, hexp_eq, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp1
  have h1 : ((a₁ - a₂ : ℝ) : ℂ) * Complex.I = (↑n * (2 * ↑Real.pi)) * Complex.I := by
    calc
      ((a₁ - a₂ : ℝ) : ℂ) * Complex.I = ↑n * (2 * ↑Real.pi * Complex.I) := hn
      _ = (↑n * (2 * ↑Real.pi)) * Complex.I := by ring
  have h2 : (a₁ - a₂ : ℝ) = (n : ℝ) * (2 * Real.pi) := by
    have hre := congrArg Complex.re (mul_right_cancel₀ Complex.I_ne_zero h1)
    simpa using hre
  have hm_r : (m : ℝ) ≠ 0 := by positivity
  have h3 : 2 * Real.pi * ((j₁.val : ℝ) - (j₂.val : ℝ)) = 2 * Real.pi * ((n : ℝ) * m) := by
    calc
      2 * Real.pi * ((j₁.val : ℝ) - (j₂.val : ℝ)) = (a₁ - a₂) * m := by
        simp only [a₁, a₂]; field_simp [hm_r]
      _ = (n : ℝ) * (2 * Real.pi) * m := by rw [h2]
      _ = 2 * Real.pi * ((n : ℝ) * m) := by ring
  have hdiff_r : (j₁.val : ℝ) - (j₂.val : ℝ) = (n : ℝ) * m :=
    mul_left_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero) h3
  have hdiff_z : (j₁.val : ℤ) - (j₂.val : ℤ) = n * (m : ℤ) := by exact_mod_cast hdiff_r
  have hj1 : (j₁.val : ℤ) < m := by exact_mod_cast j₁.isLt
  have hj2 : (j₂.val : ℤ) < m := by exact_mod_cast j₂.isLt
  have hn0 : n = 0 := by
    rcases lt_trichotomy n 0 with hneg | rfl | hpos
    · have : n * (m : ℤ) ≤ -(m : ℤ) := by nlinarith
      omega
    · rfl
    · have : (m : ℤ) ≤ n * (m : ℤ) := by nlinarith
      omega
  rw [hn0, zero_mul] at hdiff_z
  exact Fin.ext (by omega)

private lemma regPolyPt_rot_dist {m : ℕ} (hm : 3 ≤ m) (k : ℕ) (j₁ j₂ : Fin m) :
    dist (regPolyPt m ⟨(j₁.val + k) % m, Nat.mod_lt _ (by omega)⟩)
         (regPolyPt m ⟨(j₂.val + k) % m, Nat.mod_lt _ (by omega)⟩) =
      dist (regPolyPt m j₁) (regPolyPt m j₂) := by
  rw [← sq_eq_sq₀ dist_nonneg dist_nonneg]
  simp only [regPolyPt]
  rw [unitCircle_dist_sq, unitCircle_dist_sq]
  have hm_pos : 0 < m := by omega
  have hm_r : (m : ℝ) ≠ 0 := by positivity
  have hmod₁ : (m * ((j₁.val + k) / m) + (j₁.val + k) % m : ℕ) = j₁.val + k :=
    Nat.div_add_mod (j₁.val + k) m
  have hmod₂ : (m * ((j₂.val + k) / m) + (j₂.val + k) % m : ℕ) = j₂.val + k :=
    Nat.div_add_mod (j₂.val + k) m
  let z : ℤ := (((j₂.val + k) / m : ℕ) : ℤ) - (((j₁.val + k) / m : ℕ) : ℤ)
  have hmod_r : (((j₁.val + k) % m : ℕ) : ℝ) - (((j₂.val + k) % m : ℕ) : ℝ) =
      ((j₁.val : ℝ) - (j₂.val : ℝ)) + (z : ℝ) * (m : ℝ) := by
    have h1 : (((j₁.val + k) % m : ℕ) : ℝ) = (j₁.val : ℝ) + k - (m : ℝ) * (((j₁.val + k) / m : ℕ) : ℝ) := by
      have : ((m * ((j₁.val + k) / m) + (j₁.val + k) % m : ℕ) : ℝ) = ((j₁.val + k : ℕ) : ℝ) := by
        exact_mod_cast hmod₁
      push_cast at this
      linarith
    have h2 : (((j₂.val + k) % m : ℕ) : ℝ) = (j₂.val : ℝ) + k - (m : ℝ) * (((j₂.val + k) / m : ℕ) : ℝ) := by
      have : ((m * ((j₂.val + k) / m) + (j₂.val + k) % m : ℕ) : ℝ) = ((j₂.val + k : ℕ) : ℝ) := by
        exact_mod_cast hmod₂
      push_cast at this
      linarith
    simp only [z]
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
    linarith
  have hangle : 2 * Real.pi * (((j₁.val + k) % m : ℕ) : ℝ) / m -
      2 * Real.pi * (((j₂.val + k) % m : ℕ) : ℝ) / m =
      (2 * Real.pi * (j₁.val : ℝ) / m - 2 * Real.pi * (j₂.val : ℝ) / m) + (z : ℝ) * (2 * Real.pi) := by
    calc
      2 * Real.pi * (((j₁.val + k) % m : ℕ) : ℝ) / m -
          2 * Real.pi * (((j₂.val + k) % m : ℕ) : ℝ) / m
        = 2 * Real.pi * ((((j₁.val + k) % m : ℕ) : ℝ) - (((j₂.val + k) % m : ℕ) : ℝ)) / m := by ring
      _ = 2 * Real.pi * (((j₁.val : ℝ) - (j₂.val : ℝ)) + (z : ℝ) * (m : ℝ)) / m := by rw [hmod_r]
      _ = (2 * Real.pi * (j₁.val : ℝ) / m - 2 * Real.pi * (j₂.val : ℝ) / m) + (z : ℝ) * (2 * Real.pi) := by
          field_simp [hm_r]
  rw [hangle, cos_add_int_mul_two_pi]

private lemma choose_two_r_add_one (r : ℕ) :
    Nat.choose (2 * r + 1) 2 = r * (2 * r + 1) := by
  rw [Nat.choose_two_right]
  have hsub : 2 * r + 1 - 1 = 2 * r := by omega
  rw [hsub]
  have hmul : (2 * r + 1) * (2 * r) = 2 * (r * (2 * r + 1)) := by ring
  rw [hmul, Nat.mul_div_right _ (by omega)]

/-- **General Even-Size Descent Theorem (`r ≥ 2`, `n = 2r + 2`):**
If `g(r) ≤ 2r + 1` (equivalently any `(2r + 2)`-point set determines at least `r + 1` distances)
and every `(2r + 1)`-point `≤ r`-distance set with all multiplicities `≤ 2r + 3` is similar to
the regular `(2r + 1)`-gon `R_{2r+1}`, then Erdős #132 holds for `n = 2r + 2`! -/
theorem erdos132_even_of_classification {r : ℕ} (hr : 2 ≤ r)
    (hg : ∀ X : Finset Pt, X.card = 2 * r + 2 → r + 1 ≤ (distSet X).card)
    (hclass : ∀ Y : Finset Pt, Y.card = 2 * r + 1 → (distSet Y).card ≤ r →
      (∀ d ∈ distSet Y, distMult Y d ≤ 2 * r + 3) → IsSimilarRegPoly (2 * r + 1) Y) :
    Erdos132For (2 * r + 2) := by
  intro X hcard
  have h_dist_lb := hg X hcard
  by_cases hmany : r + 2 ≤ (distSet X).card
  · refine erdos132_of_many_distances (one_le_card_rareDistances (by omega)) ?_
    rw [hcard, choose_two_r_add_two]
    have hsub : r + 1 ≤ (distSet X).card - 1 := by omega
    calc
      1 + r * (2 * r + 3) < 1 + (r + 1) * (2 * r + 3) := by
        have : 0 < 2 * r + 3 := by omega
        nlinarith
      _ ≤ 1 + ((distSet X).card - 1) * (2 * r + 2 + 1) := by nlinarith
  · have hdist_eq : (distSet X).card = r + 1 := by omega
    by_contra hviol
    obtain ⟨D, hD_mem, x, hxX, v₀, hv₀_er, _, _, hdxv₀, hS_info, hY_sub, hx_er_mem⟩ :=
      even_tight_violator_descent (by omega : 1 ≤ r) hcard hdist_eq hviol
    let Y := X.erase x
    have hY_card : Y.card = 2 * r + 1 := by rw [Finset.card_erase_of_mem hxX, hcard]; omega
    let S := distSet X \ {D}
    have hS_card : S.card = r := by rw [card_erase_sub_one_ge hD_mem, hdist_eq]; omega
    have hY_dist_le : (distSet Y).card ≤ r := by
      rw [← hS_card]
      exact Finset.card_le_card hY_sub
    have hY_mult_le : ∀ d ∈ distSet Y, distMult Y d ≤ 2 * r + 3 := by
      intro d hd
      have hdS : d ∈ S := hY_sub hd
      have hXd : distMult X d = 2 * r + 3 := (hS_info d hdS).2
      have hle_X : distMult Y d ≤ distMult X d := by
        unfold distMult
        exact Finset.card_le_card
          (Finset.filter_subset_filter _ (Finset.powersetCard_mono (Finset.erase_subset x X)))
      omega
    obtain ⟨R, f, ⟨hR_pos, hf_surj, hf_dist⟩, hY_img⟩ :=
      hclass Y hY_card hY_dist_le hY_mult_le
    let m := 2 * r + 1
    have hm3 : 3 ≤ m := by omega
    have hm4 : 4 ≤ m := by omega
    let g : Fin m → Pt := fun j => f (regPolyPt m j)
    have hg_inj : Function.Injective g := by
      intro j₁ j₂ hj
      have hd0 : dist (g j₁) (g j₂) = 0 := by rw [hj, dist_self]
      rw [hf_dist] at hd0
      have hd_reg0 : dist (regPolyPt m j₁) (regPolyPt m j₂) = 0 :=
        (mul_eq_zero.mp hd0).resolve_left (ne_of_gt hR_pos)
      exact regPolyPt_injective hm3 (dist_eq_zero.mp hd_reg0)
    let jZero : Fin m := ⟨0, by omega⟩
    let y₀ : Pt := g jZero
    have hy₀Y : y₀ ∈ Y := by
      rw [← hY_img]
      exact Finset.mem_image.mpr ⟨jZero, Finset.mem_univ _, rfl⟩
    have hdeg_uniform : ∀ k : Fin m, ∀ d : ℝ,
        (Y.filter (fun z => dist (g k) z = d)).card =
          (Y.filter (fun z => dist y₀ z = d)).card := by
      intro k d
      have hfib_k : (Y.filter (fun z => dist (g k) z = d)).card =
          (Finset.univ.filter fun j : Fin m => dist (g k) (g j) = d).card := by
        symm
        refine Finset.card_bij (fun j _ => g j) ?_ ?_ ?_
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          exact ⟨hY_img ▸ Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, hj⟩
        · intro j₁ _ j₂ _ heq
          exact hg_inj heq
        · intro z hz
          simp only [Finset.mem_filter] at hz
          have hz_img : z ∈ Finset.univ.image g := hY_img ▸ hz.1
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz_img
          exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz.2⟩, rfl⟩
      have hfib_0 : (Y.filter (fun z => dist y₀ z = d)).card =
          (Finset.univ.filter fun j : Fin m => dist y₀ (g j) = d).card := by
        symm
        refine Finset.card_bij (fun j _ => g j) ?_ ?_ ?_
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          exact ⟨hY_img ▸ Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, hj⟩
        · intro j₁ _ j₂ _ heq
          exact hg_inj heq
        · intro z hz
          simp only [Finset.mem_filter] at hz
          have hz_img : z ∈ Finset.univ.image g := hY_img ▸ hz.1
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz_img
          exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz.2⟩, rfl⟩
      rw [hfib_k, hfib_0]
      let shiftFn : Fin m → Fin m := fun j => ⟨(j.val + k.val) % m, Nat.mod_lt _ (by omega)⟩
      have hshift_0 : shiftFn jZero = k := Fin.ext (by
        simp only [shiftFn, jZero, zero_add, Nat.mod_eq_of_lt k.isLt])
      have hshift_dist : ∀ j : Fin m, dist (g k) (g (shiftFn j)) = dist y₀ (g j) := by
        intro j
        calc
          dist (g k) (g (shiftFn j)) = dist (g (shiftFn jZero)) (g (shiftFn j)) := by rw [hshift_0]
          _ = R * dist (regPolyPt m (shiftFn jZero)) (regPolyPt m (shiftFn j)) := hf_dist _ _
          _ = R * dist (regPolyPt m jZero) (regPolyPt m j) := by
              rw [regPolyPt_rot_dist hm3 k.val jZero j]
          _ = dist y₀ (g j) := (hf_dist _ _).symm
      symm
      refine Finset.card_bij (fun j _ => shiftFn j) ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        rw [hshift_dist, hj]
      · intro j₁ _ j₂ _ heq
        have hval := congrArg Fin.val heq
        dsimp only [shiftFn] at hval
        have hneg : ∃ t : ℕ, t < m ∧ (t + k.val) % m = 0 := by
          by_cases hk0 : k.val = 0
          · exact ⟨0, by omega, by simp [hk0]⟩
          · refine ⟨m - k.val, by omega, ?_⟩
            have hsum : m - k.val + k.val = m := by omega
            simp [hsum]
        have heq_mod : (j₁.val + k.val) % m = (j₂.val + k.val) % m := hval
        let sh := m - k.val % m
        have hinv₁ : (j₁.val + k.val + sh) % m = j₁.val := by
          have hk_lt : k.val % m = k.val := Nat.mod_eq_of_lt k.isLt
          have : k.val + sh = m := by omega
          rw [add_assoc, this, Nat.add_mod_right, Nat.mod_eq_of_lt j₁.isLt]
        have hinv₂ : (j₂.val + k.val + sh) % m = j₂.val := by
          have hk_lt : k.val % m = k.val := Nat.mod_eq_of_lt k.isLt
          have : k.val + sh = m := by omega
          rw [add_assoc, this, Nat.add_mod_right, Nat.mod_eq_of_lt j₂.isLt]
        have hj12 : j₁.val = j₂.val := by
          rw [← hinv₁, ← hinv₂, Nat.add_mod (j₁.val + k.val) sh m,
            Nat.add_mod (j₂.val + k.val) sh m, heq_mod]
        exact Fin.ext hj12
      · intro j' hj'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'
        let t : ℕ := (j'.val + (m - k.val)) % m
        let j : Fin m := ⟨t, Nat.mod_lt _ (by omega)⟩
        have hsh_j : shiftFn j = j' := by
          apply Fin.ext
          dsimp only [shiftFn, j, t]
          rw [Nat.add_mod ((j'.val + (m - k.val)) % m) k.val m, Nat.mod_mod]
          have : j'.val + (m - k.val) + k.val = j'.val + m := by omega
          rw [← Nat.add_mod, this, Nat.add_mod_right, Nat.mod_eq_of_lt j'.isLt]
        refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hsh_j⟩
        rw [← hshift_dist j, hsh_j, hj']
    have hY_deg2 : ∀ d ∈ distSet Y,
        (Y.filter (fun z => dist y₀ z = d)).card = 2 ∧ distMult Y d = 2 * r + 1 := by
      intro d hd
      have hd_pos : 0 < d := pos_of_mem_distSet hd
      have h2e := two_mul_edgeCount_eq_sum_deg Y d hd_pos
      change 2 * distMult Y d = ∑ z ∈ Y, (Y.filter (fun w => dist z w = d)).card at h2e
      have hterm : ∀ z ∈ Y,
          (Y.filter (fun w => dist z w = d)).card = (Y.filter (fun w => dist y₀ w = d)).card := by
        intro z hz
        have hz_img : z ∈ Finset.univ.image g := hY_img ▸ hz
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hz_img
        exact hdeg_uniform k d
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, hY_card] at h2e
      have hpos1 : 1 ≤ distMult Y d := distMult_pos_of_mem_distSet hd
      have hle : distMult Y d ≤ 2 * r + 3 := hY_mult_le d hd
      let deg := (Y.filter (fun w => dist y₀ w = d)).card
      have hdeg_pos : deg ≠ 0 := by
        intro h0
        change 2 * distMult Y d = (2 * r + 1) * deg at h2e
        rw [h0, mul_zero] at h2e
        omega
      have hdeg_ne1 : deg ≠ 1 := by
        intro h1
        change 2 * distMult Y d = (2 * r + 1) * deg at h2e
        rw [h1, mul_one] at h2e
        omega
      have hdeg_le2 : deg ≤ 2 := by
        by_contra hgt
        have h3 : 3 ≤ deg := by omega
        change 2 * distMult Y d = (2 * r + 1) * deg at h2e
        have : (2 * r + 1) * 3 ≤ (2 * r + 1) * deg := Nat.mul_le_mul_left _ h3
        omega
      have hdeg_eq2 : deg = 2 := by omega
      have hmult_eq : distMult Y d = 2 * r + 1 := by
        change 2 * distMult Y d = (2 * r + 1) * deg at h2e
        rw [hdeg_eq2] at h2e
        omega
      exact ⟨hdeg_eq2, hmult_eq⟩
    have hY_dist_eq_S : distSet Y = S := by
      have hsum := sum_distMult_eq_choose Y
      rw [hY_card, choose_two_r_add_one] at hsum
      have hsum' : ∑ d ∈ distSet Y, distMult Y d = (distSet Y).card * (2 * r + 1) := by
        calc
          ∑ d ∈ distSet Y, distMult Y d
            = ∑ _d ∈ distSet Y, (2 * r + 1) := Finset.sum_congr rfl (fun d hd => (hY_deg2 d hd).2)
          _ = (distSet Y).card * (2 * r + 1) := by simp
      rw [hsum'] at hsum
      have hcardY_dist : (distSet Y).card = r := Nat.eq_of_mul_eq_mul_right (by omega) hsum
      exact Finset.eq_of_subset_of_card_le hY_sub (by rw [hS_card, hcardY_dist])
    have hx_deg2 : ∀ d ∈ S, (Y.filter (fun y => dist x y = d)).card = 2 := by
      intro d hd
      have hXd : distMult X d = 2 * r + 3 := (hS_info d hd).2
      have hYd : distMult Y d = 2 * r + 1 := (hY_deg2 d (hY_dist_eq_S ▸ hd)).2
      have hmeq := distMult_erase_eq hxX d
      change distMult X d = distMult Y d + (Y.filter (fun y => dist x y = d)).card at hmeq
      omega
    have hx_sum_pow : ∀ p : ℕ, 1 ≤ p →
        ∑ y ∈ Y, dist x y ^ p = D ^ p + ∑ d ∈ S, 2 * d ^ p := by
      intro p _
      have hv₀_Y : v₀ ∈ Y := hv₀_er
      rw [← Finset.add_sum_erase Y (fun y => dist x y ^ p) hv₀_Y, hdxv₀]
      congr 1
      have hmaps : ∀ y ∈ Y.erase v₀, dist x y ∈ S := fun y hy => hx_er_mem y hy
      rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun y => dist x y ^ p)]
      refine Finset.sum_congr rfl ?_
      intro d hd
      have hd_neD : d ≠ D := by
        intro h; subst h; exact (Finset.mem_sdiff.mp hd).2 (Finset.mem_singleton_self _)
      have hfil_eq : (Y.erase v₀).filter (fun y => dist x y = d) = Y.filter (fun y => dist x y = d) := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨⟨_, hyY⟩, hdy⟩; exact ⟨hyY, hdy⟩
        · rintro ⟨hyY, hdy⟩
          refine ⟨⟨?_, hyY⟩, hdy⟩
          rintro rfl
          exact hd_neD (hdy.symm.trans hdxv₀)
      rw [hfil_eq]
      have hconst : ∑ y ∈ Y.filter (fun y => dist x y = d), dist x y ^ p =
          ∑ _y ∈ Y.filter (fun y => dist x y = d), d ^ p :=
        Finset.sum_congr rfl (fun y hy => by rw [(Finset.mem_filter.mp hy).2])
      rw [hconst, Finset.sum_const, nsmul_eq_mul, hx_deg2 d hd]
      ring
    have hy₀_sum_pow : ∀ p : ℕ, 1 ≤ p →
        ∑ y ∈ Y, dist y₀ y ^ p = ∑ d ∈ S, 2 * d ^ p := by
      intro p hp
      rw [← Finset.add_sum_erase Y (fun y => dist y₀ y ^ p) hy₀Y, dist_self, zero_pow (by omega), zero_add]
      have hmaps : ∀ y ∈ Y.erase y₀, dist y₀ y ∈ S := by
        intro y hy
        have hy' := Finset.mem_erase.mp hy
        rw [← hY_dist_eq_S]
        exact (mem_distSet_iff Y _).mpr ⟨y₀, hy₀Y, y, hy'.2, hy'.1.symm, rfl⟩
      rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun y => dist y₀ y ^ p)]
      refine Finset.sum_congr rfl ?_
      intro d hd
      have hd_pos : 0 < d := pos_of_mem_distSet (hY_dist_eq_S ▸ hd)
      have hfil_eq : (Y.erase y₀).filter (fun y => dist y₀ y = d) = Y.filter (fun y => dist y₀ y = d) := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨⟨_, hyY⟩, hdy⟩; exact ⟨hyY, hdy⟩
        · rintro ⟨hyY, hdy⟩
          refine ⟨⟨?_, hyY⟩, hdy⟩
          rintro rfl
          rw [dist_self] at hdy
          exact (ne_of_gt hd_pos) hdy.symm
      rw [hfil_eq]
      have hconst : ∑ y ∈ Y.filter (fun y => dist y₀ y = d), dist y₀ y ^ p =
          ∑ _y ∈ Y.filter (fun y => dist y₀ y = d), d ^ p :=
        Finset.sum_congr rfl (fun y hy => by rw [(Finset.mem_filter.mp hy).2])
      rw [hconst, Finset.sum_const, nsmul_eq_mul, (hY_deg2 d (hY_dist_eq_S ▸ hd)).1]
      ring
    have hm2_Y : ∑ y ∈ Y, dist x y ^ 2 = (∑ y ∈ Y, dist y₀ y ^ 2) + D ^ 2 := by
      rw [hx_sum_pow 2 (by omega), hy₀_sum_pow 2 (by omega)]; ring
    have hm4_Y : ∑ y ∈ Y, dist x y ^ 4 = (∑ y ∈ Y, dist y₀ y ^ 4) + D ^ 4 := by
      rw [hx_sum_pow 4 (by omega), hy₀_sum_pow 4 (by omega)]; ring
    obtain ⟨x₀, hx₀⟩ := hf_surj x
    have hv₀_img : v₀ ∈ Finset.univ.image g := hY_img ▸ hv₀_er
    obtain ⟨j₀, _, hj₀⟩ := Finset.mem_image.mp hv₀_img
    let Δ := D / R
    have hD_pos : 0 < D := pos_of_mem_distSet hD_mem
    have hΔ_pos : 0 < Δ := div_pos hD_pos hR_pos
    have hR_ne0 : R ≠ 0 := ne_of_gt hR_pos
    have hdist0 : dist x₀ (regPolyPt m j₀) = Δ := by
      dsimp only [Δ]
      have hfj₀ : f (regPolyPt m j₀) = v₀ := hj₀
      rw [eq_div_iff hR_ne0, mul_comm, ← hf_dist, hx₀, hfj₀, hdxv₀]
    have hpull : ∀ (p : ℕ) (z : Pt),
        ∑ y ∈ Y, dist (f z) y ^ p = R ^ p * ∑ j : Fin m, dist z (regPolyPt m j) ^ p := by
      intro p z
      rw [← hY_img, Finset.sum_image (fun a _ b _ h => hg_inj h)]
      have hterm : ∀ j : Fin m, dist (f z) (g j) ^ p = R ^ p * dist z (regPolyPt m j) ^ p := by
        intro j
        dsimp only [g]
        rw [hf_dist, mul_pow]
      simp_rw [hterm, ← Finset.mul_sum]
    have hm2_pull : ∑ j : Fin m, dist x₀ (regPolyPt m j) ^ 2 =
        (∑ j : Fin m, dist (regPolyPt m jZero) (regPolyPt m j) ^ 2) + Δ ^ 2 := by
      have h1 := hm2_Y
      rw [← hx₀, hpull 2 x₀] at h1
      change R ^ 2 * ∑ j : Fin m, dist x₀ (regPolyPt m j) ^ 2 =
        (∑ y ∈ Y, dist (f (regPolyPt m jZero)) y ^ 2) + D ^ 2 at h1
      rw [hpull 2 (regPolyPt m jZero)] at h1
      have hD2 : D ^ 2 = R ^ 2 * Δ ^ 2 := by simp only [Δ]; field_simp [hR_ne0]
      rw [hD2, ← mul_add] at h1
      exact mul_left_cancel₀ (pow_ne_zero 2 hR_ne0) h1
    have hm4_pull : ∑ j : Fin m, dist x₀ (regPolyPt m j) ^ 4 =
        (∑ j : Fin m, dist (regPolyPt m jZero) (regPolyPt m j) ^ 4) + Δ ^ 4 := by
      have h1 := hm4_Y
      rw [← hx₀, hpull 4 x₀] at h1
      change R ^ 4 * ∑ j : Fin m, dist x₀ (regPolyPt m j) ^ 4 =
        (∑ y ∈ Y, dist (f (regPolyPt m jZero)) y ^ 4) + D ^ 4 at h1
      rw [hpull 4 (regPolyPt m jZero)] at h1
      have hD4 : D ^ 4 = R ^ 4 * Δ ^ 4 := by simp only [Δ]; field_simp [hR_ne0]
      rw [hD4, ← mul_add] at h1
      exact mul_left_cancel₀ (pow_ne_zero 4 hR_ne0) h1
    exact no_regPoly_violator_extension hm4 x₀ j₀ hΔ_pos hdist0 hm2_pull hm4_pull

/-- **Specialization to `n = 8` (`r = 3`, `m = 7`)** given `g(3) = 7` and classification of `7`-point `3`-distance sets with multiplicities `≤ 9`. -/
theorem erdos132_eight_of_g3_and_class7
    (hg3 : ∀ X : Finset Pt, X.card = 8 → 4 ≤ (distSet X).card)
    (hclass7 : ∀ Y : Finset Pt, Y.card = 7 → (distSet Y).card ≤ 3 →
      (∀ d ∈ distSet Y, distMult Y d ≤ 9) → IsSimilarRegPoly 7 Y) :
    Erdos132For 8 :=
  erdos132_even_of_classification (by omega : 2 ≤ 3) hg3 hclass7

/-- **Specialization to `n = 10` (`r = 4`, `m = 9`)** given `g(4) = 9` and classification of `9`-point `4`-distance sets with multiplicities `≤ 11`. -/
theorem erdos132_ten_of_g4_and_class9
    (hg4 : ∀ X : Finset Pt, X.card = 10 → 5 ≤ (distSet X).card)
    (hclass9 : ∀ Y : Finset Pt, Y.card = 9 → (distSet Y).card ≤ 4 →
      (∀ d ∈ distSet Y, distMult Y d ≤ 11) → IsSimilarRegPoly 9 Y) :
    Erdos132For 10 :=
  erdos132_even_of_classification (by omega : 2 ≤ 4) hg4 hclass9

/-- **Resolution of the `n = 14` Barrier (`r = 6`, `m = 13`):**
For `n = 14`, Wei (2012) gives `g(6) = 13`, and any violator forces `13`-point `≤ 6`-distance sets `Y`
with every multiplicity `≤ 15` (immediately eliminating `R_{12}^+` spectrum `(24, 12^4, 6)` and
the centered hexagram spectrum `(24, 18, 15, 12, 6, 3)` since `24 > 15`). Together with the remaining
regular `13`-gon classification `IsSimilarRegPoly 13 Y`, the `m = 13` moment obstruction closes `n = 14`. -/
theorem erdos132_fourteen_of_wei_and_class13
    (hwei : ∀ X : Finset Pt, X.card = 14 → 7 ≤ (distSet X).card)
    (hclass13 : ∀ Y : Finset Pt, Y.card = 13 → (distSet Y).card ≤ 6 →
      (∀ d ∈ distSet Y, distMult Y d ≤ 15) → IsSimilarRegPoly 13 Y) :
    Erdos132For 14 :=
  erdos132_even_of_classification (by omega : 2 ≤ 6) hwei hclass13

end RegularPolygonObstruction

end Matematyka.Erdos132
