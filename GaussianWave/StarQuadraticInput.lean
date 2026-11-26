import GaussianWave.Covariance
import GaussianWave.EdgeQuadratics
import GaussianWave.MomentTail

/-!
# The reduced one-edge input for actual finite regular-graph eigenvectors

The star is the concrete finite law of `RegularEigenData`. Its probability
space samples a uniform root and a uniform neighbor permutation. Thus the
quadratic estimate below is about actual empirical edge marks, rather than
an unrelated abstract probability distribution.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GaussianWave.RegularEigenData
open EdgeQuadratics

variable {d N c : ℕ} (D : RegularEigenData d N c)

/-- Actual uniform root and neighbor-ordering probability distribution. -/
def starProbability : FiniteProbability (Fin N × Equiv.Perm (Fin d)) := by
  letI : Nonempty (Fin N) := ⟨⟨0, D.size_pos⟩⟩
  exact FiniteProbability.uniform

/-- The finite probability expectation agrees with the actual star-law
Bochner integral for every real observable. -/
theorem starProbability_expect_eq_integral {k : ℕ}
    (q : Fin k → Fin N → ℝ)
    (f : ((Fin k × Fin (d + 1)) → ℝ) → ℝ) :
    D.starProbability.expect (fun ω => f (D.starSample q ω)) =
      ∫ x, f x ∂D.starLaw q := by
  rw [D.integral_starLaw]
  simp only [starProbability, FiniteProbability.uniform, FiniteProbability.expect,
    ← Finset.mul_sum]

/-- The actual finite law itself agrees with the regular-graph star law. -/
theorem starProbability_law {k : ℕ} (q : Fin k → Fin N → ℝ) :
    D.starProbability.law (D.starSample q) = D.starLaw q := by
  letI : Nonempty (Fin N) := ⟨⟨0, D.size_pos⟩⟩
  have hpos : (0 : ℝ) < Fintype.card (Fin N × Equiv.Perm (Fin d)) :=
    Nat.cast_pos.mpr Fintype.card_pos
  simp only [FiniteProbability.law, starProbability, FiniteProbability.uniform, starLaw]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [ENNReal.ofReal_inv_of_pos hpos, ENNReal.ofReal_natCast]
  rfl

/-- Root and one ordered neighbor, selected from a sampled physical star. -/
def edgePosition (leaf : Fin d) (r : Fin 2) : Fin (d + 1) :=
  Fin.cases 0 (fun _ => leaf.succ) r

def edgeMark (leaf : Fin d) (i : Fin c) (r : Fin 2)
    (ω : Fin N × Equiv.Perm (Fin d)) : ℝ :=
  D.starSample D.eigenvector ω (i, edgePosition leaf r)

def edgeCovariance (i : Fin c) (leaf : Fin d) (r s : Fin 2) : ℝ :=
  starWaveCovariance d (D.eigenvalue i) (edgePosition leaf r) (edgePosition leaf s)

@[simp] theorem edgeMark_root (leaf : Fin d) (i : Fin c)
    (ω : Fin N × Equiv.Perm (Fin d)) :
    D.edgeMark leaf i 0 ω = D.starSample D.eigenvector ω (i, 0) := rfl

@[simp] theorem edgeCovariance_root (leaf : Fin d) (i : Fin c) :
    D.edgeCovariance i leaf 0 0 = 1 := rfl

theorem edgeCovariance_diagonal (leaf : Fin d) (i : Fin c) (r : Fin 2) :
    D.edgeCovariance i leaf r r = 1 := by
  refine Fin.cases ?_ (fun r => ?_) r
  · rfl
  · simp [edgeCovariance, edgePosition, starWaveCovariance]

/-- The exact empirical second moments hold for these same probability-space
edge marks, including cross-channel orthogonality. -/
theorem edgeMark_second (hd : 2 ≤ d) (leaf : Fin d)
    (i j : Fin c) (r s : Fin 2) :
    D.starProbability.expect (fun ω => D.edgeMark leaf i r ω * D.edgeMark leaf j s ω) =
      (if i = j then 1 else 0) * D.edgeCovariance i leaf r s := by
  have he := D.starProbability_expect_eq_integral D.eigenvector
    (fun x => x (i, edgePosition leaf r) * x (j, edgePosition leaf s))
  simp only [edgeMark]
  rw [he]
  exact D.integral_star_orthonormal_eigen_covariance hd id Function.injective_id
    i j (edgePosition leaf r) (edgePosition leaf s)

theorem edgeMark_same_position_second (hd : 2 ≤ d) (leaf : Fin d)
    (i j : Fin c) (r : Fin 2) :
    D.starProbability.expect (fun ω => D.edgeMark leaf i r ω * D.edgeMark leaf j r ω) =
      if i = j then 1 else 0 := by
  rw [D.edgeMark_second hd, D.edgeCovariance_diagonal, mul_one]

/-- Nonconstant physical edge coordinates have exact zero mean. Only the
eigenvalue of the specified channel needs to differ from the regular degree. -/
theorem edgeMark_mean_zero (leaf : Fin d) (i : Fin c)
    (hi : D.eigenvalue i ≠ (d : ℝ)) (r : Fin 2) :
    D.starProbability.expect (D.edgeMark leaf i r) = 0 := by
  have hz := D.integral_star_eigen_coordinate_zero (fun _ : Fin 1 => i)
    (fun _ => hi) 0 (edgePosition leaf r)
  rw [← D.starProbability_expect_eq_integral (fun _ : Fin 1 => D.eigenvector i)
    (fun x => x (0, edgePosition leaf r))] at hz
  simpa only [edgeMark, starSample] using hz

/-- The raw four-endpoint eigenvector mark from two independent edge samples. -/
def twoEdgeMark (leaf : Fin d) (i : Fin c) (p : Bool × Fin 2)
    (ω : (Fin N × Equiv.Perm (Fin d)) × (Fin N × Equiv.Perm (Fin d))) : ℝ :=
  if p.1 then D.edgeMark leaf i p.2 ω.2 else D.edgeMark leaf i p.2 ω.1

/-- The physical covariance is block diagonal in the two independent edges. -/
def twoEdgeCovariance (i : Fin c) (leaf : Fin d) (p q : Bool × Fin 2) : ℝ :=
  if p.1 = q.1 then D.edgeCovariance i leaf p.2 q.2 else 0

theorem twoEdgeMark_mean_zero (leaf : Fin d) (i : Fin c)
    (hi : D.eigenvalue i ≠ (d : ℝ)) (p : Bool × Fin 2) :
    (D.starProbability.prod D.starProbability).expect (D.twoEdgeMark leaf i p) = 0 := by
  rcases p with ⟨b, r⟩
  cases b
  · change (D.starProbability.prod D.starProbability).expect
      (fun ω => D.edgeMark leaf i r ω.1) = 0
    rw [FiniteProbability.expect_prod_left, D.edgeMark_mean_zero leaf i hi r]
  · change (D.starProbability.prod D.starProbability).expect
      (fun ω => D.edgeMark leaf i r ω.2) = 0
    rw [FiniteProbability.expect_prod_right, D.edgeMark_mean_zero leaf i hi r]

/-- Exact second moments of actual two-edge marks: independence of the edge
samples removes the cross-edge blocks and orthogonality removes cross channels. -/
theorem twoEdgeMark_second (hd : 2 ≤ d) (leaf : Fin d)
    (hnonconstant : ∀ i, D.eigenvalue i ≠ (d : ℝ))
    (i j : Fin c) (p q : Bool × Fin 2) :
    (D.starProbability.prod D.starProbability).expect
      (fun ω => D.twoEdgeMark leaf i p ω * D.twoEdgeMark leaf j q ω) =
      (if i = j then 1 else 0) * D.twoEdgeCovariance i leaf p q := by
  rcases p with ⟨b, r⟩
  rcases q with ⟨c, s⟩
  cases b <;> cases c
  · simp only [twoEdgeMark, Bool.false_eq_true, ↓reduceIte, twoEdgeCovariance]
    rw [D.starProbability.expect_prod_left D.starProbability
      (fun ω => D.edgeMark leaf i r ω * D.edgeMark leaf j s ω)]
    exact D.edgeMark_second hd leaf i j r s
  · simp only [twoEdgeMark, Bool.false_eq_true, ↓reduceIte, twoEdgeCovariance,
      Bool.false_eq_true, mul_zero]
    rw [D.starProbability.expect_prod D.starProbability
      (D.edgeMark leaf i r) (D.edgeMark leaf j s),
      D.edgeMark_mean_zero leaf i (hnonconstant i) r, zero_mul]
  · simp only [twoEdgeMark, Bool.false_eq_true, ↓reduceIte, twoEdgeCovariance,
      Bool.true_eq_false, mul_zero]
    have heq : (fun ω : (Fin N × Equiv.Perm (Fin d)) × (Fin N × Equiv.Perm (Fin d)) =>
        D.edgeMark leaf i r ω.2 * D.edgeMark leaf j s ω.1) =
        (fun ω => D.edgeMark leaf j s ω.1 * D.edgeMark leaf i r ω.2) := by
      funext ω
      ring
    rw [heq, D.starProbability.expect_prod D.starProbability
      (D.edgeMark leaf j s) (D.edgeMark leaf i r),
      D.edgeMark_mean_zero leaf j (hnonconstant j) s, zero_mul]
  · simp only [twoEdgeMark, ↓reduceIte, twoEdgeCovariance]
    rw [D.starProbability.expect_prod_right D.starProbability
      (fun ω => D.edgeMark leaf i r ω * D.edgeMark leaf j s ω)]
    exact D.edgeMark_second hd leaf i j r s

/-- The quadratic used in the variance estimate is literally the raw outer
product minus the exact physical block-diagonal covariance. -/
theorem twoEdgeQuadratic_eq_outer_sub_covariance
    (leaf : Fin d) (i : Fin c) (p q : Bool × Fin 2)
    (ω : (Fin N × Equiv.Perm (Fin d)) × (Fin N × Equiv.Perm (Fin d))) :
    twoEdgeQuadratic (D.edgeMark leaf) (fun i => D.edgeCovariance i leaf) i p q ω =
      D.twoEdgeMark leaf i p ω * D.twoEdgeMark leaf i q ω - D.twoEdgeCovariance i leaf p q := by
  rcases p with ⟨b, r⟩
  rcases q with ⟨c, s⟩
  cases b <;> cases c
  · rfl
  · simp [twoEdgeQuadratic, twoEdgeMark, twoEdgeCovariance]
  · simp [twoEdgeQuadratic, twoEdgeMark, twoEdgeCovariance, mul_comm]
  · rfl

/-- Actual nonconstant bulk quadratic marks are exactly centered, before any
Gaussian approximation or asymptotic limit. -/
theorem twoEdgeQuadratic_actual_centered (hd : 2 ≤ d) (leaf : Fin d)
    (hnonconstant : ∀ i, D.eigenvalue i ≠ (d : ℝ))
    (i : Fin c) (p q : Bool × Fin 2) :
    (D.starProbability.prod D.starProbability).expect
      (twoEdgeQuadratic (D.edgeMark leaf) (fun i => D.edgeCovariance i leaf) i p q) = 0 := by
  apply EdgeQuadratics.twoEdgeQuadratic_centered D.starProbability
    (D.edgeMark leaf) (fun i => D.edgeCovariance i leaf)
  · exact fun i r => D.edgeMark_mean_zero leaf i (hnonconstant i) r
  · intro i r s
    simpa using D.edgeMark_second hd leaf i i r s

theorem twoEdge_outer_sub_covariance_centered (hd : 2 ≤ d) (leaf : Fin d)
    (hnonconstant : ∀ i, D.eigenvalue i ≠ (d : ℝ))
    (i : Fin c) (p q : Bool × Fin 2) :
    (D.starProbability.prod D.starProbability).expect (fun ω =>
      D.twoEdgeMark leaf i p ω * D.twoEdgeMark leaf i q ω - D.twoEdgeCovariance i leaf p q) = 0 := by
  calc
    _ = (D.starProbability.prod D.starProbability).expect
        (twoEdgeQuadratic (D.edgeMark leaf) (fun i => D.edgeCovariance i leaf) i p q) := by
      congr 1
      funext ω
      exact (D.twoEdgeQuadratic_eq_outer_sub_covariance leaf i p q ω).symm
    _ = 0 := D.twoEdgeQuadratic_actual_centered hd leaf hnonconstant i p q

/-- The quantitative one-edge input from the accompanying note. Its estimate
is an explicit hypothesis; no entropy or Gaussian-wave rate is asserted here. -/
def OneEdgeQuadraticBound (leaf : Fin d) (C err : ℝ) : Prop :=
  ∀ i j : Fin c, ∀ r s t u : Fin 2,
    |D.starProbability.expect (fun ω =>
      (D.edgeMark leaf i r ω * D.edgeMark leaf i s ω - D.edgeCovariance i leaf r s) *
      (D.edgeMark leaf j t ω * D.edgeMark leaf j u ω - D.edgeCovariance j leaf t u))| ≤
      (if i = j then C else 0) + err

/-- Reduced quadratic covariance control prevents loss of scalar variance:
the actual root empirical fourth moment is uniformly bounded. -/
theorem scalar_fourth_le_of_oneEdgeQuadraticBound
    (leaf : Fin d) (C err : ℝ) (hQ : D.OneEdgeQuadraticBound leaf C err)
    (i : Fin c) :
    (N : ℝ) * ∑ v, D.eigenvector i v ^ 4 ≤ 1 + C + err := by
  let X := D.edgeMark leaf i 0
  have hsecond : D.starProbability.expect (fun ω => X ω ^ 2) = 1 := by
    have he := D.starProbability_expect_eq_integral D.eigenvector
      (fun x => x (i, 0) * x (i, 0))
    have hs := D.integral_star_eigen_root_pair id i i
    simpa only [X, edgeMark_root, pow_two, he, id_eq, ↓reduceIte] using hs
  have hquad : |D.starProbability.expect (fun ω => (X ω ^ 2 - 1) ^ 2)| ≤ C + err := by
    simpa only [OneEdgeQuadraticBound, edgeCovariance_root, ↓reduceIte, pow_two, X]
      using hQ i i 0 0 0 0
  have hf := D.starProbability.fourth_moment_le_of_centered_square X C err hsecond hquad
  have he := D.starProbability_expect_eq_integral D.eigenvector (fun x => x (i, 0) ^ 4)
  have he' : D.starProbability.expect (fun ω => X ω ^ 4) =
      (N : ℝ) * ∑ v, D.eigenvector i v ^ 4 := by
    simpa only [X, edgeMark_root, D.integral_star_root_fourth] using he
  rwa [he'] at hf

/-- Every selected physical star coordinate inherits the same scalar bound,
without any restriction on the tuple size. -/
theorem integral_star_coordinate_fourth_le_of_oneEdgeQuadraticBound
    (leaf : Fin d) (C err : ℝ) (hQ : D.OneEdgeQuadraticBound leaf C err)
    {k : ℕ} (a : Fin k → Fin c) (i : Fin k) (j : Fin (d + 1)) :
    (∫ x, x (i, j) ^ 4 ∂D.starLaw (fun b => D.eigenvector (a b))) ≤ 1 + C + err := by
  rw [D.integral_star_coordinate_fourth]
  exact D.scalar_fourth_le_of_oneEdgeQuadraticBound leaf C err hQ (a i)

/-- The physical Euclidean fourth moment required by normalization is now an
actual consequence of the reduced input, with the explicit dimension factor. -/
theorem integral_star_squareMass_sq_le_of_oneEdgeQuadraticBound
    (leaf : Fin d) (C err : ℝ) (hQ : D.OneEdgeQuadraticBound leaf C err)
    {k : ℕ} (a : Fin k → Fin c) :
    Integrable (fun x => squareMass x ^ 2) (D.starLaw (fun b => D.eigenvector (a b))) ∧
    (∫ x, squareMass x ^ 2 ∂D.starLaw (fun b => D.eigenvector (a b))) ≤
      (1 + C + err) * (Fintype.card (Fin k × Fin (d + 1)) : ℝ) ^ 2 := by
  apply integral_squareMass_sq_le
  · intro p
    exact D.integrable_starLaw _ _
  · intro p
    exact D.integral_star_coordinate_fourth_le_of_oneEdgeQuadraticBound
      leaf C err hQ a p.1 p.2

/-- Full complex weighted four-endpoint covariance control, specialized to
the actual empirical eigenvector marks on two independent sampled edges. -/
theorem twoEdge_weighted_bound_of_oneEdgeQuadraticBound
    (hd : 2 ≤ d) (leaf : Fin d) (C err : ℝ) (hC : 0 ≤ C) (herr : 0 ≤ err)
    (hQ : D.OneEdgeQuadraticBound leaf C err) (h : Fin c → ℂ) :
    (D.starProbability.prod D.starProbability).expect
      (fun ω => ∑ pq : (Bool × Fin 2) × (Bool × Fin 2),
        ‖∑ i, h i * (twoEdgeQuadratic (D.edgeMark leaf)
          (fun i => D.edgeCovariance i leaf) i pq.1 pq.2 ω : ℂ)‖ ^ 2) ≤
      16 * ((C + 1) * (∑ i, ‖h i‖ ^ 2) + 2 * err * (∑ i, ‖h i‖) ^ 2) := by
  have hb := twoEdge_weighted_frobenius_bound D.starProbability (D.edgeMark leaf)
    (fun i => D.edgeCovariance i leaf) C err hC herr
    (D.edgeMark_same_position_second hd leaf)
    (fun i j r s => hQ i j r s r s) h
  simpa using hb

/-- The complete physical interface needed for centered bulk spectral sums:
exact centering and a quantitative weighted Frobenius bound for the actual
outer products at two independently sampled oriented edges. -/
theorem physical_centered_bulk_input
    (hd : 2 ≤ d) (leaf : Fin d) (C err : ℝ) (hC : 0 ≤ C) (herr : 0 ≤ err)
    (hnonconstant : ∀ i, D.eigenvalue i ≠ (d : ℝ))
    (hQ : D.OneEdgeQuadraticBound leaf C err) (h : Fin c → ℂ) :
    (∀ i p q, (D.starProbability.prod D.starProbability).expect (fun ω =>
      D.twoEdgeMark leaf i p ω * D.twoEdgeMark leaf i q ω - D.twoEdgeCovariance i leaf p q) = 0) ∧
    (D.starProbability.prod D.starProbability).expect
      (fun ω => ∑ pq : (Bool × Fin 2) × (Bool × Fin 2),
        ‖∑ i, h i * ((D.twoEdgeMark leaf i pq.1 ω * D.twoEdgeMark leaf i pq.2 ω -
          D.twoEdgeCovariance i leaf pq.1 pq.2 : ℝ) : ℂ)‖ ^ 2) ≤
      16 * ((C + 1) * (∑ i, ‖h i‖ ^ 2) + 2 * err * (∑ i, ‖h i‖) ^ 2) := by
  refine ⟨D.twoEdge_outer_sub_covariance_centered hd leaf hnonconstant, ?_⟩
  simpa only [D.twoEdgeQuadratic_eq_outer_sub_covariance] using
    D.twoEdge_weighted_bound_of_oneEdgeQuadraticBound hd leaf C err hC herr hQ h

end GaussianWave.RegularEigenData
