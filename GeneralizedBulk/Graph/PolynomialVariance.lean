import GeneralizedBulk.Graph.GeometricProposal
import GeneralizedBulk.Graph.FiniteVariance
import GeneralizedBulk.Graph.OuterCutoff

/-!
# Vanishing centered polynomial compression from actual HY tree geometry

The graph walk identities, uniform spectral bounds and exceptional proposal
probability are combined. No polynomial concentration or centered-tail
statement is supplied as an external input.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace GeneralizedBulk.Graph

def polynomialUniformBound (d : ℕ) (Q : Polynomial ℝ) : ℝ :=
  ∑ k ∈ Q.support, |Q.coeff k| * (d : ℝ) ^ k

theorem polynomialUniformBound_nonneg (d : ℕ) (Q : Polynomial ℝ) :
    0 ≤ polynomialUniformBound d Q :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))

theorem polynomial_eval_abs_le_uniformBound (d : ℕ) (Q : Polynomial ℝ) (x : ℝ) (hx : |x| ≤ d) :
    |Q.eval x| ≤ polynomialUniformBound d Q := by
  rw [Polynomial.eval_eq_sum]
  change |∑ k ∈ Q.support, Q.coeff k * x ^ k| ≤ _
  calc
    _ ≤ ∑ k ∈ Q.support, |Q.coeff k * x ^ k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg x) hx k) (abs_nonneg _)

end GeneralizedBulk.Graph

namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

theorem polynomialMatrix_graph (Q : Polynomial ℝ) :
    D.polynomialMatrix n ω Q = graphPolynomialMatrix (D.simpleGraph n ω) Q := by
  simp only [polynomialMatrix, graphPolynomialMatrix, D.simpleGraph_adjacency_complex n ω]

theorem polynomialMatrix_entry_norm_le (Q : Polynomial ℝ) (v w : Fin (N n)) :
    ‖D.polynomialMatrix n ω Q v w‖ ≤ polynomialUniformBound d Q := by
  rw [D.polynomialMatrix_eq_spectralMultiplier n ω Q]
  apply D.spectralCompression_norm_le n ω Finset.univ _ _ (polynomialUniformBound_nonneg d Q) _ v w
  intro k hk
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact polynomial_eval_abs_le_uniformBound d Q _ (D.eigenvalue_abs_le_degree n ω k)

def polynomialProposalEntry (Q : Polynomial ℝ) (i j : Fin 4) (s : ProposalSample (N n) d) : ℂ :=
  D.polynomialMatrix n ω Q (D.proposalEndpoints n ω s i) (D.proposalEndpoints n ω s j)

def polynomialProposalVariance (Q : Polynomial ℝ) (i j : Fin 4) : ℝ :=
  ∫ s, ‖D.polynomialProposalEntry n ω Q i j s -
    ∫ t, D.polynomialProposalEntry n ω Q i j t ∂uniformOrientedProposals (N n) d‖ ^ 2
      ∂uniformOrientedProposals (N n) d

/-- Off the explicitly counted exceptional proposals, the actual finite
polynomial entry equals the deterministic canonical two-edge tree value. -/
theorem polynomialProposalEntry_eq_tree_on_good
    {P : Measure Ω} [IsProbabilityMeasure P] (H : HYGeometryInput D P)
    (R : ℕ) (hn : (H.events R).threshold ≤ n) (hω : ω ∈ (H.events R).good n)
    (Q : Polynomial ℝ) (hQ : Q.natDegree ≤ R)
    (s : ProposalSample (N n) d) (hs : s ∉ D.geometricProposalBad n ω R (H.badRoots R n ω))
    (i j : Fin 4) : D.polynomialProposalEntry n ω Q i j s = twoEdgePolynomialProfile d R Q i j := by
  have hfirst : s.1.1 ∉ H.badRoots R n ω := fun h => hs (Or.inl (Or.inl h))
  have hsecond : s.2.1 ∉ H.badRoots R n ω := fun h => hs (Or.inl (Or.inr h))
  obtain ⟨left⟩ := H.edgeIso R n hn ω hω s.1.1 hfirst s.1.2
  obtain ⟨right⟩ := H.edgeIso R n hn ω hω s.2.1 hsecond s.2.2
  have hsep (a b : Fin 2) : (Q.natDegree : ℕ∞) < (D.simpleGraph n ω).edist
      (D.proposalEndpoint n ω s.1 a) (D.proposalEndpoint n ω s.2 b) := by
    have hnot : ¬ (D.simpleGraph n ω).edist
        (D.proposalEndpoint n ω s.1 a) (D.proposalEndpoint n ω s.2 b) ≤ (R : ℕ∞) := by
      intro h
      exact hs (Or.inr (Set.mem_iUnion.mpr ⟨(a,b),h⟩))
    exact (show (Q.natDegree : ℕ∞) ≤ (R : ℕ∞) by exact_mod_cast hQ).trans_lt (lt_of_not_ge hnot)
  have hMat := polynomial_two_edge_tree (D.simpleGraph n ω)
    s.1.1 (D.neighbor n ω s.1.1 s.1.2) s.2.1 (D.neighbor n ω s.2.1 s.2.2)
    d R left right Q hQ hsep
  dsimp only [polynomialProposalEntry]
  rw [D.polynomialMatrix_graph n ω Q]
  exact congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M i j) hMat

/-- The actual conditional polynomial variance is controlled by the literal
exceptional-root fraction and an internally proved short-connection count. -/
theorem polynomialProposalVariance_le_geometry
    {P : Measure Ω} [IsProbabilityMeasure P] (H : HYGeometryInput D P) (hd : 0 < d)
    (R : ℕ) (hn : (H.events R).threshold ≤ n) (hω : ω ∈ (H.events R).good n)
    (Q : Polynomial ℝ) (hQ : Q.natDegree ≤ R) (i j : Fin 4) :
    D.polynomialProposalVariance n ω Q i j ≤
      16 * polynomialUniformBound d Q ^ 2 *
        (2 * ((H.badRoots R n ω).card : ℝ) / N n + 4 * (regularBallBound d R : ℝ) / N n) := by
  letI : Nonempty (Fin (N n) × Fin d) := ⟨⟨⟨0,D.size_pos n⟩,⟨0,hd⟩⟩⟩
  have hp := finiteUniform_variance_le_bounded_exceptional_set
    (D.polynomialProposalEntry n ω Q i j) (D.geometricProposalBad n ω R (H.badRoots R n ω))
    (twoEdgePolynomialProfile d R Q i j) (polynomialUniformBound d Q)
    (polynomialUniformBound_nonneg d Q)
    (fun s hs => D.polynomialProposalEntry_eq_tree_on_good n ω H R hn hω Q hQ s hs i j)
    (fun s => D.polynomialMatrix_entry_norm_le n ω Q _ _)
  exact hp.trans (mul_le_mul_of_nonneg_left
    (D.geometricProposalBad_probability_bound n ω hd R (H.badRoots R n ω)) (by positivity))

/-- Substituting HY's actual exceptional-root bound produces a uniform
vanishing deterministic variance rate. -/
theorem polynomialProposalVariance_le_rate
    {P : Measure Ω} [IsProbabilityMeasure P] (H : HYGeometryInput D P) (hd : 0 < d)
    (R : ℕ) (hn : (H.events R).threshold ≤ n) (hω : ω ∈ (H.events R).good n)
    (Q : Polynomial ℝ) (hQ : Q.natDegree ≤ R) (i j : Fin 4) :
    D.polynomialProposalVariance n ω Q i j ≤
      16 * polynomialUniformBound d Q ^ 2 *
        (2 * (N n : ℝ) ^ (-(1 / 2 : ℝ)) + 4 * (regularBallBound d R : ℝ) / N n) := by
  apply (D.polynomialProposalVariance_le_geometry n ω H hd R hn hω Q hQ i j).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add_right
  have hp := div_le_div_of_nonneg_right (H.bad_count R n hn ω hω) (show (0 : ℝ) ≤ N n by positivity)
  have hN : 0 < (N n : ℝ) := by exact_mod_cast D.size_pos n
  have heq : (N n : ℝ) ^ (1 / 2 : ℝ) / (N n : ℝ) = (N n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc
      _ = (N n : ℝ) ^ ((1 / 2 : ℝ) - 1) := by
        simpa only [Real.rpow_one] using (Real.rpow_sub hN (1 / 2 : ℝ) 1).symm
      _ = _ := by congr 1; ring
  have hh := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)
  rw [heq] at hh
  convert hh using 1 <;> ring

/-- Along every common-good graph sequence, every fixed polynomial's actual
centered endpoint second moment tends to zero. -/
theorem polynomialProposalVariance_tendsto_zero
    {P : Measure Ω} [IsProbabilityMeasure P] (H : HYGeometryInput D P) (hd : 0 < d)
    (Q : Polynomial ℝ) (omega : ℕ → Ω)
    (hgood : ∀ᶠ n in atTop, omega n ∈ (H.events Q.natDegree).good n) (i j : Fin 4) :
    Tendsto (fun n => D.polynomialProposalVariance n (omega n) Q i j) atTop (𝓝 0) := by
  have hN : Tendsto (fun n => (N n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp D.size_tendsto
  have hhalf := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hN
  have hinv := tendsto_inv_atTop_zero.comp hN
  have hrate := ((hhalf.const_mul 2).add (hinv.const_mul (4 * (regularBallBound d Q.natDegree : ℝ)))).const_mul
    (16 * polynomialUniformBound d Q ^ 2)
  have hbound : ∀ᶠ n in atTop, D.polynomialProposalVariance n (omega n) Q i j ≤
      16 * polynomialUniformBound d Q ^ 2 *
        (2 * (N n : ℝ) ^ (-(1 / 2 : ℝ)) + 4 * (regularBallBound d Q.natDegree : ℝ) / N n) := by
    filter_upwards [hgood, eventually_ge_atTop (H.events Q.natDegree).threshold] with n hn hthreshold
    exact D.polynomialProposalVariance_le_rate n (omega n) H hd Q.natDegree hthreshold hn Q le_rfl i j
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => integral_nonneg (fun s => sq_nonneg _))) hbound
  simpa only [mul_zero, add_zero, div_eq_mul_inv] using hrate

end GeneralizedBulk.External.RegularSpectralData
