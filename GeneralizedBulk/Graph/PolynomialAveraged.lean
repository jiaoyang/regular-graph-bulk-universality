import GeneralizedBulk.Graph.MeasurableSpectralVariance
import GeneralizedBulk.Analysis.GoodEvents

/-! Averaged vanishing polynomial variance, including rare bad graph samples. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology Classical
namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

/-- Polynomial compressions are uniformly bounded even on exceptional graph
samples, which permits averaging without discarding those samples. -/
theorem polynomialProposalVariance_global_le (n : ℕ) (ω : Ω) (hd : 0 < d)
    (Q : Polynomial ℝ) (i j : Fin 4) :
    D.polynomialProposalVariance n ω Q i j ≤ 4 * polynomialUniformBound d Q ^ 2 := by
  letI : Nonempty (Fin (N n) × Fin d) := ⟨⟨⟨0,D.size_pos n⟩,⟨0,hd⟩⟩⟩
  letI := uniformOrientedProposals_isProbability (N n) d (D.size_pos n) hd
  have hp := finiteUniform_centered_secondMoment_le (D.polynomialProposalEntry n ω Q i j) 0
  simp only [sub_zero] at hp
  have hpoint (s : ProposalSample (N n) d) : ‖D.polynomialProposalEntry n ω Q i j s‖ ^ 2 ≤
      polynomialUniformBound d Q ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (polynomialUniformBound_nonneg d Q)).mpr
      (D.polynomialMatrix_entry_norm_le n ω Q _ _)
  have hi := integral_mono (μ := uniformOrientedProposals (N n) d)
    (integrable_finiteUniform_real (fun s => ‖D.polynomialProposalEntry n ω Q i j s‖ ^ 2))
    (integrable_const (μ := uniformOrientedProposals (N n) d) (polynomialUniformBound d Q ^ 2)) hpoint
  rw [integral_const] at hi
  change _ ≤ (uniformOrientedProposals (N n) d).real Set.univ • polynomialUniformBound d Q ^ 2 at hi
  rw [measureReal_univ_eq_one, one_smul] at hi
  exact hp.trans (mul_le_mul_of_nonneg_left hi (by norm_num))

theorem polynomialProposalVariance_integrable
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (hd : 0 < d) (Q : Polynomial ℝ) (i j : Fin 4) :
    Integrable (fun ω => D.polynomialProposalVariance n ω Q i j) P := by
  apply (integrable_const (4 * polynomialUniformBound d Q ^ 2)).mono'
    (D.measurable_polynomialProposalVariance n hd Q i j).aestronglyMeasurable
  filter_upwards [] with ω
  have hnonneg : 0 ≤ D.polynomialProposalVariance n ω Q i j := integral_nonneg (fun s => sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact D.polynomialProposalVariance_global_le n ω hd Q i j

/-- The full graph-averaged centered endpoint variance of every fixed
polynomial tends to zero. The exceptional HY graph event is included and
controlled by its proved finite probability bound. -/
theorem integral_polynomialProposalVariance_tendsto_zero
    {P : Measure Ω} [IsProbabilityMeasure P] (H : HYGeometryInput D P) (hd : 0 < d)
    (Q : Polynomial ℝ) (i j : Fin 4) :
    Tendsto (fun n => ∫ ω, D.polynomialProposalVariance n ω Q i j ∂P) atTop (𝓝 0) := by
  let M := polynomialUniformBound d Q
  let R := Q.natDegree
  let B := 4 * M ^ 2
  let rate (n : ℕ) := 16 * M ^ 2 *
    (2 * (N n : ℝ) ^ (-(1 / 2 : ℝ)) + 4 * (regularBallBound d R : ℝ) / N n)
  have hnonneg (n : ℕ) (ω : Ω) : 0 ≤ D.polynomialProposalVariance n ω Q i j :=
    integral_nonneg (fun s => sq_nonneg _)
  have hupper : ∀ᶠ n in atTop, (∫ ω, D.polynomialProposalVariance n ω Q i j ∂P) ≤
      rate n + 2 * B * P.real ((H.events R).good n)ᶜ := by
    filter_upwards [eventually_ge_atTop (H.events R).threshold] with n hn
    have h := Graph.integral_abs_error_good_bound P ((H.events R).good n)
      ((H.events R).measurable_good n) (fun ω => D.polynomialProposalVariance n ω Q i j)
      (D.measurable_polynomialProposalVariance n hd Q i j) 0 B
      (fun ω => by rw [abs_of_nonneg (hnonneg n ω)]; exact D.polynomialProposalVariance_global_le n ω hd Q i j)
      (by rw [abs_zero]; dsimp only [B]; positivity) (rate n) (by dsimp [rate]; positivity) (fun ω hω => by
        rw [sub_zero, abs_of_nonneg (hnonneg n ω)]
        exact D.polynomialProposalVariance_le_rate n ω H hd R hn hω Q le_rfl i j)
    have heq : (fun ω => |D.polynomialProposalVariance n ω Q i j - 0|) =
        (fun ω => D.polynomialProposalVariance n ω Q i j) :=
      funext (fun ω => by rw [sub_zero, abs_of_nonneg (hnonneg n ω)])
    rw [heq] at h
    exact h
  have hN : Tendsto (fun n => (N n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp D.size_tendsto
  have hhalf := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hN
  have hinv := tendsto_inv_atTop_zero.comp hN
  have hrate : Tendsto rate atTop (𝓝 0) := by
    have h := ((hhalf.const_mul 2).add (hinv.const_mul (4 * (regularBallBound d R : ℝ)))).const_mul (16 * M ^ 2)
    simpa only [rate, mul_zero, add_zero, div_eq_mul_inv] using h
  have hbad := ((H.events R).failure_tendsto_zero D.size_tendsto).const_mul (2 * B)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => integral_nonneg (hnonneg n))) hupper
  simpa only [zero_add, mul_zero] using hrate.add hbad

end GeneralizedBulk.External.RegularSpectralData
