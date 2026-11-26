import GeneralizedBulk.Graph.PolynomialAveraged

/-!
# Vanishing averaged centered outer spectral compression

The actual outer multiplier is compared with fixed real polynomials. Their
variance tends to zero by the proved finite tree/walk argument, and uniform
scalar approximation is transferred through the actual finite expectation.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

def outerProposalEntry (n : ℕ) (ω : Ω) (E gap : ℝ) (z : ℂ) (i j : Fin 4)
    (s : ProposalSample (N n) d) : ℂ :=
  D.spectralMultiplier n ω (outerComplexWeight (outerCutoff E gap) z)
    (D.proposalEndpoints n ω s i) (D.proposalEndpoints n ω s j)

def outerProposalVariance (n : ℕ) (ω : Ω) (E gap : ℝ) (z : ℂ) (i j : Fin 4) : ℝ :=
  ∫ s, ‖D.outerProposalEntry n ω E gap z i j s -
    ∫ t, D.outerProposalEntry n ω E gap z i j t ∂uniformOrientedProposals (N n) d‖ ^ 2
      ∂uniformOrientedProposals (N n) d

theorem measurable_outerProposalVariance (n : ℕ) (hd : 0 < d) (E gap : ℝ) (z : ℂ) (i j : Fin 4) :
    Measurable (fun ω => D.outerProposalVariance n ω E gap z i j) := by
  letI : Nonempty (Fin (N n) × Fin d) := ⟨⟨⟨0,D.size_pos n⟩,⟨0,hd⟩⟩⟩
  apply measurable_finiteUniform_variance
  intro s
  apply D.measurable_spectralProposalEntry n
  exact ((measurable_const.sub (continuous_outerCutoff E gap).measurable).complex_ofReal).div
    (Complex.measurable_ofReal.sub measurable_const)

/-- Fixed polynomial comparison with the exact finite centering retained. -/
theorem exists_outerPolynomial_variance_comparison (hd : 0 < d)
    (E gap delta : ℝ) (hgap : 0 < gap) (hdelta : 0 < delta) :
    ∃ Q : Polynomial ℝ, ∀ n : ℕ, ∀ ω : Ω, ∀ z : ℂ, ‖z - (E : ℂ)‖ ≤ gap / 2 →
      ∀ i j : Fin 4, D.outerProposalVariance n ω E gap z i j ≤
        2 * D.polynomialProposalVariance n ω Q i j +
          8 * (delta + 2 * ‖z - (E : ℂ)‖ / gap ^ 2) ^ 2 := by
  obtain ⟨Q,hQ⟩ := D.exists_outer_polynomial_compression E gap delta hgap hdelta
  refine ⟨Q, fun n ω z hz i j => ?_⟩
  letI : Nonempty (Fin (N n) × Fin d) := ⟨⟨⟨0,D.size_pos n⟩,⟨0,hd⟩⟩⟩
  apply finiteUniform_centered_variance_le_comparison
    (D.outerProposalEntry n ω E gap z i j) (D.polynomialProposalEntry n ω Q i j)
    _ (by positivity)
  intro s
  exact hQ n ω z hz _ _

/-- The comparison bounds the actual outer variance by an integrable
function of the graph sample, uniformly near the limiting spectral center. -/
theorem outerProposalVariance_integrable_near
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (hd : 0 < d)
    (E gap : ℝ) (hgap : 0 < gap) (z : ℂ) (hz : ‖z - (E : ℂ)‖ ≤ gap / 2) (i j : Fin 4) :
    Integrable (fun ω => D.outerProposalVariance n ω E gap z i j) P := by
  obtain ⟨Q,hQ⟩ := D.exists_outerPolynomial_variance_comparison hd E gap 1 hgap (by norm_num)
  have hg := ((D.polynomialProposalVariance_integrable P n hd Q i j).const_mul 2).add
    (integrable_const (8 * (1 + 2 * ‖z - (E : ℂ)‖ / gap ^ 2) ^ 2))
  apply hg.mono' (D.measurable_outerProposalVariance n hd E gap z i j).aestronglyMeasurable
  filter_upwards [] with ω
  have hnonneg : 0 ≤ D.outerProposalVariance n ω E gap z i j := integral_nonneg (fun s => sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact hQ n ω z hz i j

/-- The full averaged centered outer compression tends to zero whenever the
spectral point tends to the bulk center. This includes the actual microscopic
reparameterization and requires no acceptance-conditioned estimate. -/
theorem integral_outerProposalVariance_tendsto_zero
    {P : Measure Ω} [IsProbabilityMeasure P] (H : HYGeometryInput D P) (hd : 0 < d)
    (E gap : ℝ) (hgap : 0 < gap) (z : ℕ → ℂ) (hz : Tendsto z atTop (𝓝 (E : ℂ)))
    (i j : Fin 4) :
    Tendsto (fun n => ∫ ω, D.outerProposalVariance n ω E gap (z n) i j ∂P) atTop (𝓝 0) := by
  have hnorm : Tendsto (fun n => ‖z n - (E : ℂ)‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hz.sub_const (E : ℂ)).norm
  have herr : Tendsto (fun n => 2 * ‖z n - (E : ℂ)‖ / gap ^ 2) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_div] using (hnorm.const_mul 2).div_const (gap ^ 2)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun n => ha.trans_le (integral_nonneg (fun ω =>
      integral_nonneg (fun s => sq_nonneg _))))
  · intro epsilon hepsilon
    let delta := min (1 : ℝ) (epsilon / 64)
    have hdelta : 0 < delta := lt_min zero_lt_one (by positivity)
    have hd1 : delta ≤ 1 := min_le_left _ _
    have hde : delta ≤ epsilon / 64 := min_le_right _ _
    obtain ⟨Q,hQ⟩ := D.exists_outerPolynomial_variance_comparison hd E gap delta hgap hdelta
    have hp := D.integral_polynomialProposalVariance_tendsto_zero H hd Q i j
    filter_upwards [(tendsto_order.mp hnorm).2 (gap / 2) (half_pos hgap),
      (tendsto_order.mp herr).2 delta hdelta,
      (tendsto_order.mp hp).2 (epsilon / 8) (by positivity)] with n hclose herror hsmall
    have hpoint := hQ n
    have hiPoly := D.polynomialProposalVariance_integrable P n hd Q i j
    have hiConst := integrable_const (μ := P) (8 * (delta + 2 * ‖z n - (E : ℂ)‖ / gap ^ 2) ^ 2)
    have hbound := integral_mono (D.outerProposalVariance_integrable_near P n hd E gap hgap (z n) hclose.le i j)
      ((hiPoly.const_mul 2).add hiConst) (fun ω => hQ n ω (z n) hclose.le i j)
    simp only [Pi.add_apply] at hbound
    rw [integral_add (hiPoly.const_mul 2) hiConst, integral_const_mul, integral_const,
      measureReal_univ_eq_one, one_smul] at hbound
    have hsquare : (delta + 2 * ‖z n - (E : ℂ)‖ / gap ^ 2) ^ 2 ≤ (2 * delta) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
    have hdeltaSq : delta ^ 2 ≤ delta := by nlinarith
    nlinarith

end GeneralizedBulk.External.RegularSpectralData
