import GaussianWave.BS.HeatQuantization
import GaussianWave.BS.GridClippingLimit
import GaussianWave.BS.HeatQuantizerKernel

/-! The two genuine finite-alphabet limits used by the BS differential-entropy
lower bound: remove clipping at fixed mesh, then send the mesh to zero. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology Classical
namespace GaussianWave.BS
open Reused.Entropy

private theorem coordinate_memLp_two_of_squareRadius
    {I : Type*} [Fintype I] (μ : Measure (I → ℝ))
    (hμ : Integrable (squareRadius (I := I)) μ) (i : I) : MemLp (fun x => x i) 2 μ := by
  apply (memLp_two_iff_integrable_sq (measurable_pi_apply i).aestronglyMeasurable).mpr
  apply hμ.mono' ((measurable_pi_apply i).pow_const 2).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_coordinate_le_squareMass x i

def clippedGridVector {m : ℕ} (a : ℝ) (K : ℕ) : (Fin m → ℝ) → (Fin m → Fin (2*(K+1))) :=
  codedClipIntegerVector (K+1) (by omega) ∘ gridLabel a

theorem measurable_clippedGridVector {m : ℕ} (a : ℝ) (K : ℕ) :
    Measurable (clippedGridVector (m := m) a K) :=
  (measurable_of_countable _).comp (measurable_gridLabel a)

/-- The cutoff limit for the actual smoothed finite-window law. -/
theorem tendsto_heat_finite_grid_entropy_cutoff {m : ℕ}
    (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := Fin m)) μ) {t : ℝ} (ht : 0 < t)
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun K => Finite.entropy (lawMass (heatedLaw μ t) (clippedGridVector a K))) atTop
      (𝓝 (countableEntropy (gridMass a (heatDensity μ t)))) := by
  have h := tendsto_grid_clipping_entropy (heatedLaw μ t) id measurable_id
    (fun i => coordinate_memLp_two_of_squareRadius _ (integrable_heatedLaw_squareRadius μ hμ t) i) a ha
  simpa only [Function.comp_id, clippedGridVector, lawMass_heatedLaw_gridLabel μ ht a ha] using h

private theorem densityEntropy_heatDensity_dirac {I : Type*} [Fintype I]
    {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    densityEntropy volume (heatDensity (Measure.dirac x) t) = gaussianEntropyValue I (heatVariance t) := by
  have he (z : I → ℝ) : heatDensity (Measure.dirac x) t z = heatKernel t (z - x) := by
    simp only [heatDensity, integral_dirac]
  simp_rw [densityEntropy, he]
  rw [integral_sub_right_eq (fun z => heatKernel t z * Real.log (heatKernel t z)) x]
  exact densityEntropy_heatKernel ht

def heatGridConditionalEntropy {m : ℕ} (a t : ℝ) (x : Fin m → ℝ) : ℝ :=
  countableEntropy (gridMass a (heatDensity (Measure.dirac x) t))

def heatFiniteConditionalEntropy {m : ℕ} (a t : ℝ) (K : ℕ) (x : Fin m → ℝ) : ℝ :=
  Finite.entropy (heatQuantizerMass (clippedGridVector a K) t x)

/-- Uniform in the arbitrary signal mean, the conditional grid entropy is
Gaussian noise entropy plus the mesh normalization, up to a vanishing error. -/
theorem heatGridConditionalEntropy_error {m : ℕ} {t : ℝ} (ht : 0 < t)
    (a : ℝ) (ha : 0 < a) (x : Fin m → ℝ) :
    0 ≤ heatGridConditionalEntropy a t x + (m : ℝ)*Real.log a -
      gaussianEntropyValue (Fin m) (heatVariance t) ∧
    heatGridConditionalEntropy a t x + (m : ℝ)*Real.log a -
      gaussianEntropyValue (Fin m) (heatVariance t) ≤ ((2 : ℝ)^m/2)*(1/(2*t))*m*a^2 := by
  have h := heatDensity_grid_entropy_error (Measure.dirac x) integrable_dirac ht a ha
  rw [densityEntropy_heatDensity_dirac ht x] at h
  exact h

private theorem heatFiniteConditionalEntropy_eq_law {m : ℕ} {t : ℝ} (ht : 0 < t)
    (a : ℝ) (K : ℕ) (x : Fin m → ℝ) :
    heatFiniteConditionalEntropy a t K x =
      Finite.entropy (lawMass (heatedLaw (Measure.dirac x) t) (clippedGridVector a K)) := by
  unfold heatFiniteConditionalEntropy
  rw [heatQuantizerMass_eq_dirac_heat_law _ (measurable_clippedGridVector a K) ht]

theorem tendsto_heatFiniteConditionalEntropy_cutoff {m : ℕ} {t : ℝ} (ht : 0 < t)
    (a : ℝ) (ha : 0 < a) (x : Fin m → ℝ) :
    Tendsto (fun K => heatFiniteConditionalEntropy a t K x) atTop (𝓝 (heatGridConditionalEntropy a t x)) := by
  simp_rw [heatFiniteConditionalEntropy_eq_law ht]
  exact tendsto_heat_finite_grid_entropy_cutoff (Measure.dirac x) integrable_dirac ht a ha

theorem measurable_heatGridConditionalEntropy {m : ℕ} {t : ℝ} (ht : 0 < t)
    (a : ℝ) (ha : 0 < a) : Measurable (heatGridConditionalEntropy (m := m) a t) := by
  apply measurable_of_tendsto_metrizable (fun K => ?_)
    (tendsto_pi_nhds.2 (tendsto_heatFiniteConditionalEntropy_cutoff ht a ha))
  apply Continuous.measurable
  unfold heatFiniteConditionalEntropy Finite.entropy
  apply continuous_finset_sum
  intro b _
  exact Real.continuous_negMulLog.comp
    (continuous_heatQuantizerMass _ (measurable_clippedGridVector a K) ht b)

private def conditionalEntropyEnvelope (m : ℕ) (a t : ℝ) : ℝ :=
  |gaussianEntropyValue (Fin m) (heatVariance t) - (m : ℝ)*Real.log a| +
    ((2 : ℝ)^m/2)*(1/(2*t))*m*a^2

private theorem norm_heatGridConditionalEntropy_le {m : ℕ} {t : ℝ} (ht : 0 < t)
    (a : ℝ) (ha : 0 < a) (x : Fin m → ℝ) :
    ‖heatGridConditionalEntropy a t x‖ ≤ conditionalEntropyEnvelope m a t := by
  obtain ⟨hlo, hhi⟩ := heatGridConditionalEntropy_error ht a ha x
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · dsimp [conditionalEntropyEnvelope]
    linarith [neg_abs_le (gaussianEntropyValue (Fin m) (heatVariance t) - (m : ℝ)*Real.log a),
      show (0 : ℝ) ≤ ((2 : ℝ)^m/2)*(1/(2*t))*m*a^2 by positivity]
  · dsimp [conditionalEntropyEnvelope]
    linarith [le_abs_self (gaussianEntropyValue (Fin m) (heatVariance t) - (m : ℝ)*Real.log a)]

theorem integrable_heatGridConditionalEntropy {m : ℕ}
    (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (a : ℝ) (ha : 0 < a) : Integrable (heatGridConditionalEntropy (m := m) a t) μ :=
  (integrable_const (conditionalEntropyEnvelope m a t)).mono'
    (measurable_heatGridConditionalEntropy ht a ha).aestronglyMeasurable
    (ae_of_all _ (norm_heatGridConditionalEntropy_le ht a ha))

/-- The averaged conditional root entropy needs no input moment restriction:
its approximation error is uniform in the signal value. -/
theorem integral_heatGridConditionalEntropy_error {m : ℕ}
    (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (a : ℝ) (ha : 0 < a) :
    0 ≤ (∫ x, heatGridConditionalEntropy a t x ∂μ) + (m : ℝ)*Real.log a -
      gaussianEntropyValue (Fin m) (heatVariance t) ∧
    (∫ x, heatGridConditionalEntropy a t x ∂μ) + (m : ℝ)*Real.log a -
      gaussianEntropyValue (Fin m) (heatVariance t) ≤ ((2 : ℝ)^m/2)*(1/(2*t))*m*a^2 := by
  have hi := integrable_heatGridConditionalEntropy μ ht a ha
  let F := fun x : Fin m → ℝ => heatGridConditionalEntropy a t x + (m : ℝ)*Real.log a -
    gaussianEntropyValue (Fin m) (heatVariance t)
  have hF : Integrable F μ := (hi.add (integrable_const _)).sub (integrable_const _)
  have hlo : 0 ≤ ∫ x, F x ∂μ := integral_nonneg (fun x => (heatGridConditionalEntropy_error ht a ha x).1)
  have hhi := integral_mono hF (integrable_const (((2 : ℝ)^m/2)*(1/(2*t))*m*a^2))
    (fun x => (heatGridConditionalEntropy_error ht a ha x).2)
  have he : (∫ x, F x ∂μ) = (∫ x, heatGridConditionalEntropy a t x ∂μ) +
      (m : ℝ)*Real.log a - gaussianEntropyValue (Fin m) (heatVariance t) := by
    dsimp [F]
    rw [integral_sub (f := fun x => heatGridConditionalEntropy a t x + (m : ℝ)*Real.log a)
        (hi.add (integrable_const _)) (integrable_const _),
      integral_add hi (integrable_const _)]
    simp
  rw [he] at hlo hhi
  simpa only [integral_const, measureReal_univ_eq_one, one_smul] using And.intro hlo hhi

theorem tendsto_integral_heatGridConditionalEntropy_mesh {m : ℕ}
    (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (ha0 : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => (∫ x, heatGridConditionalEntropy (a n) t x ∂μ) + (m : ℝ)*Real.log (a n))
      atTop (𝓝 (gaussianEntropyValue (Fin m) (heatVariance t))) := by
  have hb : Tendsto (fun n => ((2 : ℝ)^m/2)*(1/(2*t))*m*(a n)^2) atTop (𝓝 0) := by
    simpa using (ha0.pow 2).const_mul (((2 : ℝ)^m/2)*(1/(2*t))*m)
  have hg := squeeze_zero
    (fun n => (integral_heatGridConditionalEntropy_error μ ht (a n) (ha n)).1)
    (fun n => (integral_heatGridConditionalEntropy_error μ ht (a n) (ha n)).2) hb
  simpa only [sub_add_cancel, zero_add] using hg.add_const (gaussianEntropyValue (Fin m) (heatVariance t))

private theorem finite_quantizer_entropy_le_grid {m : ℕ}
    (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := Fin m)) μ)
    (a : ℝ) (ha : 0 < a) (K : ℕ) :
    Finite.entropy (lawMass μ (clippedGridVector a K)) ≤ countableEntropy (lawMass μ (gridLabel a)) := by
  let Y := gridLabel (I := Fin m) a
  have hY := measurable_gridLabel (I := Fin m) a
  have hE : MemLp (fun x => integerEnergy (Y x)) 2 μ :=
    memLp_gridEnergy μ id measurable_id (coordinate_memLp_two_of_squareRadius μ hμ) a ha
  have hs := lawMass_hasSum μ Y hY
  have hm := (lawMass_weighted_hasSum μ Y hY integerEnergy (hE.integrable (by norm_num))).summable
  have hH := summable_integer_entropy (lawMass μ Y) (lawMass_nonneg μ Y) hs hm
  have he : countablePush (lawMass μ Y) (codedClipIntegerVector (K+1) (by omega)) =
      lawMass μ (clippedGridVector a K) := by
    funext j
    exact countablePush_lawMass μ Y hY _ j
  have h := countableEntropy_push_le (lawMass μ Y) (lawMass_nonneg μ Y) hs hH
    (codedClipIntegerVector (K+1) (by omega))
  rw [he, countableEntropy, tsum_fintype] at h
  exact h

/-- Averaging the finite-output conditional entropy commutes with cutoff
removal, by a proved uniform bound and ordinary dominated convergence. -/
theorem tendsto_integral_heatFiniteConditionalEntropy_cutoff {m : ℕ}
    (μ : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun K => ∫ x, heatFiniteConditionalEntropy a t K x ∂μ) atTop
      (𝓝 (∫ x, heatGridConditionalEntropy a t x ∂μ)) := by
  have hm (K : ℕ) : AEStronglyMeasurable (heatFiniteConditionalEntropy (m := m) a t K) μ := by
    apply Continuous.aestronglyMeasurable
    unfold heatFiniteConditionalEntropy Finite.entropy
    apply continuous_finset_sum
    intro b _
    exact Real.continuous_negMulLog.comp (continuous_heatQuantizerMass _ (measurable_clippedGridVector a K) ht b)
  have hb (K : ℕ) : ∀ᵐ x ∂μ, ‖heatFiniteConditionalEntropy a t K x‖ ≤ conditionalEntropyEnvelope m a t := by
    filter_upwards [] with x
    have hpos := Finite.entropy_nonneg (heatQuantizerMass (clippedGridVector a K) t x)
      (heatQuantizerMass_nonneg _ t x) (heatQuantizerMass_sum _ (measurable_clippedGridVector a K) t x)
    change |Finite.entropy (heatQuantizerMass (clippedGridVector a K) t x)| ≤ _
    rw [abs_of_nonneg hpos]
    have hle := finite_quantizer_entropy_le_grid (heatedLaw (Measure.dirac x) t)
      (integrable_heatedLaw_squareRadius (Measure.dirac x) integrable_dirac t) a ha K
    rw [← heatFiniteConditionalEntropy_eq_law ht,
      lawMass_heatedLaw_gridLabel (Measure.dirac x) ht a ha] at hle
    exact hle.trans ((le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs] using norm_heatGridConditionalEntropy_le ht a ha x))
  exact tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => conditionalEntropyEnvelope m a t)
    hm (integrable_const _) hb (ae_of_all _ (tendsto_heatFiniteConditionalEntropy_cutoff ht a ha))
end GaussianWave.BS
