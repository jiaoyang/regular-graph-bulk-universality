import GeneralizedBulk.Graph.FixedEnergyWasserstein

/-! The literal fixed-energy supremum is finite on every graph. The bound
uses the independent coupling and the exact physical second moments; no
asymptotic, moment-event, BS, or HY premise is needed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators Classical ENNReal

namespace GeneralizedBulk.Graph

private theorem independent_cost_le_second_moments
    {ι : Type*} [Fintype ι] (μ ν : Measure (ι → ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable GaussianWave.squareMass μ)
    (hν : Integrable GaussianWave.squareMass ν) :
    GaussianWave.wassersteinTwoSquared μ ν ≤ ENNReal.ofReal
      (2 * (∫ x, GaussianWave.squareMass x ∂μ) +
        2 * (∫ x, GaussianWave.squareMass x ∂ν)) := by
  let γ := GaussianWave.Coupling.independent μ ν
  have hl := (γ.integrable_fst _ hμ).const_mul 2
  have hr := (γ.integrable_snd _ hν).const_mul 2
  have hc : Integrable GaussianWave.squareTransportCost γ.measure := by
    apply (hl.add hr).mono'
      GaussianWave.continuous_squareTransportCost.measurable.aestronglyMeasurable
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (GaussianWave.squareTransportCost_nonneg z)]
    exact GaussianWave.squareTransportCost_le z
  have hb : (∫ z, GaussianWave.squareTransportCost z ∂γ.measure) ≤
      2 * (∫ x, GaussianWave.squareMass x ∂μ) +
        2 * (∫ x, GaussianWave.squareMass x ∂ν) := by
    calc
      _ ≤ ∫ z, (2 * GaussianWave.squareMass z.1 +
          2 * GaussianWave.squareMass z.2) ∂γ.measure :=
        integral_mono hc (hl.add hr) GaussianWave.squareTransportCost_le
      _ = _ := by
        rw [integral_add hl hr, integral_const_mul, integral_const_mul,
          γ.integral_fst _ hμ.aestronglyMeasurable,
          γ.integral_snd _ hν.aestronglyMeasurable]
  have heq : GaussianWave.quadraticCouplingCost γ =
      ENNReal.ofReal (∫ z, GaussianWave.squareTransportCost z ∂γ.measure) :=
    (ofReal_integral_eq_lintegral_ofReal hc
      (Eventually.of_forall GaussianWave.squareTransportCost_nonneg)).symm
  exact (GaussianWave.wassersteinTwoSquared_le_cost γ).trans
    (heq ▸ ENNReal.ofReal_le_ofReal hb)

/-- Exact unit coordinate second moments give a uniform physical squared
Wasserstein bound against the Gaussian product at the fixed energy. The bound
holds for every actual orthonormal candidate, without an energy-window premise. -/
theorem graphEigenCandidate_wassersteinTwoSquared_common_energy_le
    {d M k : ℕ} (hd : 3 ≤ d)
    (E : ℝ) (hE : E ^ 2 < 4 * ((d : ℝ) - 1))
    {g : RegularGraph M d} (A : GraphEigenCandidate d M k g) :
    GaussianWave.wassersteinTwoSquared A.val.eigenStarLaw
      (commonEnergyStarGaussian d k E (by omega)
        (strictBulk_abs_le_degree d hd E hE)) ≤
      ENNReal.ofReal (4 * (Fintype.card (Fin k × Fin (d + 1)) : ℝ)) := by
  let μ := A.val.eigenStarLaw
  let ν := commonEnergyStarGaussian d k E (by omega)
    (strictBulk_abs_le_degree d hd E hE)
  have hμi (a : Fin k × Fin (d + 1)) : Integrable (fun x => x a ^ 2) μ :=
    A.val.integrable_starLaw A.val.eigenvector _
  have hνi (a : Fin k × Fin (d + 1)) : Integrable (fun x => x a ^ 2) ν :=
    GaussianWave.gaussianCovarianceLaw_coordinate_integrable_pow _ _ a 2
  have hμ : Integrable GaussianWave.squareMass μ := by
    exact A.val.integrable_starLaw _ _
  have hν : Integrable GaussianWave.squareMass ν := by
    apply integrable_finset_sum
    intro a _
    exact hνi a
  have hμsecond (a : Fin k × Fin (d + 1)) : (∫ x, x a ^ 2 ∂μ) = 1 := by
    have heq : (∫ x, x a * x a ∂μ) = A.val.eigenStarCovariance a a :=
      A.val.integral_star_orthonormal_eigen_covariance (by omega) id
        Function.injective_id a.1 a.1 a.2 a.2
    simpa only [pow_two, A.val.eigenStarCovariance_diagonal] using heq
  have hνsecond (a : Fin k × Fin (d + 1)) : (∫ x, x a ^ 2 ∂ν) = 1 :=
    commonEnergyStarGaussian_coordinate_second d k E (by omega)
      (strictBulk_abs_le_degree d hd E hE) a
  have hμmass : (∫ x, GaussianWave.squareMass x ∂μ) =
      (Fintype.card (Fin k × Fin (d + 1)) : ℝ) := by
    change (∫ x, ∑ a : Fin k × Fin (d + 1), x a ^ 2 ∂μ) = _
    rw [integral_finset_sum _ (fun a _ => hμi a)]
    simp only [hμsecond, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hνmass : (∫ x, GaussianWave.squareMass x ∂ν) =
      (Fintype.card (Fin k × Fin (d + 1)) : ℝ) := by
    change (∫ x, ∑ a : Fin k × Fin (d + 1), x a ^ 2 ∂ν) = _
    rw [integral_finset_sum _ (fun a _ => hνi a)]
    simp only [hνsecond, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hb := independent_cost_le_second_moments μ ν hμ hν
  rw [hμmass, hνmass] at hb
  convert hb using 1
  congr 1
  ring

/-- A common finite bound for the complete fixed-energy supremum, including
empty windows and arbitrary eigenspace rotations. -/
theorem fixedEnergyStarWassersteinSup_le
    {d M k : ℕ} (hd : 3 ≤ d)
    (E : ℝ) (hE : E ^ 2 < 4 * ((d : ℝ) - 1))
    (g : RegularGraph M d) (δ : ℝ) :
    fixedEnergyStarWassersteinSup (k := k) hd E hE g δ ≤
      ENNReal.ofReal (4 * (Fintype.card (Fin k × Fin (d + 1)) : ℝ)) ^ (1 / 2 : ℝ) := by
  apply iSup_le
  intro A
  apply iSup_le
  intro _hwindow
  exact ENNReal.rpow_le_rpow
    (graphEigenCandidate_wassersteinTwoSquared_common_energy_le hd E hE A)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)

/-- The extended-real presentation of the literal supremum always has a
finite value, so it represents an ordinary real Wasserstein discrepancy. -/
theorem fixedEnergyStarWassersteinSup_lt_top
    {d M k : ℕ} (hd : 3 ≤ d)
    (E : ℝ) (hE : E ^ 2 < 4 * ((d : ℝ) - 1))
    (g : RegularGraph M d) (δ : ℝ) :
    fixedEnergyStarWassersteinSup (k := k) hd E hE g δ < ⊤ :=
  (fixedEnergyStarWassersteinSup_le hd E hE g δ).trans_lt
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
      ENNReal.ofReal_ne_top)

end GeneralizedBulk.Graph
