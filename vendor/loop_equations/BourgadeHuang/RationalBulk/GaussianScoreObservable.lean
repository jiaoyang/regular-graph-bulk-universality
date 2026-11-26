import BourgadeHuang.RationalBulk.GaussianDensityDerivative
import BourgadeHuang.RationalBulk.GaussianScoreIntegrability

/-! Every polynomially bounded observable is integrable against the full
Gaussian-beta logarithmic score, including its collision terms. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

theorem gaussianBetaDensity_coordinate_smul_integrable {β : ℝ}
    (hβ : 0 < β) {N : ℕ} (hN : 0 < N) (i : Fin N)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin N → ℝ) → E} (hF : StronglyMeasurable F) {C : ℝ} (q : ℕ)
    (hbound : ∀ x, ‖F x‖ ≤ C * coordinateEnvelope x ^ q) :
    Integrable (fun x => (gaussianBetaDensity β N x * x i) • F x) := by
  have hC : 0 ≤ C := by
    have h := (norm_nonneg (F (fun _ => 0))).trans (hbound (fun _ => 0))
    simpa [coordinateEnvelope] using h
  apply ((gaussianBetaDensity_envelope_integrable hβ hN (q + 1)).const_mul C).mono'
  · exact (((gaussianBetaDensity_continuous hβ N).stronglyMeasurable.mul
      (measurable_pi_apply i).stronglyMeasurable).smul hF).aestronglyMeasurable
  · filter_upwards [] with x
    have hd := gaussianBetaDensity_nonneg β N x
    have he : 0 ≤ coordinateEnvelope x := zero_le_one.trans (coordinateEnvelope_one_le x)
    have hxi : |x i| ≤ coordinateEnvelope x := by
      have := coordinateEnvelope_coordinate x i
      linarith
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hd]
    calc
      _ ≤ (gaussianBetaDensity β N x * |x i|) * (C * coordinateEnvelope x ^ q) :=
        mul_le_mul_of_nonneg_left (hbound x) (mul_nonneg hd (abs_nonneg _))
      _ ≤ (gaussianBetaDensity β N x * coordinateEnvelope x) *
          (C * coordinateEnvelope x ^ q) := by gcongr
      _ = _ := by simp only [pow_succ, coordinateEnvelope]; ring

theorem gaussianBetaDensity_fullScore_smul_integrable {β : ℝ}
    (hβ : 0 < β) {N : ℕ} (hN : 0 < N) (i : Fin N)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin N → ℝ) → E} (hF : StronglyMeasurable F) {C : ℝ} (q : ℕ)
    (hbound : ∀ x, ‖F x‖ ≤ C * coordinateEnvelope x ^ q) :
    Integrable (fun x => (gaussianBetaDensity β N x * gaussianBetaScore β N x i) • F x) := by
  have hlinear := (gaussianBetaDensity_coordinate_smul_integrable hβ hN i hF q hbound).smul (-(β / (2 * (N : ℝ))))
  have hsingular : Integrable (fun x =>
      ∑ j ∈ Finset.univ.erase i, (gaussianBetaDensity β N x / (x i - x j)) • F x) := by
    apply integrable_finset_sum
    intro j hj
    exact gaussianBetaDensity_score_smul_integrable hβ hN i j
      (Ne.symm (Finset.mem_erase.mp hj).1) hF q hbound
  have h := hlinear.add (hsingular.smul β)
  convert h using 1
  funext x
  simp only [Pi.add_apply, Pi.smul_apply, gaussianBetaScore, mul_add, add_smul,
    Finset.smul_sum, Finset.sum_smul, Finset.mul_sum, div_eq_mul_inv, smul_smul]
  congr 1
  · congr 1
    ring
  · apply Finset.sum_congr rfl
    intro j hj
    congr 1
    ring

end BourgadeHuang.RationalBulk
