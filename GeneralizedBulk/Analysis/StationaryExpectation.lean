import Mathlib

/-!
# Stationary differentiation by the fundamental theorem and Fubini

The vanishing expected response is a conclusion. Its inputs are genuine path
derivatives, joint measurability, one integrable response, and equality of laws.
Stationarity supplies the joint integrability needed for Fubini, so no uniform
pointwise domination of derivatives is postulated.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace GeneralizedBulk.Analysis

def angleMeasure : Measure ℝ := volume.restrict (Set.Ioc 0 1)

instance : IsProbabilityMeasure angleMeasure := by
  constructor
  simp [angleMeasure]

/-- An integrable stationary response is integrable jointly in time and the
sample. Only joint strong measurability must be proved by the flow constructor. -/
theorem integrable_stationary_path
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (G : ℝ → Ω → ℂ)
    (hjoint : AEStronglyMeasurable (fun z : ℝ × Ω => G z.1 z.2) (angleMeasure.prod P))
    (hzero : Integrable (G 0) P)
    (hstationary : ∀ t ∈ Set.Ioc (0 : ℝ) 1, IdentDistrib (G t) (G 0) P P) :
    Integrable (fun z : ℝ × Ω => G z.1 z.2) (angleMeasure.prod P) := by
  apply (integrable_prod_iff hjoint).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (hstationary t ht).symm.integrable_snd hzero
  · apply (integrable_const (∫ ω, ‖G 0 ω‖ ∂P) : Integrable _ angleMeasure).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact ((hstationary t ht).comp measurable_norm).integral_eq.symm

/-- A smooth stationary observable has zero expected derivative. This proof
uses a finite time integral, avoiding differentiation of an expectation by an
unproved domination argument. -/
theorem integral_response_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (F G : ℝ → Ω → ℂ)
    (hFzero : Integrable (F 0) P)
    (hGzero : Integrable (G 0) P)
    (hjoint : AEStronglyMeasurable (fun z : ℝ × Ω => G z.1 z.2) (angleMeasure.prod P))
    (hderivative : ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun u => F u ω) (G t ω) t)
    (hFstationary : IdentDistrib (F 1) (F 0) P P)
    (hGstationary : ∀ t ∈ Set.Ioc (0 : ℝ) 1, IdentDistrib (G t) (G 0) P P) :
    (∫ ω, G 0 ω ∂P) = 0 := by
  have hi := integrable_stationary_path P G hjoint hGzero hGstationary
  have hFTC : ∀ᵐ ω ∂P,
      (∫ t, G t ω ∂angleMeasure) = F 1 ω - F 0 ω := by
    filter_upwards [hderivative, hi.prod_left_ae] with ω hd ht
    have hinterval : IntervalIntegrable (fun t => G t ω) volume 0 1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).2 ht
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t hmem => hd t (by simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hmem))
      hinterval
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), angleMeasure] using heq
  have hFone : Integrable (F 1) P := hFstationary.symm.integrable_snd hFzero
  calc
    (∫ ω, G 0 ω ∂P) = ∫ t, (∫ ω, G t ω ∂P) ∂angleMeasure := by
      have heq : (∫ t, (∫ ω, G t ω ∂P) ∂angleMeasure) =
          ∫ t, (∫ ω, G 0 ω ∂P) ∂angleMeasure := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact (hGstationary t ht).integral_eq
      rw [heq]
      simp
    _ = ∫ ω, (∫ t, G t ω ∂angleMeasure) ∂P := integral_integral_swap hi
    _ = ∫ ω, (F 1 ω - F 0 ω) ∂P := integral_congr_ae hFTC
    _ = (∫ ω, F 1 ω ∂P) - ∫ ω, F 0 ω ∂P := integral_sub hFone hFzero
    _ = 0 := by rw [hFstationary.integral_eq]; ring

end GeneralizedBulk.Analysis
