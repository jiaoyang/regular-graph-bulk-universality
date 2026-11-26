import GeneralizedBulk.Spectral.KestenMcKayDensity
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-! The actual Kesten–McKay probability measure and its deterministic
quantiles, constructed from its continuous strictly increasing CDF. -/
noncomputable section
open scoped Topology
open Set MeasureTheory
namespace GeneralizedBulk.KestenMcKay

def law (d : ℝ) : Measure ℝ :=
  (volume.restrict (Icc (-radius d) (radius d))).withDensity (fun x => ENNReal.ofReal (rawDensity d x))

def cdf (d x : ℝ) : ℝ := ∫ t in -radius d..x, rawDensity d t

theorem measurable_rawDensity (d : ℝ) : Measurable (rawDensity d) := by
  unfold rawDensity
  fun_prop

theorem law_isProbability (d : ℝ) (hd : 3 ≤ d) : IsProbabilityMeasure (law d) := by
  constructor
  rw [law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal ((continuousOn_rawDensity d hd).integrableOn_Icc)
    ((ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ (fun x hx => rawDensity_nonneg d hd hx)))]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [radius_pos d hd]),
    integral_rawDensity d hd]
  norm_num

theorem cdf_lower (d : ℝ) : cdf d (-radius d) = 0 := by simp [cdf]

theorem cdf_upper (d : ℝ) (hd : 3 ≤ d) : cdf d (radius d) = 1 := integral_rawDensity d hd

theorem continuousOn_cdf (d : ℝ) (hd : 3 ≤ d) : ContinuousOn (cdf d) (Icc (-radius d) (radius d)) := by
  have hi : IntegrableOn (rawDensity d) (uIcc (-radius d) (radius d)) volume := by
    simpa only [uIcc_of_le (by linarith [radius_pos d hd] : -radius d ≤ radius d)] using
      (continuousOn_rawDensity d hd).integrableOn_Icc
  have hh := intervalIntegral.continuousOn_primitive_interval hi
  simpa only [uIcc_of_le (by linarith [radius_pos d hd] : -radius d ≤ radius d), cdf] using hh

theorem cdf_hasDerivAt (d : ℝ) (hd : 3 ≤ d) {x : ℝ}
    (hx : x ∈ Icc (-radius d) (radius d)) : HasDerivAt (cdf d) (rawDensity d x) x := by
  have hi : IntervalIntegrable (rawDensity d) volume (-radius d) x := by
    apply ContinuousOn.intervalIntegrable_of_Icc hx.1
    exact (continuousOn_rawDensity d hd).mono (Icc_subset_Icc le_rfl hx.2)
  have hc : ContinuousAt (rawDensity d) x := by
    unfold rawDensity
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (rawDenominator_pos d hd hx).ne'
  exact intervalIntegral.integral_hasDerivAt_right hi
    (measurable_rawDensity d).stronglyMeasurable.stronglyMeasurableAtFilter hc

theorem rawDensity_pos (d : ℝ) (hd : 3 ≤ d) {x : ℝ}
    (hx : x ∈ Ioo (-radius d) (radius d)) : 0 < rawDensity d x := by
  have hs : x ^ 2 < radius d ^ 2 := by
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg x) (radius_pos d hd).le).mpr (abs_lt.mpr hx)
  rw [radius_sq d hd] at hs
  exact div_pos (mul_pos (by linarith) (Real.sqrt_pos.mpr (by linarith)))
    (mul_pos (mul_pos (by norm_num) Real.pi_pos) (rawDenominator_pos d hd ⟨hx.1.le, hx.2.le⟩))

theorem strictMonoOn_cdf (d : ℝ) (hd : 3 ≤ d) : StrictMonoOn (cdf d) (Icc (-radius d) (radius d)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuousOn_cdf d hd)
  intro x hx
  rw [interior_Icc] at hx
  rw [(cdf_hasDerivAt d hd ⟨hx.1.le, hx.2.le⟩).deriv]
  exact rawDensity_pos d hd hx

theorem exists_quantile (d : ℝ) (hd : 3 ≤ d) (u : Icc (0 : ℝ) 1) :
    ∃ x ∈ Icc (-radius d) (radius d), cdf d x = u := by
  have hi := intermediate_value_Icc (by linarith [radius_pos d hd] : -radius d ≤ radius d)
    (continuousOn_cdf d hd)
  rw [cdf_lower, cdf_upper d hd] at hi
  exact hi u.property

def quantile (d : ℝ) (hd : 3 ≤ d) (u : Icc (0 : ℝ) 1) : ℝ :=
  Classical.choose (exists_quantile d hd u)

theorem quantile_mem (d : ℝ) (hd : 3 ≤ d) (u : Icc (0 : ℝ) 1) :
    quantile d hd u ∈ Icc (-radius d) (radius d) := (Classical.choose_spec (exists_quantile d hd u)).1

theorem cdf_quantile (d : ℝ) (hd : 3 ≤ d) (u : Icc (0 : ℝ) 1) :
    cdf d (quantile d hd u) = u := (Classical.choose_spec (exists_quantile d hd u)).2

theorem strictMono_quantile (d : ℝ) (hd : 3 ≤ d) : StrictMono (quantile d hd) := by
  intro u v huv
  by_contra hh
  have hh' : quantile d hd v ≤ quantile d hd u := le_of_not_gt hh
  have ht := (strictMonoOn_cdf d hd).monotoneOn (quantile_mem d hd v) (quantile_mem d hd u) hh'
  rw [cdf_quantile, cdf_quantile] at ht
  exact not_le_of_lt huv ht

theorem quantile_lower (d : ℝ) (hd : 3 ≤ d) : quantile d hd ⟨0, by constructor <;> norm_num⟩ = -radius d := by
  apply (strictMonoOn_cdf d hd).injOn (quantile_mem d hd _) ⟨le_rfl, by linarith [radius_pos d hd]⟩
  rw [cdf_quantile, cdf_lower]

theorem quantile_upper (d : ℝ) (hd : 3 ≤ d) : quantile d hd ⟨1, by constructor <;> norm_num⟩ = radius d := by
  apply (strictMonoOn_cdf d hd).injOn (quantile_mem d hd _) ⟨by linarith [radius_pos d hd], le_rfl⟩
  rw [cdf_quantile, cdf_upper d hd]

/-- Quantile cells have their exact prescribed probability mass. -/
theorem integral_quantile_cell (d : ℝ) (hd : 3 ≤ d) (u v : Icc (0 : ℝ) 1) :
    (∫ t in quantile d hd u..quantile d hd v, rawDensity d t) = v.val - u.val := by
  have hi (w : Icc (0 : ℝ) 1) : IntervalIntegrable (rawDensity d) volume (-radius d) (quantile d hd w) := by
    have hw := quantile_mem d hd w
    exact ContinuousOn.intervalIntegrable_of_Icc hw.1
      ((continuousOn_rawDensity d hd).mono (Icc_subset_Icc le_rfl hw.2))
  have hh := intervalIntegral.integral_interval_sub_left (hi v) (hi u)
  change cdf d (quantile d hd v) - cdf d (quantile d hd u) = _ at hh
  rw [cdf_quantile, cdf_quantile] at hh
  exact hh.symm

end GeneralizedBulk.KestenMcKay
