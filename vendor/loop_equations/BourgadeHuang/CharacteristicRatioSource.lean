import BourgadeHuang.CompactExponentialSources
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Characteristic-ratio observables as genuine integrals along straight paths. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

abbrev RatioInterval := Set.Icc (0 : ℝ) 1

def ratioIntervalMeasure : Measure RatioInterval := Measure.comap Subtype.val volume

instance : IsProbabilityMeasure ratioIntervalMeasure := by
  constructor
  change (Measure.comap Subtype.val (volume : Measure ℝ)) Set.univ = 1
  rw [← Measure.Subtype.volume_def, Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
  simp

/-- The straight path starts at the denominator and ends at the numerator. -/
def ratioPath (u v : ℂ) (t : ℝ) : ℂ := v + (t : ℂ) * (u - v)

def SameOpenHalfPlane (u v : ℂ) : Prop :=
  (0 < u.im ∧ 0 < v.im) ∨ (u.im < 0 ∧ v.im < 0)

theorem ratioPath_offReal {u v : ℂ} (h : SameOpenHalfPlane u v)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : (ratioPath u v t).im ≠ 0 := by
  have he : (ratioPath u v t).im = (1-t)*v.im + t*u.im := by simp [ratioPath]; ring
  rw [he]
  rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · have h₁ := mul_nonneg ht.1 hu.le
    have h₂ := mul_nonneg (sub_nonneg.mpr ht.2) hv.le
    by_cases ht0 : t = 0
    · simpa [ht0] using ne_of_gt hv
    · have h₃ := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) hu
      linarith
  · have h₁ := mul_nonpos_of_nonneg_of_nonpos ht.1 hu.le
    have h₂ := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.2) hv.le
    by_cases ht0 : t = 0
    · simpa [ht0] using ne_of_lt hv
    · have h₃ := mul_neg_of_pos_of_neg (lt_of_le_of_ne ht.1 (Ne.symm ht0)) hu
      linarith

theorem continuous_ratioPath (u v : ℂ) : Continuous (ratioPath u v) :=
  continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

def anchoredCharacteristicRatio (s : AnchoredCountingState) (u v : ℂ) : ℂ :=
  Complex.exp (∫ t : RatioInterval, -(u-v) * anchoredNevanlinna s (ratioPath u v t) ∂ratioIntervalMeasure)

theorem anchoredCharacteristicRatio_self (s : AnchoredCountingState) (v : ℂ) :
    anchoredCharacteristicRatio s v v = 1 := by simp [anchoredCharacteristicRatio]

theorem characteristicRatio_integrable_and_loop
    (ν : Measure AnchoredCountingState) (β : Beta) (hh : ExactAnchoredHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    {u v w : ℂ} (huv : SameOpenHalfPlane u v) (hw : w.im ≠ 0) :
    Integrable (fun s => anchoredCharacteristicRatio s u v) ν ∧
    Integrable (fun s => (anchoredLoopHead β s w +
      ∫ t : RatioInterval, -(u-v) * ((2/β.value)*anchoredInteraction s w (ratioPath u v t))
        ∂ratioIntervalMeasure) * anchoredCharacteristicRatio s u v) ν ∧
    (∫ s, (anchoredLoopHead β s w +
      ∫ t : RatioInterval, -(u-v) * ((2/β.value)*anchoredInteraction s w (ratioPath u v t))
        ∂ratioIntervalMeasure) * anchoredCharacteristicRatio s u v ∂ν) = 0 := by
  exact exponential_loop_identity_compact_source_and_integrable ratioIntervalMeasure
    (fun t : RatioInterval => ratioPath u v t) (fun _ => -(u-v))
    ((continuous_ratioPath u v).comp continuous_subtype_val) continuous_const
    (fun t => ratioPath_offReal huv t.property) ν β hh ha he hw

theorem integral_ratioInterval (f : ℝ → ℂ) :
    (∫ t : RatioInterval, f t ∂ratioIntervalMeasure) = ∫ t in (0:ℝ)..1, f t := by
  rw [ratioIntervalMeasure, integral_subtype_comap measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by norm_num)]

/-- The logarithm is used only along a path that never meets the real branch cut. -/
theorem integral_ratioPath_reciprocal {u v : ℂ} (huv : SameOpenHalfPlane u v) (x : ℝ) :
    (∫ t : RatioInterval, -(u-v) * ((x:ℂ)-ratioPath u v t)⁻¹ ∂ratioIntervalMeasure) =
      Complex.log ((x:ℂ)-u) - Complex.log ((x:ℂ)-v) := by
  have hd (t : ℝ) (ht : t ∈ Set.uIcc (0:ℝ) 1) :
      HasDerivAt (fun t : ℝ => Complex.log ((x:ℂ)-ratioPath u v t))
        (-(u-v)*((x:ℂ)-ratioPath u v t)⁻¹) t := by
    have hoff := ratioPath_offReal huv (Set.uIcc_of_le (by norm_num : (0:ℝ)≤1) ▸ ht)
    have hslit : (x:ℂ)-ratioPath u v t ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      right
      simpa using neg_ne_zero.mpr hoff
    have hp := ((hasDerivAt_const (t:ℂ) (x:ℂ)).sub
      ((hasDerivAt_const (t:ℂ) v).add ((hasDerivAt_id (t:ℂ)).mul_const (u-v)))).clog hslit
    convert hp.comp_ofReal using 1 <;> simp [ratioPath, div_eq_mul_inv]
  have hc : ContinuousOn (fun t : ℝ => -(u-v)*((x:ℂ)-ratioPath u v t)⁻¹)
      (Set.uIcc (0:ℝ) 1) := by
    apply continuousOn_const.mul
    apply ((continuous_const.sub (continuous_ratioPath u v)).continuousOn).inv₀
    intro t ht hzero
    have hoff := ratioPath_offReal huv (Set.uIcc_of_le (by norm_num : (0:ℝ)≤1) ▸ ht)
    apply hoff
    have hi := congrArg Complex.im hzero
    simpa using hi
  rw [integral_ratioInterval (fun t : ℝ => -(u-v)*((x:ℂ)-ratioPath u v t)⁻¹)]
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  simpa [ratioPath] using hf

/-- The integrated-resolvent definition agrees with the actual finite characteristic ratio. -/
theorem anchoredCharacteristicRatio_eq_finite {N : ℕ} (x : Fin N → ℝ) (center : ℝ)
    (ξ : LocalCountingMeasure) (hξ : ξ.measure = ∑ i, Measure.dirac (x i))
    {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    anchoredCharacteristicRatio
      ⟨(ξ, microscopicResolvent x center Complex.I), validAnchoredCountingState_finite x center ξ hξ⟩ u v =
      finiteCharacteristicRatio x center u v := by
  have hne {z : ℂ} (hz : z.im ≠ 0) (i : Fin N) : (x i:ℂ)-z ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    exact hz (by simpa using hi)
  have hu : u.im ≠ 0 := by
    rcases huv with ⟨h, _⟩ | ⟨h, _⟩
    · exact ne_of_gt h
    · exact ne_of_lt h
  have hv : v.im ≠ 0 := by
    rcases huv with ⟨_, h⟩ | ⟨_, h⟩
    · exact ne_of_gt h
    · exact ne_of_lt h
  have hint (i : Fin N) : Integrable
      (fun t : RatioInterval => -(u-v)*((x i:ℂ)-ratioPath u v t)⁻¹) ratioIntervalMeasure := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    apply continuous_const.mul
    exact (continuous_const.sub ((continuous_ratioPath u v).comp continuous_subtype_val)).inv₀
      (fun t => hne (ratioPath_offReal huv t.property) i)
  have harg : (∫ t : RatioInterval, -(u-v)*microscopicResolvent x center (ratioPath u v t)
      ∂ratioIntervalMeasure) = (center:ℂ)*(u-v) +
      ∑ i, (Complex.log ((x i:ℂ)-u) - Complex.log ((x i:ℂ)-v)) := by
    have halg (t : RatioInterval) : -(u-v)*microscopicResolvent x center (ratioPath u v t) =
        (center:ℂ)*(u-v) + ∑ i, -(u-v)*((x i:ℂ)-ratioPath u v t)⁻¹ := by
      simp only [microscopicResolvent]
      rw [← Finset.mul_sum]
      ring
    simp_rw [halg]
    rw [integral_add (integrable_const _) (integrable_finset_sum _ (fun i _ => hint i)),
      integral_finset_sum _ (fun i _ => hint i)]
    simp only [integral_ratioPath_reciprocal huv]
    simp
  unfold anchoredCharacteristicRatio
  have heq : (∫ t : RatioInterval, -(u-v)*anchoredNevanlinna
      ⟨(ξ, microscopicResolvent x center Complex.I), validAnchoredCountingState_finite x center ξ hξ⟩
      (ratioPath u v t) ∂ratioIntervalMeasure) =
      ∫ t : RatioInterval, -(u-v)*microscopicResolvent x center (ratioPath u v t) ∂ratioIntervalMeasure := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => congrArg (fun z : ℂ => -(u-v)*z)
      (anchoredNevanlinna_eq_finite x center ξ hξ (ratioPath_offReal huv t.property)))
  rw [heq, harg, Complex.exp_add, Complex.exp_sum]
  simp only [Complex.exp_sub, Complex.exp_log (hne hu _), Complex.exp_log (hne hv _),
    finiteCharacteristicRatio]

end BourgadeHuang
