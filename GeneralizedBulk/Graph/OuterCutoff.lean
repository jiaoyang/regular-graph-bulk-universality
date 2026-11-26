import GeneralizedBulk.Graph.PolynomialCompression

/-!
# A continuous outer resolvent cutoff and its uniform polynomial approximation

The cutoff is explicit. The outer spectral weight converges uniformly to a
continuous real function before polynomial functional calculus is applied.
-/
noncomputable section
open scoped Topology Classical
namespace GeneralizedBulk.Graph

def outerCutoff (E gap t : ℝ) : ℝ := max 0 (min 1 (2 - |t - E| / gap))

theorem continuous_outerCutoff (E gap : ℝ) : Continuous (outerCutoff E gap) :=
  continuous_const.max (continuous_const.min (continuous_const.sub
    ((continuous_id.sub continuous_const).abs.div_const gap)))

theorem outerCutoff_bounds (E gap t : ℝ) : 0 ≤ outerCutoff E gap t ∧ outerCutoff E gap t ≤ 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem outerCutoff_eq_one (E gap t : ℝ) (hgap : 0 < gap) (ht : |t - E| ≤ gap) :
    outerCutoff E gap t = 1 := by
  have hratio : |t - E| / gap ≤ 1 := (div_le_one hgap).mpr ht
  rw [outerCutoff, min_eq_left (by linarith), max_eq_right (by norm_num)]

theorem outerCutoff_eq_zero (E gap t : ℝ) (hgap : 0 < gap) (ht : 2 * gap ≤ |t - E|) :
    outerCutoff E gap t = 0 := by
  have hratio : 2 ≤ |t - E| / gap := (le_div_iff₀ hgap).mpr ht
  rw [outerCutoff, max_eq_left ((min_le_right _ _).trans (by linarith))]

def outerRealWeight (theta : ℝ → ℝ) (E t : ℝ) : ℝ := (1 - theta t) / (t - E)

def outerComplexWeight (theta : ℝ → ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  ((1 - theta t : ℝ) : ℂ) / ((t : ℂ) - z)

/-- The apparent pole of the limiting real outer weight is removable,
because the explicit cutoff is identically one on a neighborhood. -/
theorem continuous_outerRealWeight (E gap : ℝ) (hgap : 0 < gap) :
    Continuous (outerRealWeight (outerCutoff E gap) E) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = E
  · subst x
    have heq : (fun _ : ℝ => (0 : ℝ)) =ᶠ[nhds E] outerRealWeight (outerCutoff E gap) E := by
      filter_upwards [Metric.ball_mem_nhds E hgap] with t ht
      have hd : |t - E| ≤ gap := (by simpa only [Metric.mem_ball, Real.dist_eq] using ht : |t - E| < gap).le
      rw [outerRealWeight, outerCutoff_eq_one E gap t hgap hd]
      simp
    exact continuousAt_const.congr heq
  · exact ((continuous_const.sub (continuous_outerCutoff E gap)).continuousAt).div
      (continuous_id.sub continuous_const).continuousAt (sub_ne_zero.mpr hx)

/-- The actual outer complex weight differs from the real limiting weight
by at most `2 |z-E| / gap²`, uniformly in the real spectral variable. -/
theorem outerWeight_difference_norm_le (theta : ℝ → ℝ) (E gap : ℝ) (hgap : 0 < gap)
    (hbounds : ∀ t, 0 ≤ theta t ∧ theta t ≤ 1)
    (hone : ∀ t, |t - E| ≤ gap → theta t = 1)
    (z : ℂ) (hz : ‖z - (E : ℂ)‖ ≤ gap / 2) (t : ℝ) :
    ‖outerComplexWeight theta z t - ((outerRealWeight theta E t : ℝ) : ℂ)‖ ≤
      2 * ‖z - (E : ℂ)‖ / gap ^ 2 := by
  by_cases ht : |t - E| ≤ gap
  · rw [outerComplexWeight, outerRealWeight, hone t ht]
    simp only [sub_self, Complex.ofReal_zero, zero_div, norm_zero]
    positivity
  · have hr : gap < |t - E| := lt_of_not_ge ht
    have hdenE : ‖(t : ℂ) - (E : ℂ)‖ = |t - E| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hdenZ : gap / 2 ≤ ‖(t : ℂ) - z‖ := by
      have hn := norm_sub_norm_le ((t : ℂ) - (E : ℂ)) (z - (E : ℂ))
      have heq : ((t : ℂ) - (E : ℂ)) - (z - (E : ℂ)) = (t : ℂ) - z := by ring
      rw [heq, hdenE] at hn
      linarith
    have htE : (t : ℂ) - (E : ℂ) ≠ 0 := norm_ne_zero_iff.mp (by rw [hdenE]; exact ne_of_gt (hgap.trans hr))
    have htz : (t : ℂ) - z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt ((half_pos hgap).trans_le hdenZ))
    have hnum : ‖((1 - theta t : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hbounds t).2)]
      linarith [(hbounds t).1]
    have hiZ : ‖((t : ℂ) - z)⁻¹‖ ≤ (gap / 2)⁻¹ := by
      rw [norm_inv]
      exact (inv_le_inv₀ ((half_pos hgap).trans_le hdenZ) (half_pos hgap)).mpr hdenZ
    have hiE : ‖((t : ℂ) - (E : ℂ))⁻¹‖ ≤ gap⁻¹ := by
      rw [norm_inv, hdenE]
      exact (inv_le_inv₀ (hgap.trans hr) hgap).mpr hr.le
    have heq : outerComplexWeight theta z t - ((outerRealWeight theta E t : ℝ) : ℂ) =
        ((1 - theta t : ℝ) : ℂ) * (z - (E : ℂ)) * ((t : ℂ) - z)⁻¹ * ((t : ℂ) - (E : ℂ))⁻¹ := by
      simp only [outerComplexWeight, outerRealWeight, Complex.ofReal_div, Complex.ofReal_sub,
        Complex.ofReal_one]
      field_simp
      ring
    rw [heq, norm_mul, norm_mul, norm_mul]
    calc
      _ ≤ 1 * ‖z - (E : ℂ)‖ * (gap / 2)⁻¹ * gap⁻¹ := by gcongr
      _ = _ := by field_simp; ring

end GeneralizedBulk.Graph

namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

/-- A single fixed real polynomial approximates all finite outer resolvent
compressions, with the spectral displacement error displayed explicitly. -/
theorem exists_outer_polynomial_compression (E gap delta : ℝ) (hgap : 0 < gap) (hdelta : 0 < delta) :
    ∃ Q : Polynomial ℝ, ∀ n : ℕ, ∀ ω : Ω, ∀ z : ℂ, ‖z - (E : ℂ)‖ ≤ gap / 2 →
      ∀ v w : Fin (N n),
      ‖D.spectralMultiplier n ω (outerComplexWeight (outerCutoff E gap) z) v w -
        D.polynomialMatrix n ω Q v w‖ ≤ delta + 2 * ‖z - (E : ℂ)‖ / gap ^ 2 := by
  obtain ⟨Q,hQ⟩ := exists_polynomial_near_of_continuousOn (-(d : ℝ)) (d : ℝ)
    (outerRealWeight (outerCutoff E gap) E) (continuous_outerRealWeight E gap hgap).continuousOn delta hdelta
  refine ⟨Q, fun n ω z hz v w => ?_⟩
  apply D.spectralMultiplier_sub_polynomial_entry_norm_le n ω _ Q _ (by positivity) _ v w
  intro k
  calc
    _ ≤ ‖outerComplexWeight (outerCutoff E gap) z (D.eigenvalue n ω k) -
        ((outerRealWeight (outerCutoff E gap) E (D.eigenvalue n ω k) : ℝ) : ℂ)‖ +
      ‖((outerRealWeight (outerCutoff E gap) E (D.eigenvalue n ω k) : ℝ) : ℂ) -
        ((Q.eval (D.eigenvalue n ω k) : ℝ) : ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by
      have hfirst := outerWeight_difference_norm_le (outerCutoff E gap) E gap hgap
        (outerCutoff_bounds E gap) (fun t ht => outerCutoff_eq_one E gap t hgap ht) z hz (D.eigenvalue n ω k)
      have hsecond : ‖((outerRealWeight (outerCutoff E gap) E (D.eigenvalue n ω k) : ℝ) : ℂ) -
          ((Q.eval (D.eigenvalue n ω k) : ℝ) : ℂ)‖ ≤ delta := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
        exact (hQ _ (D.eigenvalue_mem_spectralInterval n ω k)).le
      linarith

end GeneralizedBulk.External.RegularSpectralData
