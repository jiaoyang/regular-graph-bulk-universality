import GeneralizedBulk.Graph.MicroscopicCappedMoments
import GeneralizedBulk.Analysis.CappedScalarRates

/-! The actual microscopic cap estimates have finite limiting constants at
every moment order, uniformly over all positive integer vertical heights. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology Classical
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Graph GeneralizedBulk.Analysis
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem exists_microscopic_capped_moment_limits {P : Measure Ω} [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (hd : 0 < d) (E : ℝ) (hE : |E| < d) (sigma center : ℝ) (hsigma : 0 < sigma)
    (good : ℕ → Set Ω) (hgood : ∀ n,MeasurableSet (good n))
    (β Cbad : ℝ) (hβ : 0 < β) (hCbad : 0 ≤ Cbad)
    (hbad : ∀ᶠ n in atTop,P.real (good n)ᶜ ≤ Cbad*(N n : ℝ)^(-β))
    (V : ℝ) (hV : 0 ≤ V)
    (hvariance : ∀ᶠ n in atTop,∀ ω ∈ good n,∀ eta : ℝ,0 < eta → 1/sigma ≤ (N n : ℝ)*eta → ∀ i j,
      (∫ t : {t : EdgePairState (N n) d // edgePairGraph t=D.spectralRegularGraph n ω},
        ‖graphDeviation (t : EdgePairState (N n) d) (spectralParameter E eta) i j‖^2
        ∂finiteUniform {t : EdgePairState (N n) d // edgePairGraph t=D.spectralRegularGraph n ω}) ≤
        V*(1+graphHeight (D.spectralRegularGraph n ω) (spectralParameter E eta))) :
    ∃ cap : ℕ → ℝ,(∀ n,0 ≤ cap n) ∧ Tendsto cap atTop atTop ∧
      ∃ constants : ℕ → ℝ,(∀ q,0 ≤ constants q) ∧ ∃ bounds : ℕ → ℕ → ℝ,
      (∀ q,Tendsto (bounds q) atTop (nhds (constants q))) ∧
      ∀ Y q : ℕ,∀ᶠ n in atTop,
        (∫ ω,(good n).indicator (fun ω => min (D.microscopicVerticalNorm n ω E sigma center Y) (cap n)^q) ω ∂P) ≤
          bounds q n := by
  obtain ⟨B,step,hB,hstep,hfinite⟩ := D.exists_microscopic_capped_vertical_moments hUniform hd E hE sigma center hsigma
    good hgood V hV hvariance
  let a : ℝ := |center|/sigma
  let b : ℝ := 1/sigma
  let epsilon := fun n => (4+2*(d : ℝ))/(N n : ℝ)+P.real (good n)ᶜ
  have ha : 0 ≤ a := div_nonneg (abs_nonneg _) hsigma.le
  have hb : 0 < b := one_div_pos.mpr hsigma
  have hε0 (n) : 0 ≤ epsilon n := add_nonneg (div_nonneg (by positivity) (Nat.cast_nonneg _)) measureReal_nonneg
  have hε := scalar_tail_error_polynomial N D.size_pos (fun n => P.real (good n)ᶜ)
    (4+2*(d : ℝ)) Cbad β (by positivity) hCbad hbad
  refine ⟨fun n => affineScalarCap a b B step (N n),
    fun n => affineScalarCap_nonneg a b B step ha hb.le hB.le hstep.le (N n),
    affineScalarCap_tendsto_atTop N D.size_tendsto a b B step hb hstep,
    fun q => affineScalarMomentLimit a b B step q,
    fun q => affineScalarMomentLimit_nonneg a b B step ha hb.le hB.le hstep.le q,
    fun q n => affineScalarMomentBound a b B step (epsilon n) (N n) q,?_,?_⟩
  · intro q
    exact affineScalarMomentBound_tendsto N D.size_tendsto epsilon hε0
      (4+2*(d : ℝ)+Cbad) (min 1 β) a b B step (by positivity) (lt_min (by norm_num) hβ) hε q
  · exact hfinite

end GeneralizedBulk.External.RegularSpectralData
