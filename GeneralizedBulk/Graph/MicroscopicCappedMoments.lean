import GeneralizedBulk.Graph.SpectralCappedMoments
import GeneralizedBulk.Graph.MicroscopicHeightBounds
import GeneralizedBulk.Analysis.ScalarCapBounds

/-! Actual microscopic scalar moments are controlled through finite caps.
The same cap and limiting constants work at every positive integer height. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology Classical
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Graph GeneralizedBulk.Analysis
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem exists_microscopic_capped_vertical_moments {P : Measure Ω} [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (hd : 0 < d) (E : ℝ) (hE : |E| < d) (sigma center : ℝ) (hsigma : 0 < sigma)
    (good : ℕ → Set Ω) (hgood : ∀ n,MeasurableSet (good n)) (V : ℝ) (hV : 0 ≤ V)
    (hvariance : ∀ᶠ n in atTop,∀ ω ∈ good n,∀ eta : ℝ,0 < eta → 1/sigma ≤ (N n : ℝ)*eta → ∀ i j,
      (∫ t : {t : EdgePairState (N n) d // edgePairGraph t=D.spectralRegularGraph n ω},
        ‖graphDeviation (t : EdgePairState (N n) d) (spectralParameter E eta) i j‖^2
        ∂finiteUniform {t : EdgePairState (N n) d // edgePairGraph t=D.spectralRegularGraph n ω}) ≤
        V*(1+graphHeight (D.spectralRegularGraph n ω) (spectralParameter E eta))) :
    ∃ B step : ℝ,0 < B ∧ 0 < step ∧ ∀ Y q : ℕ,∀ᶠ n in atTop,
      (∫ ω,(good n).indicator (fun ω => min (D.microscopicVerticalNorm n ω E sigma center Y)
        (affineScalarCap (|center|/sigma) (1/sigma) B step (N n))^q) ω ∂P) ≤
      affineScalarMomentBound (|center|/sigma) (1/sigma) B step
        ((4+2*(d : ℝ))/(N n : ℝ)+P.real (good n)ᶜ) (N n) q := by
  obtain ⟨B,step,hB,hstep,hbound⟩ := D.exists_spectral_capped_goodExcess_moments hUniform hd E hE
    (1/sigma) (one_div_pos.mpr hsigma) V hV
  refine ⟨B,step,hB,hstep,fun Y q => ?_⟩
  have heta1 : ∀ᶠ n in atTop,D.verticalMicroscopicEta n sigma Y ≤ 1 :=
    ((D.verticalMicroscopicEta_tendsto_zero sigma hsigma Y).eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))).mono
      (fun n hn => hn.le)
  filter_upwards [hvariance,heta1] with n hn hη1
  let eta := D.verticalMicroscopicEta n sigma Y
  let T := fun ω => graphHeight (D.spectralRegularGraph n ω) (spectralParameter E eta)
  let f := fun ω => D.microscopicVerticalNorm n ω E sigma center Y
  let a : ℝ := |center|/sigma
  let b : ℝ := 1/sigma
  let L := step*(logarithmicCap (N n) : ℝ)
  have ha : 0 ≤ a := div_nonneg (abs_nonneg _) hsigma.le
  have hb : 0 ≤ b := (one_div_pos.mpr hsigma).le
  have hL : 0 ≤ L := mul_nonneg hstep.le (Nat.cast_nonneg _)
  have hT : Measurable T := (measurable_of_finite (fun G : RegularGraph (N n) d => graphHeight G (spectralParameter E eta))).comp
    (D.measurable_spectralRegularGraph n)
  have hf : Measurable f := D.measurable_microscopicVerticalNorm n E sigma center Y
  have hpoint (ω : Ω) (_hω : ω ∈ good n) : f ω ≤ a+b*T ω :=
    D.microscopicVerticalNorm_affine_bound n ω E sigma center hsigma Y
  have hη := D.verticalMicroscopicEta_pos n sigma hsigma Y
  have hheight : 1/sigma ≤ (N n : ℝ)*eta := by
    rw [D.size_mul_verticalMicroscopicEta n sigma hsigma Y]
    exact div_le_div_of_nonneg_right (by have hy : (0:ℝ) ≤ Y := Nat.cast_nonneg Y; linarith : (1:ℝ) ≤ (Y : ℝ)+1) hsigma.le
  have hexc := hbound n eta hη hη1 hheight (good n) (hgood n)
    (fun ω hω i j => hn ω hω eta hη hheight i j) (logarithmicCap (N n)) q
  have haff := integral_good_capped_affine_le P (good n) (hgood n) T f hT hf
    (fun ω => norm_nonneg _) a b B L ha hb hB.le hL hpoint q
  have hmul := mul_le_mul_of_nonneg_left hexc (pow_nonneg hb q)
  have hfull := mul_le_mul_of_nonneg_left (add_le_add_left hmul ((a+b*B)^q))
    (by positivity : (0:ℝ) ≤ (2:ℝ)^(q-1))
  refine haff.trans ?_
  convert hfull using 1 <;> dsimp [a,b,L,affineScalarMomentBound] <;> ring

end GeneralizedBulk.External.RegularSpectralData
