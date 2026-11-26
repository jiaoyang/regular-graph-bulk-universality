import GeneralizedBulk.Graph.SpectralGoodImage
import GeneralizedBulk.Graph.GraphCappedMoments
import GeneralizedBulk.Analysis.CappedAffineMoments

/-! Actual spectral-model good events transfer to the uniform graph law.
The resulting capped scalar moments keep every finite exceptional error. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Graph GeneralizedBulk.Analysis
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem exists_spectral_capped_goodExcess_moments {P : Measure Ω} [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (hd : 0 < d) (E : ℝ) (hE : |E| < d) (cstar : ℝ) (hcstar : 0 < cstar)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ B step : ℝ,0 < B ∧ 0 < step ∧ ∀ n,∀ eta : ℝ,
      0 < eta → eta ≤ 1 → cstar ≤ (N n : ℝ)*eta →
      ∀ good : Set Ω,MeasurableSet good →
      (∀ ω ∈ good,∀ i j,
        (∫ s : {s : EdgePairState (N n) d // edgePairGraph s=D.spectralRegularGraph n ω},
          ‖graphDeviation (s : EdgePairState (N n) d) (spectralParameter E eta) i j‖^2
          ∂finiteUniform {s : EdgePairState (N n) d // edgePairGraph s=D.spectralRegularGraph n ω}) ≤
          C*(1+graphHeight (D.spectralRegularGraph n ω) (spectralParameter E eta))) →
      ∀ m q : ℕ,
      (∫ ω,min (goodExcess good (fun ω => graphHeight (D.spectralRegularGraph n ω) (spectralParameter E eta)) B ω)
        (step*(m : ℝ))^q ∂P) ≤
      step^q*(geometricMomentConstant q+
        2*((4+2*(d : ℝ))/(N n : ℝ)+P.real goodᶜ)*(m : ℝ)*(((m+1 : ℕ) : ℝ)^q)) := by
  letI : Nonempty Ω := MeasureTheory.ProbabilityMeasure.nonempty (⟨P,inferInstance⟩ : ProbabilityMeasure Ω)
  obtain ⟨B,step,hB,hstep,hbound⟩ := exists_graph_capped_goodExcess_moments d hd E hE cstar hcstar C hC
  refine ⟨B,step,hB,hstep,?_⟩
  intro n eta heta heta1 hheight good hgood hvariance m q
  letI : Nonempty (RegularGraph (N n) d) := ⟨D.spectralRegularGraph n (Classical.choice ‹Nonempty Ω›)⟩
  let g : Set (RegularGraph (N n) d) := D.spectralRegularGraph n '' good
  let T := fun G : RegularGraph (N n) d => graphHeight G (spectralParameter E eta)
  let H := goodExcess good (fun ω => T (D.spectralRegularGraph n ω)) B
  let HG := goodExcess g T B
  have hg : MeasurableSet g := (Set.to_countable g).measurableSet
  have hT : Measurable T := measurable_of_finite _
  have hH : Measurable H := measurable_goodExcess good _ B hgood (hT.comp (D.measurable_spectralRegularGraph n))
  have hHG : Measurable HG := measurable_goodExcess g T B hg hT
  have hdom (ω : Ω) : H ω ≤ HG (D.spectralRegularGraph n ω) := by
    by_cases hω : ω ∈ good
    · have himage : D.spectralRegularGraph n ω ∈ g := ⟨ω,hω,rfl⟩
      simp only [H,HG,goodExcess,if_pos hω,if_pos himage,le_refl]
    · simpa only [H,goodExcess,if_neg hω] using goodExcess_nonneg g T B (D.spectralRegularGraph n ω)
  have hL := integrable_nonnegative_cap_pow P H hH (fun ω => goodExcess_nonneg _ _ _ ω)
    (step*(m : ℝ)) (by positivity) q
  have hR := integrable_nonnegative_cap_pow P (fun ω => HG (D.spectralRegularGraph n ω))
    (hHG.comp (D.measurable_spectralRegularGraph n))
    (fun ω => goodExcess_nonneg _ _ _ (D.spectralRegularGraph n ω)) (step*(m : ℝ)) (by positivity) q
  have hI : (∫ ω,min (H ω) (step*(m : ℝ))^q ∂P) ≤
      ∫ ω,min (HG (D.spectralRegularGraph n ω)) (step*(m : ℝ))^q ∂P := by
    apply integral_mono hL hR
    intro ω
    exact pow_le_pow_left₀ (le_min (goodExcess_nonneg _ _ _ ω) (by positivity))
      (min_le_min_right _ (hdom ω)) q
  have hmodel : (∫ ω,min (HG (D.spectralRegularGraph n ω)) (step*(m : ℝ))^q ∂P)=
      ∫ G,min (HG G) (step*(m : ℝ))^q ∂regularGraphLaw (N n) d := by
    rw [← hUniform n,integral_map (D.measurable_spectralRegularGraph n).aemeasurable
      ((hHG.min measurable_const).pow_const q).aestronglyMeasurable]
  have hV : ∀ G ∈ g,∀ i j,
      (∫ s : {s : EdgePairState (N n) d // edgePairGraph s=G},
        ‖graphDeviation (s : EdgePairState (N n) d) (spectralParameter E eta) i j‖^2
        ∂finiteUniform {s : EdgePairState (N n) d // edgePairGraph s=G}) ≤ C*(1+T G) := by
    rintro G ⟨ω,hω,rfl⟩
    exact hvariance ω hω
  have hb := hbound (N n) (D.size_pos n) eta heta heta1 hheight g hV m q
  have hbad : (regularGraphLaw (N n) d).real gᶜ ≤ P.real goodᶜ := by
    rw [← hUniform n]
    exact map_good_image_real_failure_le P _ (D.measurable_spectralRegularGraph n) good hg
  rw [hmodel] at hI
  refine (hI.trans hb).trans ?_
  gcongr

end GeneralizedBulk.External.RegularSpectralData
