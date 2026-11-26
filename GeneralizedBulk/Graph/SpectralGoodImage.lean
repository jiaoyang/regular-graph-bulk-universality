import GeneralizedBulk.Graph.HYResolventChannel
import GeneralizedBulk.Analysis.GoodEventImage

/-! Spectral good events give genuine graph-space good events even when
eigenvector choices carry additional randomness. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology Classical
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Graph GeneralizedBulk.Analysis
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

def spectralGoodImage (good : ℕ → Set Ω) (n : ℕ) : Set (RegularGraph (N n) d) :=
  D.spectralRegularGraph n '' good n

theorem measurableSet_spectralGoodImage (good : ℕ → Set Ω) (n : ℕ) :
    MeasurableSet (D.spectralGoodImage good n) := (Set.to_countable _).measurableSet

theorem spectralGoodImage_failure_le {P : Measure Ω} [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (good : ℕ → Set Ω) (n : ℕ) :
    (regularGraphLaw (N n) d).real (D.spectralGoodImage good n)ᶜ ≤ P.real (good n)ᶜ := by
  rw [← hUniform n]
  exact map_good_image_real_failure_le P _ (D.measurable_spectralRegularGraph n) _
    (D.measurableSet_spectralGoodImage good n)

theorem spectralGoodImage_failure_tendsto_zero {P : Measure Ω} [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (good : ℕ → Set Ω) (hgood : Tendsto (fun n => P.real (good n)ᶜ) atTop (nhds 0)) :
    Tendsto (fun n => (regularGraphLaw (N n) d).real (D.spectralGoodImage good n)ᶜ) atTop (nhds 0) :=
  squeeze_zero (fun n => measureReal_nonneg) (D.spectralGoodImage_failure_le hUniform good) hgood

theorem property_on_spectralGoodImage (good : ℕ → Set Ω) (n : ℕ) (Q : RegularGraph (N n) d → Prop)
    (hQ : ∀ ω ∈ good n,Q (D.spectralRegularGraph n ω)) :
    ∀ G ∈ D.spectralGoodImage good n,Q G := by
  rintro G ⟨ω,hω,rfl⟩
  exact hQ ω hω

end GeneralizedBulk.External.RegularSpectralData
