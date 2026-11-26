import GeneralizedBulk.Parameters
import GeneralizedBulk.Loop.Hierarchy
import GeneralizedBulk.MarkedResponse

/-!
# Generalized identification from marked response identities

These generic identification lemmas use the closed-form positive coefficient
of the two-parameter model. Their analytic response identities are constructed
from the Gaussian marked series and exterior symmetry in downstream modules.

The article's uniform-graph convergence theorem, with all BS and HY estimates
constructed internally, is `Graph.uniform_regular_graph_bulk_universality`
in `ProvedRegularGraphUniversality`. This module remains the reusable generic
response layer of that completed proof.
-/

noncomputable section
open MeasureTheory BourgadeHuang

namespace GeneralizedBulk

/-- The actual Sine-one law provided by the imported characterization library. -/
def sineOneLaw : Measure LocalCountingMeasure :=
  RationalBulk.sineBetaLaw (1 : ℚ) (by norm_num)

/-- Once the marked-response identities have been proved, the generalized
coefficient cannot vanish and the existing loop characterization identifies
the counting law. No loop hierarchy or target-law equality is assumed. -/
theorem identify_of_product_response
    (parameters : Parameters)
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (P : Measure S) [IsProbabilityMeasure P]
    (Q : Measure T) [IsProbabilityMeasure Q]
    (X : S → AnchoredCountingState) (hX : Measurable X)
    (hm : ∀ q : ℕ, Integrable (fun x => ‖(X x).val.2‖ ^ q) P)
    (h dh ds : ℂ → S → T → ℂ)
    (response : Loop.ProductResponseIdentities P Q X
      (parameters.contractionCoefficient : ℂ) h dh ds) :
    Measure.map (fun x => (X x).val.1) P = sineOneLaw := by
  have hκ : (parameters.contractionCoefficient : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt parameters.contractionCoefficient_pos
  exact response.countingLaw_eq_sineOne hκ hX hm

/-- A more concrete endpoint: the two trace contractions are proved from
entrywise Wick covariance, including the spectral-derivative slot. Only the
raw integrability and stationary polynomial response remain flow premises. -/
theorem identify_of_wick_and_stationary_response
    (parameters : Parameters)
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (P : Measure S) [IsProbabilityMeasure P]
    (Q : Measure T) [IsProbabilityMeasure Q]
    (X : S → AnchoredCountingState) (hX : Measurable X)
    (hm : ∀ q : ℕ, Integrable (fun x => ‖(X x).val.2‖ ^ q) P)
    (kernel : S → Marked.SpectralSlot → Marked.SpectralSlot → ℂ)
    (Z : S → Marked.SpectralSlot → T → EndpointMatrix)
    (wick : Marked.WickFiberData P Q parameters X kernel Z)
    (flow : Marked.StationaryWeightedResponse P Q parameters X Z) :
    Measure.map (fun x => (X x).val.1) P = sineOneLaw := by
  exact identify_of_product_response parameters P Q X hX hm _ _ _
    (Marked.productResponseIdentities P Q parameters X kernel Z wick flow)

end GeneralizedBulk
