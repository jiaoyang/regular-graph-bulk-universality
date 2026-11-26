import GaussianWave.BS.SteinFactorization
import GaussianWave.BS.RootStationarity
import GaussianWave.BS.EqualityAlongHeat
import GaussianWave.BS.GaussianEntropyWitness

/-!
# Gaussian equality case of the scalar BS entropy upper bound

Zero Fisher defect gives actual score constraints, actual smooth log-density
rigidity, and a proved Stein characteristic factorization. Edge reversal then
forces Gaussian root stationarity; all transverse characteristic directions
reconstruct the full heated Gaussian law. Actual Gaussian deconvolution
recovers the original law. No Gaussianity or rigidity premise remains.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace GaussianWave.BS

theorem star_eq_standardVector_of_fisherDefect_zero
    (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := Fin d)) μ) (hmom : HasIdentitySecondMoments μ)
    {t : ℝ} (ht : 0 < t)
    (hrev : ∀ i, Measure.map binarySwap
      (Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ) =
        Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ)
    (hzero : heatFrameFisherDefect μ (starEdgeProjection d c) t = 0)
    (hperm : ∀ p : Equiv.Perm (Fin d),
      Measure.map (fun x : Fin d → ℝ => fun j => x (p j)) μ = μ) :
    μ = standardVector (Fin d) := by
  let v := heatVariance (t + 1 / 2)
  have hv : (v : ℝ) = 1 + 2 * t := by
    change max (2 * (t + 1 / 2)) 0 = 1 + 2 * t
    rw [max_eq_left (by linarith)]
    ring
  have hfactor : ∀ w : Fin d → ℝ, (∑ j, w j = 0) → squareRadius w = 1 → ∀ a s : ℝ,
      characteristicIntegral (heatedLaw μ t) (a • starRootDirection d + s • w) =
        scalarCharacteristic (Measure.map starRootForm (heatedLaw μ t)) a *
          Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * (v : ℝ) * s ^ 2)) := by
    intro w hw hunit a s
    have h := star_characteristic_transverse_factorization_of_fisherDefect_zero
      d hd c hbulk μ hμ hmom ht hrev hzero hperm w hw hunit a s
    rw [h]
    unfold scalarCharacteristic
    congr 1
    congr 1
    rw [hv]
    push_cast
    ring
  let i₀ : Fin d := ⟨0, by omega⟩
  have hheated := star_heated_gaussian_of_transverse_characteristics_and_reversal
    d (by omega) μ t v c (bulk_rho_lower d hd c hbulk).1 i₀ hfactor (hrev i₀)
  have htime : (v : ℝ) / 2 = t + 1 / 2 := by rw [hv]; ring
  rw [htime] at hheated
  exact eq_standardVector_of_heatedLaw_eq_heatGaussian μ ht hheated

/-- The strict-bulk Gaussian equality case of the actual BS upper inequality.
The only assumptions are the source's moment, entropy, and symmetry data. -/
theorem star_entropy_equality_iff_standardVector
    (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hmom : HasIdentitySecondMoments μ)
    (f : FiniteEntropyDensity μ)
    (g : ∀ i, FiniteEntropyDensity
      (Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ))
    (hrev : ∀ i, Measure.map binarySwap
      (Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ) =
        Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ)
    (hperm : ∀ p : Equiv.Perm (Fin d),
      Measure.map (fun x : Fin d → ℝ => fun j => x (p j)) μ = μ) :
    initialFrameEntropy f g = 0 ↔ μ = standardVector (Fin d) := by
  constructor
  · intro hequality
    have hμ := integrable_squareRadius_of_identitySecondMoments μ hmom
    have hzero := (star_entropy_equality_heat_and_fisher_zero d hd c hbulk μ hμ hmom f g hrev
      hequality 1 zero_lt_one).2
    exact star_eq_standardVector_of_fisherDefect_zero d hd c hbulk μ hμ hmom zero_lt_one hrev hzero hperm
  · intro hμ
    subst μ
    exact star_initialFrameEntropy_standardVector_eq_zero d (by omega) c
      (bulk_rho_lower d hd c hbulk).1 f g

/-- The regularized form needs no entropy or density hypothesis on the
original law. Equality at any one positive heat time already forces the
original actual Gaussian law. -/
theorem star_eq_standardVector_of_heated_entropy_zero
    (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hmom : HasIdentitySecondMoments μ)
    (hrev : ∀ i, Measure.map binarySwap
      (Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ) =
        Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ)
    (hperm : ∀ p : Equiv.Perm (Fin d),
      Measure.map (fun x : Fin d → ℝ => fun j => x (p j)) μ = μ)
    {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hequality : heatFrameEntropy μ (starEdgeProjection d c) t₀ = 0) :
    μ = standardVector (Fin d) := by
  have hμ := integrable_squareRadius_of_identitySecondMoments μ hmom
  have hmono := star_heatFrameEntropy_monotone d hd c hbulk μ hμ hrev
  have hconst (u : ℝ) (hu : t₀ < u) : heatFrameEntropy μ (starEdgeProjection d c) u = 0 := by
    apply le_antisymm (star_heatFrameEntropy_nonpos d hd c hbulk μ hmom hrev (ht₀.trans hu))
    rw [← hequality]
    exact hmono ht₀ (ht₀.trans hu) hu.le
  have hu : 0 < t₀ + 1 := by linarith
  have heq : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 (t₀ + 1)] heatFrameEntropy μ (starEdgeProjection d c) := by
    filter_upwards [eventually_gt_nhds (by linarith : t₀ < t₀ + 1)] with u hu'
    exact (hconst u hu').symm
  have hzero := ((hasDerivAt_heatFrameEntropy μ hμ (starEdgeProjection d c) hu).congr_of_eventuallyEq heq).unique
    (hasDerivAt_const (t₀ + 1) 0)
  exact star_eq_standardVector_of_fisherDefect_zero d hd c hbulk μ hμ hmom hu hrev hzero hperm

theorem star_heated_entropy_equality_iff_standardVector
    (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hmom : HasIdentitySecondMoments μ)
    (hrev : ∀ i, Measure.map binarySwap
      (Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ) =
        Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ)
    (hperm : ∀ p : Equiv.Perm (Fin d),
      Measure.map (fun x : Fin d → ℝ => fun j => x (p j)) μ = μ)
    {t : ℝ} (ht : 0 < t) :
    heatFrameEntropy μ (starEdgeProjection d c) t = 0 ↔ μ = standardVector (Fin d) := by
  constructor
  · exact star_eq_standardVector_of_heated_entropy_zero d hd c hbulk μ hmom hrev hperm ht
  · intro hμ
    subst μ
    let f := standardVectorEntropyDensity (Fin d)
    let g := fun i : Fin d => (standardVectorEntropyDensity Bool).cast
      (standardVector_starEdgeProjection d (by omega) c (bulk_rho_lower d hd c hbulk).1 i)
    exact (star_entropy_equality_heat_and_fisher_zero d hd c hbulk _
      (integrable_squareRadius_of_identitySecondMoments _ hmom) hmom f g hrev
      (star_initialFrameEntropy_standardVector_eq_zero d (by omega) c
        (bulk_rho_lower d hd c hbulk).1 f g) t ht).1

end GaussianWave.BS
