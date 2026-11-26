import BourgadeHuang.RationalEdge.PhysicalGaugeBounds
import BourgadeHuang.RationalEdge.LawDetermination

/-! Transport of actual normalized-observable germs back to the original
charged expectations. The Airy coordinate has an actual local inverse on
the physical chamber, and its full WKB gauge is everywhere nonzero. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set Filter
namespace BourgadeHuang.RationalEdge
open RationalBulk EdgeCMS CMS

theorem blockAnchors_eq_reflect {n m : ℕ} (theta : Fin n → Bool) (eta : Fin m → Bool) :
    blockAnchors theta eta = fun i => reflectComplex (Fin.append theta eta i) Complex.I := by
  rw [blockAnchors_eq_signAnchor]
  funext i
  cases hs : Fin.append theta eta i <;> simp [signAnchor,signValue,reflectComplex,hs]

theorem eventually_airyInverseCoordinates_airyCoordinates {d : ℕ} {z : Point d}
    (hz : ∀ i, 0<(z i).re) :
    ∀ᶠ w in 𝓝 z, airyInverseCoordinates (airyCoordinates w)=w := by
  have hpos : ∀i, ∀ᶠw in 𝓝 z, 0<(w i).re := by
    intro i
    exact ((Complex.continuous_re.comp (continuous_apply i)).continuousAt)
      (Ioi_mem_nhds (hz i))
  filter_upwards [Filter.eventually_all.mpr hpos] with w hw
  exact airyInverseCoordinates_coordinates hw

private theorem airyCoordinates_tendsto_inverse {d : ℕ}
    {c : Fin d → ℂ} {upper : Fin d → Bool} {y : Point d}
    (hy : y∈physicalChamberSet c upper) :
    Tendsto airyCoordinates (𝓝 (airyInverseCoordinates y)) (𝓝 y) := by
  have hco := airyCoordinates_inverseCoordinates
    (fun i => Complex.slitPlane_ne_zero (hy.1 i).1.1)
  have hc := (analyticAt_airyCoordinates
    (fun i => airyInverse_mem_slitPlane (y i))).continuousAt
  change Tendsto airyCoordinates (𝓝 (airyInverseCoordinates y))
    (𝓝 (airyCoordinates (airyInverseCoordinates y))) at hc
  rwa [hco] at hc

/-- A proportionality of normalized germs gives proportionality of the
actual charged expectations at the corresponding physical point. -/
theorem charged_germ_proportional_of_normalized {d : ℕ}
    (μ ν : Measure AnchoredCountingState) (β : ℂ)
    (c : Fin d → ℂ) (upper : Fin d → Bool) (a : ℂ)
    {y : Point d} (hy : y∈physicalChamberSet c upper)
    (he : physicalNormalizedObservable μ β c upper =ᶠ[𝓝 y]
      fun v => a*physicalNormalizedObservable ν β c upper v) :
    expectedChargedObservable μ c (fun i => reflectComplex (upper i) Complex.I) =ᶠ[𝓝 (airyInverseCoordinates y)]
      fun z => a*expectedChargedObservable ν c (fun i => reflectComplex (upper i) Complex.I) z := by
  have hp := (airyCoordinates_tendsto_inverse hy).eventually he
  have hi := eventually_airyInverseCoordinates_airyCoordinates
    (fun i => (hy.1 i).1.2.1)
  filter_upwards [hp,hi] with z hz hzInv
  dsimp only [physicalNormalizedObservable] at hz
  rw [hzInv] at hz
  have hg := physicalGauge_ne_zero β c z
  have hm := congrArg (fun w : ℂ => w*physicalGauge β c z) hz
  simpa only [mul_assoc,div_mul_cancel₀ _ hg] using hm

/-- Vanishing of the normalized germ implies vanishing of the genuine
unnormalized charged expectation, by the same invertible coordinate change. -/
theorem charged_germ_zero_of_normalized {d : ℕ}
    (ν : Measure AnchoredCountingState) (β : ℂ)
    (c : Fin d → ℂ) (upper : Fin d → Bool)
    {y : Point d} (hy : y∈physicalChamberSet c upper)
    (he : physicalNormalizedObservable ν β c upper =ᶠ[𝓝 y] 0) :
    expectedChargedObservable ν c (fun i => reflectComplex (upper i) Complex.I) =ᶠ[𝓝 (airyInverseCoordinates y)] 0 := by
  have hp : physicalNormalizedObservable ν β c upper =ᶠ[𝓝 y]
      fun v => (0:ℂ)*physicalNormalizedObservable ν β c upper v := by
    simpa only [zero_mul] using he
  simpa only [zero_mul] using charged_germ_proportional_of_normalized ν ν β c upper 0 hy hp

/-- The normalized observable of a probability law cannot have zero germ:
analytic continuation of its genuine charged expectation would contradict
the exact value one at its integration bases. -/
theorem physicalNormalizedObservable_not_eventually_zero {n m : ℕ}
    (ν : ProbabilityMeasure AnchoredCountingState) (β : ℝ)
    {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2))
      (ν : Measure AnchoredCountingState))
    (theta : Fin n → Bool) (eta : Fin m → Bool)
    {y : Point (n+m)}
    (hy : y∈physicalChamberSet (charges β n m) (Fin.append theta eta))
    (hyden : airyInverseCoordinates y ∈ denominatorDomain n eta) :
    ¬ physicalNormalizedObservable (ν : Measure AnchoredCountingState) (β:ℂ)
      (charges β n m) (Fin.append theta eta) =ᶠ[𝓝 y] 0 := by
  intro hz
  have hzero := charged_germ_zero_of_normalized (ν : Measure AnchoredCountingState) (β:ℂ)
    (charges β n m) (Fin.append theta eta) hy hz
  rw [← blockAnchors_eq_reflect theta eta] at hzero
  have hzero' : expectedChargedObservable (ν : Measure AnchoredCountingState)
      (charges β n m) (blockAnchors theta eta) =ᶠ[𝓝 (airyInverseCoordinates y)]
      fun z => (0:ℂ)*expectedChargedObservable (ν : Measure AnchoredCountingState)
        (charges β n m) (blockAnchors theta eta) z := by
    simpa only [zero_mul] using hzero
  have h := charged_proportionality_scalar_eq_one ν ν ha ha he he β theta eta 0 hyden hzero'
  exact zero_ne_one h

/-- Specialized transport in the standard numerator/denominator block
notation used by rational replication and law determination. -/
theorem charged_block_germ_proportional_of_normalized {n m : ℕ}
    (μ ν : Measure AnchoredCountingState) (β : ℝ)
    (theta : Fin n → Bool) (eta : Fin m → Bool) (a : ℂ)
    {y : Point (n+m)}
    (hy : y∈physicalChamberSet (charges β n m) (Fin.append theta eta))
    (he : physicalNormalizedObservable μ (β:ℂ) (charges β n m) (Fin.append theta eta) =ᶠ[𝓝 y]
      fun v => a*physicalNormalizedObservable ν (β:ℂ) (charges β n m) (Fin.append theta eta) v) :
    expectedChargedObservable μ (charges β n m) (blockAnchors theta eta) =ᶠ[𝓝 (airyInverseCoordinates y)]
      fun z => a*expectedChargedObservable ν (charges β n m) (blockAnchors theta eta) z := by
  rw [blockAnchors_eq_reflect theta eta]
  exact charged_germ_proportional_of_normalized μ ν (β:ℂ) (charges β n m)
    (Fin.append theta eta) a hy he

end BourgadeHuang.RationalEdge
