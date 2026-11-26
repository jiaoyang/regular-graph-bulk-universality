import BourgadeHuang.RationalEdge.PhysicalObservableBounds
import BourgadeHuang.EdgeCMS.PhysicalGaugeScaling

/-! Uniform bounds for the actual charged expectation divided by the complete
physical WKB gauge, including its root-pair prefactor. Neutral physical charges
make that prefactor invariant under dilation; its reciprocal is locally bounded
by analyticity and nonvanishing. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set Filter
namespace BourgadeHuang.RationalEdge
open RationalBulk EdgeCMS CMS

/-- Actual full WKB normalization, expressed in the Airy coordinates. -/
def physicalNormalizedObservable {d : ℕ} (ν : Measure AnchoredCountingState)
    (β : ℂ) (c : Fin d → ℂ) (upper : Fin d → Bool) (y : Point d) : ℂ :=
  expectedChargedObservable ν c (fun i => reflectComplex (upper i) Complex.I)
    (airyInverseCoordinates y) / physicalGauge β c (airyInverseCoordinates y)

theorem physicalNormalizedObservable_eq_phase {d : ℕ}
    (ν : Measure AnchoredCountingState) (β : ℂ) (c : Fin d → ℂ)
    (upper : Fin d → Bool) (y : Point d) :
    physicalNormalizedObservable ν β c upper y =
      airyPhaseNormalizedObservable ν c upper y *
        (physicalPrefactor β c (airyInverseCoordinates y))⁻¹ := by
  let z := airyInverseCoordinates y
  let E := expectedChargedObservable ν c (fun i => reflectComplex (upper i) Complex.I) z
  let P := physicalPrefactor β c z
  let A := physicalPhase c z
  change E / physicalGauge β c z = Complex.exp (-A) * E * P⁻¹
  rw [physicalGauge_factorization]
  change E / (Complex.exp A * P) = Complex.exp (-A) * E * P⁻¹
  rw [Complex.exp_neg]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem analyticAt_physicalPrefactor {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    {z : Point d} (hz : z ∈ PhysicalRootDomain d) :
    AnalyticAt ℂ (physicalPrefactor β c) z := by
  have hp : AnalyticAt ℂ (physicalPhase c) z := by
    unfold physicalPhase
    apply Finset.analyticAt_sum
    intro i hi
    exact analyticAt_const.mul ((analyticAt_airyCoordinate (hz i)).comp (f := fun w : Point d => w i)
      ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt z))
  exact ((analyticAt_physicalGaugeLog β c hz).sub hp).cexp

/-- In Airy coordinates the physical prefactor is exactly constant along
positive dilations, using the actual physical charge values and balance. -/
theorem physicalPrefactor_airy_dilation {d : ℕ} (β : ℂ) (hβ : β ≠ 0)
    (c : Fin d → ℂ) (hc : ∀ i, c i = -1 ∨ c i = β / 2)
    (hzero : ∑ i, c i = 0) {y : Point d} (hy : ∀ i, y i ≠ 0)
    {r : ℝ} (hr : 0 < r) :
    physicalPrefactor β c (airyInverseCoordinates ((r : ℂ) • y)) =
      physicalPrefactor β c (airyInverseCoordinates y) := by
  obtain ⟨u, hu, huc⟩ := exists_positive_cube_root hr
  have hucC : (u : ℂ)^3 = (r : ℂ) := by exact_mod_cast huc
  have hs : airyInverseCoordinates ((r : ℂ) • y) =
      fun i => (u : ℂ)^2 * airyInverseCoordinates y i := by
    funext i
    simp only [airyInverseCoordinates, Pi.smul_apply, smul_eq_mul]
    rw [← hucC, airyInverse_ofReal_cube_mul hu (hy i)]
  rw [hs]
  exact physicalPrefactor_scale_balanced β hβ c hc hzero
    (fun i => airyInverse_mem_slitPlane (y i)) hu

/-- The complete gauge-normalized expectation satisfies the boundedness
required by the finite scaled-jet argument on a genuine neighborhood in the
physical cone. This bound is derived from the edge hierarchy itself. -/
theorem physicalNormalizedObservable_local_dilation_bound
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν] (β : ℝ)
    (hβ : β ≠ 0) (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    {d : ℕ} (hd : 0 < d) (c : Fin d → ℂ) (upper : Fin d → Bool)
    (hc : ∀ i, c i = -1 ∨ c i = (β : ℂ) / 2)
    (hzero : ∑ i, c i = 0) (hsigned : ∑ i, c i * signValue (upper i) = 0)
    {y : Point d} (hy : y ∈ physicalChamberSet c upper) :
    ∃ (U : Set (Point d)) (C : ℝ), U ∈ 𝓝 y ∧ 0 < C ∧
      U ⊆ physicalChamberSet c upper ∧ ∀ v ∈ U, ∀ r : ℝ, 0 < r →
        ‖physicalNormalizedObservable ν (β : ℂ) c upper ((r : ℂ) • v)‖ ≤ C := by
  obtain ⟨U, C, hU, hC, hsub, hbound⟩ :=
    airyPhaseNormalizedObservable_local_dilation_bound ν β hh ha he hd c upper hzero hsigned hy
  let G : Point d → ℂ := fun v => (physicalPrefactor (β : ℂ) c (airyInverseCoordinates v))⁻¹
  have hG : ContinuousAt G y := by
    have hinv : AnalyticAt ℂ airyInverseCoordinates y :=
      analyticAt_airyInverseCoordinates (fun i => (hy.1 i).1.1)
    have hpf := (analyticAt_physicalPrefactor (β : ℂ) c
      (fun i => airyInverse_mem_slitPlane (y i))).comp hinv
    exact (hpf.inv (Complex.exp_ne_zero _)).continuousAt
  let V : Set (Point d) := {v | ‖G v‖ < ‖G y‖ + 1}
  have hV : V ∈ 𝓝 y := hG.norm (Iio_mem_nhds (lt_add_one _))
  refine ⟨U ∩ V, C * (‖G y‖ + 1), inter_mem hU hV,
    mul_pos hC (by positivity), fun v hv => hsub hv.1, ?_⟩
  intro v hv r hr
  have hp : (physicalPrefactor (β : ℂ) c (airyInverseCoordinates ((r : ℂ) • v)))⁻¹ = G v := by
    rw [physicalPrefactor_airy_dilation (β : ℂ) (by exact_mod_cast hβ) c hc hzero
      (fun i => Complex.slitPlane_ne_zero ((hsub hv.1).1 i).1.1) hr]
  rw [physicalNormalizedObservable_eq_phase, norm_mul, hp]
  exact mul_le_mul (hbound v hv.1 r hr) hv.2.le (norm_nonneg _) hC.le

end BourgadeHuang.RationalEdge
