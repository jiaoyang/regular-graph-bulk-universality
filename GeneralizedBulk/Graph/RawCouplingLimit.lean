import GeneralizedBulk.Graph.GraphObstruction
import GeneralizedBulk.Analysis.WeakRelations
import GeneralizedBulk.Matrix.EntryEnvelope

/-! Literal finite switched raw pairs and their inverse-free limiting laws. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.Graph
open Exterior GeneralizedSwitching Analysis

abbrev RawValue := ℂ × Mat
abbrev RawPair := RawValue × RawValue

def microscopicRawValue {N d : ℕ} (hN : 0 < N) (E sigma a : ℝ) (hsigma : 0 < sigma)
    (w : GraphNonreal) (s : EdgePairState N d) : RawValue :=
  (microscopicScalar s.val.1 hN E sigma a hsigma w,
    graphBoundary s.val.1 s.val.2 (microscopicParameter N hN E sigma hsigma w).val)

def microscopicRawPair {N d : ℕ} (hN : 0 < N) (E sigma a : ℝ) (hsigma : 0 < sigma)
    (w : GraphNonreal) (s : EdgePairState N d) : RawPair :=
  (microscopicRawValue hN E sigma a hsigma w s,
    microscopicRawValue hN E sigma a hsigma w (proposalSwitch s))

def microscopicRawLaw {N d : ℕ} (hN : 0 < N) (E sigma a : ℝ) (hsigma : 0 < sigma)
    (w : GraphNonreal) : Measure RawValue :=
  Measure.map (microscopicRawValue (d := d) hN E sigma a hsigma w) (edgePairLaw N d)

def microscopicRawPairLaw {N d : ℕ} (hN : 0 < N) (E sigma a : ℝ) (hsigma : 0 < sigma)
    (w : GraphNonreal) : Measure RawPair :=
  Measure.map (microscopicRawPair (d := d) hN E sigma a hsigma w) (edgePairLaw N d)

instance microscopicRawLaw_isProbability {N d : ℕ} [Nonempty (EdgePairState N d)]
    (hN : 0 < N) (E sigma a : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal) :
    IsProbabilityMeasure (microscopicRawLaw (d := d) hN E sigma a hsigma w) := by
  letI : IsProbabilityMeasure (edgePairLaw N d) := finiteUniform_isProbability _
  exact MeasureTheory.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

instance microscopicRawPairLaw_isProbability {N d : ℕ} [Nonempty (EdgePairState N d)]
    (hN : 0 < N) (E sigma a : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal) :
    IsProbabilityMeasure (microscopicRawPairLaw (d := d) hN E sigma a hsigma w) := by
  letI : IsProbabilityMeasure (edgePairLaw N d) := finiteUniform_isProbability _
  exact MeasureTheory.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

theorem microscopicRawPairLaw_fst {N d : ℕ} (hN : 0 < N)
    (E sigma a : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal) :
    Measure.map Prod.fst (microscopicRawPairLaw (d := d) hN E sigma a hsigma w) =
      microscopicRawLaw (d := d) hN E sigma a hsigma w := by
  rw [microscopicRawPairLaw,Measure.map_map measurable_fst (measurable_of_finite _)]
  rfl

theorem microscopicRawPairLaw_snd {N d : ℕ} (hN : 0 < N)
    (E sigma a : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal) :
    Measure.map Prod.snd (microscopicRawPairLaw (d := d) hN E sigma a hsigma w) =
      microscopicRawLaw (d := d) hN E sigma a hsigma w := by
  rw [microscopicRawPairLaw,Measure.map_map measurable_snd (measurable_of_finite _)]
  change Measure.map (microscopicRawValue hN E sigma a hsigma w ∘ proposalSwitch)
    (edgePairLaw N d) = _
  rw [← Measure.map_map (measurable_of_finite _) (measurable_of_finite _),edgePairLaw_switch_invariant]
  rfl

def rawPairSwitchResidual (x : RawPair) : Mat :=
  (1 + x.1.2 * switchIncrement) * (endpointPermutation * x.2.2 * endpointPermutation) - x.1.2

theorem continuous_rawPairSwitchResidual : Continuous rawPairSwitchResidual := by
  unfold rawPairSwitchResidual
  fun_prop

theorem microscopicRawPair_switch_failure_le_rejection {N d : ℕ}
    [Nonempty (EdgePairState N d)] (hN : 0 < N)
    (E sigma a : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal) :
    (microscopicRawPairLaw (d := d) hN E sigma a hsigma w).real
      {x | rawPairSwitchResidual x ≠ 0} ≤
      (edgePairLaw N d).real {s | ¬Accepted s} := by
  letI : IsProbabilityMeasure (edgePairLaw N d) := finiteUniform_isProbability _
  have hA : MeasurableSet {x : RawPair | rawPairSwitchResidual x ≠ 0} :=
    (isClosed_eq continuous_rawPairSwitchResidual continuous_const).measurableSet.compl
  rw [Measure.real,microscopicRawPairLaw,
    Measure.map_apply (measurable_of_finite _) hA]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro s hs ha
  apply hs
  apply sub_eq_zero.mpr
  exact proposalSwitch_compression_shift s ha _ (microscopicParameter N hN E sigma hsigma w).property

/-- The genuine finite compression identity survives rejection and weak
convergence as an almost-sure, inverse-free identity. -/
theorem microscopicRawPairLimit_inverse_free
    (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) (hNlimit : Tendsto N atTop atTop)
    (d : ℕ) (hd : 0 < d) [∀ n, Nonempty (RegularGraph (N n) d)]
    (E sigma a : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal)
    (ν : Measure RawPair) [IsProbabilityMeasure ν]
    (hweak : External.WeakLawConverges
      (fun n => microscopicRawPairLaw (d := d) (hN n) E sigma a hsigma w) ν) :
    ∀ᵐ x ∂ν, (1 + x.1.2 * switchIncrement) *
      (endpointPermutation * x.2.2 * endpointPermutation) = x.1.2 := by
  letI : ∀ n, Nonempty (EdgePairState (N n) d) := fun n => edgePairState_nonempty (hN n) hd
  have hf : Tendsto (fun n => (microscopicRawPairLaw (d := d) (hN n) E sigma a hsigma w).real
      {x | rawPairSwitchResidual x ≠ 0}) atTop (𝓝 0) := squeeze_zero
    (fun n => measureReal_nonneg)
    (fun n => microscopicRawPair_switch_failure_le_rejection (d := d) (hN n) E sigma a hsigma w)
    (edgePairLaw_rejection_tendsto_zero N hN hNlimit d hd)
  have hz : ∀ᵐ x ∂ν, entryEnvelope (rawPairSwitchResidual x) = 0 :=
    weak_limit_continuous_zero_of_failure_probability
      (fun n => microscopicRawPairLaw (d := d) (hN n) E sigma a hsigma w) ν hweak
      (fun x => entryEnvelope (rawPairSwitchResidual x))
      (continuous_entryEnvelope.comp continuous_rawPairSwitchResidual)
      (by simpa only [ne_eq,entryEnvelope_eq_zero_iff] using hf)
  filter_upwards [hz] with x hx
  exact sub_eq_zero.mp (entryEnvelope_eq_zero_iff _ |>.mp hx)

/-- The rank-two scalar shift also survives the same actual joint weak limit. -/
theorem microscopicRawPairLimit_rank_bound
    (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) (d : ℕ)
    [∀ n, Nonempty (EdgePairState (N n) d)]
    (E sigma a : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal)
    (ν : Measure RawPair) [IsProbabilityMeasure ν]
    (hweak : External.WeakLawConverges
      (fun n => microscopicRawPairLaw (d := d) (hN n) E sigma a hsigma w) ν) :
    ∀ᵐ x ∂ν, ‖x.2.1 - x.1.1‖ ≤ 4 / |w.val.im| := by
  apply weak_limit_continuous_le_of_failure_probability _ ν hweak
    (fun x => ‖x.2.1 - x.1.1‖)
    ((continuous_fst.comp continuous_snd).sub (continuous_fst.comp continuous_fst)).norm
    (4 / |w.val.im|)
  have hzero (n : ℕ) : (microscopicRawPairLaw (d := d) (hN n) E sigma a hsigma w)
      {x | 4 / |w.val.im| < ‖x.2.1 - x.1.1‖} = 0 := by
    have hA : MeasurableSet {x : RawPair | 4 / |w.val.im| < ‖x.2.1 - x.1.1‖} :=
      (isOpen_lt continuous_const
        ((continuous_fst.comp continuous_snd).sub (continuous_fst.comp continuous_fst)).norm).measurableSet
    rw [microscopicRawPairLaw,Measure.map_apply (measurable_of_finite _) hA]
    have he : microscopicRawPair (d := d) (hN n) E sigma a hsigma w ⁻¹'
        {x | 4 / |w.val.im| < ‖x.2.1 - x.1.1‖} = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro s hs
      exact not_lt_of_ge (microscopicScalar_proposalSwitch_bound s (hN n) E sigma a hsigma w) hs
    rw [he,measure_empty]
  simpa only [Measure.real,hzero,ENNReal.toReal_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem microscopicRawPairLimit_marginals
    (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) (d : ℕ)
    (E sigma a : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal)
    (ν : Measure RawPair) [IsFiniteMeasure ν] (ρ : Measure RawValue) [IsFiniteMeasure ρ]
    (hweak : External.WeakLawConverges
      (fun n => microscopicRawPairLaw (d := d) (hN n) E sigma a hsigma w) ν)
    (hmarginal : External.WeakLawConverges
      (fun n => microscopicRawLaw (d := d) (hN n) E sigma a hsigma w) ρ) :
    Measure.map Prod.fst ν = ρ ∧ Measure.map Prod.snd ν = ρ := by
  constructor
  · apply weak_limit_marginal_eq _ ν hweak Prod.fst continuous_fst ρ
    simpa only [microscopicRawPairLaw_fst] using hmarginal
  · apply weak_limit_marginal_eq _ ν hweak Prod.snd continuous_snd ρ
    simpa only [microscopicRawPairLaw_snd] using hmarginal

end GeneralizedBulk.Graph
