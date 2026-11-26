import GeneralizedBulk.Gaussian.StratifiedHeightVariance
import GeneralizedBulk.Matrix.ResidualExpectation
import GeneralizedBulk.Matrix.MeanBounds
import GeneralizedBulk.Analysis.SquarePerturbation
import GeneralizedBulk.Analysis.InfiniteMass

/-!
Inverse-free normalization of the actual mixed Gaussian marked law.

The switched coupling may be correlated. Only its two genuine scalar/matrix
marginals, the literal finite-switch identity, and the rank trace shift are
used. Finite counting-mass strata are retained until normalization excludes
them at the end.
-/
noncomputable section
open MeasureTheory BourgadeHuang Filter ProbabilityTheory
open scoped Topology ENNReal
namespace GeneralizedBulk.Gaussian
open Counting Analysis Graph GeneralizedSwitching Exterior

def normalizationHeight (n : ℕ) : ℂ := ((((n : ℝ) + 1 : ℝ) : ℂ) * Complex.I)

theorem normalizationHeight_im_pos (n : ℕ) : 0 < (normalizationHeight n).im := by
  simp [normalizationHeight]
  positivity

def massRawHeight (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (parameters : Parameters) (n : ℕ) (z : MassMarkedSample ν) : ℂ × Mat :=
  (anchoredNevanlinna (massScalarState ν z) (normalizationHeight n),
    massMarkedMatrix ν hm parameters (normalizationHeight n) z)

theorem continuous_calibratedMean (parameters : Parameters) : Continuous (calibratedMean parameters) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> norm_num [calibratedMean,meanMatrix] <;> fun_prop

theorem measurable_massRawHeight
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (parameters : Parameters) (n : ℕ) : Measurable (massRawHeight ν hm parameters n) := by
  have hs : Measurable (fun z => anchoredNevanlinna (massScalarState ν z) (normalizationHeight n)) :=
    (continuous_anchoredNevanlinna (ne_of_gt (normalizationHeight_im_pos n))).measurable.comp
      (measurable_massScalarState ν)
  exact hs.prodMk (((continuous_calibratedMean parameters).measurable.comp hs).add
    (measurable_massCenteredField ν hm parameters (normalizationHeight n,false)))

/-- The scalar/matrix marginals are the actual mixed Gaussian construction,
not an assumed stationary response or normalization conclusion. -/
theorem mass_normalization_of_inverse_free_switched_coupling
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (parameters : Parameters)
    (C1 C2 : ℝ) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hheight1 : ∀ n : ℕ, (∫ s : AnchoredCountingState,
      ‖anchoredNevanlinna s (normalizationHeight n)‖ ∂ν) ≤ C1)
    (hiheight2 : ∀ n : ℕ, Integrable (fun s : AnchoredCountingState =>
      ‖anchoredNevanlinna s (normalizationHeight n)‖ ^ 2) ν)
    (hheight2 : ∀ n : ℕ, (∫ s : AnchoredCountingState,
      ‖anchoredNevanlinna s (normalizationHeight n)‖ ^ 2 ∂ν) ≤ C2)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s t : ℕ → Ω → ℂ) (M Mt : ℕ → Ω → Mat)
    (hforward : ∀ n, IdentDistrib (fun ω => (s n ω,M n ω))
      (massRawHeight ν hm parameters n) P (massMarkedLaw ν parameters))
    (hreverse : ∀ n, IdentDistrib (fun ω => (t n ω,Mt n ω))
      (massRawHeight ν hm parameters n) P (massMarkedLaw ν parameters))
    (b : ℕ → ℝ) (hb : Tendsto b atTop (𝓝 0))
    (hrank : ∀ n, ∀ᵐ ω ∂P, ‖t n ω - s n ω‖ ≤ b n)
    (hswitch : ∀ n, ∀ᵐ ω ∂P, (1 + M n ω * switchIncrement) *
      (endpointPermutation * Mt n ω * endpointPermutation) = M n ω) :
    Tendsto (fun n : ℕ => ∫ s : AnchoredCountingState,
      ‖anchoredNevanlinna s (normalizationHeight n) - Complex.I‖ ∂ν) atTop (𝓝 0) := by
  let x := fun n ω => entryEnvelope (M n ω - calibratedMean parameters (s n ω))
  let v := fun n ω => entryEnvelope (Mt n ω - calibratedMean parameters (t n ω))
  let y := fun n ω => v n ω + parameters.scale * b n
  let k := calibratedMeanEnvelope parameters
  let h := fun n ω => k * (1 + ‖s n ω‖)
  have hIdS (n : ℕ) : IdentDistrib (s n) (fun a : AnchoredCountingState =>
      anchoredNevanlinna a (normalizationHeight n)) P ν := by
    exact ((hforward n).comp measurable_fst).trans
      ((massScalarState_identDistrib ν parameters).comp
        (continuous_anchoredNevanlinna (ne_of_gt (normalizationHeight_im_pos n))).measurable)
  have hres : Measurable (fun z : ℂ × Mat => entryEnvelope (z.2 - calibratedMean parameters z.1)) :=
    (continuous_entryEnvelope.comp
      (continuous_snd.sub ((continuous_calibratedMean parameters).comp continuous_fst))).measurable
  have hIdX (n : ℕ) : IdentDistrib (x n)
      (fun z => entryEnvelope (massCenteredField ν hm parameters (normalizationHeight n,false) z))
        P (massMarkedLaw ν parameters) := by
    simpa only [Function.comp_def,massRawHeight,x,massMarkedMatrix,Marked.mean,calibratedMean,
      add_sub_cancel_left,id_eq] using (hforward n).comp hres
  have hIdV (n : ℕ) : IdentDistrib (v n)
      (fun z => entryEnvelope (massCenteredField ν hm parameters (normalizationHeight n,false) z))
        P (massMarkedLaw ν parameters) := by
    simpa only [Function.comp_def,massRawHeight,v,massMarkedMatrix,Marked.mean,calibratedMean,
      add_sub_cancel_left,id_eq] using (hreverse n).comp hres
  have hx (n) : AEStronglyMeasurable (x n) P := (hIdX n).aestronglyMeasurable_fst
  have hv (n) : AEStronglyMeasurable (v n) P := (hIdV n).aestronglyMeasurable_fst
  have hs (n) : AEStronglyMeasurable (s n) P := (hIdS n).aestronglyMeasurable_fst
  have hh (n) : AEStronglyMeasurable (h n) P :=
    ((hs n).norm.const_add 1).const_mul k
  have hy (n) : AEStronglyMeasurable (y n) P := (hv n).add_const _
  have hs2 (n) : Integrable (fun ω => ‖s n ω‖ ^ 2) P :=
    ((hIdS n).norm.pow).symm.integrable_snd (hiheight2 n)
  have hx2 (n) : Integrable (fun ω => x n ω ^ 2) P :=
    ((hIdX n).pow).symm.integrable_snd
      (massCenteredField_entryEnvelope_square_integrable_upper ν hm parameters
        (normalizationHeight_im_pos n))
  have hv2 (n) : Integrable (fun ω => v n ω ^ 2) P :=
    ((hIdV n).pow).symm.integrable_snd
      (massCenteredField_entryEnvelope_square_integrable_upper ν hm parameters
        (normalizationHeight_im_pos n))
  have hy2 (n) : Integrable (fun ω => y n ω ^ 2) P :=
    integrable_square_add_const P (v n) (hv n) (hv2 n) _
  have hZzero := massCenteredField_entryEnvelope_square_tendsto_zero ν hm parameters
    C1 hC1 hheight1
  have hxzero : Tendsto (fun n => ∫ ω, x n ω ^ 2 ∂P) atTop (𝓝 0) := by
    convert hZzero using 1
    funext n
    exact ((hIdX n).pow).integral_eq
  have hvzero : Tendsto (fun n => ∫ ω, v n ω ^ 2 ∂P) atTop (𝓝 0) := by
    convert hZzero using 1
    funext n
    exact ((hIdV n).pow).integral_eq
  have hyzero : Tendsto (fun n => ∫ ω, y n ω ^ 2 ∂P) atTop (𝓝 0) :=
    integral_square_add_const_tendsto_zero P v hv hv2 hvzero
      (fun n => parameters.scale * b n) (by simpa using hb.const_mul parameters.scale)
  have hh2 (n) : Integrable (fun ω => h n ω ^ 2) P := by
    have hi := (integrable_square_add_const P (fun ω => ‖s n ω‖) (hs n).norm (hs2 n) 1).const_mul (k ^ 2)
    convert hi using 1
    funext ω
    dsimp [h]
    ring
  have hmean (n) : (∫ ω, h n ω ^ 2 ∂P) ≤ 2 * k ^ 2 * (1 + C2) := by
    have hp (ω) : h n ω ^ 2 ≤ 2 * k ^ 2 + (2 * k ^ 2) * ‖s n ω‖ ^ 2 := by
      dsimp [h]
      nlinarith [sq_nonneg (k * (‖s n ω‖ - 1))]
    have hi := integral_mono (hh2 n) ((integrable_const _).add ((hs2 n).const_mul _)) hp
    simp only [Pi.add_apply] at hi
    rw [integral_add (integrable_const _) ((hs2 n).const_mul _),integral_const_mul,
      integral_const,measureReal_univ_eq_one,one_smul] at hi
    rw [integral_const_mul] at hi
    have hS : (∫ ω, ‖s n ω‖ ^ 2 ∂P) ≤ C2 :=
      (((hIdS n).norm.pow).integral_eq).trans_le (hheight2 n)
    nlinarith [mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ 2 * k ^ 2)]
  have hH (n) : ∀ᵐ ω ∂P, EntryBound (calibratedMean parameters (s n ω)) (h n ω) :=
    Eventually.of_forall (fun ω => calibratedMean_entryBound parameters (s n ω))
  have hX (n) : ∀ᵐ ω ∂P, EntryBound (M n ω - calibratedMean parameters (s n ω)) (x n ω) :=
    Eventually.of_forall (fun ω => entryEnvelope_bound _)
  have hY (n) : ∀ᵐ ω ∂P, EntryBound
      (endpointPermutation * (Mt n ω - calibratedMean parameters (s n ω)) * endpointPermutation)
      (y n ω) := by
    filter_upwards [hrank n] with ω hω
    have heq : Mt n ω - calibratedMean parameters (s n ω) =
        (Mt n ω - calibratedMean parameters (t n ω)) +
          (calibratedMean parameters (t n ω) - calibratedMean parameters (s n ω)) := by abel
    rw [heq]
    exact ((entryEnvelope_bound _).add
      ((calibratedMean_sub_entryBound parameters (s n ω) (t n ω)).mono
        (mul_le_mul_of_nonneg_left hω parameters.scale_pos.le))).conjugate
  have hupper (n) : ∀ᵐ ω ∂P, 0 ≤ (s n ω).im := by
    apply (hIdS n).symm.ae_snd
      (measurableSet_le measurable_const Complex.measurable_im)
    exact Eventually.of_forall (fun a => anchoredNevanlinna_im_nonneg a (normalizationHeight_im_pos n))
  have hn := normalization_of_inverse_free_switching_and_second_moments P parameters s hs hupper
    hs2 M Mt h x y hh hx hy hH hX hY hswitch hh2 hx2 hy2 hxzero hyzero
    (2 * k ^ 2 * (1 + C2)) (by positivity) hmean
  convert hn using 1
  funext n
  exact (((hIdS n).comp (measurable_id.sub_const Complex.I)).norm).integral_eq.symm

/-- Infinite mass is a consequence of the actual inverse-free switched
coupling and scalar height moments, rather than an upstream premise of the
Gaussian series construction. -/
theorem infinite_mass_of_inverse_free_switched_coupling
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (parameters : Parameters)
    (C1 C2 : ℝ) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hheight1 : ∀ n : ℕ, (∫ s : AnchoredCountingState,
      ‖anchoredNevanlinna s (normalizationHeight n)‖ ∂ν) ≤ C1)
    (hiheight2 : ∀ n : ℕ, Integrable (fun s : AnchoredCountingState =>
      ‖anchoredNevanlinna s (normalizationHeight n)‖ ^ 2) ν)
    (hheight2 : ∀ n : ℕ, (∫ s : AnchoredCountingState,
      ‖anchoredNevanlinna s (normalizationHeight n)‖ ^ 2 ∂ν) ≤ C2)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s t : ℕ → Ω → ℂ) (M Mt : ℕ → Ω → Mat)
    (hforward : ∀ n, IdentDistrib (fun ω => (s n ω,M n ω))
      (massRawHeight ν hm parameters n) P (massMarkedLaw ν parameters))
    (hreverse : ∀ n, IdentDistrib (fun ω => (t n ω,Mt n ω))
      (massRawHeight ν hm parameters n) P (massMarkedLaw ν parameters))
    (b : ℕ → ℝ) (hb : Tendsto b atTop (𝓝 0))
    (hrank : ∀ n, ∀ᵐ ω ∂P, ‖t n ω - s n ω‖ ≤ b n)
    (hswitch : ∀ n, ∀ᵐ ω ∂P, (1 + M n ω * switchIncrement) *
      (endpointPermutation * Mt n ω * endpointPermutation) = M n ω) :
    ∀ᵐ a ∂ν, a.val.1.measure Set.univ = ∞ := by
  apply anchored_totalMass_eq_top_ae_of_normalization ν hm
    (anchoredLinearCoefficient_eq_zero_ae_of_uniform_height ν id measurable_id hm C1 hheight1)
  exact mass_normalization_of_inverse_free_switched_coupling ν hm parameters C1 C2 hC1 hC2
    hheight1 hiheight2 hheight2 P s t M Mt hforward hreverse b hb hrank hswitch

end GeneralizedBulk.Gaussian
