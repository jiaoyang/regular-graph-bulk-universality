import GaussianWave.BS.EntropyEndpoint
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Entropy upper semicontinuity under strong density convergence

Fatou's lemma is applied to the nonnegative Gibbs integrand against a fixed
positive Gaussian reference. The hypotheses concern densities, genuine
integrability, convergence in measure, and their quadratic moments. No
entropy continuity conclusion is an assumption.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace GaussianWave.BS

/-- A real-valued Fatou bound with an eventual upper bound on the integrals.
The nonnegative integrands are converted to ENNReal only for Fatou's lemma. -/
theorem integral_le_of_ae_tendsto_nonneg
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    (q : ℕ → X → ℝ) (q₀ : X → ℝ)
    (hqi : ∀ n, Integrable (q n) m) (hq₀i : Integrable q₀ m)
    (hq0 : ∀ n x, 0 ≤ q n x) (hq₀0 : ∀ x, 0 ≤ q₀ x)
    (hlim : ∀ᵐ x ∂m, Tendsto (fun n => q n x) atTop (𝓝 (q₀ x)))
    {a : ℝ} (hbound : ∀ᶠ n in atTop, (∫ x, q n x ∂m) ≤ a) :
    (∫ x, q₀ x ∂m) ≤ a := by
  have hmeas (n : ℕ) : AEMeasurable (fun x => ENNReal.ofReal (q n x)) m :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable (hqi n).aestronglyMeasurable.aemeasurable
  have hfatou := lintegral_liminf_le' hmeas
  have heq : (fun x => liminf (fun n => ENNReal.ofReal (q n x)) atTop) =ᵐ[m]
      (fun x => ENNReal.ofReal (q₀ x)) := by
    filter_upwards [hlim] with x hx
    exact ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq
  rw [lintegral_congr_ae heq,
    ← ofReal_integral_eq_lintegral_ofReal hq₀i (ae_of_all _ hq₀0)] at hfatou
  have hbound' : ∀ᶠ n in atTop,
      (∫⁻ x, ENNReal.ofReal (q n x) ∂m) ≤ ENNReal.ofReal a := by
    filter_upwards [hbound] with n hn
    rw [← ofReal_integral_eq_lintegral_ofReal (hqi n) (ae_of_all _ (hq0 n))]
    exact ENNReal.ofReal_le_ofReal hn
  have hle := hfatou.trans (liminf_le_of_frequently_le' hbound'.frequently)
  obtain ⟨n, hn⟩ := hbound.exists
  have ha : 0 ≤ a := (integral_nonneg (hq0 n)).trans hn
  exact (ENNReal.ofReal_le_ofReal_iff ha).mp hle

/-- Entropy upper semicontinuity, expressed as eventual strict upper bounds.
The reference density is fixed and its cross entropy converges. This general
form permits a Gaussian reference whose cross entropy is a quadratic moment. -/
theorem eventually_densityEntropy_lt_of_tendstoInMeasure
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    (f : ℕ → X → ℝ) (f₀ g : X → ℝ)
    (hf0 : ∀ n x, 0 ≤ f n x) (hf₀0 : ∀ x, 0 ≤ f₀ x) (hgpos : ∀ x, 0 < g x)
    (hfi : ∀ n, Integrable (f n) m) (hf₀i : Integrable f₀ m) (hgi : Integrable g m)
    (hf1 : ∀ n, (∫ x, f n x ∂m) = 1) (hf₀1 : (∫ x, f₀ x ∂m) = 1)
    (hg1 : (∫ x, g x ∂m) = 1)
    (hflog : ∀ n, Integrable (fun x => f n x * Real.log (f n x)) m)
    (hf₀log : Integrable (fun x => f₀ x * Real.log (f₀ x)) m)
    (hfcross : ∀ n, Integrable (fun x => f n x * Real.log (g x)) m)
    (hf₀cross : Integrable (fun x => f₀ x * Real.log (g x)) m)
    (hfm : TendstoInMeasure m f atTop f₀)
    (hcross : Tendsto (fun n => ∫ x, f n x * Real.log (g x) ∂m) atTop
      (𝓝 (∫ x, f₀ x * Real.log (g x) ∂m)))
    {b : ℝ} (hb : densityEntropy m f₀ < b) :
    ∀ᶠ n in atTop, densityEntropy m (f n) < b := by
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, b ≤ densityEntropy m (f n) := by
    simpa only [not_lt] using (not_eventually.mp hnot)
  obtain ⟨ns, hns, hnsb⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨ks, hks, hkae⟩ := (hfm.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  let r : ℕ → ℕ := fun n => ns (ks n)
  have hr : Tendsto r atTop atTop := hns.tendsto_atTop.comp hks.tendsto_atTop
  let q (p : X → ℝ) (x : X) :=
    p x * Real.log (p x) - p x * Real.log (g x) - p x + g x
  have hqi (n : ℕ) : Integrable (q (f (r n))) m :=
    (((hflog _).sub (hfcross _)).sub (hfi _)).add hgi
  have hq₀i : Integrable (q f₀) m :=
    ((hf₀log.sub hf₀cross).sub hf₀i).add hgi
  have hqint (p : X → ℝ) (hpi : Integrable p m)
      (hplog : Integrable (fun x => p x * Real.log (p x)) m)
      (hpcross : Integrable (fun x => p x * Real.log (g x)) m)
      (hp1 : (∫ x, p x ∂m) = 1) :
      (∫ x, q p x ∂m) = -densityEntropy m p - ∫ x, p x * Real.log (g x) ∂m := by
    rw [show (fun x => q p x) = (fun x =>
      p x * Real.log (p x) - p x * Real.log (g x) - p x + g x) from rfl,
      integral_add (f := fun x => p x * Real.log (p x) - p x * Real.log (g x) - p x)
        ((hplog.sub hpcross).sub hpi) hgi,
      integral_sub (f := fun x => p x * Real.log (p x) - p x * Real.log (g x))
        (hplog.sub hpcross) hpi,
      integral_sub (f := fun x => p x * Real.log (p x)) hplog hpcross, hp1, hg1]
    simp [densityEntropy]
  let c₀ := ∫ x, f₀ x * Real.log (g x) ∂m
  let a := -((densityEntropy m f₀ + b) / 2) - c₀
  have haeb : ∀ᶠ n in atTop, (∫ x, q (f (r n)) x ∂m) ≤ a := by
    have hsmall : c₀ - (b - densityEntropy m f₀) / 2 <
        ∫ x, f₀ x * Real.log (g x) ∂m := by dsimp [c₀]; linarith
    have he := (hcross.comp hr).eventually (lt_mem_nhds hsmall)
    filter_upwards [he] with n hn
    rw [hqint _ (hfi _) (hflog _) (hfcross _) (hf1 _)]
    have hb' : b ≤ densityEntropy m (f (r n)) := hnsb (ks n)
    dsimp [a, c₀] at *
    linarith
  have hqa : (∫ x, q f₀ x ∂m) ≤ a := by
    apply integral_le_of_ae_tendsto_nonneg m (fun n => q (f (r n))) (q f₀)
      hqi hq₀i
      (fun n x => gibbs_integrand_nonneg _ _ (hf0 _ _) (hgpos _))
      (fun x => gibbs_integrand_nonneg _ _ (hf₀0 _) (hgpos _)) _ haeb
    filter_upwards [hkae] with x hx
    exact (((Real.continuous_mul_log.continuousAt.tendsto.comp hx).sub
      (hx.mul_const (Real.log (g x)))).sub hx).add_const (g x)
  rw [hqint _ hf₀i hf₀log hf₀cross hf₀1] at hqa
  dsimp [a, c₀] at hqa
  linarith


/-- L1 distance convergence of genuine integrable real functions gives
convergence in measure, including on the infinite Lebesgue space. -/
theorem tendstoInMeasure_of_integral_abs_sub_tendsto_zero
    {X : Type*} [MeasurableSpace X] (m : Measure X)
    (f : ℕ → X → ℝ) (f₀ : X → ℝ)
    (hfi : ∀ n, Integrable (f n) m) (hf₀i : Integrable f₀ m)
    (hL1 : Tendsto (fun n => ∫ x, |f n x - f₀ x| ∂m) atTop (𝓝 0)) :
    TendstoInMeasure m f atTop f₀ := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := (1 : ℝ≥0∞)) one_ne_zero
    (fun n => (hfi n).aestronglyMeasurable) hf₀i.aestronglyMeasurable
  have heq (n : ℕ) : eLpNorm (f n - f₀) 1 m =
      ENNReal.ofReal (∫ x, |f n x - f₀ x| ∂m) := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hfi n).sub hf₀i)]
    rfl
  simp_rw [heq]
  simpa using (ENNReal.continuous_ofReal.tendsto 0).comp hL1

/-- Entropy upper semicontinuity from actual L1 density convergence and
convergence of the radial second moment. The fixed Gaussian reference and
its quadratic logarithm are supplied by the constructed heat kernel. -/
theorem eventually_densityEntropy_lt_of_L1_and_secondMoment
    {I : Type*} [Fintype I]
    (f : ℕ → (I → ℝ) → ℝ) (f₀ : (I → ℝ) → ℝ)
    (hf0 : ∀ n x, 0 ≤ f n x) (hf₀0 : ∀ x, 0 ≤ f₀ x)
    (hfi : ∀ n, Integrable (f n)) (hf₀i : Integrable f₀)
    (hf1 : ∀ n, (∫ x, f n x) = 1) (hf₀1 : (∫ x, f₀ x) = 1)
    (hflog : ∀ n, Integrable (fun x => f n x * Real.log (f n x)))
    (hf₀log : Integrable (fun x => f₀ x * Real.log (f₀ x)))
    (hfq : ∀ n, Integrable (fun x => f n x * squareRadius x))
    (hf₀q : Integrable (fun x => f₀ x * squareRadius x))
    (hL1 : Tendsto (fun n => ∫ x, |f n x - f₀ x|) atTop (𝓝 0))
    (hmoment : Tendsto (fun n => ∫ x, f n x * squareRadius x) atTop
      (𝓝 (∫ x, f₀ x * squareRadius x)))
    {b : ℝ} (hb : densityEntropy volume f₀ < b) :
    ∀ᶠ n in atTop, densityEntropy volume (f n) < b := by
  apply eventually_densityEntropy_lt_of_tendstoInMeasure volume f f₀ (heatKernel 1)
    hf0 hf₀0 (heatKernel_pos (by norm_num)) hfi hf₀i (integrable_heatKernel 1)
    hf1 hf₀1 (integral_heatKernel (by norm_num)) hflog hf₀log
    (fun n => integrable_cross_heatKernel (f n) (by norm_num) (hfi n) (hfq n))
    (integrable_cross_heatKernel f₀ (by norm_num) hf₀i hf₀q)
    (tendstoInMeasure_of_integral_abs_sub_tendsto_zero volume f f₀ hfi hf₀i hL1) _ hb
  have heq (p : (I → ℝ) → ℝ) (hpi : Integrable p)
      (hpq : Integrable (fun x => p x * squareRadius x)) (hp1 : (∫ x, p x) = 1) :
      (∫ x, p x * Real.log (heatKernel 1 x)) =
        -((Fintype.card I : ℝ) / 2 * Real.log (2 * Real.pi * (heatVariance 1 : ℝ)) +
          (∫ x, p x * squareRadius x) / (2 * (heatVariance 1 : ℝ))) := by
    linarith [crossEntropy_heatKernel p (by norm_num : (0 : ℝ) < 1) hpi hpq hp1]
  simp_rw [heq _ (hfi _) (hfq _) (hf1 _), heq _ hf₀i hf₀q hf₀1]
  exact (tendsto_const_nhds.add (hmoment.div_const _)).neg

end GaussianWave.BS
