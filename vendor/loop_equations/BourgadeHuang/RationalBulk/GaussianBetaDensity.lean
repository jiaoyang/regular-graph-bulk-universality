import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import BourgadeHuang.GaussianMoments
import Mathlib.Tactic

/-! Actual finite Gaussian beta ensemble, in microscopic bulk coordinates.
The density is with respect to Lebesgue measure on all labelled particles.
Every positive real beta is allowed, including beta below one. -/
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

/-- Each unordered pair occurs once. -/
def gaussianBetaPairs (N : ℕ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun p => p.1 < p.2

/-- Microscopic Gaussian beta density, before normalization. -/
def gaussianBetaDensity (β : ℝ) (N : ℕ) (x : Fin N → ℝ) : ℝ :=
  Real.exp (-(β / (4 * (N : ℝ))) * ∑ i, x i ^ 2) *
    ∏ p ∈ gaussianBetaPairs N, |x p.1 - x p.2| ^ β

/-- Its finite dimensional partition function. -/
def gaussianBetaPartition (β : ℝ) (N : ℕ) : ℝ :=
  ∫ x, gaussianBetaDensity β N x

/-- The actual probability measure, once beta and dimension are positive. -/
def gaussianBetaMeasure (β : ℝ) (N : ℕ) : Measure (Fin N → ℝ) :=
  (ENNReal.ofReal (gaussianBetaPartition β N))⁻¹ •
    (volume.withDensity fun x => ENNReal.ofReal (gaussianBetaDensity β N x))

theorem gaussianBetaDensity_nonneg (β : ℝ) (N : ℕ) (x : Fin N → ℝ) :
    0 ≤ gaussianBetaDensity β N x := by
  unfold gaussianBetaDensity
  positivity

theorem gaussianBetaDensity_continuous {β : ℝ} (hβ : 0 < β) (N : ℕ) :
    Continuous (gaussianBetaDensity β N) := by
  unfold gaussianBetaDensity
  apply Continuous.mul
  · fun_prop
  · apply continuous_finset_prod
    intro p hp
    exact ((continuous_apply p.1).sub (continuous_apply p.2)).abs.rpow_const
      (fun x => Or.inr hβ.le)

def coordinateEnvelope {N : ℕ} (x : Fin N → ℝ) : ℝ :=
  ∏ i, (1 + |x i|)

theorem coordinateEnvelope_one_le {N : ℕ} (x : Fin N → ℝ) :
    1 ≤ coordinateEnvelope x :=
  by
    unfold coordinateEnvelope
    calc
      1 = ∏ i : Fin N, (1:ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (by intros; norm_num)
        (by intro i hi; linarith [abs_nonneg (x i)])

theorem coordinateEnvelope_coordinate {N : ℕ} (x : Fin N → ℝ) (i : Fin N) :
    1 + |x i| ≤ coordinateEnvelope x :=
  by
    unfold coordinateEnvelope
    have hrest : (1:ℝ) ≤ ∏ j ∈ Finset.univ.erase i, (1+|x j|) := by
      calc
        1 = ∏ j ∈ Finset.univ.erase i, (1:ℝ) := by simp
        _ ≤ _ := Finset.prod_le_prod (by intros; norm_num)
          (by intro j hj; linarith [abs_nonneg (x j)])
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    exact le_mul_of_one_le_left (by positivity) hrest

theorem pair_rpow_le_envelope {β : ℝ} (hβ : 0 ≤ β) {m : ℕ}
    (hm : β ≤ m) {N : ℕ} (x : Fin N → ℝ) (i j : Fin N) :
    |x i - x j| ^ β ≤ coordinateEnvelope x ^ (2 * m) := by
  have hp := coordinateEnvelope_one_le x
  have hpi := coordinateEnvelope_coordinate x i
  have hpj := coordinateEnvelope_coordinate x j
  have hai := abs_nonneg (x i)
  have haj := abs_nonneg (x j)
  have ht : |x i - x j| ≤ coordinateEnvelope x ^ 2 := by
    calc
      _ ≤ |x i| + |x j| := abs_sub _ _
      _ ≤ (1 + |x i|) * (1 + |x j|) := by nlinarith [mul_nonneg hai haj]
      _ ≤ coordinateEnvelope x * coordinateEnvelope x :=
        mul_le_mul hpi hpj (by positivity) (by linarith)
      _ = _ := by ring
  calc
    _ ≤ (coordinateEnvelope x ^ 2) ^ β := Real.rpow_le_rpow (abs_nonneg _) ht hβ
    _ ≤ (coordinateEnvelope x ^ 2) ^ (m : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hp) hm
    _ = _ := by rw [Real.rpow_natCast, ← pow_mul]

theorem gaussian_polynomial_integrable {c : ℝ} (hc : 0 < c) (m : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|)^m * Real.exp (-c*x^2)) := by
  have h0 := integrable_exp_neg_mul_sq hc
  have hm : Integrable (fun x : ℝ => |x|^m * Real.exp (-c*x^2)) := by
    have h := (integrable_rpow_mul_exp_neg_mul_sq hc
      (s := (m : ℝ)) (by exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg m))).norm
    simpa only [Real.rpow_natCast, norm_mul, Real.norm_eq_abs, abs_pow,
      abs_of_pos (Real.exp_pos _)] using h
  refine ((h0.add hm).const_mul ((2:ℝ)^(m-1))).mono'
    (by exact (by fun_prop : Continuous (fun x : ℝ => (1 + |x|)^m * Real.exp (-c*x^2))).aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ ((2:ℝ)^(m-1) * (1^m + |x|^m)) * Real.exp (-c*x^2) :=
      mul_le_mul_of_nonneg_right (add_pow_le (by norm_num) (abs_nonneg x) m)
        (Real.exp_pos _).le
    _ = _ := by simp only [Pi.add_apply, one_pow]; ring

/-- Polynomial coordinate weights times the density are integrable. -/
theorem gaussianBetaDensity_envelope_integrable {β : ℝ} (hβ : 0 < β)
    {N : ℕ} (hN : 0 < N) (q : ℕ) :
    Integrable (fun x : Fin N → ℝ => (∏ i, (1+|x i|))^q * gaussianBetaDensity β N x) := by
  obtain ⟨m, hm⟩ := exists_nat_ge β
  let d := 2*m*(gaussianBetaPairs N).card
  let c := β / (4 * (N : ℝ))
  have hc : 0 < c := by dsimp [c]; positivity
  have hI : Integrable (fun x : Fin N → ℝ =>
      ∏ i, ((1+|x i|)^(q+d) * Real.exp (-c*x i^2))) :=
    Integrable.fintype_prod fun _ => gaussian_polynomial_integrable hc (q+d)
  refine hI.mono' (by
    exact ((continuous_finset_prod _ (fun i _ =>
      (continuous_const.add (continuous_apply i).abs))).pow q).mul
      (gaussianBetaDensity_continuous hβ N) |>.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  have he := coordinateEnvelope_one_le x
  have hb : (∏ p ∈ gaussianBetaPairs N, |x p.1-x p.2|^β) ≤
      coordinateEnvelope x ^ d := by
    calc
      _ ≤ ∏ p ∈ gaussianBetaPairs N, coordinateEnvelope x ^ (2*m) :=
        Finset.prod_le_prod (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)
          (fun p _ => pair_rpow_le_envelope hβ.le hm x p.1 p.2)
      _ = _ := by simp [d, ← pow_mul]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (gaussianBetaDensity_nonneg β N x))]
  have hexp : Real.exp (-c * ∑ i, x i^2) = ∏ i, Real.exp (-c*x i^2) := by
    rw [Finset.mul_sum, Real.exp_sum]
  calc
    _ ≤ coordinateEnvelope x ^ q *
        (Real.exp (-c * ∑ i, x i^2) * coordinateEnvelope x ^ d) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le) (by positivity)
    _ = _ := by
      rw [hexp]
      simp only [coordinateEnvelope, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      rw [pow_add]
      ring

theorem gaussianBetaDensity_integrable {β : ℝ} (hβ : 0 < β)
    {N : ℕ} (hN : 0 < N) : Integrable (gaussianBetaDensity β N) := by
  simpa using gaussianBetaDensity_envelope_integrable hβ hN 0

theorem gaussianBetaPartition_pos {β : ℝ} (hβ : 0 < β)
    {N : ℕ} (hN : 0 < N) : 0 < gaussianBetaPartition β N := by
  apply integral_pos_of_integrable_nonneg_nonzero
    (gaussianBetaDensity_continuous hβ N) (gaussianBetaDensity_integrable hβ hN)
    (gaussianBetaDensity_nonneg β N)
    (x := fun i : Fin N => (i : ℝ))
  apply ne_of_gt
  unfold gaussianBetaDensity
  apply mul_pos (Real.exp_pos _)
  apply Finset.prod_pos
  intro p hp
  apply Real.rpow_pos_of_pos
  apply abs_pos.mpr
  have hp' : p.1 < p.2 := (Finset.mem_filter.mp hp).2
  have hcast : (p.1 : ℝ) < (p.2 : ℝ) := by exact_mod_cast hp'
  linarith

/-- Normalization is proved from the genuine positive integrable density. -/
theorem gaussianBetaMeasure_probability {β : ℝ} (hβ : 0 < β)
    {N : ℕ} (hN : 0 < N) : IsProbabilityMeasure (gaussianBetaMeasure β N) := by
  constructor
  rw [gaussianBetaMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal
      (gaussianBetaDensity_integrable hβ hN)
      (Filter.Eventually.of_forall (gaussianBetaDensity_nonneg β N))]
  change (ENNReal.ofReal (gaussianBetaPartition β N))⁻¹ * ENNReal.ofReal (gaussianBetaPartition β N) = 1
  exact ENNReal.inv_mul_cancel (by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (gaussianBetaPartition_pos hβ hN)))
    ENNReal.ofReal_ne_top

/-- Density integration formula; no normalizing constant is postulated. -/
theorem gaussianBetaMeasure_integral {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin N → ℝ) → E) :
    (∫ x, f x ∂gaussianBetaMeasure β N) =
      (gaussianBetaPartition β N)⁻¹ • ∫ x, gaussianBetaDensity β N x • f x := by
  rw [gaussianBetaMeasure, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul
      (gaussianBetaDensity_continuous hβ N).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal
    (le_of_lt (gaussianBetaPartition_pos hβ hN))]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (gaussianBetaDensity_nonneg β N x)]

/-- Any polynomially bounded measurable observable has finite moments under
this finite Gaussian beta ensemble. -/
theorem gaussianBetaMeasure_integrable_of_envelope {β : ℝ} (hβ : 0 < β)
    {N : ℕ} (hN : 0 < N) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (Fin N → ℝ) → E} (hf : StronglyMeasurable f)
    {C : ℝ} (q : ℕ) (hbound : ∀ x, ‖f x‖ ≤ C * (∏ i, (1+|x i|))^q) :
    Integrable f (gaussianBetaMeasure β N) := by
  have hnonneg (x : Fin N → ℝ) := gaussianBetaDensity_nonneg β N x
  have hweighted : Integrable (fun x => gaussianBetaDensity β N x • f x) := by
    refine ((gaussianBetaDensity_envelope_integrable hβ hN q).const_mul C).mono'
      ((gaussianBetaDensity_continuous hβ N).stronglyMeasurable.smul hf).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hnonneg x)]
    calc
      _ ≤ gaussianBetaDensity β N x * (C * (∏ i, (1+|x i|))^q) :=
        mul_le_mul_of_nonneg_left (hbound x) (hnonneg x)
      _ = _ := by ring
  unfold gaussianBetaMeasure
  apply Integrable.smul_measure _
    (ENNReal.inv_ne_top.mpr (ne_of_gt
      (ENNReal.ofReal_pos.mpr (gaussianBetaPartition_pos hβ hN))))
  apply (integrable_withDensity_iff_integrable_smul'
    (gaussianBetaDensity_continuous hβ N).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  simpa only [ENNReal.toReal_ofReal (hnonneg _)] using hweighted

end BourgadeHuang.RationalBulk
