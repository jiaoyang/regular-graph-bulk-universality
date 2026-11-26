import BourgadeHuang.RationalBulk.SingularGaussianIntegrability

/-! The singular logarithmic derivatives of the finite Gaussian beta density
are genuinely integrable, including the range `0 < β < 1`. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

private theorem gaussianBetaDensity_gap_envelope_integrable_ordered {β : ℝ}
    (hβ : 0<β) {N : ℕ} (hN : 0<N) (i j : Fin N) (hij : i<j) (q : ℕ) :
    Integrable (fun x : Fin N → ℝ => coordinateEnvelope x^q *
      gaussianBetaDensity β N x / |x i-x j|) := by
  obtain ⟨m,hm⟩ := exists_nat_ge β
  let P := (gaussianBetaPairs N).erase (i,j)
  let d := 2*m*P.card
  let c := β/(4*(N:ℝ))
  have hc : 0<c := by dsimp [c]; positivity
  have hi := integrable_gap_singularity i j hij.ne hc
    (show -1<β-1 by linarith) (q+d)
  apply hi.mono'
  · exact ((((by unfold coordinateEnvelope; fun_prop : Continuous
      (fun x : Fin N → ℝ => coordinateEnvelope x)).measurable.pow_const q).mul
        (gaussianBetaDensity_continuous hβ N).measurable).div
          ((measurable_pi_apply i).sub (measurable_pi_apply j)).abs).aestronglyMeasurable
  · filter_upwards [] with x
    have hE : 0 ≤ coordinateEnvelope x := zero_le_one.trans (coordinateEnvelope_one_le x)
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      exact div_nonneg (mul_nonneg (pow_nonneg hE q) (gaussianBetaDensity_nonneg β N x)) (abs_nonneg _))]
    by_cases hz : x i-x j=0
    · simp only [hz,abs_zero,div_zero]
      positivity
    · have hgap : 0 < |x i-x j| := abs_pos.mpr hz
      have hpair : (i,j)∈gaussianBetaPairs N := by simp [gaussianBetaPairs,hij]
      have hprod : (∏ p∈P,|x p.1-x p.2|^β) ≤ coordinateEnvelope x^d := by
        calc
          _ ≤ ∏ _p∈P,coordinateEnvelope x^(2*m) :=
            Finset.prod_le_prod (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)
              (fun p _ => pair_rpow_le_envelope hβ.le hm x p.1 p.2)
          _ = _ := by simp [d,← pow_mul]
      have hfactor : (gaussianBetaDensity β N x)/|x i-x j| =
          Real.exp (-c*(∑ k,x k^2)) * |x i-x j|^(β-1) *
            (∏ p∈P,|x p.1-x p.2|^β) := by
        rw [gaussianBetaDensity,← Finset.prod_erase_mul _ _ hpair]
        dsimp only [P,c]
        rw [Real.rpow_sub hgap,Real.rpow_one]
        ring
      rw [mul_div_assoc,hfactor]
      calc
        _ ≤ coordinateEnvelope x^q *
            (Real.exp (-c*(∑ k,x k^2)) * |x i-x j|^(β-1) * coordinateEnvelope x^d) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod (by positivity))
            (pow_nonneg hE q)
        _ = _ := by rw [pow_add]; ring

/-- Arbitrary polynomial coordinate weights remain integrable after one inverse-gap factor. -/
theorem gaussianBetaDensity_gap_envelope_integrable {β : ℝ}
    (hβ : 0<β) {N : ℕ} (hN : 0<N) (i j : Fin N) (hij : i≠j) (q : ℕ) :
    Integrable (fun x : Fin N → ℝ => coordinateEnvelope x^q *
      gaussianBetaDensity β N x / |x i-x j|) := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact gaussianBetaDensity_gap_envelope_integrable_ordered hβ hN i j hij q
  · simpa only [abs_sub_comm] using gaussianBetaDensity_gap_envelope_integrable_ordered hβ hN j i hji q

/-- Collision-score integrability required by density integration by parts. -/
theorem gaussianBetaDensity_gap_integrable {β : ℝ}
    (hβ : 0<β) {N : ℕ} (hN : 0<N) (i j : Fin N) (hij : i≠j) :
    Integrable (fun x : Fin N → ℝ => gaussianBetaDensity β N x / |x i-x j|) := by
  simpa using gaussianBetaDensity_gap_envelope_integrable hβ hN i j hij 0

/-- Signed logarithmic collision scores also have every polynomial coordinate weight. -/
theorem gaussianBetaDensity_score_envelope_integrable {β : ℝ}
    (hβ : 0<β) {N : ℕ} (hN : 0<N) (i j : Fin N) (hij : i≠j) (q : ℕ) :
    Integrable (fun x : Fin N → ℝ => coordinateEnvelope x^q *
      gaussianBetaDensity β N x / (x i-x j)) := by
  apply (gaussianBetaDensity_gap_envelope_integrable hβ hN i j hij q).mono'
  · exact ((((by unfold coordinateEnvelope; fun_prop : Continuous
      (fun x : Fin N → ℝ => coordinateEnvelope x)).measurable.pow_const q).mul
        (gaussianBetaDensity_continuous hβ N).measurable).div
          ((measurable_pi_apply i).sub (measurable_pi_apply j))).aestronglyMeasurable
  · filter_upwards [] with x
    have hn := mul_nonneg (pow_nonneg (zero_le_one.trans (coordinateEnvelope_one_le x)) q)
        (gaussianBetaDensity_nonneg β N x)
    simp only [norm_div,Real.norm_eq_abs,abs_of_nonneg hn,le_refl]

theorem gaussianBetaDensity_score_integrable {β : ℝ}
    (hβ : 0<β) {N : ℕ} (hN : 0<N) (i j : Fin N) (hij : i≠j) :
    Integrable (fun x : Fin N → ℝ => gaussianBetaDensity β N x / (x i-x j)) := by
  simpa using gaussianBetaDensity_score_envelope_integrable hβ hN i j hij 0


/-- A measurable polynomially bounded observable can multiply the singular score. -/
theorem gaussianBetaDensity_score_smul_integrable {β : ℝ}
    (hβ : 0<β) {N : ℕ} (hN : 0<N) (i j : Fin N) (hij : i≠j)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin N → ℝ) → E} (hF : StronglyMeasurable F) {C : ℝ} (q : ℕ)
    (hbound : ∀ x, ‖F x‖ ≤ C*coordinateEnvelope x^q) :
    Integrable (fun x => (gaussianBetaDensity β N x / (x i-x j)) • F x) := by
  apply ((gaussianBetaDensity_gap_envelope_integrable hβ hN i j hij q).const_mul C).mono'
  · exact ((((gaussianBetaDensity_continuous hβ N).measurable.div
      ((measurable_pi_apply i).sub (measurable_pi_apply j))).stronglyMeasurable).smul hF).aestronglyMeasurable
  · filter_upwards [] with x
    rw [norm_smul,Real.norm_eq_abs,abs_div,abs_of_nonneg (gaussianBetaDensity_nonneg β N x)]
    calc
      _ ≤ (gaussianBetaDensity β N x / |x i-x j|)*(C*coordinateEnvelope x^q) :=
        mul_le_mul_of_nonneg_left (hbound x)
          (div_nonneg (gaussianBetaDensity_nonneg β N x) (abs_nonneg _))
      _ = _ := by ring

end BourgadeHuang.RationalBulk
