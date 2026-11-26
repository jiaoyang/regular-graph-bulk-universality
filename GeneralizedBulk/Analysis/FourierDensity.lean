import GeneralizedBulk.Gaussian.CharacteristicUniqueness

/-! Fourier uniqueness for an actual integrable signed real density. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Analysis
variable {I : Type*} [Fintype I]

/-- A real L¹ density with zero Fourier transform vanishes almost everywhere.
The proof uses actual positive and negative finite weighted measures. -/
theorem ae_zero_of_fourier_density_zero (μ : Measure (I → ℝ)) [SigmaFinite μ]
    (f : (I → ℝ) → ℝ) (hf : Integrable f μ)
    (hzero : ∀ t : I → ℝ,
      (∫ x, (f x : ℂ) * Complex.exp ((↑(∑ i, t i * x i) : ℂ) * Complex.I) ∂μ) = 0) :
    f =ᵐ[μ] 0 := by
  let p := fun x => max (f x) 0
  let n := fun x => max (-f x) 0
  have hp : Integrable p μ := hf.pos_part
  have hn : Integrable n μ := hf.neg.pos_part
  have hp0 (x) : 0 ≤ p x := le_max_right _ _
  have hn0 (x) : 0 ≤ n x := le_max_right _ _
  have hdecomp (x) : f x = p x - n x := by
    dsimp [p, n]
    by_cases hx : 0 ≤ f x
    · rw [max_eq_left hx, max_eq_right (by linarith)]
      ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
      ring
  let μp := μ.withDensity (fun x => ENNReal.ofReal (p x))
  let μn := μ.withDensity (fun x => ENNReal.ofReal (n x))
  letI : IsFiniteMeasure μp := isFiniteMeasure_withDensity_ofReal hp.2
  letI : IsFiniteMeasure μn := isFiniteMeasure_withDensity_ofReal hn.2
  have hmeq : μp = μn := by
    apply GeneralizedBulk.Gaussian.measure_eq_of_linear_characteristic
    intro t
    let χ := fun x : I → ℝ => Complex.exp ((↑(∑ i, t i * x i) : ℂ) * Complex.I)
    have hχ : Continuous χ := by dsimp [χ]; fun_prop
    have hχnorm (x : I → ℝ) : ‖χ x‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    have hpi : Integrable (fun x => (p x : ℂ) * χ x) μ := by
      have hh : Integrable (fun x => χ x * (p x : ℂ)) μ :=
        hp.ofReal.bdd_mul hχ.aestronglyMeasurable ⟨1, fun x => (hχnorm x).le⟩
      simpa only [mul_comm] using hh
    have hni : Integrable (fun x => (n x : ℂ) * χ x) μ := by
      have hh : Integrable (fun x => χ x * (n x : ℂ)) μ :=
        hn.ofReal.bdd_mul hχ.aestronglyMeasurable ⟨1, fun x => (hχnorm x).le⟩
      simpa only [mul_comm] using hh
    have hsum : (∫ x, (f x : ℂ) * χ x ∂μ) =
        (∫ x, (p x : ℂ) * χ x ∂μ) - ∫ x, (n x : ℂ) * χ x ∂μ := by
      rw [← integral_sub hpi hni]
      apply integral_congr_ae
      filter_upwards with x
      have hh := congrArg (fun r : ℝ => (r : ℂ)) (hdecomp x)
      push_cast at hh
      rw [hh]
      ring
    have hz := hzero t
    change (∫ x, (f x : ℂ) * χ x ∂μ) = 0 at hz
    rw [hsum] at hz
    have hi : (∫ x, (p x : ℂ) * χ x ∂μ) = ∫ x, (n x : ℂ) * χ x ∂μ := sub_eq_zero.mp hz
    change (∫ x, χ x ∂μ.withDensity (fun x => ENNReal.ofReal (p x))) =
      ∫ x, χ x ∂μ.withDensity (fun x => ENNReal.ofReal (n x))
    rw [integral_withDensity_eq_integral_toReal_smul₀ hp.aestronglyMeasurable.aemeasurable.ennreal_ofReal
        (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)) χ,
      integral_withDensity_eq_integral_toReal_smul₀ hn.aestronglyMeasurable.aemeasurable.ennreal_ofReal
        (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)) χ]
    simp only [ENNReal.toReal_ofReal (hp0 _), ENNReal.toReal_ofReal (hn0 _), Complex.real_smul]
    exact hi
  have hae := (withDensity_eq_iff_of_sigmaFinite hp.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    hn.aestronglyMeasurable.aemeasurable.ennreal_ofReal).mp hmeq
  filter_upwards [hae] with x hx
  have hpn : p x = n x := (ENNReal.ofReal_eq_ofReal_iff (hp0 x) (hn0 x)).mp hx
  rw [hdecomp, hpn, sub_self]
  rfl

end GeneralizedBulk.Analysis
