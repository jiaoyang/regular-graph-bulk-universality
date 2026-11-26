import GaussianWave.BS.DensityEntropy

/-!
# Strict Gibbs inequality for actual densities

This lower-bound analytic foundation identifies equality with equality of
the actual density laws. Integrability is explicit so no totalized integral
can create a spurious equality case.
-/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

theorem gibbs_integrand_eq_zero_iff (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    a * Real.log a - a * Real.log b - a + b = 0 ↔ a = b := by
  constructor
  · intro he
    by_contra hab
    by_cases ha0 : a = 0
    · simp only [ha0, zero_mul, sub_self, sub_zero, zero_add] at he
      exact (ne_of_gt hb) he
    have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hba : b / a ≠ 1 := by
      intro hh
      have hh' := (div_eq_one_iff_eq ha0).mp hh
      exact hab hh'.symm
    have hlog := Real.log_lt_sub_one_of_pos (div_pos hb hap) hba
    rw [Real.log_div hb.ne' ha0] at hlog
    have hm := mul_lt_mul_of_pos_left hlog hap
    have hmul : a * (b / a - 1) = b - a := by field_simp
    rw [hmul] at hm
    nlinarith
  · rintro rfl
    ring

theorem densityEntropy_eq_crossEntropy_iff
    {E : Type*} [MeasurableSpace E] (m : Measure E) (f g : E → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 < g x)
    (hfi : Integrable f m) (hgi : Integrable g m)
    (hf : (∫ x, f x ∂m) = 1) (hg : (∫ x, g x ∂m) = 1)
    (hflog : Integrable (fun x => f x * Real.log (f x)) m)
    (hcross : Integrable (fun x => f x * Real.log (g x)) m) :
    (densityEntropy m f = -(∫ x, f x * Real.log (g x) ∂m)) ↔ f =ᵐ[m] g := by
  let D := fun x => f x * Real.log (f x) - f x * Real.log (g x) - f x + g x
  have hDi : Integrable D m := ((hflog.sub hcross).sub hfi).add hgi
  have hDnonneg : ∀ x, 0 ≤ D x := fun x => gibbs_integrand_nonneg _ _ (hf0 x) (hg0 x)
  have hDint : (∫ x, D x ∂m) = -densityEntropy m f - ∫ x, f x * Real.log (g x) ∂m := by
    dsimp only [D]
    rw [integral_add (f := fun x => f x * Real.log (f x) - f x * Real.log (g x) - f x)
      ((hflog.sub hcross).sub hfi) hgi,
      integral_sub (f := fun x => f x * Real.log (f x) - f x * Real.log (g x))
        (hflog.sub hcross) hfi,
      integral_sub (f := fun x => f x * Real.log (f x)) hflog hcross, hf, hg]
    unfold densityEntropy
    ring
  constructor
  · intro he
    have hzero : (∫ x, D x ∂m) = 0 := by rw [hDint, he]; ring
    have hae := (integral_eq_zero_iff_of_nonneg hDnonneg hDi).mp hzero
    filter_upwards [hae] with x hx
    exact (gibbs_integrand_eq_zero_iff _ _ (hf0 x) (hg0 x)).mp hx
  · intro he
    unfold densityEntropy
    congr 1
    apply integral_congr_ae
    filter_upwards [he] with x hx
    rw [hx]

theorem densityEntropy_eq_crossEntropy_iff_measure_eq
    {E : Type*} [MeasurableSpace E] (m : Measure E) [SigmaFinite m] (f g : E → ℝ)
    (hfm : Measurable f) (hgm : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 < g x)
    (hfi : Integrable f m) (hgi : Integrable g m)
    (hf : (∫ x, f x ∂m) = 1) (hg : (∫ x, g x ∂m) = 1)
    (hflog : Integrable (fun x => f x * Real.log (f x)) m)
    (hcross : Integrable (fun x => f x * Real.log (g x)) m) :
    (densityEntropy m f = -(∫ x, f x * Real.log (g x) ∂m)) ↔
      m.withDensity (fun x => ENNReal.ofReal (f x)) =
        m.withDensity (fun x => ENNReal.ofReal (g x)) := by
  rw [densityEntropy_eq_crossEntropy_iff m f g hf0 hg0 hfi hgi hf hg hflog hcross]
  constructor
  · intro h
    exact withDensity_congr_ae (h.mono (fun _ hx => congrArg ENNReal.ofReal hx))
  · intro h
    have hae := (withDensity_eq_iff_of_sigmaFinite hfm.ennreal_ofReal.aemeasurable
      hgm.ennreal_ofReal.aemeasurable).mp h
    filter_upwards [hae] with x hx
    have hreal := congrArg ENNReal.toReal hx
    simpa only [ENNReal.toReal_ofReal (hf0 _), ENNReal.toReal_ofReal (hg0 _).le] using hreal

end GaussianWave.BS
