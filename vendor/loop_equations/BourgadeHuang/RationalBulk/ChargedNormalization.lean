import BourgadeHuang.RationalBulk.SmallSources
import BourgadeHuang.RationalBulk.ChargedObservables

/-! Quantitative normalization of the actual general-beta charged observable
for small weighted displacements within either half-plane. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

theorem reflected_realCenteredSource (epsilon : Bool) (c : ℝ)
    (gamma rho : RatioInterval → ℂ) (s : AnchoredCountingState) :
    reflectComplex epsilon (compactCenteredSource ratioIntervalMeasure gamma
      (fun t=>(c:ℂ)*rho t) s) =
      (c:ℂ)*reflectComplex epsilon (compactCenteredSource ratioIntervalMeasure gamma rho s) := by
  have h : compactCenteredSource ratioIntervalMeasure gamma (fun t=>(c:ℂ)*rho t) s =
      (c:ℂ)*compactCenteredSource ratioIntervalMeasure gamma rho s := by
    simp only [compactCenteredSource,mul_assoc,integral_const_mul]
  rw [h]
  cases epsilon <;> simp [reflectComplex]

/-- Every positive coupling has an explicit small-source bound. Charges may
be any real numbers, so this also covers the physical rational charge blocks. -/
theorem expectedChargedObservable_normalized_bound {d : ℕ}
    (nu : Measure AnchoredCountingState) [IsProbabilityMeasure nu]
    (beta : ℝ) (hh : ExactHierarchy nu beta) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) nu)
    (c : Fin d → ℝ) (epsilon : Fin d → Bool) (u v : Fin d → ℂ)
    {eta delta : ℝ} (heta : 0<eta) (hdelta : 0<delta)
    (hu : ∀j,eta≤(reflectComplex (epsilon j) (u j)).im)
    (hv : ∀j,eta≤(reflectComplex (epsilon j) (v j)).im)
    (hdist : ∀j,|c j| *‖u j-v j‖≤delta*eta) :
    ‖Complex.exp (-(∑j,(c j:ℂ)*signedRatioPhase (epsilon j) (u j) (v j)))*
      expectedChargedObservable nu (fun j=>(c j:ℂ)) v u-1‖≤
      delta*(16*localLawConstant beta*(d:ℝ)^2+(d:ℝ)*
        Real.exp (((d:ℝ)*delta)^2/bulkExponentialScale beta)) := by
  by_cases hd : d=0
  · subst d
    simp [expectedChargedObservable,chargedObservable]
  have hdp : 0<d := Nat.pos_of_ne_zero hd
  let U := fun j=>reflectComplex (epsilon j) (u j)
  let V := fun j=>reflectComplex (epsilon j) (v j)
  let gamma := fun j=>fun t : RatioInterval=>ratioPath (U j) (V j) t
  let rho := fun j=>fun _ : RatioInterval=>(c j:ℂ)*(U j-V j)
  have hgamma j : Continuous (gamma j) := (continuous_ratioPath _ _).comp continuous_subtype_val
  have hrho j : Continuous (rho j) := continuous_const
  have hup j t : 0<(gamma j t).im := heta.trans_le (ratioPath_im_lower (hu j) (hv j) t)
  have hr j t : ‖rho j t‖≤delta*(gamma j t).im := by
    dsimp [rho,gamma,U,V]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,← reflectComplex_sub,norm_reflectComplex]
    exact (hdist j).trans (mul_le_mul_of_nonneg_left (ratioPath_im_lower (hu j) (hv j) t) hdelta.le)
  obtain ⟨_,hb⟩ := finiteReflectedCompactSource_exponential_close hdp ratioIntervalMeasure
    epsilon gamma rho hgamma hrho hup nu beta hh ha he hdelta hr
  have huv j := sameOpenHalfPlane_of_reflect_pos (epsilon j) (heta.trans_le (hu j)) (heta.trans_le (hv j))
  have heq s : chargedObservable (fun j=>(c j:ℂ)) v s u =
      Complex.exp (∑j,(c j:ℂ)*signedRatioPhase (epsilon j) (u j) (v j))*
        Complex.exp (∑j,reflectComplex (epsilon j)
          (compactCenteredSource ratioIntervalMeasure (gamma j) (rho j) s)) := by
    rw [chargedObservable_eq_exp _ _ _ huv,← Complex.exp_add]
    congr 1
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [gamma,rho,U,V]
    rw [nevanlinnaPathPrimitive_signed_centered s (epsilon j)
      (heta.trans_le (hu j)) (heta.trans_le (hv j))]
    have hrhoeq : (fun _ : RatioInterval=>(c j:ℂ)*(reflectComplex (epsilon j) (u j)-
        reflectComplex (epsilon j) (v j))) =
      (fun _ : RatioInterval=>(-(c j):ℝ)*( -(reflectComplex (epsilon j) (u j)-
        reflectComplex (epsilon j) (v j)) : ℂ)) := by
      funext t
      push_cast
      ring
    rw [hrhoeq,reflected_realCenteredSource]
    push_cast
    ring
  simp only [expectedChargedObservable,heq,integral_const_mul]
  rw [← mul_assoc,← Complex.exp_add,neg_add_cancel,Complex.exp_zero,one_mul]
  exact hb

theorem tendsto_expectedChargedObservable_normalized
    {A : Type*} {l : Filter A} {d : ℕ}
    (nu : Measure AnchoredCountingState) [IsProbabilityMeasure nu]
    (beta : ℝ) (hh : ExactHierarchy nu beta) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) nu)
    (c : Fin d → ℝ) (epsilon : Fin d → Bool) (u v : A → Fin d → ℂ)
    (eta delta : A → ℝ) (hdelta : Tendsto delta l (𝓝 0))
    (hgeom : ∀ᶠt in l,0<eta t ∧ 0<delta t ∧
      (∀j,eta t≤(reflectComplex (epsilon j) (u t j)).im) ∧
      (∀j,eta t≤(reflectComplex (epsilon j) (v t j)).im) ∧
      (∀j,|c j| *‖u t j-v t j‖≤delta t*eta t)) :
    Tendsto (fun t=>Complex.exp (-(∑j,(c j:ℂ)*signedRatioPhase (epsilon j) (u t j) (v t j)))*
      expectedChargedObservable nu (fun j=>(c j:ℂ)) (v t) (u t)) l (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb : Tendsto (fun t=>delta t*(16*localLawConstant beta*(d:ℝ)^2+(d:ℝ)*
      Real.exp (((d:ℝ)*delta t)^2/bulkExponentialScale beta))) l (𝓝 0) := by
    have hc : Continuous (fun r : ℝ=>r*(16*localLawConstant beta*(d:ℝ)^2+(d:ℝ)*
        Real.exp (((d:ℝ)*r)^2/bulkExponentialScale beta))) := by fun_prop
    simpa using hc.continuousAt.tendsto.comp hdelta
  apply squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) _ hb
  filter_upwards [hgeom] with t ht
  exact expectedChargedObservable_normalized_bound nu beta hh ha he c epsilon (u t) (v t)
    ht.1 ht.2.1 ht.2.2.1 ht.2.2.2.1 ht.2.2.2.2

end BourgadeHuang.RationalBulk
