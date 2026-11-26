import BourgadeHuang.RationalBulk.GaussianBetaIntegrationByParts
import BourgadeHuang.RationalBulk.GaussianFiniteDivergence
import BourgadeHuang.RationalBulk.FiniteLoopBounds
import BourgadeHuang.RationalBulk.GaussianReferenceBridge
import BourgadeHuang.RationalBulk.GaussianScoreObservable

/-! The unconditional exact finite Gaussian-beta loop identity. Every collision
score and test derivative is integrated using the actual density and proved
integrability. No finite loop identity is assumed. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

theorem gaussianBetaDensity_integrable_anchoredGrowth {β : ℝ} (hβ : 0<β)
    {N : ℕ} (hN : 0<N) {F : AnchoredCountingState → ℂ} (hF : Continuous F)
    {d : ℕ} (hgrowth : AnchoredGrowth F d) :
    Integrable (fun x : Fin N → ℝ => (gaussianBetaDensity β N x : ℂ) * F (finiteAnchoredState x 0)) := by
  obtain ⟨C,hC,hbound⟩ := hgrowth
  apply gaussianBetaDensity_mul_integrable_of_envelope hβ hN
    ((hF.measurable.comp (measurable_finiteAnchoredState N 0)).stronglyMeasurable) 0
    (C := C*(1+(N:ℝ))^d)
  intro x
  simp only [pow_zero,mul_one]
  apply (hbound _).trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply pow_le_pow_left₀ (by positivity)
  have hb := finiteAnchoredState_anchor_bound x 0
  simpa only [abs_zero,add_zero] using add_le_add_left hb 1

/-- The monomial in the finite density identity is the actual state observable. -/
theorem resolventMonomial_finite {N n : ℕ} (x : Fin N → ℝ)
    {w : ℂ} {aux : Fin n → ℂ} (hw : w.im≠0) (ha : ∀a,(aux a).im≠0) :
    resolventMonomial (finiteAnchoredState x 0) w aux =
      microscopicResolvent x 0 w * ∏a,microscopicResolvent x 0 (aux a) := by
  simp only [resolventMonomial,finiteAnchoredState_nevanlinna x 0 hw,
    finiteAnchoredState_nevanlinna x 0 (ha _)]

/-- The exact finite loop equation for the actual normalized Gaussian beta law,
valid for every positive real beta and all mixed or repeated off-real parameters. -/
theorem gaussianBeta_finite_loop_identity (β : ℝ) (hβ : 0<β)
    (N n : ℕ) (w : ℂ) (hw : w.im≠0) (aux : Fin n → ℂ) (ha : ∀a,(aux a).im≠0) :
    (∫x,loopIntegrand β (finiteAnchoredState x 0) w aux ∂gaussianBetaMeasure β (N+1)) =
      -(w/(N+1:ℂ)) * ∫x,resolventMonomial (finiteAnchoredState x 0) w aux
        ∂gaussianBetaMeasure β (N+1) := by
  let L := fun x : Fin (N+1) → ℝ => loopIntegrand β (finiteAnchoredState x 0) w aux
  let M := fun x : Fin (N+1) → ℝ => resolventMonomial (finiteAnchoredState x 0) w aux
  let den := fun x : Fin (N+1) → ℝ => (gaussianBetaDensity β (N+1) x : ℂ)
  let k : ℂ := -(β:ℂ)/2
  let c : ℂ := w/(N+1:ℂ)
  have hL : Integrable (fun x => den x * L x) :=
    gaussianBetaDensity_integrable_anchoredGrowth hβ (by omega)
      (continuous_loopIntegrand β hw ha) (growth_loopIntegrand β hw ha)
  have hM : Integrable (fun x => den x * M x) :=
    gaussianBetaDensity_integrable_anchoredGrowth hβ (by omega)
      (continuous_resolventMonomial hw ha) (growth_resolventMonomial hw ha)
  let Q := fun (i : Fin (N+1)) (x : Fin (N+1) → ℝ) =>
    den x * (resolventTestDerivative x w aux i +
      (gaussianBetaScore β (N+1) x i : ℂ)*resolventTest x w aux i)
  have hQi (i : Fin (N+1)) : Integrable (Q i) := by
    obtain ⟨CF,_,hF⟩ := bounded_resolventTest i hw ha
    obtain ⟨CD,_,hD⟩ := bounded_resolventTestDerivative i hw ha
    have hDI := gaussianBetaDensity_mul_integrable_of_envelope hβ (by omega)
      (continuous_resolventTestDerivative i hw ha).stronglyMeasurable 0
      (C:=CD) (by simpa only [pow_zero,mul_one] using hD)
    have hSI := gaussianBetaDensity_fullScore_smul_integrable hβ (by omega) i
      (continuous_resolventTest i hw ha).stronglyMeasurable 0
      (C:=CF) (by simpa only [pow_zero,mul_one] using hF)
    convert hDI.add hSI using 1
    ext x
    simp only [Q,den,Pi.add_apply,Complex.real_smul,Complex.ofReal_mul]
    ring
  have hQ0 (i : Fin (N+1)) : (∫x,Q i x)=0 := by
    obtain ⟨CF,_,hF⟩ := bounded_resolventTest i hw ha
    obtain ⟨CD,_,hD⟩ := bounded_resolventTestDerivative i hw ha
    exact gaussianBetaDensity_integrationByParts_of_envelope hβ i
      (fun x => resolventTest x w aux i) (fun x => resolventTestDerivative x w aux i)
      (continuous_resolventTest i hw ha) (continuous_resolventTestDerivative i hw ha).stronglyMeasurable
      (fun x => hasDerivAt_resolventTest x i hw ha) 0 0
      (CF:=CF) (CD:=CD) (by simpa only [pow_zero,mul_one] using hF)
      (by simpa only [pow_zero,mul_one] using hD)
  have hsum : (∫x,∑i,Q i x)=0 := by
    rw [integral_finset_sum _ (fun i _ => hQi i)]
    simp only [hQ0,Finset.sum_const_zero]
  have hpoint x : (∑i,Q i x)=k*((den x*L x)+c*(den x*M x)) := by
    have h := gaussian_density_divergence_identity hβ (show 0<N+1 by omega) x hw ha
    dsimp only [Q,den]
    rw [h]
    rw [←resolventMonomial_finite x hw ha]
    dsimp [k,c,den,L,M]
    push_cast
    ring
  simp_rw [hpoint] at hsum
  rw [integral_const_mul,integral_add hL (hM.const_mul c),integral_const_mul] at hsum
  have hk : k≠0 := by dsimp [k]; exact div_ne_zero (neg_ne_zero.mpr (by exact_mod_cast hβ.ne')) (by norm_num)
  have hzero : (∫x,den x*L x)+c*(∫x,den x*M x)=0 := (mul_eq_zero.mp hsum).resolve_left hk
  rw [gaussianBetaMeasure_integral hβ (show 0<N+1 by omega),
    gaussianBetaMeasure_integral hβ (show 0<N+1 by omega)]
  simp only [Complex.real_smul]
  change _*(∫x,den x*L x) = -c*(_*(∫x,den x*M x))
  have hEq : (∫x,den x*L x) = -c*(∫x,den x*M x) := by linear_combination hzero
  rw [hEq]
  ring

end BourgadeHuang.RationalBulk
