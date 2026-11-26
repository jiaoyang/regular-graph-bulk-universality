import BourgadeHuang.CMS.GeneralCoupling

/-! Actual analytic conjugation of the general-coupling CMS operators. All
coordinate derivatives here are the derivatives of the displayed functions. -/
noncomputable section
open scoped BigOperators Topology
namespace BourgadeHuang.CMS

private theorem hasDerivAt_slice {d : ℕ} {f : Point d → ℂ} {z : Point d}
    (hf : DifferentiableAt ℂ f z) (i : Fin d) :
    HasDerivAt (fun w => f (Function.update z i w)) (coordDeriv i f z) (z i) := by
  rw [coordDeriv_eq_fderiv hf]
  exact hf.hasFDerivAt.comp_hasDerivAt_of_eq (z i) (hasDerivAt_update z i (z i))
    (Function.update_eq_self i z).symm

theorem coordDeriv_mul_analytic {d : ℕ} {f g : Point d → ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) (i : Fin d) :
    coordDeriv i (fun w => f w*g w) z =
      coordDeriv i f z*g z+f z*coordDeriv i g z := by
  simpa only [Function.update_eq_self] using
    ((hasDerivAt_slice hf.differentiableAt i).mul (hasDerivAt_slice hg.differentiableAt i)).deriv

theorem secondPartial_mul_analytic {d : ℕ} {f g : Point d → ℂ} {z : Point d}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) (i : Fin d) :
    secondPartial i (fun w => f w*g w) z =
      secondPartial i f z*g z+2*coordDeriv i f z*coordDeriv i g z+
        f z*secondPartial i g z := by
  unfold secondPartial
  have heq : (coordDeriv i (fun w => f w*g w)) =ᶠ[𝓝 z]
      (fun w => coordDeriv i f w*g w+f w*coordDeriv i g w) := by
    filter_upwards [hf.eventually_analyticAt,hg.eventually_analyticAt] with w hwf hwg
    exact coordDeriv_mul_analytic hwf hwg i
  rw [coordDeriv_congr_nhds heq]
  have hdf := analyticAt_coordDeriv hf i
  have hdg := analyticAt_coordDeriv hg i
  change coordDeriv i ((fun w => coordDeriv i f w*g w)+(fun w => f w*coordDeriv i g w)) z = _
  rw [coordDeriv_add_analytic (f := fun w => coordDeriv i f w*g w)
    (g := fun w => f w*coordDeriv i g w) (hdf.mul hg) (hf.mul hdg)]
  rw [coordDeriv_mul_analytic hdf hg,coordDeriv_mul_analytic hf hdg]
  ring

theorem coordDeriv_cexp {d : ℕ} {L : Point d → ℂ} {z : Point d}
    (hL : AnalyticAt ℂ L z) (i : Fin d) :
    coordDeriv i (fun w => Complex.exp (L w)) z = coordDeriv i L z*Complex.exp (L z) := by
  simpa only [Function.update_eq_self,mul_comm] using (hasDerivAt_slice hL.differentiableAt i).cexp.deriv

theorem secondPartial_cexp {d : ℕ} {L : Point d → ℂ} {z : Point d}
    (hL : AnalyticAt ℂ L z) (i : Fin d) :
    secondPartial i (fun w => Complex.exp (L w)) z =
      (secondPartial i L z+(coordDeriv i L z)^2)*Complex.exp (L z) := by
  unfold secondPartial
  have heq : coordDeriv i (fun w => Complex.exp (L w)) =ᶠ[𝓝 z]
      (fun w => coordDeriv i L w*Complex.exp (L w)) := by
    filter_upwards [hL.eventually_analyticAt] with w hw
    exact coordDeriv_cexp hw i
  have hexp : AnalyticAt ℂ (fun w => Complex.exp (L w)) z := hL.cexp
  rw [coordDeriv_congr_nhds heq,
    coordDeriv_mul_analytic (analyticAt_coordDeriv hL i) hexp,coordDeriv_cexp hL]
  ring

/-- Explicit conjugated differential operator, with the actual logarithmic
phase `L`; no unproved logarithmic-derivative data is stored in the definition. -/
def conjugatedDeformedOperator {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (L : Point d → ℂ) (i : Fin d) (W : Point d → ℂ) (z : Point d) : ℂ :=
  secondPartial i W z+2*coordDeriv i L z*coordDeriv i W z+
    (secondPartial i L z+(coordDeriv i L z)^2+c i^2)*W z+
      (2/β)*∑j∈Finset.univ.erase i,
        (c i*c j*coordDeriv i W z-c i^2*coordDeriv j W z+
          (c i*c j*coordDeriv i L z-c i^2*coordDeriv j L z)*W z)/(z i-z j)

theorem deformedOperator_exp_mul {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    {L W : Point d → ℂ} {z : Point d} (hL : AnalyticAt ℂ L z)
    (hW : AnalyticAt ℂ W z) (i : Fin d) :
    deformedOperator β c i (fun w => Complex.exp (L w)*W w) z =
      Complex.exp (L z)*conjugatedDeformedOperator β c L i W z := by
  have ht (j : Fin d) :
      (c i*c j*(coordDeriv i L z*Complex.exp (L z)*W z+Complex.exp (L z)*coordDeriv i W z)-
        c i^2*(coordDeriv j L z*Complex.exp (L z)*W z+Complex.exp (L z)*coordDeriv j W z))/(z i-z j) =
      Complex.exp (L z)*((c i*c j*coordDeriv i W z-c i^2*coordDeriv j W z+
        (c i*c j*coordDeriv i L z-c i^2*coordDeriv j L z)*W z)/(z i-z j)) := by ring
  have hexp : AnalyticAt ℂ (fun w => Complex.exp (L w)) z := hL.cexp
  simp only [deformedOperator,secondPartial_mul_analytic hexp hW,
    secondPartial_cexp hL,coordDeriv_mul_analytic hexp hW,coordDeriv_cexp hL,ht,
    ← Finset.mul_sum,conjugatedDeformedOperator]
  ring

theorem deformedOperator_exp_mul_eq_zero_iff {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    {L W : Point d → ℂ} {z : Point d} (hL : AnalyticAt ℂ L z)
    (hW : AnalyticAt ℂ W z) (i : Fin d) :
    deformedOperator β c i (fun w => Complex.exp (L w)*W w) z = 0 ↔
      conjugatedDeformedOperator β c L i W z = 0 := by
  rw [deformedOperator_exp_mul β c hL hW,mul_eq_zero]
  simp [Complex.exp_ne_zero]

end BourgadeHuang.CMS
