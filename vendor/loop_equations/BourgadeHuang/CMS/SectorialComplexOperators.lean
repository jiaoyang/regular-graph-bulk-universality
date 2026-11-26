import BourgadeHuang.CMS.ComplexMatrixCoefficients
import BourgadeHuang.CMS.SectorialMatrixAnalytic

/-! Supremum-norm holomorphic complex operators assembled from the actual
sectorial radial coefficients. -/
noncomputable section
open scoped Topology BoundedContinuousFunction BigOperators
open Filter Set
namespace BourgadeHuang.CMS

/-- Assemble a finite family of scalar analytic lifts, retaining a single
neighborhood valid for every time on the unbounded ray. -/
theorem exists_analytic_complexMatrix_family
    {P X J K : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [TopologicalSpace X] [Fintype J] [Fintype K] [DecidableEq J]
    (f : J → K → P → X → ℂ) {p : P}
    (hf : ∀i j,∃F : P → (X →ᵇ ℂ),AnalyticAt ℂ F p ∧
      ∀ᶠw in 𝓝 p,∀t,F w t=f i j w t) :
    ∃A : P → (X →ᵇ ((K → ℂ) →L[ℂ] (J → ℂ))),AnalyticAt ℂ A p ∧
      ∀ᶠw in 𝓝 p,∀t v i,A w t v i=∑j,f i j w t*v j := by
  choose F hF hEq using hf
  refine ⟨fun w => complexBoundedMatrix (fun i j => F i j w),
    analyticAt_complexBoundedMatrix hF,?_⟩
  filter_upwards [Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hEq i))] with w hw
  intro t v i
  simp only [complexBoundedMatrix_apply,hw]

namespace SectorialData
variable {d : ℕ} (D : SectorialData d) (σ : Fin d → Sign) {z : Point d} {R : ℝ}
  (hR : 0<R) (hz : z∈OrderedDomain d) (hsep : ∀i j,i≠j→R≤‖z i-z j‖)
  {J K : Type*} [Fintype J] [Fintype K] [DecidableEq J]

include hR hz hsep in
/-- The actual principal triangular matrix has a holomorphic lift in operator
supremum norm, on a neighborhood common to the entire radial half-line. -/
theorem exists_analytic_principalOperator_family (ω : Point d)
    (rows : J → Finset (Fin d)) (cols : K → Finset (Fin d)) :
    ∃A : Point d → (Tail R →ᵇ ((K → ℂ) →L[ℂ] (J → ℂ))),AnalyticAt ℂ A z ∧
      ∀ᶠw in 𝓝 z,∀t v i,A w t v i=
        ∑j,D.principalRemainder ω (sectorialRay σ w R t) (t:ℝ) (rows i) (cols j)*v j := by
  apply exists_analytic_complexMatrix_family
  intro i j
  exact D.exists_analytic_principalRemainder_family σ hR hz hsep ω (rows i) (cols j)

include hR hz hsep in
/-- The reciprocal radial matrix, including all empty/nonempty row and column
blocks, has genuine Banach-space holomorphic dependence. -/
theorem exists_analytic_radialOperator_family (ω : Point d)
    (rows : J → Finset (Fin d)) (cols : K → Finset (Fin d)) :
    ∃A : Point d → (Tail R →ᵇ ((K → ℂ) →L[ℂ] (J → ℂ))),AnalyticAt ℂ A z ∧
      ∀ᶠw in 𝓝 z,∀t v i,A w t v i=
        ∑j,D.radialRemainder ω (sectorialRay σ w R t) (t:ℝ) (rows i) (cols j)*v j := by
  apply exists_analytic_complexMatrix_family
  intro i j
  exact D.exists_analytic_radialRemainder_family σ hR hz hsep ω (rows i) (cols j)

end SectorialData
end BourgadeHuang.CMS
