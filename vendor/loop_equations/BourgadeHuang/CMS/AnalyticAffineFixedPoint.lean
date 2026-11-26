import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Normed

/-! Holomorphic dependence of genuine affine contraction fixed points on
Banach-space parameters, using the actual inverse operator. -/
noncomputable section
open scoped Topology
namespace BourgadeHuang.CMS
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The actual inverse-operator formula for the affine fixed point. -/
def affineFixedPoint (A : E →L[ℂ] E) (b : E) : E := Ring.inverse (1-A) b

theorem affineFixedPoint_equation {A : E →L[ℂ] E} (hA : ‖A‖<1) (b : E) :
    b+A (affineFixedPoint A b)=affineFixedPoint A b := by
  have hu : IsUnit (1-A) := isUnit_one_sub_of_norm_lt_one hA
  have hh := congrArg (fun L : E →L[ℂ] E => L b) (Ring.mul_inverse_cancel (1-A) hu)
  change affineFixedPoint A b-A (affineFixedPoint A b)=b at hh
  exact (sub_eq_iff_eq_add.mp hh).symm

theorem affineFixedPoint_unique {A : E →L[ℂ] E} (hA : ‖A‖<1) (b v : E)
    (hv : b+A v=v) : v=affineFixedPoint A b := by
  have hu : IsUnit (1-A) := isUnit_one_sub_of_norm_lt_one hA
  have hh := congrArg (fun L : E →L[ℂ] E => L v) (Ring.inverse_mul_cancel (1-A) hu)
  have he : (1-A) v=b := by change v-A v=b; exact sub_eq_iff_eq_add.mpr hv.symm
  change Ring.inverse (1-A) ((1-A) v)=v at hh
  rw [he] at hh
  exact hh.symm

/-- No differentiability of a selected fixed point is assumed: the unique
point equals an explicitly analytic inverse-operator expression. -/
theorem analyticAt_affineFixedPoint {A : P → E →L[ℂ] E} {b : P → E} {x : P}
    (hA : AnalyticAt ℂ A x) (hb : AnalyticAt ℂ b x) (hsmall : ‖A x‖<1) :
    AnalyticAt ℂ (fun y => affineFixedPoint (A y) (b y)) x := by
  have hu : IsUnit (1-A x) := isUnit_one_sub_of_norm_lt_one hsmall
  have hi : AnalyticAt ℂ Ring.inverse (1-A x) := by
    simpa only [hu.unit_spec] using analyticAt_inverse (𝕜 := ℂ) hu.unit
  have hI := hi.comp (f := fun y => (1 : E →L[ℂ] E)-A y) (analyticAt_const.sub hA)
  exact ((ContinuousLinearMap.id ℂ (E →L[ℂ] E)).analyticAt_bilinear _).comp₂ hI hb

theorem analyticAt_selected_affineFixedPoint {A : P → E →L[ℂ] E} {b v : P → E} {x : P}
    (hA : AnalyticAt ℂ A x) (hb : AnalyticAt ℂ b x) (hsmall : ‖A x‖<1)
    (hv : ∀ᶠy in 𝓝 x,b y+A y (v y)=v y) : AnalyticAt ℂ v x := by
  have he : ∀ᶠy in 𝓝 x,v y=affineFixedPoint (A y) (b y) := by
    filter_upwards [hv,hA.continuousAt.norm.eventually (Iio_mem_nhds hsmall)] with y hy hnorm
    exact affineFixedPoint_unique hnorm (b y) (v y) hy
  exact (analyticAt_affineFixedPoint hA hb hsmall).congr (he.mono (fun _ h => h.symm))

end BourgadeHuang.CMS
