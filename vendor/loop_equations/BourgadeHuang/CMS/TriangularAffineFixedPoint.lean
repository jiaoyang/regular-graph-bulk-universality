import BourgadeHuang.CMS.FilteredOperatorInverse

/-! Holomorphic fixed points after exact finite triangular elimination. -/
noncomputable section
open scoped Topology
namespace BourgadeHuang.CMS
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The explicit fixed point after eliminating the nilpotent principal part. -/
def triangularAffineFixedPoint (B A : E →L[ℂ] E) (b : E) (H : ℕ) : E :=
  affineFixedPoint (triangularInverse B H*A) (triangularInverse B H b)

theorem triangularAffineFixedPoint_equation {B A : E →L[ℂ] E} {H : ℕ}
    (hB : B^H=0) (hA : ‖triangularInverse B H*A‖<1) (b : E) :
    b+B (triangularAffineFixedPoint B A b H)+A (triangularAffineFixedPoint B A b H)=
      triangularAffineFixedPoint B A b H := by
  let v := triangularAffineFixedPoint B A b H
  have h : triangularInverse B H (b+A v)=v := by
    simpa only [map_add,ContinuousLinearMap.mul_apply] using
      affineFixedPoint_equation hA (triangularInverse B H b)
  have he := congrArg (fun x => (1-B) x) h
  have hi := congrArg (fun L : E →L[ℂ] E => L (b+A v)) (mul_triangularInverse hB)
  change (1-B) (triangularInverse B H (b+A v))=b+A v at hi
  dsimp only at he
  rw [hi] at he
  change b+A v=v-B v at he
  change b+B v+A v=v
  simpa only [add_assoc,add_comm,add_left_comm] using eq_sub_iff_add_eq.mp he

theorem triangularAffineFixedPoint_unique {B A : E →L[ℂ] E} {H : ℕ}
    (hB : B^H=0) (hA : ‖triangularInverse B H*A‖<1) (b v : E)
    (hv : b+B v+A v=v) : v=triangularAffineFixedPoint B A b H := by
  apply affineFixedPoint_unique hA
  have he : (1-B) v=b+A v := by
    change v-B v=b+A v
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_assoc,add_comm,add_left_comm] using hv.symm)
  have hi := congrArg (fun L : E →L[ℂ] E => L v) (triangularInverse_mul hB)
  change triangularInverse B H ((1-B) v)=v at hi
  rw [he,map_add] at hi
  exact hi

theorem analyticAt_triangularAffineFixedPoint
    {B A : P → E →L[ℂ] E} {b : P → E} {x : P} (H : ℕ)
    (hB : AnalyticAt ℂ B x) (hA : AnalyticAt ℂ A x) (hb : AnalyticAt ℂ b x)
    (hsmall : ‖triangularInverse (B x) H*A x‖<1) :
    AnalyticAt ℂ (fun y => triangularAffineFixedPoint (B y) (A y) (b y) H) x := by
  have hT := analyticAt_triangularInverse hB H
  apply analyticAt_affineFixedPoint (hT.mul hA) _ hsmall
  exact ((ContinuousLinearMap.id ℂ (E →L[ℂ] E)).analyticAt_bilinear _).comp₂ hT hb

/-- Holomorphy is deduced from the actual fixed-point equation and uniqueness,
without assuming regularity of a chosen solution. -/
theorem analyticAt_selected_triangularAffineFixedPoint
    {B A : P → E →L[ℂ] E} {b v : P → E} {x : P} (H : ℕ)
    (hB : AnalyticAt ℂ B x) (hA : AnalyticAt ℂ A x) (hb : AnalyticAt ℂ b x)
    (hsmall : ‖triangularInverse (B x) H*A x‖<1)
    (hNil : ∀ᶠy in 𝓝 x,B y^H=0)
    (hv : ∀ᶠy in 𝓝 x,b y+B y (v y)+A y (v y)=v y) : AnalyticAt ℂ v x := by
  have hc := ((analyticAt_triangularInverse hB H).mul hA).continuousAt.norm
  have he : ∀ᶠy in 𝓝 x,v y=triangularAffineFixedPoint (B y) (A y) (b y) H := by
    filter_upwards [hNil,hv,hc.eventually (Iio_mem_nhds hsmall)] with y hny hvy hsy
    exact triangularAffineFixedPoint_unique hny hsy (b y) (v y) hvy
  exact (analyticAt_triangularAffineFixedPoint H hB hA hb hsmall).congr
    (he.mono (fun _ h => h.symm))

end BourgadeHuang.CMS
