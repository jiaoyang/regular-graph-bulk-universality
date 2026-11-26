import BourgadeHuang.EdgeCMS.RootGeometry
import BourgadeHuang.RationalEdge.ChargedNormalization

/-! The deterministic center in the charged edge path estimate is the actual
principal square root. Its path integral is the Airy phase difference. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory
namespace BourgadeHuang.RationalEdge
open EdgeCMS

theorem ratioPath_mem_slitPlane {u v : ℂ} (huv : SameOpenHalfPlane u v)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : ratioPath u v t ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inr (ratioPath_offReal huv ht))

theorem continuous_root_ratioPath {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    Continuous (fun t : RatioInterval => root (ratioPath u v t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (analyticAt_root (ratioPath_mem_slitPlane huv t.property)).continuousAt.comp (f := fun t : RatioInterval => ratioPath u v t)
    ((continuous_ratioPath u v).comp continuous_subtype_val).continuousAt

/-- The actual deterministic path phase is exactly `2/3(u sqrt(u)-v sqrt(v))`. -/
theorem centeredPathPhase_root {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    centeredPathPhase u v (fun t => root (ratioPath u v t)) =
      edgePrimitive u-edgePrimitive v := by
  have hd (t : ℝ) (ht : t ∈ Set.uIcc (0:ℝ) 1) :
      HasDerivAt (fun t : ℝ => edgePrimitive (ratioPath u v t))
        ((u-v)*root (ratioPath u v t)) t := by
    have hslit := ratioPath_mem_slitPlane huv (Set.uIcc_of_le (by norm_num : (0:ℝ)≤1) ▸ ht)
    have hp := (hasDerivAt_const (t:ℂ) v).add ((hasDerivAt_id (t:ℂ)).mul_const (u-v))
    have hf := (hasDerivAt_edgePrimitive hslit).comp (t:ℂ) hp
    convert hf.comp_ofReal using 1
    simp only [Function.comp_apply,zero_add,one_mul,id_eq,ratioPath]
    ring
  have hc : ContinuousOn (fun t : ℝ => (u-v)*root (ratioPath u v t))
      (Set.uIcc (0:ℝ) 1) := by
    apply continuousOn_const.mul
    intro t ht
    have hslit := ratioPath_mem_slitPlane huv (Set.uIcc_of_le (by norm_num : (0:ℝ)≤1) ▸ ht)
    exact ((analyticAt_root hslit).continuousAt.comp
      (continuous_ratioPath u v).continuousAt).continuousWithinAt
  unfold centeredPathPhase
  rw [integral_ratioInterval (fun t : ℝ => (u-v)*root (ratioPath u v t))]
  simpa [ratioPath] using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable

end BourgadeHuang.RationalEdge
