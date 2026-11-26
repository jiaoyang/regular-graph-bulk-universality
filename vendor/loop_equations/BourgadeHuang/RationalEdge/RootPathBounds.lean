import BourgadeHuang.RationalEdge.ChargedPathBounds
import BourgadeHuang.RationalEdge.EdgePhasePaths

/-! A direct edge charged-observable estimate in a concrete convex sector.
All random estimates follow from the exact edge hierarchy; the deterministic
normalizing phase is the actual Airy phase `2/3 z sqrt(z)`. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory
namespace BourgadeHuang.RationalEdge
open RationalBulk EdgeCMS

theorem root_reflect (epsilon : Bool) {z : ℂ} (hz : z.im≠0) :
    root (reflectComplex epsilon z)=reflectComplex epsilon (root z) := by
  cases epsilon
  · exact root_conj hz
  · rfl

theorem reflect_ratioPath (epsilon : Bool) (u v : ℂ) (t : ℝ) :
    reflectComplex epsilon (ratioPath u v t)=
      ratioPath (reflectComplex epsilon u) (reflectComplex epsilon v) t := by
  cases epsilon
  · simp only [reflectComplex,Bool.false_eq_true,if_false,ratioPath_conj]
  · rfl

theorem ratioPath_sector {u v : ℂ} (hu : u.re≤u.im) (hv : v.re≤v.im)
    (t : RatioInterval) : (ratioPath u v t).re≤(ratioPath u v t).im := by
  have hre : (ratioPath u v t).re=(1-(t:ℝ))*v.re+(t:ℝ)*u.re := by simp [ratioPath];ring
  have him : (ratioPath u v t).im=(1-(t:ℝ))*v.im+(t:ℝ)*u.im := by simp [ratioPath];ring
  rw [hre,him]
  exact add_le_add (mul_le_mul_of_nonneg_left hv (sub_nonneg.mpr t.property.2))
    (mul_le_mul_of_nonneg_left hu t.property.1)

theorem expectedChargedObservable_airyPhase_bound
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν] (β : ℝ)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {d : ℕ} (hd : 0<d) (c u v : Fin d → ℂ) (epsilon : Fin d → Bool)
    (hu : ∀ j, 0<(reflectComplex (epsilon j) (u j)).im)
    (hv : ∀ j, 0<(reflectComplex (epsilon j) (v j)).im)
    (husector : ∀ j, (reflectComplex (epsilon j) (u j)).re≤(reflectComplex (epsilon j) (u j)).im)
    (hvsector : ∀ j, (reflectComplex (epsilon j) (v j)).re≤(reflectComplex (epsilon j) (v j)).im)
    {δ : ℝ} (hδ : 0<δ)
    (hcost : ∀ j, ‖c j*(u j-v j)‖≤δ*min
      (reflectComplex (epsilon j) (u j)).im (reflectComplex (epsilon j) (v j)).im) :
    ‖Complex.exp (-(∑ j, c j*(edgePrimitive (u j)-edgePrimitive (v j))))*
      expectedChargedObservable ν c v u-1‖ ≤
      δ*(16*localLawConstant β*edgeStabilityConstant 4*(d:ℝ)^2+
        (d:ℝ)*Real.exp (((d:ℝ)*δ)^2/edgeExponentialScale β 4)) := by
  have huv j : SameOpenHalfPlane (u j) (v j) := by
    cases he : epsilon j
    · exact Or.inr (by simpa [reflectComplex, he] using And.intro (hu j) (hv j))
    · exact Or.inl (by simpa [reflectComplex, he] using And.intro (hu j) (hv j))
  let m := fun j (t : RatioInterval) => root (ratioPath (u j) (v j) t)
  have hm j : Continuous (m j) := continuous_root_ratioPath (huv j)
  have hlow j (t : RatioInterval) : min (reflectComplex (epsilon j) (u j)).im
      (reflectComplex (epsilon j) (v j)).im≤
        (reflectComplex (epsilon j) (ratioPath (u j) (v j) t)).im := by
    rw [reflect_ratioPath]
    exact ratioPath_im_lower (min_le_left _ _) (min_le_right _ _) t
  have hw j (t : RatioInterval) :
      0<(reflectComplex (epsilon j) (ratioPath (u j) (v j) t)).im :=
    (lt_min (hu j) (hv j)).trans_le (hlow j t)
  have hroot j (t : RatioInterval) : reflectComplex (epsilon j) (m j t)=
      root (reflectComplex (epsilon j) (ratioPath (u j) (v j) t)) :=
    (root_reflect (epsilon j) (ratioPath_offReal (huv j) t.property)).symm
  have hr2 j t : (reflectComplex (epsilon j) (m j t))^2=
      reflectComplex (epsilon j) (ratioPath (u j) (v j) t) := by
    rw [hroot]
    apply root_sq
    intro heq
    simpa [heq] using hw j t
  have hr j t : 0<(reflectComplex (epsilon j) (m j t)).im := by
    rw [hroot]
    exact root_im_pos (hw j t)
  have hsector j t : ‖reflectComplex (epsilon j) (m j t)‖≤
      4*(reflectComplex (epsilon j) (m j t)).im := by
    rw [hroot]
    apply root_norm_le_four_im (hw j t)
    rw [reflect_ratioPath]
    exact ratioPath_sector (husector j) (hvsector j) t
  have h := expectedChargedObservable_edge_normalized_bound ν β hh ha he hd c u v
    epsilon m huv hm (by norm_num : (0:ℝ)≤4) hδ hw hr2 hr hsector
    (fun j t => (hcost j).trans (mul_le_mul_of_nonneg_left (hlow j t) hδ.le))
  have hphase j : centeredPathPhase (u j) (v j) (m j)=edgePrimitive (u j)-edgePrimitive (v j) :=
    centeredPathPhase_root (huv j)
  simpa only [hphase] using h

end BourgadeHuang.RationalEdge
