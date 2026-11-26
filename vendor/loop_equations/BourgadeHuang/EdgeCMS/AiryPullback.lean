import BourgadeHuang.EdgeCMS.AiryInverse
import BourgadeHuang.CMS.SquareFreeJets

/-! Coordinatewise chain rules for the genuine multivariable Airy map. -/
noncomputable section
open Filter Set
open scoped Topology
namespace BourgadeHuang.EdgeCMS
open CMS

def airyCoordinates {d : ℕ} (z : Point d) : Point d := fun i => airyCoordinate (z i)

def airyInverseCoordinates {d : ℕ} (y : Point d) : Point d := fun i => airyInverse (y i)

theorem airyCoordinates_update {d : ℕ} (z : Point d) (i : Fin d) (w : ℂ) :
    airyCoordinates (Function.update z i w) =
      Function.update (airyCoordinates z) i (airyCoordinate w) := by
  funext j
  by_cases h : j = i
  · subst j; simp [airyCoordinates]
  · simp [airyCoordinates, Function.update_of_ne h, h]

theorem analyticAt_coordinateSlice {d : ℕ} {F : Point d → ℂ} {z : Point d}
    (hF : AnalyticAt ℂ F z) (i : Fin d) :
    AnalyticAt ℂ (fun w => F (Function.update z i w)) (z i) := by
  have hu : AnalyticAt ℂ (fun w : ℂ => Function.update z i w) (z i) := by
    apply analyticAt_pi_iff.mpr
    intro j
    by_cases h : j = i
    · subst j; simpa using (analyticAt_id : AnalyticAt ℂ (fun w : ℂ => w) (z i))
    · simpa [Function.update_of_ne h] using
        (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => z j) (z i))
  have hF' : AnalyticAt ℂ F (Function.update z i (z i)) := by simpa using hF
  exact hF'.comp hu

theorem analyticAt_airyCoordinates {d : ℕ} {z : Point d}
    (hz : ∀ i, z i ∈ Complex.slitPlane) : AnalyticAt ℂ (@airyCoordinates d) z := by
  apply analyticAt_pi_iff.mpr
  intro i
  exact (analyticAt_airyCoordinate (hz i)).comp (f := fun w : Point d => w i)
    ((ContinuousLinearMap.proj i : Point d →L[ℂ] ℂ).analyticAt z)

theorem analyticAt_airyInverseCoordinates {d : ℕ} {y : Point d}
    (hy : ∀ i, y i ∈ Complex.slitPlane) : AnalyticAt ℂ (@airyInverseCoordinates d) y := by
  apply analyticAt_pi_iff.mpr
  intro i
  exact (analyticAt_airyInverse (hy i)).comp (f := fun w : Point d => w i)
    ((ContinuousLinearMap.proj i : Point d →L[ℂ] ℂ).analyticAt y)

theorem airyCoordinates_inverseCoordinates {d : ℕ} {y : Point d}
    (hy : ∀ i, y i ≠ 0) : airyCoordinates (airyInverseCoordinates y) = y := by
  funext i
  exact airyCoordinate_airyInverse (hy i)

theorem airyInverseCoordinates_coordinates {d : ℕ} {z : Point d}
    (hz : ∀ i, 0 < (z i).re) : airyInverseCoordinates (airyCoordinates z) = z := by
  funext i
  exact airyInverse_airyCoordinate (hz i)

theorem coordDeriv_airy_pullback {d : ℕ} {F : Point d → ℂ} {z : Point d}
    (hF : AnalyticAt ℂ F (airyCoordinates z)) (i : Fin d)
    (hz : z i ∈ Complex.slitPlane) :
    coordDeriv i (fun w => F (airyCoordinates w)) z =
      root (z i) * coordDeriv i F (airyCoordinates z) := by
  unfold coordDeriv
  simp only [airyCoordinates_update]
  exact airyCoordinate_first_chain hz (analyticAt_coordinateSlice hF i).differentiableAt

/-- Iterating the genuine coordinate derivative twice is exactly the second
ordinary derivative of the corresponding coordinate slice. -/
theorem secondPartial_eq_second_slice {d : ℕ} (F : Point d → ℂ) (z : Point d)
    (i : Fin d) : secondPartial i F z =
      deriv (deriv (fun w => F (Function.update z i w))) (z i) := by
  simp only [secondPartial, coordDeriv, Function.update_self, Function.update_idem]

theorem secondPartial_airy_pullback {d : ℕ} {F : Point d → ℂ} {z : Point d}
    (hF : AnalyticAt ℂ F (airyCoordinates z)) (i : Fin d)
    (hz : z i ∈ Complex.slitPlane) :
    secondPartial i (fun w => F (airyCoordinates w)) z =
      z i * secondPartial i F (airyCoordinates z) +
        coordDeriv i F (airyCoordinates z) / (2 * root (z i)) := by
  rw [secondPartial_eq_second_slice, secondPartial_eq_second_slice]
  simp only [airyCoordinates_update, coordDeriv]
  exact airyCoordinate_second_chain hz (analyticAt_coordinateSlice hF i)

end BourgadeHuang.EdgeCMS
