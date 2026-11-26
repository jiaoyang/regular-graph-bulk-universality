import BourgadeHuang.OrthogonalRatioAnalytic

/-! Common series for each actual coordinate slice of the orthogonal family. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

set_option maxHeartbeats 1000000 in
theorem hasAnchoredPowerSeries_orthogonalRatios_numerator {q : ℕ}
    (u v w : Fin q → ℂ) (hwv : ∀ j, SameOpenHalfPlane (w j) (v j)) (i : Fin q) :
    HasAnchoredPowerSeries (fun s z => orthogonalCharacteristicRatios s (Function.update u i z) v w) (u i) := by
  let L : ℂ →L[ℂ] OrthogonalRatioPoint q := (ContinuousLinearMap.single ℂ (fun _ : Fin q => ℂ) i).prod (0 : ℂ →L[ℂ] ((Fin q → ℂ) × (Fin q → ℂ)))
  let b : OrthogonalRatioPoint q := (Function.update u i 0,v,w)
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro z
    simp [L,Prod.norm_def,Pi.norm_single]
  have hmap (z : ℂ) : L z+b = (Function.update u i z,v,w) := by
    ext j <;> simp [L,b,Pi.single_apply,Function.update_apply]
    split_ifs <;> simp_all
  have hcenter : L (u i)+b = (u,v,w) := by
    rw [hmap,Function.update_eq_self]
  have hp : HasAnchoredPowerSeries (fun s (p : OrthogonalRatioPoint q) =>
      orthogonalCharacteristicRatios s p.1 p.2.1 p.2.2) (L (u i)+b) := by
    rw [hcenter]
    exact hasAnchoredPowerSeries_orthogonalRatios_joint u v w hwv
  simpa only [hmap] using hp.comp_affine L hL b (u i)

set_option maxHeartbeats 1000000 in
theorem hasAnchoredPowerSeries_orthogonalRatios_firstDenominator {q : ℕ}
    (u v w : Fin q → ℂ) (hwv : ∀ j, SameOpenHalfPlane (w j) (v j)) (i : Fin q) :
    HasAnchoredPowerSeries (fun s z => orthogonalCharacteristicRatios s u (Function.update v i z) w) (v i) := by
  let L : ℂ →L[ℂ] OrthogonalRatioPoint q := (0 : ℂ →L[ℂ] (Fin q → ℂ)).prod ((ContinuousLinearMap.single ℂ (fun _ : Fin q => ℂ) i).prod (0 : ℂ →L[ℂ] (Fin q → ℂ)))
  let b : OrthogonalRatioPoint q := (u,Function.update v i 0,w)
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro z
    simp [L,Prod.norm_def,Pi.norm_single]
  have hmap (z : ℂ) : L z+b = (u,Function.update v i z,w) := by
    ext j <;> simp [L,b,Pi.single_apply,Function.update_apply]
    split_ifs <;> simp_all
  have hcenter : L (v i)+b = (u,v,w) := by
    rw [hmap,Function.update_eq_self]
  have hp : HasAnchoredPowerSeries (fun s (p : OrthogonalRatioPoint q) =>
      orthogonalCharacteristicRatios s p.1 p.2.1 p.2.2) (L (v i)+b) := by
    rw [hcenter]
    exact hasAnchoredPowerSeries_orthogonalRatios_joint u v w hwv
  simpa only [hmap] using hp.comp_affine L hL b (v i)

set_option maxHeartbeats 1000000 in
theorem hasAnchoredPowerSeries_orthogonalRatios_secondDenominator {q : ℕ}
    (u v w : Fin q → ℂ) (hwv : ∀ j, SameOpenHalfPlane (w j) (v j)) (i : Fin q) :
    HasAnchoredPowerSeries (fun s z => orthogonalCharacteristicRatios s u v (Function.update w i z)) (w i) := by
  let L : ℂ →L[ℂ] OrthogonalRatioPoint q := (0 : ℂ →L[ℂ] (Fin q → ℂ)).prod ((0 : ℂ →L[ℂ] (Fin q → ℂ)).prod (ContinuousLinearMap.single ℂ (fun _ : Fin q => ℂ) i))
  let b : OrthogonalRatioPoint q := (u,v,Function.update w i 0)
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro z
    simp [L,Prod.norm_def,Pi.norm_single]
  have hmap (z : ℂ) : L z+b = (u,v,Function.update w i z) := by
    ext j <;> simp [L,b,Pi.single_apply,Function.update_apply]
    split_ifs <;> simp_all
  have hcenter : L (w i)+b = (u,v,w) := by
    rw [hmap,Function.update_eq_self]
  have hp : HasAnchoredPowerSeries (fun s (p : OrthogonalRatioPoint q) =>
      orthogonalCharacteristicRatios s p.1 p.2.1 p.2.2) (L (w i)+b) := by
    rw [hcenter]
    exact hasAnchoredPowerSeries_orthogonalRatios_joint u v w hwv
  simpa only [hmap] using hp.comp_affine L hL b (w i)

end BourgadeHuang
