import BourgadeHuang.CMS.CanonicalConnectionBounds
import BourgadeHuang.CMS.CanonicalJetDerivativeCovariance
import BourgadeHuang.CMS.SectorialObstruction

/-! Quantitative decay of the actual coordinate defects of the constructed
canonical family, before their vanishing is inferred from radial uniqueness. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1000000
namespace RadialConstructionData
variable {d : ℕ} (P : RadialConstructionData d)

/-- Every degree-scaled coordinate obstruction is O(t⁻¹), with a common
constant for all subsets along the complete ray. -/
theorem obstruction_scaled_bound {z : Point d}
    (hz : z∈OrderedGapDomain d P.radius) (i : Fin d) :
    ∃C : ℝ,0≤C ∧ ∀t : Tail P.radius,∀S : Finset (Fin d),
      ‖(t.val:ℂ)^S.card*P.D.obstruction P.canonicalJet i S
        (sectorialRay P.sign z P.radius t)‖≤C/t.val := by
  obtain ⟨C1,hC1,h1⟩ := P.canonicalJet_scaled_coordinate_bound hz
  obtain ⟨C2,hC2,h2⟩ := P.connection_action_reciprocal_bound hz i
  refine ⟨C1+C2,add_nonneg hC1 hC2,?_⟩
  intro t S
  simp only [SectorialData.obstruction,coordinateObstruction,mul_sub]
  exact (norm_sub_le _ _).trans ((add_le_add (h1 t i S) (h2 t S)).trans_eq (by ring))

/-- Continuity of each actual obstruction along the entire closed tail. -/
theorem continuous_obstruction_ray {z : Point d}
    (hz : z∈OrderedGapDomain d P.radius) (i : Fin d) (S : Finset (Fin d)) :
    Continuous (fun t : Tail P.radius=>P.D.obstruction P.canonicalJet i S
      (sectorialRay P.sign z P.radius t)) := by
  have hr : Continuous (fun t : Tail P.radius=>sectorialRay P.sign z P.radius t) := by
    apply continuous_pi
    intro j
    change Continuous (fun t : Tail P.radius=>z j+((t.val-P.radius:ℝ):ℂ)*shiftedDirection P.sign j)
    fun_prop
  have ha := P.D.analyticOnNhd_obstruction P.canonicalJet
    (orderedGapDomain_subset_orderedDomain P.radius_pos.le) P.analyticOnNhd_canonicalJet i S
  exact continuous_iff_continuousAt.mpr (fun t =>
    (ha _ (shiftedRay_mem_orderedGapDomain P.sign hz (sub_nonneg.mpr t.property))).continuousAt.comp
      (f:=fun t : Tail P.radius=>sectorialRay P.sign z P.radius t) hr.continuousAt)

end RadialConstructionData
end BourgadeHuang.CMS
