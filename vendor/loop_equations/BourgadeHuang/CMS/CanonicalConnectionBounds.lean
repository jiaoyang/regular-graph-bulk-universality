import BourgadeHuang.CMS.CanonicalRayCovariance
import BourgadeHuang.CMS.ConnectionTailBounds

/-! Actual uniform decay of the connection applied to the canonical radial
vector. The constants are obtained from its constructed bounded families. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1000000
namespace RadialConstructionData
variable {d : ℕ} (P : RadialConstructionData d)

/-- Time-parametrized form of exact base-point covariance. -/
theorem canonicalJet_sectorialRay {z : Point d} (hz : z∈OrderedGapDomain d P.radius)
    (t : Tail P.radius) (S : Finset (Fin d)) :
    P.canonicalJet (sectorialRay P.sign z P.radius t) S=
      ((t.val:ℂ)^S.card)⁻¹*P.fullFamily z t S := by
  simpa only [sectorialRay,add_sub_cancel] using
    P.canonicalJet_shift hz (sub_nonneg.mpr t.property) S

/-- Full-vector boundedness and the stronger nonempty normalization. -/
theorem fullFamily_bounds {z : Point d} (hz : z∈OrderedGapDomain d P.radius) :
    ∃B0 B1 : ℝ,0≤B0 ∧ 0≤B1 ∧ ∀t : Tail P.radius,
      (∀S,‖P.fullFamily z t S‖≤B0) ∧
      ∀S : NonemptySubset d,‖P.fullFamily z t S.val‖≤B1/t.val := by
  obtain ⟨B1,hB1,hB⟩ := P.families_reciprocal_bound hz
  refine ⟨max ‖P.emptyFamily z‖ ‖P.nonemptyFamily z‖,B1,by positivity,hB1,?_⟩
  intro t
  constructor
  · intro S
    by_cases hS : S.Nonempty
    · change ‖P.fullFamily z t (⟨S,hS⟩ : NonemptySubset d).val‖≤_
      rw [fullFamily_nonempty,tailExtension_apply]
      exact ((norm_le_pi_norm (P.nonemptyFamily z t) ⟨S,hS⟩).trans ((P.nonemptyFamily z).norm_coe_le_norm t)).trans (le_max_right _ _)
    · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      rw [fullFamily_empty,tailExtension_apply]
      exact ((norm_le_pi_norm (P.emptyFamily z t) ()).trans ((P.emptyFamily z).norm_coe_le_norm t)).trans (le_max_left _ _)
  · intro S
    rw [fullFamily_nonempty,tailExtension_apply]
    exact (norm_le_pi_norm (P.nonemptyFamily z t) S).trans (hB t).2

/-- Every scaled connection row decays at least as t⁻¹, uniformly along the
entire actual ray. No compatibility of the candidate jets is assumed. -/
theorem connection_action_reciprocal_bound {z : Point d}
    (hz : z∈OrderedGapDomain d P.radius) (i : Fin d) :
    ∃C : ℝ,0≤C ∧ ∀t : Tail P.radius,∀S : Finset (Fin d),
      ‖(t.val:ℂ)^S.card*(∑T : Finset (Fin d),
        P.D.connection i (sectorialRay P.sign z P.radius t) S T*
          P.canonicalJet (sectorialRay P.sign z P.radius t) T)‖≤C/t.val := by
  classical
  obtain ⟨B0,B1,hB0,hB1,hB⟩ := P.fullFamily_bounds hz
  let K : Finset (Fin d) → ℝ := fun S =>
    ‖P.D.phase i‖*B1+
      (Fintype.card (NonemptySubset d):ℝ)*SquareFreeTerm.rowBound (P.D.correctionRow S i)*B1+
      (Fintype.card (Finset (Fin d)):ℝ)*(1+SquareFreeTerm.rowBound (P.D.correctionRow S i))*B0
  have hK : ∀S,0≤K S := by
    intro S
    dsimp only [K]
    have hM := SquareFreeTerm.rowBound_nonneg (P.D.correctionRow S i)
    positivity
  refine ⟨∑S,K S,Finset.sum_nonneg (fun S _=>hK S),?_⟩
  intro t S
  simp_rw [P.canonicalJet_sectorialRay hz t]
  have ht := P.radius_pos.trans_le t.property
  have hs := sectorialRay_separation P.sign
    (orderedGapDomain_subset_orderedDomain P.radius_pos.le hz)
    (orderedGapDomain_norm_separation hz) t.property
  have hb := P.D.norm_scaled_connection_le i S (sectorialRay P.sign z P.radius t)
    (P.fullFamily z t) ht hB0 hB1 hs (hB t).1 (hB t).2
  exact hb.trans (div_le_div_of_nonneg_right
    (Finset.single_le_sum (fun S _=>hK S) (Finset.mem_univ S)) ht.le)

end RadialConstructionData
end BourgadeHuang.CMS
