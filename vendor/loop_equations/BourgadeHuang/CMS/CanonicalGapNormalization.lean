import BourgadeHuang.CMS.CanonicalRadiusIndependence

/-! Genuine sectorial normalization in all large-gap directions. Radius
independence allows the actual canonical germ to be estimated using an
arbitrarily enlarged starting radius with one fixed contraction margin. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 100000
namespace RadialConstructionData
variable {d : ℕ} (P : RadialConstructionData d)

/-- The fixed threshold before the reciprocal radius factor. -/
def uniformRadiusThreshold : ℝ :=
  P.uniformInverseBound*P.gap⁻¹*(P.uniformBlockBound*P.uniformBlockBound+P.uniformBlockBound)

/-- Changing only the auxiliary starting radius is an actual construction
of the same analytic system. -/
def withRadius (R : ℝ) (hR : 0<R) (hlarge : P.uniformRadiusThreshold<R) :
    RadialConstructionData d where
  D := P.D
  sign := P.sign
  radius := R
  gap := P.gap
  radius_pos := hR
  gap_pos := P.gap_pos
  lam := P.lam
  lam_eq := P.lam_eq
  lam_gap := P.lam_gap
  radius_large := hlarge

/-- The normalized scalar germ tends to one quantitatively on every large
chamber, with a numerator independent of its radius. -/
theorem normalizedGerm_gap_bound {R : ℝ} (hR : 0<R)
    (hlarge : 2*P.uniformRadiusThreshold≤R) {z : Point d}
    (hzP : z∈OrderedGapDomain d P.radius) (hzR : z∈OrderedGapDomain d R) :
    ‖P.normalizedGerm z-1‖≤
      (P.uniformBlockBound*(2*P.uniformInverseBound*P.gap⁻¹*P.uniformBlockBound))/R := by
  have hstrict : P.uniformRadiusThreshold<R := by linarith
  let Q := P.withRadius R hR hstrict
  rw [P.normalizedGerm_eq Q rfl rfl hzP hzR]
  have hq := Q.uniformSolutionBound_le_twice hlarge
  have hb := (norm_le_pi_norm (Q.emptyFamily z (⟨R,le_rfl⟩ : Tail Q.radius)-1) ()).trans
    (Q.family_values_uniform hzR ⟨R,le_rfl⟩).1
  exact hb.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hq P.uniformBlockBound_pos.le) hR.le)

/-- Every nonempty canonical square-free component has the corresponding
extra inverse powers of the large chamber gap. -/
theorem canonicalJet_gap_bound {R : ℝ} (hR : 0<R)
    (hlarge : 2*P.uniformRadiusThreshold≤R) {z : Point d}
    (hzP : z∈OrderedGapDomain d P.radius) (hzR : z∈OrderedGapDomain d R)
    (S : NonemptySubset d) :
    ‖P.canonicalJet z S.val‖≤
      (2*P.uniformInverseBound*P.gap⁻¹*P.uniformBlockBound)/R^(S.val.card+1) := by
  have hstrict : P.uniformRadiusThreshold<R := by linarith
  let Q := P.withRadius R hR hstrict
  rw [P.canonicalJet_eq Q rfl rfl hzP hzR]
  have hq := Q.uniformSolutionBound_le_twice hlarge
  have hb := ((norm_le_pi_norm (Q.nonemptyFamily z (⟨R,le_rfl⟩ : Tail Q.radius)) S).trans
    (Q.family_values_uniform hzR ⟨R,le_rfl⟩).2).trans
    (div_le_div_of_nonneg_right hq hR.le)
  change ‖((R:ℂ)^S.val.card)⁻¹*Q.fullFamily z R S.val‖≤_
  rw [fullFamily_nonempty]
  change ‖((R:ℂ)^S.val.card)⁻¹*tailExtension (Q.nonemptyFamily z)
    (⟨R,le_rfl⟩ : Tail Q.radius).val S‖≤_
  rw [tailExtension_apply,norm_mul,norm_inv,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos hR]
  apply (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (pow_nonneg hR.le _))).trans_eq
  change (R^S.val.card)⁻¹*((2*P.uniformInverseBound*P.gap⁻¹*P.uniformBlockBound)/R)=_
  rw [pow_succ]
  field_simp
  ring

/-- Genuine normalization along any filter for which all ordered real gaps
tend to infinity; no single-ray restriction remains. -/
theorem normalizedGerm_tendsto_one_of_gaps {α : Type*} {l : Filter α}
    {z : α → Point d} (hgap : ∀R : ℝ,∀ᶠx in l,z x∈OrderedGapDomain d R) :
    Tendsto (fun x=>P.normalizedGerm (z x)) l (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let C := P.uniformBlockBound*(2*P.uniformInverseBound*P.gap⁻¹*P.uniformBlockBound)
  have hC : 0≤C := mul_nonneg P.uniformBlockBound_pos.le
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) P.uniformInverseBound_nonneg)
      (inv_nonneg.mpr P.gap_pos.le)) P.uniformBlockBound_pos.le)
  let R := max (2*P.uniformRadiusThreshold) (C/ε)+1
  have hR : 0<R := by dsimp [R];have := le_max_right (2*P.uniformRadiusThreshold) (C/ε);positivity
  have hlarge : 2*P.uniformRadiusThreshold≤R := by
    dsimp [R]
    linarith [le_max_left (2*P.uniformRadiusThreshold) (C/ε)]
  have hsmall : C/R<ε := by
    apply (div_lt_iff₀ hR).mpr
    have hh : C/ε<R := by dsimp [R];linarith [le_max_right (2*P.uniformRadiusThreshold) (C/ε)]
    have hh' := (div_lt_iff₀ hε).mp hh
    nlinarith
  filter_upwards [hgap P.radius,hgap R] with x hxP hxR
  rw [dist_eq_norm]
  exact (P.normalizedGerm_gap_bound hR hlarge hxP hxR).trans_lt hsmall

end RadialConstructionData
end BourgadeHuang.CMS
