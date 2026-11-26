import BourgadeHuang.CMS.CanonicalSectorialFamily

/-! Bounds for the actual canonical Volterra families, uniform in their
base point throughout the large chamber. Every constant is calculated from
the fixed coefficient budget, the positive gap, and the starting radius. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 100000

/-- Quantitative size of the actual affine fixed point, from its equation. -/
theorem norm_affineFixedPoint_le_of_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E) (b : E) {k B : ℝ}
    (hA : ‖A‖≤k) (hk : k<1) (hb : ‖b‖≤B) :
    ‖affineFixedPoint A b‖≤B/(1-k) := by
  have he := affineFixedPoint_equation (hA.trans_lt hk) b
  have hn : ‖affineFixedPoint A b‖≤B+k*‖affineFixedPoint A b‖ := by
    calc
      _=‖b+A (affineFixedPoint A b)‖ := congrArg norm he.symm
      _≤‖b‖+‖A (affineFixedPoint A b)‖ := norm_add_le _ _
      _≤B+k*‖affineFixedPoint A b‖ := add_le_add hb
        ((A.le_opNorm _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _)))
  apply (le_div_iff₀ (sub_pos.mpr hk)).mpr
  nlinarith

namespace RadialConstructionData
variable {d : ℕ} (P : RadialConstructionData d)

def uniformBlockBound : ℝ := RadialOperatorFamily.blockBound P.D (shiftedDirection P.sign)
def uniformInverseBound : ℝ := triangularInverseBound P.gap P.uniformBlockBound (d+1)
def uniformContractionBound : ℝ :=
  P.uniformInverseBound*P.radius⁻¹*P.gap⁻¹*(P.uniformBlockBound*P.uniformBlockBound+P.uniformBlockBound)
def uniformSolutionBound : ℝ :=
  P.uniformInverseBound*P.gap⁻¹*P.uniformBlockBound/(1-P.uniformContractionBound)

theorem uniformBlockBound_pos : 0<P.uniformBlockBound :=
  RadialOperatorFamily.blockBound_pos _ _

theorem uniformInverseBound_nonneg : 0≤P.uniformInverseBound :=
  triangularInverseBound_nonneg P.gap_pos.le P.uniformBlockBound_pos.le _

theorem uniformContractionBound_nonneg : 0≤P.uniformContractionBound := by
  unfold uniformContractionBound
  exact mul_nonneg (mul_nonneg (mul_nonneg P.uniformInverseBound_nonneg
    (inv_nonneg.mpr P.radius_pos.le)) (inv_nonneg.mpr P.gap_pos.le))
    (add_nonneg (mul_nonneg P.uniformBlockBound_pos.le P.uniformBlockBound_pos.le)
      P.uniformBlockBound_pos.le)

theorem uniformContractionBound_lt_one : P.uniformContractionBound<1 := by
  unfold uniformContractionBound
  rw [show P.uniformInverseBound*P.radius⁻¹*P.gap⁻¹*
      (P.uniformBlockBound*P.uniformBlockBound+P.uniformBlockBound)=
      (P.uniformInverseBound*P.gap⁻¹*(P.uniformBlockBound*P.uniformBlockBound+P.uniformBlockBound))/P.radius by ring]
  exact (div_lt_one P.radius_pos).mpr P.radius_large

theorem uniformSolutionBound_nonneg : 0≤P.uniformSolutionBound := by
  unfold uniformSolutionBound
  exact div_nonneg (mul_nonneg (mul_nonneg P.uniformInverseBound_nonneg
    (inv_nonneg.mpr P.gap_pos.le)) P.uniformBlockBound_pos.le)
    (sub_pos.mpr P.uniformContractionBound_lt_one).le

/-- The local coefficient bounds hold with one common, explicit budget. -/
theorem localFamily_operator_bounds {z : Point d}
    (hz : z∈OrderedGapDomain d P.radius) :
    ‖(P.localFamily z hz).nOp z‖≤P.uniformBlockBound ∧
    ‖(P.localFamily z hz).c01Op z‖≤P.uniformBlockBound ∧
    ‖(P.localFamily z hz).c10Op z‖≤P.uniformBlockBound ∧
    ‖(P.localFamily z hz).c11Op z‖≤P.uniformBlockBound := by
  obtain ⟨hn,h01,h10,h11⟩ := (P.localFamily z hz).norm_blocks_le P.D
    (shiftedDirection P.sign) P.sign (P.localFamily_spec z hz).2.2.self_of_nhds.1
    P.radius_pos (orderedGapDomain_subset_orderedDomain P.radius_pos.le hz)
    (orderedGapDomain_norm_separation hz)
  exact ⟨(norm_complexBoundedCoefficientOperator_le _).trans hn,
    (norm_complexBoundedCoefficientOperator_le _).trans h01,
    (norm_complexBoundedCoefficientOperator_le _).trans h10,
    (norm_complexBoundedCoefficientOperator_le _).trans h11⟩

/-- A uniform explicit contraction bound for every actual local operator. -/
theorem norm_localFamily_effectiveOperator_le {z : Point d}
    (hz : z∈OrderedGapDomain d P.radius) :
    ‖(P.localFamily z hz).effectiveOperator P.radius_pos P.gap_pos P.lam P.lam_gap z‖≤
      P.uniformContractionBound := by
  obtain ⟨hn,h01,h10,h11⟩ := P.localFamily_operator_bounds hz
  exact norm_eliminated_coupledVolterra_le P.radius_pos P.gap_pos P.uniformBlockBound_pos.le
    (freeForcingOperator P.radius_pos P.gap_pos P.lam P.lam_gap)
    (freeRemainderOperator P.radius_pos P.gap_pos P.lam P.lam_gap)
    (complexPrimitiveOperator (E:=EmptyVector) P.radius_pos)
    ((P.localFamily z hz).nOp z) ((P.localFamily z hz).c01Op z)
    ((P.localFamily z hz).c10Op z) ((P.localFamily z hz).c11Op z)
    (norm_freeForcingOperator_le P.radius_pos P.gap_pos P.lam P.lam_gap)
    (norm_freeRemainderOperator_le P.radius_pos P.gap_pos P.lam P.lam_gap)
    (norm_complexPrimitiveOperator_le P.radius_pos) hn h01 h10 h11 (d+1)

/-- The weighted family is uniformly bounded over the entire large chamber. -/
theorem norm_weightedFamily_uniform {z : Point d}
    (hz : z∈OrderedGapDomain d P.radius) :
    ‖P.weightedFamily z‖≤P.uniformSolutionBound := by
  let F := P.localFamily z hz
  let Q := freeForcingOperator P.radius_pos P.gap_pos P.lam P.lam_gap
  let T := triangularInverse (Q.comp (F.nOp z)) (d+1)
  have hQ : ‖Q‖≤P.gap⁻¹ := norm_freeForcingOperator_le _ _ _ _
  obtain ⟨hn,_,h10,_⟩ := P.localFamily_operator_bounds hz
  have hT : ‖T‖≤P.uniformInverseBound :=
    norm_triangularInverse_comp_le P.gap_pos P.uniformBlockBound_pos.le Q (F.nOp z) hQ hn _
  have he : ‖BoundedContinuousFunction.const (Tail P.radius) (1:EmptyVector)‖≤1 := by
    exact (BoundedContinuousFunction.norm_const_le _).trans (by
      apply pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr
      intro u
      simp)
  have hb : ‖T (Q (F.c10Op z (BoundedContinuousFunction.const _ (1:EmptyVector))))‖≤
      P.uniformInverseBound*P.gap⁻¹*P.uniformBlockBound := by
    have hinner : ‖F.c10Op z (BoundedContinuousFunction.const _ (1:EmptyVector))‖≤P.uniformBlockBound :=
      ((F.c10Op z).le_opNorm _).trans (by
        simpa only [mul_one] using mul_le_mul h10 he (norm_nonneg _) P.uniformBlockBound_pos.le)
    have hmid : ‖Q (F.c10Op z (BoundedContinuousFunction.const _ (1:EmptyVector)))‖≤
        P.gap⁻¹*P.uniformBlockBound :=
      (Q.le_opNorm _).trans (mul_le_mul hQ hinner (norm_nonneg _) (inv_nonneg.mpr P.gap_pos.le))
    exact (T.le_opNorm _).trans ((mul_le_mul hT hmid (norm_nonneg _)
      P.uniformInverseBound_nonneg).trans_eq (by ring))
  have h := norm_affineFixedPoint_le_of_bound
    (F.effectiveOperator P.radius_pos P.gap_pos P.lam P.lam_gap z) _
    (P.norm_localFamily_effectiveOperator_le hz) P.uniformContractionBound_lt_one hb
  simpa only [weightedFamily,dif_pos hz,RadialOperatorFamily.weightedSolution,
    coupledVolterraSolution,triangularAffineFixedPoint,RadialOperatorFamily.effectiveOperator,
    F,Q,T,uniformSolutionBound] using h

/-- Reciprocal-tail bounds use the same constant for every base point. -/
theorem family_values_uniform {z : Point d}
    (hz : z∈OrderedGapDomain d P.radius) (t : Tail P.radius) :
    ‖P.emptyFamily z t-1‖≤P.uniformBlockBound*P.uniformSolutionBound/t.val ∧
      ‖P.nonemptyFamily z t‖≤P.uniformSolutionBound/t.val := by
  have ht : 0≤t.val := (P.radius_pos.trans_le t.property).le
  have hZ := P.norm_weightedFamily_uniform hz
  constructor
  · let F := P.localFamily z hz
    have h01 := (P.localFamily_operator_bounds hz).2.1
    have he : P.emptyFamily z=BoundedContinuousFunction.const _ (1:EmptyVector)+
        boundedUnweight P.radius_pos (complexPrimitiveOperator P.radius_pos
          (F.c01Op z (P.weightedFamily z))) := by
      simp only [emptyFamily,weightedFamily,dif_pos hz,F,
        RadialOperatorFamily.normalizedEmpty,coupledEmptyComponent]
    rw [he]
    change ‖(1:EmptyVector)+boundedUnweight P.radius_pos _ t-1‖≤_
    rw [add_sub_cancel_left]
    apply (norm_unweight_le P.radius_pos _ t).trans
    apply div_le_div_of_nonneg_right _ ht
    have hprim := (complexPrimitiveOperator (E:=EmptyVector) P.radius_pos).le_opNorm
      (F.c01Op z (P.weightedFamily z))
    apply hprim.trans
    have hp : ‖complexPrimitiveOperator (E:=EmptyVector) P.radius_pos‖≤1 :=
      norm_complexPrimitiveOperator_le _
    have hb := ((F.c01Op z).le_opNorm _).trans
      (mul_le_mul h01 hZ (norm_nonneg _) P.uniformBlockBound_pos.le)
    simpa only [one_mul] using mul_le_mul hp hb (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
  · exact (norm_unweight_le P.radius_pos _ t).trans (div_le_div_of_nonneg_right hZ ht)

/-- Uniform bounds in the Banach norms, including the complete empty
correction rather than just one scalar evaluation. -/
theorem family_norms_uniform {z : Point d}
    (hz : z∈OrderedGapDomain d P.radius) :
    ‖P.emptyFamily z-BoundedContinuousFunction.const _ (1:EmptyVector)‖≤
        P.uniformBlockBound*P.uniformSolutionBound/P.radius ∧
      ‖P.nonemptyFamily z‖≤P.uniformSolutionBound/P.radius := by
  constructor
  · apply (BoundedContinuousFunction.norm_le (div_nonneg (mul_nonneg P.uniformBlockBound_pos.le P.uniformSolutionBound_nonneg) P.radius_pos.le :
        0≤P.uniformBlockBound*P.uniformSolutionBound/P.radius)).mpr
    intro t
    exact (P.family_values_uniform hz t).1.trans
      (div_le_div_of_nonneg_left (mul_nonneg P.uniformBlockBound_pos.le
        P.uniformSolutionBound_nonneg) P.radius_pos t.property)
  · apply (BoundedContinuousFunction.norm_le (div_nonneg P.uniformSolutionBound_nonneg P.radius_pos.le)).mpr
    intro t
    exact (P.family_values_uniform hz t).2.trans
      (div_le_div_of_nonneg_left P.uniformSolutionBound_nonneg P.radius_pos t.property)

/-- With a fixed contraction margin, the weighted bound is independent of
any increase in the starting radius. -/
theorem uniformSolutionBound_le_of_margin {k : ℝ}
    (hk : P.uniformContractionBound≤k) (hk1 : k<1) :
    P.uniformSolutionBound≤P.uniformInverseBound*P.gap⁻¹*P.uniformBlockBound/(1-k) := by
  apply div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg P.uniformInverseBound_nonneg
    (inv_nonneg.mpr P.gap_pos.le)) P.uniformBlockBound_pos.le)
    (sub_pos.mpr hk1) (by linarith)

/-- Doubling the explicit threshold gives a common one-half contraction
margin, suitable for letting the sectorial gap tend to infinity. -/
theorem uniformContractionBound_le_half
    (hlarge : 2*(P.uniformInverseBound*P.gap⁻¹*
      (P.uniformBlockBound*P.uniformBlockBound+P.uniformBlockBound))≤P.radius) :
    P.uniformContractionBound≤1/2 := by
  unfold uniformContractionBound
  rw [show P.uniformInverseBound*P.radius⁻¹*P.gap⁻¹*
      (P.uniformBlockBound*P.uniformBlockBound+P.uniformBlockBound)=
      (P.uniformInverseBound*P.gap⁻¹*(P.uniformBlockBound*P.uniformBlockBound+P.uniformBlockBound))/P.radius by ring]
  apply (div_le_iff₀ P.radius_pos).mpr
  linarith

/-- The uniform solution budget at all sufficiently large radii has no
remaining dependence on the radius. -/
theorem uniformSolutionBound_le_twice
    (hlarge : 2*(P.uniformInverseBound*P.gap⁻¹*
      (P.uniformBlockBound*P.uniformBlockBound+P.uniformBlockBound))≤P.radius) :
    P.uniformSolutionBound≤2*P.uniformInverseBound*P.gap⁻¹*P.uniformBlockBound := by
  apply (P.uniformSolutionBound_le_of_margin (P.uniformContractionBound_le_half hlarge)
    (by norm_num : (1:ℝ)/2<1)).trans_eq
  ring

end RadialConstructionData
end BourgadeHuang.CMS
