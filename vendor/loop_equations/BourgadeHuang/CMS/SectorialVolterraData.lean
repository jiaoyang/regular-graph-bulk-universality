import BourgadeHuang.CMS.SectorialRadialBounds
import BourgadeHuang.CMS.SectorialPhysicalGap
import BourgadeHuang.CMS.NormalizedRadialSolution

/-! Bounded operator data for the genuine sectorial Volterra problem. -/
noncomputable section
open scoped BigOperators Topology BoundedContinuousFunction
open Set
namespace BourgadeHuang.CMS

section FiniteOperators
variable {J : Type*} [Fintype J]

def finiteRowOperator (a : J → ℂ) : (J → ℂ) →L[ℝ] ℂ :=
  ∑j,a j • ContinuousLinearMap.proj j

@[simp] theorem finiteRowOperator_apply (a : J → ℂ) (v : J → ℂ) :
    finiteRowOperator a v=∑j,a j*v j := by
  simp [finiteRowOperator,ContinuousLinearMap.sum_apply]

def finiteColumnOperator (a : J → ℂ) : ℂ →L[ℝ] (J → ℂ) :=
  ContinuousLinearMap.pi (fun j => a j • ContinuousLinearMap.id ℝ ℂ)

omit [Fintype J] in
@[simp] theorem finiteColumnOperator_apply (a : J → ℂ) (v : ℂ) (j : J) :
    finiteColumnOperator a v j=a j*v := rfl

theorem continuous_finiteRowOperator : Continuous (finiteRowOperator (J := J)) := by
  apply continuous_finset_sum
  intro j _
  exact (continuous_apply j).smul continuous_const

theorem continuous_finiteColumnOperator : Continuous (finiteColumnOperator (J := J)) := by
  classical
  have he : finiteColumnOperator (J := J)=fun a => ∑j,a j • ContinuousLinearMap.single ℝ (fun _ : J => ℂ) j := by
    funext a
    ext v j
    simp [finiteColumnOperator,ContinuousLinearMap.sum_apply,Finset.sum_apply,Pi.single_apply]
  rw [he]
  apply continuous_finset_sum
  intro j _
  exact (continuous_apply j).smul continuous_const

theorem norm_finiteRowOperator_le {a : J → ℂ} {B : ℝ} (hB : 0≤B)
    (ha : ∀j,‖a j‖≤B) : ‖finiteRowOperator a‖≤(Fintype.card J:ℝ)*B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hB)
  intro v
  rw [finiteRowOperator_apply]
  calc
    _≤∑j,‖a j*v j‖ := norm_sum_le _ _
    _≤∑_j : J,B*‖v‖ := Finset.sum_le_sum (fun j _ => by
      rw [norm_mul]
      exact mul_le_mul (ha j) (norm_le_pi_norm v j) (norm_nonneg _) hB)
    _=_ := by simp [mul_assoc]

theorem norm_finiteColumnOperator_le {a : J → ℂ} {B : ℝ} (hB : 0≤B)
    (ha : ∀j,‖a j‖≤B) : ‖finiteColumnOperator a‖≤B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hB (norm_nonneg v))).mpr
  intro j
  rw [finiteColumnOperator_apply,norm_mul]
  exact mul_le_mul_of_nonneg_right (ha j) (norm_nonneg _)

end FiniteOperators

abbrev NonemptySubset (d : ℕ) := {S : Finset (Fin d) // S.Nonempty}

namespace SectorialData

variable {d : ℕ} (D : SectorialData d) (σ : Fin d → Sign) {z : Point d} {R : ℝ}
  (hR : 0<R) (hz : z∈OrderedDomain d) (hsep : ∀i j,i≠j→R≤‖z i-z j‖)

def boundedPrincipalRemainder : Tail R →ᵇ (NonemptySubset d → NonemptySubset d → ℂ) :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t S T => D.principalRemainder (shiftedDirection σ) (sectorialRay σ z R t) (t:ℝ) S.val T.val)
    (continuous_pi (fun S => continuous_pi (fun T => D.continuous_principalRemainder_ray _ _ _ σ hz)))
    (D.matrixBound (shiftedDirection σ)) (fun t => by
      apply (pi_norm_le_iff_of_nonneg (D.matrixBound_pos _).le).mpr
      intro S
      apply (pi_norm_le_iff_of_nonneg (D.matrixBound_pos _).le).mpr
      intro T
      exact (D.norm_principalRemainder_le _ _ _ (hR.trans_le t.property)
        (sectorialRay_separation σ hz hsep t.property)).trans (D.principalRowBound_le_matrixBound _ _))

theorem boundedPrincipalRemainder_degree (t : Tail R) (S T : NonemptySubset d)
    (hT : ¬T.val.card<S.val.card) : D.boundedPrincipalRemainder σ hR hz hsep t S T=0 :=
  D.principalRemainder_strict_degree _ _ _ _ _ hT

theorem norm_boundedPrincipalRemainder_le :
    ‖D.boundedPrincipalRemainder σ hR hz hsep‖≤D.matrixBound (shiftedDirection σ) := by
  apply (BoundedContinuousFunction.norm_le (D.matrixBound_pos _).le).mpr
  intro t
  apply (pi_norm_le_iff_of_nonneg (D.matrixBound_pos _).le).mpr
  intro S
  apply (pi_norm_le_iff_of_nonneg (D.matrixBound_pos _).le).mpr
  intro T
  exact (D.norm_principalRemainder_le _ _ _ (hR.trans_le t.property)
    (sectorialRay_separation σ hz hsep t.property)).trans (D.principalRowBound_le_matrixBound _ _)

include hR hz hsep in
private theorem radial_entry_le (t : Tail R) (S T : Finset (Fin d)) :
    ‖D.radialRemainder (shiftedDirection σ) (sectorialRay σ z R t) (t:ℝ) S T‖≤
      D.matrixBound (shiftedDirection σ) :=
  (D.norm_radialRemainder_le _ _ _ (hR.trans_le t.property)
    (sectorialRay_separation σ hz hsep t.property)).trans (D.remainderRowBound_le_matrixBound _ _)

def boundedC01 : Tail R →ᵇ ((NonemptySubset d → ℂ) →L[ℝ] ℂ) :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => finiteRowOperator (fun T : NonemptySubset d =>
      D.radialRemainder (shiftedDirection σ) (sectorialRay σ z R t) (t:ℝ) ∅ T.val))
    (continuous_finiteRowOperator.comp (continuous_pi (fun T => D.continuous_radialRemainder_ray _ ∅ T.val σ hz)))
    ((Fintype.card (NonemptySubset d):ℝ)*D.matrixBound (shiftedDirection σ))
    (fun t => norm_finiteRowOperator_le (D.matrixBound_pos _).le
      (fun T => D.radial_entry_le σ hR hz hsep t ∅ T.val))

def boundedC10 : Tail R →ᵇ (ℂ →L[ℝ] (NonemptySubset d → ℂ)) :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => finiteColumnOperator (fun S : NonemptySubset d =>
      D.radialRemainder (shiftedDirection σ) (sectorialRay σ z R t) (t:ℝ) S.val ∅))
    (continuous_finiteColumnOperator.comp (continuous_pi (fun S => D.continuous_radialRemainder_ray _ S.val ∅ σ hz)))
    (D.matrixBound (shiftedDirection σ))
    (fun t => norm_finiteColumnOperator_le (D.matrixBound_pos _).le
      (fun S => D.radial_entry_le σ hR hz hsep t S.val ∅))

def boundedC11 : Tail R →ᵇ ((NonemptySubset d → ℂ) →L[ℝ] (NonemptySubset d → ℂ)) :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => finiteMatrixOperator (fun S T : NonemptySubset d =>
      D.radialRemainder (shiftedDirection σ) (sectorialRay σ z R t) (t:ℝ) S.val T.val))
    (continuous_finiteMatrixOperator.comp (continuous_pi (fun S => continuous_pi (fun T =>
      D.continuous_radialRemainder_ray _ S.val T.val σ hz))))
    ((Fintype.card (NonemptySubset d):ℝ)*D.matrixBound (shiftedDirection σ))
    (fun t => norm_finiteMatrixOperator_le (D.matrixBound_pos _).le
      (fun S T => D.radial_entry_le σ hR hz hsep t S.val T.val))


theorem norm_boundedC01_le : ‖D.boundedC01 σ hR hz hsep‖≤
    (Fintype.card (NonemptySubset d):ℝ)*D.matrixBound (shiftedDirection σ) := by
  unfold boundedC01
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
    (mul_nonneg (Nat.cast_nonneg _) (D.matrixBound_pos _).le) _

theorem norm_boundedC10_le : ‖D.boundedC10 σ hR hz hsep‖≤D.matrixBound (shiftedDirection σ) := by
  unfold boundedC10
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (D.matrixBound_pos _).le _

theorem norm_boundedC11_le : ‖D.boundedC11 σ hR hz hsep‖≤
    (Fintype.card (NonemptySubset d):ℝ)*D.matrixBound (shiftedDirection σ) := by
  unfold boundedC11
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
    (mul_nonneg (Nat.cast_nonneg _) (D.matrixBound_pos _).le) _

/-- Common operator bound independent of the base point and initial radius. -/
def volterraBound : ℝ := ((Fintype.card (NonemptySubset d):ℝ)+1)*D.matrixBound (shiftedDirection σ)

theorem volterraBound_pos : 0<D.volterraBound σ :=
  mul_pos (by positivity) (D.matrixBound_pos _)

theorem boundedC_norms_le :
    ‖D.boundedC01 σ hR hz hsep‖≤D.volterraBound σ ∧
    ‖D.boundedC10 σ hR hz hsep‖≤D.volterraBound σ ∧
    ‖D.boundedC11 σ hR hz hsep‖≤D.volterraBound σ := by
  have h1 := D.norm_boundedC01_le σ hR hz hsep
  have h2 := D.norm_boundedC10_le σ hR hz hsep
  have h3 := D.norm_boundedC11_le σ hR hz hsep
  have hb := (D.matrixBound_pos (shiftedDirection σ)).le
  have hc : (0:ℝ)≤Fintype.card (NonemptySubset d) := Nat.cast_nonneg _
  unfold volterraBound
  constructor
  · nlinarith
  constructor <;> nlinarith

end SectorialData
end BourgadeHuang.CMS
