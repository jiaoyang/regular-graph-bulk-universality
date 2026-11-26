import BourgadeHuang.CMS.GeneralBranchBounds
import BourgadeHuang.CMS.GapExpressions

/-! Actual rational-expression representatives of the conjugated coefficients,
and all-order inverse-gap estimates for their genuine Fréchet coordinate jets. -/
noncomputable section
open scoped BigOperators
open Set
namespace BourgadeHuang.CMS
open GapExpression

def branchCorrectionExpression {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (i : Fin d) : GapExpression d :=
  finSum d (fun j => mul (const (couplingExponent β c σ i j)) (inverseGap i j))

theorem eval_branchCorrectionExpression {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (i : Fin d) (z : Point d) :
    (branchCorrectionExpression β c σ i).eval z=branchCorrection β c σ i z := by
  simp only [branchCorrectionExpression,eval_finSum,eval,eval_inverseGap,branchCorrection,div_eq_mul_inv]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  simp

theorem homogeneous_branchCorrectionExpression {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (i : Fin d) : (branchCorrectionExpression β c σ i).Homogeneous 1 := by
  apply homogeneous_finSum
  intro j
  exact (Homogeneous.const _).mul (homogeneous_inverseGap i j)

def branchPotentialExpression {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (i : Fin d) : GapExpression d :=
  add (add ((branchCorrectionExpression β c σ i).derivative i)
    (mul (branchCorrectionExpression β c σ i) (branchCorrectionExpression β c σ i)))
    (mul (const (2/β)) (finSum d (fun j => mul
      (add (mul (const (c i*c j)) (branchCorrectionExpression β c σ i))
        (mul (const (-(c i^2))) (branchCorrectionExpression β c σ j))) (inverseGap i j))))

theorem homogeneous_branchPotentialExpression {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (i : Fin d) : (branchPotentialExpression β c σ i).Homogeneous 2 := by
  apply Homogeneous.add
  · exact (homogeneous_derivative (homogeneous_branchCorrectionExpression β c σ i) i).add
      ((homogeneous_branchCorrectionExpression β c σ i).mul
        (homogeneous_branchCorrectionExpression β c σ i))
  · apply Homogeneous.mul (n := 0) (m := 2) (Homogeneous.const _)
    apply homogeneous_finSum
    intro j
    exact (((Homogeneous.const _).mul (homogeneous_branchCorrectionExpression β c σ i)).add
      ((Homogeneous.const _).mul (homogeneous_branchCorrectionExpression β c σ j))).mul
      (homogeneous_inverseGap i j)

theorem eval_branchPotentialExpression {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (i : Fin d) {z : Point d} (hz : CollisionFree z) :
    (branchPotentialExpression β c σ i).eval z=generalBranchPotential β c σ i z := by
  have hfun : (branchCorrectionExpression β c σ i).eval=branchCorrection β c σ i :=
    funext (eval_branchCorrectionExpression β c σ i)
  have hd : ((branchCorrectionExpression β c σ i).derivative i).eval z=
      branchCorrectionDerivative β c σ i z := by
    rw [← coordDeriv_eval _ hz,hfun]
    exact (hasDerivAt_branchCorrection β c σ hz i).deriv
  simp only [branchPotentialExpression,eval,eval_finSum,eval_inverseGap,
    eval_branchCorrectionExpression,hd,generalBranchPotential,pow_two,div_eq_mul_inv]
  congr 1
  congr 1
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  simp only [sub_self,inv_zero,mul_zero,sub_zero]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- First-derivative coefficient in the explicit sectorial equation. -/
def sectorialFirstCoefficient {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (i j : Fin d) (z : Point d) : ℂ :=
  if j=i then 2*branchCorrection β c σ i z+(2/β)*∑k∈Finset.univ.erase i,c i*c k/(z i-z k)
  else -(2/β)*c i^2/(z i-z j)

def sectorialFirstExpression {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (i j : Fin d) : GapExpression d :=
  if j=i then add (mul (const 2) (branchCorrectionExpression β c σ i))
    (mul (const (2/β)) (finSum d (fun k => mul (const (c i*c k)) (inverseGap i k))))
  else mul (const (-(2/β)*c i^2)) (inverseGap i j)

theorem homogeneous_sectorialFirstExpression {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (i j : Fin d) : (sectorialFirstExpression β c σ i j).Homogeneous 1 := by
  unfold sectorialFirstExpression
  split_ifs
  · apply Homogeneous.add
    · exact (Homogeneous.const _).mul (homogeneous_branchCorrectionExpression β c σ i)
    · apply Homogeneous.mul (n := 0) (m := 1) (Homogeneous.const _)
      exact homogeneous_finSum _ (fun k => (Homogeneous.const _).mul (homogeneous_inverseGap i k))
  · exact (Homogeneous.const _).mul (homogeneous_inverseGap i j)

theorem eval_sectorialFirstExpression {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (i j : Fin d) (z : Point d) :
    (sectorialFirstExpression β c σ i j).eval z=sectorialFirstCoefficient β c σ i j z := by
  unfold sectorialFirstExpression sectorialFirstCoefficient
  split_ifs
  · simp only [eval,eval_finSum,eval_inverseGap,eval_branchCorrectionExpression,div_eq_mul_inv]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    simp
  · simp [eval,eval_inverseGap,div_eq_mul_inv]


/-- The coefficient matrix represents exactly the first-order part of the
conjugated equation, including its diagonal contribution. -/
theorem sectorialFirstCoefficient_sum {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (i : Fin d) (z : Point d) (D : Fin d → ℂ) :
    (∑j,sectorialFirstCoefficient β c σ i j z*D j)=
      2*branchCorrection β c σ i z*D i+
      (2/β)*∑j∈Finset.univ.erase i,(c i*c j*D i-c i^2*D j)/(z i-z j) := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have he (j : Fin d) (hj : j∈Finset.univ.erase i) :
      sectorialFirstCoefficient β c σ i j z*D j=-(2/β)*c i^2/(z i-z j)*D j := by
    simp only [sectorialFirstCoefficient,if_neg (Finset.ne_of_mem_erase hj)]
  rw [Finset.sum_congr rfl he]
  simp only [sectorialFirstCoefficient,if_pos rfl,ite_true]
  have ht j : (c i*c j*D i-c i^2*D j)/(z i-z j)=
      (c i*c j/(z i-z j))*D i-(c i^2/(z i-z j))*D j := by ring
  simp_rw [ht]
  rw [Finset.sum_sub_distrib,← Finset.sum_mul]
  have hn : (∑j∈Finset.univ.erase i,-(2/β)*c i^2/(z i-z j)*D j)=
      -(2/β)*∑j∈Finset.univ.erase i,(c i^2/(z i-z j))*D j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hn]
  ring

theorem sectorialOperator_eq_firstCoefficients {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (i : Fin d) (W : Point d → ℂ) (z : Point d) :
    sectorialOperator β c σ i W z=
      secondPartial i W z+2*Complex.I*c i*signValue (σ i)*coordDeriv i W z+
      (∑j,sectorialFirstCoefficient β c σ i j z*coordDeriv j W z)+
      generalBranchPotential β c σ i z*W z := by
  rw [sectorialFirstCoefficient_sum]
  unfold sectorialOperator
  ring

private theorem coordinateJet_eq_of_eqOn_ordered {d n : ℕ} {f g : Point d → ℂ}
    (h : EqOn f g (OrderedDomain d)) {z : Point d} (hz : z∈OrderedDomain d)
    (v : Fin n → Fin d) : coordinateJet n f z v=coordinateJet n g z v := by
  unfold coordinateJet
  rw [iteratedFDeriv_eq_of_eqOn_open (orderedDomain_isOpen d) hz h]

/-- Formula (7.51) for every actual first-order coefficient, at arbitrary
coordinate derivative order. The finite constant is constructed explicitly. -/
theorem norm_coordinateJet_sectorialFirstCoefficient_le {d n : ℕ}
    (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign) (i j : Fin d) (v : Fin n → Fin d)
    {z : Point d} (hz : z∈OrderedDomain d) {R : ℝ} (hR : 0<R)
    (hsep : ∀a b,a≠b→R≤‖z a-z b‖) :
    ‖coordinateJet n (sectorialFirstCoefficient β c σ i j) z v‖≤
      (GapExpression.iterated n v (sectorialFirstExpression β c σ i j)).size/R^(1+n) := by
  rw [coordinateJet_eq_of_eqOn_ordered
    (fun w _ => (eval_sectorialFirstExpression β c σ i j w).symm) hz v]
  exact norm_coordinateJet_le (homogeneous_sectorialFirstExpression β c σ i j) v hz hR hsep

/-- Formula (7.51) for the actual scalar remainder: every further derivative
adds exactly one inverse power of the separation. -/
theorem norm_coordinateJet_generalBranchPotential_le {d n : ℕ}
    (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign) (i : Fin d) (v : Fin n → Fin d)
    {z : Point d} (hz : z∈OrderedDomain d) {R : ℝ} (hR : 0<R)
    (hsep : ∀a b,a≠b→R≤‖z a-z b‖) :
    ‖coordinateJet n (generalBranchPotential β c σ i) z v‖≤
      (GapExpression.iterated n v (branchPotentialExpression β c σ i)).size/R^(2+n) := by
  rw [coordinateJet_eq_of_eqOn_ordered
    (fun w hw => (eval_branchPotentialExpression β c σ i (orderedDomain_collisionFree hw)).symm) hz v]
  exact norm_coordinateJet_le (homogeneous_branchPotentialExpression β c σ i) v hz hR hsep

end BourgadeHuang.CMS
