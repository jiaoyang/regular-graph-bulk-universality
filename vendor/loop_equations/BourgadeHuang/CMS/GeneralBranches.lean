import BourgadeHuang.CMS.GeneralGauge
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! Nonvanishing holomorphic branch factors for arbitrary CMS coupling, with
actual logarithmic derivatives. The logarithms are taken on positively ordered
coordinate differences, so the branch is globally specified on the chamber. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BourgadeHuang.CMS

def upperPairs (d : ℕ) : Finset (Fin d × Fin d) := Finset.univ.filter (fun p => p.1<p.2)

/-- Labels refer to the charge-weighted phase: numerator labels are the negatives
of the numerator signs in the usual two-block formula. -/
def couplingExponent {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (i j : Fin d) : ℂ := c i*c j/β*(signValue (σ i)*signValue (σ j)-1)

theorem couplingExponent_symm {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (i j : Fin d) :
    couplingExponent β c σ i j=couplingExponent β c σ j i := by
  unfold couplingExponent
  ring

@[simp] theorem couplingExponent_self {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (i : Fin d) : couplingExponent β c σ i i=0 := by
  simp [couplingExponent,← sq,signValue_sq]

def generalBranchLog {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (z : Point d) : ℂ :=
  Complex.I*∑i,c i*signValue (σ i)*z i+
    ∑p∈upperPairs d,couplingExponent β c σ p.1 p.2*Complex.log (z p.2-z p.1)

def generalBranch {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (z : Point d) : ℂ := Complex.exp (generalBranchLog β c σ z)

def branchCorrection {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (i : Fin d) (z : Point d) : ℂ :=
  ∑j∈Finset.univ.erase i,couplingExponent β c σ i j/(z i-z j)

def branchCorrectionDerivative {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (i : Fin d) (z : Point d) : ℂ :=
  -∑j∈Finset.univ.erase i,couplingExponent β c σ i j/(z i-z j)^2

@[simp] theorem generalBranch_ne_zero {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (z : Point d) : generalBranch β c σ z≠0 := Complex.exp_ne_zero _

theorem analyticAt_generalBranchLog {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) {z : Point d} (hz : z∈OrderedDomain d) :
    AnalyticAt ℂ (generalBranchLog β c σ) z := by
  apply AnalyticAt.add
  · apply AnalyticAt.mul analyticAt_const
    exact Finset.analyticAt_sum _ (fun i _ => analyticAt_const.mul ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt z))
  · apply Finset.analyticAt_sum
    intro p hp
    apply AnalyticAt.mul analyticAt_const
    apply AnalyticAt.clog (((ContinuousLinearMap.proj (R := ℂ) p.2).analyticAt z).sub ((ContinuousLinearMap.proj (R := ℂ) p.1).analyticAt z))
    exact Or.inl (by simpa only [Complex.sub_re] using sub_pos.mpr (hz _ _ (Finset.mem_filter.mp hp).2))

theorem analyticAt_generalBranch {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) {z : Point d} (hz : z∈OrderedDomain d) :
    AnalyticAt ℂ (generalBranch β c σ) z := (analyticAt_generalBranchLog β c σ hz).cexp

private theorem sum_upperPairs_first {d : ℕ} (i : Fin d) (f : Fin d × Fin d → ℂ) :
    (∑p∈upperPairs d,if p.1=i then f p else 0)=∑j,if i < j then f (i,j) else 0 := by
  classical
  simp only [upperPairs,Finset.sum_filter,Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro j _
    simp
  · intro j _ hji
    simp [hji]
  · simp

private theorem sum_upperPairs_second {d : ℕ} (i : Fin d) (f : Fin d × Fin d → ℂ) :
    (∑p∈upperPairs d,if p.2=i then f p else 0)=∑j,if j < i then f (j,i) else 0 := by
  classical
  simp only [upperPairs,Finset.sum_filter,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki
    simp [hki]
  · simp

private theorem sum_upperPairs_logDerivative {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (i : Fin d) (z : Point d) :
    (∑p∈upperPairs d,couplingExponent β c σ p.1 p.2*pairSlope i p/(z p.1-z p.2))=
      branchCorrection β c σ i z := by
  have ht (p : Fin d × Fin d) :
      couplingExponent β c σ p.1 p.2*pairSlope i p/(z p.1-z p.2)=
      (if p.1=i then couplingExponent β c σ p.1 p.2/(z p.1-z p.2) else 0)-
      (if p.2=i then couplingExponent β c σ p.1 p.2/(z p.1-z p.2) else 0) := by
    simp only [pairSlope,mul_sub,mul_ite,mul_one,mul_zero,sub_div,ite_div,zero_div]
  simp_rw [ht]
  rw [Finset.sum_sub_distrib,sum_upperPairs_first,sum_upperPairs_second]
  unfold branchCorrection
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  simp only [sub_self,div_zero,sub_zero]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [hij,not_lt.mpr hij.le]
  · simp
  · simp only [hji,not_lt.mpr hji.le,if_true,if_false,zero_sub]
    rw [couplingExponent_symm β c σ j i,show z j-z i=-(z i-z j) by ring,div_neg,neg_neg]

theorem hasDerivAt_generalBranchLog {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) {z : Point d} (hz : z∈OrderedDomain d) (i : Fin d) :
    HasDerivAt (fun w => generalBranchLog β c σ (Function.update z i w))
      (Complex.I*c i*signValue (σ i)+branchCorrection β c σ i z) (z i) := by
  have hphase := (HasDerivAt.sum (u := Finset.univ)
    (fun j _ => (hasDerivAt_update_coord z i j).const_mul (c j*signValue (σ j)))).const_mul Complex.I
  have hsum := HasDerivAt.sum (u := upperPairs d) (fun p hp =>
    (((hasDerivAt_update_coord z i p.2).sub (hasDerivAt_update_coord z i p.1)).clog
      (show Function.update z i (z i) p.2-Function.update z i (z i) p.1∈Complex.slitPlane from by
        simp only [Function.update_eq_self]
        exact Or.inl (by simpa only [Complex.sub_re] using sub_pos.mpr (hz _ _ (Finset.mem_filter.mp hp).2)))).const_mul
      (couplingExponent β c σ p.1 p.2))
  have ht (p : Fin d × Fin d) :
      couplingExponent β c σ p.1 p.2*((if p.2=i then 1 else 0)-(if p.1=i then 1 else 0))/
        (z p.2-z p.1)=couplingExponent β c σ p.1 p.2*pairSlope i p/(z p.1-z p.2) := by
    rw [show z p.2-z p.1=-(z p.1-z p.2) by ring,div_neg]
    unfold pairSlope
    ring
  convert hphase.add hsum using 1
  simp only [Function.update_eq_self,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp_rw [← mul_div_assoc,ht]
  rw [sum_upperPairs_logDerivative]
  ring

theorem coordDeriv_generalBranchLog {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) {z : Point d} (hz : z∈OrderedDomain d) (i : Fin d) :
    coordDeriv i (generalBranchLog β c σ) z=
      Complex.I*c i*signValue (σ i)+branchCorrection β c σ i z :=
  (hasDerivAt_generalBranchLog β c σ hz i).deriv

theorem hasDerivAt_generalBranch {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) {z : Point d} (hz : z∈OrderedDomain d) (i : Fin d) :
    HasDerivAt (fun w => generalBranch β c σ (Function.update z i w))
      ((Complex.I*c i*signValue (σ i)+branchCorrection β c σ i z)*generalBranch β c σ z) (z i) := by
  simpa only [generalBranch,Function.update_eq_self,mul_comm] using
    (hasDerivAt_generalBranchLog β c σ hz i).cexp


theorem hasDerivAt_branchCorrection {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) {z : Point d} (hz : CollisionFree z) (i : Fin d) :
    HasDerivAt (fun w => branchCorrection β c σ i (Function.update z i w))
      (branchCorrectionDerivative β c σ i z) (z i) := by
  have ht (j : Fin d) (hj : j∈Finset.univ.erase i) :=
    (((hasDerivAt_update_coord z i i).sub (hasDerivAt_update_coord z i j)).inv
      (by simpa only [Function.update_eq_self] using hz.sub_ne_zero (Finset.ne_of_mem_erase hj).symm)).const_mul
      (couplingExponent β c σ i j)
  have hsum := HasDerivAt.sum (u := Finset.univ.erase i) ht
  convert hsum using 1
  unfold branchCorrectionDerivative
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Function.update_eq_self,if_pos rfl,if_neg (Finset.ne_of_mem_erase hj),sub_zero,ite_true]
  ring

theorem secondPartial_generalBranchLog {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) {z : Point d} (hz : z∈OrderedDomain d) (i : Fin d) :
    secondPartial i (generalBranchLog β c σ) z=branchCorrectionDerivative β c σ i z := by
  have heq : coordDeriv i (generalBranchLog β c σ) =ᶠ[𝓝 z]
      (fun w => Complex.I*c i*signValue (σ i)+branchCorrection β c σ i w) := by
    filter_upwards [(orderedDomain_isOpen d).eventually_mem hz] with w hw
    exact coordDeriv_generalBranchLog β c σ hw i
  unfold secondPartial
  rw [coordDeriv_congr_nhds heq]
  exact ((hasDerivAt_branchCorrection β c σ (orderedDomain_collisionFree hz) i).const_add
    (Complex.I*c i*signValue (σ i))).deriv

/-- Cancellation of the complete order-one-over-gap scalar term. -/
theorem couplingExponent_linear_cancellation {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (i j : Fin d) :
    2*(Complex.I*c i*signValue (σ i))*couplingExponent β c σ i j+
      (2/β)*(c i*c j*(Complex.I*c i*signValue (σ i))-
        c i^2*(Complex.I*c j*signValue (σ j)))=0 := by
  cases hi : σ i <;> cases hj : σ j <;> simp only [couplingExponent,hi,hj,signValue_true,signValue_false] <;> ring

theorem branchCorrection_linear_cancellation {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) (i : Fin d) (z : Point d) :
    2*(Complex.I*c i*signValue (σ i))*branchCorrection β c σ i z+
      (2/β)*∑j∈Finset.univ.erase i,
        (c i*c j*(Complex.I*c i*signValue (σ i))-
          c i^2*(Complex.I*c j*signValue (σ j)))/(z i-z j)=0 := by
  unfold branchCorrection
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j hj
  rw [← mul_div_assoc,← mul_div_assoc,← add_div,couplingExponent_linear_cancellation,zero_div]

/-- The scalar remainder after exponential and logarithmic branch conjugation. -/
def generalBranchPotential {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (i : Fin d) (z : Point d) : ℂ :=
  branchCorrectionDerivative β c σ i z+(branchCorrection β c σ i z)^2+
    (2/β)*∑j∈Finset.univ.erase i,
      (c i*c j*branchCorrection β c σ i z-c i^2*branchCorrection β c σ j z)/(z i-z j)

/-- Explicit cancellation formula used to obtain degree-minus-two remainder
bounds; it is valid for every coupling and all collision-free ordered points. -/
theorem generalBranch_scalar_remainder {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) {z : Point d} (hz : z∈OrderedDomain d) (i : Fin d) :
    secondPartial i (generalBranchLog β c σ) z+
      (coordDeriv i (generalBranchLog β c σ) z)^2+c i^2+
      (2/β)*∑j∈Finset.univ.erase i,
        (c i*c j*coordDeriv i (generalBranchLog β c σ) z-
          c i^2*coordDeriv j (generalBranchLog β c σ) z)/(z i-z j)=
      generalBranchPotential β c σ i z := by
  simp only [secondPartial_generalBranchLog β c σ hz,coordDeriv_generalBranchLog β c σ hz]
  have hphase : (Complex.I*c i*signValue (σ i))^2+c i^2=0 := by
    rw [mul_pow,mul_pow,Complex.I_sq,signValue_sq]
    ring
  have hsplit (j : Fin d) :
      (c i*c j*(Complex.I*c i*signValue (σ i)+branchCorrection β c σ i z)-
        c i^2*(Complex.I*c j*signValue (σ j)+branchCorrection β c σ j z))/(z i-z j)=
      (c i*c j*(Complex.I*c i*signValue (σ i))-
        c i^2*(Complex.I*c j*signValue (σ j)))/(z i-z j)+
      (c i*c j*branchCorrection β c σ i z-c i^2*branchCorrection β c σ j z)/(z i-z j) := by ring
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib,mul_add]
  have hcancel := branchCorrection_linear_cancellation β c σ i z
  unfold generalBranchPotential
  linear_combination hphase+hcancel


/-- The sectorial equation after cancellation of the leading branch. -/
def sectorialOperator {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (i : Fin d) (W : Point d → ℂ) (z : Point d) : ℂ :=
  secondPartial i W z+2*Complex.I*c i*signValue (σ i)*coordDeriv i W z+
    2*branchCorrection β c σ i z*coordDeriv i W z+
    (2/β)*∑j∈Finset.univ.erase i,
      (c i*c j*coordDeriv i W z-c i^2*coordDeriv j W z)/(z i-z j)+
    generalBranchPotential β c σ i z*W z

theorem conjugatedDeformedOperator_generalBranchLog {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) {z : Point d} (hz : z∈OrderedDomain d) (i : Fin d)
    (W : Point d → ℂ) :
    conjugatedDeformedOperator β c (generalBranchLog β c σ) i W z=
      sectorialOperator β c σ i W z := by
  let L := generalBranchLog β c σ
  have ht j :
      (c i*c j*coordDeriv i W z-c i^2*coordDeriv j W z+
        (c i*c j*coordDeriv i L z-c i^2*coordDeriv j L z)*W z)/(z i-z j)=
      (c i*c j*coordDeriv i W z-c i^2*coordDeriv j W z)/(z i-z j)+
        ((c i*c j*coordDeriv i L z-c i^2*coordDeriv j L z)/(z i-z j))*W z := by ring
  change secondPartial i W z+2*coordDeriv i L z*coordDeriv i W z+
    (secondPartial i L z+(coordDeriv i L z)^2+c i^2)*W z+
      (2/β)*∑j∈Finset.univ.erase i,
        (c i*c j*coordDeriv i W z-c i^2*coordDeriv j W z+
          (c i*c j*coordDeriv i L z-c i^2*coordDeriv j L z)*W z)/(z i-z j) = _
  simp_rw [ht]
  rw [Finset.sum_add_distrib,← Finset.sum_mul,mul_add]
  have hs := generalBranch_scalar_remainder β c σ hz i
  change secondPartial i L z+(coordDeriv i L z)^2+c i^2+
    (2/β)*∑j∈Finset.univ.erase i,
      (c i*c j*coordDeriv i L z-c i^2*coordDeriv j L z)/(z i-z j)=_ at hs
  have hd : coordDeriv i L z=Complex.I*c i*signValue (σ i)+branchCorrection β c σ i z :=
    coordDeriv_generalBranchLog β c σ hz i
  unfold sectorialOperator
  linear_combination hs*W z+2*hd*coordDeriv i W z

theorem deformedOperator_generalBranch_mul {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) {W : Point d → ℂ} {z : Point d}
    (hz : z∈OrderedDomain d) (hW : AnalyticAt ℂ W z) (i : Fin d) :
    deformedOperator β c i (fun w => generalBranch β c σ w*W w) z=
      generalBranch β c σ z*sectorialOperator β c σ i W z := by
  change deformedOperator β c i (fun w => Complex.exp (generalBranchLog β c σ w)*W w) z=
    Complex.exp (generalBranchLog β c σ z)*sectorialOperator β c σ i W z
  rw [deformedOperator_exp_mul β c (analyticAt_generalBranchLog β c σ hz) hW,
    conjugatedDeformedOperator_generalBranchLog β c σ hz]

theorem deformedOperator_generalBranch_mul_eq_zero_iff {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (σ : Fin d → Sign) {W : Point d → ℂ} {z : Point d}
    (hz : z∈OrderedDomain d) (hW : AnalyticAt ℂ W z) (i : Fin d) :
    deformedOperator β c i (fun w => generalBranch β c σ w*W w) z=0 ↔
      sectorialOperator β c σ i W z=0 := by
  rw [deformedOperator_generalBranch_mul β c σ hz hW,mul_eq_zero]
  simp

end BourgadeHuang.CMS
