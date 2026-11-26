import BourgadeHuang.OrthogonalCMS
import BourgadeHuang.CMS.GeneralCoupling

/-! The three-block orthogonal system in the unified charge coordinates used
for general-coupling analytic continuation and asymptotic analysis. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang
namespace OrthogonalCMS

def blockFunction {q : ℕ} (F : RatioFunction q) : CMS.Point (q+(q+q)) → ℂ :=
  CMS.blockFunction (fun u => CMS.blockFunction (F u))

@[simp] theorem blockFunction_append {q : ℕ} (F : RatioFunction q) (u v w : Fin q → ℂ) :
    blockFunction F (Fin.append u (Fin.append v w)) = F u v w := by
  simp [blockFunction]

def numeratorIndex {q : ℕ} (i : Fin q) : Fin (q+(q+q)) := Fin.castAdd (q+q) i
def firstDenominatorIndex {q : ℕ} (i : Fin q) : Fin (q+(q+q)) := Fin.natAdd q (Fin.castAdd q i)
def secondDenominatorIndex {q : ℕ} (i : Fin q) : Fin (q+(q+q)) := Fin.natAdd q (Fin.natAdd q i)

theorem coordDeriv_numerator {q : ℕ} (F : RatioFunction q) (i : Fin q) :
    CMS.coordDeriv (numeratorIndex i) (blockFunction F) = blockFunction (numeratorPartial i F) := by
  rw [numeratorIndex,blockFunction,CMS.coordDeriv_blockFunction_left]
  rfl

theorem coordDeriv_firstDenominator {q : ℕ} (F : RatioFunction q) (i : Fin q) :
    CMS.coordDeriv (firstDenominatorIndex i) (blockFunction F) = blockFunction (firstDenominatorPartial i F) := by
  rw [firstDenominatorIndex,blockFunction,CMS.coordDeriv_blockFunction_right]
  funext z
  change CMS.coordDeriv (Fin.castAdd q i)
    (CMS.blockFunction (F (fun j => z (Fin.castAdd (q+q) j))))
      (fun j => z (Fin.natAdd q j)) = _
  rw [CMS.coordDeriv_blockFunction_left]
  rfl

theorem coordDeriv_secondDenominator {q : ℕ} (F : RatioFunction q) (i : Fin q) :
    CMS.coordDeriv (secondDenominatorIndex i) (blockFunction F) = blockFunction (secondDenominatorPartial i F) := by
  rw [secondDenominatorIndex,blockFunction,CMS.coordDeriv_blockFunction_right]
  funext z
  change CMS.coordDeriv (Fin.natAdd q i)
    (CMS.blockFunction (F (fun j => z (Fin.castAdd (q+q) j))))
      (fun j => z (Fin.natAdd q j)) = _
  rw [CMS.coordDeriv_blockFunction_right]
  rfl

theorem secondPartial_numerator {q : ℕ} (F : RatioFunction q) (i : Fin q) :
    CMS.secondPartial (numeratorIndex i) (blockFunction F) =
      blockFunction (numeratorPartial i (numeratorPartial i F)) := by
  rw [CMS.secondPartial,coordDeriv_numerator,coordDeriv_numerator]

theorem secondPartial_firstDenominator {q : ℕ} (F : RatioFunction q) (i : Fin q) :
    CMS.secondPartial (firstDenominatorIndex i) (blockFunction F) =
      blockFunction (firstDenominatorPartial i (firstDenominatorPartial i F)) := by
  rw [CMS.secondPartial,coordDeriv_firstDenominator,coordDeriv_firstDenominator]

theorem secondPartial_secondDenominator {q : ℕ} (F : RatioFunction q) (i : Fin q) :
    CMS.secondPartial (secondDenominatorIndex i) (blockFunction F) =
      blockFunction (secondDenominatorPartial i (secondDenominatorPartial i F)) := by
  rw [CMS.secondPartial,coordDeriv_secondDenominator,coordDeriv_secondDenominator]

def charges (q : ℕ) : Fin (q+(q+q)) → ℂ :=
  Fin.append (fun _ => -1) (Fin.append (fun _ => 1/2) (fun _ => 1/2))

private theorem sum_erase_eq_sum {d : ℕ} (f : Fin d → ℂ) (i : Fin d) (hi : f i = 0) :
    (∑j∈Finset.univ.erase i,f j) = ∑j,f j := by
  have h := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  simpa only [hi,add_zero] using h

theorem deformedOperator_numerator {q : ℕ} (F : RatioFunction q) (u v w : Fin q → ℂ) (i : Fin q) :
    CMS.deformedOperator 1 (charges q) (numeratorIndex i) (blockFunction F) (Fin.append u (Fin.append v w)) =
      numeratorOperator i F u v w := by
  unfold CMS.deformedOperator
  rw [secondPartial_numerator,sum_erase_eq_sum _ _ (by simp),Fin.sum_univ_add]
  have hN (j : Fin q) : CMS.coordDeriv (Fin.castAdd (q+q) j) (blockFunction F) =
      blockFunction (numeratorPartial j F) := coordDeriv_numerator F j
  have hV (j : Fin q) : CMS.coordDeriv (Fin.natAdd q (Fin.castAdd q j)) (blockFunction F) =
      blockFunction (firstDenominatorPartial j F) := coordDeriv_firstDenominator F j
  have hW (j : Fin q) : CMS.coordDeriv (Fin.natAdd q (Fin.natAdd q j)) (blockFunction F) =
      blockFunction (secondDenominatorPartial j F) := coordDeriv_secondDenominator F j
  simp only [Fin.sum_univ_add,hN,hV,hW,
    coordDeriv_numerator,coordDeriv_firstDenominator,coordDeriv_secondDenominator,blockFunction_append]
  simp only [charges,numeratorIndex,firstDenominatorIndex,secondDenominatorIndex,
    Fin.append_left,Fin.append_right,div_one,mul_add,Finset.mul_sum]
  have hn (A B z : ℂ) : 2*(((-1)*(-1)*A-(-1)^2*B)/z) = 2*((A-B)/z) := by ring
  have hd (A B z : ℂ) : 2*(((-1)*(1/2)*A-(-1)^2*B)/z) = -((A+2*B)/z) := by ring
  simp_rw [hn,hd,Finset.sum_neg_distrib]
  rw [← Finset.mul_sum,← sum_erase_eq_sum
    (fun j => (numeratorPartial i F u v w-numeratorPartial j F u v w)/(u i-u j)) i (by simp)]
  unfold numeratorOperator
  ring

theorem deformedOperator_firstDenominator {q : ℕ} (F : RatioFunction q) (u v w : Fin q → ℂ) (i : Fin q) :
    CMS.deformedOperator 1 (charges q) (firstDenominatorIndex i) (blockFunction F) (Fin.append u (Fin.append v w)) =
      firstDenominatorOperator i F u v w := by
  unfold CMS.deformedOperator
  rw [secondPartial_firstDenominator,sum_erase_eq_sum _ _ (by simp),Fin.sum_univ_add]
  have hN (j : Fin q) : CMS.coordDeriv (Fin.castAdd (q+q) j) (blockFunction F) =
      blockFunction (numeratorPartial j F) := coordDeriv_numerator F j
  have hV (j : Fin q) : CMS.coordDeriv (Fin.natAdd q (Fin.castAdd q j)) (blockFunction F) =
      blockFunction (firstDenominatorPartial j F) := coordDeriv_firstDenominator F j
  have hW (j : Fin q) : CMS.coordDeriv (Fin.natAdd q (Fin.natAdd q j)) (blockFunction F) =
      blockFunction (secondDenominatorPartial j F) := coordDeriv_secondDenominator F j
  simp only [Fin.sum_univ_add,hN,hV,hW,
    coordDeriv_numerator,coordDeriv_firstDenominator,coordDeriv_secondDenominator,blockFunction_append]
  simp only [charges,numeratorIndex,firstDenominatorIndex,secondDenominatorIndex,
    Fin.append_left,Fin.append_right,div_one,mul_add,Finset.mul_sum]
  have hn (A B z : ℂ) : 2*(((1/2)*(-1)*A-(1/2)^2*B)/z) = -((A+(1/2)*B)/z) := by ring
  have hd (A B z : ℂ) : 2*(((1/2)*(1/2)*A-(1/2)^2*B)/z) = (1/2)*((A-B)/z) := by ring
  simp_rw [hn,hd,Finset.sum_neg_distrib]
  rw [← Finset.mul_sum,← Finset.mul_sum,← sum_erase_eq_sum
    (fun j => (firstDenominatorPartial i F u v w-firstDenominatorPartial j F u v w)/(v i-v j)) i (by simp)]
  unfold firstDenominatorOperator
  ring

theorem deformedOperator_secondDenominator {q : ℕ} (F : RatioFunction q) (u v w : Fin q → ℂ) (i : Fin q) :
    CMS.deformedOperator 1 (charges q) (secondDenominatorIndex i) (blockFunction F) (Fin.append u (Fin.append v w)) =
      secondDenominatorOperator i F u v w := by
  unfold CMS.deformedOperator
  rw [secondPartial_secondDenominator,sum_erase_eq_sum _ _ (by simp),Fin.sum_univ_add]
  have hN (j : Fin q) : CMS.coordDeriv (Fin.castAdd (q+q) j) (blockFunction F) =
      blockFunction (numeratorPartial j F) := coordDeriv_numerator F j
  have hV (j : Fin q) : CMS.coordDeriv (Fin.natAdd q (Fin.castAdd q j)) (blockFunction F) =
      blockFunction (firstDenominatorPartial j F) := coordDeriv_firstDenominator F j
  have hW (j : Fin q) : CMS.coordDeriv (Fin.natAdd q (Fin.natAdd q j)) (blockFunction F) =
      blockFunction (secondDenominatorPartial j F) := coordDeriv_secondDenominator F j
  simp only [Fin.sum_univ_add,hN,hV,hW,
    coordDeriv_numerator,coordDeriv_firstDenominator,coordDeriv_secondDenominator,blockFunction_append]
  simp only [charges,numeratorIndex,firstDenominatorIndex,secondDenominatorIndex,
    Fin.append_left,Fin.append_right,div_one,mul_add,Finset.mul_sum]
  have hn (A B z : ℂ) : 2*(((1/2)*(-1)*A-(1/2)^2*B)/z) = -((A+(1/2)*B)/z) := by ring
  have hd (A B z : ℂ) : 2*(((1/2)*(1/2)*A-(1/2)^2*B)/z) = (1/2)*((A-B)/z) := by ring
  simp_rw [hn,hd,Finset.sum_neg_distrib]
  rw [← Finset.mul_sum,← Finset.mul_sum,← sum_erase_eq_sum
    (fun j => (secondDenominatorPartial i F u v w-secondDenominatorPartial j F u v w)/(w i-w j)) i (by simp)]
  unfold secondDenominatorOperator
  ring

end OrthogonalCMS

def expectedOrthogonalRatioFunction {q : ℕ} (ν : Measure AnchoredCountingState) : CMS.Point (q+(q+q)) → ℂ :=
  OrthogonalCMS.blockFunction (expectedOrthogonalCharacteristicRatios ν)

theorem analyticAt_expectedOrthogonalRatioFunction {q : ℕ}
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (z : CMS.Point (q+(q+q)))
    (hwv : ∀ j, SameOpenHalfPlane (z (OrthogonalCMS.secondDenominatorIndex j))
      (z (OrthogonalCMS.firstDenominatorIndex j))) :
    AnalyticAt ℂ (expectedOrthogonalRatioFunction ν) z := by
  have hmap : AnalyticAt ℂ (fun x : CMS.Point (q+(q+q)) =>
      ((fun j => x (OrthogonalCMS.numeratorIndex j)),
        (fun j => x (OrthogonalCMS.firstDenominatorIndex j)),
        (fun j => x (OrthogonalCMS.secondDenominatorIndex j)))) z :=
    (AnalyticAt.pi (fun j => CMS.analyticAt_coord z _)).prod
      ((AnalyticAt.pi (fun j => CMS.analyticAt_coord z _)).prod
        (AnalyticAt.pi (fun j => CMS.analyticAt_coord z _)))
  exact (analyticAt_expectedOrthogonalCharacteristicRatios_joint ν ha he
    (fun j => z (OrthogonalCMS.numeratorIndex j)) _ _ hwv).comp
      (f := fun x : CMS.Point (q+(q+q)) =>
        ((fun j => x (OrthogonalCMS.numeratorIndex j)),
          (fun j => x (OrthogonalCMS.firstDenominatorIndex j)),
          (fun j => x (OrthogonalCMS.secondDenominatorIndex j)))) hmap

end BourgadeHuang
