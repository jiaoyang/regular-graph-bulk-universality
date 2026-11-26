import BourgadeHuang.CMS.GeneralGauge
import BourgadeHuang.CMS.ExplicitSolutions
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Local differential calculus for the actual general-coupling CMS operators. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace BourgadeHuang.CMS

variable {d : ℕ} {f g : Point d → ℂ} {z : Point d}

theorem coordDeriv_comm_analytic (hf : AnalyticAt ℂ f z) (i j : Fin d) :
    coordDeriv i (coordDeriv j f) z = coordDeriv j (coordDeriv i f) z := by
  rw [coordDeriv_coordDeriv_eq_fderiv hf,coordDeriv_coordDeriv_eq_fderiv hf]
  exact hf.contDiffAt.isSymmSndFDerivAt_of_omega.eq _ _

theorem secondPartial_coordDeriv_analytic (hf : AnalyticAt ℂ f z) (i j : Fin d) :
    secondPartial i (coordDeriv j f) z = coordDeriv j (secondPartial i f) z := by
  have he : coordDeriv i (coordDeriv j f) =ᶠ[𝓝 z] coordDeriv j (coordDeriv i f) := by
    filter_upwards [hf.eventually_analyticAt] with w hw
    exact coordDeriv_comm_analytic hw i j
  unfold secondPartial
  rw [coordDeriv_congr_nhds he]
  exact coordDeriv_comm_analytic (analyticAt_coordDeriv hf i) i j

theorem secondPartial_comm_analytic (hf : AnalyticAt ℂ f z) (i j : Fin d) :
    secondPartial i (secondPartial j f) z = secondPartial j (secondPartial i f) z := by
  change secondPartial i (coordDeriv j (coordDeriv j f)) z = _
  rw [secondPartial_coordDeriv_analytic (analyticAt_coordDeriv hf j)]
  have he : secondPartial i (coordDeriv j f) =ᶠ[𝓝 z] coordDeriv j (secondPartial i f) := by
    filter_upwards [hf.eventually_analyticAt] with w hw
    exact secondPartial_coordDeriv_analytic hw i j
  rw [coordDeriv_congr_nhds he]
  rfl

theorem coordDeriv_const_mul_analytic (hf : AnalyticAt ℂ f z) (a : ℂ) (i : Fin d) :
    coordDeriv i (fun w => a*f w) z = a*coordDeriv i f z := by
  exact coordDeriv_smul_analytic hf a i

theorem coordDeriv_sub_analytic (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (i : Fin d) : coordDeriv i (fun w => f w-g w) z = coordDeriv i f z-coordDeriv i g z := by
  have he : (fun w => f w-g w) = f+(-1:ℂ)•g := by ext; simp [sub_eq_add_neg]
  rw [he,coordDeriv_add_analytic hf (hg.const_smul),coordDeriv_smul_analytic hg]
  simp [sub_eq_add_neg]

theorem secondPartial_const_mul_analytic (hf : AnalyticAt ℂ f z) (a : ℂ) (i : Fin d) :
    secondPartial i (fun w => a*f w) z = a*secondPartial i f z := by
  exact secondPartial_smul_analytic hf a i

theorem secondPartial_sub_analytic (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (i : Fin d) : secondPartial i (fun w => f w-g w) z = secondPartial i f z-secondPartial i g z := by
  have he : (fun w => f w-g w) = f+(-1:ℂ)•g := by ext; simp [sub_eq_add_neg]
  rw [he,secondPartial_add_analytic hf (hg.const_smul),secondPartial_smul_analytic hg]
  simp [sub_eq_add_neg]

/-- The constant two-coordinate vector field in a CMS pair interaction. -/
def chargeDirection (c : Fin d → ℂ) (i j : Fin d) (f : Point d → ℂ) (z : Point d) : ℂ :=
  c i*c j*coordDeriv i f z-c i^2*coordDeriv j f z

theorem analyticAt_chargeDirection (c : Fin d → ℂ) (i j : Fin d)
    (hf : AnalyticAt ℂ f z) : AnalyticAt ℂ (chargeDirection c i j f) z :=
  (analyticAt_const.mul (analyticAt_coordDeriv hf i)).sub
    (analyticAt_const.mul (analyticAt_coordDeriv hf j))

theorem coordDeriv_chargeDirection (c : Fin d → ℂ) (i j k : Fin d)
    (hf : AnalyticAt ℂ f z) :
    coordDeriv k (chargeDirection c i j f) z = chargeDirection c i j (coordDeriv k f) z := by
  unfold chargeDirection
  rw [coordDeriv_sub_analytic (f := fun w => c i*c j*coordDeriv i f w) (g := fun w => c i^2*coordDeriv j f w) (analyticAt_const.mul (analyticAt_coordDeriv hf i))
    (analyticAt_const.mul (analyticAt_coordDeriv hf j))]
  rw [coordDeriv_const_mul_analytic (analyticAt_coordDeriv hf i),
    coordDeriv_const_mul_analytic (analyticAt_coordDeriv hf j),
    coordDeriv_comm_analytic hf k i,coordDeriv_comm_analytic hf k j]

theorem secondPartial_chargeDirection (c : Fin d → ℂ) (i j k : Fin d)
    (hf : AnalyticAt ℂ f z) :
    secondPartial k (chargeDirection c i j f) z = chargeDirection c i j (secondPartial k f) z := by
  unfold chargeDirection
  rw [secondPartial_sub_analytic (f := fun w => c i*c j*coordDeriv i f w) (g := fun w => c i^2*coordDeriv j f w) (analyticAt_const.mul (analyticAt_coordDeriv hf i))
    (analyticAt_const.mul (analyticAt_coordDeriv hf j))]
  rw [secondPartial_const_mul_analytic (analyticAt_coordDeriv hf i),
    secondPartial_const_mul_analytic (analyticAt_coordDeriv hf j),
    secondPartial_coordDeriv_analytic hf k i,secondPartial_coordDeriv_analytic hf k j]

theorem chargeDirection_mul (c : Fin d → ℂ) (i j : Fin d)
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) :
    chargeDirection c i j (fun w => f w*g w) z =
      chargeDirection c i j f z*g z+f z*chargeDirection c i j g z := by
  simp only [chargeDirection,coordDeriv_mul_analytic hf hg]
  ring

theorem chargeDirection_comm (c : Fin d → ℂ) (i j k l : Fin d)
    (hf : AnalyticAt ℂ f z) :
    chargeDirection c i j (chargeDirection c k l f) z =
      chargeDirection c k l (chargeDirection c i j f) z := by
  change c i*c j*coordDeriv i (chargeDirection c k l f) z-c i^2*coordDeriv j (chargeDirection c k l f) z =
    c k*c l*coordDeriv k (chargeDirection c i j f) z-c k^2*coordDeriv l (chargeDirection c i j f) z
  rw [coordDeriv_chargeDirection c k l i hf,coordDeriv_chargeDirection c k l j hf,
    coordDeriv_chargeDirection c i j k hf,coordDeriv_chargeDirection c i j l hf]
  unfold chargeDirection
  rw [coordDeriv_comm_analytic hf k i,coordDeriv_comm_analytic hf l i,
    coordDeriv_comm_analytic hf k j,coordDeriv_comm_analytic hf l j]
  ring

def inverseGap (i j : Fin d) (z : Point d) : ℂ := (z i-z j)⁻¹

theorem analyticAt_inverseGap (i j : Fin d) (h : z i-z j ≠ 0) :
    AnalyticAt ℂ (inverseGap i j) z :=
  (((ContinuousLinearMap.proj (R := ℂ) i).analyticAt z).sub
    ((ContinuousLinearMap.proj (R := ℂ) j).analyticAt z)).inv h

theorem coordDeriv_inverseGap (i j k : Fin d) (h : z i-z j ≠ 0) :
    coordDeriv k (inverseGap i j) z = -pairSlope k (i,j)*(inverseGap i j z)^2 := by
  have hd := (hasDerivAt_pairInverse z k (i,j) h).deriv
  change coordDeriv k (inverseGap i j) z = _ at hd
  rw [hd]
  simp only [inverseGap,div_eq_mul_inv]
  ring

theorem secondPartial_inverseGap (i j k : Fin d) (h : z i-z j ≠ 0) :
    secondPartial k (inverseGap i j) z = 2*(pairSlope k (i,j))^2*(inverseGap i j z)^3 := by
  have he : coordDeriv k (inverseGap i j) =ᶠ[𝓝 z]
      (fun w => -pairSlope k (i,j)*(inverseGap i j w*inverseGap i j w)) := by
    have hn : ∀ᶠ w in 𝓝 z, w i-w j ≠ 0 :=
      ((continuous_apply i).sub (continuous_apply j)).continuousAt.eventually_ne h
    filter_upwards [hn] with w hw
    simpa only [pow_two] using coordDeriv_inverseGap i j k hw
  unfold secondPartial
  rw [coordDeriv_congr_nhds he,
    coordDeriv_const_mul_analytic (f := fun w => inverseGap i j w*inverseGap i j w) ((analyticAt_inverseGap i j h).mul (analyticAt_inverseGap i j h)),
    coordDeriv_mul_analytic (analyticAt_inverseGap i j h) (analyticAt_inverseGap i j h),
    coordDeriv_inverseGap i j k h]
  ring

/-- The actual first-order pair interaction, before multiplying by `2/β`. -/
def pairOperator (c : Fin d → ℂ) (i j : Fin d) (f : Point d → ℂ) (z : Point d) : ℂ :=
  inverseGap i j z*chargeDirection c i j f z

def freeOperator (c : Fin d → ℂ) (i : Fin d) (f : Point d → ℂ) (z : Point d) : ℂ :=
  secondPartial i f z+c i^2*f z

def operatorCommutator (A B : (Point d → ℂ) → Point d → ℂ)
    (f : Point d → ℂ) (z : Point d) : ℂ := A (B f) z-B (A f) z

theorem analyticAt_pairOperator (c : Fin d → ℂ) (i j : Fin d)
    (hf : AnalyticAt ℂ f z) (h : z i-z j ≠ 0) :
    AnalyticAt ℂ (pairOperator c i j f) z :=
  (analyticAt_inverseGap i j h).mul (analyticAt_chargeDirection c i j hf)

theorem analyticAt_freeOperator (c : Fin d → ℂ) (i : Fin d)
    (hf : AnalyticAt ℂ f z) : AnalyticAt ℂ (freeOperator c i f) z :=
  (analyticAt_coordDeriv (analyticAt_coordDeriv hf i) i).add (analyticAt_const.mul hf)

/-- Product differentiation cancels every second derivative in the pair bracket. -/
theorem pairOperator_commutator (c : Fin d → ℂ) (i j k l : Fin d)
    (hf : AnalyticAt ℂ f z) (hij : z i-z j ≠ 0) (hkl : z k-z l ≠ 0) :
    operatorCommutator (pairOperator c i j) (pairOperator c k l) f z =
      inverseGap i j z*chargeDirection c i j (inverseGap k l) z*chargeDirection c k l f z-
      inverseGap k l z*chargeDirection c k l (inverseGap i j) z*chargeDirection c i j f z := by
  unfold operatorCommutator
  change inverseGap i j z*chargeDirection c i j
      (fun w => inverseGap k l w*chargeDirection c k l f w) z-
    inverseGap k l z*chargeDirection c k l
      (fun w => inverseGap i j w*chargeDirection c i j f w) z = _
  rw [chargeDirection_mul c i j (analyticAt_inverseGap k l hkl)
    (analyticAt_chargeDirection c k l hf),
    chargeDirection_mul c k l (analyticAt_inverseGap i j hij)
    (analyticAt_chargeDirection c i j hf),chargeDirection_comm c i j k l hf]
  ring

theorem chargeDirection_add (c : Fin d → ℂ) (i j : Fin d)
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) :
    chargeDirection c i j (f+g) z = chargeDirection c i j f z+chargeDirection c i j g z := by
  simp only [chargeDirection,coordDeriv_add_analytic hf hg]
  ring

theorem chargeDirection_const_mul (c : Fin d → ℂ) (i j : Fin d)
    (hf : AnalyticAt ℂ f z) (a : ℂ) :
    chargeDirection c i j (fun w => a*f w) z = a*chargeDirection c i j f z := by
  simp only [chargeDirection,coordDeriv_const_mul_analytic hf]
  ring

/-- The actual free/pair commutator is only second order. -/
theorem free_pair_commutator (c : Fin d → ℂ) (i k l : Fin d)
    (hf : AnalyticAt ℂ f z) (hkl : z k-z l ≠ 0) :
    operatorCommutator (freeOperator c i) (pairOperator c k l) f z =
      secondPartial i (inverseGap k l) z*chargeDirection c k l f z+
      2*coordDeriv i (inverseGap k l) z*chargeDirection c k l (coordDeriv i f) z := by
  have hd := analyticAt_chargeDirection c k l hf
  have hs : AnalyticAt ℂ (secondPartial i f) z :=
    analyticAt_coordDeriv (analyticAt_coordDeriv hf i) i
  unfold operatorCommutator freeOperator pairOperator
  rw [secondPartial_mul_analytic (analyticAt_inverseGap k l hkl) hd]
  change _ - inverseGap k l z*chargeDirection c k l
    ((secondPartial i f)+(fun w => c i^2*f w)) z = _
  rw [chargeDirection_add (g := fun w => c i^2*f w) c k l hs (analyticAt_const.mul hf),
    chargeDirection_const_mul c k l hf,
    secondPartial_chargeDirection c k l i hf,coordDeriv_chargeDirection c k l i hf]
  ring

theorem freeOperator_commutator (c : Fin d → ℂ) (i j : Fin d)
    (hf : AnalyticAt ℂ f z) :
    operatorCommutator (freeOperator c i) (freeOperator c j) f z = 0 := by
  have hs k : AnalyticAt ℂ (secondPartial k f) z :=
    analyticAt_coordDeriv (analyticAt_coordDeriv hf k) k
  unfold operatorCommutator freeOperator
  change secondPartial i ((secondPartial j f)+(fun w => c j^2*f w)) z+_-
    (secondPartial j ((secondPartial i f)+(fun w => c i^2*f w)) z+_) = 0
  rw [secondPartial_add_analytic (g := fun w => c j^2*f w) (hs j) (analyticAt_const.mul hf),
    secondPartial_add_analytic (g := fun w => c i^2*f w) (hs i) (analyticAt_const.mul hf),
    secondPartial_const_mul_analytic hf,secondPartial_const_mul_analytic hf,
    secondPartial_comm_analytic hf i j]
  ring

theorem chargeDirection_inverseGap (c : Fin d → ℂ) (i j k l : Fin d)
    (hkl : z k-z l ≠ 0) :
    chargeDirection c i j (inverseGap k l) z =
      -(c i*c j*pairSlope i (k,l)-c i^2*pairSlope j (k,l))*(inverseGap k l z)^2 := by
  simp only [chargeDirection,coordDeriv_inverseGap k l _ hkl]
  ring

theorem operatorCommutator_swap (A B : (Point d → ℂ) → Point d → ℂ)
    (f : Point d → ℂ) (z : Point d) :
    operatorCommutator A B f z = -operatorCommutator B A f z := by
  unfold operatorCommutator
  ring

end BourgadeHuang.CMS
