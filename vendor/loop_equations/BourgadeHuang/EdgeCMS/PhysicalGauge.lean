import BourgadeHuang.EdgeCMS.Gauge
import BourgadeHuang.EdgeCMS.WKBAlgebra
import BourgadeHuang.EdgeCMS.RootGeometry
import BourgadeHuang.CMS.GeneralBranches

/-! The physical Airy WKB factor, including every pair-root logarithm.
Its logarithmic derivatives are proved for the displayed analytic function. -/
noncomputable section
open scoped BigOperators Topology
open Filter Set
namespace BourgadeHuang.EdgeCMS
open CMS

def PhysicalRootDomain (d : ℕ) : Set (Point d) := {z | ∀ i, z i ∈ Complex.slitPlane}

theorem physicalRootDomain_isOpen (d : ℕ) : IsOpen (PhysicalRootDomain d) := by
  have he : PhysicalRootDomain d = ⋂ i : Fin d, {z : Point d | z i ∈ Complex.slitPlane} := by
    ext z
    simp [PhysicalRootDomain]
  rw [he]
  exact isOpen_iInter_of_finite fun i => Complex.isOpen_slitPlane.preimage (continuous_apply i)

theorem physicalRootDomain_slit {d : ℕ} {z : Point d}
    (hz : z ∈ PhysicalRootDomain d) (i : Fin d) : z i ∈ Complex.slitPlane := hz i

theorem root_re_pos_of_slit {z : ℂ} (hz : z ∈ Complex.slitPlane) : 0<(root z).re := by
  have ha := Complex.neg_pi_lt_arg z
  have hb : z.arg<Real.pi := Complex.arg_lt_pi_iff.mpr (by
    rcases hz with hx | hy
    · exact Or.inl hx.le
    · exact Or.inr hy)
  have hcos : 0<Real.cos (z.arg/2) := Real.cos_pos_of_mem_Ioo ⟨by linarith,by linarith⟩
  simpa [root,Complex.exp_re,Complex.div_ofNat_im,Complex.log_im] using
    mul_pos (Real.exp_pos ((Complex.log z/2).re)) hcos

theorem rootSum_slit {d : ℕ} {z : Point d}
    (hz : z ∈ PhysicalRootDomain d) (i j : Fin d) :
    root (z i) + root (z j) ∈ Complex.slitPlane := by
  apply Or.inl
  simpa only [Complex.add_re] using add_pos (root_re_pos_of_slit (hz i)) (root_re_pos_of_slit (hz j))

def physicalGaugeLog {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (z : Point d) : ℂ :=
  (∑ i, scalarWKBLog (c i) (z i)) +
    ∑ p ∈ upperPairs d,
      rootPairExponent β c p.1 p.2 * Complex.log (root (z p.1) + root (z p.2))

def physicalGauge {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (z : Point d) : ℂ :=
  Complex.exp (physicalGaugeLog β c z)

@[simp] theorem physicalGauge_ne_zero {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (z : Point d) : physicalGauge β c z ≠ 0 := Complex.exp_ne_zero _

def physicalCorrection {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (i : Fin d) (z : Point d) : ℂ := rootCorrection β c (fun j => root (z j)) i

theorem analyticAt_physicalGaugeLog {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    {z : Point d} (hz : z ∈ PhysicalRootDomain d) :
    AnalyticAt ℂ (physicalGaugeLog β c) z := by
  apply AnalyticAt.add
  · exact Finset.analyticAt_sum _ fun i _ =>
      (analyticAt_scalarWKBLog (c i) (physicalRootDomain_slit hz i)).comp (f := fun w : Point d => w i)
        ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt z)
  · apply Finset.analyticAt_sum
    intro p hp
    apply AnalyticAt.mul analyticAt_const
    apply AnalyticAt.clog
    · exact ((analyticAt_root (physicalRootDomain_slit hz p.1)).comp (f := fun w : Point d => w p.1)
        ((ContinuousLinearMap.proj (R := ℂ) p.1).analyticAt z)).add
        ((analyticAt_root (physicalRootDomain_slit hz p.2)).comp (f := fun w : Point d => w p.2)
          ((ContinuousLinearMap.proj (R := ℂ) p.2).analyticAt z))
    · exact rootSum_slit hz p.1 p.2

theorem analyticAt_physicalGauge {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    {z : Point d} (hz : z ∈ PhysicalRootDomain d) :
    AnalyticAt ℂ (physicalGauge β c) z := (analyticAt_physicalGaugeLog β c hz).cexp

private theorem sum_upperPairs_first {d : ℕ} (i : Fin d) (f : Fin d × Fin d → ℂ) :
    (∑ p ∈ upperPairs d, if p.1=i then f p else 0) =
      ∑ j, if i < j then f (i,j) else 0 := by
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
    (∑ p ∈ upperPairs d, if p.2=i then f p else 0) =
      ∑ j, if j < i then f (j,i) else 0 := by
  classical
  simp only [upperPairs,Finset.sum_filter,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki
    simp [hki]
  · simp

private theorem rootPairCorrection_eq {d : ℕ} (β : ℂ) (c r : Fin d → ℂ)
    (i j : Fin d) :
    rootPairExponent β c i j * (1 / (2*r i)) / (r i+r j) =
      rootPairCorrection β c r i j := by
  simp only [rootPairExponent,rootPairCorrection,div_eq_mul_inv,mul_inv_rev]
  norm_num
  ring

private theorem sum_upperPairs_rootDerivative {d : ℕ}
    (β : ℂ) (c r : Fin d → ℂ) (i : Fin d) :
    (∑ p ∈ upperPairs d, rootPairExponent β c p.1 p.2 *
      ((if p.1=i then 1/(2*r p.1) else 0) +
        (if p.2=i then 1/(2*r p.2) else 0)) / (r p.1+r p.2)) =
      rootCorrection β c r i := by
  classical
  have he (p : Fin d × Fin d) :
      rootPairExponent β c p.1 p.2 *
      ((if p.1=i then 1/(2*r p.1) else 0) +
        (if p.2=i then 1/(2*r p.2) else 0)) / (r p.1+r p.2) =
      (if p.1=i then rootPairCorrection β c r p.1 p.2 else 0) +
      (if p.2=i then rootPairCorrection β c r p.2 p.1 else 0) := by
    rw [mul_add,add_div]
    congr 1
    · split_ifs <;> simp only [rootPairCorrection_eq,mul_zero,zero_div]
    · split_ifs with hp
      · rw [rootPairExponent_symm β c p.1 p.2,add_comm (r p.1),rootPairCorrection_eq]
      · simp
  simp_rw [he]
  rw [Finset.sum_add_distrib,sum_upperPairs_first,sum_upperPairs_second]
  unfold rootCorrection
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  rw [← Finset.sum_add_distrib]
  have hsplit : (∑ j, ((if i < j then rootPairCorrection β c r i j else 0) +
      (if j < i then rootPairCorrection β c r i j else 0))) =
      ∑ j, if j=i then 0 else rootPairCorrection β c r i j := by
    apply Finset.sum_congr rfl
    intro j _
    rcases lt_trichotomy i j with hj | rfl | hj
    · simp [hj,not_lt.mpr hj.le,hj.ne']
    · simp
    · simp [hj,not_lt.mpr hj.le,hj.ne]
  rw [hsplit,Finset.sum_ite,Finset.sum_const_zero,zero_add]
  simp only [Finset.filter_ne',Finset.filter_eq',Finset.mem_univ,if_true]
  exact Finset.sum_erase_eq_sub (Finset.mem_univ i)

theorem hasDerivAt_physicalGaugeLog {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    {z : Point d} (hz : z ∈ PhysicalRootDomain d) (i : Fin d) :
    HasDerivAt (fun w => physicalGaugeLog β c (Function.update z i w))
      (scalarWKBLogDerivative (c i) (z i)+physicalCorrection β c i z) (z i) := by
  have hs (j : Fin d) : HasDerivAt
      (fun w => scalarWKBLog (c j) (Function.update z i w j))
      (if j=i then scalarWKBLogDerivative (c j) (z j) else 0) (z i) := by
    by_cases hji : j=i
    · subst j
      simpa only [Function.update_same,if_pos rfl] using
        hasDerivAt_scalarWKBLog (c i) (physicalRootDomain_slit hz i)
    · simpa only [Function.update_of_ne hji,if_neg hji] using
        hasDerivAt_const (z i) (scalarWKBLog (c j) (z j))
  have hr (j : Fin d) : HasDerivAt (fun w => root (Function.update z i w j))
      (if j=i then 1/(2*root (z j)) else 0) (z i) := by
    by_cases hji : j=i
    · subst j
      simpa only [Function.update_same,if_pos rfl] using
        hasDerivAt_root (physicalRootDomain_slit hz i)
    · simpa only [Function.update_of_ne hji,if_neg hji] using
        hasDerivAt_const (z i) (root (z j))
  have hphase := HasDerivAt.sum (u := Finset.univ) (fun j _ => hs j)
  have hp := HasDerivAt.sum (u := upperPairs d) (fun p _ =>
    (((hr p.1).add (hr p.2)).clog
      (by simpa only [Function.update_eq_self] using rootSum_slit hz p.1 p.2)).const_mul
        (rootPairExponent β c p.1 p.2))
  convert hphase.add hp using 1
  simp only [Function.update_eq_self,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp_rw [← mul_div_assoc]
  exact congrArg (fun t => scalarWKBLogDerivative (c i) (z i)+t)
    (sum_upperPairs_rootDerivative β c (fun j => root (z j)) i).symm

theorem coordDeriv_physicalGaugeLog {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    {z : Point d} (hz : z ∈ PhysicalRootDomain d) (i : Fin d) :
    coordDeriv i (physicalGaugeLog β c) z =
      scalarWKBLogDerivative (c i) (z i)+physicalCorrection β c i z :=
  (hasDerivAt_physicalGaugeLog β c hz i).deriv

theorem analyticAt_physicalCorrection {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (hβ : β ≠ 0) {z : Point d} (hz : z ∈ PhysicalRootDomain d) (i : Fin d) :
    AnalyticAt ℂ (physicalCorrection β c i) z := by
  have hr j : AnalyticAt ℂ (fun w : Point d => root (w j)) z :=
    (analyticAt_root (hz j)).comp (f := fun w : Point d => w j)
      ((ContinuousLinearMap.proj (R := ℂ) j).analyticAt z)
  unfold physicalCorrection rootCorrection rootPairCorrection
  apply Finset.analyticAt_sum
  intro j hj
  exact analyticAt_const.div ((analyticAt_const.mul (hr i)).mul ((hr i).add (hr j)))
    (mul_ne_zero (mul_ne_zero hβ (root_ne_zero _))
      (Complex.slitPlane_ne_zero (rootSum_slit hz i j)))

theorem analyticAt_scalarWKBLogDerivative_coord {d : ℕ}
    (c : Fin d → ℂ) {z : Point d} (hz : z ∈ PhysicalRootDomain d) (i : Fin d) :
    AnalyticAt ℂ (fun w : Point d => scalarWKBLogDerivative (c i) (w i)) z := by
  have hp := (ContinuousLinearMap.proj (R := ℂ) i).analyticAt z
  have hr := (analyticAt_root (hz i)).comp (f := fun w : Point d => w i) hp
  exact (analyticAt_const.mul hr).sub
    (analyticAt_const.div (analyticAt_const.mul hp)
      (mul_ne_zero (by norm_num) (Complex.slitPlane_ne_zero (hz i))))

theorem secondPartial_physicalGaugeLog {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (hβ : β ≠ 0) {z : Point d} (hz : z ∈ PhysicalRootDomain d) (i : Fin d) :
    secondPartial i (physicalGaugeLog β c) z =
      c i/(2*root (z i)) + 1/(4*(z i)^2) +
        coordDeriv i (physicalCorrection β c i) z := by
  have heq : coordDeriv i (physicalGaugeLog β c) =ᶠ[𝓝 z]
      (fun w => scalarWKBLogDerivative (c i) (w i)+physicalCorrection β c i w) := by
    filter_upwards [(physicalRootDomain_isOpen d).eventually_mem hz] with w hw
    exact coordDeriv_physicalGaugeLog β c hw i
  unfold secondPartial
  rw [coordDeriv_congr_nhds heq]
  change coordDeriv i ((fun w => scalarWKBLogDerivative (c i) (w i)) +
    physicalCorrection β c i) z = _
  rw [coordDeriv_add_analytic (analyticAt_scalarWKBLogDerivative_coord c hz i)
    (analyticAt_physicalCorrection β c hβ hz i)]
  congr 1
  change deriv (fun w => scalarWKBLogDerivative (c i) (Function.update z i w i)) (z i) = _
  simp only [Function.update_self]
  exact (hasDerivAt_scalarWKBLogDerivative (c i) (hz i)).deriv

/-- The remaining scalar potential before division by `zᵢ`. Every displayed
term has degree minus two in the original spectral coordinates. -/
def physicalScalarRemainder {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (i : Fin d) (z : Point d) : ℂ :=
  5/(16*(z i)^2) + coordDeriv i (physicalCorrection β c i) z -
    physicalCorrection β c i z/(2*z i) + (physicalCorrection β c i z)^2 +
    (2/β)*∑ j ∈ Finset.univ.erase i,
      (c i*c j*(physicalCorrection β c i z-1/(4*z i)) -
        c i^2*(physicalCorrection β c j z-1/(4*z j))) / (z i-z j)

/-- Exact cancellation of the linear edge potential and the complete
order-minus-one-half pair contribution in the physical WKB factor. -/
theorem physicalGauge_scalar_cancellation {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (hβ : β ≠ 0) {z : Point d} (hz : z ∈ PhysicalRootDomain d)
    (hcollision : CollisionFree z) (i : Fin d) :
    secondPartial i (physicalGaugeLog β c) z +
      (coordDeriv i (physicalGaugeLog β c) z)^2 - c i^2*z i +
      (2/β)*∑ j ∈ Finset.univ.erase i,
        (c i*c j*coordDeriv i (physicalGaugeLog β c) z -
          c i^2*coordDeriv j (physicalGaugeLog β c) z)/(z i-z j) =
      physicalScalarRemainder β c i z := by
  simp only [secondPartial_physicalGaugeLog β c hβ hz,
    coordDeriv_physicalGaugeLog β c hz]
  have hscalar := scalarWKB_riccati_residual (c i) (hz i)
  rw [(hasDerivAt_scalarWKBLogDerivative (c i) (hz i)).deriv] at hscalar
  have hcancel := root_correction_linear_cancellation β c (fun j => root (z j)) z hβ
    (fun j => root_sq (Complex.slitPlane_ne_zero (hz j)))
    (fun j => root_ne_zero (z j)) hcollision i
  change 2*(c i*root (z i))*physicalCorrection β c i z +
    (2/β)*∑ j ∈ Finset.univ.erase i,
      (c i*c j*(c i*root (z i))-c i^2*(c j*root (z j)))/(z i-z j)=0 at hcancel
  have hsplit (j : Fin d) :
      (c i*c j*(scalarWKBLogDerivative (c i) (z i)+physicalCorrection β c i z) -
        c i^2*(scalarWKBLogDerivative (c j) (z j)+physicalCorrection β c j z))/(z i-z j) =
      (c i*c j*(c i*root (z i))-c i^2*(c j*root (z j)))/(z i-z j) +
      (c i*c j*(physicalCorrection β c i z-1/(4*z i)) -
        c i^2*(physicalCorrection β c j z-1/(4*z j)))/(z i-z j) := by
    unfold scalarWKBLogDerivative
    ring
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib,mul_add]
  unfold physicalScalarRemainder
  unfold scalarWKBLogDerivative at hscalar ⊢
  linear_combination hscalar+hcancel

end BourgadeHuang.EdgeCMS
