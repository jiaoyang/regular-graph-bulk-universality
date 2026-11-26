import BourgadeHuang.EdgeCMS.PhysicalGauge
import BourgadeHuang.EdgeCMS.AiryPullback
import BourgadeHuang.EdgeCMS.SectorialReduction
import BourgadeHuang.EdgeCMS.PhysicalChamber

/-! Actual homogeneous coefficients of the physical edge WKB system,
pulled back by the genuine Airy inverse. -/
noncomputable section
open scoped BigOperators Topology
open Filter Set
namespace BourgadeHuang.EdgeCMS
open CMS

def rootCone (d : ℕ) : OpenCone d where
  carrier := PhysicalRootDomain d
  isOpen := physicalRootDomain_isOpen d
  scale_mem := by
    intro t ht z hz i
    exact positive_real_mul_mem_slitPlane ht (hz i)

def physicalCorrectionCoefficient {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (hβ : β ≠ 0) (i : Fin d) : Coefficient (rootCone d) where
  eval := physicalCorrection β c i
  analytic := fun z hz => analyticAt_physicalCorrection β c hβ hz i

theorem physicalCorrection_scale {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (hβ : β ≠ 0) (i : Fin d) {t : ℝ} (ht : 0<t)
    {z : Point d} (hz : z ∈ PhysicalRootDomain d) :
    physicalCorrection β c i ((t : ℂ) • z) = (t : ℂ)⁻¹*physicalCorrection β c i z := by
  let u := Real.sqrt t
  have hu : 0<u := Real.sqrt_pos.mpr ht
  have hu2 : u^2=t := Real.sq_sqrt ht.le
  have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hroot (j : Fin d) : root (((t : ℂ) • z) j) = (u : ℂ)*root (z j) := by
    change root ((t : ℂ)*z j) = _
    rw [← hu2,Complex.ofReal_pow]
    exact root_ofReal_sq_mul hu (Complex.slitPlane_ne_zero (hz j))
  unfold physicalCorrection rootCorrection rootPairCorrection
  simp_rw [hroot]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hs := Complex.slitPlane_ne_zero (rootSum_slit hz i j)
  have htcast : (t : ℂ)=(u : ℂ)^2 := by exact_mod_cast hu2.symm
  rw [htcast]
  rw [← mul_add]
  field_simp [hu0,hβ,root_ne_zero (z i),hs]
  <;> ring <;> simp_all

theorem physicalCorrectionCoefficient_homogeneous {d : ℕ}
    (β : ℂ) (c : Fin d → ℂ) (hβ : β ≠ 0) (i : Fin d) :
    (physicalCorrectionCoefficient β c hβ i).Homogeneous 1 := by
  intro t ht z hz
  simpa only [physicalCorrectionCoefficient,pow_one] using
    physicalCorrection_scale β c hβ i ht hz

theorem physicalCorrection_derivative_scale {d : ℕ}
    (β : ℂ) (c : Fin d → ℂ) (hβ : β ≠ 0) (i j : Fin d)
    {t : ℝ} (ht : 0<t) {z : Point d} (hz : z ∈ PhysicalRootDomain d) :
    coordDeriv j (physicalCorrection β c i) ((t : ℂ) • z) =
      ((t : ℂ)⁻¹)^2*coordDeriv j (physicalCorrection β c i) z :=
  Coefficient.homogeneous_derivative (physicalCorrectionCoefficient_homogeneous β c hβ i) j ht hz

def physicalFirstRaw {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (i j : Fin d) (z : Point d) : ℂ :=
  (if j=i then 2*physicalCorrection β c i z/root (z i) +
    (2/β)*∑ k ∈ Finset.univ.erase i, c i*c k/(root (z i)*(z i-z k)) else 0) -
  (2/β)*c i^2*root (z j)/(z i*(z i-z j))

def physicalScalarRaw {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (i : Fin d) (z : Point d) : ℂ := physicalScalarRemainder β c i z/z i

theorem analyticAt_physicalScalarRemainder {d : ℕ}
    (β : ℂ) (c : Fin d → ℂ) (hβ : β ≠ 0)
    {z : Point d} (hz : z ∈ PhysicalRootDomain d) (hcoll : CollisionFree z)
    (i : Fin d) : AnalyticAt ℂ (physicalScalarRemainder β c i) z := by
  have hp j := (ContinuousLinearMap.proj (R := ℂ) j).analyticAt z
  have hΩ j := analyticAt_physicalCorrection β c hβ hz j
  have hzi j := Complex.slitPlane_ne_zero (hz j)
  unfold physicalScalarRemainder
  apply AnalyticAt.add
  · exact (((analyticAt_const.div (analyticAt_const.mul ((hp i).pow 2))
      (mul_ne_zero (by norm_num) (pow_ne_zero _ (hzi i)))).add
      (analyticAt_coordDeriv (hΩ i) i)).sub
      ((hΩ i).div (analyticAt_const.mul (hp i))
        (mul_ne_zero (by norm_num) (hzi i)))).add ((hΩ i).pow 2)
  · apply AnalyticAt.mul analyticAt_const
    apply Finset.analyticAt_sum
    intro j hj
    have hdiff k : AnalyticAt ℂ (fun w : Point d =>
        physicalCorrection β c k w - 1 / (4 * w k)) z :=
      (hΩ k).sub (analyticAt_const.div (analyticAt_const.mul (hp k))
        (mul_ne_zero (by norm_num) (hzi k)))
    exact ((analyticAt_const.mul (hdiff i)).sub (analyticAt_const.mul (hdiff j))).div
      ((hp i).sub (hp j)) (hcoll.sub_ne_zero (Finset.ne_of_mem_erase hj).symm)

theorem analyticAt_physicalScalarRaw {d : ℕ}
    (β : ℂ) (c : Fin d → ℂ) (hβ : β ≠ 0)
    {z : Point d} (hz : z ∈ PhysicalRootDomain d) (hcoll : CollisionFree z)
    (i : Fin d) : AnalyticAt ℂ (physicalScalarRaw β c i) z :=
  (analyticAt_physicalScalarRemainder β c hβ hz hcoll i).div
    ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt z)
    (Complex.slitPlane_ne_zero (hz i))

theorem analyticAt_physicalFirstRaw {d : ℕ}
    (β : ℂ) (c : Fin d → ℂ) (hβ : β ≠ 0)
    {z : Point d} (hz : z ∈ PhysicalRootDomain d) (hcoll : CollisionFree z)
    (i j : Fin d) : AnalyticAt ℂ (physicalFirstRaw β c i j) z := by
  have hp k := (ContinuousLinearMap.proj (R := ℂ) k).analyticAt z
  have hr k := (analyticAt_root (hz k)).comp (f := fun w : Point d => w k) (hp k)
  have hsum : AnalyticAt ℂ (fun w : Point d =>
      (2/β)*∑ k ∈ Finset.univ.erase i, c i*c k/(root (w i)*(w i-w k))) z := by
    apply AnalyticAt.mul analyticAt_const
    apply Finset.analyticAt_sum
    intro k hk
    exact analyticAt_const.div ((hr i).mul ((hp i).sub (hp k)))
      (mul_ne_zero (root_ne_zero _) (hcoll.sub_ne_zero (Finset.ne_of_mem_erase hk).symm))
  have hdiag : AnalyticAt ℂ (fun w : Point d =>
      2*physicalCorrection β c i w/root (w i) +
        (2/β)*∑ k ∈ Finset.univ.erase i, c i*c k/(root (w i)*(w i-w k))) z :=
    ((analyticAt_const.mul (analyticAt_physicalCorrection β c hβ hz i)).div
    (hr i) (root_ne_zero _)).add hsum
  change AnalyticAt ℂ (fun w => physicalFirstRaw β c i j w) z
  by_cases hji : j=i
  · subst j
    simpa only [physicalFirstRaw,if_pos rfl,sub_self,mul_zero,div_zero,sub_zero] using hdiag
  · simp only [physicalFirstRaw,if_neg hji,zero_sub]
    exact ((analyticAt_const.mul (hr j)).div ((hp i).mul ((hp i).sub (hp j)))
      (mul_ne_zero (Complex.slitPlane_ne_zero (hz i)) (hcoll.sub_ne_zero (Ne.symm hji)))).neg


theorem physicalScalarRemainder_scale {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (hβ : β ≠ 0) (i : Fin d) {t : ℝ} (ht : 0<t)
    {z : Point d} (hz : z ∈ PhysicalRootDomain d) (hcoll : CollisionFree z) :
    physicalScalarRemainder β c i ((t : ℂ) • z) =
      ((t : ℂ)⁻¹)^2 * physicalScalarRemainder β c i z := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hzi := Complex.slitPlane_ne_zero (hz i)
  have hs : (∑ j ∈ Finset.univ.erase i,
      (c i*c j*(physicalCorrection β c i ((t:ℂ)•z)-1/(4*((t:ℂ)•z) i))-
        c i^2*(physicalCorrection β c j ((t:ℂ)•z)-1/(4*((t:ℂ)•z) j))) /
          (((t:ℂ)•z) i-((t:ℂ)•z) j)) =
      ((t:ℂ)⁻¹)^2 * ∑ j ∈ Finset.univ.erase i,
      (c i*c j*(physicalCorrection β c i z-1/(4*z i))-
        c i^2*(physicalCorrection β c j z-1/(4*z j)))/(z i-z j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [physicalCorrection_scale β c hβ i ht hz,
      physicalCorrection_scale β c hβ j ht hz]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [← mul_sub]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
    ring
  unfold physicalScalarRemainder
  rw [hs,physicalCorrection_scale β c hβ i ht hz,
    physicalCorrection_derivative_scale β c hβ i i ht hz]
  simp only [Pi.smul_apply,smul_eq_mul]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

theorem physicalScalarRaw_scale {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (hβ : β ≠ 0) (i : Fin d) {t : ℝ} (ht : 0<t)
    {z : Point d} (hz : z ∈ PhysicalRootDomain d) (hcoll : CollisionFree z) :
    physicalScalarRaw β c i ((t : ℂ) • z) =
      ((t : ℂ)⁻¹)^3 * physicalScalarRaw β c i z := by
  unfold physicalScalarRaw
  rw [physicalScalarRemainder_scale β c hβ i ht hz hcoll]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [div_mul_eq_div_mul_one_div, ← inv_eq_one_div]
  ring

theorem physicalFirstRaw_sq_scale {d : ℕ} (β : ℂ) (c : Fin d → ℂ)
    (hβ : β ≠ 0) (i j : Fin d) {u : ℝ} (hu : 0<u)
    {z : Point d} (hz : z ∈ PhysicalRootDomain d) (hcoll : CollisionFree z) :
    physicalFirstRaw β c i j ((u : ℂ)^2 • z) =
      ((u : ℂ)⁻¹)^3 * physicalFirstRaw β c i j z := by
  have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hz0 k := Complex.slitPlane_ne_zero (hz k)
  have hroot k : root (((u : ℂ)^2 • z) k) = (u:ℂ)*root (z k) :=
    root_ofReal_sq_mul hu (hz0 k)
  have hΩ : physicalCorrection β c i ((u:ℂ)^2•z) =
      ((u:ℂ)⁻¹)^2*physicalCorrection β c i z := by
    simpa only [Complex.ofReal_pow,inv_pow] using
      physicalCorrection_scale β c hβ i (sq_pos_of_pos hu) hz
  have hs : (∑ k ∈ Finset.univ.erase i,
      c i*c k/(root (((u:ℂ)^2•z) i)*(((u:ℂ)^2•z) i-((u:ℂ)^2•z) k))) =
      ((u:ℂ)⁻¹)^3 * ∑ k ∈ Finset.univ.erase i,
        c i*c k/(root (z i)*(z i-z k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hroot]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [← mul_sub]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
    ring
  unfold physicalFirstRaw
  rw [hs,hΩ,hroot,hroot]
  simp only [Pi.smul_apply,smul_eq_mul]
  by_cases hji : j=i
  · subst j
    simp only [if_pos rfl,ite_true,sub_self,mul_zero,div_zero,sub_zero]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
    ring
  · simp only [if_neg hji,zero_sub]
    rw [← mul_sub]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
    have hi : (u:ℂ)*((u:ℂ)⁻¹)^4 = ((u:ℂ)⁻¹)^3 := by
      calc
        _ = ((u:ℂ)*(u:ℂ)⁻¹)*((u:ℂ)⁻¹)^3 := by ring
        _ = _ := by rw [mul_inv_cancel₀ hu0,one_mul]
    convert congrArg (fun a : ℂ => a *
      (-(2*β⁻¹*c i^2*root (z j)*(z i)⁻¹*(z i-z j)⁻¹))) hi using 1 <;> ring


/-- All collision-free slit coordinates, allowing mixtures of both halfplanes. -/
def physicalAiryCone (d : ℕ) : OpenCone d where
  carrier := {y | (∀i, y i∈Complex.slitPlane) ∧ CollisionFree y}
  isOpen := (physicalRootDomain_isOpen d).inter (isOpen_collisionFree d)
  scale_mem := by
    intro t ht y hy
    refine ⟨fun i => positive_real_mul_mem_slitPlane ht (hy.1 i),?_⟩
    intro i j hij
    apply hy.2
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr ht.ne') hij

theorem airyInverseCoordinates_mem_rootDomain {d : ℕ} (y : Point d) :
    airyInverseCoordinates y∈PhysicalRootDomain d := fun i => airyInverse_mem_slitPlane (y i)

theorem airyInverseCoordinates_collisionFree {d : ℕ} {y : Point d}
    (hy : y∈(physicalAiryCone d).carrier) : CollisionFree (airyInverseCoordinates y) := by
  intro i j hij
  apply hy.2
  have h := congrArg airyCoordinate hij
  simpa only [airyInverseCoordinates,airyCoordinate_airyInverse
    (Complex.slitPlane_ne_zero (hy.1 i)),airyCoordinate_airyInverse
    (Complex.slitPlane_ne_zero (hy.1 j))] using h

theorem airyInverseCoordinates_cube_scale {d : ℕ} {u : ℝ} (hu : 0<u)
    {y : Point d} (hy : ∀i,y i≠0) :
    airyInverseCoordinates ((u:ℂ)^3•y) = (u:ℂ)^2•airyInverseCoordinates y := by
  funext i
  exact airyInverse_ofReal_cube_mul hu (hy i)

def physicalFirstCoefficient {d : ℕ} (β : ℂ) (c : Fin d→ℂ) (hβ : β≠0)
    (i j : Fin d) : Coefficient (physicalAiryCone d) where
  eval y := physicalFirstRaw β c i j (airyInverseCoordinates y)
  analytic := by
    intro y hy
    exact (analyticAt_physicalFirstRaw β c hβ
      (airyInverseCoordinates_mem_rootDomain y) (airyInverseCoordinates_collisionFree hy) i j).comp
        (analyticAt_airyInverseCoordinates hy.1)

def physicalScalarCoefficient {d : ℕ} (β : ℂ) (c : Fin d→ℂ) (hβ : β≠0)
    (i : Fin d) : Coefficient (physicalAiryCone d) where
  eval y := physicalScalarRaw β c i (airyInverseCoordinates y)
  analytic := by
    intro y hy
    exact (analyticAt_physicalScalarRaw β c hβ
      (airyInverseCoordinates_mem_rootDomain y) (airyInverseCoordinates_collisionFree hy) i).comp
        (analyticAt_airyInverseCoordinates hy.1)

theorem physicalFirstCoefficient_homogeneous {d : ℕ}
    (β : ℂ) (c : Fin d→ℂ) (hβ : β≠0) (i j : Fin d) :
    (physicalFirstCoefficient β c hβ i j).Homogeneous 1 := by
  intro t ht y hy
  obtain ⟨u,hu,hu3⟩ := exists_positive_cube_root ht
  have huc : (u:ℂ)^3=(t:ℂ) := by exact_mod_cast hu3
  change physicalFirstRaw β c i j (airyInverseCoordinates ((t:ℂ)•y)) =
    ((t:ℂ)⁻¹)^1*physicalFirstRaw β c i j (airyInverseCoordinates y)
  rw [←huc,airyInverseCoordinates_cube_scale hu (fun i=>Complex.slitPlane_ne_zero (hy.1 i)),
    physicalFirstRaw_sq_scale β c hβ i j hu (airyInverseCoordinates_mem_rootDomain y)
      (airyInverseCoordinates_collisionFree hy),inv_pow,pow_one]

theorem physicalScalarCoefficient_homogeneous {d : ℕ}
    (β : ℂ) (c : Fin d→ℂ) (hβ : β≠0) (i : Fin d) :
    (physicalScalarCoefficient β c hβ i).Homogeneous 2 := by
  intro t ht y hy
  obtain ⟨u,hu,hu3⟩ := exists_positive_cube_root ht
  have huc : (u:ℂ)^3=(t:ℂ) := by exact_mod_cast hu3
  change physicalScalarRaw β c i (airyInverseCoordinates ((t:ℂ)•y)) =
    ((t:ℂ)⁻¹)^2*physicalScalarRaw β c i (airyInverseCoordinates y)
  rw [←huc,airyInverseCoordinates_cube_scale hu (fun i=>Complex.slitPlane_ne_zero (hy.1 i))]
  have h := physicalScalarRaw_scale β c hβ i (sq_pos_of_pos hu)
    (airyInverseCoordinates_mem_rootDomain y) (airyInverseCoordinates_collisionFree hy)
  rw [Complex.ofReal_pow] at h
  rw [h]
  simp only [inv_pow]
  ring

/-- The actual edge CMS system in Airy coordinates.  Both lower order
coefficients are constructed analytic functions and their degrees are proved. -/
def physicalSectorialData {d : ℕ} (β : ℂ) (c : Fin d→ℂ) (hβ : β≠0) :
    SectorialData (physicalAiryCone d) where
  phase i := 2*c i
  first := physicalFirstCoefficient β c hβ
  scalar := physicalScalarCoefficient β c hβ
  first_homogeneous := physicalFirstCoefficient_homogeneous β c hβ
  scalar_homogeneous := physicalScalarCoefficient_homogeneous β c hβ

end BourgadeHuang.EdgeCMS
