import BourgadeHuang.CMS.PhysicalPhaseSelection
import BourgadeHuang.CMS.AffineRayLimits

/-! Genuine two-scale rays used in the balanced sectorial asymptotics.
Real gaps grow linearly; imaginary gaps grow at either of two exact scales. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BourgadeHuang.CMS
variable {d : ℕ}

def twoScaleRay (ξ δ : Fin d → ℝ) (σ : Fin d → Sign) (k : ℕ) (r : ℝ) : Point d :=
  fun i => Complex.ofReal (r*ξ i)+Complex.I*signValue (σ i)*
    Complex.ofReal (r^(k+2)+r*δ i)

def twoScaleGapExponent (k : ℕ) (σ : Fin d → Sign) (i j : Fin d) : ℕ :=
  if σ i=σ j then 1 else k+2

def twoScaleGapLimit (ξ δ : Fin d → ℝ) (σ : Fin d → Sign) (i j : Fin d) : ℂ :=
  if σ i=σ j then Complex.ofReal (ξ j-ξ i)+
    Complex.I*signValue (σ i)*Complex.ofReal (δ j-δ i)
  else Complex.I*(signValue (σ j)-signValue (σ i))

@[simp] theorem twoScaleRay_re (ξ δ : Fin d → ℝ) (σ : Fin d → Sign)
    (k : ℕ) (r : ℝ) (i : Fin d) : (twoScaleRay ξ δ σ k r i).re=r*ξ i := by
  simp only [twoScaleRay,Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,one_mul,sub_zero,
    zero_sub]
  cases hs : σ i <;> simp [hs,signValue]

theorem twoScaleRay_gap_re (ξ δ : Fin d → ℝ) (σ : Fin d → Sign)
    (k : ℕ) (r : ℝ) (i j : Fin d) :
    (twoScaleRay ξ δ σ k r j-twoScaleRay ξ δ σ k r i).re=r*(ξ j-ξ i) := by
  simp only [Complex.sub_re,twoScaleRay_re,mul_sub]

theorem twoScaleRay_eventually_orderedGapDomain (ξ δ : Fin d → ℝ) (σ : Fin d → Sign)
    (k : ℕ) (hξ : StrictMono ξ) (R : ℝ) :
    ∀ᶠr : ℝ in atTop,twoScaleRay ξ δ σ k r ∈ OrderedGapDomain d R := by
  have hi (i j : Fin d) : ∀ᶠr : ℝ in atTop,i<j →
      R<(twoScaleRay ξ δ σ k r j-twoScaleRay ξ δ σ k r i).re := by
    by_cases hij : i<j
    · have hp : 0<ξ j-ξ i := sub_pos.mpr (hξ hij)
      filter_upwards [eventually_gt_atTop (R/(ξ j-ξ i))] with r hr _
      rw [twoScaleRay_gap_re]
      exact (div_lt_iff₀ hp).mp hr
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hij h))
  exact Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hi i))

theorem twoScaleRay_gap_eq (ξ δ : Fin d → ℝ) (σ : Fin d → Sign)
    (k : ℕ) (r : ℝ) (i j : Fin d) :
    twoScaleRay ξ δ σ k r j-twoScaleRay ξ δ σ k r i =
      (r:ℂ)*(Complex.ofReal (ξ j-ξ i)+Complex.I*
        (signValue (σ j)*Complex.ofReal (δ j)-signValue (σ i)*Complex.ofReal (δ i)))+
      Complex.I*(signValue (σ j)-signValue (σ i))*(r:ℂ)^(k+2) := by
  simp only [twoScaleRay,Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_pow,
    Complex.ofReal_sub]
  ring

theorem twoScaleRay_normalized_gap_same (ξ δ : Fin d → ℝ) (σ : Fin d → Sign)
    (k : ℕ) {r : ℝ} (hr : r≠0) (i j : Fin d) (hs : σ i=σ j) :
    (twoScaleRay ξ δ σ k r j-twoScaleRay ξ δ σ k r i)/(r:ℂ) =
      twoScaleGapLimit ξ δ σ i j := by
  rw [twoScaleRay_gap_eq,twoScaleGapLimit,if_pos hs,← hs]
  have hr' : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr
  simp only [sub_self,mul_zero,zero_mul,add_zero,Complex.ofReal_sub]
  field_simp
  ring

theorem twoScaleRay_normalized_gap_opposite (ξ δ : Fin d → ℝ) (σ : Fin d → Sign)
    (k : ℕ) {r : ℝ} (hr : r≠0) (i j : Fin d) (hs : σ i≠σ j) :
    (twoScaleRay ξ δ σ k r j-twoScaleRay ξ δ σ k r i)/(r:ℂ)^(k+2) =
      ((r:ℂ)⁻¹)^(k+1)*(Complex.ofReal (ξ j-ξ i)+Complex.I*
        (signValue (σ j)*Complex.ofReal (δ j)-signValue (σ i)*Complex.ofReal (δ i)))+
      twoScaleGapLimit ξ δ σ i j := by
  rw [twoScaleRay_gap_eq,twoScaleGapLimit,if_neg hs]
  have hr' : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr
  rw [inv_pow,show k+2=(k+1)+1 by omega,pow_succ]
  field_simp
  ring

theorem tendsto_twoScaleRay_normalized_gap (ξ δ : Fin d → ℝ) (σ : Fin d → Sign)
    (k : ℕ) (i j : Fin d) :
    Tendsto (fun r : ℝ => (twoScaleRay ξ δ σ k r j-twoScaleRay ξ δ σ k r i)/
      (r:ℂ)^twoScaleGapExponent k σ i j) atTop (𝓝 (twoScaleGapLimit ξ δ σ i j)) := by
  by_cases hs : σ i=σ j
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    simpa only [twoScaleGapExponent,if_pos hs,pow_one] using
      (twoScaleRay_normalized_gap_same ξ δ σ k hr.ne' i j hs).symm
  · have h := ((tendsto_complex_real_inv_atTop.pow (k+1)).mul_const
        (Complex.ofReal (ξ j-ξ i)+Complex.I*
          (signValue (σ j)*Complex.ofReal (δ j)-signValue (σ i)*Complex.ofReal (δ i)))).add_const
      (twoScaleGapLimit ξ δ σ i j)
    simp only [zero_pow (Nat.succ_ne_zero k),zero_mul,zero_add] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    simpa only [twoScaleGapExponent,if_neg hs] using
      (twoScaleRay_normalized_gap_opposite ξ δ σ k hr.ne' i j hs).symm

theorem twoScaleGapLimit_mem_slitPlane (ξ δ : Fin d → ℝ) (σ : Fin d → Sign)
    (hξ : StrictMono ξ) {i j : Fin d} (hij : i<j) :
    twoScaleGapLimit ξ δ σ i j ∈ Complex.slitPlane := by
  by_cases hs : σ i=σ j
  · apply Or.inl
    rw [twoScaleGapLimit,if_pos hs]
    cases h : σ i <;> simpa [h,signValue] using sub_pos.mpr (hξ hij)
  · apply Or.inr
    rw [twoScaleGapLimit,if_neg hs]
    cases hi : σ i <;> cases hj : σ j <;> simp_all [signValue] <;> norm_num

theorem twoScaleGapLimit_ne_zero (ξ δ : Fin d → ℝ) (σ : Fin d → Sign)
    (hξ : StrictMono ξ) {i j : Fin d} (hij : i<j) :
    twoScaleGapLimit ξ δ σ i j≠0 :=
  Complex.slitPlane_ne_zero (twoScaleGapLimit_mem_slitPlane ξ δ σ hξ hij)

end BourgadeHuang.CMS
