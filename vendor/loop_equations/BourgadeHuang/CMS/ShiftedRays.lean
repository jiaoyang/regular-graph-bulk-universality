import BourgadeHuang.CMS.GeneralCouplingJets
import BourgadeHuang.CMS.RayIndependence

/-! Actual shifted-ray geometry and spectral gap used in the general-coupling
sectorial construction. Separation grows uniformly even for mixed signs. -/
noncomputable section
open scoped BigOperators
open Set
namespace BourgadeHuang.CMS

/-- Ordered chamber with a fixed positive gap in real parts. -/
def OrderedGapDomain (d : ℕ) (D : ℝ) : Set (Point d) :=
  {z | ∀ i j, i < j → D < (z j-z i).re}

def shiftedDirection {d : ℕ} (σ : Fin d → Sign) (j : Fin d) : ℂ :=
  (j.val : ℂ)+Complex.I*signValue (σ j)

def shiftedRay {d : ℕ} (σ : Fin d → Sign) (z : Point d) (r : ℝ) : Point d :=
  fun j => z j+(r:ℂ)*shiftedDirection σ j

@[simp] theorem shiftedDirection_re {d : ℕ} (σ : Fin d → Sign) (j : Fin d) :
    (shiftedDirection σ j).re = j.val := by cases h : σ j <;> simp [shiftedDirection,signValue,h]

@[simp] theorem shiftedDirection_im {d : ℕ} (σ : Fin d → Sign) (j : Fin d) :
    (shiftedDirection σ j).im = realSign (σ j) := by
  cases h : σ j <;> simp [shiftedDirection,signValue,realSign,h]

theorem shiftedRay_mem_orderedGapDomain {d : ℕ} {D r : ℝ}
    (σ : Fin d → Sign) {z : Point d} (hz : z∈OrderedGapDomain d D) (hr : 0≤r) :
    shiftedRay σ z r∈OrderedGapDomain d D := by
  intro i j hij
  have hgap := hz i j hij
  have hji : (0:ℝ)≤j.val-i.val := by exact sub_nonneg.mpr (Nat.cast_le.mpr (Nat.le_of_lt hij))
  have hmul := mul_nonneg hr hji
  simpa only [shiftedRay,Complex.sub_re,Complex.add_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,shiftedDirection_re] using
    (show D < (z j).re+r*j.val-((z i).re+r*i.val) by simp only [Complex.sub_re] at hgap; nlinarith)

theorem orderedGapDomain_subset_orderedDomain {d : ℕ} {D : ℝ} (hD : 0≤D) :
    OrderedGapDomain d D ⊆ OrderedDomain d := by
  intro z hz i j hij
  have h := hz i j hij
  simp only [Complex.sub_re] at h
  linarith

private theorem norm_le_norm_add_nonneg_real (z : ℂ) (a : ℝ)
    (hz : 0≤z.re) (ha : 0≤a) : ‖z‖≤‖z+(a:ℂ)‖ := by
  have hsq : ‖z‖^2≤‖z+(a:ℂ)‖^2 := by
    simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,
      Complex.add_re,Complex.ofReal_re,Complex.add_im,Complex.ofReal_im,add_zero]
    nlinarith
  nlinarith [norm_nonneg z,norm_nonneg (z+(a:ℂ))]

/-- Each pair remains separated by one quarter of the initial separation plus
elapsed ray time. No minima or nonempty-pair convention is needed. -/
theorem shiftedRay_pair_separation {d : ℕ} (σ : Fin d → Sign) {z : Point d}
    (hz : z∈OrderedDomain d) {i j : Fin d} (hij : i<j) {R r : ℝ}
    (hR : R≤‖z j-z i‖) (hr : 0≤r) :
    (R+r)/4≤‖shiftedRay σ z r j-shiftedRay σ z r i‖ := by
  let a : ℝ := r*((j.val:ℝ)-i.val)
  let b : ℝ := r*(realSign (σ j)-realSign (σ i))
  have hn : (1:ℝ)≤(j.val:ℝ)-i.val := by
    have h : i.val+1≤j.val := hij
    have hcast : (i.val:ℝ)+1≤j.val := by exact_mod_cast h
    linarith
  have ha : 0≤a := mul_nonneg hr (by linarith)
  have har : r≤a := by dsimp [a]; nlinarith
  have hzr : 0≤(z j-z i).re := by simpa only [Complex.sub_re] using sub_nonneg.mpr (hz i j hij).le
  have heq : shiftedRay σ z r j-shiftedRay σ z r i =
      (z j-z i+(a:ℂ))+Complex.I*(b:ℂ) := by
    apply Complex.ext <;>
      simp only [shiftedRay,Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
        Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
        shiftedDirection_re,shiftedDirection_im,Complex.I_re,Complex.I_im] <;>
      dsimp [a,b] <;> ring
  have hb : |b|≤2*r := by
    have hsign : |realSign (σ j)-realSign (σ i)|≤2 := by
      cases σ j <;> cases σ i <;> norm_num [realSign]
    rw [show b=r*(realSign (σ j)-realSign (σ i)) from rfl,abs_mul,abs_of_nonneg hr]
    nlinarith
  have hnormb : ‖Complex.I*(b:ℂ)‖≤2*r := by simpa using hb
  have hbase : ‖z j-z i‖≤‖z j-z i+(a:ℂ)‖ := norm_le_norm_add_nonneg_real _ _ hzr ha
  have htriangle := norm_sub_norm_le (z j-z i+(a:ℂ)) (-(Complex.I*(b:ℂ)))
  have hlow : R-2*r≤‖shiftedRay σ z r j-shiftedRay σ z r i‖ := by
    rw [heq]
    simp only [norm_neg,sub_neg_eq_add] at htriangle
    linarith
  have hre : r≤‖shiftedRay σ z r j-shiftedRay σ z r i‖ := by
    have h := Complex.re_le_norm (shiftedRay σ z r j-shiftedRay σ z r i)
    rw [heq]
    rw [heq] at h
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_self,add_zero] at h
    linarith
  linarith

/-- Uniform pairwise lower bounds persist along the full shifted ray. -/
theorem shiftedRay_separation {d : ℕ} (σ : Fin d → Sign) {z : Point d}
    (hz : z∈OrderedDomain d) {R r : ℝ}
    (hR : ∀i j,i≠j→R≤‖z i-z j‖) (hr : 0≤r) :
    ∀i j,i≠j→(R+r)/4≤‖shiftedRay σ z r i-shiftedRay σ z r j‖ := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · simpa only [norm_sub_rev] using shiftedRay_pair_separation σ hz h (hR j i hij.symm) hr
  · exact shiftedRay_pair_separation σ hz h (hR i j hij) hr

/-- The diagonal of the nonempty radial jet block. -/
def radialDiagonal {d : ℕ} (a : Fin d → ℝ) (σ : Fin d → Sign)
    (s : Finset (Fin d)) : ℂ :=
  ∑j∈s,-Complex.I*(a j:ℂ)*signValue (σ j)*shiftedDirection σ j

theorem radialDiagonal_re {d : ℕ} (a : Fin d → ℝ) (σ : Fin d → Sign)
    (s : Finset (Fin d)) : (radialDiagonal a σ s).re=∑j∈s,a j := by
  simp only [radialDiagonal,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j hj
  cases h : σ j <;> simp [shiftedDirection,signValue,h,Complex.mul_re,Complex.mul_im]

theorem radialDiagonal_gap {d : ℕ} (a : Fin d → ℝ) (σ : Fin d → Sign)
    {c : ℝ} (hc : 0≤c) (ha : ∀j,c≤a j) {s : Finset (Fin d)} (hs : s.Nonempty) :
    c≤(radialDiagonal a σ s).re := by
  rw [radialDiagonal_re]
  obtain ⟨j,hj⟩ := hs
  exact (ha j).trans (Finset.single_le_sum (fun i _ => hc.trans (ha i)) hj)

end BourgadeHuang.CMS
