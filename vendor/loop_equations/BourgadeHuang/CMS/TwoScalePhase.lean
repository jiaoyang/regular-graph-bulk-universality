import BourgadeHuang.CMS.TwoScaleRays
import BourgadeHuang.CMS.BinaryChargeRays
import BourgadeHuang.OrthogonalBranchBalance

/-! Exact exponential phases of the two-scale rays, and strict suppression
of every competing numerator sign with the prescribed denominator signs. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BourgadeHuang.CMS

@[simp] theorem twoScaleRay_im {d : ℕ} (ξ δ : Fin d → ℝ) (σ : Fin d → Sign)
    (k : ℕ) (r : ℝ) (i : Fin d) :
    (twoScaleRay ξ δ σ k r i).im = realSign (σ i)*(r^(k+2)+r*δ i) := by
  simp only [twoScaleRay,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
    Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_re,mul_zero,zero_mul,
    zero_add,add_zero,sub_zero,one_mul]
  cases hs : σ i <;> simp [hs,signValue,realSign]

theorem twoScale_height_pos_eventually (b : ℝ) (k : ℕ) :
    ∀ᶠr : ℝ in atTop,0<r^(k+2)+r*b := by
  filter_upwards [eventually_gt_atTop (max 1 (-b))] with r hr
  have hr1 : 1≤r := (le_max_left _ _).trans hr.le
  have hr0 : 0<r := lt_of_lt_of_le zero_lt_one hr1
  have hp : r≤r^(k+1) := le_self_pow₀ hr1 (by omega)
  have hb : 0<r^(k+1)+b := by have := (le_max_right _ _).trans_lt hr; linarith
  rw [show k+2=(k+1)+1 by omega,pow_succ]
  nlinarith

theorem twoScaleRay_eventually_halfPlane {d : ℕ} (ξ δ : Fin d → ℝ)
    (σ : Fin d → Sign) (k : ℕ) :
    ∀ᶠr : ℝ in atTop,∀i,if σ i then 0<(twoScaleRay ξ δ σ k r i).im
      else (twoScaleRay ξ δ σ k r i).im<0 := by
  apply Filter.eventually_all.mpr
  intro i
  filter_upwards [twoScale_height_pos_eventually (δ i) k] with r hr
  rw [twoScaleRay_im]
  cases hs : σ i <;> simp [hs,realSign] <;> linarith

theorem generalRayPhase_twoScale_real {d : ℕ} (c ξ δ : Fin d → ℝ)
    (τ σ : Fin d → Sign) (k : ℕ) (r : ℝ) :
    (generalRayPhase (fun i=>(c i:ℂ)) τ (twoScaleRay ξ δ σ k r)).re =
      -∑i,c i*realSign (τ i)*realSign (σ i)*(r^(k+2)+r*δ i) := by
  unfold generalRayPhase
  rw [Finset.mul_sum,Complex.re_sum,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [←ofReal_realSign]
  simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,one_mul,
    add_zero,zero_add,sub_zero,zero_sub,twoScaleRay_im]
  ring

theorem generalRayPhase_twoScale_target {d : ℕ} (c ξ δ : Fin d → ℝ)
    (σ : Fin d → Sign) (k : ℕ) (r : ℝ) :
    (generalRayPhase (fun i=>(c i:ℂ)) σ (twoScaleRay ξ δ σ k r)).re =
      -(∑i,c i)*r^(k+2)-r*∑i,c i*δ i := by
  rw [generalRayPhase_twoScale_real]
  have hs (i : Fin d) : c i*realSign (σ i)*realSign (σ i)=c i := by
    cases ht : σ i <;> simp [realSign,ht]
  simp_rw [hs,mul_add]
  rw [Finset.sum_add_distrib,←Finset.sum_mul]
  simp_rw [show ∀i,c i*(r*δ i)=r*(c i*δ i) by intro i;ring]
  rw [←Finset.mul_sum]
  ring

variable {n m : ℕ}

theorem twoScalePhase_binary_re (ξ : Fin (n+m) → ℝ)
    (ε : Fin n → Sign) (η : Fin m → Sign) (b d : ℝ) (k : ℕ)
    (τ : Fin (n+m) → Sign) (r : ℝ) :
    (generalRayPhase (binaryCharges n m) τ
      (twoScaleRay ξ (Fin.append (fun _=>b) (fun _=>d)) (Fin.append ε η) k r)).re =
      (∑i,realSign (τ (Fin.castAdd m i))*realSign (ε i))*(r^(k+2)+r*b)-
      (1/2:ℝ)*(∑j,realSign (τ (Fin.natAdd n j))*realSign (η j))*(r^(k+2)+r*d) := by
  have hc : binaryCharges n m = fun i => ((Fin.append (fun _ : Fin n => (-1:ℝ))
      (fun _ : Fin m => (1:ℝ)/2) i : ℝ):ℂ) := by
    funext i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;> simp [binaryCharges]
  rw [hc,generalRayPhase_twoScale_real,Fin.sum_univ_add]
  simp only [Fin.append_left,Fin.append_right,neg_one_mul,neg_mul,Finset.sum_neg_distrib,
    Finset.sum_mul,←Finset.mul_sum,mul_assoc]
  ring

theorem twoScalePhase_binary_target (ξ : Fin (n+m) → ℝ)
    (ε : Fin n → Sign) (η : Fin m → Sign) (b d : ℝ) (k : ℕ) (r : ℝ) :
    (generalRayPhase (binaryCharges n m) (Fin.append ε η)
      (twoScaleRay ξ (Fin.append (fun _=>b) (fun _=>d)) (Fin.append ε η) k r)).re =
      (n:ℝ)*(r^(k+2)+r*b)-(m:ℝ)/2*(r^(k+2)+r*d) := by
  rw [twoScalePhase_binary_re]
  have hs (s : Sign) : realSign s*realSign s=1 := by cases s <;> norm_num [realSign]
  simp only [Fin.append_left,Fin.append_right,hs,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one]
  ring

theorem twoScalePhase_gap (ξ : Fin (n+m) → ℝ)
    (ε : Fin n → Sign) (η : Fin m → Sign) (b d : ℝ) (k : ℕ)
    (τ : Fin (n+m) → Sign) (hb : 0≤b)
    (hden : ∀j,τ (Fin.natAdd n j)=η j) (hne : τ≠Fin.append ε η) :
    ∃e : ℝ,0<e ∧ ∀ᶠr : ℝ in atTop,
      (generalRayPhase (binaryCharges n m) τ
        (twoScaleRay ξ (Fin.append (fun _=>b) (fun _=>d)) (Fin.append ε η) k r)-
       generalRayPhase (binaryCharges n m) (Fin.append ε η)
        (twoScaleRay ξ (Fin.append (fun _=>b) (fun _=>d)) (Fin.append ε η) k r)).re ≤ -e*r := by
  classical
  have hex : ∃i : Fin n,τ (Fin.castAdd m i)≠ε i := by
    by_contra hh
    push_neg at hh
    apply hne
    funext i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i
    · simpa only [Fin.append_left] using hh j
    · simpa only [Fin.append_right] using hden j
  obtain ⟨i₀,hi₀⟩ := hex
  let gain : Fin n → ℝ := fun i => 1-realSign (τ (Fin.castAdd m i))*realSign (ε i)
  have hg (i : Fin n) : 0≤gain i := by
    cases hs : τ (Fin.castAdd m i) <;> cases ht : ε i <;> norm_num [gain,realSign,hs,ht]
  have hg₀ : gain i₀=2 := by
    cases hs : τ (Fin.castAdd m i₀) <;> cases ht : ε i₀ <;> simp_all [gain,realSign] <;> norm_num
  have hsum : 2≤∑i,gain i := by
    rw [←hg₀]
    exact Finset.single_le_sum (fun i _=>hg i) (Finset.mem_univ _)
  have hs : (∑i,gain i)=(n:ℝ)-∑i,realSign (τ (Fin.castAdd m i))*realSign (ε i) := by
    simp [gain,Finset.sum_sub_distrib]
  refine ⟨2,by norm_num,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ)] with r hr
  have hr0 : 0≤r := zero_le_one.trans hr
  have hp : r≤r^(k+2) := le_self_pow₀ hr (by omega)
  have hh : r≤r^(k+2)+r*b := by nlinarith
  rw [Complex.sub_re,twoScalePhase_binary_re,twoScalePhase_binary_target]
  have hsign (j : Fin m) : realSign (τ (Fin.natAdd n j))*realSign (η j)=1 := by
    rw [hden]
    cases ht : η j <;> norm_num [realSign,ht]
  simp only [hsign,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  nlinarith

end BourgadeHuang.CMS
