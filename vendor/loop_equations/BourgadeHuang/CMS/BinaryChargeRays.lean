import BourgadeHuang.CMS.BinaryPhaseWeights
import BourgadeHuang.CMS.PhysicalPhaseSelection

/-! Explicit rays separate all orthogonal CMS phases. A wrong denominator
sign costs more exponential growth than all numerator signs can compensate. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BourgadeHuang.CMS
variable {n m : ℕ}

@[simp] theorem binaryComplexPow_re (k : ℕ) : ((2:ℂ)^k).re=(2:ℝ)^k := by
  rw [show (2:ℂ)^k=Complex.ofReal ((2:ℝ)^k) by norm_cast]
  rfl

@[simp] theorem binaryComplexPow_im (k : ℕ) : ((2:ℂ)^k).im=0 := by
  rw [show (2:ℂ)^k=Complex.ofReal ((2:ℝ)^k) by norm_cast]
  rfl

def binaryCharges (n m : ℕ) : Fin (n+m) → ℂ :=
  Fin.append (fun _ : Fin n => -1) (fun _ : Fin m => (1:ℂ)/2)

def binaryChargeDirection (n : ℕ) (η : Fin m → Sign) : Point (n+m) :=
  Fin.append (fun i : Fin n => (i.val:ℂ)+Complex.I*((2:ℝ)^i.val:ℂ))
    (fun j : Fin m => ((n+j.val:ℕ):ℂ)+
      Complex.I*(realSign (η j)*(2:ℝ)^(n+j.val+1):ℝ))

def binaryPhaseSigns (η : Fin m → Sign) (σ : Fin (n+m) → Sign) : Fin (n+m) → Sign :=
  Fin.append (fun i => σ (Fin.castAdd m i))
    (fun j => if η j then !(σ (Fin.natAdd n j)) else σ (Fin.natAdd n j))

def binaryObservableRate (n m : ℕ) : ℝ :=
  (∑i : Fin n,(2:ℝ)^i.val)-(∑j : Fin m,(2:ℝ)^(n+j.val))

@[simp] theorem binaryChargeDirection_re (η : Fin m → Sign) (i : Fin (n+m)) :
    (binaryChargeDirection n η i).re=i.val := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp [binaryChargeDirection]
  · cases hs : η j <;> simp [binaryChargeDirection,hs,realSign,signValue]

theorem binaryChargeDirection_ordered (η : Fin m → Sign) :
    binaryChargeDirection n η ∈ OrderedDomain (n+m) := by
  intro i j hij
  simp only [binaryChargeDirection_re]
  exact_mod_cast hij

theorem generalRayPhase_binary_re (η : Fin m → Sign) (σ : Fin (n+m) → Sign) :
    (generalRayPhase (binaryCharges n m) σ (binaryChargeDirection n η)).re =
      (∑i : Fin n,realSign (σ (Fin.castAdd m i))*(2:ℝ)^i.val) -
        ∑j : Fin m,realSign (σ (Fin.natAdd n j))*realSign (η j)*(2:ℝ)^(n+j.val) := by
  unfold generalRayPhase
  rw [Finset.mul_sum, Complex.re_sum, Fin.sum_univ_add, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr rfl
    intro i _
    cases hs : σ (Fin.castAdd m i) <;>
      simp [binaryCharges,binaryChargeDirection,hs,signValue,realSign,
        Complex.mul_re,Complex.mul_im]
  · apply Finset.sum_congr rfl
    intro j _
    cases hs : σ (Fin.natAdd n j) <;> cases ht : η j <;>
      simp [binaryCharges,binaryChargeDirection,hs,ht,signValue,realSign,
        Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im,pow_succ] <;> ring

theorem binaryPhaseSigns_injective (η : Fin m → Sign) :
    Function.Injective (binaryPhaseSigns (n:=n) η) := by
  intro σ τ h
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · have hh := congrFun h (Fin.castAdd m i)
    simpa only [binaryPhaseSigns,Fin.append_left] using hh
  · have hh := congrFun h (Fin.natAdd n j)
    simp only [binaryPhaseSigns,Fin.append_right] at hh
    cases ht : η j <;> simp [ht] at hh <;> exact hh

theorem generalRayPhase_binary_code (η : Fin m → Sign) (σ : Fin (n+m) → Sign) :
    (generalRayPhase (binaryCharges n m) σ (binaryChargeDirection n η)).re =
      ∑i,realSign (binaryPhaseSigns η σ i)*(2:ℝ)^i.val := by
  rw [generalRayPhase_binary_re,Fin.sum_univ_add]
  simp only [binaryPhaseSigns,Fin.append_left,Fin.append_right,Fin.coe_castAdd,Fin.coe_natAdd]
  rw [sub_eq_add_neg,← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  cases hs : σ (Fin.natAdd n j) <;> cases ht : η j <;> simp [hs,ht,realSign]

/-- Every physical sign pattern has its own distinct real exponential rate. -/
theorem generalRayPhase_binary_injective (η : Fin m → Sign) :
    Function.Injective (fun σ : Fin (n+m) → Sign =>
      (generalRayPhase (binaryCharges n m) σ (binaryChargeDirection n η)).re) := by
  intro σ τ h
  dsimp only at h
  rw [generalRayPhase_binary_code,generalRayPhase_binary_code] at h
  exact binaryPhaseSigns_injective η (signed_binary_sum_injective (n+m) h)

/-- One wrong denominator sign already dominates the total possible loss
from all numerator signs, because its binary weight is strictly larger. -/
theorem generalRayPhase_binary_gt_observable_of_wrong_denominator
    (η : Fin m → Sign) (σ : Fin (n+m) → Sign)
    (hwrong : ∃j,σ (Fin.natAdd n j)≠η j) :
    binaryObservableRate n m <
      (generalRayPhase (binaryCharges n m) σ (binaryChargeDirection n η)).re := by
  obtain ⟨j₀,hj₀⟩ := hwrong
  have hnum : -(∑i : Fin n,(2:ℝ)^i.val) ≤
      ∑i : Fin n,realSign (σ (Fin.castAdd m i))*(2:ℝ)^i.val := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    cases hs : σ (Fin.castAdd m i) <;> simp [hs,realSign] <;> positivity
  let gain : Fin m → ℝ := fun j =>
    (1-realSign (σ (Fin.natAdd n j))*realSign (η j))*(2:ℝ)^(n+j.val)
  have hg (j : Fin m) : 0≤gain j := by
    cases hs : σ (Fin.natAdd n j) <;> cases ht : η j <;>
      simp [gain,hs,ht,realSign] <;> positivity
  have hg₀ : gain j₀=2*(2:ℝ)^(n+j₀.val) := by
    cases hs : σ (Fin.natAdd n j₀) <;> cases ht : η j₀ <;>
      simp_all [gain,realSign] <;> norm_num
  have hgain : 2*(2:ℝ)^(n+j₀.val) ≤ ∑j,gain j := by
    rw [← hg₀]
    exact Finset.single_le_sum (fun j _ => hg j) (Finset.mem_univ j₀)
  have he : (∑j,gain j) = (∑j : Fin m,(2:ℝ)^(n+j.val)) -
      ∑j : Fin m,realSign (σ (Fin.natAdd n j))*realSign (η j)*(2:ℝ)^(n+j.val) := by
    simp only [gain,sub_mul,one_mul,Finset.sum_sub_distrib]
  have hdom := sum_binary_weights_lt_pow (n:=n) (j:=n+j₀.val) (Nat.le_add_right _ _)
  rw [generalRayPhase_binary_re]
  unfold binaryObservableRate
  linarith

theorem binaryCharges_physical (n m : ℕ) (i : Fin (n+m)) :
    binaryCharges n m i= -1 ∨ binaryCharges n m i=(1:ℂ)/2 := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp [binaryCharges]

/-- The previously constructed physical sectorial basis has no wrong
denominator phases whenever the observable has its actual ray growth rate. -/
theorem physical_expansion_binary_denominator_support
    (η : Fin m → Sign) (a : (Fin (n+m) → Sign) → ℂ) (F : ℝ → ℂ) (C : ℝ)
    (hexp : ∀ᶠr : ℝ in atTop,F r=∑σ,a σ*
      RadialConstructionData.physicalBranch (by norm_num : 0<(1:ℝ)) (binaryCharges n m) σ
        (binaryCharges_physical n m) (fun i=>(r:ℂ)*binaryChargeDirection n η i))
    (hbound : ∀ᶠr : ℝ in atTop,‖F r‖≤C*Real.exp (r*binaryObservableRate n m)) :
    ∀σ,(∃j,σ (Fin.natAdd n j)≠η j) → a σ=0 := by
  intro σ hσ
  exact RadialConstructionData.physical_expansion_phase_support
    (by norm_num : 0<(1:ℝ)) (binaryCharges n m) (binaryCharges_physical n m)
    (binaryChargeDirection n η) (binaryChargeDirection_ordered η)
    (generalRayPhase_binary_injective η) a F (binaryObservableRate n m) C hexp hbound σ
    (generalRayPhase_binary_gt_observable_of_wrong_denominator η σ hσ)

end BourgadeHuang.CMS
