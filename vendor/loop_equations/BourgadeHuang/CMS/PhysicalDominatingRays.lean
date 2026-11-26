import BourgadeHuang.CMS.GeneralBranchRayAsymptotics
import BourgadeHuang.CMS.SectorialPhysicalGap

/-! Separating rays for physical general-coupling phases. The real coordinate
gaps grow linearly, and each prescribed sign has strictly dominant phase. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1000000
variable {d : ℕ}

/-- Reverse the physical stable-ray sign to make the chosen exponential grow. -/
def dominantPhysicalDirection (c : Fin d → ℂ) (σ : Fin d → Sign) (i : Fin d) : ℂ :=
  (i.val:ℂ)-Complex.I*signValue (SectorialData.physicalRaySign c σ i)

@[simp] theorem dominantPhysicalDirection_re (c : Fin d → ℂ) (σ : Fin d → Sign)
    (i : Fin d) : (dominantPhysicalDirection c σ i).re=i.val := by
  cases h : SectorialData.physicalRaySign c σ i <;> simp [dominantPhysicalDirection,h,signValue]

theorem dominantPhysicalDirection_collisionFree (c : Fin d → ℂ) (σ : Fin d → Sign) :
    CollisionFree (dominantPhysicalDirection c σ) := by
  intro i j hij
  have hr := congrArg Complex.re hij
  simp only [dominantPhysicalDirection_re] at hr
  exact Fin.ext (Nat.cast_injective hr)

/-- Every real ordered gap tends to infinity along these genuine rays. -/
theorem dominantPhysicalRay_gaps (c : Fin d → ℂ) (σ : Fin d → Sign) (R : ℝ) :
    ∀ᶠr : ℝ in atTop,(fun i=>(r:ℂ)*dominantPhysicalDirection c σ i)∈OrderedGapDomain d R := by
  filter_upwards [eventually_gt_atTop (max R 0)] with r hr
  have hr0 : 0<r := (le_max_right _ _).trans_lt hr
  have hrR : R<r := (le_max_left _ _).trans_lt hr
  intro i j hij
  have hji : (1:ℝ)≤(j.val:ℝ)-i.val := by
    have hnat : i.val+1≤j.val := hij
    have hcast : (i.val:ℝ)+1≤j.val := by exact_mod_cast hnat
    linarith
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,dominantPhysicalDirection_re]
  nlinarith

/-- Exact real exponential phase as a weighted sign pairing. -/
theorem generalRayPhase_dominantPhysical_re {β : ℝ} (c : Fin d → ℂ)
    (σ τ : Fin d → Sign) (hc : ∀i,c i= -1 ∨ c i=(β:ℂ)/2) :
    (generalRayPhase c τ (dominantPhysicalDirection c σ)).re=
      ∑i,(SectorialData.physicalPhaseSize β c i/2)*
        realSign (SectorialData.physicalRaySign c τ i)*
        realSign (SectorialData.physicalRaySign c σ i) := by
  unfold generalRayPhase
  rw [Finset.mul_sum,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hci : c i= -1
  · cases hs : σ i <;> cases ht : τ i <;>
      simp [dominantPhysicalDirection,SectorialData.physicalRaySign,
        SectorialData.physicalPhaseSize,hci,hs,ht,realSign,signValue]
  · have hce := (hc i).resolve_left hci
    simp only [dominantPhysicalDirection,SectorialData.physicalRaySign,
      SectorialData.physicalPhaseSize,if_neg hci]
    rw [hce]
    cases hs : σ i <;> cases ht : τ i <;>
      simp [hs,ht,realSign,signValue,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im] <;> ring

/-- The chosen sign has the full positive exponential rate. -/
theorem generalRayPhase_dominantPhysical_self {β : ℝ} (c : Fin d → ℂ)
    (σ : Fin d → Sign) (hc : ∀i,c i= -1 ∨ c i=(β:ℂ)/2) :
    (generalRayPhase c σ (dominantPhysicalDirection c σ)).re=
      ∑i,SectorialData.physicalPhaseSize β c i/2 := by
  rw [generalRayPhase_dominantPhysical_re c σ σ hc]
  apply Finset.sum_congr rfl
  intro i hi
  cases SectorialData.physicalRaySign c σ i <;> simp [realSign]

/-- Every other sign has a strictly smaller real exponential rate. -/
theorem generalRayPhase_dominantPhysical_lt {β : ℝ} (hβ : 0<β) (c : Fin d → ℂ)
    (σ τ : Fin d → Sign) (hc : ∀i,c i= -1 ∨ c i=(β:ℂ)/2) (hne : τ≠σ) :
    (generalRayPhase c τ (dominantPhysicalDirection c σ)).re<
      (generalRayPhase c σ (dominantPhysicalDirection c σ)).re := by
  classical
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hne
  have hweight (i : Fin d) : 0<SectorialData.physicalPhaseSize β c i/2 := by
    have hp := SectorialData.physicalPhaseSize_lower hβ c i
    have hm : 0<min 2 β := lt_min (by norm_num) hβ
    exact half_pos (hm.trans_le hp)
  have hsign : SectorialData.physicalRaySign c τ j≠SectorialData.physicalRaySign c σ j := by
    unfold SectorialData.physicalRaySign
    split_ifs <;> simpa using hj
  rw [generalRayPhase_dominantPhysical_re c σ τ hc,generalRayPhase_dominantPhysical_self c σ hc]
  apply Finset.sum_lt_sum
  · intro i hi
    have hw := hweight i
    cases SectorialData.physicalRaySign c τ i <;> cases SectorialData.physicalRaySign c σ i <;>
      simp [realSign] <;> linarith
  · refine ⟨j,Finset.mem_univ _,?_⟩
    have hw := hweight j
    cases ht : SectorialData.physicalRaySign c τ j <;>
      cases hs : SectorialData.physicalRaySign c σ j <;>
      simp [ht,hs] at hsign ⊢ <;> simp [realSign] <;> linarith

end BourgadeHuang.CMS
