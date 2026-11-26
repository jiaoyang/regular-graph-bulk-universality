import BourgadeHuang.CMS.SectorialRadialSystem

/-! The radial spectral gap for the actual numerator and denominator charges. -/
noncomputable section
open scoped BigOperators
namespace BourgadeHuang.CMS.SectorialData

/-- Negative charges reverse the branch sign in the ray direction. -/
def physicalRaySign {d : ℕ} (c : Fin d → ℂ) (σ : Fin d → Sign) (i : Fin d) : Sign :=
  if c i=-1 then !(σ i) else σ i

def physicalPhaseSize {d : ℕ} (β : ℝ) (c : Fin d → ℂ) (i : Fin d) : ℝ :=
  if c i=-1 then 2 else β

theorem general_phase_eq_physical {d : ℕ} (β : ℝ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (hc : ∀i,c i=-1 ∨ c i=(β:ℂ)/2) (i : Fin d) :
    (general (β:ℂ) c σ).phase i=
      Complex.I*(physicalPhaseSize β c i:ℂ)*signValue (physicalRaySign c σ i) := by
  by_cases hi : c i=-1
  · cases hs : σ i <;> simp [general,physicalPhaseSize,physicalRaySign,hi,hs,signValue] <;> ring
  · have he : c i=(β:ℂ)/2 := (hc i).resolve_left hi
    change 2*Complex.I*c i*signValue (σ i)=_
    rw [show physicalPhaseSize β c i=β by simp [physicalPhaseSize,hi],
      show physicalRaySign c σ i=σ i by simp [physicalRaySign,hi],he]
    ring

theorem physicalPhaseSize_lower {d : ℕ} {β : ℝ} (_hβ : 0<β) (c : Fin d → ℂ) (i : Fin d) :
    min 2 β≤physicalPhaseSize β c i := by
  unfold physicalPhaseSize
  split
  · exact min_le_left _ _
  · exact min_le_right _ _

theorem principalDiagonal_general_eq {d : ℕ} (β : ℝ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (hc : ∀i,c i=-1 ∨ c i=(β:ℂ)/2) (S : Finset (Fin d)) :
    (general (β:ℂ) c σ).principalDiagonal (shiftedDirection (physicalRaySign c σ)) S=
      radialDiagonal (physicalPhaseSize β c) (physicalRaySign c σ) S := by
  unfold principalDiagonal radialDiagonal
  rw [Finset.sum_ite_mem]
  simp only [Finset.univ_inter]
  apply Finset.sum_congr rfl
  intro i hi
  rw [general_phase_eq_physical β c σ hc i]
  ring

/-- The positive radial gap is proved from β>0 and the actual physical charges. -/
theorem principalDiagonal_general_gap {d : ℕ} {β : ℝ} (hβ : 0<β)
    (c : Fin d → ℂ) (σ : Fin d → Sign) (hc : ∀i,c i=-1 ∨ c i=(β:ℂ)/2)
    (S : Finset (Fin d)) (hS : S.Nonempty) :
    min 2 β≤((general (β:ℂ) c σ).principalDiagonal
      (shiftedDirection (physicalRaySign c σ)) S).re := by
  rw [principalDiagonal_general_eq β c σ hc]
  exact radialDiagonal_gap (physicalPhaseSize β c) (physicalRaySign c σ)
    (le_min (by norm_num) hβ.le) (physicalPhaseSize_lower hβ c) hS

end BourgadeHuang.CMS.SectorialData
