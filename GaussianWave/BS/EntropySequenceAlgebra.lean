import Mathlib

/-! The numerical final step of the relative entropy comparison. The
probabilistic gap inequalities are established in the separate SSA modules. -/
noncomputable section
open Filter
open scoped Topology
namespace GaussianWave.BS

def relativeBallBalance (C E : ℕ → ℝ) (d : ℝ) (k : ℕ) := C k-d/2*E k
def vertexOverlapGap (C E : ℕ → ℝ) (d : ℝ) (k : ℕ) :=
  d*E (k+1)-(d-1)*C k-C (k+1)
def edgeOverlapGap (C E : ℕ → ℝ) (k : ℕ) := 2*C k-E k-E (k+1)

theorem relativeBallBalance_difference (C E : ℕ → ℝ) (d : ℝ) (k : ℕ) :
    relativeBallBalance C E d k-relativeBallBalance C E d (k+1)=
      vertexOverlapGap C E d k+d/2*edgeOverlapGap C E k := by
  unfold relativeBallBalance vertexOverlapGap edgeOverlapGap
  ring

theorem relativeBallBalance_antitone (C E : ℕ → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (hC : ∀ k,0 ≤ vertexOverlapGap C E d k) (hE : ∀ k,0 ≤ edgeOverlapGap C E k) :
    Antitone (relativeBallBalance C E d) := by
  apply antitone_nat_of_succ_le
  intro k
  have h := relativeBallBalance_difference C E d k
  have hp := mul_nonneg (div_nonneg hd (by norm_num : (0 : ℝ) ≤ 2)) (hE k)
  linarith [hC k]

theorem entropyBalance_lower_of_antitone_sub_reference (X G : ℕ → ℝ)
    (hX : ∀ k,0 ≤ X k) (hG : Tendsto G atTop (𝓝 0))
    (hmono : Antitone (fun k => X k-G k)) : ∀ k,0 ≤ X k-G k := by
  intro k
  have hlim : Tendsto (fun n => -G n) atTop (𝓝 0) := by simpa only [neg_zero] using hG.neg
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop k] with n hn
  exact (show -G n ≤ X n-G n by linarith [hX n]).trans (hmono hn)

theorem entropyBalance_zero_of_lower_and_upper (X G : ℕ → ℝ)
    (hX : ∀ k,0 ≤ X k) (hG : Tendsto G atTop (𝓝 0))
    (hmono : Antitone (fun k => X k-G k)) (hupper : X 0-G 0 ≤ 0) :
    ∀ k,X k-G k=0 := by
  have hnonneg := entropyBalance_lower_of_antitone_sub_reference X G hX hG hmono
  intro k
  exact le_antisymm ((hmono (Nat.zero_le k)).trans hupper) (hnonneg k)

theorem overlapGaps_zero_of_balances_zero (C E : ℕ → ℝ) (d : ℝ) (hd : 0<d)
    (hC : ∀ k,0 ≤ vertexOverlapGap C E d k) (hE : ∀ k,0 ≤ edgeOverlapGap C E k)
    (hzero : ∀ k,relativeBallBalance C E d k=0) :
    ∀ k,vertexOverlapGap C E d k=0 ∧ edgeOverlapGap C E k=0 := by
  intro k
  have h := relativeBallBalance_difference C E d k
  rw [hzero k,hzero (k+1)] at h
  have hc := hC k
  have he := hE k
  have hw : 0<d/2 := by positivity
  have hp := mul_nonneg hw.le he
  have hv : vertexOverlapGap C E d k=0 := by linarith
  have heq : d/2*edgeOverlapGap C E k=0 := by linarith
  exact ⟨hv,(mul_eq_zero.mp heq).resolve_left hw.ne'⟩

end GaussianWave.BS
