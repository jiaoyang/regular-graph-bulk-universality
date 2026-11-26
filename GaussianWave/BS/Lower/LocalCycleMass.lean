import GaussianWave.BS.Lower.PatternCounts
import GaussianWave.BS.Reused.Graph.BallCounting

/-! Actual mass of vertices near finite cycles in a uniform simple regular
graph. Fixed-radius ball bounds and direct switching estimates are combined
before any graph-limit or process-classification argument. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
set_option maxHeartbeats 400000

namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Graph

variable {m N d : ℕ}

/-- A root lies within radius `R` of an actual injective copy of `H`. -/
def NearPattern (H : SimpleGraph (Fin m)) (G : RegularGraph N d) (R : ℕ) (v : Fin N) : Prop :=
  ∃ f : Fin m ↪ Fin N,H.map f ≤ G.val ∧ ∃ j : Fin m,G.val.edist (f j) v ≤ (R : ℕ∞)

/-- Literal number of roots near an injectively embedded pattern. -/
def nearPatternCount (H : SimpleGraph (Fin m)) (G : RegularGraph N d) (R : ℕ) : ℝ :=
  ∑ v : Fin N,if NearPattern H G R v then 1 else 0

theorem nearPatternCount_eq_card (H : SimpleGraph (Fin m)) (G : RegularGraph N d) (R : ℕ) :
    nearPatternCount H G R = Fintype.card {v : Fin N // NearPattern H G R v} := by
  simp only [nearPatternCount,Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter,
    Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem nearPatternCount_nonneg (H : SimpleGraph (Fin m)) (G : RegularGraph N d) (R : ℕ) :
    0 ≤ nearPatternCount H G R :=
  Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

/-- An exact dependency/volume bound: each copy can affect at most `m` balls
of radius `R`, and each such ball has a size bounded independently of `N`. -/
theorem nearPatternCount_le (H : SimpleGraph (Fin m)) (G : RegularGraph N d) (R : ℕ) :
    nearPatternCount H G R ≤ (m*regularBallBound d R : ℕ)*patternCount H G := by
  let Q (f : Fin m ↪ Fin N) (v : Fin N) : ℝ :=
    if H.map f ≤ G.val then ∑ j : Fin m,if G.val.edist (f j) v ≤ (R : ℕ∞) then 1 else 0 else 0
  have hQ (f : Fin m ↪ Fin N) (v : Fin N) : 0 ≤ Q f v := by
    dsimp [Q]
    split_ifs
    · exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
    · exact le_rfl
  have hpoint (v : Fin N) : (if NearPattern H G R v then (1 : ℝ) else 0) ≤ ∑ f,Q f v := by
    split_ifs with hv
    · obtain ⟨f,hf,j,hj⟩ := hv
      calc
        1 ≤ Q f v := by
          dsimp only [Q]
          rw [if_pos hf]
          have hh : (if G.val.edist (f j) v ≤ (R : ℕ∞) then (1 : ℝ) else 0) ≤
              ∑ i : Fin m,if G.val.edist (f i) v ≤ (R : ℕ∞) then (1 : ℝ) else 0 :=
            Finset.single_le_sum (f := fun i : Fin m =>
              if G.val.edist (f i) v ≤ (R : ℕ∞) then (1 : ℝ) else 0)
              (fun i _ => by dsimp only; split_ifs <;> norm_num) (Finset.mem_univ j)
          simpa only [if_pos hj] using hh
        _ ≤ _ := Finset.single_le_sum (fun f _ => hQ f v) (Finset.mem_univ f)
    · exact Finset.sum_nonneg (fun f _ => hQ f v)
  have hball (f : Fin m ↪ Fin N) (j : Fin m) :
      (∑ v : Fin N,if G.val.edist (f j) v ≤ (R : ℕ∞) then (1 : ℝ) else 0) ≤ regularBallBound d R := by
    have h := regular_graphBall_card_le G.val G.property (f j) R
    have he : (∑ v : Fin N,if G.val.edist (f j) v ≤ (R : ℕ∞) then (1 : ℝ) else 0) =
        (graphBallVertices G.val (f j) R).card := by
      simp only [graphBallVertices,Finset.card_eq_sum_ones,Finset.sum_filter,
        Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    rw [he]
    exact_mod_cast h
  calc
    _ ≤ ∑ v : Fin N,∑ f : Fin m ↪ Fin N,Q f v := Finset.sum_le_sum (fun v _ => hpoint v)
    _ = ∑ f : Fin m ↪ Fin N,∑ v : Fin N,Q f v := Finset.sum_comm
    _ ≤ ∑ f : Fin m ↪ Fin N,if H.map f ≤ G.val then ((m*regularBallBound d R : ℕ) : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro f hf
      by_cases h : H.map f ≤ G.val
      · simp only [Q,if_pos h]
        rw [Finset.sum_comm]
        calc
          _ ≤ ∑ _j : Fin m,(regularBallBound d R : ℝ) := Finset.sum_le_sum (fun j _ => hball f j)
          _ = _ := by simp [Nat.cast_mul]
      · simp only [Q,if_neg h,Finset.sum_const_zero,le_refl]
    _ = _ := by
      simp only [patternCount,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f hf
      split_ifs <;> simp

/-- A concrete finite-`N` probability bound for roots near a fixed cycle.
The right side is `O(1/N)` for every fixed radius and cycle length. -/
theorem near_cycle_mass_probability [Nonempty (RegularGraph N d)]
    (n R : ℕ) (hN : 0 < N) (hd : 0 < d)
    (hsize : 2*(4*d+2*d^2+2*(n+3)) ≤ N*d) (ε : ℝ) (hε : 0 < ε) :
    (regularGraphLaw N d).real
      {G | ε*(N : ℝ) ≤ nearPatternCount (SimpleGraph.cycleGraph (n+3)) G R} ≤
        ((n+3)*regularBallBound d R : ℕ)*(2*(d : ℝ))^(n+3)/(ε*(N : ℝ)) := by
  letI := regularGraphLaw_isProbability N d
  have hnon := fun G : RegularGraph N d => nearPatternCount_nonneg (SimpleGraph.cycleGraph (n+3)) G R
  have hm := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hnon)
    (Integrable.of_finite : Integrable
      (fun G => nearPatternCount (SimpleGraph.cycleGraph (n+3)) G R) (regularGraphLaw N d)) (ε*(N : ℝ))
  have hi : (∫ G,nearPatternCount (SimpleGraph.cycleGraph (n+3)) G R ∂regularGraphLaw N d) ≤
      ((n+3)*regularBallBound d R : ℕ)*(2*(d : ℝ))^(n+3) := by
    calc
      _ ≤ ∫ G,((n+3)*regularBallBound d R : ℕ)*patternCount (SimpleGraph.cycleGraph (n+3)) G
          ∂regularGraphLaw N d := integral_mono Integrable.of_finite Integrable.of_finite
            (fun G => nearPatternCount_le _ G R)
      _ = ((n+3)*regularBallBound d R : ℕ)*
          (∫ G,patternCount (SimpleGraph.cycleGraph (n+3)) G ∂regularGraphLaw N d) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (integral_cycleCount_le n hN hd hsize) (by positivity)
  apply (le_div_iff₀ (mul_pos hε (by exact_mod_cast hN))).mpr
  simpa only [mul_comm] using hm.trans hi

end GaussianWave.BS.Lower
