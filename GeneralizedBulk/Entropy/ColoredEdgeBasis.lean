import GeneralizedBulk.Entropy.ObservationRetainedBasis
import GeneralizedBulk.Entropy.ColoredGaussianChannels

/-! The retained edge observation has exactly two actual Gaussian coordinates
per color. Its dimension is proved using the concrete orthonormal frame. -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Channel

def coloredEdgeFrame (d k : ℕ) (hd : 2 ≤ d) (i : Fin d) : (Fin k ⊕ Fin k) → ColoredStar d k :=
  Sum.elim (coloredDirectionA d k hd (fun _ => 0) i) (coloredDirectionB d k hd (fun _ => 0) i)

theorem coloredEdgeFrame_orthonormal (d k : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    Orthonormal ℝ (coloredEdgeFrame d k hd i) := by
  rw [orthonormal_iff_ite]
  intro a b
  have hA : @inner ℝ (WhiteStar d) _ (directionA d hd 0 i) (directionA d hd 0 i) = 1 := by
    rw [real_inner_self_eq_norm_sq, directionA_norm_sq d hd 0 (by norm_num)]
  have hB : @inner ℝ (WhiteStar d) _ (directionB d hd 0 i) (directionB d hd 0 i) = 1 := by
    rw [real_inner_self_eq_norm_sq, directionB_norm_sq d hd 0 (by norm_num)]
  have hAB := directionA_inner_directionB d hd 0 i
  have hBA : @inner ℝ (WhiteStar d) _ (directionB d hd 0 i) (directionA d hd 0 i) = 0 := by
    rw [real_inner_comm, hAB]
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      simp only [coloredEdgeFrame, Sum.elim_inl, coloredDirectionA, blockVector_inner, blockVector_apply]
      by_cases hab : a = b <;> simp only [hab, ↓reduceIte, hA, Sum.inl.injEq, inner_zero_right]
    | inr b =>
      simp only [coloredEdgeFrame, Sum.elim_inl, Sum.elim_inr, coloredDirectionA, coloredDirectionB,
        blockVector_inner, blockVector_apply]
      by_cases hab : a = b <;> simp only [hab, ↓reduceIte, hAB, hBA, inner_zero_right, Sum.inl_ne_inr, Sum.inr_ne_inl]
  | inr a =>
    cases b with
    | inl b =>
      rw [real_inner_comm]
      simp only [coloredEdgeFrame, Sum.elim_inl, Sum.elim_inr, coloredDirectionA, coloredDirectionB,
        blockVector_inner, blockVector_apply]
      by_cases hab : b = a <;> simp only [hab, ↓reduceIte, hAB, hBA, inner_zero_right, Sum.inl_ne_inr, Sum.inr_ne_inl]
    | inr b =>
      simp only [coloredEdgeFrame, Sum.elim_inr, coloredDirectionB, blockVector_inner, blockVector_apply]
      by_cases hab : a = b <;> simp only [hab, ↓reduceIte, hB, Sum.inr.injEq, inner_zero_right]

def coloredEdgeFrameVector (d k : ℕ) (hd : 2 ≤ d) (i : Fin d)
    (j : Fin k ⊕ Fin k) : coloredEdgeSpace d k hd i :=
  ⟨coloredEdgeFrame d k hd i j, by
    cases j with
    | inl a => exact coloredDirectionA_mem_edgeSpace d k hd (fun _ => 0) i a
    | inr a => exact coloredDirectionB_mem_edgeSpace d k hd (fun _ => 0) i a⟩

theorem coloredEdgeFrameVector_orthonormal (d k : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    Orthonormal ℝ (coloredEdgeFrameVector d k hd i) := by
  rw [orthonormal_iff_ite]
  intro a b
  change @inner ℝ (ColoredStar d k) _ (coloredEdgeFrame d k hd i a) (coloredEdgeFrame d k hd i b) = _
  exact orthonormal_iff_ite.mp (coloredEdgeFrame_orthonormal d k hd i) a b

def coloredEdgeBasis (d k : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    OrthonormalBasis (Fin k ⊕ Fin k) ℝ (coloredEdgeSpace d k hd i) :=
  OrthonormalBasis.mk (coloredEdgeFrameVector_orthonormal d k hd i) (by
    intro x hx
    have he := coloredEdgeProjection_reconstruction d k hd (fun _ => 0) (fun _ => by norm_num) i x
    rw [(mem_coloredEdgeSpace_iff d k hd i x).mp x.property] at he
    have hsum : (∑ j : Fin k ⊕ Fin k, (@inner ℝ (ColoredStar d k) _ (coloredEdgeFrame d k hd i j) x) •
        coloredEdgeFrameVector d k hd i j) = x := by
      apply Subtype.ext
      simp only [Fintype.sum_sum_type, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, coloredEdgeFrameVector,
        coloredEdgeFrame, Sum.elim_inl, Sum.elim_inr]
      rw [← Finset.sum_add_distrib]
      exact he.symm
    rw [← hsum]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))))

theorem finrank_coloredEdgeSpace (d k : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    Module.finrank ℝ (coloredEdgeSpace d k hd i) = 2 * k := by
  rw [Module.finrank_eq_card_basis (coloredEdgeBasis d k hd i).toBasis]
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

theorem card_coloredObserved (d k : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    Fintype.card (coloredObserved d k hd i) = 2 * k := by
  rw [coloredObserved, card_observationIndices, finrank_coloredEdgeSpace]

end GeneralizedBulk.Entropy.Channel
