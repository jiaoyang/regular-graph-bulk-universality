import GeneralizedBulk.Entropy.ColoredFourthCoercivity

/-! Continuity of the actual correlated-star reversal, proved from its
explicit reflection formula. -/
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 200000
namespace GeneralizedBulk.Entropy.Channel

theorem continuous_alpha : Continuous alpha := by
  unfold alpha
  fun_prop

theorem continuous_beta : Continuous beta := by
  unfold beta
  fun_prop

theorem continuous_directionA (d : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    Continuous (fun c : ℝ => directionA d hd c i) := by
  exact (WithLp.prod_continuous_equiv_symm 2 ℝ (Transverse d)).comp
    (continuous_alpha.prodMk (continuous_beta.neg.smul continuous_const))

theorem continuous_directionB (d : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    Continuous (fun c : ℝ => directionB d hd c i) := by
  exact (WithLp.prod_continuous_equiv_symm 2 ℝ (Transverse d)).comp
    (continuous_beta.prodMk (continuous_alpha.smul continuous_const))

/-- On the actual nondegenerate channel domain the reflected direction has
constant squared norm two. -/
theorem endpoint_difference_norm_sq (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) (i : Fin d) :
    ‖directionA d hd c i - directionB d hd c i‖ ^ 2 = 2 := by
  rw [norm_sub_sq_real, directionA_norm_sq d hd c hc i, directionB_norm_sq d hd c hc i,
    directionA_inner_directionB]
  norm_num

/-- The actual endpoint reflection has a denominator-free continuous formula
on the channel parameter domain. -/
theorem endpointReversal_formula (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (i : Fin d) (y : WhiteStar d) :
    endpointReversal d hd c i y = y -
      (@inner ℝ (WhiteStar d) _ (directionA d hd c i - directionB d hd c i) y) •
        (directionA d hd c i - directionB d hd c i) := by
  rw [endpointReversal, Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  change -(2 • ((@inner ℝ (WhiteStar d) _ (directionA d hd c i - directionB d hd c i) y /
    ‖directionA d hd c i - directionB d hd c i‖ ^ 2) •
      (directionA d hd c i - directionB d hd c i)) - y) = _
  have hn := endpoint_difference_norm_sq d hd c hc i
  rw [hn]
  simp only [two_smul]
  have hscale : (@inner ℝ (WhiteStar d) _ (directionA d hd c i - directionB d hd c i) y / 2) +
      (@inner ℝ (WhiteStar d) _ (directionA d hd c i - directionB d hd c i) y / 2) =
      @inner ℝ (WhiteStar d) _ (directionA d hd c i - directionB d hd c i) y := by ring
  rw [← add_smul, hscale]
  abel

/-- The open physical correlation domain, used to keep continuity statements
honest at the degenerate endpoint values. -/
abbrev StarParameters (k : ℕ) := {c : Fin k → ℝ // ∀ a, |c a| < 1}

theorem continuous_endpointReversal_parameter (d k : ℕ) (hd : 2 ≤ d) (i : Fin d) (a : Fin k) :
    Continuous (fun z : StarParameters k × WhiteStar d => endpointReversal d hd (z.1.val a) i z.2) := by
  have hdA : Continuous (fun z : StarParameters k × WhiteStar d => directionA d hd (z.1.val a) i) :=
    (continuous_directionA d hd i).comp ((continuous_apply a).comp (continuous_subtype_val.comp continuous_fst))
  have hdB : Continuous (fun z : StarParameters k × WhiteStar d => directionB d hd (z.1.val a) i) :=
    (continuous_directionB d hd i).comp ((continuous_apply a).comp (continuous_subtype_val.comp continuous_fst))
  have heq : (fun z : StarParameters k × WhiteStar d => endpointReversal d hd (z.1.val a) i z.2) =
      fun z => z.2 - (@inner ℝ (WhiteStar d) _ (directionA d hd (z.1.val a) i - directionB d hd (z.1.val a) i) z.2) •
        (directionA d hd (z.1.val a) i - directionB d hd (z.1.val a) i) :=
    funext (fun z => endpointReversal_formula d hd (z.1.val a) (z.1.property a) i z.2)
  rw [heq]
  exact continuous_snd.sub (((hdA.sub hdB).inner continuous_snd).smul (hdA.sub hdB))

theorem continuous_coloredReversal_parameter (d k : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    Continuous (fun z : StarParameters k × ColoredStar d k => coloredReversal d k hd z.1.val i z.2) := by
  have hm : Continuous (fun z : StarParameters k × ColoredStar d k =>
      fun a : Fin k => endpointReversal d hd (z.1.val a) i (z.2 a)) := by
    apply continuous_pi
    intro a
    have hp : Continuous (fun z : StarParameters k × ColoredStar d k => (z.1, z.2 a)) :=
      continuous_fst.prodMk ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin k => WhiteStar d) a).continuous.comp continuous_snd)
    have ht := Continuous.comp (g := fun z : StarParameters k × WhiteStar d => endpointReversal d hd (z.1.val a) i z.2)
      (f := fun z : StarParameters k × ColoredStar d k => (z.1, z.2 a))
      (continuous_endpointReversal_parameter d k hd i a) hp
    simpa only [Function.comp_apply] using ht
  have hh := (PiLp.continuous_equiv_symm 2 (fun _ : Fin k => WhiteStar d)).comp hm
  change Continuous (fun z : StarParameters k × ColoredStar d k =>
    (WithLp.equiv 2 (Fin k → WhiteStar d)).symm (fun a => endpointReversal d hd (z.1.val a) i (z.2 a)))
  exact hh

/-- The concrete reversal matrices depend continuously on the correlations,
by actual action on the finitely many fixed basis vectors. -/
theorem continuous_coloredReversalMatrix_mulVec (d k : ℕ) (hd : 2 ≤ d) (i : Fin d)
    (x : ScalarCoordinate d k → ℝ) :
    Continuous (fun c : StarParameters k => (coloredReversalMatrix d k hd c.val i).mulVec x) := by
  have heq : (fun c : StarParameters k => (coloredReversalMatrix d k hd c.val i).mulVec x) =
      fun c => scalarCoordinates d k (coloredReversal d k hd c.val i ((scalarCoordinates d k).symm x)) := by
    funext c
    have h := isometryMatrix_repr (scalarAdaptedBasis d k) (coloredReversal d k hd c.val i) ((scalarCoordinates d k).symm x)
    change (coloredReversalMatrix d k hd c.val i).mulVec
      (scalarCoordinates d k ((scalarCoordinates d k).symm x)) = scalarCoordinates d k _ at h
    rw [(scalarCoordinates d k).apply_symm_apply] at h
    exact h
  rw [heq]
  have hm : Continuous (fun c : StarParameters k => (c, (scalarCoordinates d k).symm x)) :=
    continuous_id.prodMk continuous_const
  have hr := (continuous_coloredReversal_parameter d k hd i).comp hm
  exact (scalarCoordinates d k).continuous.comp hr

end GeneralizedBulk.Entropy.Channel
