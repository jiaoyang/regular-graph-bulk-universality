import GaussianWave.BS.Lower.CoverRecoloring
import GaussianWave.Foundation

/-! Actual weak marked-cover limits transfer all continuous finite product
recolorings. The discrepancy caused by colliding graph-cover images is
bounded by the already counted exceptional-root fraction. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
set_option maxHeartbeats 900000
namespace GaussianWave.BS.Lower
open GaussianWave.BS GaussianWave.BS.Reused.Graph
open GaussianWave.BS.Reused.Entropy

variable {r : ℕ} {S F : Type*} [Fintype S] [Fintype F]

def windowRecolorTest (φ : (Fin r → ℝ) → F → ℝ) (w : S → F)
    (y : (Fin r × S) → ℝ) : ℝ := ∏ v,φ (fun a => y (a,v)) (w v)

def windowRecolorMass (μ : Measure ((Fin r × S) → ℝ))
    (φ : (Fin r → ℝ) → F → ℝ) (w : S → F) : ℝ := ∫ y,windowRecolorTest φ w y ∂μ

def windowRecolorBCF (φ : (Fin r → ℝ) → F → ℝ)
    (hφ0 : ∀ y b,0 ≤ φ y b) (hφ1 : ∀ y,∑ b,φ y b=1)
    (hφc : ∀ b,Continuous (fun y => φ y b)) (w : S → F) :
    BoundedContinuousFunction ((Fin r × S) → ℝ) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (windowRecolorTest φ w)
    (by
      unfold windowRecolorTest
      exact continuous_finset_prod _ (fun v _ => (hφc (w v)).comp
        (continuous_pi (fun a => continuous_apply (a,v)))))
    1 (fun y => by
      have h0 : 0 ≤ windowRecolorTest φ w y := Finset.prod_nonneg (fun _ _ => hφ0 _ _)
      rw [Real.norm_eq_abs,abs_of_nonneg h0]
      have hle : windowRecolorTest φ w y ≤ ∏ _v : S,(1 : ℝ) :=
        Finset.prod_le_prod (fun _ _ => hφ0 _ _) (fun v _ => profile_coordinate_le_one _ (hφ0 _) (hφ1 _) (w v))
      simpa using hle)

theorem weak_window_recolorMass (μ : ℕ → Measure ((Fin r × S) → ℝ))
    (ν : Measure ((Fin r × S) → ℝ)) (hweak : WeakLawConverges μ ν)
    (φ : (Fin r → ℝ) → F → ℝ)
    (hφ0 : ∀ y b,0 ≤ φ y b) (hφ1 : ∀ y,∑ b,φ y b=1)
    (hφc : ∀ b,Continuous (fun y => φ y b)) (w : S → F) :
    Tendsto (fun n => windowRecolorMass (μ n) φ w) atTop (𝓝 (windowRecolorMass ν φ w)) :=
  hweak (windowRecolorBCF φ hφ0 hφ1 hφc w)

theorem productCoverRecolorMass_eq_windowIntegral {N m q : ℕ}
    (G : RegularGraph N (m+2)) (k : ℕ) (x : Fin N → Fin r → ℝ)
    (φ : (Fin r → ℝ) → Fin q → ℝ) (w : VertexBallVertex (m+2) k → Fin q) :
    productCoverRecolorMass G k (fun v => φ (x v)) w=
      windowRecolorMass (finiteVertexCoverLaw G k (fun a v => x v a)) φ w := by
  rw [windowRecolorMass,integral_finiteVertexCoverLaw]
  rfl

/-- The actual independent graph recoloring converges to the independent
finite recoloring of the marked-window weak limit. -/
theorem weak_actualCover_recolorMass {m q : ℕ} (N : ℕ → ℕ)
    (G : ∀ n,RegularGraph (N n) (m+2)) (k : ℕ) (x : ∀ n,Fin (N n) → Fin r → ℝ)
    (ν : Measure ((Fin r × VertexBallVertex (m+2) k) → ℝ))
    (hweak : WeakLawConverges (fun n => finiteVertexCoverLaw (G n) k (fun a v => x n v a)) ν)
    (hbad : Tendsto (fun n => (N n : ℝ)⁻¹*badVertexCoverRootCount (G n) k) atTop (𝓝 0))
    (φ : (Fin r → ℝ) → Fin q → ℝ)
    (hφ0 : ∀ y b,0 ≤ φ y b) (hφ1 : ∀ y,∑ b,φ y b=1)
    (hφc : ∀ b,Continuous (fun y => φ y b)) (w : VertexBallVertex (m+2) k → Fin q) :
    Tendsto (fun n => actualCoverRecolorMass (G n) k (fun v => φ (x n v))
      (fun v => hφ0 (x n v)) (fun v => hφ1 (x n v)) w) atTop (𝓝 (windowRecolorMass ν φ w)) := by
  let a n := actualCoverRecolorMass (G n) k (fun v => φ (x n v))
    (fun v => hφ0 (x n v)) (fun v => hφ1 (x n v)) w
  let b n := productCoverRecolorMass (G n) k (fun v => φ (x n v)) w
  have hb : Tendsto b atTop (𝓝 (windowRecolorMass ν φ w)) := by
    have h := weak_window_recolorMass _ ν hweak φ hφ0 hφ1 hφc w
    simpa only [b,productCoverRecolorMass_eq_windowIntegral] using h
  have hd : Tendsto (fun n => a n-b n) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ hbad
    intro n
    rw [Real.norm_eq_abs]
    exact actual_product_cover_recolor_error (G n) k (fun v => φ (x n v))
      (fun v => hφ0 (x n v)) (fun v => hφ1 (x n v)) w
  simpa only [sub_add_cancel,zero_add] using hd.add hb

end GaussianWave.BS.Lower
