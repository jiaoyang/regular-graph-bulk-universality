import GaussianWave.BS.Lower.MarkerDecoration

/-! Quantitative free-marker quotient errors vanish, and the two finite
stabilizer contributions cancel in the BS star-minus-edge functional. -/
noncomputable section
open Filter
open scoped BigOperators Classical Topology
set_option maxHeartbeats 1000000

namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite

section OneOrbitFamily
variable {G V F : Type*} [Group G] [Fintype G] [Fintype V] [Fintype F]
  [MulAction G V] [FaithfulSMul G V]

local instance cancellationReindexLabelAction (m : ℕ) : MulAction G (V → F × Fin m) := arrowAction

/-- The marker quotient's centered entropy converges to the original color
entropy minus the genuine finite stabilizer entropy. -/
theorem marker_orbit_centered_entropy_tendsto
    (p : (V → F) → ℝ) (hp : ∀ w,0 ≤ p w) (hs : ∑ w,p w = 1)
    (hinv : ∀ (g : G) c,p (fun v => c (g⁻¹ • v)) = p c)
    (m : ℕ → ℕ) (hm : ∀ n,0 < m n) (hminf : Tendsto m atTop atTop)
    (B : ℕ → Type*) [∀ n,Fintype (B n)] (f : ∀ n,(V → F × Fin (m n)) → B n)
    (hcode : ∀ n w w',f n w = f n w' ↔ w ∈ MulAction.orbit G w') :
    Tendsto (fun n => entropy (pushMass (f n) (markerDecoratedMass p (m n)))-
      (Fintype.card V : ℝ)*Real.log (m n)) atTop
        (𝓝 (entropy p-Real.log (Fintype.card G))) := by
  let err (n : ℕ) := entropy (pushMass (f n) (markerDecoratedMass p (m n)))-entropy p-
    (Fintype.card V : ℝ)*Real.log (m n)+Real.log (Fintype.card G)
  have hb (n : ℕ) : 0 ≤ err n ∧ err n ≤
      ((Fintype.card V : ℝ)^2/(m n : ℝ))*Real.log (Fintype.card G) :=
    marker_orbit_entropy_defect_bound p hp hs hinv (m n) (hm n) (f n) (hcode n)
  have hmr : Tendsto (fun n => (m n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hminf
  have hupper : Tendsto (fun n => ((Fintype.card V : ℝ)^2/(m n : ℝ))*Real.log (Fintype.card G))
      atTop (𝓝 0) := by
    simpa only [zero_mul] using (hmr.const_div_atTop ((Fintype.card V : ℝ)^2)).mul_const (Real.log (Fintype.card G))
  have herr : Tendsto err atTop (𝓝 0) := squeeze_zero (fun n => (hb n).1) (fun n => (hb n).2) hupper
  have hc : Tendsto (fun _ : ℕ => entropy p-Real.log (Fintype.card G)) atTop
      (𝓝 (entropy p-Real.log (Fintype.card G))) := tendsto_const_nhds
  have h := hc.add herr
  have he (n : ℕ) : (entropy p-Real.log (Fintype.card G))+err n =
      entropy (pushMass (f n) (markerDecoratedMass p (m n)))-(Fintype.card V : ℝ)*Real.log (m n) := by
    dsimp [err]
    ring
  simpa only [add_zero,he] using h

end OneOrbitFamily

/-- The two concrete stabilizer group orders used in the tree recoding have
exactly cancelling weighted logarithms. This includes `t=1`. -/
theorem stabilizer_power_log_cancellation (d t : ℕ) :
    Real.log (t^d : ℕ)-((d : ℝ)/2)*Real.log (t^2 : ℕ) = 0 := by
  simp only [Nat.cast_pow,Real.log_pow]
  ring

section TwoOrbitFamilies
variable {GC GE VC VE F : Type*} [Group GC] [Group GE]
  [Fintype GC] [Fintype GE] [Fintype VC] [Fintype VE] [Fintype F]
  [MulAction GC VC] [FaithfulSMul GC VC] [MulAction GE VE] [FaithfulSMul GE VE]

local instance cReindexAction (m : ℕ) : MulAction GC (VC → F × Fin m) := arrowAction
local instance eReindexAction (m : ℕ) : MulAction GE (VE → F × Fin m) := arrowAction

/-- The actual pair of orbit-coded marker-decorated finite laws has precisely
the original star-minus-edge entropy in the large-marker limit. The two
hypotheses are ordinary finite vertex/group cardinal identities, not entropy
or process-classification conclusions. -/
theorem marker_star_edge_entropy_cancellation
    (pC : (VC → F) → ℝ) (pE : (VE → F) → ℝ)
    (hpC : ∀ w,0 ≤ pC w) (hpE : ∀ w,0 ≤ pE w) (hsC : ∑ w,pC w = 1) (hsE : ∑ w,pE w = 1)
    (hinvC : ∀ (g : GC) c,pC (fun v => c (g⁻¹ • v)) = pC c)
    (hinvE : ∀ (g : GE) c,pE (fun v => c (g⁻¹ • v)) = pE c)
    (d : ℕ) (t : ℕ) (hgroupC : Fintype.card GC = t^d) (hgroupE : Fintype.card GE = t^2)
    (hverts : (Fintype.card VC : ℝ)-((d : ℝ)/2)*Fintype.card VE = 1)
    (m : ℕ → ℕ) (hm : ∀ n,0 < m n) (hminf : Tendsto m atTop atTop)
    (BC BE : ℕ → Type*) [∀ n,Fintype (BC n)] [∀ n,Fintype (BE n)]
    (fC : ∀ n,(VC → F × Fin (m n)) → BC n) (fE : ∀ n,(VE → F × Fin (m n)) → BE n)
    (hcodeC : ∀ n w w',fC n w = fC n w' ↔ w ∈ MulAction.orbit GC w')
    (hcodeE : ∀ n w w',fE n w = fE n w' ↔ w ∈ MulAction.orbit GE w') :
    Tendsto (fun n => entropy (pushMass (fC n) (markerDecoratedMass pC (m n)))-
      ((d : ℝ)/2)*entropy (pushMass (fE n) (markerDecoratedMass pE (m n)))-Real.log (m n)) atTop
        (𝓝 (entropy pC-((d : ℝ)/2)*entropy pE)) := by
  have hC := marker_orbit_centered_entropy_tendsto pC hpC hsC hinvC m hm hminf BC fC hcodeC
  have hE := marker_orbit_centered_entropy_tendsto pE hpE hsE hinvE m hm hminf BE fE hcodeE
  have h := hC.sub (hE.const_mul ((d : ℝ)/2))
  have hg : Real.log (Fintype.card GC)-((d : ℝ)/2)*Real.log (Fintype.card GE) = 0 := by
    rw [hgroupC,hgroupE]
    exact stabilizer_power_log_cancellation d t
  have hpoint (n : ℕ) :
      (entropy (pushMass (fC n) (markerDecoratedMass pC (m n)))-(Fintype.card VC : ℝ)*Real.log (m n))-
        ((d : ℝ)/2)*(entropy (pushMass (fE n) (markerDecoratedMass pE (m n)))-(Fintype.card VE : ℝ)*Real.log (m n)) =
      entropy (pushMass (fC n) (markerDecoratedMass pC (m n)))-
        ((d : ℝ)/2)*entropy (pushMass (fE n) (markerDecoratedMass pE (m n)))-Real.log (m n) := by
    have hv := congrArg (fun a : ℝ => a*Real.log (m n)) hverts
    nlinarith
  have hlim : (entropy pC-Real.log (Fintype.card GC))-
      ((d : ℝ)/2)*(entropy pE-Real.log (Fintype.card GE)) = entropy pC-((d : ℝ)/2)*entropy pE := by
    linarith
  simpa only [hpoint,hlim] using h

end TwoOrbitFamilies
end GaussianWave.BS.Lower
