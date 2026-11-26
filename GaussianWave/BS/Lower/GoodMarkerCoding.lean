import GaussianWave.BS.Lower.MarkerCancellation
import GaussianWave.BS.Lower.ApproximateOrbitEntropy

/-! Neighborhood tuple codes need recover stabilizer orbits only when the
markers are distinct. The bad-marker ambiguity is controlled explicitly;
no global exact-fiber statement is used. -/
noncomputable section
open Filter
open scoped BigOperators Classical Topology
set_option maxHeartbeats 1600000

namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite

variable {G V F B : Type*} [Group G] [Fintype G] [Fintype V] [Fintype F] [Fintype B]
  [MulAction G V] [FaithfulSMul G V]

local instance goodMarkerReindexAction (m : ℕ) : MulAction G (V → F × Fin m) := arrowAction

/-- A normalized finite color law has at least one possible color word. -/
theorem colorWord_nonempty_of_mass_one (p : (V → F) → ℝ) (hs : ∑ w,p w = 1) : Nonempty (V → F) := by
  rcases isEmpty_or_nonempty (V → F) with h | h
  · letI := h; simp at hs
  · exact h

/-- Honest two-sided finite-marker error for the actual coarser code. -/
theorem good_marker_entropy_error_bound (p : (V → F) → ℝ)
    (hp : ∀ w,0 ≤ p w) (hs : ∑ w,p w = 1)
    (hpinv : ∀ (g : G) c,p (fun v => c (g⁻¹ • v)) = p c)
    (m : ℕ) (hm : 0 < m) (f : (V → F × Fin m) → B)
    (hfinv : ∀ (g : G) w,f (fun v => w (g⁻¹ • v)) = f w)
    (hrecover : ∀ w,Function.Injective (fun v => (w v).2) → ∀ w',f w' = f w → w' ∈ MulAction.orbit G w) :
    -((Fintype.card V : ℝ)^2/(m : ℝ))*Real.log (Fintype.card (V → F × Fin m)) ≤
      entropy (pushMass f (markerDecoratedMass p m))-entropy p-
        (Fintype.card V : ℝ)*Real.log m+Real.log (Fintype.card G) ∧
      entropy (pushMass f (markerDecoratedMass p m))-entropy p-
        (Fintype.card V : ℝ)*Real.log m+Real.log (Fintype.card G) ≤
          ((Fintype.card V : ℝ)^2/(m : ℝ))*Real.log (Fintype.card G) := by
  let A := V → F × Fin m
  let good (w : A) := Function.Injective (fun v => (w v).2)
  let δ : ℝ := ∑ w : A,@ite ℝ (good w) (Classical.propDecidable _) 0 (markerDecoratedMass p m w)
  have hpi (g : G) (w : A) : markerDecoratedMass p m (g • w) = markerDecoratedMass p m w := by
    unfold markerDecoratedMass uniformFieldMass
    exact congrArg (fun a : ℝ => a*((m : ℝ)^Fintype.card V)⁻¹) (hpinv g (fun v => (w v).1))
  have hbound := entropy_good_orbit_coding_error_bound f hfinv (markerDecoratedMass p m)
    (markerDecoratedMass_nonneg p hp m) (markerDecoratedMass_sum p hs m hm) hpi good
    (fun w hw => reindexing_free_of_injective_markers w hw) hrecover
  have hδ : δ ≤ (Fintype.card V : ℝ)^2/(m : ℝ) := by
    convert markerDecoratedMass_collision_bound p hs m hm using 1
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hg : good w
    · simp only [δ,good] at hg ⊢
      simp only [if_pos hg]
    · simp only [δ,good] at hg ⊢
      simp only [if_neg hg]
  have hword := colorWord_nonempty_of_mass_one p hs
  let c := Classical.choice hword
  letI : Nonempty A := ⟨fun v => (c v,⟨0,hm⟩)⟩
  have hlogA : 0 ≤ Real.log (Fintype.card A) := Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α := A))
  have hlogG : 0 ≤ Real.log (Fintype.card G) := Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α := G))
  have hlow := mul_le_mul_of_nonneg_right hδ hlogA
  have hupp := mul_le_mul_of_nonneg_right hδ hlogG
  have hent := markerDecoratedMass_entropy p hs m hm
  change -δ*Real.log (Fintype.card A) ≤ _ ∧ _ at hbound
  constructor <;> linarith [hbound.1,hbound.2,hent,hlow,hupp]

/-- The full finite decorated alphabet has at most polynomial marker growth. -/
theorem decoratedAlphabet_log_le (m : ℕ) (hm : 0 < m)
    (hA : 0 < Fintype.card (V → F × Fin m)) :
    Real.log (Fintype.card (V → F × Fin m)) ≤
      (Fintype.card V : ℝ)*(Real.log (Fintype.card F+1 : ℕ)+Real.log m) := by
  have hcard : Fintype.card (V → F × Fin m) ≤ ((Fintype.card F+1)*m)^Fintype.card V := by
    simp only [Fintype.card_fun,Fintype.card_prod,Fintype.card_fin]
    exact Nat.pow_le_pow_left (Nat.mul_le_mul_right m (Nat.le_succ _)) _
  have h : Real.log (Fintype.card (V → F × Fin m)) ≤
      Real.log (((Fintype.card F+1)*m)^Fintype.card V : ℕ) :=
    Real.log_le_log (by exact_mod_cast hA) (by exact_mod_cast hcard)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hFpos : (0 : ℝ) < (Fintype.card F+1 : ℕ) := by exact_mod_cast Nat.succ_pos (Fintype.card F)
  simpa only [Nat.cast_pow,Real.log_pow,Nat.cast_mul,Real.log_mul (ne_of_gt hFpos) (ne_of_gt hmpos)] using h

/-- Distinct-marker orbit recovery suffices for the centered code entropy
limit, including all repeated-marker inputs and their extra ambiguity. -/
theorem good_marker_centered_entropy_tendsto
    (p : (V → F) → ℝ) (hp : ∀ w,0 ≤ p w) (hs : ∑ w,p w = 1)
    (hpinv : ∀ (g : G) c,p (fun v => c (g⁻¹ • v)) = p c)
    (m : ℕ → ℕ) (hm : ∀ n,0 < m n) (hminf : Tendsto m atTop atTop)
    (B : ℕ → Type*) [∀ n,Fintype (B n)] (f : ∀ n,(V → F × Fin (m n)) → B n)
    (hfinv : ∀ n (g : G) w,f n (fun v => w (g⁻¹ • v)) = f n w)
    (hrecover : ∀ n w,Function.Injective (fun v => (w v).2) → ∀ w',f n w' = f n w → w' ∈ MulAction.orbit G w) :
    Tendsto (fun n => entropy (pushMass (f n) (markerDecoratedMass p (m n)))-
      (Fintype.card V : ℝ)*Real.log (m n)) atTop (𝓝 (entropy p-Real.log (Fintype.card G))) := by
  let err (n : ℕ) := entropy (pushMass (f n) (markerDecoratedMass p (m n)))-entropy p-
    (Fintype.card V : ℝ)*Real.log (m n)+Real.log (Fintype.card G)
  let K : ℝ := (Fintype.card V : ℝ)^2
  let L : ℝ := Real.log (Fintype.card G)
  let S : ℝ := Real.log (Fintype.card F+1 : ℕ)
  let c := Classical.choice (colorWord_nonempty_of_mass_one p hs)
  have hA (n : ℕ) : 0 < Fintype.card (V → F × Fin (m n)) :=
    Fintype.card_pos_iff.mpr ⟨fun v => (c v,⟨0,hm n⟩)⟩
  have hb (n : ℕ) : -(K/(m n : ℝ))*((Fintype.card V : ℝ)*(S+Real.log (m n))) ≤ err n ∧
      err n ≤ (K/(m n : ℝ))*L := by
    have h := good_marker_entropy_error_bound p hp hs hpinv (m n) (hm n) (f n) (hfinv n) (hrecover n)
    have hlog := decoratedAlphabet_log_le (V := V) (F := F) (m n) (hm n) (hA n)
    have hnon : 0 ≤ K/(m n : ℝ) := by dsimp [K]; positivity
    have hl := mul_le_mul_of_nonneg_left hlog hnon
    constructor
    · dsimp only [err,K,S] at hl ⊢
      linarith [h.1]
    · exact h.2
  have hmr : Tendsto (fun n => (m n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hminf
  have hlogratio : Tendsto (fun n => Real.log (m n)/(m n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,pow_one,one_mul,add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hmr
  have hlow : Tendsto (fun n => -(K/(m n : ℝ))*((Fintype.card V : ℝ)*(S+Real.log (m n)))) atTop (𝓝 0) := by
    have h := ((hmr.const_div_atTop S).add hlogratio).const_mul (-(K*(Fintype.card V : ℝ)))
    convert h using 1
    · funext n; dsimp only; ring
    · simp
  have hupp : Tendsto (fun n => (K/(m n : ℝ))*L) atTop (𝓝 0) := by
    simpa only [zero_mul] using (hmr.const_div_atTop K).mul_const L
  have herr : Tendsto err atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hupp (fun n => (hb n).1) (fun n => (hb n).2)
  have hc : Tendsto (fun _ : ℕ => entropy p-Real.log (Fintype.card G)) atTop
      (𝓝 (entropy p-Real.log (Fintype.card G))) := tendsto_const_nhds
  have h := hc.add herr
  have he (n : ℕ) : (entropy p-Real.log (Fintype.card G))+err n =
      entropy (pushMass (f n) (markerDecoratedMass p (m n)))-(Fintype.card V : ℝ)*Real.log (m n) := by dsimp [err]; ring
  simpa only [add_zero,he] using h

section GoodTwoOrbitFamilies
variable {GC GE VC VE F : Type*} [Group GC] [Group GE]
  [Fintype GC] [Fintype GE] [Fintype VC] [Fintype VE] [Fintype F]
  [MulAction GC VC] [FaithfulSMul GC VC] [MulAction GE VE] [FaithfulSMul GE VE]

local instance goodCReindexAction (m : ℕ) : MulAction GC (VC → F × Fin m) := arrowAction
local instance goodEReindexAction (m : ℕ) : MulAction GE (VE → F × Fin m) := arrowAction

/-- The actual pair of orbit-coded marker-decorated finite laws has precisely
the original star-minus-edge entropy in the large-marker limit. The two
hypotheses are ordinary finite vertex/group cardinal identities, not entropy
or process-classification conclusions. -/
theorem good_marker_star_edge_entropy_cancellation
    (pC : (VC → F) → ℝ) (pE : (VE → F) → ℝ)
    (hpC : ∀ w,0 ≤ pC w) (hpE : ∀ w,0 ≤ pE w) (hsC : ∑ w,pC w = 1) (hsE : ∑ w,pE w = 1)
    (hinvC : ∀ (g : GC) c,pC (fun v => c (g⁻¹ • v)) = pC c)
    (hinvE : ∀ (g : GE) c,pE (fun v => c (g⁻¹ • v)) = pE c)
    (d : ℕ) (t : ℕ) (hgroupC : Fintype.card GC = t^d) (hgroupE : Fintype.card GE = t^2)
    (hverts : (Fintype.card VC : ℝ)-((d : ℝ)/2)*Fintype.card VE = 1)
    (m : ℕ → ℕ) (hm : ∀ n,0 < m n) (hminf : Tendsto m atTop atTop)
    (BC BE : ℕ → Type*) [∀ n,Fintype (BC n)] [∀ n,Fintype (BE n)]
    (fC : ∀ n,(VC → F × Fin (m n)) → BC n) (fE : ∀ n,(VE → F × Fin (m n)) → BE n)
    (hfinvC : ∀ n (g : GC) w,fC n (fun v => w (g⁻¹ • v)) = fC n w)
    (hfinvE : ∀ n (g : GE) w,fE n (fun v => w (g⁻¹ • v)) = fE n w)
    (hrecoverC : ∀ n w,Function.Injective (fun v => (w v).2) → ∀ w',fC n w' = fC n w → w' ∈ MulAction.orbit GC w)
    (hrecoverE : ∀ n w,Function.Injective (fun v => (w v).2) → ∀ w',fE n w' = fE n w → w' ∈ MulAction.orbit GE w) :
    Tendsto (fun n => entropy (pushMass (fC n) (markerDecoratedMass pC (m n)))-
      ((d : ℝ)/2)*entropy (pushMass (fE n) (markerDecoratedMass pE (m n)))-Real.log (m n)) atTop
        (𝓝 (entropy pC-((d : ℝ)/2)*entropy pE)) := by
  have hC := good_marker_centered_entropy_tendsto pC hpC hsC hinvC m hm hminf BC fC hfinvC hrecoverC
  have hE := good_marker_centered_entropy_tendsto pE hpE hsE hinvE m hm hminf BE fE hfinvE hrecoverE
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

end GoodTwoOrbitFamilies

end GaussianWave.BS.Lower
