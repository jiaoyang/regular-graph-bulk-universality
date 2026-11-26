import GaussianWave.BS.Lower.FiniteRecoloring
import GaussianWave.Foundation

/-! Literal empirical marked stars and independent finite recolorings. The
mean recoloring profile is identified with bounded continuous product tests
of the original marked-star law, so weak graph limits transfer directly. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
set_option maxHeartbeats 800000

namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite
open GaussianWave.BS.Reused.Graph GaussianWave.BS.Reused.Graph.Configuration
open GaussianWave.BS.Reused.Graph.ColorProfiles

variable {N d q r : ℕ}

local instance (d : ℕ) : MeasurableSpace (Equiv.Perm (Fin d)) := ⊤
local instance (d : ℕ) : MeasurableSingletonClass (Equiv.Perm (Fin d)) := ⟨fun _ => trivial⟩

def bareStarSite (G : RegularGraph N d) (v : Fin N) : Fin (d+1) ↪ Fin N where
  toFun := Fin.cases v (graphNeighbor G v)
  inj' := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro k
      refine Fin.cases ?_ (fun j => ?_) k
      · intro h; rfl
      · intro h
        have ha := (canonicalPortLabeling G v j).property
        change G.val.Adj v (graphNeighbor G v j) at ha
        change v = graphNeighbor G v j at h
        rw [← h] at ha
        exact False.elim (G.val.loopless v ha)
    · intro k
      refine Fin.cases ?_ (fun l => ?_) k
      · intro h
        have ha := (canonicalPortLabeling G v j).property
        change G.val.Adj v (graphNeighbor G v j) at ha
        change graphNeighbor G v j = v at h
        rw [h] at ha
        exact False.elim (G.val.loopless v ha)
      · intro h
        apply congrArg Fin.succ
        apply (canonicalPortLabeling G v).injective
        exact Subtype.ext h

def sampledStarSite (G : RegularGraph N d) (z : Fin N × Equiv.Perm (Fin d)) :
    Fin (d+1) ↪ Fin N :=
  (neighborSlotPerm z.2).symm.toEmbedding.trans (bareStarSite G z.1)

theorem sampledStarWord_eq_restrict (G : RegularGraph N d) (z : Fin N × Equiv.Perm (Fin d))
    (c : VertexColoring N q) : sampledStarWord G c z = fun i => c (sampledStarSite G z i) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

def markedStarSample (G : RegularGraph N d) (x : Fin N → Fin r → ℝ)
    (z : Fin N × Equiv.Perm (Fin d)) (aj : Fin r × Fin (d+1)) : ℝ :=
  x (sampledStarSite G z aj.2) aj.1

def markedStarLaw (G : RegularGraph N d) (x : Fin N → Fin r → ℝ) :
    Measure ((Fin r × Fin (d+1)) → ℝ) :=
  Measure.map (markedStarSample G x) (finiteUniform (Fin N × Equiv.Perm (Fin d)))

theorem markedStarLaw_isProbability (G : RegularGraph N d) (hN : 0 < N)
    (x : Fin N → Fin r → ℝ) : IsProbabilityMeasure (markedStarLaw G x) := by
  letI : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  letI := finiteUniform_isProbability (Fin N × Equiv.Perm (Fin d))
  change IsProbabilityMeasure (Measure.map (markedStarSample G x)
    (finiteUniform (Fin N × Equiv.Perm (Fin d))))
  exact isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

def recolorWordTest (φ : (Fin r → ℝ) → Fin q → ℝ) (w : Fin (d+1) → Fin q)
    (y : (Fin r × Fin (d+1)) → ℝ) : ℝ :=
  ∏ j,φ (fun a => y (a,j)) (w j)

def starRecolorMass (μ : Measure ((Fin r × Fin (d+1)) → ℝ))
    (φ : (Fin r → ℝ) → Fin q → ℝ) (w : Fin (d+1) → Fin q) : ℝ :=
  ∫ y,recolorWordTest φ w y ∂μ

/-- Literal equality of the mean independent recoloring profile and the
independent recoloring of the actual empirical marked-star law. -/
theorem mean_star_profile_eq_recolorMass (G : RegularGraph N d)
    (x : Fin N → Fin r → ℝ) (φ : (Fin r → ℝ) → Fin q → ℝ)
    (hφ0 : ∀ y b,0 ≤ φ y b) (hφ1 : ∀ y,∑ b,φ y b = 1)
    (hφm : ∀ b,Measurable (fun y => φ y b)) :
    meanProfile (independentColoringLaw (fun v => φ (x v)) (fun v => hφ0 (x v)) (fun v => hφ1 (x v)))
      (graphStarProfile G) = starRecolorMass (markedStarLaw G x) φ := by
  let P := independentColoringLaw (fun v => φ (x v)) (fun v => hφ0 (x v)) (fun v => hφ1 (x v))
  funext w
  change meanProfile P (fun c => graphStarProfile G (id c)) w = _
  rw [mean_graphStarProfile_eq_sample_law G P id measurable_id]
  rw [lawMass_finiteSampleLaw P _ (uniformSampleWeight_nonneg _) _
    (fun z => measurable_of_finite _) id measurable_id]
  have htest : Measurable (recolorWordTest (d := d) φ w) := by
    unfold recolorWordTest
    exact Finset.measurable_prod _ (fun j _ => (hφm (w j)).comp (measurable_pi_lambda _ (fun a => measurable_pi_apply (a,j))))
  rw [starRecolorMass,markedStarLaw,
    integral_map (measurable_of_finite _).aemeasurable htest.aestronglyMeasurable,integral_finiteUniform]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [show (id ∘ fun c => sampledStarWord G (id c) z) =
      (fun c i => c (sampledStarSite G z i)) by
        funext c
        exact sampledStarWord_eq_restrict G z c]
  rw [independentColoringLaw_restrict_mass]
  rfl

/-- Recoloring product tests are bounded continuous functions even for an
unbounded original mark alphabet. -/
def recolorWordBCF (φ : (Fin r → ℝ) → Fin q → ℝ)
    (hφ0 : ∀ y b,0 ≤ φ y b) (hφ1 : ∀ y,∑ b,φ y b = 1)
    (hφc : ∀ b,Continuous (fun y => φ y b)) (w : Fin (d+1) → Fin q) :
    BoundedContinuousFunction ((Fin r × Fin (d+1)) → ℝ) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (recolorWordTest φ w)
    (by
      unfold recolorWordTest
      exact continuous_finset_prod _ (fun j _ => (hφc (w j)).comp (continuous_pi (fun a => continuous_apply (a,j)))))
    1 (fun y => by
      have h0 : 0 ≤ recolorWordTest φ w y := Finset.prod_nonneg (fun j _ => hφ0 _ _)
      rw [Real.norm_eq_abs,abs_of_nonneg h0]
      have hle : recolorWordTest φ w y ≤ ∏ _j : Fin (d+1),(1 : ℝ) :=
        Finset.prod_le_prod (fun j _ => hφ0 _ _)
          (fun j _ => profile_coordinate_le_one _ (hφ0 _) (hφ1 _) (w j))
      simpa using hle)

/-- Actual weak convergence of marked stars implies coordinatewise
convergence of every finite randomized recoloring profile. -/
theorem weak_markedStar_recolorMass {N : ℕ → ℕ}
    (G : ∀ n,RegularGraph (N n) d) (x : ∀ n,Fin (N n) → Fin r → ℝ)
    (μ : Measure ((Fin r × Fin (d+1)) → ℝ))
    (hweak : WeakLawConverges (fun n => markedStarLaw (G n) (x n)) μ)
    (φ : (Fin r → ℝ) → Fin q → ℝ)
    (hφ0 : ∀ y b,0 ≤ φ y b) (hφ1 : ∀ y,∑ b,φ y b = 1)
    (hφc : ∀ b,Continuous (fun y => φ y b)) (w : Fin (d+1) → Fin q) :
    Tendsto (fun n => meanProfile
      (independentColoringLaw (fun v => φ (x n v)) (fun v => hφ0 (x n v)) (fun v => hφ1 (x n v)))
      (graphStarProfile (G n)) w) atTop (𝓝 (starRecolorMass μ φ w)) := by
  have h := hweak (recolorWordBCF φ hφ0 hφ1 hφc w)
  simp_rw [mean_star_profile_eq_recolorMass (G _) (x _) φ hφ0 hφ1 (fun b => (hφc b).measurable)]
  exact h

def rootEntropyTest (φ : (Fin r → ℝ) → Fin q → ℝ)
    (y : (Fin r × Fin (d+1)) → ℝ) : ℝ :=
  entropy (φ (fun a => y (a,0)))

def rootEntropyBCF (φ : (Fin r → ℝ) → Fin q → ℝ)
    (hφ0 : ∀ y b,0 ≤ φ y b) (hφ1 : ∀ y,∑ b,φ y b = 1)
    (hφc : ∀ b,Continuous (fun y => φ y b)) :
    BoundedContinuousFunction ((Fin r × Fin (d+1)) → ℝ) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (rootEntropyTest φ)
    (by
      unfold rootEntropyTest entropy
      exact continuous_finset_sum _ (fun b _ => Real.continuous_negMulLog.comp
        ((hφc b).comp (continuous_pi (fun a => continuous_apply (a,0))))))
    q (fun y => by
      have hn (b : Fin q) : 0 ≤ Real.negMulLog (φ (fun a => y (a,0)) b) :=
        Real.negMulLog_nonneg (hφ0 _ _) (profile_coordinate_le_one _ (hφ0 _) (hφ1 _) b)
      have h0 : 0 ≤ rootEntropyTest φ y := by
        change 0 ≤ ∑ b : Fin q,Real.negMulLog (φ (fun a => y (a,0)) b)
        exact Finset.sum_nonneg (fun b _ => hn b)
      rw [Real.norm_eq_abs,abs_of_nonneg h0]
      calc
        _ ≤ ∑ _b : Fin q,(1 : ℝ) := Finset.sum_le_sum (fun b _ =>
          (negMulLog_le_one_sub _ (hφ0 _ _)).trans (by linarith [hφ0 (fun a => y (a,0)) b]))
        _ = _ := by simp)

/-- The empirical conditional recoloring entropy is the literal bounded
continuous root test of the actual marked-star law. -/
theorem rootEntropy_markedStarLaw (G : RegularGraph N d) (hN : 0 < N)
    (x : Fin N → Fin r → ℝ) (φ : (Fin r → ℝ) → Fin q → ℝ)
    (hφc : ∀ b,Continuous (fun y => φ y b)) :
    (∫ y,rootEntropyTest φ y ∂markedStarLaw G x) = (N : ℝ)⁻¹*∑ v,entropy (φ (x v)) := by
  have hm : Measurable (rootEntropyTest (d := d) φ) := by
    unfold rootEntropyTest entropy
    exact Finset.measurable_sum _ (fun b _ => Real.continuous_negMulLog.measurable.comp
      ((hφc b).measurable.comp (measurable_pi_lambda _ (fun a => measurable_pi_apply (a,0)))))
  rw [markedStarLaw,integral_map (measurable_of_finite _).aemeasurable hm.aestronglyMeasurable,
    integral_finiteUniform]
  have he (z : Fin N × Equiv.Perm (Fin d)) :
      rootEntropyTest φ (markedStarSample G x z) = entropy (φ (x z.1)) := by rfl
  simp_rw [he]
  simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
  rw [← Finset.mul_sum]
  have hP : (Fintype.card (Equiv.Perm (Fin d)) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp
  ring

/-- The conditional entropy term in randomized L1 passes to the graph limit
using weak convergence alone. -/
theorem weak_markedStar_rootEntropy {N : ℕ → ℕ}
    (G : ∀ n,RegularGraph (N n) d) (hN : ∀ n,0 < N n)
    (x : ∀ n,Fin (N n) → Fin r → ℝ) (μ : Measure ((Fin r × Fin (d+1)) → ℝ))
    (hweak : WeakLawConverges (fun n => markedStarLaw (G n) (x n)) μ)
    (φ : (Fin r → ℝ) → Fin q → ℝ)
    (hφ0 : ∀ y b,0 ≤ φ y b) (hφ1 : ∀ y,∑ b,φ y b = 1)
    (hφc : ∀ b,Continuous (fun y => φ y b)) :
    Tendsto (fun n => (N n : ℝ)⁻¹*∑ v,entropy (φ (x n v))) atTop
      (𝓝 (∫ y,rootEntropyTest φ y ∂μ)) := by
  have h := hweak (rootEntropyBCF φ hφ0 hφ1 hφc)
  change Tendsto (fun n => ∫ y,rootEntropyTest φ y ∂markedStarLaw (G n) (x n)) atTop
    (𝓝 (∫ y,rootEntropyTest φ y ∂μ)) at h
  simp_rw [rootEntropy_markedStarLaw (G _) (hN _) (x _) φ hφc] at h
  exact h

end GaussianWave.BS.Lower
