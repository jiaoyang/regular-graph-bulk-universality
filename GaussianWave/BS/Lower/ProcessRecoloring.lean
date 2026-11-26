import GaussianWave.BS.Lower.FiniteProductMarginals
import GaussianWave.BS.Lower.PathCodeRelabeling

/-! Probability normalization, symmetry and independent-marker identities
for literal continuous finite recolorings of actual process marginals. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
set_option maxHeartbeats 1200000
namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite

variable {r : ℕ} {V F : Type*} [Fintype V] [Fintype F]

theorem windowRecolorMass_nonneg (μ : Measure ((Fin r × V) → ℝ))
    (φ : (Fin r → ℝ) → F → ℝ) (hφ0 : ∀ x b,0 ≤ φ x b) (b : V → F) :
    0 ≤ windowRecolorMass μ φ b := integral_nonneg (fun _ => Finset.prod_nonneg (fun _ _ => hφ0 _ _))

theorem windowRecolorMass_sum (μ : Measure ((Fin r × V) → ℝ)) [IsProbabilityMeasure μ]
    (φ : (Fin r → ℝ) → F → ℝ) (hφ0 : ∀ x b,0 ≤ φ x b)
    (hφ1 : ∀ x,∑ b,φ x b=1) (hφc : ∀ b,Continuous (fun x => φ x b)) :
    (∑ b,windowRecolorMass μ φ b)=1 := by
  have hi (b : V → F) : Integrable (windowRecolorTest φ b) μ :=
    (windowRecolorBCF φ hφ0 hφ1 hφc b).integrable μ
  unfold windowRecolorMass
  rw [← integral_finset_sum _ (fun b _ => hi b)]
  have hp (x : (Fin r × V) → ℝ) : (∑ b : V → F,windowRecolorTest φ b x)=1 := by
    rw [show (∑ b : V → F,windowRecolorTest φ b x)=(∏ v : V,∑ b : F,φ (fun a => x (a,v)) b) from (Fintype.prod_sum _).symm]
    simp only [hφ1,Finset.prod_const_one]
  simp_rw [hp]
  simp

def windowCoordinateReindex (τ : Equiv.Perm V) (x : (Fin r × V) → ℝ) : (Fin r × V) → ℝ :=
  fun av => x (av.1,τ av.2)

theorem measurable_windowCoordinateReindex (τ : Equiv.Perm V) :
    Measurable (windowCoordinateReindex (r := r) τ) :=
  measurable_pi_lambda _ (fun av => measurable_pi_apply (av.1,τ av.2))

theorem windowRecolorMass_invariant (μ : Measure ((Fin r × V) → ℝ))
    (τ : Equiv.Perm V) (hμ : Measure.map (windowCoordinateReindex (r := r) τ) μ=μ)
    (φ : (Fin r → ℝ) → F → ℝ) (hφm : ∀ b,Measurable (fun x => φ x b)) (b : V → F) :
    windowRecolorMass μ φ (fun v => b (τ.symm v))=windowRecolorMass μ φ b := by
  have htest : Measurable (windowRecolorTest φ b) :=
    Finset.measurable_prod _ (fun v _ => (hφm (b v)).comp (measurable_pi_lambda _ (fun a => measurable_pi_apply (a,v))))
  have hprod (x : (Fin r × V) → ℝ) :
      windowRecolorTest φ (fun v => b (τ.symm v)) x=
        windowRecolorTest φ b (windowCoordinateReindex τ x) := by
    have h := Equiv.prod_comp τ (fun v => φ (fun a => x (a,v)) (b (τ.symm v)))
    simpa only [windowRecolorTest,windowCoordinateReindex,Equiv.symm_apply_apply] using h.symm
  unfold windowRecolorMass
  simp_rw [hprod]
  rw [← integral_map (measurable_windowCoordinateReindex τ).aemeasurable htest.aestronglyMeasurable,hμ]

def processWindowProjection {T : Type*} (site : V → T) (x : (Fin r × T) → ℝ) : (Fin r × V) → ℝ :=
  fun av => x (av.1,site av.2)

theorem measurable_processWindowProjection {T : Type*} (site : V → T) :
    Measurable (processWindowProjection (r := r) site) :=
  measurable_pi_lambda _ (fun av => measurable_pi_apply (av.1,site av.2))

theorem processWindowProjection_invariant {T : Type*} (P : Measure ((Fin r × T) → ℝ))
    (site : V → T) (τ : Equiv.Perm V) (e : Equiv.Perm T)
    (hP : Measure.map (fun x av => x (av.1,e av.2)) P=P)
    (hsite : ∀ v,e (site v)=site (τ v)) :
    Measure.map (windowCoordinateReindex (r := r) τ) (Measure.map (processWindowProjection site) P)=
      Measure.map (processWindowProjection site) P := by
  have hmap : Measurable (fun x : (Fin r × T) → ℝ => fun av : Fin r × T => x (av.1,e av.2)) :=
    measurable_pi_lambda _ (fun av => measurable_pi_apply (av.1,e av.2))
  rw [Measure.map_map (measurable_windowCoordinateReindex τ) (measurable_processWindowProjection site)]
  have heq : windowCoordinateReindex (r := r) τ ∘ processWindowProjection site=
      processWindowProjection site ∘ (fun x av => x (av.1,e av.2)) := by
    funext x av
    simp only [Function.comp_apply,windowCoordinateReindex,processWindowProjection,hsite]
  rw [heq,← Measure.map_map (measurable_processWindowProjection site) hmap,hP]

def markerKernel (φ : (Fin r → ℝ) → F → ℝ) (m : ℕ) (x : Fin r → ℝ) (b : F × Fin m) : ℝ :=
  φ x b.1/(m : ℝ)

theorem markerKernel_nonneg (φ : (Fin r → ℝ) → F → ℝ) (hφ0 : ∀ x b,0 ≤ φ x b)
    (m : ℕ) : ∀ x b,0 ≤ markerKernel φ m x b := fun x b => div_nonneg (hφ0 _ _) (Nat.cast_nonneg _)

theorem markerKernel_sum (φ : (Fin r → ℝ) → F → ℝ) (hφ1 : ∀ x,∑ b,φ x b=1)
    (m : ℕ) (hm : 0 < m) (x : Fin r → ℝ) : (∑ b : F × Fin m,markerKernel φ m x b)=1 := by
  simp only [markerKernel,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  simp only [mul_div_cancel₀ _ hmr,hφ1]

theorem markerKernel_continuous (φ : (Fin r → ℝ) → F → ℝ)
    (hφc : ∀ b,Continuous (fun x => φ x b)) (m : ℕ) (b : F × Fin m) :
    Continuous (fun x => markerKernel φ m x b) := (hφc b.1).div_const _

theorem windowRecolorMass_markerKernel (μ : Measure ((Fin r × V) → ℝ))
    (φ : (Fin r → ℝ) → F → ℝ) (m : ℕ) :
    windowRecolorMass μ (markerKernel φ m)=markerDecoratedMass (windowRecolorMass μ φ) m := by
  funext b
  unfold windowRecolorMass windowRecolorTest markerKernel markerDecoratedMass uniformFieldMass
  simp_rw [finiteProductMass_marker_factor]
  exact integral_mul_const _ _

end GaussianWave.BS.Lower
