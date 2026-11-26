import GaussianWave.BS.Lower.DifferentialEntropyTransfer
import GaussianWave.BS.Lower.CoverRecoloringLimit

/-! Ordinary finite-alphabet reindexing and channel/site coordinate
transport for the genuine randomized entropy lower statement. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Entropy

def coordinatewisePaletteEquiv (V : Type*) {A B : Type*} (e : A ≃ B) : (V → A) ≃ (V → B) where
  toFun := fun x v => e (x v)
  invFun := fun x v => e.symm (x v)
  left_inv := by intro x; funext v; simp
  right_inv := by intro x; funext v; simp

theorem entropy_palette_reindex {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : A → ℝ) : Finite.entropy (fun b => p (e.symm b))=Finite.entropy p :=
  e.symm.sum_comp (fun a => Real.negMulLog (p a))

theorem entropy_recolorMass_palette_reindex {V A B : Type*} [Fintype V] [Fintype A] [Fintype B]
    {r : ℕ} (e : A ≃ B) (μ : Measure ((V × Fin r) → ℝ)) (φ : (Fin r → ℝ) → A → ℝ) :
    Finite.entropy (recolorMass μ (fun x b => φ x (e.symm b)))=Finite.entropy (recolorMass μ φ) := by
  unfold Finite.entropy
  rw [← (coordinatewisePaletteEquiv V e).sum_comp]
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  simp only [recolorMass,coordinatewisePaletteEquiv,Equiv.coe_fn_mk,Equiv.symm_apply_apply]

/-- Finite palettes indexed by `Fin q` already imply the literal
all-finite-alphabet statement. Empty palettes are excluded by normalization,
not by an extra source hypothesis. -/
theorem hasFiniteRecoloringEntropyLower_of_fin {V W : Type*} [Fintype V] [Fintype W] {r : ℕ}
    (μC : Measure ((V × Fin r) → ℝ)) (μE : Measure ((W × Fin r) → ℝ))
    (μo : Measure (Fin r → ℝ)) (weight : ℝ)
    (h : ∀ (q : ℕ),0 < q → ∀ φ : (Fin r → ℝ) → Fin q → ℝ,
      (∀ b,Continuous (fun x => φ x b)) → (∀ x b,0 ≤ φ x b) → (∀ x,∑ b,φ x b=1) →
      (∫ x,Finite.entropy (φ x) ∂μo) ≤ Finite.entropy (recolorMass μC φ)-weight*Finite.entropy (recolorMass μE φ)) :
    HasFiniteRecoloringEntropyLower μC μE μo weight := by
  intro F instF φ hφc hφ0 hφ1
  have hF : Nonempty F := by
    by_contra hempty
    letI : IsEmpty F := not_nonempty_iff.mp hempty
    have hh := hφ1 (fun _ => 0)
    simp at hh
  letI := hF
  let e := Fintype.equivFin F
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hφsum (x : Fin r → ℝ) : (∑ b : Fin (Fintype.card F),φ x (e.symm b))=1 :=
    (e.symm.sum_comp (φ x)).trans (hφ1 x)
  have hh := h (Fintype.card F) hq (fun x b => φ x (e.symm b))
    (fun b => hφc _) (fun x b => hφ0 _ _) hφsum
  simpa only [entropy_palette_reindex,entropy_recolorMass_palette_reindex] using hh

def siteFirstCoordinates {V : Type*} (r : ℕ) (x : (Fin r × V) → ℝ) : (V × Fin r) → ℝ :=
  fun va => x (va.2,va.1)

theorem measurable_siteFirstCoordinates {V : Type*} (r : ℕ) : Measurable (siteFirstCoordinates (V := V) r) :=
  measurable_pi_lambda _ (fun va => measurable_pi_apply (va.2,va.1))

theorem windowRecolorMass_eq_siteFirst {V F : Type*} [Fintype V] [Fintype F] {r : ℕ}
    (μ : Measure ((Fin r × V) → ℝ)) (φ : (Fin r → ℝ) → F → ℝ)
    (hφm : ∀ b,Measurable (fun x => φ x b)) (b : V → F) :
    windowRecolorMass μ φ b=recolorMass (Measure.map (siteFirstCoordinates r) μ) φ b := by
  have htest : Measurable (fun y : (V × Fin r) → ℝ => ∏ v,φ (fun a => y (v,a)) (b v)) :=
    Finset.measurable_prod _ (fun v _ => (hφm (b v)).comp (measurable_pi_lambda _ (fun a => measurable_pi_apply (v,a))))
  rw [recolorMass,integral_map (measurable_siteFirstCoordinates r).aemeasurable htest.aestronglyMeasurable]
  rfl

end GaussianWave.BS.Lower
