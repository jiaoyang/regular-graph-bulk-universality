import GaussianWave.BS.Lower.PathCodeEntropy
import GaussianWave.BS.Lower.FinitePaletteTransport

/-! Actual neighborhood codes commute with bijective color relabeling.
This permits finite marker pairs to be encoded as `Fin q` without changing
the entropy of any center-code tuple. -/
noncomputable section
open scoped BigOperators Classical
set_option maxHeartbeats 1000000
namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite

def boundedColorWordEquiv {A B : Type*} (R : ℕ) (e : A ≃ B) :
    BoundedColorWord A R ≃ BoundedColorWord B R :=
  Equiv.sigmaCongrRight (fun n : Fin (R+1) => Equiv.piCongrRight (fun _ : Fin (n.val+1) => e))

def pathCodePaletteEquiv {A B : Type*} (R : ℕ) (e : A ≃ B) :
    PathNeighborhoodCode A R ≃ PathNeighborhoodCode B R :=
  Equiv.arrowCongr (boundedColorWordEquiv R e) (Equiv.refl Bool)

theorem pathNeighborhoodCode_palette_relabel {V A B : Type*} (H : SimpleGraph V) (R : ℕ)
    (e : A ≃ B) (color : V → A) (o : V) :
    pathNeighborhoodCode H R (e ∘ color) o=pathCodePaletteEquiv R e (pathNeighborhoodCode H R color o) := by
  funext word
  change decide (ColoredPathWord H R (e ∘ color) o word)=
    decide (ColoredPathWord H R color o ((boundedColorWordEquiv R e).symm word))
  congr 1
  apply propext
  constructor
  · rintro ⟨p,hp0,hp,hc⟩
    refine ⟨p,hp0,hp,fun j => ?_⟩
    change color (p j)=e.symm (word.2 j)
    exact e.apply_eq_iff_eq_symm_apply.mp (hc j)
  · rintro ⟨p,hp0,hp,hc⟩
    refine ⟨p,hp0,hp,fun j => ?_⟩
    exact e.apply_eq_iff_eq_symm_apply.mpr (hc j)

theorem centerPathCodes_palette_relabel {V I A B : Type*} (H : SimpleGraph V) (R : ℕ)
    (center : I → V) (e : A ≃ B) (color : V → A) :
    centerPathCodes H R center (e ∘ color)=
      coordinatewisePaletteEquiv I (pathCodePaletteEquiv R e) (centerPathCodes H R center color) := by
  funext i
  exact pathNeighborhoodCode_palette_relabel H R e color (center i)

theorem pushMass_equiv_apply {A B : Type*} [Fintype A] (e : A ≃ B) (p : A → ℝ) (b : B) :
    pushMass e p b=p (e.symm b) := by
  unfold pushMass
  have hfilter : (Finset.univ.filter (fun a : A => e a=b))={e.symm b} := by
    ext a
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    exact e.apply_eq_iff_eq_symm_apply
  rw [hfilter]
  simp

theorem windowRecolorMass_palette_push {V A B : Type*} [Fintype V] [Fintype A] [Fintype B]
    {r : ℕ} (e : A ≃ B) (μ : MeasureTheory.Measure ((Fin r × V) → ℝ)) (φ : (Fin r → ℝ) → A → ℝ) :
    pushMass (coordinatewisePaletteEquiv V e) (windowRecolorMass μ φ)=
      windowRecolorMass μ (fun x b => φ x (e.symm b)) := by
  funext b
  rw [pushMass_equiv_apply]
  rfl

theorem entropy_centerPathCodes_palette_push {V I A B : Type*}
    [Fintype V] [Fintype I] [Fintype A] [Fintype B]
    [DecidableEq V] [DecidableEq I] [DecidableEq A] [DecidableEq B]
    (H : SimpleGraph V) (R : ℕ) (center : I → V) (e : A ≃ B) (p : (V → A) → ℝ) :
    entropy (pushMass (centerPathCodes H R center) (pushMass (coordinatewisePaletteEquiv V e) p))=
      entropy (pushMass (centerPathCodes H R center) p) := by
  rw [pushMass_comp]
  have he : centerPathCodes H R center ∘ coordinatewisePaletteEquiv V e=
      coordinatewisePaletteEquiv I (pathCodePaletteEquiv R e) ∘ centerPathCodes H R center := by
    funext w
    exact centerPathCodes_palette_relabel H R center e w
  rw [he]
  exact entropy_pushMass_equiv_comp _ _ _

theorem entropy_vertexPathStarCode_palette_push {A : Type*} [Fintype A] (d q k : ℕ)
    (e : A ≃ Fin q) (p : (GaussianWave.BS.VertexBallVertex d k → A) → ℝ) :
    entropy (pushMass (vertexPathStarCode d q k) (pushMass (coordinatewisePaletteEquiv _ e) p))=
      entropy (pushMass (centerPathCodes (vertexBallGraph d k) k (vertexBallStarCenter d k)) p) := by
  rw [entropy_vertexPathStarCode]
  exact entropy_centerPathCodes_palette_push
    (V := GaussianWave.BS.VertexBallVertex d k) (I := Fin (d+1)) (A := A) (B := Fin q)
    (vertexBallGraph d k) k (vertexBallStarCenter d k) e p

end GaussianWave.BS.Lower
