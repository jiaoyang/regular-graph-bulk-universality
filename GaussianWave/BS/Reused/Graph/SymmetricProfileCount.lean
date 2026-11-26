import GaussianWave.BS.Reused.Graph.ProfileUniform

/-! Exact finite fibers relating symmetric coloring profiles to ordered
profiles, uniformly over every configuration and every coloring. -/
noncomputable section
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Graph.Configuration
open ColorProfiles

theorem histogram_val_wordCount {N d q : ℕ} (w : Fin N → StarWord d q) (s : StarWord d q) :
    (histogram N w s).val = wordCount w s := by
  unfold histogram wordCount
  dsimp only
  congr 2

theorem mem_typeClass_iff_histogram_eq {N d q : ℕ} (z w : Fin N → StarWord d q) :
    z ∈ typeClass w ↔ histogram N z = histogram N w := by
  simp only [typeClass,Finset.mem_filter,Finset.mem_univ,true_and,funext_iff,Fin.ext_iff,
    histogram_val_wordCount]

def SymmetricColoringFiber {N d q : ℕ} (p : Pairing (Stub N d)) (S : StarWord d q → ℝ) :=
  {c : VertexColoring N q // symmetrizedMass (histogram N (configurationWord p c)) = S}

instance {N d q : ℕ} (p : Pairing (Stub N d)) (S : StarWord d q → ℝ) :
    Fintype (SymmetricColoringFiber p S) := by unfold SymmetricColoringFiber; infer_instance

def configurationSymmetricColoringCount {N d q : ℕ} (p : Pairing (Stub N d))
    (S : StarWord d q → ℝ) : ℕ := Fintype.card (SymmetricColoringFiber p S)

abbrev SymmetricOrderedIndex (N d q : ℕ) (S : StarWord d q → ℝ) :=
  {profile : realizedProfiles N d q // symmetrizedMass profile.val = S}

def SymmetricColoringCode {N d q : ℕ} (p : Pairing (Stub N d)) (S : StarWord d q → ℝ) :=
  Σ profile : SymmetricOrderedIndex N d q S,
    {c : VertexColoring N q // histogram N (configurationWord p c) = profile.val.val}

instance {N d q : ℕ} (p : Pairing (Stub N d)) (S : StarWord d q → ℝ) :
    Fintype (SymmetricColoringCode p S) := by unfold SymmetricColoringCode; infer_instance

def symmetricColoringCode {N d q : ℕ} (p : Pairing (Stub N d)) (S : StarWord d q → ℝ)
    (c : SymmetricColoringFiber p S) : SymmetricColoringCode p S :=
  ⟨⟨⟨histogram N (configurationWord p c.val),Finset.mem_image.mpr
    ⟨configurationWord p c.val,Finset.mem_univ _,rfl⟩⟩,c.property⟩,⟨c.val,rfl⟩⟩

theorem symmetricColoringCode_injective {N d q : ℕ} (p : Pairing (Stub N d)) (S : StarWord d q → ℝ) :
    Function.Injective (symmetricColoringCode p S) := by
  intro c e he
  apply Subtype.ext
  exact congrArg (fun z : SymmetricColoringCode p S => z.2.val) he

theorem orderedColoring_fiber_card {N d q : ℕ} (p : Pairing (Stub N d))
    (profile : realizedProfiles N d q) :
    Fintype.card {c : VertexColoring N q // histogram N (configurationWord p c) = profile.val} =
      configurationColoringCount (profileRepresentative profile) p := by
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro c
  rw [← profileRepresentative_histogram profile,← mem_typeClass_iff_histogram_eq]

theorem symmetricColoringCount_le_sum {N d q : ℕ} (p : Pairing (Stub N d)) (S : StarWord d q → ℝ) :
    configurationSymmetricColoringCount p S ≤
      ∑ profile : SymmetricOrderedIndex N d q S,
        configurationColoringCount (profileRepresentative profile.val) p := by
  have h := Fintype.card_le_of_injective _ (symmetricColoringCode_injective p S)
  rw [show Fintype.card (SymmetricColoringCode p S) =
      ∑ profile : SymmetricOrderedIndex N d q S,
        Fintype.card {c : VertexColoring N q // histogram N (configurationWord p c) = profile.val.val} from
      Fintype.card_sigma] at h
  simpa only [orderedColoring_fiber_card] using h

end GaussianWave.BS.Reused.Graph.Configuration
