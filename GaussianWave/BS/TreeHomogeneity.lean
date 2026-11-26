import GaussianWave.BS.TreeLevelTransitivity
import GaussianWave.BS.RadialTreeGeometry

/-! Actual sphere transitivity at arbitrary centers of the constructed
regular tree. -/
noncomputable section
open scoped Classical
namespace GaussianWave.BS

theorem regularTreeIso_dist (d : ℕ) (e : regularWordTree d ≃g regularWordTree d)
    (v w : RegularTreeVertex d) :
    (regularWordTree d).dist (e v) (e w) = (regularWordTree d).dist v w := by
  have hle (f : regularWordTree d ≃g regularWordTree d) (x y : RegularTreeVertex d) :
      (regularWordTree d).dist (f x) (f y) ≤ (regularWordTree d).dist x y := by
    obtain ⟨p,hp⟩ := (regularWordTree_connected d).exists_walk_length_eq_dist x y
    have hh := (regularWordTree d).dist_le (p.map f.toHom)
    simpa only [SimpleGraph.Walk.length_map, hp] using hh
  apply le_antisymm (hle e v w)
  simpa only [e.symm_apply_apply] using hle e.symm (e v) (e w)

theorem regularTreeIso_depth (d : ℕ) (e : regularWordTree d ≃g regularWordTree d)
    (hroot : e none = none) (v : RegularTreeVertex d) :
    regularTreeDepth (e v) = regularTreeDepth v := by
  have h := regularTreeIso_dist d e none v
  rw [hroot,regularTree_dist_root,regularTree_dist_root] at h
  exact h

theorem regularTreeIso_parent (d : ℕ) (e : regularWordTree d ≃g regularWordTree d)
    (hroot : e none = none) (v : RegularTreeVertex d) :
    e (regularTreeParent v) = regularTreeParent (e v) := by
  cases v with
  | none => simpa only [regularTreeParent,hroot]
  | some aw =>
    rcases aw with ⟨a,w⟩
    have h := e.map_rel_iff.mpr
      (Or.inl ⟨Option.some_ne_none (a,w),rfl⟩ :
        (regularWordTree d).Adj (some (a,w)) (regularTreeParent (some (a,w))))
    apply regularTree_adj_parent_of_depth_le h
    rw [regularTreeIso_depth d e hroot,regularTreeIso_depth d e hroot]
    have hh := regularTreeDepth_parent a w
    omega

/-- Equal-distance vertices lie in the same orbit of the actual center
stabilizer, constructed by rerooting and finite-prefix permutations. -/
theorem exists_regularTreeSphereAutomorphism (q : ℕ)
    (c v w : RegularTreeVertex (q+1))
    (h : (regularWordTree (q+1)).dist c v = (regularWordTree (q+1)).dist c w) :
    ∃ f : regularWordTree (q+1) ≃g regularWordTree (q+1), f c = c ∧ f v = w := by
  let e := regularTreeReroot q c
  have he : e none = c := regularTreeReroot_root q c
  have hd : regularTreeDepth (e.symm v) = regularTreeDepth (e.symm w) := by
    rw [← regularTree_dist_root, ← regularTree_dist_root]
    have hv := regularTreeIso_dist (q+1) e none (e.symm v)
    have hw := regularTreeIso_dist (q+1) e none (e.symm w)
    rw [he, e.apply_symm_apply] at hv hw
    exact hv.symm.trans (h.trans hw)
  obtain ⟨g,hroot,hg⟩ := exists_regularTreeLevelAutomorphism (q+1) (e.symm v) (e.symm w) hd
  refine ⟨(e.symm.trans g).trans e, ?_, ?_⟩
  · change e (g (e.symm c)) = c
    rw [← he, e.symm_apply_apply, hroot, he]
  · change e (g (e.symm v)) = w
    rw [hg, e.apply_symm_apply]

end GaussianWave.BS
