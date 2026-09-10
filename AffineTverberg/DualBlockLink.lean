import AffineTverberg.DualBlockDecomposition
import AffineTverberg.LinkPseudomanifold

set_option linter.style.header false

/-!
# The boundary of a dual block is the subdivided link

The chains of faces strictly containing `s` correspond, by `u ↦ u \ s`, to the
chains of nonempty faces of the combinatorial link `link K s`.  Hence the
boundary of the dual block of `s` is *exactly* the barycentric subdivision of
the link of `s`, realized by placing the face `t` of the link at the barycenter
of the coface `t ∪ s`:

* `dualBlockBoundaryFaces_eq_image` — the combinatorial identity;
* `dualBlockBoundarySpace_eq_geometricCarrier` — the geometric identity of
  polyhedra.

This isolates the remaining input of the dual-cell argument: the homology of
the *ordinary* link of a face (not of the closed-star link).
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg.Simplicial

variable {V : Type*} [Fintype V] [LinearOrder V]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Finset (Finset V)} {p : V → E}

/-- Realizing a face family through a relabelling of its vertices. -/
theorem geometricCarrier_image_family {W : Type*} [DecidableEq W]
    (F : Finset (Finset W)) (φ : W → W) (q : W → E) :
    geometricCarrier (F.image (Finset.image φ)) q = geometricCarrier F (fun w ↦ q (φ w)) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨C₀, hC₀, rfl⟩ := Finset.mem_image.mp hC
    refine Set.mem_iUnion₂.mpr ⟨C₀, hC₀, ?_⟩
    rwa [Finset.coe_image, Set.image_image] at hxC
  · intro x hx
    obtain ⟨C₀, hC₀, hxC₀⟩ := Set.mem_iUnion₂.mp hx
    refine Set.mem_iUnion₂.mpr ⟨C₀.image φ, Finset.mem_image_of_mem _ hC₀, ?_⟩
    rwa [Finset.coe_image, Set.image_image]

/-- The boundary of the dual block of `s` is the barycentric subdivision of the
link of `s`, with the face `t` of the link placed at the coface `t ∪ s`. -/
theorem dualBlockBoundaryFaces_eq_image (K : Finset (Finset V)) (s : Finset V) :
    dualBlockBoundaryFaces K s
      = (subdivisionFaces (link K s)).image (Finset.image fun t ↦ t ∪ s) := by
  classical
  apply Finset.ext
  intro C
  constructor
  · intro hC
    obtain ⟨hCsd, hCs⟩ := mem_dualBlockBoundaryFaces.mp hC
    obtain ⟨hCK, hchain⟩ := mem_subdivisionFaces.mp hCsd
    refine Finset.mem_image.mpr ⟨C.image fun u ↦ u \ s, mem_subdivisionFaces.mpr ⟨?_, ?_, ?_⟩, ?_⟩
    · intro t ht
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
      refine mem_link_iff.mpr ⟨?_, Finset.sdiff_disjoint⟩
      rw [Finset.sdiff_union_of_subset (hCs u hu).subset]
      exact hCK hu
    · intro t ht
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨v, hvu, hvs⟩ := Finset.exists_of_ssubset (hCs u hu)
      exact ⟨v, Finset.mem_sdiff.mpr ⟨hvu, hvs⟩⟩
    · intro t ht t' ht'
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp ht'
      rcases hchain.2 u hu u' hu' with h | h
      · exact Or.inl (Finset.sdiff_subset_sdiff h (le_refl s))
      · exact Or.inr (Finset.sdiff_subset_sdiff h (le_refl s))
    · rw [Finset.image_image]
      apply Finset.ext
      intro u
      simp only [Finset.mem_image, Function.comp_apply]
      constructor
      · rintro ⟨u', hu', rfl⟩
        rwa [Finset.sdiff_union_of_subset (hCs u' hu').subset]
      · intro hu
        exact ⟨u, hu, by rw [Finset.sdiff_union_of_subset (hCs u hu).subset]⟩
  · intro hC
    obtain ⟨C₀, hC₀, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨hC₀L, hchain₀⟩ := mem_subdivisionFaces.mp hC₀
    have hmem : ∀ t ∈ C₀, t ∪ s ∈ K ∧ Disjoint t s ∧ t.Nonempty := by
      intro t ht
      obtain ⟨hmem, hdisj⟩ := mem_link_iff.mp (hC₀L ht)
      exact ⟨hmem, hdisj, hchain₀.1 t ht⟩
    refine mem_dualBlockBoundaryFaces.mpr ⟨mem_subdivisionFaces.mpr ⟨?_, ?_, ?_⟩, ?_⟩
    · intro u hu
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
      exact (hmem t ht).1
    · intro u hu
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨v, hv⟩ := (hmem t ht).2.2
      exact ⟨v, Finset.mem_union_left s hv⟩
    · intro u hu u' hu'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp hu'
      rcases hchain₀.2 t ht t' ht' with h | h
      · exact Or.inl (Finset.union_subset_union h (le_refl s))
      · exact Or.inr (Finset.union_subset_union h (le_refl s))
    · intro u hu
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨-, hdisj, hne⟩ := hmem t ht
      obtain ⟨v, hv⟩ := hne
      refine ⟨Finset.subset_union_right, fun hsub ↦ ?_⟩
      have hvs : v ∈ s := hsub (Finset.mem_union_left s hv)
      exact (Finset.disjoint_left.mp hdisj hv) hvs

/-- The polyhedron of the boundary of a dual block is the realization of the
subdivided link. -/
theorem dualBlockBoundarySpace_eq_geometricCarrier (K : Finset (Finset V)) (p : V → E)
    (s : Finset V) :
    dualBlockBoundarySpace K p s
      = geometricCarrier (subdivisionFaces (link K s))
          (fun t ↦ faceBarycenter p (t ∪ s)) := by
  rw [dualBlockBoundarySpace, dualBlockBoundaryFaces_eq_image,
    geometricCarrier_image_family]

end AffineTverberg.Simplicial

end
