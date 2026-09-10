import AffineTverberg.SimplicialSkeletonHomology

set_option linter.style.header false

/-!
# Working inside the affine span of a face

A nonempty geometric realization can be placed in the vector space parallel
to its affine span. Unused abstract vertices are assigned the origin; this
does not change any realized face. Convexity, the geometric realization
axioms, and full affine span in the new coordinates are proved explicitly.

This removes the full-ambient-dimension restriction from the local filling
argument, so the dimension bound is the dimension of the actual face.
-/

noncomputable section

open Set CategoryTheory

namespace AffineTverberg.Simplicial

variable {V E : Type} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [Fintype V] [FiniteDimensional ℝ E] in
/-- The same abstract face family has a full-dimensional geometric
realization in the vector space parallel to its affine span. -/
theorem exists_realization_in_affineSpan
    {K : Finset (Finset V)} {p : V → E} (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p)
    (hne : (geometricCarrier K p).Nonempty)
    (hconv : Convex ℝ (geometricCarrier K p)) :
    ∃ q : V → (affineSpan ℝ (geometricCarrier K p)).direction,
      IsGeometricRealization K q ∧ Convex ℝ (geometricCarrier K q) ∧
      affineSpan ℝ (geometricCarrier K q) = ⊤ := by
  classical
  let L := affineSpan ℝ (geometricCarrier K p)
  obtain ⟨x, hx⟩ := hne
  let o : L := ⟨x, subset_affineSpan ℝ _ hx⟩
  have : Nonempty L := ⟨o⟩
  let e := AffineEquiv.vaddConst ℝ o
  let a : L.direction →ᵃ[ℝ] E := L.subtype.comp e.toAffineMap
  let q : V → L.direction := fun v ↦ if h : p v ∈ L then e.symm ⟨p v, h⟩ else 0
  have hainj : Function.Injective a := Subtype.val_injective.comp e.injective
  have hapoint (s : Finset V) (hs : s ∈ K) (v : V) (hv : v ∈ s) : a (q v) = p v := by
    have hpL : p v ∈ L := subset_affineSpan ℝ _
      (Set.mem_iUnion₂.mpr ⟨s, hs, subset_convexHull ℝ _ (Set.mem_image_of_mem p hv)⟩)
    simp only [q, dite_eq_left hpL]
    change (e (e.symm ⟨p v, hpL⟩)).val = p v
    rw [e.apply_symm_apply]
  have himg (s : Finset V) (hs : s ∈ K) :
      a '' convexHull ℝ (q '' (s : Set V)) = convexHull ℝ (p '' (s : Set V)) := by
    rw [a.image_convexHull, Set.image_image]
    congr 1
    exact Set.image_congr fun v hv ↦ hapoint s hs v hv
  have hcarrier : a '' geometricCarrier K q = geometricCarrier K p := by
    simp only [geometricCarrier, Set.image_iUnion]
    exact Set.iUnion_congr fun s ↦ Set.iUnion_congr fun hs ↦ himg s hs
  have hgeomq : IsGeometricRealization K q := by
    constructor
    · intro s hs
      apply AffineIndependent.of_comp a
      have heq : a ∘ (fun v : s ↦ q v.val) = fun v : s ↦ p v.val := by
        funext v
        exact hapoint s hs v.val v.property
      rw [heq]
      exact hgeom.independent s hs
    · intro s hs t ht z hz
      have haz := hgeom.intersection s hs t ht
        ⟨(himg s hs).subset ⟨z, hz.1, rfl⟩, (himg t ht).subset ⟨z, hz.2, rfl⟩⟩
      rw [← himg (s ∩ t) (hK s hs _ Finset.inter_subset_left)] at haz
      obtain ⟨w, hw, heq⟩ := haz
      exact hainj heq ▸ hw
  refine ⟨q, hgeomq, ?_, ?_⟩
  · have hpre : a ⁻¹' geometricCarrier K p = geometricCarrier K q := by
      rw [← hcarrier, Set.preimage_image_eq _ hainj]
    rw [← hpre]
    exact hconv.affine_preimage a
  · have hspan : (affineSpan ℝ (geometricCarrier K q)).map a = L := by
      rw [AffineSubspace.map_span, hcarrier]
    apply top_unique
    intro z _
    have haz : a z ∈ L := (e z).property
    obtain ⟨w, hw, heq⟩ := hspan.ge haz
    exact hainj heq ▸ hw

/-- The nonemptiness part of local acyclicity in the dimension of the
actual face, with no requirement that it span the original ambient space. -/
theorem nonempty_geometricGood_of_affineSpan
    {K : Finset (Finset V)} {p : V → E} (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) (G : Finset V)
    (hne : (geometricCarrier K p).Nonempty)
    (hconv : Convex ℝ (geometricCarrier K p))
    (hbad : ∀ t ∈ inducedFaces K Gᶜ,
      t.card ≤ Module.finrank ℝ (affineSpan ℝ (geometricCarrier K p)).direction) :
    (geometricCarrier (inducedFaces K G) p).Nonempty := by
  obtain ⟨q, hq, hqconv, hqfull⟩ := exists_realization_in_affineSpan hK hgeom hne hconv
  obtain ⟨x, hx⟩ := nonempty_geometricGood hK hq G hqconv hqfull hbad
  let e := (geometricRealizationHomeomorph (hq.induced G)).symm.trans
    (geometricRealizationHomeomorph (hgeom.induced G))
  exact ⟨_, (e ⟨x, hx⟩).property⟩

/-- Reduced degree zero for an arbitrary convex face, using its own affine
dimension in the bad-simplex bound. -/
theorem isIso_augmentation_geometricGood_of_affineSpan
    {K : Finset (Finset V)} {p : V → E} (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) (G : Finset V)
    (hne : (geometricCarrier K p).Nonempty)
    (hconv : Convex ℝ (geometricCarrier K p))
    (hbad : ∀ t ∈ inducedFaces K Gᶜ,
      t.card < Module.finrank ℝ (affineSpan ℝ (geometricCarrier K p)).direction) :
    IsIso (realSingularAugmentation (TopCat.of ↥(geometricCarrier (inducedFaces K G) p))) := by
  obtain ⟨q, hq, hqconv, hqfull⟩ := exists_realization_in_affineSpan hK hgeom hne hconv
  have := pathConnectedSpace_geometricGood hK hq G hqconv hqfull hbad
  let e := (geometricRealizationHomeomorph (hq.induced G)).symm.trans
    (geometricRealizationHomeomorph (hgeom.induced G))
  have := e.pathConnectedSpace
  infer_instance

end AffineTverberg.Simplicial

namespace AffineTverberg.Simplicial

variable {V E : Type} [Fintype V] [LinearOrder V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Every relevant simplicial class maps to zero in actual singular homology
for an arbitrary convex face, using its affine dimension. Only the general
comparison theorem is still needed to turn this into homology vanishing. -/
theorem comparisonHomologyMap_good_eq_zero_of_affineSpan
    {K : Finset (Finset V)} {p : V → E} (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) (G : Finset V) (n : ℕ) (hn : n ≠ 0)
    (hne : (geometricCarrier K p).Nonempty)
    (hconv : Convex ℝ (geometricCarrier K p))
    (hbad : ∀ t ∈ inducedFaces K Gᶜ,
      t.card + (n + 1) ≤ Module.finrank ℝ (affineSpan ℝ (geometricCarrier K p)).direction) :
    comparisonHomologyMap (faceClosed_inducedFaces hK G) n = 0 := by
  obtain ⟨q, hq, hqconv, hqfull⟩ := exists_realization_in_affineSpan hK hgeom hne hconv
  exact comparisonHomologyMap_good_eq_zero hK hq G n hn hqconv hqfull hbad

/-- The complete geometric and cycle-filling consequences of the paper's
purity and good-vertex hypotheses for an arbitrary convex face. The last
conclusion concerns the actual comparison map, not an assumed isomorphism. -/
theorem local_filling_consequences_of_good_count
    {K : Finset (Finset V)} {p : V → E} (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) (G : Finset V) (m : ℕ)
    (hne : (geometricCarrier K p).Nonempty)
    (hconv : Convex ℝ (geometricCarrier K p))
    (hpure : ∀ s ∈ K, ∃ t ∈ K, s ⊆ t ∧
      t.card = Module.finrank ℝ (affineSpan ℝ (geometricCarrier K p)).direction + 1)
    (hgood : ∀ t ∈ K,
      t.card = Module.finrank ℝ (affineSpan ℝ (geometricCarrier K p)).direction + 1 →
      m + 1 ≤ (t ∩ G).card) :
    (geometricCarrier (inducedFaces K G) p).Nonempty ∧
      (1 ≤ m → IsIso (realSingularAugmentation
        (TopCat.of ↥(geometricCarrier (inducedFaces K G) p)))) ∧
      ∀ n, n ≠ 0 → n + 1 ≤ m →
        comparisonHomologyMap (faceClosed_inducedFaces hK G) n = 0 := by
  have hbound (t : Finset V) (ht : t ∈ inducedFaces K Gᶜ) :
      t.card + m ≤ Module.finrank ℝ (affineSpan ℝ (geometricCarrier K p)).direction :=
    card_bad_le_of_good_count hpure hgood ht
  refine ⟨nonempty_geometricGood_of_affineSpan hK hgeom G hne hconv ?_, ?_, ?_⟩
  · intro t ht
    have := hbound t ht
    omega
  · intro hm
    apply isIso_augmentation_geometricGood_of_affineSpan hK hgeom G hne hconv
    intro t ht
    have := hbound t ht
    omega
  · intro n hn hnm
    apply comparisonHomologyMap_good_eq_zero_of_affineSpan hK hgeom G n hn hne hconv
    intro t ht
    have := hbound t ht
    omega

end AffineTverberg.Simplicial
