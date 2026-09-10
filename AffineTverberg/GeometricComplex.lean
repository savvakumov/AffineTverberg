import AffineTverberg.BarycentricRealization

set_option linter.style.header false

/-!
# A finite geometric realization as an actual simplicial complex

The finite face-family representation used for the join subdivision gives a
`Geometry.SimplicialComplex` on its actual geometric vertices. Empty faces
are removed according to Mathlib's convention. Its carrier is exactly the
existing geometric carrier, and its faces are finite. Global injectivity of
unused vertex labels is not required.
-/

noncomputable section

open Set

namespace AffineTverberg.Simplicial

variable {V E : Type} [DecidableEq V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Finset (Finset V)} {p : V → E}

open Classical in
/-- The affine independence of a face transfers to its finite image of vertices. -/
theorem IsGeometricRealization.affineIndependent_image
    (hgeom : IsGeometricRealization K p) {s : Finset V} (hs : s ∈ K) :
    AffineIndependent ℝ ((↑) : ↥(s.image p) → E) := by
  let f : ↥s → ↥(s.image p) := fun v => ⟨p v, Finset.mem_image_of_mem p v.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v w hvw
      exact (hgeom.independent s hs).injective (congrArg Subtype.val hvw)
    · rintro ⟨x, hx⟩
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨⟨v, hv⟩, rfl⟩
  let e := Equiv.ofBijective f hf
  exact (affineIndependent_equiv e).mp (hgeom.independent s hs)

open Classical in
/-- All finite images of the abstract faces, including the empty face if present. -/
def realizedFaceFamily (K : Finset (Finset V)) (p : V → E) : Set (Finset E) :=
  (fun s => s.image p) '' (K : Set (Finset V))

omit [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem realizedFaceFamily_isLowerSet (hK : FaceClosed K) :
    IsLowerSet (realizedFaceFamily K p) := by
  classical
  intro S T hTS hS
  obtain ⟨s, hs, rfl⟩ := hS
  let t := s.filter fun v => p v ∈ T
  have ht : t ⊆ s := Finset.filter_subset _ _
  refine ⟨t, hK s hs t ht, ?_⟩
  apply Finset.ext
  intro x
  constructor
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hv).2
  · intro hx
    obtain ⟨v, hv, hvx⟩ := Finset.mem_image.mp (hTS hx)
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, by rwa [hvx]⟩, hvx⟩

/-- The geometric image faces inherit the actual convex-hull intersection axiom. -/
theorem realizedFaceFamily_inter_subset (hgeom : IsGeometricRealization K p)
    {S T : Finset E} (hS : S ∈ realizedFaceFamily K p) (hT : T ∈ realizedFaceFamily K p) :
    convexHull ℝ (S : Set E) ∩ convexHull ℝ (T : Set E) ⊆
      convexHull ℝ (S ∩ T : Set E) := by
  classical
  obtain ⟨s, hs, rfl⟩ := hS
  obtain ⟨t, ht, rfl⟩ := hT
  rw [Finset.coe_image, Finset.coe_image]
  apply (hgeom.intersection s hs t ht).trans
  apply convexHull_mono
  rintro x ⟨v, hv, rfl⟩
  exact ⟨⟨v, (Finset.mem_inter.mp hv).1, rfl⟩,
    ⟨v, (Finset.mem_inter.mp hv).2, rfl⟩⟩

/-- The actual finite geometric simplicial complex represented by the face family. -/
def geometricComplex (hK : FaceClosed K) (hgeom : IsGeometricRealization K p) :
    Geometry.SimplicialComplex ℝ E :=
  Geometry.SimplicialComplex.ofErase (realizedFaceFamily K p)
    (fun _ hs => by
      obtain ⟨s, hs, rfl⟩ := hs
      exact hgeom.affineIndependent_image hs)
    (realizedFaceFamily_isLowerSet hK)
    (fun _ hS _ hT => realizedFaceFamily_inter_subset hgeom hS hT)

theorem geometricComplex_faces_finite (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) : (geometricComplex hK hgeom).faces.Finite := by
  classical
  have hfin : (realizedFaceFamily K p).Finite :=
    K.finite_toSet.image (fun s : Finset V => s.image p)
  exact hfin.subset (fun _ hs => hs.1)

/-- Its polyhedron is the literal geometric carrier already used in the proof. -/
theorem geometricComplex_space (hK : FaceClosed K) (hgeom : IsGeometricRealization K p) :
    (geometricComplex hK hgeom).space = geometricCarrier K p := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨S, hS, hxS⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨s, hs, rfl⟩ := hS.1
    exact Set.mem_iUnion₂.mpr ⟨s, hs, by simpa only [Finset.coe_image] using hxS⟩
  · intro hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
    have hne : s.image p ≠ ∅ := by
      intro hempty
      have hxs' : x ∈ convexHull ℝ (s.image p : Set E) := by
        simpa only [Finset.coe_image] using hxs
      simp [hempty] at hxs'
    exact Geometry.SimplicialComplex.mem_space_iff.mpr
      ⟨s.image p, ⟨⟨s, hs, rfl⟩, hne⟩, by simpa only [Finset.coe_image] using hxs⟩

/-- An abstract subcomplex becomes an actual geometric subcomplex. -/
theorem geometricComplex_faces_mono {L : Finset (Finset V)}
    (hL : FaceClosed L) (hK : FaceClosed K) (hLK : L ⊆ K)
    (hgeom : IsGeometricRealization K p) :
    (geometricComplex hL (hgeom.mono hLK)).faces ⊆ (geometricComplex hK hgeom).faces := by
  rintro S ⟨⟨s, hs, rfl⟩, hne⟩
  exact ⟨⟨s, hLK hs, rfl⟩, hne⟩

open Classical in
/-- No vertices of an individual simplex are collapsed by a geometric realization. -/
theorem IsGeometricRealization.card_image (hgeom : IsGeometricRealization K p)
    {s : Finset V} (hs : s ∈ K) : (s.image p).card = s.card := by
  apply Finset.card_image_of_injOn
  intro v hv w hw hvw
  exact congrArg Subtype.val ((hgeom.independent s hs).injective
    (show p (⟨v, hv⟩ : ↥s).val = p (⟨w, hw⟩ : ↥s).val from hvw))

/-- The geometric complex has the same upper bound on simplex dimension. -/
theorem geometricComplex_card_le (hK : FaceClosed K) (hgeom : IsGeometricRealization K p)
    {d : ℕ} (hcard : ∀ s ∈ K, s.card ≤ d)
    {S : Finset E} (hS : S ∈ (geometricComplex hK hgeom).faces) : S.card ≤ d := by
  classical
  obtain ⟨s, hs, rfl⟩ := hS.1
  rw [hgeom.card_image hs]
  exact hcard s hs

/-- Extension to top-dimensional simplices passes to the actual geometric complex. -/
theorem geometricComplex_exists_top_extension (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) {d : ℕ}
    (hext : ∀ s ∈ K, ∃ t ∈ K, s ⊆ t ∧ t.card = d)
    {S : Finset E} (hS : S ∈ (geometricComplex hK hgeom).faces) :
    ∃ T ∈ (geometricComplex hK hgeom).faces, S ⊆ T ∧ T.card = d := by
  classical
  obtain ⟨s, hs, rfl⟩ := hS.1
  obtain ⟨t, ht, hst, hcard⟩ := hext s hs
  have himg : s.image p ⊆ t.image p := Finset.image_subset_image hst
  refine ⟨t.image p, ⟨⟨t, ht, rfl⟩, ?_⟩, himg, (hgeom.card_image ht).trans hcard⟩
  intro hempty
  change t.image p = ∅ at hempty
  exact hS.2 (Finset.eq_empty_iff_forall_notMem.mpr fun x hx => by
    have := himg hx
    simp [hempty] at this)

/-- In particular, purity is preserved without a global injectivity assumption on labels. -/
theorem geometricComplex_card_facet (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) {d : ℕ}
    (hext : ∀ s ∈ K, ∃ t ∈ K, s ⊆ t ∧ t.card = d)
    {S : Finset E} (hS : S ∈ (geometricComplex hK hgeom).facets) : S.card = d := by
  obtain ⟨T, hT, hST, hcard⟩ := geometricComplex_exists_top_extension hK hgeom hext hS.1
  rwa [← hS.2 hT hST] at hcard

end AffineTverberg.Simplicial
