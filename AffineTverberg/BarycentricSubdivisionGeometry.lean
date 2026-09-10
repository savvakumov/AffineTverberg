import AffineTverberg.BarycentricSubdivisionIndependence

set_option linter.style.header false

/-!
# The barycentric subdivision as a geometric complex

The barycenters of the nonempty faces of a geometrically realized finite
complex `K` realize the chain family `subdivisionFaces K` as an actual
geometric simplicial complex with the *same* polyhedron, and the same holds
for every face-closed subfamily, so subdivision is compatible with
subcomplexes.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg.Simplicial

variable {V : Type*} [DecidableEq V]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Finset (Finset V)} {p : V → E}

/-- A convex combination of the points of a finite family lies in the convex
hull of its image. -/
theorem sum_smul_mem_convexHull_image {ι : Type*} (C : Finset ι) (f : ι → E)
    {a : ι → ℝ} (ha0 : ∀ t ∈ C, 0 ≤ a t) (ha1 : ∑ t ∈ C, a t = 1) :
    (∑ t ∈ C, a t • f t) ∈ convexHull ℝ (f '' (C : Set ι)) := by
  have hmem := Finset.centerMass_mem_convexHull (R := ℝ) (s := f '' (C : Set ι)) C
    (w := a) ha0 (by rw [ha1]; exact zero_lt_one) (z := f)
    (fun i hi ↦ Set.mem_image_of_mem f hi)
  rwa [Finset.centerMass, ha1, inv_one, one_smul] at hmem

/-- Convex combinations over a finite index set with an injective realization. -/
theorem mem_convexHull_image_iff {ι : Type*} (C : Finset ι) (f : ι → E)
    (hinj : Set.InjOn f (C : Set ι)) (x : E) :
    x ∈ convexHull ℝ (f '' (C : Set ι)) ↔
      ∃ a : ι → ℝ, (∀ t ∈ C, 0 ≤ a t) ∧ (∑ t ∈ C, a t = 1) ∧ (∑ t ∈ C, a t • f t) = x := by
  classical
  constructor
  · intro hx
    have hx' : x ∈ convexHull ℝ ((C.image f : Finset E) : Set E) := by
      rwa [Finset.coe_image]
    obtain ⟨w, hw0, hw1, hwx⟩ := (Finset.convexHull_eq (C.image f)).subset hx'
    refine ⟨fun t ↦ w (f t), fun t ht ↦ hw0 _ (Finset.mem_image_of_mem f ht), ?_, ?_⟩
    · rw [← hw1, Finset.sum_image hinj]
    · rw [← hwx, Finset.centerMass, hw1, inv_one, one_smul]
      exact (Finset.sum_image (f := fun y ↦ w y • id y) hinj).symm
  · rintro ⟨a, ha0, ha1, rfl⟩
    exact sum_smul_mem_convexHull_image C f ha0 ha1

omit [DecidableEq V] in
/-- Monotonicity of the polyhedron in the face family, at arbitrary universes
(`LocalGeometricFilling.geometricCarrier_mono` is the same statement restricted
to `Type`). -/
theorem geometricCarrier_mono_of_subset {L : Finset (Finset V)} (hLK : L ⊆ K) (q : V → E) :
    geometricCarrier L q ⊆ geometricCarrier K q := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion₂.mpr ⟨s, hLK hs, hxs⟩

/-- Two face-closed subfamilies of a geometric complex meet exactly in the
polyhedron of their intersection. -/
theorem geometricCarrier_inter (hgeom : IsGeometricRealization K p)
    {A B : Finset (Finset V)} (hA : FaceClosed A) (hB : FaceClosed B)
    (hAK : A ⊆ K) (hBK : B ⊆ K) :
    geometricCarrier A p ∩ geometricCarrier B p = geometricCarrier (A ∩ B) p := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨hxA, hxB⟩
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp hxA
    obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.mp hxB
    have hx := hgeom.intersection a (hAK ha) b (hBK hb) ⟨hxa, hxb⟩
    refine Set.mem_iUnion₂.mpr ⟨a ∩ b, Finset.mem_inter.mpr
      ⟨hA a ha _ Finset.inter_subset_left, hB b hb _ Finset.inter_subset_right⟩, hx⟩
  · exact Set.subset_inter (geometricCarrier_mono_of_subset Finset.inter_subset_left p)
      (geometricCarrier_mono_of_subset Finset.inter_subset_right p)

/-- The uniform coordinate vector of a nonempty face lies in the barycentric
realization. -/
theorem uniformCoord_mem_barycentricCarrier [Fintype V] {s : Finset V} (hs : s ∈ K)
    (hsne : s.Nonempty) :
    uniformCoord s ∈ barycentricCarrier K :=
  ⟨uniformCoord_nonneg s, sum_uniformCoord hsne, ⟨s, hs, fun _ hv ↦ uniformCoord_eq_zero hv⟩⟩

/-- Distinct nonempty faces of a realized complex have distinct barycenters. -/
theorem faceBarycenter_injOn [Finite V] (hgeom : IsGeometricRealization K p) {s t : Finset V}
    (hs : s ∈ K) (ht : t ∈ K) (hsne : s.Nonempty) (htne : t.Nonempty)
    (heq : faceBarycenter p s = faceBarycenter p t) : s = t := by
  let _ : Fintype V := Fintype.ofFinite V
  have h := barycentricEvaluation_injOn_carrier hgeom
    (uniformCoord_mem_barycentricCarrier hs hsne)
    (uniformCoord_mem_barycentricCarrier ht htne)
    (by rw [barycentricEvaluation_uniformCoord, barycentricEvaluation_uniformCoord, heq])
  ext v
  constructor
  · intro hv
    by_contra hvt
    have := congrFun h v
    rw [uniformCoord_eq_zero hvt] at this
    exact absurd this (ne_of_gt (uniformCoord_pos hv))
  · intro hv
    by_contra hvs
    have := congrFun h v
    rw [uniformCoord_eq_zero hvs] at this
    exact absurd this.symm (ne_of_gt (uniformCoord_pos hv))

/-- The barycenters of the faces of a chain are pairwise distinct. -/
theorem injOn_faceBarycenter_of_chain [Finite V] (hgeom : IsGeometricRealization K p)
    {C : Finset (Finset V)} (hCK : C ⊆ K) (hC : IsFaceChain C) :
    Set.InjOn (faceBarycenter p) (C : Set (Finset V)) := by
  intro s hs t ht heq
  exact faceBarycenter_injOn hgeom (hCK hs) (hCK ht) (hC.1 s hs) (hC.1 t ht) heq

/-- The image under the geometric evaluation of a chain combination. -/
theorem barycentricEvaluation_chainCombination [Fintype V] (p : V → E) (C : Finset (Finset V))
    (a : Finset V → ℝ) :
    barycentricEvaluation p (chainCombination C a) = ∑ t ∈ C, a t • faceBarycenter p t := by
  rw [chainCombination, map_sum]
  exact Finset.sum_congr rfl fun t _ ↦ by
    rw [map_smul, barycentricEvaluation_uniformCoord]

/-- A chain combination with positive weights is a point of the barycentric
realization. -/
theorem chainCombination_mem_barycentricCarrier [Fintype V] {C : Finset (Finset V)} (hCK : C ⊆ K)
    (hC : IsFaceChain C) (hCne : C.Nonempty) {a : Finset V → ℝ} (ha0 : ∀ t ∈ C, 0 ≤ a t)
    (ha1 : ∑ t ∈ C, a t = 1) : chainCombination C a ∈ barycentricCarrier K := by
  obtain ⟨T, hTC, hTmax⟩ := hC.exists_max hCne
  refine ⟨chainCombination_nonneg ha0, sum_chainCombination hC ha1, ⟨T, hCK hTC, ?_⟩⟩
  intro v hv
  exact chainCombination_eq_zero fun t ht hvt ↦ hv (hTmax t ht hvt)

/-- The barycenters realize the barycentric subdivision as a geometric complex. -/
theorem isGeometricRealization_subdivisionFaces [Finite V]
    (hgeom : IsGeometricRealization K p) :
    IsGeometricRealization (subdivisionFaces K) (faceBarycenter p) := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  refine ⟨fun C hC ↦ ?_, fun C hC D hD ↦ ?_⟩
  · obtain ⟨hCK, hchain⟩ := mem_subdivisionFaces.mp hC
    exact affineIndependent_faceBarycenter hgeom hCK hchain
  obtain ⟨hCK, hchainC⟩ := mem_subdivisionFaces.mp hC
  obtain ⟨hDK, hchainD⟩ := mem_subdivisionFaces.mp hD
  rintro x ⟨hxC, hxD⟩
  obtain ⟨a, ha0, ha1, hax⟩ :=
    (mem_convexHull_image_iff C _ (injOn_faceBarycenter_of_chain hgeom hCK hchainC) x).mp hxC
  obtain ⟨b, hb0, hb1, hbx⟩ :=
    (mem_convexHull_image_iff D _ (injOn_faceBarycenter_of_chain hgeom hDK hchainD) x).mp hxD
  -- restrict to the members carrying positive weight
  set C' := C.filter fun t ↦ 0 < a t with hC'
  set D' := D.filter fun t ↦ 0 < b t with hD'
  have hazero : ∀ t ∈ C, t ∉ C' → a t = 0 := by
    intro t ht htn
    rcases lt_or_eq_of_le (ha0 t ht) with h | h
    · exact absurd (Finset.mem_filter.mpr ⟨ht, h⟩) htn
    · exact h.symm
  have hbzero : ∀ t ∈ D, t ∉ D' → b t = 0 := by
    intro t ht htn
    rcases lt_or_eq_of_le (hb0 t ht) with h | h
    · exact absurd (Finset.mem_filter.mpr ⟨ht, h⟩) htn
    · exact h.symm
  have ha1' : ∑ t ∈ C', a t = 1 := by
    rw [← ha1]; exact (Finset.sum_subset (Finset.filter_subset _ _) hazero).symm ▸ rfl
  have hb1' : ∑ t ∈ D', b t = 1 := by
    rw [← hb1]; exact (Finset.sum_subset (Finset.filter_subset _ _) hbzero).symm ▸ rfl
  have hax' : ∑ t ∈ C', a t • faceBarycenter p t = x := by
    rw [← hax]
    refine Finset.sum_subset (Finset.filter_subset _ _) fun t ht htn ↦ ?_
    rw [hazero t ht htn, zero_smul]
  have hbx' : ∑ t ∈ D', b t • faceBarycenter p t = x := by
    rw [← hbx]
    refine Finset.sum_subset (Finset.filter_subset _ _) fun t ht htn ↦ ?_
    rw [hbzero t ht htn, zero_smul]
  have hC'ne : C'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Finset.sum_empty] at ha1'
    exact zero_ne_one ha1'
  have hD'ne : D'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Finset.sum_empty] at hb1'
    exact zero_ne_one hb1'
  have hC'K : C' ⊆ K := (Finset.filter_subset _ _).trans hCK
  have hD'K : D' ⊆ K := (Finset.filter_subset _ _).trans hDK
  have hchainC' : IsFaceChain C' := hchainC.mono (Finset.filter_subset _ _)
  have hchainD' : IsFaceChain D' := hchainD.mono (Finset.filter_subset _ _)
  have hposC : ∀ t ∈ C', 0 < a t := fun t ht ↦ (Finset.mem_filter.mp ht).2
  have hposD : ∀ t ∈ D', 0 < b t := fun t ht ↦ (Finset.mem_filter.mp ht).2
  -- the two chains give the same barycentric coordinate vector
  have hevalC : barycentricEvaluation p (chainCombination C' a) = x := by
    rw [barycentricEvaluation_chainCombination, hax']
  have hevalD : barycentricEvaluation p (chainCombination D' b) = x := by
    rw [barycentricEvaluation_chainCombination, hbx']
  have hmu : chainCombination C' a = chainCombination D' b :=
    barycentricEvaluation_injOn_carrier hgeom
      (chainCombination_mem_barycentricCarrier hC'K hchainC' hC'ne
        (fun t ht ↦ (hposC t ht).le) ha1')
      (chainCombination_mem_barycentricCarrier hD'K hchainD' hD'ne
        (fun t ht ↦ (hposD t ht).le) hb1')
      (by rw [hevalC, hevalD])
  have hCD : C' = D' := eq_of_chainCombination_eq hchainC' hchainD' hposC hposD hmu
  -- hence the common chain lies in the intersection
  have hsub : C' ⊆ C ∩ D := by
    intro t ht
    exact Finset.mem_inter.mpr ⟨Finset.filter_subset _ _ ht,
      Finset.filter_subset _ _ (hCD ▸ ht)⟩
  refine (mem_convexHull_image_iff (C ∩ D) _ ?_ x).mpr ⟨a, ?_, ?_, ?_⟩
  · exact injOn_faceBarycenter_of_chain hgeom
      ((Finset.inter_subset_left).trans hCK)
      (hchainC.mono Finset.inter_subset_left)
  · exact fun t ht ↦ ha0 t (Finset.mem_inter.mp ht).1
  · rw [← ha1']
    refine (Finset.sum_subset hsub fun t ht htn ↦ ?_).symm
    exact hazero t (Finset.mem_inter.mp ht).1 htn
  · rw [← hax']
    refine (Finset.sum_subset hsub fun t ht htn ↦ ?_).symm
    rw [hazero t (Finset.mem_inter.mp ht).1 htn, zero_smul]

/-- The subdivision has the same polyhedron as the original complex. -/
theorem geometricCarrier_subdivisionFaces [Finite V] (hK : FaceClosed K) :
    geometricCarrier (subdivisionFaces K) (faceBarycenter p) = geometricCarrier K p := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨hCK, hchain⟩ := mem_subdivisionFaces.mp hC
    rcases Finset.eq_empty_or_nonempty C with rfl | hCne
    · simp at hxC
    obtain ⟨T, hTC, hTmax⟩ := hchain.exists_max hCne
    have hsub : (faceBarycenter p) '' (C : Set (Finset V)) ⊆ convexHull ℝ (p '' (T : Set V)) := by
      rintro _ ⟨t, ht, rfl⟩
      exact convexHull_mono (Set.image_mono (by exact_mod_cast hTmax t ht))
        (faceBarycenter_mem_convexHull p (hchain.1 t ht))
    have : x ∈ convexHull ℝ (p '' (T : Set V)) :=
      convexHull_min hsub (convex_convexHull ℝ _) hxC
    exact Set.mem_iUnion₂.mpr ⟨T, hCK hTC, this⟩
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨lam, hlam, rfl⟩ := (barycentricEvaluation_face_image p s).superset hxs
    obtain ⟨C, a, hchain, hCs, ha0, ha1, hcomb⟩ :=
      exists_chain_decomposition hlam.1 hlam.2.1 hlam.2.2
    have hCK : C ⊆ K := fun t ht ↦ hK s hs t (hCs t ht)
    refine Set.mem_iUnion₂.mpr ⟨C, mem_subdivisionFaces.mpr ⟨hCK, hchain⟩, ?_⟩
    rw [← hcomb, barycentricEvaluation_chainCombination]
    exact sum_smul_mem_convexHull_image C _ ha0 ha1

/-- Subdivision is compatible with face-closed subfamilies: the subdivided
subcomplex has exactly the polyhedron of the subcomplex. -/
theorem geometricCarrier_subdivisionFaces_of_subset [Finite V] {L : Finset (Finset V)}
    (hL : FaceClosed L) (hLK : L ⊆ K) :
    subdivisionFaces L ⊆ subdivisionFaces K ∧
      geometricCarrier (subdivisionFaces L) (faceBarycenter p) = geometricCarrier L p :=
  ⟨subdivisionFaces_mono hLK, geometricCarrier_subdivisionFaces hL⟩

section Complex

variable {V₀ : Type} [Fintype V₀] [DecidableEq V₀] {E₀ : Type}
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
  {K₀ : Finset (Finset V₀)} {p₀ : V₀ → E₀}

/-- The barycentric subdivision as an actual `Geometry.SimplicialComplex`. -/
def subdivisionComplex (hgeom : IsGeometricRealization K₀ p₀) :
    Geometry.SimplicialComplex ℝ E₀ :=
  geometricComplex (faceClosed_subdivisionFaces K₀) (isGeometricRealization_subdivisionFaces hgeom)

theorem subdivisionComplex_space (hK : FaceClosed K₀) (hgeom : IsGeometricRealization K₀ p₀) :
    (subdivisionComplex hgeom).space = geometricCarrier K₀ p₀ := by
  rw [subdivisionComplex, geometricComplex_space, geometricCarrier_subdivisionFaces hK]

theorem subdivisionComplex_faces_finite (hgeom : IsGeometricRealization K₀ p₀) :
    (subdivisionComplex hgeom).faces.Finite :=
  geometricComplex_faces_finite _ _

end Complex

end AffineTverberg.Simplicial

end
