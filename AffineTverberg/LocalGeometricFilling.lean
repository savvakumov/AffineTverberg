import AffineTverberg.GeneralPositionHomotopy

set_option linter.style.header false

/-!
# Local filling for the good part of a geometric triangulation

For a finite geometric triangulation of a full-dimensional convex set, a
bound on the sizes of bad simplices gives a contractible filling carrier for
the low-dimensional skeleton of the good induced subcomplex. This is the
geometric step of the paper's local acyclicity argument with its actual
good/bad induced realizations. No simplicial-to-singular comparison is assumed.
-/

noncomputable section

open Set CategoryTheory

namespace AffineTverberg.Simplicial

variable {V E : Type} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

section PointFamilies

variable [DecidableEq E]

/-- Replace the abstract vertex labels of every simplex by their positions. -/
def pointFamily (K : Finset (Finset V)) (p : V → E) : Finset (Finset E) :=
  K.image (fun s ↦ s.image p)

omit [Fintype V] [DecidableEq V] in
theorem hullCarrier_pointFamily (K : Finset (Finset V)) (p : V → E) :
    GeneralPosition.hullCarrier (pointFamily K p) = geometricCarrier K p := by
  ext x
  simp [GeneralPosition.hullCarrier, pointFamily, geometricCarrier]

end PointFamilies

/-- The simplicial skeleton in geometric dimension at most `j`. -/
def skeleton (K : Finset (Finset V)) (j : ℕ) : Finset (Finset V) :=
  K.filter (fun s ↦ s.card ≤ j + 1)

omit [Fintype V] [DecidableEq V] in
theorem faceClosed_skeleton {K : Finset (Finset V)} (hK : FaceClosed K) (j : ℕ) :
    FaceClosed (skeleton K j) := by
  intro s hs t hts
  obtain ⟨hsK, hsc⟩ := Finset.mem_filter.mp hs
  exact Finset.mem_filter.mpr ⟨hK s hsK t hts, (Finset.card_le_card hts).trans hsc⟩

omit [Fintype V] [DecidableEq V] in
theorem skeleton_subset (K : Finset (Finset V)) (j : ℕ) : skeleton K j ⊆ K :=
  Finset.filter_subset _ _

/-- Purity and the good-vertex count bound every bad simplex, including ones
lying on a boundary face of the triangulation. -/
theorem card_bad_le_of_good_count {K : Finset (Finset V)} {G : Finset V} {k m : ℕ}
    (hpure : ∀ s ∈ K, ∃ t ∈ K, s ⊆ t ∧ t.card = k + 1)
    (hgood : ∀ t ∈ K, t.card = k + 1 → m + 1 ≤ (t ∩ G).card)
    {s : Finset V} (hs : s ∈ inducedFaces K Gᶜ) : s.card + m ≤ k := by
  obtain ⟨hsK, hsG⟩ := mem_inducedFaces.mp hs
  obtain ⟨t, ht, hst, htc⟩ := hpure s hsK
  have hsub : s ⊆ t \ G := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨hst hv, Finset.mem_compl.mp (hsG hv)⟩
  have hc := Finset.card_le_card hsub
  have hpartition := Finset.card_inter_add_card_sdiff t G
  have hg := hgood t ht htc
  omega

omit [Fintype V] [DecidableEq V] in
theorem geometricCarrier_mono {K L : Finset (Finset V)} {p : V → E} (hKL : K ⊆ L) :
    geometricCarrier K p ⊆ geometricCarrier L p := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion₂.mpr ⟨s, hKL hs, hxs⟩

/-- Good and bad induced realizations are genuinely disjoint in the ambient
space, by the simplex intersection axiom. -/
theorem disjoint_geometric_good_bad {K : Finset (Finset V)} {p : V → E}
    (hgeom : IsGeometricRealization K p) (G : Finset V) :
    Disjoint (geometricCarrier (inducedFaces K G) p)
      (geometricCarrier (inducedFaces K Gᶜ) p) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hy
  obtain ⟨hsK, hsG⟩ := mem_inducedFaces.mp hs
  obtain ⟨htK, htG⟩ := mem_inducedFaces.mp ht
  have he : s ∩ t = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro v hv
    obtain ⟨hvs, hvt⟩ := Finset.mem_inter.mp hv
    exact Finset.mem_compl.mp (htG hvt) (hsG hvs)
  have hi := hgeom.intersection s hsK t htK ⟨hxs, hxt⟩
  simp [he] at hi

/-- The inverse of the geometric complement equivalence is the literal
inclusion of the good realization, not just an unspecified homotopy inverse. -/
theorem geometricInducedComplement_inv_val
    {K : Finset (Finset V)} {p : V → E} (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) (G : Finset V)
    (x : ↥(geometricCarrier (inducedFaces K G) p)) :
    ((geometricInducedComplementHomotopyEquiv hK hgeom G).invFun x).val = x.val := by
  change barycentricEvaluation p
      ((geometricRealizationHomeomorph (hgeom.induced G)).symm x).val = x.val
  exact congrArg Subtype.val ((geometricRealizationHomeomorph (hgeom.induced G)).apply_symm_apply x)

section Filling

variable [FiniteDimensional ℝ E]

/-- Nonemptiness is the reduced-degree-minus-one case of the local argument;
it needs only codimension one for the bad simplices. -/
theorem nonempty_geometricGood
    {K : Finset (Finset V)} {p : V → E} (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) (G : Finset V)
    (hconv : Convex ℝ (geometricCarrier K p))
    (hfull : affineSpan ℝ (geometricCarrier K p) = ⊤)
    (hbad : ∀ t ∈ inducedFaces K Gᶜ, t.card ≤ Module.finrank ℝ E) :
    (geometricCarrier (inducedFaces K G) p).Nonempty := by
  classical
  have hc : ∀ t ∈ pointFamily (inducedFaces K Gᶜ) p, t.card ≤ Module.finrank ℝ E := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.card_image_le.trans (hbad s hs)
  have hne := GeneralPosition.complement_nonempty hconv hfull hc
  rw [hullCarrier_pointFamily] at hne
  obtain ⟨x, hx⟩ := hne
  exact ⟨_, ((geometricInducedComplementHomotopyEquiv hK hgeom G) ⟨x, hx⟩).property⟩

/-- The good induced realization is path connected when the bad simplices
have codimension at least two. This includes the reduced-degree-zero part
of the local acyclicity argument without any homology comparison. -/
theorem pathConnectedSpace_geometricGood
    {K : Finset (Finset V)} {p : V → E} (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) (G : Finset V)
    (hconv : Convex ℝ (geometricCarrier K p))
    (hfull : affineSpan ℝ (geometricCarrier K p) = ⊤)
    (hbad : ∀ t ∈ inducedFaces K Gᶜ, t.card < Module.finrank ℝ E) :
    PathConnectedSpace ↥(geometricCarrier (inducedFaces K G) p) := by
  classical
  have hc : ∀ t ∈ pointFamily (inducedFaces K Gᶜ) p, t.card < Module.finrank ℝ E := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    exact (Finset.card_image_le).trans_lt (hbad s hs)
  have hconn := GeneralPosition.isPathConnected_complement hconv hfull hc
  rw [hullCarrier_pointFamily] at hconn
  have : PathConnectedSpace
      ↥(geometricCarrier K p \ geometricCarrier (inducedFaces K Gᶜ) p) :=
    isPathConnected_iff_pathConnectedSpace.mp hconn
  exact GeneralPosition.pathConnectedSpace_of_homotopyEquiv
    (geometricInducedComplementHomotopyEquiv hK hgeom G)

/-- The actual reduced H0 conclusion of the local argument. -/
theorem isIso_augmentation_geometricGood
    {K : Finset (Finset V)} {p : V → E} (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) (G : Finset V)
    (hconv : Convex ℝ (geometricCarrier K p))
    (hfull : affineSpan ℝ (geometricCarrier K p) = ⊤)
    (hbad : ∀ t ∈ inducedFaces K Gᶜ, t.card < Module.finrank ℝ E) :
    IsIso (realSingularAugmentation (TopCat.of ↥(geometricCarrier (inducedFaces K G) p))) := by
  have := pathConnectedSpace_geometricGood hK hgeom G hconv hfull hbad
  infer_instance

/-- A good skeleton in degree `j` has a contractible filling inside the
complement of the bad realization whenever `j + 1 + #bad ≤ dim E`. -/
theorem exists_contractible_filling_goodSkeleton
    {K : Finset (Finset V)} {p : V → E} (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) (G : Finset V) (j : ℕ)
    (hconv : Convex ℝ (geometricCarrier K p))
    (hfull : affineSpan ℝ (geometricCarrier K p) = ⊤)
    (hbad : ∀ t ∈ inducedFaces K Gᶜ, t.card + (j + 1) ≤ Module.finrank ℝ E) :
    ∃ C : Set E, geometricCarrier (skeleton (inducedFaces K G) j) p ⊆ C ∧
      C ⊆ geometricCarrier K p \ geometricCarrier (inducedFaces K Gᶜ) p ∧
      ContractibleSpace C := by
  classical
  have hsub : skeleton (inducedFaces K G) j ⊆ K :=
    (skeleton_subset _ _).trans fun _ hs ↦ (mem_inducedFaces.mp hs).1
  have hempty : ∅ ∈ K := by
    obtain ⟨x, hx⟩ := AffineSubspace.nonempty_of_affineSpan_eq_top ℝ E E hfull
    obtain ⟨s, hs, _⟩ := Set.mem_iUnion₂.mp hx
    exact hK s hs ∅ (Finset.empty_subset s)
  have hne : (pointFamily (skeleton (inducedFaces K G) j) p).Nonempty := by
    apply Finset.image_nonempty.mpr
    refine ⟨∅, Finset.mem_filter.mpr ⟨?_, by simp⟩⟩
    exact mem_inducedFaces.mpr ⟨hempty, Finset.empty_subset G⟩
  have hKP : GeneralPosition.hullCarrier (pointFamily (skeleton (inducedFaces K G) j) p) ⊆
      geometricCarrier K p := by
    rw [hullCarrier_pointFamily]
    exact geometricCarrier_mono hsub
  have hd : Disjoint
      (GeneralPosition.hullCarrier (pointFamily (skeleton (inducedFaces K G) j) p))
      (GeneralPosition.hullCarrier (pointFamily (inducedFaces K Gᶜ) p)) := by
    rw [hullCarrier_pointFamily, hullCarrier_pointFamily]
    exact (disjoint_geometric_good_bad hgeom G).mono_left
      (geometricCarrier_mono (skeleton_subset _ _))
  have hc : ∀ s ∈ pointFamily (skeleton (inducedFaces K G) j) p,
      ∀ t ∈ pointFamily (inducedFaces K Gᶜ) p,
        (s ∪ t).card ≤ Module.finrank ℝ E := by
    intro s hs t ht
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
    have hsc := (Finset.mem_filter.mp hs').2
    have htc := hbad t' ht'
    have hsimg := Finset.card_image_le (f := p) (s := s')
    have htimg := Finset.card_image_le (f := p) (s := t')
    have hu := Finset.card_union_le (s'.image p) (t'.image p)
    omega
  obtain ⟨C, hKC, hCP, hC⟩ := GeneralPosition.exists_contractible_filling
    hconv hfull hne hKP hd hc
  rw [hullCarrier_pointFamily] at hKC hCP
  exact ⟨C, hKC, hCP, hC⟩

/-- The low-dimensional good skeleton is null-homotopic inside the actual
complement of the bad induced realization. -/
theorem nullhomotopic_goodSkeleton_in_complement
    {K : Finset (Finset V)} {p : V → E} (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) (G : Finset V) (j : ℕ)
    (hconv : Convex ℝ (geometricCarrier K p))
    (hfull : affineSpan ℝ (geometricCarrier K p) = ⊤)
    (hbad : ∀ t ∈ inducedFaces K Gᶜ, t.card + (j + 1) ≤ Module.finrank ℝ E) :
    ∃ h : geometricCarrier (skeleton (inducedFaces K G) j) p ⊆
        geometricCarrier K p \ geometricCarrier (inducedFaces K Gᶜ) p,
      (ContinuousMap.inclusion h).Nullhomotopic := by
  obtain ⟨C, hKC, hCP, hC⟩ :=
    exists_contractible_filling_goodSkeleton hK hgeom G j hconv hfull hbad
  have := hC
  exact ⟨hKC.trans hCP, GeneralPosition.inclusion_nullhomotopic_of_contractible hKC hCP⟩

/-- Retracting the generic coned filling back to the good induced subcomplex
makes its low-dimensional skeleton inclusion null-homotopic there. -/
theorem nullhomotopic_goodSkeleton_in_good
    {K : Finset (Finset V)} {p : V → E} (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) (G : Finset V) (j : ℕ)
    (hconv : Convex ℝ (geometricCarrier K p))
    (hfull : affineSpan ℝ (geometricCarrier K p) = ⊤)
    (hbad : ∀ t ∈ inducedFaces K Gᶜ, t.card + (j + 1) ≤ Module.finrank ℝ E) :
    (ContinuousMap.inclusion (geometricCarrier_mono (p := p)
      (skeleton_subset (inducedFaces K G) j))).Nullhomotopic := by
  let e := geometricInducedComplementHomotopyEquiv hK hgeom G
  let f := ContinuousMap.inclusion (geometricCarrier_mono (p := p)
    (skeleton_subset (inducedFaces K G) j))
  obtain ⟨h, hn⟩ := nullhomotopic_goodSkeleton_in_complement hK hgeom G j hconv hfull hbad
  have he : e.invFun.comp f = ContinuousMap.inclusion h := by
    ext x
    exact geometricInducedComplement_inv_val hK hgeom G (f x)
  have hn' : (e.toFun.comp (e.invFun.comp f)).Nullhomotopic := by
    rw [he]
    exact hn.comp_right e.toFun
  have hhom : (e.toFun.comp (e.invFun.comp f)).Homotopic f :=
    e.right_inv.comp (ContinuousMap.Homotopic.refl f)
  obtain ⟨a, ha⟩ := hn'
  exact ⟨a, hhom.symm.trans ha⟩

/-- The genuine singular homology map of the good-skeleton inclusion is zero
in every positive degree under the geometric filling bound. -/
theorem singularHomology_goodSkeleton_map_zero
    {K : Finset (Finset V)} {p : V → E} (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) (G : Finset V) (j : ℕ)
    (hconv : Convex ℝ (geometricCarrier K p))
    (hfull : affineSpan ℝ (geometricCarrier K p) = ⊤)
    (hbad : ∀ t ∈ inducedFaces K Gᶜ, t.card + (j + 1) ≤ Module.finrank ℝ E)
    (n : ℕ) (hn : n ≠ 0) :
    (realSingularHomology n).map (TopCat.ofHom
      (ContinuousMap.inclusion (geometricCarrier_mono (p := p)
        (skeleton_subset (inducedFaces K G) j)))) = 0 :=
  GeneralPosition.homologyMap_eq_zero_of_nullhomotopic
    (nullhomotopic_goodSkeleton_in_good hK hgeom G j hconv hfull hbad) n hn

/-- The precise good-vertex and purity hypotheses used in the paper imply
the filling statement for every skeleton in the asserted degree range. -/
theorem filling_goodSkeleton_of_good_count
    {K : Finset (Finset V)} {p : V → E} (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) (G : Finset V) {m j : ℕ}
    (hconv : Convex ℝ (geometricCarrier K p))
    (hfull : affineSpan ℝ (geometricCarrier K p) = ⊤)
    (hpure : ∀ s ∈ K, ∃ t ∈ K, s ⊆ t ∧ t.card = Module.finrank ℝ E + 1)
    (hgood : ∀ t ∈ K, t.card = Module.finrank ℝ E + 1 → m + 1 ≤ (t ∩ G).card)
    (hj : j + 1 ≤ m) :
    ∃ C : Set E, geometricCarrier (skeleton (inducedFaces K G) j) p ⊆ C ∧
      C ⊆ geometricCarrier K p \ geometricCarrier (inducedFaces K Gᶜ) p ∧
      ContractibleSpace C := by
  apply exists_contractible_filling_goodSkeleton hK hgeom G j hconv hfull
  intro t ht
  have := card_bad_le_of_good_count hpure hgood ht
  omega

end Filling

end AffineTverberg.Simplicial
