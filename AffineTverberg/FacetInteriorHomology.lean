import AffineTverberg.GeometricLocalStar

set_option linter.style.header false

/-!
# Interior points of a facet are not homology boundary points

For a finite geometric simplicial complex whose polyhedron is a ball, the
centroid of a facet has a neighbourhood inside the polyhedron which is an
honest metric ball of the `n`-dimensional affine hull of that facet.  Its
puncture is homotopy equivalent to an `(n-1)`-sphere, so Mayer-Vietoris against
the contractible polyhedron shows that removing the centroid leaves homology of
rank one in degree `n - 1`.  Hence the centroid of a facet never lies in the
homology boundary.

Together with `IsSimplicialBall.centroid_boundaryRidge_mem_homologyBoundary`
this is the local-homology dictionary in the two extreme cases: codimension
zero (interior) and a codimension-one face in exactly one facet (boundary).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric Set

namespace AffineTverberg

variable {e n : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}

/-- Around the centroid of an affinely independent finset, all points of the
affine hull that are close enough lie in the closed simplex.  The witnesses are
the barycentric coordinate functionals of an affine basis extending `F`. -/
theorem exists_localRadius_affineSpan_of_notMem_erase {F : Finset (CoordinateSpace e)}
    (hind : AffineIndependent ℝ ((↑) : ↑F → CoordinateSpace e)) {p : CoordinateSpace e}
    (hpF : p ∈ convexHull ℝ (F : Set (CoordinateSpace e)))
    (hproper : ∀ v ∈ F, p ∉ convexHull ℝ
      ((F.erase v : Finset (CoordinateSpace e)) : Set (CoordinateSpace e))) :
    ∃ δ > 0, ∀ y ∈ affineSpan ℝ (F : Set (CoordinateSpace e)),
      ‖y - p‖ < δ → y ∈ convexHull ℝ (F : Set (CoordinateSpace e)) := by
  classical
  have hind' : AffineIndependent ℝ
      ((fun x => x) : ((F : Set (CoordinateSpace e)) : Type) → CoordinateSpace e) := hind
  obtain ⟨t, hFt, hindt, hspant⟩ := exists_subset_affineIndependent_affineSpan_eq_top hind'
  have hrange : affineSpan ℝ (Set.range (fun x : (↑t : Type) => (x : CoordinateSpace e))) = ⊤ := by
    rwa [Subtype.range_coe]
  let b : AffineBasis (↑t : Type) ℝ (CoordinateSpace e) :=
    ⟨fun x => (x : CoordinateSpace e), hindt, hrange⟩
  -- the coordinate functionals of the vertices of `F`
  let c : ↥F → (CoordinateSpace e →ᵃ[ℝ] ℝ) := fun i => b.coord ⟨(i : CoordinateSpace e), hFt i.2⟩
  have hc : ∀ i j : ↥F, c i (j : CoordinateSpace e) = if i = j then 1 else 0 := by
    intro i j
    simp only [c]
    have hbj : b ⟨(j : CoordinateSpace e), hFt j.2⟩ = (j : CoordinateSpace e) := rfl
    by_cases hij : i = j
    · have hif : (if i = j then (1 : ℝ) else 0) = 1 := by simp [hij]
      rw [hif]
      have hbi := b.coord_apply_eq ⟨(i : CoordinateSpace e), hFt i.2⟩
      rw [show b ⟨(i : CoordinateSpace e), hFt i.2⟩ = (i : CoordinateSpace e) from rfl] at hbi
      rw [← hij]
      exact hbi
    · have hne' : (⟨(i : CoordinateSpace e), hFt i.2⟩ : (↑t : Type)) ≠
          ⟨(j : CoordinateSpace e), hFt j.2⟩ := by
        simp only [ne_eq, Subtype.mk.injEq]
        exact fun h => hij (Subtype.ext h)
      have hif : (if i = j then (1 : ℝ) else 0) = 0 := by simp [hij]
      rw [hif]
      have hb0 := b.coord_apply_ne hne'
      rw [hbj] at hb0
      exact hb0
  -- the value of a coordinate on an affine combination of the vertices of `F`
  have hcomb : ∀ (w : ↥F → ℝ), (∑ i, w i = 1) → ∀ i : ↥F,
      c i (Finset.affineCombination ℝ (Finset.univ : Finset ↥F)
        ((↑) : ↥F → CoordinateSpace e) w) = w i := by
    intro w hw i
    rw [Finset.univ.map_affineCombination ((↑) : ↥F → CoordinateSpace e) w hw (c i),
      Finset.affineCombination_eq_linear_combination _ _ _ hw]
    have : ∀ j : ↥F, w j • (c i ((j : CoordinateSpace e))) = if i = j then w j else 0 := by
      intro j
      rw [hc i j]
      by_cases hij : i = j <;> simp [hij]
    simp only [Function.comp_apply, this]
    simp
  -- the coordinates are nonnegative on the closed simplex
  have hnonneg : ∀ (i : ↥F), ∀ z ∈ convexHull ℝ (F : Set (CoordinateSpace e)), 0 ≤ c i z := by
    intro i z hz
    have himg : (c i) '' (convexHull ℝ (F : Set (CoordinateSpace e))) =
        convexHull ℝ ((c i) '' (F : Set (CoordinateSpace e))) := AffineMap.image_convexHull _ _
    have hmem : c i z ∈ convexHull ℝ ((c i) '' (F : Set (CoordinateSpace e))) := by
      rw [← himg]
      exact ⟨z, hz, rfl⟩
    have hsub : convexHull ℝ ((c i) '' (F : Set (CoordinateSpace e))) ⊆ Set.Ici (0 : ℝ) := by
      apply convexHull_min _ (convex_Ici 0)
      rintro _ ⟨x, hx, rfl⟩
      have hx' := hc i ⟨x, hx⟩
      simp only [Set.mem_Ici]
      rw [hx']
      split <;> norm_num
    exact hsub hmem
  -- and they are strictly positive at a point off every proper face
  have hpspan : p ∈ affineSpan ℝ (Set.range ((↑) : ↥F → CoordinateSpace e)) := by
    rw [Subtype.range_coe]
    exact convexHull_subset_affineSpan _ hpF
  obtain ⟨w, hw1, hpw⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hpspan
  have hcw : ∀ i : ↥F, c i p = w i := by
    intro i
    rw [hpw]
    exact hcomb w hw1 i
  have hpos : ∀ i : ↥F, 0 < c i p := by
    intro i
    rcases lt_or_eq_of_le (hnonneg i p hpF) with hlt | heq
    · exact hlt
    · exfalso
      have hwi : w i = 0 := by rw [← hcw i, ← heq]
      have hsum : ∑ j ∈ (Finset.univ : Finset ↥F).erase i, w j = 1 := by
        rw [Finset.sum_erase _ hwi]
        exact hw1
      have hlin : p = ∑ j : ↥F, w j • (j : CoordinateSpace e) := by
        rw [hpw, Finset.affineCombination_eq_linear_combination _ _ _ hw1]
      have hlin' : p = ∑ j ∈ (Finset.univ : Finset ↥F).erase i,
          w j • (j : CoordinateSpace e) := by
        rw [hlin, Finset.sum_erase _ (by rw [hwi, zero_smul])]
      have hcm : ((Finset.univ : Finset ↥F).erase i).centerMass w
          (fun j : ↥F => (j : CoordinateSpace e)) = p := by
        rw [Finset.centerMass_eq_of_sum_1 _ _ hsum, ← hlin']
      have hmemE : p ∈ convexHull ℝ
          ((F.erase (i : CoordinateSpace e) : Finset (CoordinateSpace e)) :
            Set (CoordinateSpace e)) := by
        rw [← hcm]
        refine Finset.centerMass_mem_convexHull _ (fun j _ => ?_) ?_ (fun j hj => ?_)
        · rw [← hcw j]
          exact hnonneg j p hpF
        · rw [hsum]
          norm_num
        · have hji : j ≠ i := (Finset.mem_erase.mp hj).1
          exact Finset.mem_coe.mpr
            (Finset.mem_erase.mpr ⟨fun hcon => hji (Subtype.ext hcon), j.2⟩)
      exact hproper (i : CoordinateSpace e) i.2 hmemE
  -- the set where all these coordinates are positive is open
  have hopen : IsOpen {y : CoordinateSpace e | ∀ i : ↥F, 0 < c i y} := by
    have : {y : CoordinateSpace e | ∀ i : ↥F, 0 < c i y} = ⋂ i : ↥F, (c i) ⁻¹' (Ioi 0) := by
      ext y
      simp [Set.mem_iInter]
    rw [this]
    exact isOpen_iInter_of_finite fun i =>
      (((c i).continuous_of_finiteDimensional).isOpen_preimage _ isOpen_Ioi)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen _ (fun i => hpos i)
  refine ⟨δ, hδ, fun y hy hdist => ?_⟩
  have hyV : ∀ i : ↥F, 0 < c i y := by
    apply hball
    simpa [Metric.mem_ball, dist_eq_norm] using hdist
  have hyrange : y ∈ affineSpan ℝ (Set.range ((↑) : ↥F → CoordinateSpace e)) := by
    rwa [Subtype.range_coe]
  obtain ⟨w, hw1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hyrange
  have hwnonneg : ∀ i ∈ (Finset.univ : Finset ↥F), 0 ≤ w i := by
    intro i _
    have hpos' := hyV i
    rw [hcomb w hw1 i] at hpos'
    exact le_of_lt hpos'
  have := affineCombination_mem_convexHull (R := ℝ)
    (v := ((↑) : ↥F → CoordinateSpace e)) (w := w) hwnonneg hw1
  rwa [Subtype.range_coe] at this

/-- The centroid version: near the centroid of `F`, the affine hull of `F`
is contained in the closed simplex. -/
theorem exists_localRadius_affineSpan {F : Finset (CoordinateSpace e)}
    (hind : AffineIndependent ℝ ((↑) : ↑F → CoordinateSpace e)) (hne : F.Nonempty) :
    ∃ δ > 0, ∀ y ∈ affineSpan ℝ (F : Set (CoordinateSpace e)),
      ‖y - F.centroid ℝ id‖ < δ → y ∈ convexHull ℝ (F : Set (CoordinateSpace e)) := by
  refine exists_localRadius_affineSpan_of_notMem_erase hind
    (F.centroid_mem_convexHull (R := ℝ) hne) (fun v hv hmem => ?_)
  have hsub := subset_of_centroid_mem_affineSpan hne hind (Finset.erase_subset v F)
    (convexHull_subset_affineSpan _ hmem)
  exact (Finset.notMem_erase v F) (hsub hv)

/-! ### The local model of a neighbourhood inside an affine subspace -/

section LocalModel

variable {S : Set (CoordinateSpace e)} {W : Submodule ℝ (CoordinateSpace e)} {r : ℝ}
  (P : ↥S)

/-- If, near `P`, the set `S` is exactly the `r`-ball of the affine subspace
`P + W`, then that neighbourhood is homeomorphic to the `r`-ball of `W`. -/
def localBallHomeomorph
    (hmemW : ∀ x ∈ S, ‖x - (P : CoordinateSpace e)‖ < r → x - (P : CoordinateSpace e) ∈ W)
    (hback : ∀ u : ↥W, ‖(u : CoordinateSpace e)‖ < r →
      (P : CoordinateSpace e) + (u : CoordinateSpace e) ∈ S) :
    ↥{q : ↥S | ‖(q : CoordinateSpace e) - (P : CoordinateSpace e)‖ < r} ≃ₜ
      ↥(ball (0 : ↥W) r) where
  toFun q := by
    refine ⟨⟨(q : CoordinateSpace e) - (P : CoordinateSpace e), hmemW q.1.1 q.1.2 q.2⟩, ?_⟩
    have h : ‖(q : CoordinateSpace e) - (P : CoordinateSpace e)‖ < r := q.2
    exact mem_ball_zero_iff.mpr h
  invFun u := by
    have h : ‖(u.1 : CoordinateSpace e)‖ < r := mem_ball_zero_iff.mp u.2
    refine ⟨⟨(P : CoordinateSpace e) + (u.1 : CoordinateSpace e), hback u.1 h⟩, ?_⟩
    change ‖((P : CoordinateSpace e) + (u.1 : CoordinateSpace e)) - (P : CoordinateSpace e)‖ < r
    simpa using h
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  continuous_toFun :=
    (((continuous_subtype_val.comp continuous_subtype_val).sub
      continuous_const).subtype_mk _).subtype_mk _
  continuous_invFun :=
    ((continuous_const.add
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _).subtype_mk _

/-- The same neighbourhood with `P` removed is the punctured `r`-ball of `W`. -/
def localPuncturedHomeomorph
    (hmemW : ∀ x ∈ S, ‖x - (P : CoordinateSpace e)‖ < r → x - (P : CoordinateSpace e) ∈ W)
    (hback : ∀ u : ↥W, ‖(u : CoordinateSpace e)‖ < r →
      (P : CoordinateSpace e) + (u : CoordinateSpace e) ∈ S) :
    ↥({q : ↥S | q ≠ P} ∩
      {q : ↥S | ‖(q : CoordinateSpace e) - (P : CoordinateSpace e)‖ < r}) ≃ₜ
      ↥(puncturedNbhd (0 : ↥W) r) where
  toFun q := by
    refine ⟨⟨(q : CoordinateSpace e) - (P : CoordinateSpace e), hmemW q.1.1 q.1.2 q.2.2⟩, ?_, ?_⟩
    · intro hzero
      apply q.2.1
      have h0 : (q : CoordinateSpace e) - (P : CoordinateSpace e) = 0 :=
        congrArg Subtype.val hzero
      exact Subtype.ext (sub_eq_zero.mp h0)
    · have h : ‖(q : CoordinateSpace e) - (P : CoordinateSpace e)‖ < r := q.2.2
      simpa using h
  invFun u := by
    have h : ‖(u.1 : CoordinateSpace e)‖ < r := by
      have h0 : ‖u.1 - (0 : ↥W)‖ < r := u.2.2
      simpa using h0
    refine ⟨⟨(P : CoordinateSpace e) + (u.1 : CoordinateSpace e), hback u.1 h⟩, ?_, ?_⟩
    · intro hq
      apply u.2.1
      have h0 : (P : CoordinateSpace e) + (u.1 : CoordinateSpace e) = (P : CoordinateSpace e) :=
        congrArg Subtype.val hq
      apply Subtype.ext
      simpa using h0
    · change ‖((P : CoordinateSpace e) + (u.1 : CoordinateSpace e)) - (P : CoordinateSpace e)‖ < r
      simpa using h
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  continuous_toFun :=
    (((continuous_subtype_val.comp continuous_subtype_val).sub
      continuous_const).subtype_mk _).subtype_mk _
  continuous_invFun :=
    ((continuous_const.add
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _).subtype_mk _

end LocalModel

/-! ### The centroid of a facet is an interior point -/

namespace IsSimplicialBall

/-- **A carrier point of a facet is not a homology boundary point.**  A metric
ball of the affine hull of the facet is a neighbourhood of such a point inside
the polyhedron, so the punctured neighbourhood is homotopy equivalent to an
`(n-1)`-sphere; Mayer-Vietoris injectivity against the contractible polyhedron
shows that the complement of the point has homology of rank at least one in
degree `n - 1`. -/
theorem carrierPoint_facet_notMem_homologyBoundary
    (hball : IsSimplicialBall n K) (hn : 2 ≤ n)
    {F : Finset (CoordinateSpace e)} (hF : F ∈ K.facets) {p : CoordinateSpace e}
    (hp : IsCarrierPoint K F p) :
    (⟨p, hp.mem_space (Geometry.SimplicialComplex.facets_subset hF)⟩ : ↥K.space) ∉
      homologyBoundary ↥K.space (n - 1) := by
  classical
  have hFfaces : F ∈ K.faces := Geometry.SimplicialComplex.facets_subset hF
  have hind : AffineIndependent ℝ ((↑) : ↑F → CoordinateSpace e) := K.indep hFfaces
  have hproper : ∀ v ∈ F, p ∉ convexHull ℝ
      ((F.erase v : Finset (CoordinateSpace e)) : Set (CoordinateSpace e)) := by
    intro v hv hmem
    rcases (F.erase v).eq_empty_or_nonempty with hempty | hne'
    · rw [hempty] at hmem
      simp at hmem
    · exact hp.notMem_convexHull_erase hFfaces hv hne' hmem
  obtain ⟨δ, hδ, hd⟩ := exists_localRadius_affineSpan_of_notMem_erase hind hp.1 hproper
  have hmax : ∀ G ∈ K.faces, F ⊆ G → G ⊆ F := by
    intro G hG hFG
    have hGF := (Geometry.SimplicialComplex.mem_facets.mp hF).2 G hG hFG
    exact hGF ▸ Finset.Subset.refl G
  obtain ⟨ε, hε, hloc⟩ := exists_localRadius_of_carrier hball.finite_faces hp hmax
  have hr : 0 < min δ ε := lt_min hδ hε
  have hpspace : p ∈ K.space := hp.mem_space hFfaces
  have hpconv : p ∈ convexHull ℝ (F : Set (CoordinateSpace e)) := hp.1
  have hpspan : p ∈ affineSpan ℝ (F : Set (CoordinateSpace e)) :=
    convexHull_subset_affineSpan _ hpconv
  -- the direction of the affine hull of the facet, of dimension `n`
  have hWdim : Module.finrank ℝ ↥(affineSpan ℝ (F : Set (CoordinateSpace e))).direction = n := by
    have hcard : Fintype.card ↥F = n + 1 := by
      simp [Fintype.card_coe, hball.pure F hF]
    have hvs := hind.finrank_vectorSpan hcard
    have hset : vectorSpan ℝ (Set.range ((↑) : ↥F → CoordinateSpace e)) =
        (affineSpan ℝ (F : Set (CoordinateSpace e))).direction := by
      rw [direction_affineSpan, Subtype.range_coe]
    rw [← (LinearEquiv.ofEq _ _ hset).finrank_eq]
    exact hvs
  have hWdim' : Module.finrank ℝ ↥(affineSpan ℝ (F : Set (CoordinateSpace e))).direction =
      (n - 2) + 2 := by rw [hWdim]; omega
  -- the two directions of the local identification
  have hmemW : ∀ x ∈ K.space, ‖x - p‖ < min δ ε →
      x - p ∈ (affineSpan ℝ (F : Set (CoordinateSpace e))).direction := by
    intro x hx hxr
    have hxconv : x ∈ convexHull ℝ (F : Set (CoordinateSpace e)) :=
      hloc x hx (lt_of_lt_of_le hxr (min_le_right _ _))
    have hxspan : x ∈ affineSpan ℝ (F : Set (CoordinateSpace e)) :=
      convexHull_subset_affineSpan _ hxconv
    simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hxspan hpspan
  have hback : ∀ u : ↥(affineSpan ℝ (F : Set (CoordinateSpace e))).direction,
      ‖(u : CoordinateSpace e)‖ < min δ ε →
      p + (u : CoordinateSpace e) ∈ K.space := by
    intro u hu
    have hspan : p + (u : CoordinateSpace e) ∈
        affineSpan ℝ (F : Set (CoordinateSpace e)) := by
      have hv := AffineSubspace.vadd_mem_of_mem_direction u.2 hpspan
      simpa [vadd_eq_add, add_comm] using hv
    refine Geometry.SimplicialComplex.convexHull_subset_space hFfaces (hd _ hspan ?_)
    simpa using lt_of_lt_of_le hu (min_le_left _ _)
  set P : ↥K.space := ⟨p, hpspace⟩
  have hPval : (P : CoordinateSpace e) = p := rfl
  -- the Mayer-Vietoris cover
  have hAopen : IsOpen {q : ↥K.space | q ≠ P} := isOpen_compl_singleton
  have hBopen : IsOpen
      {q : ↥K.space | ‖(q : CoordinateSpace e) - (P : CoordinateSpace e)‖ < min δ ε} := by
    have hcont : Continuous fun q : ↥K.space =>
        ‖(q : CoordinateSpace e) - (P : CoordinateSpace e)‖ :=
      continuous_norm.comp (continuous_subtype_val.sub continuous_const)
    exact isOpen_lt hcont continuous_const
  have hcov : ∀ q : ↥K.space, q ∈ {q : ↥K.space | q ≠ P} ∨
      q ∈ {q : ↥K.space | ‖(q : CoordinateSpace e) - (P : CoordinateSpace e)‖ < min δ ε} := by
    intro q
    by_cases h : q = P
    · refine Or.inr ?_
      change ‖(q : CoordinateSpace e) - (P : CoordinateSpace e)‖ < min δ ε
      rw [h]
      simpa using hr
    · exact Or.inl h
  have homeoB := localBallHomeomorph (W := (affineSpan ℝ (F : Set (CoordinateSpace e))).direction)
    (r := min δ ε) P hmemW hback
  have homeoAB :=
    localPuncturedHomeomorph (W := (affineSpan ℝ (F : Set (CoordinateSpace e))).direction)
      (r := min δ ε) P hmemW hback
  -- the punctured neighbourhood has the homology of an (n-1)-sphere
  have hequiv : ContinuousMap.HomotopyEquiv
      ↥({q : ↥K.space | q ≠ P} ∩
        {q : ↥K.space | ‖(q : CoordinateSpace e) - (P : CoordinateSpace e)‖ < min δ ε})
      ↥(sphere (0 : ↥(affineSpan ℝ (F : Set (CoordinateSpace e))).direction) 1) :=
    homeoAB.toHomotopyEquiv.trans (puncturedNbhdHomotopyEquiv _ (min δ ε) hr)
  have hiso := (realSingularHomologyIsoOfHomotopyEquiv hequiv ((n - 2) + 1)).toLinearEquiv
  have hrank : Module.finrank ℝ ((realSingularHomology ((n - 2) + 1)).obj
      (TopCat.of ↥({q : ↥K.space | q ≠ P} ∩
        {q : ↥K.space | ‖(q : CoordinateSpace e) - (P : CoordinateSpace e)‖ < min δ ε}))) = 1 := by
    rw [hiso.finrank_eq]
    exact Simplicial.finrank_realSingularHomology_sphere
      (E := ↥(affineSpan ℝ (F : Set (CoordinateSpace e))).direction) (n := n - 2) hWdim'
  have hdeg : (n - 2) + 1 = n - 1 := by omega
  rw [hdeg] at hrank
  -- the two vanishing inputs of Mayer-Vietoris
  have : ContractibleSpace ↥K.space := hball.contractibleSpace_space
  have hXzero : IsZero ((realSingularHomology ((n - 1) + 1)).obj (TopCat.of ↥K.space)) := by
    have : Subsingleton ((realSingularHomology ((n - 1) + 1)).obj (TopCat.of ↥K.space)) :=
      realSingularHomology_subsingleton_of_contractible ↥K.space ((n - 1) + 1) (by omega)
    exact ModuleCat.isZero_of_subsingleton _
  have hBzero : IsZero ((realSingularHomology (n - 1)).obj (TopCat.of
      ↥{q : ↥K.space | ‖(q : CoordinateSpace e) - (P : CoordinateSpace e)‖ < min δ ε})) := by
    have hball' : ContractibleSpace
        ↥(ball (0 : ↥(affineSpan ℝ (F : Set (CoordinateSpace e))).direction) (min δ ε)) :=
      (convex_ball _ (min δ ε)).contractibleSpace ⟨0, by simpa using hr⟩
    have : ContractibleSpace
        ↥{q : ↥K.space | ‖(q : CoordinateSpace e) - (P : CoordinateSpace e)‖ < min δ ε} :=
      homeoB.toHomotopyEquiv.contractibleSpace
    have : Subsingleton ((realSingularHomology (n - 1)).obj (TopCat.of
        ↥{q : ↥K.space | ‖(q : CoordinateSpace e) - (P : CoordinateSpace e)‖ < min δ ε})) :=
      realSingularHomology_subsingleton_of_contractible _ (n - 1) (by omega)
    exact ModuleCat.isZero_of_subsingleton _
  have hinj := AffChain.injective_homology_inter_left (X := TopCat.of ↥K.space)
    {q : ↥K.space | q ≠ P}
    {q : ↥K.space | ‖(q : CoordinateSpace e) - (P : CoordinateSpace e)‖ < min δ ε}
    hAopen hBopen hcov (n - 1) hXzero hBzero
  intro hmemb
  have hsubA : Subsingleton ((realSingularHomology (n - 1)).obj
      (TopCat.of ↥{q : ↥K.space | q ≠ P})) := hmemb
  have hsubAB : Subsingleton ((realSingularHomology (n - 1)).obj (TopCat.of
      ↥({q : ↥K.space | q ≠ P} ∩
        {q : ↥K.space | ‖(q : CoordinateSpace e) - (P : CoordinateSpace e)‖ < min δ ε}))) :=
    ⟨fun x y => hinj (Subsingleton.elim _ _)⟩
  rw [Module.finrank_zero_of_subsingleton] at hrank
  exact zero_ne_one hrank

/-- The centroid of a facet is not a homology boundary point. -/
theorem centroid_facet_notMem_homologyBoundary
    (hball : IsSimplicialBall n K) (hn : 2 ≤ n)
    {F : Finset (CoordinateSpace e)} (hF : F ∈ K.facets) :
    (⟨F.centroid ℝ id, centroid_mem_space (Geometry.SimplicialComplex.facets_subset hF)⟩ :
        ↥K.space) ∉ homologyBoundary ↥K.space (n - 1) :=
  carrierPoint_facet_notMem_homologyBoundary hball hn hF
    (isCarrierPoint_centroid (Geometry.SimplicialComplex.facets_subset hF))

end IsSimplicialBall

end AffineTverberg
