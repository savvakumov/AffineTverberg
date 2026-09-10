import AffineTverberg.GeneralPositionCone
import AffineTverberg.SingularHomology

set_option linter.style.header false

/-!
# Topological consequences of the general-position cone

The inclusion of a low-dimensional finite affine carrier into the complement
of a sufficiently small bad polyhedron is null-homotopic. In positive degrees
its map on actual singular homology is zero. The complement itself is nonempty
in codimension at least one, and path connected in codimension at least two.
These statements use the explicit generic coned carrier, not an assumed
general-position theorem or a homology comparison.
-/

noncomputable section

open Set CategoryTheory CategoryTheory.Limits

namespace AffineTverberg.GeneralPosition

/-- Path connectedness is preserved by a genuine homotopy equivalence;
surjectivity of its chosen forward map is not required. -/
theorem pathConnectedSpace_of_homotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) [PathConnectedSpace X] : PathConnectedSpace Y := by
  obtain ⟨H⟩ := e.right_inv
  have hpoint (y : Y) : Joined (e.toFun (e.invFun y)) y := ⟨H.evalAt y⟩
  refine ⟨(PathConnectedSpace.nonempty (X := X)).map e.toFun, ?_⟩
  intro y z
  exact (hpoint y).symm.trans
    (((PathConnectedSpace.joined (e.invFun y) (e.invFun z)).map e.continuous).trans (hpoint z))

/-- A null-homotopic continuous map induces the zero map on ordinary singular
homology in positive degrees. The constant map factors through `Unit`. -/
theorem homologyMap_eq_zero_of_nullhomotopic
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)}
    (hf : f.Nullhomotopic) (n : ℕ) (hn : n ≠ 0) :
    (realSingularHomology n).map (TopCat.ofHom f) = 0 := by
  obtain ⟨y, ⟨H⟩⟩ := hf
  rw [realSingularHomology_map_eq_of_homotopy H n]
  change (realSingularHomology n).map (TopCat.ofHom (ContinuousMap.const X y)) = 0
  have hfactor : TopCat.ofHom (ContinuousMap.const X y) =
      TopCat.ofHom (ContinuousMap.const X ()) ≫
        TopCat.ofHom (ContinuousMap.const Unit y) := rfl
  rw [hfactor, Functor.map_comp]
  have := realSingularHomology_subsingleton_of_contractible Unit n hn
  have hz : (realSingularHomology n).map (TopCat.ofHom (ContinuousMap.const X ())) = 0 := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun _ ↦ Subsingleton.elim _ _
  rw [hz, zero_comp]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A bad finite polyhedron of dimension strictly below the ambient dimension
cannot fill a full-dimensional convex set. -/
theorem complement_nonempty {B : Finset (Finset E)} {P : Set E}
    (hP : Convex ℝ P) (hfull : affineSpan ℝ P = ⊤)
    (hcard : ∀ t ∈ B, t.card ≤ Module.finrank ℝ E) :
    (P \ hullCarrier B).Nonempty := by
  classical
  have hd := dense_avoid_affineSubspaces B (fun t ↦ affineSpan ℝ (t : Set E))
    (fun t ht ↦ affineSpan_ne_top_of_card_le (hcard t ht))
  obtain ⟨p, hp, havoid⟩ := hd.inter_open_nonempty (interior P) isOpen_interior
    (hP.interior_nonempty_iff_affineSpan_eq_top.mpr hfull)
  refine ⟨p, interior_subset hp, ?_⟩
  intro hbad
  obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hbad
  exact havoid t ht (convexHull_subset_affineSpan (t : Set E) hpt)

omit [FiniteDimensional ℝ E] [NormedSpace ℝ E] in
/-- Factoring a subspace inclusion through a contractible intermediate subset
provides an actual null-homotopy in the ambient target. -/
theorem inclusion_nullhomotopic_of_contractible {S C T : Set E}
    (hSC : S ⊆ C) (hCT : C ⊆ T) [ContractibleSpace C] :
    (ContinuousMap.inclusion (hSC.trans hCT)).Nullhomotopic := by
  exact ((id_nullhomotopic C).comp_left (ContinuousMap.inclusion hSC)).comp_right
    (ContinuousMap.inclusion hCT)

/-- The generic cone gives a null-homotopy of the inclusion of the entire
finite affine carrier inside the same complement. -/
theorem inclusion_nullhomotopic [DecidableEq E] {K B : Finset (Finset E)} {P : Set E}
    (hP : Convex ℝ P) (hfull : affineSpan ℝ P = ⊤) (hK : K.Nonempty)
    (hKP : hullCarrier K ⊆ P)
    (hdisj : Disjoint (hullCarrier K) (hullCarrier B))
    (hcard : ∀ s ∈ K, ∀ t ∈ B, (s ∪ t).card ≤ Module.finrank ℝ E) :
    (ContinuousMap.inclusion (show hullCarrier K ⊆ P \ hullCarrier B from
      fun _ hx ↦ ⟨hKP hx, fun hb ↦ Set.disjoint_left.mp hdisj hx hb⟩)).Nullhomotopic := by
  classical
  obtain ⟨C, hKC, hCP, hC⟩ := exists_contractible_filling hP hfull hK hKP hdisj hcard
  let := hC
  exact inclusion_nullhomotopic_of_contractible hKC hCP

omit [FiniteDimensional ℝ E] [NormedSpace ℝ E] in
/-- Positive-degree singular homology of the first inclusion vanishes when
the map factors through a contractible subset. -/
theorem homologyMap_inclusion_eq_zero_of_contractible {S C T : Set E}
    (hSC : S ⊆ C) (hCT : C ⊆ T) [ContractibleSpace C] (n : ℕ) (hn : n ≠ 0) :
    (realSingularHomology n).map
      (TopCat.ofHom (ContinuousMap.inclusion (hSC.trans hCT))) = 0 := by
  have hcomp : TopCat.ofHom (ContinuousMap.inclusion (hSC.trans hCT)) =
      TopCat.ofHom (ContinuousMap.inclusion hSC) ≫
        TopCat.ofHom (ContinuousMap.inclusion hCT) := rfl
  rw [hcomp, Functor.map_comp]
  have := realSingularHomology_subsingleton_of_contractible C n hn
  have hzero : (realSingularHomology n).map (TopCat.ofHom (ContinuousMap.inclusion hSC)) = 0 := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun _ ↦ Subsingleton.elim _ _
  rw [hzero, zero_comp]

/-- The actual singular homology map out of the low-dimensional finite
carrier is zero in every positive degree. -/
theorem homologyMap_inclusion_eq_zero [DecidableEq E] {K B : Finset (Finset E)} {P : Set E}
    (hP : Convex ℝ P) (hfull : affineSpan ℝ P = ⊤) (hK : K.Nonempty)
    (hKP : hullCarrier K ⊆ P)
    (hdisj : Disjoint (hullCarrier K) (hullCarrier B))
    (hcard : ∀ s ∈ K, ∀ t ∈ B, (s ∪ t).card ≤ Module.finrank ℝ E)
    (n : ℕ) (hn : n ≠ 0) :
    (realSingularHomology n).map (TopCat.ofHom
      (ContinuousMap.inclusion (show hullCarrier K ⊆ P \ hullCarrier B from
        fun _ hx ↦ ⟨hKP hx, fun hb ↦ Set.disjoint_left.mp hdisj hx hb⟩))) = 0 := by
  classical
  obtain ⟨C, hKC, hCP, hC⟩ := exists_contractible_filling hP hfull hK hKP hdisj hcard
  let := hC
  exact homologyMap_inclusion_eq_zero_of_contractible hKC hCP n hn

/-- The complement of a finite polyhedron of codimension at least two inside
a full-dimensional convex set is path connected. -/
theorem isPathConnected_complement {B : Finset (Finset E)} {P : Set E}
    (hP : Convex ℝ P) (hfull : affineSpan ℝ P = ⊤)
    (hcard : ∀ t ∈ B, t.card < Module.finrank ℝ E) :
    IsPathConnected (P \ hullCarrier B) := by
  classical
  refine isPathConnected_iff.mpr ⟨complement_nonempty hP hfull
    (fun t ht ↦ (hcard t ht).le), ?_⟩
  intro x hx y hy
  let K : Finset (Finset E) := {{x}, {y}}
  have hcarrier : hullCarrier K = {x, y} := by
    ext z
    simp [hullCarrier, K, or_comm]
  have hKP : hullCarrier K ⊆ P := by
    rw [hcarrier]
    exact Set.insert_subset hx.1 (Set.singleton_subset_iff.mpr hy.1)
  have hdisj : Disjoint (hullCarrier K) (hullCarrier B) := by
    rw [hcarrier]
    exact Set.disjoint_left.mpr fun z hz hb ↦ by
      rcases hz with rfl | hzy
      · exact hx.2 hb
      · exact hy.2 (Set.mem_singleton_iff.mp hzy ▸ hb)
  have hKcard : ∀ s ∈ K, s.card = 1 := by
    intro s hs
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl <;> simp
  obtain ⟨C, hKC, hCP, hC⟩ := exists_contractible_filling hP hfull
    (show K.Nonempty from Finset.insert_nonempty _ _) hKP hdisj (by
      intro s hs t ht
      have hle := Finset.card_union_le s t
      rw [hKcard s hs] at hle
      have := hcard t ht
      omega)
  have := hC
  have hpC : IsPathConnected C := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  exact (hpC.joinedIn x (hKC (hcarrier ▸ Set.mem_insert x {y})) y
    (hKC (hcarrier ▸ Set.mem_insert_of_mem x (Set.mem_singleton y)))).mono hCP

/-- This is the reduced-degree-zero acyclicity conclusion for the actual
complement, expressed by the genuine singular augmentation. -/
theorem isIso_augmentation_complement {B : Finset (Finset E)} {P : Set E}
    (hP : Convex ℝ P) (hfull : affineSpan ℝ P = ⊤)
    (hcard : ∀ t ∈ B, t.card < Module.finrank ℝ E) :
    IsIso (realSingularAugmentation (TopCat.of ↥(P \ hullCarrier B))) := by
  have : PathConnectedSpace ↥(P \ hullCarrier B) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_complement hP hfull hcard)
  infer_instance

end AffineTverberg.GeneralPosition
