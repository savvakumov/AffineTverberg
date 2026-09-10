import AffineTverberg.InducedComplement
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.LinearAlgebra.AffineSpace.Independent

set_option linter.style.header false

/-!
# Barycentric and geometric realizations

The normalization homotopy in `InducedComplement` is written in standard
barycentric coordinates. This file identifies that model with the geometric
realization of any finite complex with affinely independent faces and the
usual convex-hull intersection property. In particular, no global affine
independence of the vertices is required.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg.Simplicial

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The standard simplex supported on a specified face. -/
def barycentricFace (s : Finset V) : Set (V → ℝ) :=
  {x | (∀ v, 0 ≤ x v) ∧ (∑ v, x v) = 1 ∧ ∀ v, v ∉ s → x v = 0}

omit [DecidableEq V] in
theorem barycentricFace_mono {s t : Finset V} (hst : s ⊆ t) :
    barycentricFace s ⊆ barycentricFace t := by
  rintro x ⟨h0, h1, hs⟩
  exact ⟨h0, h1, fun v hv ↦ hs v fun hvs ↦ hv (hst hvs)⟩

omit [DecidableEq V] in
theorem barycentricCarrier_eq_union (K : Finset (Finset V)) :
    barycentricCarrier K = ⋃ s ∈ K, barycentricFace s := by
  ext x
  simp only [barycentricCarrier, barycentricFace, mem_ofPred_eq, mem_iUnion]
  aesop

omit [DecidableEq V] in
theorem barycentricFace_convex (s : Finset V) : Convex ℝ (barycentricFace s) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun v ↦ add_nonneg (mul_nonneg ha (hx.1 v)) (mul_nonneg hb (hy.1 v)), ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx.2.1, hy.2.1, mul_one, hab]
  · intro v hv
    simp [hx.2.2 v hv, hy.2.2 v hv]

omit [DecidableEq V] in
theorem barycentricFace_isClosed (s : Finset V) : IsClosed (barycentricFace s) := by
  have heq : barycentricFace s = stdSimplex ℝ V ∩
      ⋂ v, ⋂ (_ : v ∉ s), {x : V → ℝ | x v = 0} := by
    ext x
    simp [barycentricFace, stdSimplex, and_assoc]
  rw [heq]
  exact (isClosed_stdSimplex ℝ V).inter
    (isClosed_iInter fun v ↦ isClosed_iInter fun _ ↦
      isClosed_eq (continuous_apply v) continuous_const)

omit [DecidableEq V] in
theorem barycentricFace_isCompact (s : Finset V) : IsCompact (barycentricFace s) :=
  (isCompact_stdSimplex ℝ V).of_isClosed_subset (barycentricFace_isClosed s)
    (fun _ hx ↦ ⟨hx.1, hx.2.1⟩)

omit [DecidableEq V] in
theorem barycentricCarrier_isCompact (K : Finset (Finset V)) :
    IsCompact (barycentricCarrier K) := by
  rw [barycentricCarrier_eq_union]
  exact K.finite_toSet.isCompact_biUnion fun s _ ↦ barycentricFace_isCompact s

omit [DecidableEq V] in
theorem barycentricCarrier_mono {K L : Finset (Finset V)} (hKL : K ⊆ L) :
    barycentricCarrier K ⊆ barycentricCarrier L := by
  rintro x ⟨h0, h1, s, hs, hxs⟩
  exact ⟨h0, h1, s, hKL hs, hxs⟩

theorem single_mem_barycentricFace {s : Finset V} {v : V} (hv : v ∈ s) :
    Pi.single v (1 : ℝ) ∈ barycentricFace s := by
  refine ⟨fun w ↦ ?_, ?_, ?_⟩
  · by_cases h : w = v <;> simp [h]
  · simp [Pi.single_apply, eq_comm]
  · intro w hw
    simp [show w ≠ v from fun h ↦ hw (h ▸ hv)]

omit [DecidableEq V] in
theorem sum_face_eq_one {s : Finset V} {x : V → ℝ}
    (hx : x ∈ barycentricFace s) : ∑ v ∈ s, x v = 1 := by
  rw [Finset.sum_subset (Finset.subset_univ s) (fun v _ hv ↦ hx.2.2 v hv)]
  exact hx.2.1

theorem sum_smul_single_eq_of_mem_barycentricFace {s : Finset V} {x : V → ℝ}
    (hx : x ∈ barycentricFace s) : (∑ v ∈ s, x v • Pi.single v (1 : ℝ)) = x := by
  ext w
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hw : w ∈ s
  · rw [Finset.sum_eq_single w]
    · simp
    · intro v _ hvw
      simp [Pi.single_eq_of_ne hvw.symm]
    · exact fun h ↦ (h hw).elim
  · rw [hx.2.2 w hw]
    exact Finset.sum_eq_zero fun v hv ↦ by
      simp [Pi.single_eq_of_ne (show w ≠ v from fun h ↦ hw (h ▸ hv))]

/-- A face in the barycentric model is exactly the convex hull of its
standard basis vertices. -/
theorem barycentricFace_eq_convexHull (s : Finset V) :
    barycentricFace s = convexHull ℝ ((fun v ↦ Pi.single v (1 : ℝ)) '' (s : Set V)) := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [← sum_smul_single_eq_of_mem_barycentricFace hx]
    exact (convex_convexHull ℝ _).sum_mem (fun v _ ↦ hx.1 v)
      (sum_face_eq_one hx) (fun v hv ↦ subset_convexHull ℝ _ ⟨v, hv, rfl⟩)
  · apply convexHull_min
    · rintro _ ⟨v, hv, rfl⟩
      exact single_mem_barycentricFace hv
    · exact barycentricFace_convex s

section Geometric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Evaluate barycentric coordinates at the specified geometric vertices. -/
def barycentricEvaluation (p : V → E) : (V → ℝ) →ₗ[ℝ] E where
  toFun x := ∑ v, x v • p v
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [mul_smul, Finset.smul_sum]

omit [DecidableEq V] in
theorem continuous_barycentricEvaluation (p : V → E) :
    Continuous (barycentricEvaluation p) := by
  change Continuous (fun x : V → ℝ ↦ ∑ v, x v • p v)
  fun_prop

@[simp]
theorem barycentricEvaluation_single (p : V → E) (v : V) :
    barycentricEvaluation p (Pi.single v (1 : ℝ)) = p v := by
  simp [barycentricEvaluation, Pi.single_apply, eq_comm]

omit [DecidableEq V] in
theorem barycentricEvaluation_face_image (p : V → E) (s : Finset V) :
    barycentricEvaluation p '' barycentricFace s = convexHull ℝ (p '' (s : Set V)) := by
  classical
  rw [barycentricFace_eq_convexHull, (barycentricEvaluation p).image_convexHull,
    Set.image_image]
  simp only [barycentricEvaluation_single]

/-- The union of the geometric simplices corresponding to the finite face family. -/
def geometricCarrier (K : Finset (Finset V)) (p : V → E) : Set E :=
  ⋃ s ∈ K, convexHull ℝ (p '' (s : Set V))

omit [DecidableEq V] in
theorem barycentricEvaluation_carrier_image (K : Finset (Finset V)) (p : V → E) :
    barycentricEvaluation p '' barycentricCarrier K = geometricCarrier K p := by
  simp only [barycentricCarrier_eq_union, geometricCarrier, Set.image_iUnion,
    barycentricEvaluation_face_image]

/-- Standard geometric simplicial-complex hypotheses. They assert only
independence and the intersection condition, not a topological conclusion. -/
structure IsGeometricRealization (K : Finset (Finset V)) (p : V → E) : Prop where
  independent : ∀ s ∈ K, AffineIndependent ℝ (fun v : s ↦ p v.val)
  intersection : ∀ s ∈ K, ∀ t ∈ K,
    convexHull ℝ (p '' (s : Set V)) ∩ convexHull ℝ (p '' (t : Set V)) ⊆
      convexHull ℝ (p '' ((s ∩ t : Finset V) : Set V))

omit [DecidableEq V] in
theorem barycentricEvaluation_eq_sum_face {s : Finset V} {x : V → ℝ}
    (hx : x ∈ barycentricFace s) (p : V → E) :
    barycentricEvaluation p x = ∑ v ∈ s, x v • p v := by
  exact (Finset.sum_subset (Finset.subset_univ s)
    (fun v _ hv ↦ by rw [hx.2.2 v hv, zero_smul])).symm

omit [DecidableEq V] in
/-- Affine independence gives uniqueness on each individual face. -/
theorem barycentricEvaluation_injOn_face (p : V → E) {s : Finset V}
    (hind : AffineIndependent ℝ (fun v : s ↦ p v.val)) :
    Set.InjOn (barycentricEvaluation p) (barycentricFace s) := by
  classical
  intro x hx y hy heq
  have hw : (∑ v : s, x v.val) = ∑ v : s, y v.val := by
    simpa only [Finset.sum_coe_sort] using (sum_face_eq_one hx).trans (sum_face_eq_one hy).symm
  have hwp : (∑ v : s, x v.val • p v.val) = ∑ v : s, y v.val • p v.val := by
    have h := (barycentricEvaluation_eq_sum_face hx p).symm.trans
      (heq.trans (barycentricEvaluation_eq_sum_face hy p))
    rw [← Finset.sum_attach s (fun v ↦ x v • p v),
      ← Finset.sum_attach s (fun v ↦ y v • p v)] at h
    exact h
  have hxy := hind.eq_of_sum_eq_sum hw hwp
  ext v
  by_cases hv : v ∈ s
  · exact hxy ⟨v, hv⟩ (Finset.mem_univ _)
  · rw [hx.2.2 v hv, hy.2.2 v hv]

/-- The gluing condition turns facewise uniqueness into global uniqueness. -/
theorem barycentricEvaluation_injOn_carrier {K : Finset (Finset V)} {p : V → E}
    (hgeom : IsGeometricRealization K p) :
    Set.InjOn (barycentricEvaluation p) (barycentricCarrier K) := by
  intro x hx y hy heq
  obtain ⟨s, hs, hxs⟩ := hx.2.2
  obtain ⟨t, ht, hyt⟩ := hy.2.2
  have hxface : x ∈ barycentricFace s := ⟨hx.1, hx.2.1, hxs⟩
  have hyface : y ∈ barycentricFace t := ⟨hy.1, hy.2.1, hyt⟩
  have hximage : barycentricEvaluation p x ∈ convexHull ℝ (p '' (s : Set V)) := by
    rw [← barycentricEvaluation_face_image]
    exact ⟨x, hxface, rfl⟩
  have hyimage : barycentricEvaluation p x ∈ convexHull ℝ (p '' (t : Set V)) := by
    rw [heq, ← barycentricEvaluation_face_image]
    exact ⟨y, hyface, rfl⟩
  have hinter := hgeom.intersection s hs t ht ⟨hximage, hyimage⟩
  rw [← barycentricEvaluation_face_image] at hinter
  obtain ⟨w, hw, hweq⟩ := hinter
  have hws := barycentricFace_mono Finset.inter_subset_left hw
  have hwt := barycentricFace_mono Finset.inter_subset_right hw
  exact ((barycentricEvaluation_injOn_face p (hgeom.independent s hs))
    hxface hws hweq.symm).trans
      ((barycentricEvaluation_injOn_face p (hgeom.independent t ht))
        hwt hyface (hweq.trans heq))

/-- The geometric realization map, with the actual target carrier. -/
def geometricRealizationMap (K : Finset (Finset V)) (p : V → E) :
    C(↥(barycentricCarrier K), ↥(geometricCarrier K p)) where
  toFun x := ⟨barycentricEvaluation p x.val,
    (barycentricEvaluation_carrier_image K p).subset ⟨x.val, x.property, rfl⟩⟩
  continuous_toFun :=
    ((continuous_barycentricEvaluation p).comp continuous_subtype_val).subtype_mk _

theorem geometricRealizationMap_bijective {K : Finset (Finset V)} {p : V → E}
    (hgeom : IsGeometricRealization K p) : Function.Bijective (geometricRealizationMap K p) := by
  constructor
  · intro x y heq
    exact Subtype.ext (barycentricEvaluation_injOn_carrier hgeom x.property y.property
      (congrArg Subtype.val heq))
  · intro z
    have hz := (barycentricEvaluation_carrier_image K p).superset z.property
    obtain ⟨x, hx, hxeq⟩ := hz
    exact ⟨⟨x, hx⟩, Subtype.ext hxeq⟩

/-- A finite geometric simplicial realization is homeomorphic to the
standard barycentric realization. Continuity of the inverse follows from
compactness and the Hausdorff property, not from a coordinate choice. -/
def geometricRealizationHomeomorph {K : Finset (Finset V)} {p : V → E}
    (hgeom : IsGeometricRealization K p) :
    barycentricCarrier K ≃ₜ geometricCarrier K p := by
  letI : CompactSpace (barycentricCarrier K) :=
    isCompact_iff_compactSpace.mp (barycentricCarrier_isCompact K)
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (geometricRealizationMap K p) (geometricRealizationMap_bijective hgeom))
    (geometricRealizationMap K p).continuous

@[simp]
theorem geometricRealizationHomeomorph_apply {K : Finset (Finset V)} {p : V → E}
    (hgeom : IsGeometricRealization K p) (x : barycentricCarrier K) :
    (geometricRealizationHomeomorph hgeom x).val = barycentricEvaluation p x.val := rfl

omit [Fintype V] in
theorem IsGeometricRealization.mono {K L : Finset (Finset V)} {p : V → E}
    (hgeom : IsGeometricRealization K p) (hLK : L ⊆ K) : IsGeometricRealization L p :=
  ⟨fun s hs ↦ hgeom.independent s (hLK hs),
    fun s hs t ht ↦ hgeom.intersection s (hLK hs) t (hLK ht)⟩

omit [Fintype V] in
theorem IsGeometricRealization.induced {K : Finset (Finset V)} {p : V → E}
    (hgeom : IsGeometricRealization K p) (G : Finset V) :
    IsGeometricRealization (inducedFaces K G) p :=
  hgeom.mono (fun _ hs ↦ (mem_inducedFaces.mp hs).1)

/-- The realization homeomorphism identifies every subfamily with its
geometric carrier, not merely the whole complex. -/
theorem evaluation_mem_subfamily_iff {K L : Finset (Finset V)} {p : V → E}
    (hgeom : IsGeometricRealization K p) (hLK : L ⊆ K)
    {x : V → ℝ} (hx : x ∈ barycentricCarrier K) :
    barycentricEvaluation p x ∈ geometricCarrier L p ↔ x ∈ barycentricCarrier L := by
  constructor
  · intro h
    obtain ⟨y, hy, hyeq⟩ := (barycentricEvaluation_carrier_image L p).superset h
    have hyx := barycentricEvaluation_injOn_carrier hgeom
      (barycentricCarrier_mono hLK hy) hx hyeq
    exact hyx ▸ hy
  · intro h
    exact (barycentricEvaluation_carrier_image L p).subset ⟨x, h, rfl⟩

/-- Flatten the subtype presentation of a set difference. -/
private def differenceSubtypeHomeomorph {X : Type*} [TopologicalSpace X] (s t : Set X) :
    ↥(s \ t) ≃ₜ {x : s // x.val ∉ t} where
  toFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  invFun x := ⟨x.val.val, x.val.property, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- The homeomorphism also identifies the literal complements of any
subfamily in the two realizations. -/
def geometricComplementHomeomorph {K L : Finset (Finset V)} {p : V → E}
    (hgeom : IsGeometricRealization K p) (hLK : L ⊆ K) :
    ↥(barycentricCarrier K \ barycentricCarrier L) ≃ₜ
      ↥(geometricCarrier K p \ geometricCarrier L p) :=
  (differenceSubtypeHomeomorph (barycentricCarrier K) (barycentricCarrier L)).trans
    (((geometricRealizationHomeomorph hgeom).subtype (fun x ↦
      (not_congr (evaluation_mem_subfamily_iff hgeom hLK x.property)).symm)).trans
        (differenceSubtypeHomeomorph (geometricCarrier K p) (geometricCarrier L p)).symm)

/-- The geometric version of the paper's induced-complement lemma:
the complement of the bad induced subcomplex is homotopy equivalent
to the good induced subcomplex. -/
def geometricInducedComplementHomotopyEquiv {K : Finset (Finset V)} {p : V → E}
    (hK : FaceClosed K) (hgeom : IsGeometricRealization K p) (G : Finset V) :
    ContinuousMap.HomotopyEquiv
      ↥(geometricCarrier K p \ geometricCarrier (inducedFaces K Gᶜ) p)
      ↥(geometricCarrier (inducedFaces K G) p) :=
  (geometricComplementHomeomorph hgeom
    (fun _ hs ↦ (mem_inducedFaces.mp hs).1)).symm.toHomotopyEquiv.trans
      ((inducedComplementHomotopyEquiv hK G).trans
        (geometricRealizationHomeomorph (hgeom.induced G)).toHomotopyEquiv)

omit [Fintype V] in
/-- A geometric complex from Mathlib supplies the realization hypotheses
for any injectively labelled finite collection of its faces. The empty
simplex is allowed in our augmented face-family convention. -/
theorem isGeometricRealization_of_simplicialComplex
    [DecidableEq E] (L : Geometry.SimplicialComplex ℝ E)
    {K : Finset (Finset V)} {p : V → E}
    (hp : Function.Injective p)
    (hfaces : ∀ s ∈ K, s.Nonempty → s.image p ∈ L.faces) :
    IsGeometricRealization K p := by
  classical
  constructor
  · intro s hs
    by_cases hse : s = ∅
    · subst s
      exact affineIndependent_of_subsingleton ℝ _
    · let e : s ↪ (s.image p) :=
        ⟨fun v ↦ ⟨p v.val, Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩⟩,
          fun u v h ↦ Subtype.ext (hp (congrArg Subtype.val h))⟩
      exact (L.indep (hfaces s hs (Finset.nonempty_iff_ne_empty.mpr hse))).comp_embedding e
  · intro s hs t ht
    by_cases hse : s = ∅
    · simp [hse]
    by_cases hte : t = ∅
    · simp [hte]
    have hi := L.inter_subset_convexHull
      (hfaces s hs (Finset.nonempty_iff_ne_empty.mpr hse))
      (hfaces t ht (Finset.nonempty_iff_ne_empty.mpr hte))
    simpa only [Finset.coe_image, Finset.coe_inter, Set.image_inter hp] using hi

end Geometric

end AffineTverberg.Simplicial
