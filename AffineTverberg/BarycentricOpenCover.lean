import AffineTverberg.BarycentricRealization
import AffineTverberg.SingularHomology
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

set_option linter.style.header false

/-!
# A finite good open cover of a barycentric realization

The vertex opens are given by strict positivity of the corresponding
barycentric coordinate. They cover the realization. Every nonempty finite
intersection is star-shaped around the barycenter of its vertex set, hence
contractible, and occurs exactly when that vertex set is a face.

These are the geometric hypotheses for a small-chain or good-cover homology
argument. No singular-chain descent, nerve theorem, or comparison is assumed.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg.Simplicial

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Uniform barycentric weights on a finite face. -/
def faceCenter (s : Finset V) : V → ℝ := fun v ↦ if v ∈ s then (s.card : ℝ)⁻¹ else 0

theorem faceCenter_mem_barycentricFace {s : Finset V} (hs : s.Nonempty) :
    faceCenter s ∈ barycentricFace s := by
  have hc : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hs)
  refine ⟨fun v ↦ by simp only [faceCenter]; split <;> positivity, ?_, ?_⟩
  · calc
      ∑ v, faceCenter s v = ∑ v ∈ s, faceCenter s v :=
        (Finset.sum_subset (Finset.subset_univ s) (fun v _ hv ↦ by simp [faceCenter, hv])).symm
      _ = ∑ _v ∈ s, (s.card : ℝ)⁻¹ :=
        Finset.sum_congr rfl fun v hv ↦ by simp [faceCenter, hv]
      _ = 1 := by simp only [Finset.sum_const, nsmul_eq_mul]; exact mul_inv_cancel₀ hc
  · intro v hv
    simp [faceCenter, hv]

omit [Fintype V] in
theorem faceCenter_pos {s : Finset V} {v : V} (hv : v ∈ s) : 0 < faceCenter s v := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr ⟨v, hv⟩
  simp only [faceCenter, hv, ite_true]
  exact inv_pos.mpr hc

/-- The intersection of the coordinate-positive vertex opens indexed by `s`. -/
def openStar (K : Finset (Finset V)) (s : Finset V) : Set ↥(barycentricCarrier K) :=
  {x | ∀ v ∈ s, 0 < x.val v}

omit [DecidableEq V] in
theorem isOpen_openStar (K : Finset (Finset V)) (s : Finset V) : IsOpen (openStar K s) := by
  have heq : openStar K s = ⋂ v ∈ s, {x : ↥(barycentricCarrier K) | 0 < x.val v} := by
    ext x
    simp [openStar]
  rw [heq]
  exact isOpen_biInter_finset fun v _ ↦ isOpen_lt continuous_const
    ((continuous_apply v).comp continuous_subtype_val)

omit [DecidableEq V] in
theorem openStar_eq_vertex_inter (K : Finset (Finset V)) (s : Finset V) :
    openStar K s = ⋂ v ∈ s, openStar K {v} := by
  ext x
  simp [openStar]

theorem openStar_union (K : Finset (Finset V)) (s t : Finset V) :
    openStar K (s ∪ t) = openStar K s ∩ openStar K t := by
  ext x
  simp only [openStar, mem_ofPred_eq, Finset.mem_union, mem_inter_iff]
  aesop

omit [DecidableEq V] in
/-- Every point belongs to at least one coordinate-positive vertex open. -/
theorem iUnion_openStar_singleton (K : Finset (Finset V)) :
    (⋃ v : V, openStar K {v}) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hpos : ∃ v, 0 < x.val v := by
    by_contra h
    push Not at h
    have hsum : ∑ v, x.val v ≤ 0 := Finset.sum_nonpos fun v _ ↦ h v
    rw [x.property.2.1] at hsum
    norm_num at hsum
  obtain ⟨v, hv⟩ := hpos
  exact mem_iUnion.mpr ⟨v, by simpa only [openStar, mem_ofPred_eq, Finset.mem_singleton,
    forall_eq] using hv⟩

omit [DecidableEq V] in
/-- Positivity on `s` forces any supporting simplex of a point to contain `s`. -/
theorem subset_support_of_openStar {K : Finset (Finset V)} {s t : Finset V}
    {x : ↥(barycentricCarrier K)} (hx : x ∈ openStar K s)
    (hsupp : ∀ v, v ∉ t → x.val v = 0) : s ⊆ t := by
  intro v hv
  by_contra hvt
  have hpos := hx v hv
  rw [hsupp v hvt] at hpos
  exact (lt_irrefl 0) hpos

omit [DecidableEq V] in
/-- Nonempty intersections are indexed exactly by nonempty faces. -/
theorem openStar_nonempty_iff {K : Finset (Finset V)} (hK : FaceClosed K)
    {s : Finset V} (hs : s.Nonempty) : (openStar K s).Nonempty ↔ s ∈ K := by
  classical
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨t, ht, hsupp⟩ := x.property.2.2
    exact hK t ht s (subset_support_of_openStar hx hsupp)
  · intro hsK
    have hc := faceCenter_mem_barycentricFace hs
    refine ⟨⟨faceCenter s, hc.1, hc.2.1, s, hsK, hc.2.2⟩, ?_⟩
    exact fun v hv ↦ faceCenter_pos hv

/-- The same open intersection as a subset of the ambient coordinate space. -/
def ambientOpenStar (K : Finset (Finset V)) (s : Finset V) : Set (V → ℝ) :=
  {x | x ∈ barycentricCarrier K ∧ ∀ v ∈ s, 0 < x v}

def openStarHomeomorph (K : Finset (Finset V)) (s : Finset V) :
    openStar K s ≃ₜ ambientOpenStar K s where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- A finite open intersection is star-shaped, even though the entire
realization need not be convex. Each point and the center lie in a common face. -/
theorem starConvex_ambientOpenStar (K : Finset (Finset V)) {s : Finset V}
    (hs : s.Nonempty) : StarConvex ℝ (faceCenter s) (ambientOpenStar K s) := by
  rintro y ⟨hy, hpos⟩ a b ha hb hab
  obtain ⟨t, ht, hysupp⟩ := hy.2.2
  have hst : s ⊆ t := subset_support_of_openStar (x := ⟨y, hy⟩) hpos hysupp
  have hcenter : faceCenter s ∈ barycentricFace t :=
    barycentricFace_mono hst (faceCenter_mem_barycentricFace hs)
  have hpoint : y ∈ barycentricFace t := ⟨hy.1, hy.2.1, hysupp⟩
  have hcomb := barycentricFace_convex t hcenter hpoint ha hb hab
  refine ⟨⟨hcomb.1, hcomb.2.1, t, ht, hcomb.2.2⟩, ?_⟩
  intro v hv
  change 0 < a * faceCenter s v + b * y v
  have hc := faceCenter_pos hv
  have hyp := hpos v hv
  rcases eq_or_lt_of_le ha with hzero | hapos
  · have ha0 : a = 0 := hzero.symm
    have hb1 : b = 1 := by linarith
    simpa only [ha0, hb1, zero_mul, one_mul, zero_add] using hyp
  · exact add_pos_of_pos_of_nonneg (mul_pos hapos hc) (mul_nonneg hb hyp.le)

omit [DecidableEq V] in
/-- Every nonempty finite intersection of vertex opens is contractible. -/
theorem contractibleSpace_openStar {K : Finset (Finset V)} {s : Finset V}
    (hs : s.Nonempty) (hsK : s ∈ K) : ContractibleSpace ↥(openStar K s) := by
  classical
  have hc := faceCenter_mem_barycentricFace hs
  have hcenter : faceCenter s ∈ ambientOpenStar K s :=
    ⟨⟨hc.1, hc.2.1, s, hsK, hc.2.2⟩, fun v hv ↦ faceCenter_pos hv⟩
  have : ContractibleSpace ↥(ambientOpenStar K s) :=
    (starConvex_ambientOpenStar K hs).contractibleSpace ⟨_, hcenter⟩
  exact (openStarHomeomorph K s).contractibleSpace

omit [DecidableEq V] in
/-- A uniform radius makes every sufficiently small piece of a compact
parameter space map into one vertex open. This is the geometric smallness
input for subdividing singular simplices. -/
theorem exists_lebesgue_radius_openStar {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {K : Finset (Finset V)} (f : C(X, ↥(barycentricCarrier K))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : X, ∃ v : V, Metric.ball x ε ⊆ f ⁻¹' openStar K {v} := by
  have hc : (univ : Set X) ⊆ ⋃ v, f ⁻¹' openStar K {v} := by
    intro x _
    have hx : f x ∈ ⋃ v, openStar K {v} := by rw [iUnion_openStar_singleton]; trivial
    obtain ⟨v, hv⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨v, hv⟩
  obtain ⟨ε, hε, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun v ↦ (isOpen_openStar K {v}).preimage f.continuous) hc
  exact ⟨ε, hε, fun x ↦ hball x (mem_univ x)⟩

section SingularHomology

variable {U : Type} [Fintype U]

/-- Actual singular acyclicity of each nonempty open intersection, including
the augmentation endpoint needed in a good-cover comparison. -/
theorem openStar_singularAcyclic {K : Finset (Finset U)} {s : Finset U}
    (hs : s.Nonempty) (hsK : s ∈ K) :
    CategoryTheory.IsIso (realSingularAugmentation (TopCat.of ↥(openStar K s))) ∧
      ∀ k, k ≠ 0 → Subsingleton ((realSingularHomology k).obj (TopCat.of ↥(openStar K s))) := by
  have := contractibleSpace_openStar hs hsK
  exact realSingularHomology_contractible ↥(openStar K s)

end SingularHomology

end AffineTverberg.Simplicial
