import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

set_option linter.style.header false

/-!
# The simplicial fibers in Lemma Y

This file formalizes the combinatorial fiber appearing in the simplicial-ball
case of `lemma:Y` in `affine-tverberg17.tex`.  For each vertex `v`, the allowed
copies are the factors on which the functional is nonnegative.  The diagonal
sum relation makes every such color set nonempty, and the whole fiber is the
join complex consisting of partial choices of one allowed color per vertex.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace AffineTverberg

section NonnegativeFactor

variable {I : Type*} [Fintype I] [Nonempty I]

/-- If finitely many real numbers sum to zero, at least one is nonnegative. -/
theorem exists_nonnegative_of_sum_eq_zero (a : I → ℝ) (hsum : ∑ i, a i = 0) :
    ∃ i, 0 ≤ a i := by
  by_contra h
  push Not at h
  have hneg : ∑ i, a i < ∑ _i : I, (0 : ℝ) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ ↦ h i
  rw [hsum] at hneg
  simp at hneg

/-- The allowed factor copies of a vertex: precisely those where the
functional is nonnegative. -/
abbrev NonnegativeColor (a : I → ℝ) := {i : I // 0 ≤ a i}

/-- The diagonal relation makes the allowed color set nonempty. -/
theorem nonempty_nonnegativeColor (a : I → ℝ) (hsum : ∑ i, a i = 0) :
    Nonempty (NonnegativeColor a) := by
  obtain ⟨i, hi⟩ := exists_nonnegative_of_sum_eq_zero a hsum
  exact ⟨⟨i, hi⟩⟩

end NonnegativeFactor

section JoinComplex

variable {V I : Type*} [Fintype I] [Nonempty I]
  (σ : Finset V) (evalFn : V → I → ℝ)

/-- A colored vertex consists of a vertex of `σ` and an allowed
nonnegative factor for it. -/
abbrev NonnegativeColoredVertex :=
  Σ v : {v // v ∈ σ}, NonnegativeColor (evalFn v)

/-- A set of colored vertices is a join face when it uses each underlying
vertex at most once. -/
def IsColorChoiceFace (s : Finset (NonnegativeColoredVertex σ evalFn)) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, a.1 = b.1 → a = b

/-- The abstract simplicial complex
`W_{v₁}(y) * ⋯ * W_{v_N}(y)` from the paper. -/
def nonnegativeJoinComplex :
    AbstractSimplicialComplex (NonnegativeColoredVertex σ evalFn) where
  faces := {s | s.Nonempty ∧ IsColorChoiceFace σ evalFn s}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    refine ⟨ht, ?_⟩
    intro a ha b hb hab
    exact hs.2 a (hts ha) b (hts hb) hab
  singleton_mem := by
    intro v
    refine ⟨Finset.singleton_nonempty v, ?_⟩
    intro a ha b hb _hab
    exact (Finset.mem_singleton.mp ha).trans (Finset.mem_singleton.mp hb).symm

omit [Fintype I] [Nonempty I] in
@[simp]
theorem mem_nonnegativeJoinComplex_iff
    (s : Finset (NonnegativeColoredVertex σ evalFn)) :
    s ∈ nonnegativeJoinComplex σ evalFn ↔
      s.Nonempty ∧ IsColorChoiceFace σ evalFn s :=
  Iff.rfl

omit [Fintype I] [Nonempty I] in
/-- Every face of the join contains at most one vertex over each vertex of
`σ`, hence has at most `σ.card` vertices. -/
theorem nonnegativeJoinComplex_face_card_le
    {s : Finset (NonnegativeColoredVertex σ evalFn)}
    (hs : s ∈ nonnegativeJoinComplex σ evalFn) :
    s.card ≤ σ.card := by
  classical
  have hinj : Set.InjOn (fun a : NonnegativeColoredVertex σ evalFn ↦ a.1) s := by
    intro a ha b hb hab
    exact hs.2 a ha b hb hab
  calc
    s.card ≤ (Finset.univ : Finset {v // v ∈ σ}).card :=
      Finset.card_le_card_of_injOn (fun a : NonnegativeColoredVertex σ evalFn ↦ a.1)
        (by simp [Set.MapsTo]) hinj
    _ = σ.card := by simp

variable (hdiag : ∀ v ∈ σ, ∑ i, evalFn v i = 0)

include hdiag

/-- A chosen allowed factor for every vertex, available because of the
diagonal relation. -/
noncomputable def chosenNonnegativeColor (v : {v // v ∈ σ}) :
    NonnegativeColor (evalFn v) :=
  Classical.choice (nonempty_nonnegativeColor (evalFn v) (hdiag v v.2))

/-- The corresponding colored copy of `v`. -/
noncomputable def chosenColoredVertex (v : {v // v ∈ σ}) :
    NonnegativeColoredVertex σ evalFn :=
  ⟨v, chosenNonnegativeColor σ evalFn hdiag v⟩

theorem chosenColoredVertex_injective :
    Function.Injective (chosenColoredVertex σ evalFn hdiag) := by
  intro v w h
  exact congrArg Sigma.fst h

/-- Choosing one allowed color at every vertex gives a full join face. -/
noncomputable def chosenFullJoinFace :
    Finset (NonnegativeColoredVertex σ evalFn) :=
  by
    classical
    exact Finset.univ.image (chosenColoredVertex σ evalFn hdiag)

/-- The chosen full face contains exactly one colored copy of every vertex. -/
theorem chosenFullJoinFace_card :
    (chosenFullJoinFace σ evalFn hdiag).card = σ.card := by
  classical
  rw [chosenFullJoinFace, Finset.card_image_of_injective _
    (chosenColoredVertex_injective σ evalFn hdiag)]
  simp

/-- If `σ` is nonempty, the chosen full set is a face of the join complex. -/
theorem chosenFullJoinFace_mem (hσ : σ.Nonempty) :
    chosenFullJoinFace σ evalFn hdiag ∈ nonnegativeJoinComplex σ evalFn := by
  classical
  constructor
  · obtain ⟨v, hv⟩ := hσ
    refine ⟨chosenColoredVertex σ evalFn hdiag ⟨v, hv⟩, ?_⟩
    simp [chosenFullJoinFace]
  · intro a ha b hb hab
    rw [chosenFullJoinFace, Finset.mem_image] at ha hb
    obtain ⟨va, _hva, rfl⟩ := ha
    obtain ⟨vb, _hvb, rfl⟩ := hb
    have hv : va = vb := hab
    subst vb
    rfl

/-- A join face covers the base when it contains a colored copy of every
vertex of `σ`. -/
def CoversBaseVertices (s : Finset (NonnegativeColoredVertex σ evalFn)) : Prop :=
  ∀ v : {v // v ∈ σ}, ∃ w ∈ s, w.1 = v

/-- Maximality among the faces of the nonnegative join complex. -/
def IsMaximalNonnegativeJoinFace
    (s : Finset (NonnegativeColoredVertex σ evalFn)) : Prop :=
  s ∈ nonnegativeJoinComplex σ evalFn ∧
    ∀ t, t ∈ nonnegativeJoinComplex σ evalFn → s ⊆ t → t = s

omit [Fintype I] [Nonempty I] hdiag in
/-- A face which covers every base vertex has exactly `σ.card` vertices. -/
theorem face_card_eq_of_coversBaseVertices
    {s : Finset (NonnegativeColoredVertex σ evalFn)}
    (hs : s ∈ nonnegativeJoinComplex σ evalFn)
    (hcover : CoversBaseVertices σ evalFn s) :
    s.card = σ.card := by
  classical
  have hinj : Set.InjOn (fun a : NonnegativeColoredVertex σ evalFn ↦ a.1) s := by
    intro a ha b hb hab
    exact hs.2 a ha b hb hab
  have himage : s.image (fun a : NonnegativeColoredVertex σ evalFn ↦ a.1) =
      (Finset.univ : Finset {v // v ∈ σ}) := by
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, iff_true]
    obtain ⟨w, hw, hwv⟩ := hcover v
    exact ⟨w, hw, hwv⟩
  calc
    s.card = (s.image (fun a : NonnegativeColoredVertex σ evalFn ↦ a.1)).card :=
      ((Finset.card_image_iff.mpr hinj).symm)
    _ = (Finset.univ : Finset {v // v ∈ σ}).card := congrArg Finset.card himage
    _ = σ.card := by simp

omit [Fintype I] [Nonempty I] hdiag in
/-- A face covering every base vertex is maximal. -/
theorem maximal_of_coversBaseVertices
    {s : Finset (NonnegativeColoredVertex σ evalFn)}
    (hs : s ∈ nonnegativeJoinComplex σ evalFn)
    (hcover : CoversBaseVertices σ evalFn s) :
    IsMaximalNonnegativeJoinFace σ evalFn s := by
  refine ⟨hs, ?_⟩
  intro t ht hst
  apply Finset.Subset.antisymm
  · intro w hw
    obtain ⟨a, ha, haw⟩ := hcover w.1
    have hwa : w = a := ht.2 w hw a (hst ha) haw.symm
    simpa [hwa] using ha
  · exact hst

/-- A maximal join face must contain a colored copy of every base vertex. -/
theorem maximalFace_coversBaseVertices
    {s : Finset (NonnegativeColoredVertex σ evalFn)}
    (hmax : IsMaximalNonnegativeJoinFace σ evalFn s) :
    CoversBaseVertices σ evalFn s := by
  classical
  intro v
  by_contra hmissing
  push Not at hmissing
  let w : NonnegativeColoredVertex σ evalFn :=
    chosenColoredVertex σ evalFn hdiag v
  have hwbase : w.1 = v := rfl
  have hwmem : w ∉ s := by
    intro hw
    exact (hmissing w hw) hwbase
  have hinsert : insert w s ∈ nonnegativeJoinComplex σ evalFn := by
    constructor
    · exact ⟨w, Finset.mem_insert_self w s⟩
    · intro a ha b hb hab
      simp only [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · rfl
      · exact False.elim <| (hmissing b hb) <| by simpa [hwbase] using hab.symm
      · exact False.elim <| (hmissing a ha) <| by simpa [hwbase] using hab
      · exact hmax.1.2 a ha b hb hab
  have heq : insert w s = s :=
    hmax.2 (insert w s) hinsert (Finset.subset_insert w s)
  exact hwmem (by rw [← heq]; exact Finset.mem_insert_self w s)

/-- All maximal faces of the simplicial fiber contain exactly one allowed
copy of each vertex, so the complex is pure of face-cardinality `σ.card`. -/
theorem maximalNonnegativeJoinFace_card
    {s : Finset (NonnegativeColoredVertex σ evalFn)}
    (hmax : IsMaximalNonnegativeJoinFace σ evalFn s) :
    s.card = σ.card :=
  face_card_eq_of_coversBaseVertices σ evalFn hmax.1
    (maximalFace_coversBaseVertices σ evalFn hdiag hmax)

/-- The explicitly chosen full face is maximal. -/
theorem chosenFullJoinFace_maximal (hσ : σ.Nonempty) :
    IsMaximalNonnegativeJoinFace σ evalFn (chosenFullJoinFace σ evalFn hdiag) := by
  apply maximal_of_coversBaseVertices σ evalFn
    (chosenFullJoinFace_mem σ evalFn hdiag hσ)
  intro v
  exact ⟨chosenColoredVertex σ evalFn hdiag v, by
    simp [chosenFullJoinFace], rfl⟩

end JoinComplex

end AffineTverberg
