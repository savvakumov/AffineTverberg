import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

set_option linter.style.header false

/-!
# The bad-edge-midpoint subdivision: combinatorics

This file constructs, purely combinatorially, the subdivision of a join complex
used in the affine Tverberg argument, and proves its structural properties.

## Setting

The vertices of the join complex form a type `W` equipped with a linear order
(the *fixed order of join vertices*) and a map `orig : W → V` recording which
*original* vertex each join vertex is a copy of.  A **bad pair** in a face
`S : Finset W` is a pair of distinct elements of `S` with the same original
vertex; in the join `Q = P^{*r}` these are exactly the *bad edges*, i.e. the
edges joining two copies of the same original vertex.  A face is **deleted**
when it contains no bad pair, i.e. `orig` is injective on it.

## The construction

`apexSet orig S` is the apex chosen for the face `S`:

* if `S` is deleted, the singleton consisting of the earliest vertex of `S`;
* otherwise the earliest bad pair of `S` (first minimizing the smaller endpoint,
  then the larger one).

Vertices of the subdivision are therefore *subsets of `W` of size one or two*;
geometrically a singleton `{u}` is the original vertex `u` and a bad pair
`{u, w}` is the midpoint of the corresponding bad edge.  The subdivision of `S`
is defined by recursion on `#S`:

`sdFaces S = B ∪ B.image (insert (apexSet orig S))`,
`B = ⋃ (u ∈ apexSet orig S), sdFaces (S.erase u)`,

that is, the boundary faces of `S` *not* containing the apex are subdivided
recursively and coned from the apex.

## Main results

* `sdFaces_faceClosed`, `sdFaces_mono` (compatibility across faces),
  `sdFaces_vertex_subset`, `sdFaces_card_le`;
* `sdFaces_filter_notMem` : the subcomplex of `sdFaces S` on the vertices
  avoiding a given join vertex `u` is exactly `sdFaces (S.erase u)`;
* `sdFaces_of_isDeletedFace` : a deleted face is not subdivided at all;
* `sdFaces_filter_good` : the *good* induced subcomplex of `sdFaces S`
  (all vertices singletons) is exactly the deleted join inside `S`;
* `card_image_orig_le_card_good` : every top-dimensional simplex of the
  subdivision of `S` has at least `m(S) + 1` good vertices, where `m(S) + 1` is
  the number of distinct original vertices occurring in `S`.
-/

open scoped BigOperators

namespace AffineTverberg
namespace BadEdge

variable {W V : Type*} [DecidableEq W] [LinearOrder W] [DecidableEq V]

/-! ### Deleted faces and bad pairs -/

/-- `S` is a deleted face: no two of its elements are copies of the same
original vertex. -/
def IsDeletedFace (orig : W → V) (S : Finset W) : Prop :=
  ∀ u ∈ S, ∀ w ∈ S, orig u = orig w → u = w

instance (orig : W → V) (S : Finset W) : Decidable (IsDeletedFace orig S) := by
  unfold IsDeletedFace; infer_instance

omit [DecidableEq W] [LinearOrder W] [DecidableEq V] in
theorem IsDeletedFace.mono {orig : W → V} {S T : Finset W}
    (hS : IsDeletedFace orig S) (hTS : T ⊆ S) : IsDeletedFace orig T :=
  fun u hu w hw h ↦ hS u (hTS hu) w (hTS hw) h

/-- The elements of `S` belonging to some bad pair of `S`. -/
def badElts (orig : W → V) (S : Finset W) : Finset W :=
  S.filter fun u ↦ ∃ w ∈ S, w ≠ u ∧ orig w = orig u

omit [LinearOrder W] in
theorem mem_badElts {orig : W → V} {S : Finset W} {u : W} :
    u ∈ badElts orig S ↔ u ∈ S ∧ ∃ w ∈ S, w ≠ u ∧ orig w = orig u := by
  simp [badElts]

omit [LinearOrder W] in
theorem badElts_subset (orig : W → V) (S : Finset W) : badElts orig S ⊆ S :=
  Finset.filter_subset _ _

omit [LinearOrder W] in
theorem badElts_mono {orig : W → V} {S T : Finset W} (hTS : T ⊆ S) :
    badElts orig T ⊆ badElts orig S := by
  intro u hu
  rw [mem_badElts] at hu ⊢
  obtain ⟨huT, w, hwT, hwu, hwo⟩ := hu
  exact ⟨hTS huT, w, hTS hwT, hwu, hwo⟩

omit [LinearOrder W] in
theorem badElts_eq_empty_iff {orig : W → V} {S : Finset W} :
    badElts orig S = ∅ ↔ IsDeletedFace orig S := by
  constructor
  · intro h u hu w hw huw
    by_contra hne
    have : w ∈ badElts orig S := mem_badElts.mpr ⟨hw, u, hu, hne, huw⟩
    simp [h] at this
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    obtain ⟨huS, w, hwS, hwu, hwo⟩ := mem_badElts.mp hu
    exact hwu (h w hwS u huS hwo)

/-- The elements of `S` forming a bad pair with the given vertex `u`. -/
def apexPartner (orig : W → V) (S : Finset W) (u : W) : Finset W :=
  S.filter fun w ↦ w ≠ u ∧ orig w = orig u

omit [LinearOrder W] in
theorem mem_apexPartner {orig : W → V} {S : Finset W} {u w : W} :
    w ∈ apexPartner orig S u ↔ w ∈ S ∧ w ≠ u ∧ orig w = orig u := by
  simp [apexPartner]

omit [LinearOrder W] in
theorem apexPartner_mono {orig : W → V} {S T : Finset W} (hTS : T ⊆ S) (u : W) :
    apexPartner orig T u ⊆ apexPartner orig S u := by
  intro w hw
  rw [mem_apexPartner] at hw ⊢
  exact ⟨hTS hw.1, hw.2⟩

omit [LinearOrder W] in
theorem apexPartner_nonempty {orig : W → V} {S : Finset W} {u : W}
    (hu : u ∈ badElts orig S) : (apexPartner orig S u).Nonempty := by
  obtain ⟨-, w, hwS, hwu, hwo⟩ := mem_badElts.mp hu
  exact ⟨w, mem_apexPartner.mpr ⟨hwS, hwu, hwo⟩⟩

/-! ### The chosen apex -/

/-- The apex chosen to subdivide the face `S`: the earliest bad pair if `S` is
not deleted, and otherwise the singleton of the earliest vertex of `S`. -/
def apexSet (orig : W → V) (S : Finset W) : Finset W :=
  if h : (badElts orig S).Nonempty then
    insert ((badElts orig S).min' h)
      {(apexPartner orig S ((badElts orig S).min' h)).min'
        (apexPartner_nonempty (Finset.min'_mem _ h))}
  else if hS : S.Nonempty then {S.min' hS} else ∅

theorem apexSet_of_bad {orig : W → V} {S : Finset W} (h : (badElts orig S).Nonempty) :
    apexSet orig S =
      insert ((badElts orig S).min' h)
        {(apexPartner orig S ((badElts orig S).min' h)).min'
          (apexPartner_nonempty (Finset.min'_mem _ h))} := by
  rw [apexSet, dite_eq_left h]

theorem apexSet_of_deleted {orig : W → V} {S : Finset W}
    (h : badElts orig S = ∅) (hS : S.Nonempty) :
    apexSet orig S = {S.min' hS} := by
  have h' : ¬ (badElts orig S).Nonempty := by simp [h]
  rw [apexSet, dite_eq_right h', dite_eq_left hS]

theorem apexSet_empty (orig : W → V) : apexSet orig (∅ : Finset W) = ∅ := by
  have h : ¬ ((badElts orig (∅ : Finset W)).Nonempty) := by
    simp [badElts]
  rw [apexSet, dite_eq_right h, dite_eq_right (by simp)]

theorem apexSet_subset (orig : W → V) (S : Finset W) : apexSet orig S ⊆ S := by
  by_cases h : (badElts orig S).Nonempty
  · rw [apexSet_of_bad h]
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact badElts_subset orig S (Finset.min'_mem _ h)
    · rw [Finset.mem_singleton] at hx
      subst hx
      exact (mem_apexPartner.mp (Finset.min'_mem _ (apexPartner_nonempty
        (Finset.min'_mem _ h)))).1
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    rcases S.eq_empty_or_nonempty with rfl | hS
    · simp [apexSet_empty]
    · rw [apexSet_of_deleted h hS]
      simpa using Finset.min'_mem _ hS

theorem apexSet_nonempty {orig : W → V} {S : Finset W} (hS : S.Nonempty) :
    (apexSet orig S).Nonempty := by
  by_cases h : (badElts orig S).Nonempty
  · rw [apexSet_of_bad h]; exact Finset.insert_nonempty _ _
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [apexSet_of_deleted h hS]
    exact Finset.singleton_nonempty _

theorem apexSet_card_eq_one {orig : W → V} {S : Finset W}
    (h : badElts orig S = ∅) (hS : S.Nonempty) : (apexSet orig S).card = 1 := by
  rw [apexSet_of_deleted h hS]; simp

/-- Recognition lemma for the apex in the non-deleted case: it is the pair
formed by the earliest bad vertex and its earliest partner. -/
theorem apexSet_eq_pair_of_minimal {orig : W → V} {S : Finset W} {u w : W}
    (hu : u ∈ badElts orig S) (hw : w ∈ apexPartner orig S u)
    (hu_min : ∀ x ∈ badElts orig S, u ≤ x)
    (hw_min : ∀ x ∈ apexPartner orig S u, w ≤ x) :
    apexSet orig S = {u, w} := by
  have hbad : (badElts orig S).Nonempty := ⟨u, hu⟩
  rw [apexSet_of_bad hbad]
  have hm : (badElts orig S).min' hbad = u :=
    le_antisymm (Finset.min'_le _ _ hu) (hu_min _ (Finset.min'_mem _ hbad))
  have hpart : apexPartner orig S ((badElts orig S).min' hbad) = apexPartner orig S u := by
    rw [hm]
  have hp : (apexPartner orig S ((badElts orig S).min' hbad)).min'
      (apexPartner_nonempty (Finset.min'_mem _ hbad)) = w := by
    refine le_antisymm (Finset.min'_le _ _ (by rw [hpart]; exact hw)) ?_
    refine hw_min _ ?_
    rw [← hpart]
    exact Finset.min'_mem _ (apexPartner_nonempty (Finset.min'_mem _ hbad))
  rw [hp, hm]

/-- The data of the apex in the non-deleted case. -/
theorem exists_apexSet_pair {orig : W → V} {S : Finset W}
    (h : (badElts orig S).Nonempty) :
    ∃ u w : W, apexSet orig S = {u, w} ∧ u ≠ w ∧ orig u = orig w ∧ u ∈ S ∧ w ∈ S := by
  refine ⟨(badElts orig S).min' h,
    (apexPartner orig S ((badElts orig S).min' h)).min'
      (apexPartner_nonempty (Finset.min'_mem _ h)), apexSet_of_bad h, ?_⟩
  obtain ⟨hwS, hwu, hwo⟩ := mem_apexPartner.mp (Finset.min'_mem _
      (apexPartner_nonempty (Finset.min'_mem _ h)))
  exact ⟨fun hcontra ↦ hwu hcontra.symm, hwo.symm,
    badElts_subset orig S (Finset.min'_mem _ h), hwS⟩

/-- In the non-deleted case the apex is a genuine bad pair. -/
theorem apexSet_card_eq_two {orig : W → V} {S : Finset W}
    (h : (badElts orig S).Nonempty) : (apexSet orig S).card = 2 := by
  obtain ⟨u, w, hpair, huw, -, -, -⟩ := exists_apexSet_pair h
  rw [hpair, Finset.card_insert_of_notMem (by simpa using huw), Finset.card_singleton]

theorem apexSet_not_isDeletedFace {orig : W → V} {S : Finset W}
    (h : (badElts orig S).Nonempty) : ¬ IsDeletedFace orig (apexSet orig S) := by
  obtain ⟨u, w, hpair, huw, horig, -, -⟩ := exists_apexSet_pair h
  intro hdel
  exact huw (hdel u (by rw [hpair]; simp) w (by rw [hpair]; simp) horig)

/-- If `S` is deleted, so is its apex. -/
theorem apexSet_isDeletedFace {orig : W → V} {S : Finset W}
    (h : IsDeletedFace orig S) : IsDeletedFace orig (apexSet orig S) :=
  h.mono (apexSet_subset orig S)

/-- **The fixed ordering makes the apex hereditary**: if a subface `T` of `S`
still contains the apex of `S`, then it has the same apex.  This is the source
of the compatibility of the subdivisions across faces. -/
theorem apexSet_mono {orig : W → V} {S T : Finset W} (hTS : T ⊆ S)
    (hT : T.Nonempty) (ha : apexSet orig S ⊆ T) :
    apexSet orig T = apexSet orig S := by
  by_cases h : (badElts orig S).Nonempty
  · set u := (badElts orig S).min' h with hu_def
    set w := (apexPartner orig S u).min' (apexPartner_nonempty (Finset.min'_mem _ h)) with hw_def
    have hSa : apexSet orig S = insert u {w} := apexSet_of_bad h
    have huT : u ∈ T := ha (by rw [hSa]; simp)
    have hwT : w ∈ T := ha (by rw [hSa]; simp)
    have hw : w ∈ apexPartner orig S u :=
      Finset.min'_mem _ (apexPartner_nonempty (Finset.min'_mem _ h))
    obtain ⟨-, hwu, hwo⟩ := mem_apexPartner.mp hw
    have huTbad : u ∈ badElts orig T := mem_badElts.mpr ⟨huT, w, hwT, hwu, hwo⟩
    have hwTp : w ∈ apexPartner orig T u := mem_apexPartner.mpr ⟨hwT, hwu, hwo⟩
    rw [apexSet_eq_pair_of_minimal huTbad hwTp
      (fun x hx ↦ by
        rw [hu_def]; exact Finset.min'_le _ _ (badElts_mono hTS hx))
      (fun x hx ↦ by
        rw [hw_def]; exact Finset.min'_le _ _ (apexPartner_mono hTS u hx)), hSa]
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    have hdelS : IsDeletedFace orig S := badElts_eq_empty_iff.mp h
    have hdelT : badElts orig T = ∅ := badElts_eq_empty_iff.mpr (hdelS.mono hTS)
    have hS : S.Nonempty := hT.mono hTS
    have hminT : T.min' hT = S.min' hS := by
      have hmem : S.min' hS ∈ T := by
        have := apexSet_of_deleted h hS
        have : S.min' hS ∈ apexSet orig S := by rw [this]; simp
        exact ha this
      refine le_antisymm (Finset.min'_le _ _ hmem) ?_
      exact Finset.min'_le _ _ (hTS (Finset.min'_mem _ hT))
    rw [apexSet_of_deleted hdelT hT, apexSet_of_deleted h hS, hminT]

/-! ### The subdivision -/

/-- The simplices of the bad-edge subdivision of the face `S`.  A vertex of the
subdivision is a singleton `{u}` (an original join vertex) or a bad pair
`{u, w}` (the midpoint of a bad edge).  Boundary faces of `S` not containing
the apex are subdivided recursively and coned from the apex. -/
def sdFaces (orig : W → V) (S : Finset W) : Finset (Finset (Finset W)) :=
  if hS : S.Nonempty then
    let B : Finset (Finset (Finset W)) :=
      (apexSet orig S).attach.biUnion fun u ↦ sdFaces orig (S.erase u.1)
    B ∪ B.image (insert (apexSet orig S))
  else {∅}
  termination_by S.card
  decreasing_by exact Finset.card_erase_lt_of_mem (apexSet_subset orig S u.2)

/-- The subdivided boundary of `S`: the union of the subdivisions of the facets
of `S` opposite to the vertices of the apex. -/
def sdBase (orig : W → V) (S : Finset W) : Finset (Finset (Finset W)) :=
  (apexSet orig S).attach.biUnion fun u ↦ sdFaces orig (S.erase u.1)

theorem mem_sdBase {orig : W → V} {S : Finset W} {σ : Finset (Finset W)} :
    σ ∈ sdBase orig S ↔ ∃ u ∈ apexSet orig S, σ ∈ sdFaces orig (S.erase u) := by
  simp [sdBase]

theorem sdFaces_eq_union {orig : W → V} {S : Finset W} (hS : S.Nonempty) :
    sdFaces orig S = sdBase orig S ∪ (sdBase orig S).image (insert (apexSet orig S)) := by
  rw [sdFaces]
  simp only [hS, ↓reduceDIte]
  rfl

theorem sdFaces_empty (orig : W → V) : sdFaces orig (∅ : Finset W) = {∅} := by
  rw [sdFaces]
  simp

theorem mem_sdFaces_iff {orig : W → V} {S : Finset W} (hS : S.Nonempty)
    {σ : Finset (Finset W)} :
    σ ∈ sdFaces orig S ↔
      σ ∈ sdBase orig S ∨ ∃ τ ∈ sdBase orig S, insert (apexSet orig S) τ = σ := by
  rw [sdFaces_eq_union hS]
  simp [Finset.mem_union, Finset.mem_image]

/-! ### Basic structure of the subdivision -/

theorem empty_mem_sdFaces (orig : W → V) (S : Finset W) : ∅ ∈ sdFaces orig S := by
  induction S using Finset.strongInduction with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS
    · simp [sdFaces_empty]
    · obtain ⟨u, hu⟩ := apexSet_nonempty (orig := orig) hS
      have hlt : S.erase u ⊂ S := Finset.erase_ssubset (apexSet_subset orig S hu)
      rw [mem_sdFaces_iff hS]
      exact Or.inl (mem_sdBase.mpr ⟨u, hu, ih _ hlt⟩)

/-- Every vertex of a simplex of the subdivision of `S` is a nonempty subset of
`S` with at most two elements: an original vertex or a bad-edge midpoint. -/
theorem sdFaces_vertex (orig : W → V) (S : Finset W) {σ : Finset (Finset W)}
    (hσ : σ ∈ sdFaces orig S) :
    ∀ s ∈ σ, s.Nonempty ∧ s ⊆ S ∧ s.card ≤ 2 := by
  induction S using Finset.strongInduction generalizing σ with
  | _ S ih =>
    intro s hs
    rcases S.eq_empty_or_nonempty with rfl | hS
    · rw [sdFaces_empty] at hσ
      simp only [Finset.mem_singleton] at hσ
      subst hσ
      simp at hs
    · have hcard : (apexSet orig S).card ≤ 2 := by
        by_cases hb : (badElts orig S).Nonempty
        · exact le_of_eq (apexSet_card_eq_two hb)
        · rw [Finset.not_nonempty_iff_eq_empty] at hb
          exact le_of_eq_of_le (apexSet_card_eq_one hb hS) one_le_two
      have hbase : ∀ τ ∈ sdBase orig S, ∀ t ∈ τ, t.Nonempty ∧ t ⊆ S ∧ t.card ≤ 2 := by
        intro τ hτ t ht
        obtain ⟨u, hu, hτu⟩ := mem_sdBase.mp hτ
        have hlt : S.erase u ⊂ S := Finset.erase_ssubset (apexSet_subset orig S hu)
        obtain ⟨h1, h2, h3⟩ := ih _ hlt hτu t ht
        exact ⟨h1, h2.trans (Finset.erase_subset _ _), h3⟩
      rcases (mem_sdFaces_iff hS).mp hσ with h | ⟨τ, hτ, rfl⟩
      · exact hbase _ h _ hs
      · rcases Finset.mem_insert.mp hs with rfl | hs
        · exact ⟨apexSet_nonempty hS, apexSet_subset orig S, hcard⟩
        · exact hbase _ hτ _ hs

theorem sdFaces_card_le (orig : W → V) (S : Finset W) {σ : Finset (Finset W)}
    (hσ : σ ∈ sdFaces orig S) : σ.card ≤ S.card := by
  induction S using Finset.strongInduction generalizing σ with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS
    · rw [sdFaces_empty] at hσ
      simp only [Finset.mem_singleton] at hσ
      simp [hσ]
    · have hbase : ∀ τ ∈ sdBase orig S, τ.card + 1 ≤ S.card := by
        intro τ hτ
        obtain ⟨u, hu, hτu⟩ := mem_sdBase.mp hτ
        have huS : u ∈ S := apexSet_subset orig S hu
        have hlt : S.erase u ⊂ S := Finset.erase_ssubset huS
        have := ih _ hlt hτu
        rw [Finset.card_erase_of_mem huS] at this
        have h1 : 1 ≤ S.card := Finset.card_pos.mpr hS
        omega
      rcases (mem_sdFaces_iff hS).mp hσ with h | ⟨τ, hτ, rfl⟩
      · exact le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hbase _ h))
      · exact le_trans (Finset.card_insert_le _ _) (hbase _ hτ)

/-- The subdivision of a face is a simplicial complex. -/
theorem sdFaces_faceClosed (orig : W → V) (S : Finset W) {σ τ : Finset (Finset W)}
    (hσ : σ ∈ sdFaces orig S) (hτσ : τ ⊆ σ) : τ ∈ sdFaces orig S := by
  induction S using Finset.strongInduction generalizing σ τ with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS
    · rw [sdFaces_empty] at hσ ⊢
      simp only [Finset.mem_singleton] at hσ ⊢
      subst hσ
      exact Finset.subset_empty.mp hτσ
    · have hbase : ∀ σ' ∈ sdBase orig S, ∀ τ' ⊆ σ', τ' ∈ sdBase orig S := by
        intro σ' hσ' τ' hτ'
        obtain ⟨u, hu, hσu⟩ := mem_sdBase.mp hσ'
        have hlt : S.erase u ⊂ S := Finset.erase_ssubset (apexSet_subset orig S hu)
        exact mem_sdBase.mpr ⟨u, hu, ih _ hlt hσu hτ'⟩
      rw [mem_sdFaces_iff hS]
      rcases (mem_sdFaces_iff hS).mp hσ with h | ⟨ρ, hρ, rfl⟩
      · exact Or.inl (hbase _ h _ hτσ)
      · by_cases ha : apexSet orig S ∈ τ
        · refine Or.inr ⟨τ.erase (apexSet orig S), hbase _ hρ _ ?_, ?_⟩
          · intro x hx
            have hxτ : x ∈ τ := Finset.mem_of_mem_erase hx
            have hxne : x ≠ apexSet orig S := Finset.ne_of_mem_erase hx
            rcases Finset.mem_insert.mp (hτσ hxτ) with h' | h'
            · exact absurd h' hxne
            · exact h'
          · exact Finset.insert_erase ha
        · refine Or.inl (hbase _ hρ _ ?_)
          intro x hx
          rcases Finset.mem_insert.mp (hτσ hx) with h' | h'
          · exact absurd (h' ▸ hx) ha
          · exact h'

/-- **Compatibility across faces**: the subdivision of a subface is a
subcomplex of the subdivision.  This is where the fixed orderings are used. -/
theorem sdFaces_mono (orig : W → V) {S T : Finset W} (hTS : T ⊆ S) :
    sdFaces orig T ⊆ sdFaces orig S := by
  induction S using Finset.strongInduction generalizing T with
  | _ S ih =>
    rcases T.eq_empty_or_nonempty with rfl | hT
    · rw [sdFaces_empty]
      intro σ hσ
      rw [Finset.mem_singleton] at hσ
      subst hσ
      exact empty_mem_sdFaces orig S
    · have hS : S.Nonempty := hT.mono hTS
      by_cases ha : apexSet orig S ⊆ T
      · have hapex : apexSet orig T = apexSet orig S := apexSet_mono hTS hT ha
        have hbase : sdBase orig T ⊆ sdBase orig S := by
          intro σ hσ
          obtain ⟨u, hu, hσu⟩ := mem_sdBase.mp hσ
          rw [hapex] at hu
          have hlt : S.erase u ⊂ S := Finset.erase_ssubset (apexSet_subset orig S hu)
          exact mem_sdBase.mpr ⟨u, hu, ih _ hlt (Finset.erase_subset_erase u hTS) hσu⟩
        intro σ hσ
        rw [mem_sdFaces_iff hS]
        rcases (mem_sdFaces_iff hT).mp hσ with h | ⟨τ, hτ, rfl⟩
        · exact Or.inl (hbase h)
        · exact Or.inr ⟨τ, hbase hτ, by rw [hapex]⟩
      · obtain ⟨u, hu, huT⟩ := Finset.not_subset.mp ha
        have hlt : S.erase u ⊂ S := Finset.erase_ssubset (apexSet_subset orig S hu)
        have hTsub : T ⊆ S.erase u := Finset.subset_erase.mpr ⟨hTS, huT⟩
        intro σ hσ
        rw [mem_sdFaces_iff hS]
        exact Or.inl (mem_sdBase.mpr ⟨u, hu, ih _ hlt hTsub hσ⟩)

/-- Removing the apex from a simplex of `sdFaces S` lands in the subdivision of
one of the two facets opposite the apex. -/
theorem exists_erase_apex_mem {orig : W → V} {S : Finset W} (hS : S.Nonempty)
    {σ : Finset (Finset W)} (hσ : σ ∈ sdFaces orig S) :
    ∃ u ∈ apexSet orig S, σ.erase (apexSet orig S) ∈ sdFaces orig (S.erase u) := by
  rcases (mem_sdFaces_iff hS).mp hσ with h | ⟨τ, hτ, rfl⟩
  · obtain ⟨u, hu, hσu⟩ := mem_sdBase.mp h
    exact ⟨u, hu, sdFaces_faceClosed orig _ hσu (Finset.erase_subset _ _)⟩
  · obtain ⟨u, hu, hτu⟩ := mem_sdBase.mp hτ
    refine ⟨u, hu, sdFaces_faceClosed orig _ hτu ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp (Finset.mem_of_mem_erase hx) with h' | h'
    · exact absurd h' (Finset.ne_of_mem_erase hx)
    · exact h'

/-! ### Deleted faces are not subdivided -/

/-- The undivided simplex on a set of join vertices, as a simplex of the
subdivision: each vertex `u` becomes the subdivision vertex `{u}`. -/
def sdSimplexOf (T : Finset W) : Finset (Finset W) := T.image fun u ↦ ({u} : Finset W)

omit [LinearOrder W] in
theorem sdSimplexOf_injective : Function.Injective (sdSimplexOf (W := W)) := by
  intro T T' h
  ext u
  constructor <;> intro hu
  · have : ({u} : Finset W) ∈ sdSimplexOf T' := by
      rw [← h]; exact Finset.mem_image_of_mem _ hu
    obtain ⟨v, hv, hv'⟩ := Finset.mem_image.mp this
    rwa [← Finset.singleton_inj.mp hv']
  · have : ({u} : Finset W) ∈ sdSimplexOf T := by
      rw [h]; exact Finset.mem_image_of_mem _ hu
    obtain ⟨v, hv, hv'⟩ := Finset.mem_image.mp this
    rwa [← Finset.singleton_inj.mp hv']

omit [LinearOrder W] in
@[simp]
theorem sdSimplexOf_empty : sdSimplexOf (∅ : Finset W) = ∅ := by simp [sdSimplexOf]

omit [LinearOrder W] in
theorem sdSimplexOf_insert (u : W) (T : Finset W) :
    sdSimplexOf (insert u T) = insert {u} (sdSimplexOf T) := by
  simp [sdSimplexOf, Finset.image_insert]

omit [LinearOrder W] in
theorem card_sdSimplexOf (T : Finset W) : (sdSimplexOf T).card = T.card :=
  Finset.card_image_of_injective _ fun _ _ h ↦ Finset.singleton_inj.mp h

omit [LinearOrder W] in
theorem sdSimplexOf_good (T : Finset W) : ∀ s ∈ sdSimplexOf T, s.card = 1 := by
  intro s hs
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hs
  simp

omit [LinearOrder W] in
theorem sdSimplexOf_mono {T T' : Finset W} (h : T ⊆ T') : sdSimplexOf T ⊆ sdSimplexOf T' :=
  Finset.image_subset_image h

/-- A deleted face carries no bad edge, so it is coned from its earliest vertex
at every step and is left undivided. -/
theorem sdFaces_of_isDeletedFace (orig : W → V) {S : Finset W}
    (hdel : IsDeletedFace orig S) :
    sdFaces orig S = S.powerset.image sdSimplexOf := by
  induction S using Finset.strongInduction with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS
    · rw [sdFaces_empty]
      simp
    · have hb : badElts orig S = ∅ := badElts_eq_empty_iff.mpr hdel
      set v := S.min' hS with hv
      have hvS : v ∈ S := Finset.min'_mem _ _
      have hapex : apexSet orig S = {v} := apexSet_of_deleted hb hS
      have hlt : S.erase v ⊂ S := Finset.erase_ssubset hvS
      have hIH : sdFaces orig (S.erase v) = (S.erase v).powerset.image sdSimplexOf :=
        ih _ hlt (hdel.mono (Finset.erase_subset _ _))
      have hbase : sdBase orig S = (S.erase v).powerset.image sdSimplexOf := by
        ext σ
        rw [mem_sdBase, hapex]
        constructor
        · rintro ⟨u, hu, hσ⟩
          rw [Finset.mem_singleton] at hu
          subst hu
          rwa [hIH] at hσ
        · intro hσ
          exact ⟨v, Finset.mem_singleton_self _, by rw [hIH]; exact hσ⟩
      ext σ
      rw [mem_sdFaces_iff hS, hbase, hapex]
      constructor
      · rintro (hσ | ⟨τ, hτ, rfl⟩)
        · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hσ
          exact Finset.mem_image.mpr ⟨T, Finset.mem_powerset.mpr
            ((Finset.mem_powerset.mp hT).trans (Finset.erase_subset _ _)), rfl⟩
        · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hτ
          refine Finset.mem_image.mpr ⟨insert v T, Finset.mem_powerset.mpr ?_, ?_⟩
          · exact Finset.insert_subset hvS
              ((Finset.mem_powerset.mp hT).trans (Finset.erase_subset _ _))
          · rw [sdSimplexOf_insert]
      · intro hσ
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hσ
        rw [Finset.mem_powerset] at hT
        by_cases hvT : v ∈ T
        · refine Or.inr ⟨sdSimplexOf (T.erase v), Finset.mem_image.mpr
            ⟨T.erase v, Finset.mem_powerset.mpr (Finset.erase_subset_erase v hT), rfl⟩, ?_⟩
          rw [← sdSimplexOf_insert, Finset.insert_erase hvT]
        · exact Or.inl (Finset.mem_image.mpr ⟨T,
            Finset.mem_powerset.mpr (Finset.subset_erase.mpr ⟨hT, hvT⟩), rfl⟩)

/-! ### Induced subcomplexes on the vertices avoiding a join vertex -/

/-- The subcomplex of the subdivision of `S` spanned by the subdivision vertices
avoiding a given join vertex `u` is exactly the subdivision of `S.erase u`. -/
theorem sdFaces_filter_notMem (orig : W → V) (S : Finset W) (u : W) :
    (sdFaces orig S).filter (fun σ ↦ ∀ s ∈ σ, u ∉ s) = sdFaces orig (S.erase u) := by
  induction S using Finset.strongInduction with
  | _ S ih =>
    ext σ
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨hσ, havoid⟩
      rcases S.eq_empty_or_nonempty with rfl | hS
      · simpa using hσ
      · set a := apexSet orig S with ha
        have haS : a ⊆ S := apexSet_subset orig S
        by_cases hua : u ∈ a
        · have hanot : a ∉ σ := fun hmem ↦ havoid a hmem hua
          have hbase : σ ∈ sdBase orig S := by
            rcases (mem_sdFaces_iff hS).mp hσ with h | ⟨τ, -, rfl⟩
            · exact h
            · exact absurd (Finset.mem_insert_self _ _) hanot
          obtain ⟨w, hw, hσw⟩ := mem_sdBase.mp hbase
          have hlt : S.erase w ⊂ S := Finset.erase_ssubset (haS hw)
          have := (ih _ hlt).symm ▸ (Finset.mem_filter.mpr ⟨hσw, havoid⟩ :
            σ ∈ (sdFaces orig (S.erase w)).filter (fun σ ↦ ∀ s ∈ σ, u ∉ s))
          have hsub : (S.erase w).erase u ⊆ S.erase u :=
            Finset.erase_subset_erase u (Finset.erase_subset _ _)
          exact sdFaces_mono orig hsub this
        · have haS' : a ⊆ S.erase u := Finset.subset_erase.mpr ⟨haS, hua⟩
          have hS' : (S.erase u).Nonempty := (apexSet_nonempty hS).mono haS'
          have hapex : apexSet orig (S.erase u) = a :=
            apexSet_mono (Finset.erase_subset _ _) hS' haS'
          have hbase : ∀ τ ∈ sdBase orig S, (∀ s ∈ τ, u ∉ s) → τ ∈ sdBase orig (S.erase u) := by
            intro τ hτ hτavoid
            obtain ⟨w, hw, hτw⟩ := mem_sdBase.mp hτ
            have hlt : S.erase w ⊂ S := Finset.erase_ssubset (haS hw)
            have hmem : τ ∈ sdFaces orig ((S.erase w).erase u) :=
              (ih _ hlt) ▸ Finset.mem_filter.mpr ⟨hτw, hτavoid⟩
            rw [mem_sdBase, hapex]
            exact ⟨w, hw, by rwa [Finset.erase_right_comm] at hmem⟩
          rcases (mem_sdFaces_iff hS).mp hσ with h | ⟨τ, hτ, rfl⟩
          · exact (mem_sdFaces_iff hS').mpr (Or.inl (hbase _ h havoid))
          · refine (mem_sdFaces_iff hS').mpr (Or.inr ⟨τ, hbase _ hτ ?_, by rw [hapex]⟩)
            exact fun s hs ↦ havoid s (Finset.mem_insert_of_mem hs)
    · intro hσ
      refine ⟨sdFaces_mono orig (Finset.erase_subset _ _) hσ, ?_⟩
      intro s hs hus
      exact (Finset.mem_erase.mp ((sdFaces_vertex orig _ hσ s hs).2.1 hus)).1 rfl

/-- Membership form of `sdFaces_filter_notMem`. -/
theorem mem_sdFaces_erase_of_avoid {orig : W → V} {S : Finset W} {u : W}
    {σ : Finset (Finset W)} (hσ : σ ∈ sdFaces orig S) (havoid : ∀ s ∈ σ, u ∉ s) :
    σ ∈ sdFaces orig (S.erase u) := by
  rw [← sdFaces_filter_notMem orig S u]
  exact Finset.mem_filter.mpr ⟨hσ, havoid⟩

/-! ### Good and bad vertices -/

/-- A subdivision vertex is *good* when it is an original join vertex, i.e. a
singleton; the inserted bad-edge midpoints (pairs) are *bad*. -/
def IsGoodSdVertex (s : Finset W) : Prop := s.card = 1

instance (s : Finset W) : Decidable (IsGoodSdVertex s) := by
  unfold IsGoodSdVertex; infer_instance

theorem not_isGoodSdVertex_apexSet {orig : W → V} {S : Finset W}
    (h : (badElts orig S).Nonempty) : ¬ IsGoodSdVertex (apexSet orig S) := by
  rw [IsGoodSdVertex, apexSet_card_eq_two h]
  omega

/-- **The good induced subcomplex is the deleted join.**  The simplices of the
subdivision of `S` all of whose vertices are good are exactly the (undivided)
deleted subfaces of `S`. -/
theorem sdFaces_filter_good (orig : W → V) (S : Finset W) :
    (sdFaces orig S).filter (fun σ ↦ ∀ s ∈ σ, IsGoodSdVertex s) =
      (S.powerset.filter (IsDeletedFace orig)).image sdSimplexOf := by
  induction S using Finset.strongInduction with
  | _ S ih =>
    by_cases hdel : IsDeletedFace orig S
    · rw [sdFaces_of_isDeletedFace orig hdel]
      have hfil : S.powerset.filter (IsDeletedFace orig) = S.powerset := by
        apply Finset.filter_true_of_mem
        intro T hT
        exact hdel.mono (Finset.mem_powerset.mp hT)
      rw [hfil]
      apply Finset.filter_true_of_mem
      intro σ hσ
      obtain ⟨T, -, rfl⟩ := Finset.mem_image.mp hσ
      exact sdSimplexOf_good T
    · have hbad : (badElts orig S).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hcontra
        exact hdel (badElts_eq_empty_iff.mp hcontra)
      have hS : S.Nonempty := by
        rcases S.eq_empty_or_nonempty with rfl | hS
        · exact absurd (fun u hu ↦ absurd hu (by simp)) hdel
        · exact hS
      have hanotgood : ¬ IsGoodSdVertex (apexSet orig S) := not_isGoodSdVertex_apexSet hbad
      ext σ
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨hσ, hgood⟩
        have hanot : apexSet orig S ∉ σ := fun hmem ↦ hanotgood (hgood _ hmem)
        have hbase : σ ∈ sdBase orig S := by
          rcases (mem_sdFaces_iff hS).mp hσ with h | ⟨τ, -, rfl⟩
          · exact h
          · exact absurd (Finset.mem_insert_self _ _) hanot
        obtain ⟨w, hw, hσw⟩ := mem_sdBase.mp hbase
        have hlt : S.erase w ⊂ S := Finset.erase_ssubset (apexSet_subset orig S hw)
        have := (ih _ hlt) ▸ Finset.mem_filter.mpr ⟨hσw, hgood⟩
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp this
        rw [Finset.mem_filter, Finset.mem_powerset] at hT
        exact Finset.mem_image.mpr ⟨T, Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (hT.1.trans (Finset.erase_subset _ _)), hT.2⟩, rfl⟩
      · intro hσ
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hσ
        rw [Finset.mem_filter, Finset.mem_powerset] at hT
        obtain ⟨hTS, hTdel⟩ := hT
        have hex : ∃ w ∈ apexSet orig S, w ∉ T := by
          by_contra hcontra
          push Not at hcontra
          exact apexSet_not_isDeletedFace hbad (hTdel.mono hcontra)
        obtain ⟨w, hw, hwT⟩ := hex
        have hlt : S.erase w ⊂ S := Finset.erase_ssubset (apexSet_subset orig S hw)
        have hmem : sdSimplexOf T ∈
            (sdFaces orig (S.erase w)).filter (fun σ ↦ ∀ s ∈ σ, IsGoodSdVertex s) := by
          rw [ih _ hlt]
          exact Finset.mem_image.mpr ⟨T, Finset.mem_filter.mpr
            ⟨Finset.mem_powerset.mpr (Finset.subset_erase.mpr ⟨hTS, hwT⟩), hTdel⟩, rfl⟩
        obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hmem
        exact ⟨(mem_sdFaces_iff hS).mpr (Or.inl (mem_sdBase.mpr ⟨w, hw, h1⟩)), h2⟩

/-- The good simplices of the subdivision, described elementwise. -/
theorem good_mem_sdFaces_iff (orig : W → V) (S : Finset W) {σ : Finset (Finset W)} :
    (σ ∈ sdFaces orig S ∧ ∀ s ∈ σ, IsGoodSdVertex s) ↔
      ∃ T, T ⊆ S ∧ IsDeletedFace orig T ∧ σ = sdSimplexOf T := by
  constructor
  · intro h
    have hmem : σ ∈ (sdFaces orig S).filter (fun σ ↦ ∀ s ∈ σ, IsGoodSdVertex s) :=
      Finset.mem_filter.mpr h
    rw [sdFaces_filter_good] at hmem
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hmem
    rw [Finset.mem_filter, Finset.mem_powerset] at hT
    exact ⟨T, hT.1, hT.2, rfl⟩
  · rintro ⟨T, hTS, hTdel, rfl⟩
    have hmem : sdSimplexOf T ∈
        (sdFaces orig S).filter (fun σ ↦ ∀ s ∈ σ, IsGoodSdVertex s) := by
      rw [sdFaces_filter_good]
      exact Finset.mem_image.mpr ⟨T, Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hTS, hTdel⟩, rfl⟩
    exact Finset.mem_filter.mp hmem

/-! ### The good-vertex count on top-dimensional simplices -/

/-- **Good-vertex count.**  Every top-dimensional simplex of the subdivision of
`S` contains at least `m(S) + 1` good vertices, where `m(S) + 1` is the number
of distinct original vertices occurring in `S`. -/
theorem card_image_orig_le_card_good (orig : W → V) (S : Finset W)
    {σ : Finset (Finset W)} (hσ : σ ∈ sdFaces orig S) (hcard : σ.card = S.card) :
    (S.image orig).card ≤ (σ.filter IsGoodSdVertex).card := by
  induction S using Finset.strongInduction generalizing σ with
  | _ S ih =>
    by_cases hdel : IsDeletedFace orig S
    · rw [sdFaces_of_isDeletedFace orig hdel] at hσ
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hσ
      rw [Finset.mem_powerset] at hT
      have hTS : T = S := Finset.eq_of_subset_of_card_le hT
        (le_of_eq (by rw [← hcard, card_sdSimplexOf]))
      subst hTS
      have hfil : (sdSimplexOf T).filter IsGoodSdVertex = sdSimplexOf T := by
        apply Finset.filter_true_of_mem
        intro s hs
        exact sdSimplexOf_good T s hs
      rw [hfil, card_sdSimplexOf]
      exact Finset.card_image_le
    · have hbad : (badElts orig S).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hcontra
        exact hdel (badElts_eq_empty_iff.mp hcontra)
      have hS : S.Nonempty := by
        rcases S.eq_empty_or_nonempty with rfl | hS
        · exact absurd (fun u hu ↦ absurd hu (by simp)) hdel
        · exact hS
      set a := apexSet orig S with ha
      have hacard : a.card = 2 := apexSet_card_eq_two hbad
      have hbasecard : ∀ τ ∈ sdBase orig S, τ.card + 1 ≤ S.card := by
        intro τ hτ
        obtain ⟨w, hw, hτw⟩ := mem_sdBase.mp hτ
        have hwS : w ∈ S := apexSet_subset orig S hw
        have := sdFaces_card_le orig _ hτw
        rw [Finset.card_erase_of_mem hwS] at this
        have h1 : 1 ≤ S.card := Finset.card_pos.mpr hS
        omega
      rcases (mem_sdFaces_iff hS).mp hσ with h | ⟨τ, hτ, rfl⟩
      · have := hbasecard _ h
        omega
      · obtain ⟨w, hw, hτw⟩ := mem_sdBase.mp hτ
        have hwS : w ∈ S := apexSet_subset orig S hw
        have hlt : S.erase w ⊂ S := Finset.erase_ssubset hwS
        have hb := hbasecard _ hτ
        have hanotτ : a ∉ τ := by
          intro hmem
          rw [Finset.insert_eq_self.mpr hmem] at hcard
          omega
        have hcardτ : τ.card = (S.erase w).card := by
          rw [Finset.card_insert_of_notMem hanotτ] at hcard
          rw [Finset.card_erase_of_mem hwS]
          omega
        have hIH := ih _ hlt hτw hcardτ
        have hfil : (insert a τ).filter IsGoodSdVertex = τ.filter IsGoodSdVertex := by
          rw [Finset.filter_insert, ite_eq_right (not_isGoodSdVertex_apexSet hbad)]
        rw [hfil]
        refine le_trans (le_of_eq ?_) hIH
        congr 1
        obtain ⟨p, q, hpair, hpq, hporig, hpS, hqS⟩ := exists_apexSet_pair hbad
        apply Finset.Subset.antisymm
        · intro x hx
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
          by_cases hyw : y = w
          · subst hyw
            have hother : ∃ z ∈ S, z ≠ y ∧ orig z = orig y := by
              have hwpair : y ∈ ({p, q} : Finset W) := by
                rw [← hpair]
                simpa only [ha] using hw
              rcases Finset.mem_insert.mp hwpair with rfl | hw'
              · exact ⟨q, hqS, fun h' ↦ hpq h'.symm, hporig.symm⟩
              · rw [Finset.mem_singleton] at hw'
                subst hw'
                exact ⟨p, hpS, hpq, hporig⟩
            obtain ⟨z, hzS, hzy, hzo⟩ := hother
            rw [← hzo]
            exact Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hzy, hzS⟩)
          · exact Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hyw, hy⟩)
        · exact Finset.image_subset_image (Finset.erase_subset _ _)

end BadEdge
end AffineTverberg
