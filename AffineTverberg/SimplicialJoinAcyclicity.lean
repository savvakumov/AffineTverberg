import AffineTverberg.MayerVietoris
import AffineTverberg.SimplicialFiber

set_option linter.style.header false

/-!
# Acyclicity of a finite join of nonempty discrete sets

This file proves the higher-degree acyclicity statement needed for the
simplicial fibers of `lemma:Y`: the join

`W_{b₁} * W_{b₂} * ⋯ * W_{b_N}`

of finitely many *nonempty* sets of vertices (each `W_b` regarded as a discrete
complex, i.e. a set of points) has vanishing reduced homology in every
geometric degree `≤ N - 2`.  In the augmented (cardinality) grading used
throughout `AffineTverberg/SimplicialHomology.lean`, where degree `k` means
geometric degree `k - 1`, this reads: the join is reduced acyclic in every
degree `k < N`, and this includes the augmentation degree `k = 0`.

The top degree `k = N` is genuinely excluded: the join of `N` nonempty discrete
sets is a wedge of `(N-1)`-spheres, which usually has nontrivial top homology.

## Main definitions

* `AffineTverberg.Simplicial.coneOn` : the cone with a given apex over a finite
  face-closed family.
* `AffineTverberg.Simplicial.coneUnion` : the union of the cones with apexes in
  a finite set `S` over a fixed family; this is the join of `S` (as a discrete
  set) with the family.
* `AffineTverberg.Simplicial.joinFiber`, `AffineTverberg.Simplicial.joinComplex` :
  for a "base" map `base : V → B`, a set `A` of allowed vertices and a finite
  set `T` of base vertices, the join complex of the fibers `A ∩ base⁻¹ b`,
  `b ∈ T`: the faces are the subsets of `A` using at most one vertex over each
  base vertex, and only base vertices from `T`.  The empty simplex is a face.
* `AffineTverberg.colorChoiceFamily` : the specialization to the colored
  vertices of `AffineTverberg/SimplicialFiber.lean`, i.e. the finite face-closed
  family of all `IsColorChoiceFace` faces, the empty simplex included.

## Main results

* `isReducedAcyclicUpTo_union_shift` : the finite-union form of Mayer–Vietoris
  which only requires the *adjacent lower* degree on the intersection.
* `isReducedAcyclicUpTo_coneUnion` : joining a nonempty discrete set to a family
  which is acyclic in degrees `< N` gives a family acyclic in degrees `≤ N`.
* `isReducedAcyclicAt_joinComplex` : **the general join theorem**, the join of
  the nonempty fibers over `T` is reduced acyclic in every degree `k < T.card`.
* `isReducedAcyclicAt_colorChoiceFamily` : the specialization to the colored
  faces of the simplicial fiber: reduced acyclic in every degree `k < σ.card`.
-/

noncomputable section

open scoped BigOperators

namespace AffineTverberg

namespace Simplicial

section Cones

variable {V : Type*} [LinearOrder V]

/-- The cone with apex `a` over the family `K`: all faces of `K`, together with
all faces of `K` enlarged by `a`. -/
def coneOn (a : V) (K : Finset (Finset V)) : Finset (Finset V) :=
  K ∪ K.image (insert a)

theorem mem_coneOn {a : V} {K : Finset (Finset V)} {s : Finset V} :
    s ∈ coneOn a K ↔ s ∈ K ∨ ∃ t ∈ K, insert a t = s := by
  simp [coneOn, Finset.mem_union, Finset.mem_image]

theorem subset_coneOn (a : V) (K : Finset (Finset V)) : K ⊆ coneOn a K :=
  Finset.subset_union_left

/-- `coneOn a K` is a cone with apex `a`. -/
theorem isConeWithApex_coneOn (a : V) (K : Finset (Finset V)) :
    IsConeWithApex (coneOn a K) a := by
  intro s hs
  rcases mem_coneOn.mp hs with h | ⟨t, ht, rfl⟩
  · exact mem_coneOn.mpr (Or.inr ⟨s, h, rfl⟩)
  · exact mem_coneOn.mpr (Or.inr ⟨t, ht, by rw [Finset.insert_idem]⟩)

theorem faceClosed_coneOn {a : V} {K : Finset (Finset V)} (hK : FaceClosed K) :
    FaceClosed (coneOn a K) := by
  intro s hs t hts
  rcases mem_coneOn.mp hs with h | ⟨u, hu, rfl⟩
  · exact mem_coneOn.mpr (Or.inl (hK s h t hts))
  · by_cases hat : a ∈ t
    · refine mem_coneOn.mpr (Or.inr ⟨t.erase a, hK u hu _ ?_, Finset.insert_erase hat⟩)
      intro x hx
      have hxa : x ≠ a := Finset.ne_of_mem_erase hx
      rcases Finset.mem_insert.mp (hts (Finset.mem_of_mem_erase hx)) with h | h
      · exact absurd h hxa
      · exact h
    · refine mem_coneOn.mpr (Or.inl (hK u hu t ?_))
      intro x hx
      rcases Finset.mem_insert.mp (hts hx) with h | h
      · exact absurd (h ▸ hx) hat
      · exact h

/-- Cones are reduced acyclic in every degree. -/
theorem isReducedAcyclic_coneOn {𝕜 : Type*} [Field 𝕜] [Fintype V] (a : V)
    (K : Finset (Finset V)) :
    IsReducedAcyclic 𝕜 (coneOn a K) :=
  isReducedAcyclic_of_cone (isConeWithApex_coneOn a K)

/-- The union of the cones with apexes in `S` over `K`: the join of the discrete
set `S` with the family `K`. -/
def coneUnion (S : Finset V) (K : Finset (Finset V)) : Finset (Finset V) :=
  S.biUnion fun v => coneOn v K

theorem mem_coneUnion {S : Finset V} {K : Finset (Finset V)} {s : Finset V} :
    s ∈ coneUnion S K ↔ ∃ v ∈ S, s ∈ coneOn v K := by
  simp [coneUnion]

theorem coneUnion_insert (a : V) (S : Finset V) (K : Finset (Finset V)) :
    coneUnion (insert a S) K = coneUnion S K ∪ coneOn a K := by
  ext s
  simp only [mem_coneUnion, Finset.mem_union, Finset.mem_insert]
  constructor
  · rintro ⟨v, rfl | hv, hs⟩
    · exact Or.inr hs
    · exact Or.inl ⟨v, hv, hs⟩
  · rintro (⟨v, hv, hs⟩ | hs)
    · exact ⟨v, Or.inr hv, hs⟩
    · exact ⟨a, Or.inl rfl, hs⟩

theorem subset_coneUnion {S : Finset V} (hS : S.Nonempty) (K : Finset (Finset V)) :
    K ⊆ coneUnion S K := by
  obtain ⟨v, hv⟩ := hS
  exact fun s hs => mem_coneUnion.mpr ⟨v, hv, subset_coneOn v K hs⟩

theorem faceClosed_coneUnion {S : Finset V} {K : Finset (Finset V)} (hK : FaceClosed K) :
    FaceClosed (coneUnion S K) := by
  intro s hs t hts
  obtain ⟨v, hv, hsv⟩ := mem_coneUnion.mp hs
  exact mem_coneUnion.mpr ⟨v, hv, faceClosed_coneOn hK s hsv t hts⟩

/-- Two cones over `K` with distinct apexes, none of which occurs in a face of
`K`, meet exactly in `K`. -/
theorem coneUnion_inter_coneOn {K : Finset (Finset V)} {S : Finset V} {a : V}
    (hS : S.Nonempty) (ha : a ∉ S) (hafresh : ∀ s ∈ K, a ∉ s) :
    coneUnion S K ∩ coneOn a K = K := by
  ext s
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨h1, h2⟩
    rcases mem_coneOn.mp h2 with h | ⟨t, ht, rfl⟩
    · exact h
    · exfalso
      obtain ⟨v, hv, hsv⟩ := mem_coneUnion.mp h1
      have hat : a ∈ insert a t := Finset.mem_insert_self a t
      rcases mem_coneOn.mp hsv with h | ⟨u, hu, hu2⟩
      · exact hafresh _ h hat
      · rw [← hu2] at hat
        rcases Finset.mem_insert.mp hat with h | h
        · exact ha (h ▸ hv)
        · exact hafresh u hu h
  · intro hs
    exact ⟨subset_coneUnion hS K hs, subset_coneOn a K hs⟩

end Cones

section Gluing

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder V] [Fintype V]

/-- The Mayer–Vietoris union theorem in the form actually needed for iterated
joins: to get exactness of `K ∪ L` in all degrees `≤ N` one only needs
exactness of `K ∩ L` in the degrees `< N`, i.e. one degree lower. -/
theorem isReducedAcyclicUpTo_union_shift {K L : Finset (Finset V)} (hK : FaceClosed K)
    (hL : FaceClosed L) {N : ℕ} (hKa : IsReducedAcyclicUpTo 𝕜 K N)
    (hLa : IsReducedAcyclicUpTo 𝕜 L N)
    (hKLa : ∀ n, n + 1 ≤ N → IsReducedAcyclicAt 𝕜 (K ∩ L) n) :
    IsReducedAcyclicUpTo 𝕜 (K ∪ L) N := by
  intro n hn
  cases n with
  | zero => exact isReducedAcyclicAt_union_zero (hKa 0 (Nat.zero_le _)) (hLa 0 (Nat.zero_le _))
  | succ m =>
      exact isReducedAcyclicAt_union_succ hK hL (hKa (m + 1) hn) (hLa (m + 1) hn) (hKLa m hn)

/-- **Joining a nonempty discrete set raises acyclicity by one degree.**  If `K`
is exact in all degrees `< N` and `S` is a nonempty set of vertices none of which
occurs in a face of `K`, then the join `coneUnion S K` is exact in all degrees
`≤ N`.  Only the lower degrees are used on the intersections. -/
theorem isReducedAcyclicUpTo_coneUnion {K : Finset (Finset V)} (hK : FaceClosed K)
    {S : Finset V} (hS : S.Nonempty) {N : ℕ}
    (hKa : ∀ n, n + 1 ≤ N → IsReducedAcyclicAt 𝕜 K n) :
    (∀ v ∈ S, ∀ s ∈ K, v ∉ s) → IsReducedAcyclicUpTo 𝕜 (coneUnion S K) N := by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton a =>
      intro _
      have hone : coneUnion ({a} : Finset V) K = coneOn a K := by
        ext s; simp [mem_coneUnion]
      rw [hone]
      exact isReducedAcyclicUpTo_of_isReducedAcyclic (isReducedAcyclic_coneOn a K) N
  | cons a S ha hSne ih =>
      intro hfresh
      have hfreshS : ∀ v ∈ S, ∀ s ∈ K, v ∉ s := fun v hv =>
        hfresh v (Finset.mem_cons.mpr (Or.inr hv))
      have hafresh : ∀ s ∈ K, a ∉ s := hfresh a (Finset.mem_cons_self a S)
      have hcons : coneUnion (Finset.cons a S ha) K = coneUnion S K ∪ coneOn a K := by
        rw [Finset.cons_eq_insert, coneUnion_insert]
      rw [hcons]
      refine isReducedAcyclicUpTo_union_shift (faceClosed_coneUnion hK) (faceClosed_coneOn hK)
        (ih hfreshS)
        (isReducedAcyclicUpTo_of_isReducedAcyclic (isReducedAcyclic_coneOn a K) N)
        (fun n hn => ?_)
      rw [coneUnion_inter_coneOn hSne ha hafresh]
      exact hKa n hn

end Gluing

section JoinComplex

variable {V B : Type*}

open Classical in
/-- The set of allowed vertices lying over the base vertex `b`. -/
def joinFiber (base : V → B) (A : Finset V) (b : B) : Finset V :=
  A.filter fun v => base v = b

theorem mem_joinFiber {base : V → B} {A : Finset V} {b : B} {v : V} :
    v ∈ joinFiber base A b ↔ v ∈ A ∧ base v = b := by
  classical
  simp [joinFiber]

open Classical in
/-- The join complex of the fibers `joinFiber base A b`, `b ∈ T`: the faces are
the subsets of `A` all of whose vertices lie over base vertices in `T`, using at
most one vertex over each base vertex.  The empty simplex is a face, so this is
the family used by the augmented (reduced) chain complex. -/
def joinComplex (base : V → B) (A : Finset V) (T : Finset B) : Finset (Finset V) :=
  A.powerset.filter fun s =>
    (∀ v ∈ s, base v ∈ T) ∧ ∀ v ∈ s, ∀ w ∈ s, base v = base w → v = w

/-- The exact membership criterion for the join complex. -/
theorem mem_joinComplex {base : V → B} {A : Finset V} {T : Finset B} {s : Finset V} :
    s ∈ joinComplex base A T ↔
      s ⊆ A ∧ (∀ v ∈ s, base v ∈ T) ∧ ∀ v ∈ s, ∀ w ∈ s, base v = base w → v = w := by
  classical
  simp [joinComplex, Finset.mem_filter, Finset.mem_powerset]

theorem empty_mem_joinComplex (base : V → B) (A : Finset V) (T : Finset B) :
    (∅ : Finset V) ∈ joinComplex base A T :=
  mem_joinComplex.mpr ⟨Finset.empty_subset _, by simp, by simp⟩

theorem faceClosed_joinComplex (base : V → B) (A : Finset V) (T : Finset B) :
    FaceClosed (joinComplex base A T) := by
  intro s hs t hts
  obtain ⟨hsA, hsT, hsinj⟩ := mem_joinComplex.mp hs
  exact mem_joinComplex.mpr ⟨hts.trans hsA, fun v hv => hsT v (hts hv),
    fun v hv w hw => hsinj v (hts hv) w (hts hw)⟩

theorem joinComplex_mono_base {base : V → B} {A : Finset V} {T T' : Finset B} (h : T ⊆ T') :
    joinComplex base A T ⊆ joinComplex base A T' := by
  intro s hs
  obtain ⟨hsA, hsT, hsinj⟩ := mem_joinComplex.mp hs
  exact mem_joinComplex.mpr ⟨hsA, fun v hv => h (hsT v hv), hsinj⟩

/-- A vertex over a base vertex outside `T` occurs in no face of the join
complex over `T`. -/
theorem notMem_of_base_notMem {base : V → B} {A : Finset V} {T : Finset B} {b : B}
    (hb : b ∉ T) {v : V} (hv : base v = b) {s : Finset V} (hs : s ∈ joinComplex base A T) :
    v ∉ s := by
  intro hvs
  exact hb (hv ▸ (mem_joinComplex.mp hs).2.1 v hvs)

/-- **The inductive step:** adding one base vertex to the join amounts to joining
the (nonempty) discrete fiber over it. -/
theorem joinComplex_cons [LinearOrder V] {base : V → B} {A : Finset V} {T : Finset B} {b : B}
    (hb : b ∉ T) :
    joinComplex base A (Finset.cons b T hb) = coneUnion (joinFiber base A b)
      (joinComplex base A T) ∪ joinComplex base A T := by
  ext s
  constructor
  · intro hs
    obtain ⟨hsA, hsT, hsinj⟩ := mem_joinComplex.mp hs
    by_cases hex : ∃ v ∈ s, base v = b
    · obtain ⟨v, hvs, hvb⟩ := hex
      have hterase : s.erase v ∈ joinComplex base A T := by
        refine mem_joinComplex.mpr ⟨(Finset.erase_subset _ _).trans hsA, ?_, ?_⟩
        · intro w hw
          have hws : w ∈ s := Finset.mem_of_mem_erase hw
          rcases Finset.mem_cons.mp (hsT w hws) with h | h
          · exact absurd (hsinj w hws v hvs (by rw [h, hvb]))
              (Finset.ne_of_mem_erase hw)
          · exact h
        · exact fun x hx y hy => hsinj x (Finset.mem_of_mem_erase hx) y
            (Finset.mem_of_mem_erase hy)
      refine Finset.mem_union_left _ (mem_coneUnion.mpr ⟨v, mem_joinFiber.mpr ⟨hsA hvs, hvb⟩, ?_⟩)
      exact mem_coneOn.mpr (Or.inr ⟨s.erase v, hterase, Finset.insert_erase hvs⟩)
    · push Not at hex
      refine Finset.mem_union_right _ (mem_joinComplex.mpr ⟨hsA, ?_, hsinj⟩)
      intro v hv
      rcases Finset.mem_cons.mp (hsT v hv) with h | h
      · exact absurd h (hex v hv)
      · exact h
  · intro hs
    rcases Finset.mem_union.mp hs with hs | hs
    · obtain ⟨v, hv, hsv⟩ := mem_coneUnion.mp hs
      obtain ⟨hvA, hvb⟩ := mem_joinFiber.mp hv
      rcases mem_coneOn.mp hsv with h | ⟨t, ht, rfl⟩
      · exact joinComplex_mono_base (Finset.subset_cons hb) h
      · obtain ⟨htA, htT, htinj⟩ := mem_joinComplex.mp ht
        refine mem_joinComplex.mpr ⟨Finset.insert_subset hvA htA, ?_, ?_⟩
        · intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact Finset.mem_cons.mpr (Or.inl hvb)
          · exact Finset.mem_cons.mpr (Or.inr (htT w hw))
        · have hkey : ∀ w ∈ t, base w ≠ base v := by
            intro w hw hcon
            have hbT : b ∈ T := by
              rw [← hvb, ← hcon]
              exact htT w hw
            exact hb hbT
          intro x hx y hy hxy
          rcases Finset.mem_insert.mp hx with hx' | hx'
          · rcases Finset.mem_insert.mp hy with hy' | hy'
            · rw [hx', hy']
            · exfalso
              refine hkey y hy' ?_
              rw [← hxy, hx']
          · rcases Finset.mem_insert.mp hy with hy' | hy'
            · exfalso
              refine hkey x hx' ?_
              rw [hxy, hy']
            · exact htinj x hx' y hy' hxy
    · exact joinComplex_mono_base (Finset.subset_cons hb) hs

/-- **The general join theorem.**  If every base vertex of `T` has a nonempty
fiber of allowed vertices, then the join complex over `T` is reduced acyclic in
every degree `k < T.card` (geometric degree `≤ T.card - 2`).  The top degree
`T.card` is genuinely excluded. -/
theorem isReducedAcyclicAt_joinComplex (𝕜 : Type*) [Field 𝕜] [LinearOrder V] [Fintype V]
    (base : V → B) (A : Finset V)
    (T : Finset B) (hne : ∀ b ∈ T, (joinFiber base A b).Nonempty) :
    ∀ k, k + 1 ≤ T.card → IsReducedAcyclicAt 𝕜 (joinComplex base A T) k := by
  induction T using Finset.cons_induction with
  | empty => intro k hk; simp at hk
  | cons b T hb ih =>
      have hneT : ∀ c ∈ T, (joinFiber base A c).Nonempty := fun c hc =>
        hne c (Finset.mem_cons.mpr (Or.inr hc))
      have hbne : (joinFiber base A b).Nonempty := hne b (Finset.mem_cons_self b T)
      intro k hk
      rw [Finset.card_cons] at hk
      have hunion : joinComplex base A (Finset.cons b T hb)
          = coneUnion (joinFiber base A b) (joinComplex base A T) := by
        rw [joinComplex_cons hb]
        exact Finset.union_eq_left.mpr (subset_coneUnion hbne _)
      rw [hunion]
      refine isReducedAcyclicUpTo_coneUnion (𝕜 := 𝕜) (N := T.card)
        (faceClosed_joinComplex base A T) hbne (fun n hn => ih hneT n hn) ?_ k (by omega)
      intro v hv s hs
      exact notMem_of_base_notMem hb (mem_joinFiber.mp hv).2 hs

end JoinComplex

end Simplicial

/-! ### The colored faces of the simplicial fiber -/

section ColoredFiber

open Simplicial

variable {V I : Type*} (σ : Finset V) (evalFn : V → I → ℝ)
  [Fintype (NonnegativeColoredVertex σ evalFn)]

/-- The finite face-closed family of *all* color-choice faces, the empty simplex
included.  This is the augmented model of the join complex
`W_{v₁} * ⋯ * W_{v_N}` of `AffineTverberg/SimplicialFiber.lean`. -/
def colorChoiceFamily : Finset (Finset (NonnegativeColoredVertex σ evalFn)) :=
  joinComplex Sigma.fst Finset.univ Finset.univ

/-- **The exact membership criterion**: the members of the family are exactly the
color-choice faces, the empty one included. -/
theorem mem_colorChoiceFamily_iff (s : Finset (NonnegativeColoredVertex σ evalFn)) :
    s ∈ colorChoiceFamily σ evalFn ↔ IsColorChoiceFace σ evalFn s :=
  Iff.trans mem_joinComplex
    ⟨fun h a ha b hb hab => h.2.2 a ha b hb hab,
      fun h => ⟨Finset.subset_univ _, fun _ _ => Finset.mem_univ _, h⟩⟩

/-- The family consists of the empty simplex together with the faces of the
`AbstractSimplicialComplex` `nonnegativeJoinComplex`. -/
theorem mem_colorChoiceFamily_iff_empty_or_mem_join
    (s : Finset (NonnegativeColoredVertex σ evalFn)) :
    s ∈ colorChoiceFamily σ evalFn ↔
      s = ∅ ∨ s ∈ nonnegativeJoinComplex σ evalFn := by
  rw [mem_colorChoiceFamily_iff, mem_nonnegativeJoinComplex_iff]
  constructor
  · intro h
    rcases Finset.eq_empty_or_nonempty s with rfl | hs
    · exact Or.inl rfl
    · exact Or.inr ⟨hs, h⟩
  · rintro (rfl | ⟨-, h⟩)
    · intro a ha
      simp at ha
    · exact h

theorem faceClosed_colorChoiceFamily : FaceClosed (colorChoiceFamily σ evalFn) :=
  faceClosed_joinComplex Sigma.fst Finset.univ Finset.univ

/-- Every color-choice face has at most `σ.card` vertices, so the family has no
simplices in degrees above `σ.card`. -/
theorem card_le_of_mem_colorChoiceFamily {s : Finset (NonnegativeColoredVertex σ evalFn)}
    (hs : s ∈ colorChoiceFamily σ evalFn) : s.card ≤ σ.card := by
  classical
  have hinj : Set.InjOn (fun a : NonnegativeColoredVertex σ evalFn ↦ a.1) s :=
    fun a ha b hb hab => (mem_colorChoiceFamily_iff σ evalFn s).mp hs a ha b hb hab
  calc
    s.card ≤ (Finset.univ : Finset {v // v ∈ σ}).card :=
      Finset.card_le_card_of_injOn (fun a : NonnegativeColoredVertex σ evalFn ↦ a.1)
        (by simp [Set.MapsTo]) hinj
    _ = σ.card := by simp

/-- **Acyclicity of the simplicial fiber.**  Assuming the diagonal relation
(which makes every allowed color set `W_v` nonempty), the family of color-choice
faces is reduced acyclic in every degree `k < σ.card`; in geometric terms its
reduced homology vanishes in all degrees `j ≤ σ.card - 2`.  The augmentation
degree `k = 0` is included, and the top degree `k = σ.card` is deliberately
*not* claimed. -/
theorem isReducedAcyclicAt_colorChoiceFamily (𝕜 : Type*) [Field 𝕜] [Fintype I] [Nonempty I]
    [LinearOrder (NonnegativeColoredVertex σ evalFn)]
    (hdiag : ∀ v ∈ σ, ∑ i, evalFn v i = 0) {k : ℕ} (hk : k < σ.card) :
    IsReducedAcyclicAt 𝕜 (colorChoiceFamily σ evalFn) k := by
  have hfib : ∀ b ∈ (Finset.univ : Finset {v // v ∈ σ}),
      (joinFiber (Sigma.fst : NonnegativeColoredVertex σ evalFn → {v // v ∈ σ})
        Finset.univ b).Nonempty := by
    intro b _
    exact ⟨chosenColoredVertex σ evalFn hdiag b, mem_joinFiber.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have hcard : (Finset.univ : Finset {v // v ∈ σ}).card = σ.card := by simp
  have hle : k + 1 ≤ (Finset.univ : Finset {v // v ∈ σ}).card := by omega
  exact isReducedAcyclicAt_joinComplex 𝕜 Sigma.fst Finset.univ Finset.univ hfib k hle

/-- The homology module form of the previous theorem. -/
theorem homology_colorChoiceFamily_subsingleton (𝕜 : Type*) [Field 𝕜] [Fintype I] [Nonempty I]
    [LinearOrder (NonnegativeColoredVertex σ evalFn)]
    (hdiag : ∀ v ∈ σ, ∑ i, evalFn v i = 0) {k : ℕ} (hk : k < σ.card) :
    Subsingleton (homology 𝕜 (colorChoiceFamily σ evalFn) k) :=
  (homology_subsingleton_iff _ _).mpr (isReducedAcyclicAt_colorChoiceFamily σ evalFn 𝕜 hdiag hk)

end ColoredFiber

section NonVacuity

open Simplicial

variable {V I : Type*} (σ : Finset V) (evalFn : V → I → ℝ)

/-- The colored vertices form a finite type, so the `Fintype` hypothesis of the
results above is satisfiable. -/
instance finite_nonnegativeColoredVertex [Finite I] :
    Finite (NonnegativeColoredVertex σ evalFn) := by
  infer_instance

theorem nonempty_fintype_nonnegativeColoredVertex [Finite I] :
    Nonempty (Fintype (NonnegativeColoredVertex σ evalFn)) :=
  ⟨Fintype.ofFinite _⟩

/-- A linear order on the colored vertices always exists: the homology above does
not depend on the choice, which only fixes the orientation convention. -/
theorem nonempty_linearOrder_nonnegativeColoredVertex :
    Nonempty (LinearOrder (NonnegativeColoredVertex σ evalFn)) := by
  classical
  exact ⟨linearOrderOfSTO WellOrderingRel⟩

end NonVacuity

/-! ### Sharpness: the top degree really is excluded

The join of one nonempty discrete set with two elements is a pair of points,
which is *not* reduced acyclic in degree `1 = T.card`.  So the bound `k < T.card`
in `isReducedAcyclicAt_joinComplex` cannot be improved. -/

section Sharpness

open Simplicial

theorem joinComplex_unit_base_eq_twoPoints :
    joinComplex (fun _ : Fin 2 => ()) Finset.univ {()} = twoPoints := by
  ext s
  rw [mem_joinComplex]
  simp only [twoPoints, Finset.mem_union, Finset.mem_powerset]
  constructor
  · rintro ⟨-, -, hinj⟩
    by_cases h0 : (0 : Fin 2) ∈ s
    · exact Or.inl fun x hx => Finset.mem_singleton.mpr (hinj x hx 0 h0 trivial)
    · refine Or.inr fun x hx => Finset.mem_singleton.mpr ?_
      fin_cases x
      · exact absurd hx h0
      · rfl
  · intro h
    refine ⟨Finset.subset_univ _, by simp, fun x hx y hy _ => ?_⟩
    rcases h with h | h <;>
      rw [Finset.mem_singleton.mp (h hx), Finset.mem_singleton.mp (h hy)]

/-- The join of a single nonempty discrete set of two points has nonvanishing
reduced homology in degree `T.card = 1`. -/
theorem not_isReducedAcyclicAt_joinComplex_top :
    ¬ IsReducedAcyclicAt ℚ (joinComplex (fun _ : Fin 2 => ()) Finset.univ {()})
      ({()} : Finset Unit).card := by
  rw [joinComplex_unit_base_eq_twoPoints]
  simpa using not_isReducedAcyclicAt_twoPoints

end Sharpness

end AffineTverberg
