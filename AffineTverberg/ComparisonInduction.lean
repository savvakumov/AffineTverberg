import AffineTverberg.SimplicialMayerVietorisSES

set_option linter.style.header false

/-!
# The general simplicial-to-singular comparison theorem

This file proves, unconditionally, that for every finite linearly ordered
vertex type `V` and every finite face-closed family `K ⊆ Finset V` the
comparison chain map

`comparisonChainMap hK : simplicialChains hK ⟶ singularChains K`

from the oriented simplicial chain complex of `K` to Mathlib's singular chain
complex of the barycentric realization of `K` is a quasi-isomorphism, so that
`comparisonHomologyMap hK n` is an isomorphism in every ordinary degree `n`.

The proof is an induction on `K.card`.  A face `s` of maximal cardinality is
removed and the realization is covered by the two open sets

* `punctured K s` — the realization with the barycenter of `s` deleted, which
  deformation retracts onto the realization of `K.erase s`;
* `faceStar K s` — the union of the open stars of the vertices of `s`, which
  deformation retracts onto the closed simplex of `s`.

Their intersection deformation retracts onto the realization of the boundary
`boundaryFamily s`.  Because `faceStar K s` contains the whole closed simplex
of `s`, the comparison chain map lands in the complex of chains that are small
for this cover, so it becomes an honest morphism of Mayer-Vietoris short exact
sequences of chain complexes; the compatibility with the connecting maps is
therefore not an extra hypothesis but is supplied by Mathlib's
`HomologicalComplex.HomologySequence.quasiIso_τ₃`.  Finally the small-chain
theorem `quasiIso_smallInc` for the *open* cover turns the statement about
small chains into the statement about all singular chains.

The base case is the family all of whose faces are empty (in particular the
void family and `{∅}`): there the realization is empty and both chain
complexes vanish.
-/

noncomputable section

open CategoryTheory Limits

namespace AffineTverberg

namespace AffChain

variable {C D C' D' E F : ChainComplex (ModuleCat.{0} ℝ) ℕ}

/-- Composition on the left distributes over `pairLift`. -/
theorem comp_pairLift (θ : F ⟶ E) (α : E ⟶ C) (β : E ⟶ D) :
    θ ≫ pairLift α β = pairLift (θ ≫ α) (θ ≫ β) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

variable {X : TopCat.{0}} {ι : Type} (U : ι → Set X)

/-- The inclusion of the small chains is a monomorphism of chain complexes. -/
instance mono_smallInc : Mono (smallInc U) :=
  HomologicalComplex.mono_of_mono_f _
    (fun n => (ModuleCat.mono_iff_injective _).2 (smallInc_injective U n))

end AffChain

namespace Simplicial

open AffChain

variable {V : Type} [Fintype V] [LinearOrder V]

/-! ### Naturality of the comparison map into a subspace -/

variable {K L M : Finset (Finset V)}

omit [LinearOrder V] in
theorem singularChainsMap_eq_singChainsMap (h : K ⊆ L) :
    singularChainsMap h = singChainsMap (baryInclusion h) := rfl

/-- Naturality of `comparisonSub` in the subfamily. -/
theorem comparisonSub_naturality (hL : FaceClosed L) (hM : FaceClosed M)
    (hLM : L ⊆ M) (hMK : M ⊆ K) (S : Set ↥(barySpace K))
    (hS : ∀ y : ↥(barySpace K), y.val ∈ barycentricCarrier M → y ∈ S) :
    simplicialChainsInclusion hL hM hLM ≫ comparisonSub hM hMK S hS =
      comparisonSub hL (hLM.trans hMK) S
        (fun y hy => hS y (barycentricCarrier_mono hLM hy)) := by
  have hnat := comparisonChainMap_naturality hL hM hLM
  rw [comparisonSub, ← Category.assoc, ← hnat, Category.assoc,
    singularChainsMap_eq_singChainsMap, ← singChainsMap_comp]
  rfl

/-! ### The degenerate case of a family with no nonempty face -/

theorem subsingleton_simplicialChains_X (hK : FaceClosed K) (hempty : ∀ t ∈ K, t = ∅) (m : ℕ) :
    Subsingleton ((simplicialChains hK).X m) := by
  have hzero : ∀ x : Finset V → ℝ, x ∈ chains ℝ K (m + 1) → x = 0 := by
    intro x hx
    funext t
    by_contra h
    obtain ⟨htK, htcard⟩ := hx t h
    rw [hempty t htK] at htcard
    simp at htcard
  constructor
  intro c d
  refine chainCoeff_injective hK ?_
  rw [hzero _ (chainCoeff_mem hK c), hzero _ (chainCoeff_mem hK d)]

omit [LinearOrder V] in
theorem isEmpty_barycentricCarrier (hempty : ∀ t ∈ K, t = ∅) :
    IsEmpty ↥(barycentricCarrier K) := by
  constructor
  rintro ⟨x, -, hsum, t, htK, hsupp⟩
  rw [hempty t htK] at hsupp
  have : ∀ v, x v = 0 := fun v => hsupp v (Finset.notMem_empty v)
  rw [Finset.sum_congr rfl (fun v _ => this v)] at hsum
  simp at hsum

omit [LinearOrder V] in
theorem subsingleton_singularChains_X (hempty : ∀ t ∈ K, t = ∅) (m : ℕ) :
    Subsingleton ((singularChains K).X m) := by
  have hE : IsEmpty ↥(barycentricCarrier K) := isEmpty_barycentricCarrier hempty
  have hidx : IsEmpty (singIdx (barySpace K) m) := by
    constructor
    intro x
    exact hE.false (simplexMap x (stdSimplex.vertex (0 : Fin (m + 1))))
  have hsub : Subsingleton (singIdx (barySpace K) m →₀ ℝ) := by
    constructor
    intro f g
    exact Finsupp.ext fun x => hidx.elim x
  exact (chainEquiv (barySpace K) m).injective.subsingleton

/-- The degenerate base case: if no face of `K` is nonempty, both chain
complexes vanish and the comparison map is an isomorphism. -/
theorem quasiIso_comparisonChainMap_of_empty (hK : FaceClosed K) (hempty : ∀ t ∈ K, t = ∅) :
    QuasiIso (comparisonChainMap hK) := by
  have hiso : ∀ m : ℕ, IsIso ((comparisonChainMap hK).f m) := by
    intro m
    have h1 := subsingleton_simplicialChains_X hK hempty m
    have h2 := subsingleton_singularChains_X hempty m
    have hm : Mono ((comparisonChainMap hK).f m) :=
      (ModuleCat.mono_iff_injective _).2 (fun _ _ _ => Subsingleton.elim _ _)
    have he : Epi ((comparisonChainMap hK).f m) :=
      (ModuleCat.epi_iff_surjective _).2 (fun _ => ⟨0, Subsingleton.elim _ _⟩)
    exact isIso_of_mono_of_epi _
  have : IsIso (comparisonChainMap hK) := HomologicalComplex.Hom.isIso_of_components _
  infer_instance

/-! ### The two open sets of the cover -/

section Step

variable {K : Finset (Finset V)} {s : Finset V}

/-- The first member of the open cover of the realization of `K`: the
realization with the barycenter of the face `s` removed, typed as a subset of
the realization viewed as a topological space. -/
def coverPunctured (K : Finset (Finset V)) (s : Finset V) : Set ↥(barySpace K) := punctured K s

/-- The second member of the open cover of the realization of `K`: the union
of the open stars of the vertices of `s`, typed as a subset of the realization
viewed as a topological space.  It contains the whole closed simplex of
`s`. -/
def coverStar (K : Finset (Finset V)) (s : Finset V) : Set ↥(barySpace K) := faceStar K s

theorem isOpen_coverPunctured (K : Finset (Finset V)) (s : Finset V) :
    IsOpen (coverPunctured K s) := isOpen_punctured K s

omit [LinearOrder V] in
theorem isOpen_coverStar (K : Finset (Finset V)) (s : Finset V) :
    IsOpen (coverStar K s) := isOpen_faceStar K s

/-- The two sets cover the realization. -/
theorem mem_coverPunctured_union_coverStar (hs : s.Nonempty) (x : ↥(barySpace K)) :
    x ∈ coverPunctured K s ∪ coverStar K s := mem_punctured_or_faceStar hs x

omit [Fintype V] in
theorem faceClosed_erase_of_max (hK : FaceClosed K) (hmax : ∀ t ∈ K, s ⊆ t → t = s) :
    FaceClosed (K.erase s) := by
  intro t ht u hut
  obtain ⟨htne, htK⟩ := Finset.mem_erase.1 ht
  refine Finset.mem_erase.2 ⟨?_, hK t htK u hut⟩
  rintro rfl
  exact htne (hmax t htK hut)

omit [Fintype V] in
theorem faceClosed_boundaryFamily (s : Finset V) : FaceClosed (boundaryFamily s) := by
  intro t ht u hut
  obtain ⟨htne, htp⟩ := Finset.mem_erase.1 ht
  refine Finset.mem_erase.2 ⟨?_, Finset.mem_powerset.2 (hut.trans (Finset.mem_powerset.1 htp))⟩
  rintro rfl
  exact htne (Finset.Subset.antisymm (Finset.mem_powerset.1 htp) hut)

/-- The realization of `K.erase s` misses the barycenter of `s`. -/
theorem mem_coverPunctured_of_mem_carrier_erase (hmax : ∀ t ∈ K, s ⊆ t → t = s)
    (y : ↥(barySpace K)) (hy : y.val ∈ barycentricCarrier (K.erase s)) :
    y ∈ coverPunctured K s := by
  intro hEq
  exact faceCenter_notMem_carrier_erase hmax (hEq ▸ hy)

omit [LinearOrder V] in
/-- The closed simplex of `s` lies in the open star of its vertices. -/
theorem mem_coverStar_of_mem_barycentricFace (K : Finset (Finset V)) (s : Finset V)
    (y : ↥(barySpace K)) (hy : y.val ∈ barycentricFace s) : y ∈ coverStar K s := by
  change 0 < starMass s y.val
  rw [starMass_eq_one_of_mem_barycentricFace hy]
  norm_num

omit [LinearOrder V] in
theorem mem_coverStar_of_mem_carrier_powerset (K : Finset (Finset V)) (s : Finset V)
    (y : ↥(barySpace K)) (hy : y.val ∈ barycentricCarrier s.powerset) : y ∈ coverStar K s :=
  mem_coverStar_of_mem_barycentricFace K s y (by rwa [barycentricCarrier_powerset] at hy)

theorem mem_inter_of_mem_carrier_boundaryFamily (K : Finset (Finset V)) (s : Finset V)
    (y : ↥(barySpace K)) (hy : y.val ∈ barycentricCarrier (boundaryFamily s)) :
    y ∈ coverPunctured K s ∩ coverStar K s := by
  refine ⟨?_, mem_coverStar_of_mem_carrier_powerset K s y
    (barycentricCarrier_mono (Finset.erase_subset _ _) hy)⟩
  intro hEq
  exact faceCenter_notMem_carrier_erase
    (fun t ht hst => Finset.Subset.antisymm (Finset.mem_powerset.1 ht) hst) (hEq ▸ hy)

/-- Every closed simplex of `K` lies in one of the two open sets of the
cover. -/
theorem faces_small (hmax : ∀ t ∈ K, s ⊆ t → t = s) : ∀ t ∈ K,
    (∀ y : ↥(barySpace K), y.val ∈ barycentricFace t → y ∈ coverPunctured K s) ∨
    (∀ y : ↥(barySpace K), y.val ∈ barycentricFace t → y ∈ coverStar K s) := by
  intro t ht
  by_cases hts : t = s
  · subst hts
    exact Or.inr (mem_coverStar_of_mem_barycentricFace K t)
  · exact Or.inl fun y hy => mem_coverPunctured_of_mem_carrier_erase hmax y
      (barycentricFace_subset_carrier (Finset.mem_erase.2 ⟨hts, ht⟩) hy)

/-! ### The three vertical quasi-isomorphisms -/

/-- The comparison map of `K.erase s` into the punctured realization. -/
abbrev compErase (hA : FaceClosed (K.erase s)) (hmax : ∀ t ∈ K, s ⊆ t → t = s) :
    simplicialChains hA ⟶ singChains (subSpace (coverPunctured K s)) :=
  comparisonSub hA (Finset.erase_subset _ _) (coverPunctured K s)
    (mem_coverPunctured_of_mem_carrier_erase hmax)

/-- The comparison map of the closed simplex of `s` into the open star. -/
abbrev compStar (hBK : s.powerset ⊆ K) :
    simplicialChains (faceClosed_powerset s) ⟶ singChains (subSpace (coverStar K s)) :=
  comparisonSub (faceClosed_powerset s) hBK (coverStar K s)
    (mem_coverStar_of_mem_carrier_powerset K s)

/-- The comparison map of the boundary of `s` into the intersection of the two
sets of the cover. -/
abbrev compBoundary (hCK : boundaryFamily s ⊆ K) :
    simplicialChains (faceClosed_boundaryFamily s) ⟶
      singChains (subSpace (coverPunctured K s ∩ coverStar K s)) :=
  comparisonSub (faceClosed_boundaryFamily s) hCK (coverPunctured K s ∩ coverStar K s)
    (mem_inter_of_mem_carrier_boundaryFamily K s)

theorem quasiIso_compErase (hK : FaceClosed K) (hs : s.Nonempty)
    (hmax : ∀ t ∈ K, s ⊆ t → t = s) (hA : FaceClosed (K.erase s))
    (ihA : QuasiIso (comparisonChainMap hA)) : QuasiIso (compErase hA hmax) :=
  quasiIso_comparisonSub hA (Finset.erase_subset _ _) _ _ ihA
    (puncturedHomotopyEquiv hK hs hmax).symm rfl

theorem quasiIso_compStar (hsK : s ∈ K) (hs : s.Nonempty) (hBK : s.powerset ⊆ K) :
    QuasiIso (compStar hBK) := by
  refine quasiIso_comparisonSub _ hBK _ _ ?_ (starHomotopyEquiv hsK).symm rfl
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  obtain ⟨v, hv⟩ := hs
  exact isIso_comparisonHomologyMap_powerset hv n

theorem quasiIso_compBoundary (hsK : s ∈ K) (hs : s.Nonempty)
    (hmax : ∀ t ∈ K, s ⊆ t → t = s) (hCK : boundaryFamily s ⊆ K)
    (ihC : QuasiIso (comparisonChainMap (faceClosed_boundaryFamily s))) :
    QuasiIso (compBoundary hCK) :=
  quasiIso_comparisonSub _ hCK _ _ ihC
    (starPuncturedBoundaryHomotopyEquiv hs hsK hmax).symm rfl

/-! ### The two commuting squares -/

theorem comparison_comm₁₂ (hmax : ∀ t ∈ K, s ⊆ t → t = s)
    (hA : FaceClosed (K.erase s)) (hCA : boundaryFamily s ⊆ K.erase s)
    (hBK : s.powerset ⊆ K) (hCK : boundaryFamily s ⊆ K) :
    simpMvF (faceClosed_boundaryFamily s) hA (faceClosed_powerset s) hCA
        (Finset.erase_subset _ _) ≫ pairMap (compErase hA hmax) (compStar hBK) =
      compBoundary hCK ≫ mvF (coverPunctured K s) (coverStar K s) := by
  rw [show simpMvF (faceClosed_boundaryFamily s) hA (faceClosed_powerset s) hCA
        (Finset.erase_subset _ _) =
      pairLift (simplicialChainsInclusion (faceClosed_boundaryFamily s) hA hCA)
        (-(simplicialChainsInclusion (faceClosed_boundaryFamily s) (faceClosed_powerset s)
          (Finset.erase_subset _ _))) from rfl,
    show mvF (coverPunctured K s) (coverStar K s) =
      pairLift (subMap Set.inter_subset_left) (-(subMap Set.inter_subset_right)) from rfl,
    pairLift_comp, comp_pairLift, Preadditive.neg_comp, Preadditive.comp_neg,
    comparisonSub_naturality (faceClosed_boundaryFamily s) hA hCA (Finset.erase_subset _ _),
    comparisonSub_naturality (faceClosed_boundaryFamily s) (faceClosed_powerset s)
      (Finset.erase_subset _ _) hBK,
    comparisonSub_comp_subMap, comparisonSub_comp_subMap]

theorem comparison_comm₂₃ (hK : FaceClosed K) (hmax : ∀ t ∈ K, s ⊆ t → t = s)
    (hA : FaceClosed (K.erase s)) (hBK : s.powerset ⊆ K) :
    simpMvG hA (faceClosed_powerset s) hK (Finset.erase_subset _ _) hBK ≫
        comparisonSmall hK (faces_small hmax) =
      pairMap (compErase hA hmax) (compStar hBK) ≫
        mvG (coverPunctured K s) (coverStar K s) := by
  rw [← cancel_mono (smallInc (mvCover (coverPunctured K s) (coverStar K s))),
    Category.assoc, Category.assoc, comparisonSmall_comp_smallInc, mvG_comp_smallInc,
    show simpMvG hA (faceClosed_powerset s) hK (Finset.erase_subset _ _) hBK =
      pairDesc (simplicialChainsInclusion hA hK (Finset.erase_subset _ _))
        (simplicialChainsInclusion (faceClosed_powerset s) hK hBK) from rfl,
    pairDesc_comp, pairMap_comp_pairDesc, comparisonSub_comp_chainsInclusion,
    comparisonSub_comp_chainsInclusion,
    comparisonChainMap_naturality hA hK (Finset.erase_subset _ _),
    comparisonChainMap_naturality (faceClosed_powerset s) hK hBK]

/-! ### Assembling the induction step -/

omit [Fintype V] in
theorem subset_erase_union_powerset (K : Finset (Finset V)) (s : Finset V) :
    K ⊆ K.erase s ∪ s.powerset := by
  intro t ht
  by_cases hts : t = s
  · exact Finset.mem_union_right _ (hts ▸ Finset.mem_powerset_self s)
  · exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hts, ht⟩)

omit [Fintype V] in
theorem mem_boundaryFamily_of_mem_both (K : Finset (Finset V)) (s : Finset V) :
    ∀ t, t ∈ K.erase s → t ∈ s.powerset → t ∈ boundaryFamily s :=
  fun _ ht htp => Finset.mem_erase.2 ⟨(Finset.mem_erase.1 ht).1, htp⟩

/-- The morphism from the simplicial Mayer-Vietoris short exact sequence of
the decomposition `K = (K.erase s) ∪ s.powerset` to the singular Mayer-Vietoris
short exact sequence of the open cover `{coverPunctured K s, coverStar K s}`,
given by the comparison map in each of the three spots. -/
def comparisonMvHom (hK : FaceClosed K) (hmax : ∀ t ∈ K, s ⊆ t → t = s)
    (hA : FaceClosed (K.erase s)) (hCA : boundaryFamily s ⊆ K.erase s)
    (hBK : s.powerset ⊆ K) (hCK : boundaryFamily s ⊆ K) :
    simpMvShortComplex (faceClosed_boundaryFamily s) hA (faceClosed_powerset s) hK hCA
        (Finset.erase_subset _ _) (Finset.erase_subset _ _) hBK ⟶
      mvShortComplex (coverPunctured K s) (coverStar K s) where
  τ₁ := compBoundary hCK
  τ₂ := pairMap (compErase hA hmax) (compStar hBK)
  τ₃ := comparisonSmall hK (faces_small hmax)
  comm₁₂ := (comparison_comm₁₂ hmax hA hCA hBK hCK).symm
  comm₂₃ := (comparison_comm₂₃ hK hmax hA hBK).symm

/-- **The induction step.**  If `s` is a maximal nonempty face of `K` and the
comparison map is a quasi-isomorphism for `K.erase s` and for the boundary of
`s`, then it is one for `K`. -/
theorem quasiIso_comparisonChainMap_step (hK : FaceClosed K) (hsK : s ∈ K) (hs : s.Nonempty)
    (hmax : ∀ t ∈ K, s ⊆ t → t = s) (hA : FaceClosed (K.erase s))
    (ihA : QuasiIso (comparisonChainMap hA))
    (ihC : QuasiIso (comparisonChainMap (faceClosed_boundaryFamily s))) :
    QuasiIso (comparisonChainMap hK) := by
  have hBK : s.powerset ⊆ K := fun t ht => hK s hsK t (Finset.mem_powerset.1 ht)
  have hCA : boundaryFamily s ⊆ K.erase s := fun t ht =>
    Finset.mem_erase.2 ⟨(Finset.mem_erase.1 ht).1, hBK (Finset.erase_subset _ _ ht)⟩
  have hCK : boundaryFamily s ⊆ K := hCA.trans (Finset.erase_subset _ _)
  have := quasiIso_compErase hK hs hmax hA ihA
  have := quasiIso_compStar hsK hs hBK
  have hqC := quasiIso_compBoundary hsK hs hmax hCK ihC
  have hq3 : QuasiIso (comparisonSmall hK (faces_small hmax)) :=
    HomologicalComplex.HomologySequence.quasiIso_τ₃ (comparisonMvHom hK hmax hA hCA hBK hCK)
      (simpMv_shortExact (faceClosed_boundaryFamily s) hA (faceClosed_powerset s) hK hCA
        (Finset.erase_subset _ _) (Finset.erase_subset _ _) hBK
        (subset_erase_union_powerset K s) (mem_boundaryFamily_of_mem_both K s))
      (mvShortExact (coverPunctured K s) (coverStar K s)) hqC (quasiIso_pairMap _ _)
  have hsi : QuasiIso (smallInc (mvCover (coverPunctured K s) (coverStar K s))) :=
    quasiIso_smallInc _
      (isOpen_mvCover _ _ (isOpen_coverPunctured K s) (isOpen_coverStar K s))
      (exists_mem_mvCover _ _ (mem_coverPunctured_union_coverStar hs))
  rw [← comparisonSmall_comp_smallInc hK (faces_small hmax)]
  infer_instance

/-! ### The general comparison theorem -/

/-- **The comparison chain map is a quasi-isomorphism** for every finite
face-closed family. -/
theorem quasiIso_comparisonChainMap {K : Finset (Finset V)} (hK : FaceClosed K) :
    QuasiIso (comparisonChainMap hK) := by
  classical
  induction hn : K.card using Nat.strong_induction_on generalizing K with
  | _ n ih =>
    subst hn
    by_cases hempty : ∀ t ∈ K, t = ∅
    · exact quasiIso_comparisonChainMap_of_empty hK hempty
    · push Not at hempty
      obtain ⟨t₀, ht₀K, ht₀⟩ := hempty
      -- choose a face of maximal cardinality
      obtain ⟨s, hsK, hsmax⟩ := K.exists_max_image Finset.card ⟨t₀, ht₀K⟩
      have hs : s.Nonempty := by
        rw [← Finset.card_pos]
        exact lt_of_lt_of_le (Finset.card_pos.2 ht₀)
          (hsmax t₀ ht₀K)
      have hmax : ∀ t ∈ K, s ⊆ t → t = s := fun t htK hst =>
        (Finset.eq_of_subset_of_card_le hst (hsmax t htK)).symm
      have hA : FaceClosed (K.erase s) := faceClosed_erase_of_max hK hmax
      have hcardA : (K.erase s).card < K.card := Finset.card_erase_lt_of_mem hsK
      have hcardC : (boundaryFamily s).card < K.card := by
        refine lt_of_le_of_lt (Finset.card_le_card ?_) hcardA
        exact fun t ht =>
          Finset.mem_erase.2 ⟨(Finset.mem_erase.1 ht).1,
            hK s hsK t (Finset.mem_powerset.1 (Finset.erase_subset _ _ ht))⟩
      exact quasiIso_comparisonChainMap_step hK hsK hs hmax hA
        (ih _ hcardA hA rfl) (ih _ hcardC (faceClosed_boundaryFamily s) rfl)

/-- **The general comparison theorem.**  For every finite linearly ordered
vertex type, every finite face-closed family `K` and every ordinary degree `n`,
the comparison map from the oriented simplicial homology of `K` to the singular
homology of the barycentric realization of `K` is an isomorphism. -/
theorem isIso_comparisonHomologyMap {K : Finset (Finset V)} (hK : FaceClosed K) (n : ℕ) :
    IsIso (comparisonHomologyMap hK n) := by
  have hq := quasiIso_comparisonChainMap hK
  have h : IsIso (HomologicalComplex.homologyMap (comparisonChainMap hK) n) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    exact (quasiIso_iff _).1 hq n
  exact h

/-! ### Reduced homology in degree zero

In degree `0` the correct statement is about the *augmented* complexes: the
comparison theorem identifies the reduced degree-zero homology of `K` with the
reduced degree-zero singular homology of the realization, i.e. with the kernel
of Mathlib's singular augmentation.  We record the transfer of invertibility of
the augmentation, which is the reduced vanishing statement. -/

/-- The comparison map in degree `0` intertwines the two augmentations. -/
theorem comparisonHomologyMap_zero_realSingularAugmentation {K : Finset (Finset V)}
    (hK : FaceClosed K) :
    HomologicalComplex.homologyMap (comparisonChainMap hK) 0 ≫
        (realSingularAugmentation (barySpace K) :
          (singularChains K).homology 0 ⟶ ModuleCat.of ℝ ℝ) =
      augHomology (simplicialChains hK) (simplicialAug hK) (d_simplicialAug hK) := by
  rw [← augHomology_singular_eq K]
  exact comparisonHomologyMap_zero_augHomology hK

/-- **Reduced degree zero.**  If the augmentation of the oriented simplicial
chain complex of `K` induces an isomorphism on degree-zero homology — that is,
if the reduced simplicial homology of `K` vanishes in degree `0` — then
Mathlib's singular augmentation of the realization of `K` is an isomorphism,
i.e. the reduced singular homology of the realization vanishes in degree
`0`. -/
theorem isIso_realSingularAugmentation_of_simplicial {K : Finset (Finset V)}
    (hK : FaceClosed K)
    (h : IsIso (augHomology (simplicialChains hK) (simplicialAug hK) (d_simplicialAug hK))) :
    IsIso (realSingularAugmentation (barySpace K)) := by
  have hc : IsIso (HomologicalComplex.homologyMap (comparisonChainMap hK) 0) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    exact (quasiIso_iff _).1 (quasiIso_comparisonChainMap hK) 0
  have hcomp : IsIso (HomologicalComplex.homologyMap (comparisonChainMap hK) 0 ≫
      (realSingularAugmentation (barySpace K) :
        (singularChains K).homology 0 ⟶ ModuleCat.of ℝ ℝ)) := by
    rw [comparisonHomologyMap_zero_realSingularAugmentation hK]
    exact h
  exact IsIso.of_isIso_comp_left
    (HomologicalComplex.homologyMap (comparisonChainMap hK) 0)
    (realSingularAugmentation (barySpace K))

end Step

end Simplicial

end AffineTverberg
