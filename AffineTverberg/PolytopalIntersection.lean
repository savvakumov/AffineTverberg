import AffineTverberg.PolytopalRealization
import AffineTverberg.BarycentricRealization
import Mathlib.Analysis.Convex.Join

set_option linter.style.header false

/-!
# The intersection property of the polytopal bad-vertex triangulation

Together with `affineIndependent_sdPoint` this gives the genuine geometric
simplicial complex structure of the triangulation.

The three ingredients are

* `simplexCarrier_inter_sdCarrier` — **exact face restriction**: the part of a
  simplex lying in a face of the Cayley join is the subsimplex spanned by the
  vertices contained in that face.  This is the maximizer description
  `exposedBy_convexHull` of a face of a `V`-polytope applied to the simplex.
* `sdQ_filter_mem` — the corresponding combinatorial restriction: the vertices
  of a simplex of `sdQ S` contained in a face `H` of the family form a simplex
  of `sdQ H`.  The hereditary apex rule `apexSet_mono` is what makes this work.
* `param_eq_of_cone_eq` — **the cone lemma**: two cones with a common apex over
  faces avoiding the apex can only meet with equal ray parameters, hence meet in
  the cone over the intersection of the faces.

`simplexCarrier_inter` then proves the intersection condition, and
`isGeometricRealization_sdQ` assembles the geometric realization.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg
namespace BadVertex

open CayleyJoin PolytopeFace BadEdge

variable {n : ℕ} {P : FullDimensionalPolytope n} {m : ℕ}

/-! ### Elementary facts about simplex carriers -/

theorem simplexCarrier_mono {σ τ : Finset (Finset (JoinVertex P m))} (h : σ ⊆ τ) :
    simplexCarrier P m σ ⊆ simplexCarrier P m τ :=
  convexHull_mono (image_mono (by exact_mod_cast h))

theorem simplexCarrier_empty :
    simplexCarrier P m (∅ : Finset (Finset (JoinVertex P m))) = ∅ := by
  simp [simplexCarrier]

theorem sdPoint_mem_simplexCarrier {σ : Finset (Finset (JoinVertex P m))}
    {b : Finset (JoinVertex P m)} (hb : b ∈ σ) :
    sdPoint P m b ∈ simplexCarrier P m σ :=
  subset_convexHull ℝ _ ⟨b, hb, rfl⟩

/-- A simplex of the subdivision of a face lies in the carrier of that face. -/
theorem simplexCarrier_subset_sdCarrier {G : Finset (JoinVertex P m)}
    {σ : Finset (Finset (JoinVertex P m))} (hσ : σ ∈ sdQ P m G) :
    simplexCarrier P m σ ⊆ sdCarrier P m G := by
  apply convexHull_min _ (sdCarrier_convex P m G)
  rintro _ ⟨b, hb, rfl⟩
  exact sdPoint_mem_sdCarrier P m (sdPoset_vertex_subset hσ hb) (sdPoset_vertex_nonempty hσ hb)

theorem simplexCarrier_subset_join {S : Finset (JoinVertex P m)}
    {σ : Finset (Finset (JoinVertex P m))} (hσ : σ ∈ sdQ P m S) :
    simplexCarrier P m σ ⊆ polytopalJoinCarrier P m := by
  apply convexHull_min _ (convex_convexHull ℝ _)
  rintro _ ⟨b, hb, rfl⟩
  exact sdPoint_mem_join b (sdPoset_vertex_nonempty hσ hb)

/-! ### Exact face restriction -/

/-- **Exact restriction of a simplex to a face of the Cayley join.**  A point of
a simplex lying in a face of the family already lies in the subsimplex spanned
by the vertices contained in that face. -/
theorem simplexCarrier_inter_sdCarrier {H : Finset (JoinVertex P m)}
    (hH : H ∈ faceFamily P m) {S : Finset (JoinVertex P m)}
    {σ : Finset (Finset (JoinVertex P m))} (hσ : σ ∈ sdQ P m S) :
    simplexCarrier P m σ ∩ sdCarrier P m H ⊆
      simplexCarrier P m (σ.filter fun b ↦ b ⊆ H) := by
  classical
  rintro x ⟨hxσ, hxH⟩
  obtain ⟨l, hl⟩ := (sdCarrier_isExposed hH) ⟨x, hxH⟩
  rw [hl] at hxH
  set s := σ.image (sdPoint P m) with hs
  have hcoe : (s : Set (PolytopalJoinAmbient n m)) = sdPoint P m '' (σ : Set _) := by
    rw [hs, Finset.coe_image]
  have hxhull : x ∈ convexHull ℝ (s : Set (PolytopalJoinAmbient n m)) := by
    rw [hcoe]; exact hxσ
  have hsQ : ∀ v ∈ s, v ∈ polytopalJoinCarrier P m := by
    intro v hv
    rw [hs, Finset.mem_image] at hv
    obtain ⟨b, hb, rfl⟩ := hv
    exact sdPoint_mem_join b (sdPoset_vertex_nonempty hσ hb)
  have hhullQ : convexHull ℝ (s : Set (PolytopalJoinAmbient n m)) ⊆
      polytopalJoinCarrier P m :=
    convexHull_min hsQ (convex_convexHull ℝ _)
  have hxexp : x ∈ exposedBy (convexHull ℝ (s : Set (PolytopalJoinAmbient n m))) l :=
    ⟨hxhull, fun y hy ↦ hxH.2 y (hhullQ hy)⟩
  rw [exposedBy_convexHull] at hxexp
  refine convexHull_min ?_ (convex_convexHull ℝ _) hxexp
  intro v hv
  obtain ⟨hvs, hvmax⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hv)
  -- `v` attains the maximum of `l`, hence lies in the face
  have hle : l v ≤ l x := hxH.2 v (hsQ v hvs)
  have hge : l x ≤ l v := by
    have hsub : convexHull ℝ (s : Set (PolytopalJoinAmbient n m)) ⊆ {z | l z ≤ l v} :=
      convexHull_min (fun w hw ↦ hvmax w (Finset.mem_coe.mp hw))
        (convex_halfSpace_le l.toLinearMap.isLinear _)
    exact hsub hxhull
  have hvF : v ∈ sdCarrier P m H := by
    rw [hl]
    exact ⟨hsQ v hvs, fun y hy ↦ by rw [le_antisymm hle hge]; exact hxH.2 y hy⟩
  rw [hs, Finset.mem_image] at hvs
  obtain ⟨b, hb, rfl⟩ := hvs
  refine subset_convexHull ℝ _ ⟨b, ?_, rfl⟩
  refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hb, ?_⟩)
  exact subset_of_sdPoint_mem_sdCarrier hH (sdPoset_vertex_nonempty hσ hb)
    (sdPoset_vertex_card_le_two hσ hb) hvF

/-! ### Combinatorial restriction -/

/-- **Combinatorial restriction.**  The vertices of a simplex of `sdQ S`
contained in a face `H` of the family span a simplex of `sdQ H`. -/
theorem sdQ_filter_mem {S H : Finset (JoinVertex P m)} (hH : H ∈ faceFamily P m)
    (hHS : H ⊆ S) {σ : Finset (Finset (JoinVertex P m))} (hσ : σ ∈ sdQ P m S) :
    σ.filter (fun b ↦ b ⊆ H) ∈ sdQ P m H := by
  classical
  induction hk : S.card using Nat.strong_induction_on generalizing S H σ with
  | _ k ih =>
    subst hk
    rcases mem_sdPoset_iff.mp hσ with rfl | ⟨G, hGfam, hGS, hna, hcase⟩
    · have : (∅ : Finset (Finset (JoinVertex P m))).filter (fun b ↦ b ⊆ H) = ∅ := by simp
      rw [this]
      exact (mem_sdQ_iff P m).mpr (Or.inl rfl)
    · have hlt : G.card < S.card := card_lt_of_apexSet_not_subset (orig := origIndex P m) hGS hna
      obtain ⟨hGHfam, -⟩ := sdCarrier_inter hGfam hH
      have hGHG : G ∩ H ⊆ G := Finset.inter_subset_left
      have hGHH : G ∩ H ⊆ H := Finset.inter_subset_right
      -- restricting a simplex of `sdQ G` to `H` is the same as restricting to `G ∩ H`
      have hfilter : ∀ ρ ∈ sdQ P m G,
          ρ.filter (fun b ↦ b ⊆ H) = ρ.filter (fun b ↦ b ⊆ G ∩ H) := by
        intro ρ hρ
        apply Finset.filter_congr
        intro b hb
        have hbG : b ⊆ G := sdPoset_vertex_subset hρ hb
        exact ⟨fun h ↦ Finset.subset_inter hbG h, fun h ↦ h.trans hGHH⟩
      rcases hcase with h | ⟨ρ, hρ, rfl⟩
      · rw [hfilter σ h]
        exact sdQ_mono P m hGHfam hGHH (ih G.card hlt hGHfam hGHG h rfl)
      · by_cases hsub : apexSet (origIndex P m) S ⊆ H
        · -- the apex survives, and it is also the apex of `H`
          have hne : (apexSet (origIndex P m) S).Nonempty :=
            apexSet_nonempty_of_not_subset hna
          have hHne : H.Nonempty := hne.mono hsub
          have hapex : apexSet (origIndex P m) H = apexSet (origIndex P m) S :=
            apexSet_mono hHS hHne hsub
          have hfil : (insert (apexSet (origIndex P m) S) ρ).filter (fun b ↦ b ⊆ H)
              = insert (apexSet (origIndex P m) S) (ρ.filter fun b ↦ b ⊆ G ∩ H) := by
            rw [Finset.filter_insert, ite_eq_left hsub, hfilter ρ hρ]
          rw [hfil]
          rw [mem_sdQ_iff P m]
          refine Or.inr ⟨G ∩ H, hGHfam, hGHH, ?_,
            Or.inr ⟨ρ.filter (fun b ↦ b ⊆ G ∩ H), ih G.card hlt hGHfam hGHG hρ rfl,
              by rw [hapex]⟩⟩
          rw [hapex]
          intro hcon
          exact hna (hcon.trans hGHG)
        · have hfil : (insert (apexSet (origIndex P m) S) ρ).filter (fun b ↦ b ⊆ H)
              = ρ.filter (fun b ↦ b ⊆ G ∩ H) := by
            rw [Finset.filter_insert, ite_eq_right hsub, hfilter ρ hρ]
          rw [hfil]
          exact sdQ_mono P m hGHfam hGHH (ih G.card hlt hGHfam hGHG hρ rfl)

/-! ### The cone lemma -/

section Cone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The cone lemma.**  If two cones with a common apex `q` over exposed faces
avoiding `q` meet, the ray parameters agree. -/
theorem param_eq_of_cone_eq {A F₁ F₂ : Set E} (h1 : IsExposed ℝ A F₁) (h2 : IsExposed ℝ A F₂)
    {q : E} (hq : q ∈ A) (hq1 : q ∉ F₁) (hq2 : q ∉ F₂) {y₁ y₂ : E}
    (hy₁ : y₁ ∈ F₁) (hy₂ : y₂ ∈ F₂) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (heq : (1 - s) • q + s • y₁ = (1 - t) • q + t • y₂) : s = t := by
  have key : ∀ (G₁ G₂ : Set E), IsExposed ℝ A G₁ → q ∉ G₁ → ∀ {z₁ z₂ : E},
      z₁ ∈ G₁ → z₂ ∈ G₂ → G₂ ⊆ A → ∀ {u v : ℝ}, 0 ≤ u → 0 ≤ v →
      (1 - u) • q + u • z₁ = (1 - v) • q + v • z₂ → u ≤ v := by
    intro G₁ G₂ hG₁ hqG₁ z₁ z₂ hz₁ hz₂ hG₂A u v hu hv heq'
    obtain ⟨l, hl⟩ := hG₁ ⟨z₁, hz₁⟩
    rw [hl] at hz₁
    have hqlt : l q < l z₁ := by
      rcases lt_or_eq_of_le (hz₁.2 q hq) with h | h
      · exact h
      · exact absurd (by rw [hl]; exact ⟨hq, fun y hy ↦ by rw [h]; exact hz₁.2 y hy⟩) hqG₁
    have hz₂le : l z₂ ≤ l z₁ := hz₁.2 z₂ (hG₂A hz₂)
    have hval := congrArg l heq'
    simp only [map_add, map_smul, smul_eq_mul] at hval
    nlinarith [hval, hqlt, hz₂le, hu, hv]
  have h12 := key F₁ F₂ h1 hq1 hy₁ hy₂ h2.subset hs ht heq
  have h21 := key F₂ F₁ h2 hq2 hy₂ hy₁ h1.subset ht hs heq.symm
  exact le_antisymm h12 h21

end Cone


/-! ### The intersection condition -/

theorem simplexCarrier_insert (a : Finset (JoinVertex P m))
    (ρ : Finset (Finset (JoinVertex P m))) :
    simplexCarrier P m (insert a ρ) =
      convexHull ℝ (insert (sdPoint P m a)
        (sdPoint P m '' (ρ : Set (Finset (JoinVertex P m))))) := by
  rw [simplexCarrier, Finset.coe_insert, Set.image_insert_eq]

/-- **The intersection condition of a geometric simplicial complex** for the
polytopal bad-vertex triangulation: two simplices meet exactly in the carrier of
their common face. -/
theorem simplexCarrier_inter {S : Finset (JoinVertex P m)}
    {σ τ : Finset (Finset (JoinVertex P m))} (hσ : σ ∈ sdQ P m S) (hτ : τ ∈ sdQ P m S) :
    simplexCarrier P m σ ∩ simplexCarrier P m τ ⊆ simplexCarrier P m (σ ∩ τ) := by
  classical
  induction hk : S.card using Nat.strong_induction_on generalizing S σ τ with
  | _ k ih =>
    subst hk
    -- the common step: if the point lies in a strictly smaller face of the family
    have key : ∀ H : Finset (JoinVertex P m), H ∈ faceFamily P m → H ⊆ S → H.card < S.card →
        ∀ σ' τ' : Finset (Finset (JoinVertex P m)), σ' ∈ sdQ P m S → τ' ∈ sdQ P m S →
        ∀ x, x ∈ simplexCarrier P m σ' → x ∈ simplexCarrier P m τ' →
        x ∈ sdCarrier P m H → x ∈ simplexCarrier P m (σ' ∩ τ') := by
      intro H hHfam hHS hHcard σ' τ' hσ' hτ' x hxσ hxτ hxH
      have h1 : x ∈ simplexCarrier P m (σ'.filter fun b ↦ b ⊆ H) :=
        simplexCarrier_inter_sdCarrier hHfam hσ' ⟨hxσ, hxH⟩
      have h2 : x ∈ simplexCarrier P m (τ'.filter fun b ↦ b ⊆ H) :=
        simplexCarrier_inter_sdCarrier hHfam hτ' ⟨hxτ, hxH⟩
      have hres := ih H.card hHcard (sdQ_filter_mem hHfam hHS hσ')
        (sdQ_filter_mem hHfam hHS hτ') rfl ⟨h1, h2⟩
      refine simplexCarrier_mono ?_ hres
      intro b hb
      rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hb
      exact Finset.mem_inter.mpr ⟨hb.1.1, hb.2.1⟩
    rintro x ⟨hxσ, hxτ⟩
    rcases (mem_sdQ_iff P m).mp hσ with rfl | ⟨G₁, hG₁fam, hG₁S, hna₁, hcase₁⟩
    · rw [simplexCarrier_empty] at hxσ; exact absurd hxσ (by simp)
    rcases (mem_sdQ_iff P m).mp hτ with rfl | ⟨G₂, hG₂fam, hG₂S, hna₂, hcase₂⟩
    · rw [simplexCarrier_empty] at hxτ; exact absurd hxτ (by simp)
    have hlt₁ : G₁.card < S.card :=
      card_lt_of_apexSet_not_subset (orig := origIndex P m) hG₁S hna₁
    have hlt₂ : G₂.card < S.card :=
      card_lt_of_apexSet_not_subset (orig := origIndex P m) hG₂S hna₂
    rcases hcase₁ with h₁ | ⟨ρ₁, hρ₁, rfl⟩
    · -- `σ` avoids the apex
      exact key G₁ hG₁fam hG₁S hlt₁ σ τ hσ hτ x hxσ hxτ
        (simplexCarrier_subset_sdCarrier h₁ hxσ)
    rcases hcase₂ with h₂ | ⟨ρ₂, hρ₂, rfl⟩
    · -- `τ` avoids the apex
      exact key G₂ hG₂fam hG₂S hlt₂ _ τ hσ hτ x hxσ hxτ
        (simplexCarrier_subset_sdCarrier h₂ hxτ)
    -- both contain the apex: the cone argument
    set a := apexSet (origIndex P m) S with ha
    set q := sdPoint P m a with hq
    have hane : a.Nonempty := apexSet_nonempty_of_not_subset hna₁
    have hqJ : q ∈ polytopalJoinCarrier P m := sdPoint_mem_join a hane
    have hqG : ∀ G : Finset (JoinVertex P m), G ∈ faceFamily P m → ¬ a ⊆ G →
        q ∉ sdCarrier P m G := by
      intro G hGfam hna hmem
      exact hna (subset_of_sdPoint_mem_sdCarrier hGfam hane (apexSet_card_le_two S) hmem)
    have hinter : insert a ρ₁ ∩ insert a ρ₂ = insert a (ρ₁ ∩ ρ₂) := by
      ext b
      simp only [Finset.mem_inter, Finset.mem_insert]
      tauto
    have hqmem : q ∈ simplexCarrier P m (insert a (ρ₁ ∩ ρ₂)) :=
      sdPoint_mem_simplexCarrier (Finset.mem_insert_self _ _)
    rw [hinter]
    -- degenerate cases: one of the two simplices is just the apex
    rcases ρ₁.eq_empty_or_nonempty with rfl | hρ₁ne
    · have hsing : simplexCarrier P m (insert a (∅ : Finset (Finset (JoinVertex P m))))
          = {q} := by
        simp [simplexCarrier, hq]
      rw [hsing, mem_singleton_iff] at hxσ
      rw [hxσ]
      exact hqmem
    rcases ρ₂.eq_empty_or_nonempty with rfl | hρ₂ne
    · have hsing : simplexCarrier P m (insert a (∅ : Finset (Finset (JoinVertex P m))))
          = {q} := by
        simp [simplexCarrier, hq]
      rw [hsing, mem_singleton_iff] at hxτ
      rw [hxτ]
      exact hqmem
    -- decompose the point on the two cones
    have himg₁ : (sdPoint P m '' (ρ₁ : Set (Finset (JoinVertex P m)))).Nonempty := by
      obtain ⟨b, hb⟩ := hρ₁ne
      exact ⟨sdPoint P m b, ⟨b, hb, rfl⟩⟩
    have himg₂ : (sdPoint P m '' (ρ₂ : Set (Finset (JoinVertex P m)))).Nonempty := by
      obtain ⟨b, hb⟩ := hρ₂ne
      exact ⟨sdPoint P m b, ⟨b, hb, rfl⟩⟩
    rw [simplexCarrier_insert, convexHull_insert himg₁] at hxσ
    rw [simplexCarrier_insert, convexHull_insert himg₂] at hxτ
    obtain ⟨q₁, hq₁, y₁, hy₁, hseg₁⟩ := mem_convexJoin.mp hxσ
    obtain ⟨q₂, hq₂, y₂, hy₂, hseg₂⟩ := mem_convexJoin.mp hxτ
    rw [mem_singleton_iff] at hq₁ hq₂
    subst hq₁
    subst hq₂
    obtain ⟨u₁, s, hu₁, hs, hsum₁, hx₁⟩ := hseg₁
    obtain ⟨u₂, t, hu₂, ht, hsum₂, hx₂⟩ := hseg₂
    have hy₁c : y₁ ∈ simplexCarrier P m ρ₁ := hy₁
    have hy₂c : y₂ ∈ simplexCarrier P m ρ₂ := hy₂
    have hy₁F : y₁ ∈ sdCarrier P m G₁ := simplexCarrier_subset_sdCarrier hρ₁ hy₁c
    have hy₂F : y₂ ∈ sdCarrier P m G₂ := simplexCarrier_subset_sdCarrier hρ₂ hy₂c
    have heq : (1 - s) • q + s • y₁ = (1 - t) • q + t • y₂ := by
      rw [show (1 : ℝ) - s = u₁ by linarith, show (1 : ℝ) - t = u₂ by linarith, hx₁, hx₂]
    have hst : s = t :=
      param_eq_of_cone_eq (sdCarrier_isExposed hG₁fam) (sdCarrier_isExposed hG₂fam) hqJ
        (hqG G₁ hG₁fam hna₁) (hqG G₂ hG₂fam hna₂) hy₁F hy₂F hs ht heq
    subst hst
    rcases eq_or_lt_of_le hs with hs0 | hspos
    · -- the point is the apex
      have hx : x = q := by
        rw [← hx₁, ← hs0]
        have hu : u₁ = 1 := by linarith
        rw [hu]
        simp [hq]
      rw [hx]
      exact hqmem
    · -- equal ray parameters force equal points on the two faces
      have hyy : y₁ = y₂ := by
        have hsm : s • y₁ = s • y₂ := by
          have h' := congrArg (fun z ↦ z - (1 - s) • q) heq
          simpa using h'
        exact smul_right_injective _ (ne_of_gt hspos) hsm
      subst hyy
      have hyH : y₁ ∈ sdCarrier P m (G₁ ∩ G₂) := by
        rw [(sdCarrier_inter hG₁fam hG₂fam).2]
        exact ⟨hy₁F, hy₂F⟩
      obtain ⟨hGHfam, -⟩ := sdCarrier_inter hG₁fam hG₂fam
      have hGHS : G₁ ∩ G₂ ⊆ S := (Finset.inter_subset_left).trans hG₁S
      have hGHcard : (G₁ ∩ G₂).card < S.card :=
        lt_of_le_of_lt (Finset.card_le_card Finset.inter_subset_left) hlt₁
      have hρ₁S : ρ₁ ∈ sdQ P m S := sdQ_mono P m hG₁fam hG₁S hρ₁
      have hρ₂S : ρ₂ ∈ sdQ P m S := sdQ_mono P m hG₂fam hG₂S hρ₂
      have hyres : y₁ ∈ simplexCarrier P m (ρ₁ ∩ ρ₂) :=
        key (G₁ ∩ G₂) hGHfam hGHS hGHcard ρ₁ ρ₂ hρ₁S hρ₂S y₁ hy₁c hy₂c hyH
      have hymem : y₁ ∈ simplexCarrier P m (insert a (ρ₁ ∩ ρ₂)) :=
        simplexCarrier_mono (Finset.subset_insert _ _) hyres
      have hxseg : x ∈ segment ℝ q y₁ := ⟨u₁, s, hu₁, le_of_lt hspos, hsum₁, hx₁⟩
      exact (convex_convexHull ℝ _).segment_subset hqmem hymem hxseg

/-- **The polytopal bad-vertex triangulation is a geometric realization.** -/
theorem isGeometricRealization_sdQ (S : Finset (JoinVertex P m)) :
    Simplicial.IsGeometricRealization (sdQ P m S) (sdPoint P m) where
  independent := fun _ hσ ↦ affineIndependent_sdPoint hσ
  intersection := fun _ hσ _ hτ ↦ simplexCarrier_inter hσ hτ

end BadVertex
end AffineTverberg
