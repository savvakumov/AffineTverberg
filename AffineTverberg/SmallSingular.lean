import AffineTverberg.SmallChains

set_option linter.style.header false

/-!
# Iterated subdivision makes singular simplices small

This file carries the mesh estimates of `AffineTverberg.SmallChains` over to
singular chains, and proves the *small chain reduction*: given an open cover
`U : ι → Set X` of a space `X` and a singular simplex `σ : Δ n → X`, some
iterate `sd ^ m` of the barycentric subdivision operator takes `σ` into the
submodule spanned by singular simplices each of whose images is contained in a
single member of the cover.

The main results are

* `realChain_sdSing`, `realChain_sdIterMap` : the subdivision operator commutes
  with realization of affine chains along a singular simplex;
* `smallChains` : the submodule of `U`-small singular chains, and
  `smallChains_d` : it is stable under the boundary, i.e. it is a genuine
  subcomplex;
* `exists_sdIterMap_sElt_mem_smallChains` : **the small chain reduction** for a
  single singular simplex;
* `exists_sdIterMap_mem_smallChains` : the same statement for an arbitrary
  singular chain.

Together with `sdIterHomotopy` (an actual chain homotopy from `sd ^ m` to the
identity) this is the analytic heart of the classical small-chain theorem.

## What follows this file

`AffineTverberg.SmallChainTheorem` uses the results proved here, together with
the bookkeeping operator `D = Σ_{i<m} T ∘ sd ^ i`, to prove both halves of the
small chain theorem at the level of chains. What is still *not* proved, and is
not assumed anywhere in this development, is listed at the end of that file.
-/

noncomputable section

open CategoryTheory Limits Simplicial Metric
open scoped BigOperators

namespace AffineTverberg

namespace AffChain

variable {X : TopCat.{0}}

/-! ### Basis elements of the singular chain groups -/

/-- The basis element of the singular chain group given by a singular simplex. -/
def sElt {n : ℕ} (σ : C(Δt n, X)) : (singChains X).X n := (ιs (singSimplex σ)).hom (1 : ℝ)

lemma realChain_sElt {k n : ℕ} (σ : C(Δt k, X)) (w : Fin (n + 1) → Δt k) :
    ((realChain σ).f n).hom (elt w) = sElt (σ.comp (affMap w)) := by
  have h := congrArg (fun (g : ModuleCat.of ℝ ℝ ⟶ (singChains X).X n) => g.hom (1 : ℝ))
    (ιa_realChain_singSimplex σ w)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, elt, sElt] using h

lemma sElt_d {n : ℕ} (σ : C(Δt (n + 1), X)) :
    ((singChains X).d (n + 1) n).hom (sElt σ) =
      ∑ i : Fin (n + 2), (-1 : ℝ) ^ (i : ℕ) • sElt (σ.comp (faceMap i)) := by
  have h := (TopCat.toSSet.obj X).ιChainComplex_d (ModuleCat.of ℝ ℝ) (singSimplex σ)
  have h2 := congrArg (fun (g : ModuleCat.of ℝ ℝ ⟶ (singChains X).X n) => g.hom (1 : ℝ)) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  change ((singChains X).d (n + 1) n).hom ((ιs (singSimplex σ)).hom (1 : ℝ)) = _
  rw [h2]
  rw [show ((∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        ιs ((TopCat.toSSet.obj X).δ i (singSimplex σ))).hom (1 : ℝ)) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        ((ιs ((TopCat.toSSet.obj X).δ i (singSimplex σ))).hom (1 : ℝ)) by simp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Int.cast_smul_eq_zsmul ℝ ((-1 : ℤ) ^ (i : ℕ))]
  push_cast
  rw [delta_singSimplex]
  rfl

/-! ### Subdivision commutes with realization -/

/-- The subdivision of the realization of an affine chain along `σ` is the
realization of its affine subdivision. -/
theorem realChain_sdSing {k n : ℕ} (σ : C(Δt k, X)) :
    (realChain σ).f n ≫ sdSing X n = sdHom k n ≫ (realChain σ).f n := by
  refine affChains_hom_ext fun v => ?_
  have htuple : (fun a => affPoint v (idTuple n a)) = v := funext fun a => affPoint_vertex v a
  have hmid : ιa (idTuple n) ≫ sdHom n n ≫ (pushChain v).f n = ιa v ≫ sdHom k n := by
    rw [pushChain_sdHom, ← Category.assoc, ιa_pushChain, htuple]
  calc ιa v ≫ (realChain σ).f n ≫ sdSing X n
      = ιs (singSimplex (σ.comp (affMap v))) ≫ sdSing X n := by
        rw [← Category.assoc, ιa_realChain_singSimplex]
    _ = ιa (idTuple n) ≫ sdHom n n ≫ (realChain (σ.comp (affMap v))).f n := ιs_sdSing _
    _ = ιa (idTuple n) ≫ sdHom n n ≫ ((pushChain v).f n ≫ (realChain σ).f n) := by
        rw [realChain_comp_affMap]
    _ = (ιa (idTuple n) ≫ sdHom n n ≫ (pushChain v).f n) ≫ (realChain σ).f n := by
        simp only [Category.assoc]
    _ = (ιa v ≫ sdHom k n) ≫ (realChain σ).f n := by rw [hmid]
    _ = ιa v ≫ sdHom k n ≫ (realChain σ).f n := by rw [Category.assoc]

/-- The iterated subdivision of the realization of an affine chain along `σ` is
the realization of its iterated affine subdivision. -/
theorem realChain_sdIterMap {k n : ℕ} (σ : C(Δt k, X)) (m : ℕ) :
    (realChain σ).f n ≫ (sdIterMap X m).f n = sdIterHom k m n ≫ (realChain σ).f n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sdIterMap_succ]
    change (realChain σ).f n ≫ ((sdIterMap X m).f n ≫ (sdChainMap X).f n) = _
    rw [← Category.assoc, ih, Category.assoc]
    change sdIterHom k m n ≫ ((realChain σ).f n ≫ sdSing X n) = _
    rw [realChain_sdSing, sdIterHom_succ, Category.assoc]

lemma sElt_eq_realChain_elt {n : ℕ} (σ : C(Δt n, X)) :
    sElt σ = ((realChain σ).f n).hom (elt (idTuple n)) := by
  rw [realChain_sElt]
  congr 1
  rw [affMap_idTuple]
  rfl

lemma sdIterMap_sElt {n : ℕ} (σ : C(Δt n, X)) (m : ℕ) :
    ((sdIterMap X m).f n).hom (sElt σ) =
      ((realChain σ).f n).hom ((sdIterHom n m n).hom (elt (idTuple n))) := by
  rw [sElt_eq_realChain_elt]
  have h := congrArg (fun (g : (affChains n).X n ⟶ (singChains X).X n) =>
    g.hom (elt (idTuple n))) (realChain_sdIterMap σ m)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-! ### Small chains -/

variable {ι : Type}

/-- The set of basis singular `n`-chains whose image lies inside a single
member of the family `U`. -/
def smallSet (U : ι → Set X) (n : ℕ) : Set ((singChains X).X n) :=
  {x | ∃ (σ : C(Δt n, X)) (i : ι), (∀ t, σ t ∈ U i) ∧ x = sElt σ}

/-- The submodule of `U`-small singular `n`-chains. -/
def smallChains (U : ι → Set X) (n : ℕ) : Submodule ℝ ((singChains X).X n) :=
  Submodule.span ℝ (smallSet U n)

lemma sElt_mem_smallChains {U : ι → Set X} {n : ℕ} {σ : C(Δt n, X)} {i : ι}
    (h : ∀ t, σ t ∈ U i) : sElt σ ∈ smallChains U n :=
  Submodule.subset_span ⟨σ, i, h, rfl⟩

/-- The submodule of singular `n`-chains carried by a single subset `S` of
`X`. -/
def chainsIn (S : Set X) (n : ℕ) : Submodule ℝ ((singChains X).X n) :=
  Submodule.span ℝ {x | ∃ σ : C(Δt n, X), (∀ t, σ t ∈ S) ∧ x = sElt σ}

lemma sElt_mem_chainsIn {S : Set X} {n : ℕ} {σ : C(Δt n, X)} (h : ∀ t, σ t ∈ S) :
    sElt σ ∈ chainsIn S n :=
  Submodule.subset_span ⟨σ, h, rfl⟩

/-- The small chains of a family are exactly the sum of the chains carried by
its members. This is the description of the small chains used in the
Mayer-Vietoris argument. -/
theorem smallChains_eq_iSup (U : ι → Set X) (n : ℕ) :
    smallChains U n = ⨆ i, chainsIn (U i) n := by
  refine le_antisymm (Submodule.span_le.2 ?_) (iSup_le fun i => Submodule.span_le.2 ?_)
  · rintro x ⟨σ, i, hσ, rfl⟩
    exact le_iSup (fun i => chainsIn (U i) n) i (sElt_mem_chainsIn hσ)
  · rintro x ⟨σ, hσ, rfl⟩
    exact sElt_mem_smallChains (i := i) hσ

/-- **The small chains form a subcomplex**: the boundary of a `U`-small chain
is `U`-small. -/
theorem smallChains_d (U : ι → Set X) (n : ℕ) {x : (singChains X).X (n + 1)}
    (hx : x ∈ smallChains U (n + 1)) :
    ((singChains X).d (n + 1) n).hom x ∈ smallChains U n := by
  have hle : smallChains U (n + 1) ≤
      (smallChains U n).comap ((singChains X).d (n + 1) n).hom := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨σ, i, hσ, rfl⟩
    change ((singChains X).d (n + 1) n).hom (sElt σ) ∈ smallChains U n
    rw [sElt_d]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
    exact sElt_mem_smallChains (i := i) fun t => hσ _
  exact hle hx

/-! ### The small chain reduction -/

/-- Any two points of a standard simplex are at distance at most `1`. -/
lemma dist_le_one {k : ℕ} (x y : Δt k) : dist x y ≤ 1 := by
  refine dist_le_of_coords x y 1 zero_le_one fun c => ?_
  have hx1 : (x : Fin (k + 1) → ℝ) c ≤ 1 := by
    rw [← x.2.2]
    exact Finset.single_le_sum (f := (x : Fin (k + 1) → ℝ)) (fun i _ => x.2.1 i)
      (Finset.mem_univ c)
  have hy1 : (y : Fin (k + 1) → ℝ) c ≤ 1 := by
    rw [← y.2.2]
    exact Finset.single_le_sum (f := (y : Fin (k + 1) → ℝ)) (fun i _ => y.2.1 i)
      (Finset.mem_univ c)
  have hx0 : 0 ≤ (x : Fin (k + 1) → ℝ) c := x.2.1 c
  have hy0 : 0 ≤ (y : Fin (k + 1) → ℝ) c := y.2.1 c
  rw [abs_le]
  constructor <;> linarith

/-- The whole image of an affine simplex with small vertex set is contained in a
small ball around its first vertex. -/
lemma affMap_mem_ball {k n : ℕ} (w : Fin (n + 1) → Δt k) (δ δ' : ℝ)
    (h : ∀ a b, dist (w a) (w b) ≤ δ) (hδ : δ < δ') (t : Δt n) :
    affPoint w t ∈ ball (w 0) δ' := by
  have hδ0 : 0 ≤ δ := le_trans dist_nonneg (h 0 0)
  have hd := dist_affPoint_le (w 0) w t δ hδ0 fun a => h 0 a
  refine mem_ball.2 ?_
  rw [dist_comm]
  exact lt_of_le_of_lt hd hδ

/-- **The small chain reduction for a single singular simplex.** Given an open
cover `U` of `X` and a singular simplex `σ`, some iterate of the barycentric
subdivision carries `σ` into the submodule of `U`-small chains. -/
theorem exists_sdIterMap_sElt_mem_smallChains {ι : Type} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcov : ∀ x : X, ∃ i, x ∈ U i) {n : ℕ} (σ : C(Δt n, X)) :
    ∃ m : ℕ, ((sdIterMap X m).f n).hom (sElt σ) ∈ smallChains U n := by
  classical
  -- the pullback cover of the standard simplex
  have hopen : ∀ i, IsOpen (σ ⁻¹' U i) := fun i => (hU i).preimage σ.continuous
  have hcover : (Set.univ : Set (Δt n)) ⊆ ⋃ i, σ ⁻¹' U i := by
    intro t _
    obtain ⟨i, hi⟩ := hcov (σ t)
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  obtain ⟨δ, hδ0, hδ⟩ :=
    lebesgue_number_lemma_of_metric (s := (Set.univ : Set (Δt n)))
      (isCompact_univ) hopen hcover
  -- choose an iterate whose mesh is smaller than the Lebesgue number
  have hr : (n : ℝ) / ((n : ℝ) + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hδ0 hr
  refine ⟨m, ?_⟩
  rw [sdIterMap_sElt]
  have hmesh := sdIterHom_elt_mem_spanTuples (k := n) (n := n) m (idTuple n) 1 zero_le_one
    (fun a b => dist_le_one _ _)
  refine map_mem_of_mem_spanTuples ((realChain σ).f n) ?_ hmesh
  rintro w ⟨-, hw⟩
  rw [realChain_sElt]
  obtain ⟨i, hi⟩ := hδ (w 0) (Set.mem_univ _)
  refine sElt_mem_smallChains (i := i) fun t => ?_
  have hball : affPoint w t ∈ ball (w 0) δ :=
    affMap_mem_ball w (((n : ℝ) / ((n : ℝ) + 1)) ^ m * 1) δ (by simpa using hw)
      (by simpa using hm) t
  exact hi hball

/-- The basis elements span the singular chain groups. -/
lemma singChains_span_sElt (n : ℕ) :
    Submodule.span ℝ (Set.range (fun σ : C(Δt n, X) => sElt σ)) = ⊤ := by
  set S := Submodule.span ℝ (Set.range (fun σ : C(Δt n, X) => sElt σ)) with hS
  have hmem : ∀ (σ : C(Δt n, X)) (r : ℝ), (ιs (singSimplex σ)).hom r ∈ S := by
    intro σ r
    have hr : (ιs (singSimplex σ)).hom r = r • sElt σ := by
      rw [sElt, ← map_smul]
      congr 1
      simp
    rw [hr]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self σ))
  have hq : (ModuleCat.ofHom S.mkQ :
      (singChains X).X n ⟶ ModuleCat.of ℝ (((singChains X).X n) ⧸ S)) = 0 := by
    refine singChains_hom_ext' fun σ => ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
    change S.mkQ ((ιs (singSimplex σ)).hom r) = (0 : ((singChains X).X n) ⧸ S)
    exact (Submodule.Quotient.mk_eq_zero _).2 (hmem σ r)
  refine eq_top_iff.2 fun x _ => ?_
  have hx := congrArg (fun (g : (singChains X).X n ⟶
    ModuleCat.of ℝ (((singChains X).X n) ⧸ S)) => g.hom x) hq
  exact (Submodule.Quotient.mk_eq_zero _).1 hx

/-- **The small chain reduction.** Given an open cover `U` of `X`, every
singular chain becomes `U`-small after finitely many barycentric
subdivisions. -/
theorem exists_sdIterMap_mem_smallChains {ι : Type} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcov : ∀ x : X, ∃ i, x ∈ U i) {n : ℕ}
    (x : (singChains X).X n) :
    ∃ m : ℕ, ((sdIterMap X m).f n).hom x ∈ smallChains U n := by
  classical
  -- the set of chains for which some iterate works is a submodule
  have hmono : ∀ (m m' : ℕ), m ≤ m' → ∀ y : (singChains X).X n,
      ((sdIterMap X m).f n).hom y ∈ smallChains U n →
      ((sdIterMap X m').f n).hom y ∈ smallChains U n := by
    intro m m' hmm
    obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hmm
    induction p with
    | zero => intro y hy; simpa using hy
    | succ p ih =>
      intro y hy
      have hstep : ∀ z : (singChains X).X n, z ∈ smallChains U n →
          ((sdChainMap X).f n).hom z ∈ smallChains U n := by
        intro z hz
        have hle : smallChains U n ≤ (smallChains U n).comap ((sdChainMap X).f n).hom := by
          refine Submodule.span_le.2 ?_
          rintro y' ⟨τ, i, hτ, rfl⟩
          change ((sdChainMap X).f n).hom (sElt τ) ∈ smallChains U n
          have hτ' : ((sdChainMap X).f n).hom (sElt τ) =
              ((realChain τ).f n).hom ((sdHom n n).hom (elt (idTuple n))) := by
            change (sdSing X n).hom (sElt τ) = _
            rw [sElt_eq_realChain_elt]
            have h := congrArg (fun (g : (affChains n).X n ⟶ (singChains X).X n) =>
              g.hom (elt (idTuple n))) (realChain_sdSing (n := n) τ)
            simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
          rw [hτ']
          have hmesh := sdHom_elt_mem_spanTuples (k := n) n (idTuple n) 1 zero_le_one
            (fun a b => dist_le_one _ _)
          refine map_mem_of_mem_spanTuples ((realChain τ).f n) ?_ hmesh
          rintro w ⟨-, -⟩
          rw [realChain_sElt]
          exact sElt_mem_smallChains (i := i) fun t => hτ _
        exact hle hz
      have := ih (by omega) y hy
      have hsucc : ((sdIterMap X (m + (p + 1))).f n).hom y =
          ((sdChainMap X).f n).hom (((sdIterMap X (m + p)).f n).hom y) := by
        rw [show m + (p + 1) = (m + p) + 1 from rfl, sdIterMap_succ]
        rfl
      rw [hsucc]
      exact hstep _ this
  -- it suffices to treat basis elements
  have hx : x ∈ Submodule.span ℝ (Set.range (fun σ : C(Δt n, X) => sElt σ)) := by
    rw [singChains_span_sElt]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨σ, rfl⟩ := hy
    exact exists_sdIterMap_sElt_mem_smallChains U hU hcov σ
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨ma, hma⟩ := ha
    obtain ⟨mb, hmb⟩ := hb
    refine ⟨max ma mb, ?_⟩
    rw [map_add]
    exact Submodule.add_mem _ (hmono _ _ (le_max_left _ _) _ hma)
      (hmono _ _ (le_max_right _ _) _ hmb)
  | smul c a _ ha =>
    obtain ⟨m, hm⟩ := ha
    exact ⟨m, by rw [map_smul]; exact Submodule.smul_mem _ _ hm⟩

end AffChain

end AffineTverberg
