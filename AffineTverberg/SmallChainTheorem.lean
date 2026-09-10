import AffineTverberg.SmallSingular

set_option linter.style.header false

/-!
# The small chain theorem

Let `U : ι → Set X` be an open cover of a topological space `X`. This file
proves the two halves of the classical *small chain theorem*: the inclusion of
the subcomplex of `U`-small singular chains into the singular chain complex is
a quasi-isomorphism. The two halves are stated at the level of chains, which is
exactly the form in which they are used to derive singular Mayer-Vietoris:

* `exists_small_cycle_homologous` : every singular cycle is homologous to a
  `U`-small cycle;
* `small_boundary_of_boundary` : a `U`-small cycle that bounds in the singular
  chain complex already bounds a `U`-small chain.

The proofs use the genuine barycentric subdivision operator of
`AffineTverberg.SingularSubdivision`, the small chain reduction of
`AffineTverberg.SmallSingular`, and the explicit chain homotopy

  `tdIter X m = Σ_{i < m} sd ^ i ≫ T`,   `∂ ∘ tdIter + tdIter ∘ ∂ = 1 - sd ^ m`,

whose smallness properties (`tdIter_mem_smallChains`) are also proved, since
they are what makes the second half work.

Nothing is assumed: all identities are proved from the alternating face maps
and the affine subdivision operators.

## Precise remaining obligations towards the general comparison

The small-chain theorem is fully packaged in `SmallChainQuasiIso`. The
subsequent comparison obligations remain open; none is assumed here.

1. *Packaging (done in `SmallChainQuasiIso`)*: the subcomplex `C^U ⊆ C_*(X)` is an
   object of `ChainComplex (ModuleCat ℝ) ℕ` (its degreewise pieces are
   `smallChains U n`, and `smallChains_d` shows the boundary restricts), and
   `exists_small_cycle_homologous` and `small_boundary_of_boundary` prove
   the inclusion `C^U ⟶ C_*(X)` is a quasi-isomorphism. These are the surjectivity and
   the injectivity of the induced map on homology, in element form.
2. *Mayer-Vietoris*: for an open cover `X = A ∪ B`, the short exact sequence
   `0 ⟶ C_*(A ∩ B) ⟶ C_*(A) ⊕ C_*(B) ⟶ C^{A,B} ⟶ 0` together with 1 gives the
   singular Mayer-Vietoris long exact sequence, and likewise excision.
3. *The comparison*: `IsIso (Simplicial.comparisonHomologyMap hK n)` for a
   face-closed `K : Finset (Finset V)` and every ordinary degree `n`. The
   classical route is induction on the number of simplices of `K`, splitting
   off a top-dimensional simplex and applying 2 to the open cover of the
   realization by an open star neighbourhood of that simplex and the
   complement of its barycentre; degree zero is ordinary `H₀`, and reduced
   `H₀` is the kernel of the augmentation, a distinction that must be kept.
4. *Specialisation*: only after 3 can the comparison be applied to the ridge
   fiber (`AffineTverberg.RidgeFiberComparison`) and to the midpoint bad
   subcomplex (`AffineTverberg.SimplicialBadHomology`,
   `AffineTverberg.SimplicialBadTopology`). Boundary sphere identification,
   Alexander duality and Leray-Vietoris-Begle remain separate statements and
   are not hidden inside any of the above.
-/

noncomputable section

open CategoryTheory Limits Simplicial Metric
open scoped BigOperators

namespace AffineTverberg

namespace AffChain

variable {X : TopCat.{0}} {ι : Type}

/-! ### Affine chains are spanned by their basis elements -/

lemma affChains_span_elt (k n : ℕ) :
    Submodule.span ℝ (Set.range (fun w : Fin (n + 1) → Δt k => elt w)) = ⊤ := by
  set S := Submodule.span ℝ (Set.range (fun w : Fin (n + 1) → Δt k => elt w)) with hS
  have hmem : ∀ (w : Fin (n + 1) → Δt k) (r : ℝ), (ιa w).hom r ∈ S := by
    intro w r
    have hr : (ιa w).hom r = r • elt w := by
      rw [elt, ← map_smul]
      congr 1
      simp
    rw [hr]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self w))
  have hq : (ModuleCat.ofHom S.mkQ :
      (affChains k).X n ⟶ ModuleCat.of ℝ (((affChains k).X n) ⧸ S)) = 0 := by
    refine affChains_hom_ext fun w => ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
    change S.mkQ ((ιa w).hom r) = (0 : ((affChains k).X n) ⧸ S)
    exact (Submodule.Quotient.mk_eq_zero _).2 (hmem w r)
  refine eq_top_iff.2 fun x _ => ?_
  have hx := congrArg (fun (g : (affChains k).X n ⟶
    ModuleCat.of ℝ (((affChains k).X n) ⧸ S)) => g.hom x) hq
  exact (Submodule.Quotient.mk_eq_zero _).1 hx

/-! ### Smallness is inherited by everything realized along a small simplex -/

/-- Everything realized along a singular simplex with image in one member of
the cover is a small chain. -/
lemma realChain_mem_smallChains {U : ι → Set X} {n j : ℕ} {σ : C(Δt n, X)} {i : ι}
    (hσ : ∀ t, σ t ∈ U i) (y : (affChains n).X j) :
    ((realChain σ).f j).hom y ∈ smallChains U j := by
  have hy : y ∈ Submodule.span ℝ (Set.range (fun w : Fin (j + 1) → Δt n => elt w)) := by
    rw [affChains_span_elt]; trivial
  induction hy using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨w, rfl⟩ := ha
    rw [realChain_sElt]
    exact sElt_mem_smallChains (i := i) fun t => hσ _
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

/-- To check that a map preserves small chains it suffices to check it on
small basis chains. -/
lemma smallChains_map {U : ι → Set X} {n j : ℕ}
    (f : (singChains X).X n ⟶ (singChains X).X j)
    (h : ∀ (σ : C(Δt n, X)) (i : ι), (∀ t, σ t ∈ U i) → f.hom (sElt σ) ∈ smallChains U j)
    {x : (singChains X).X n} (hx : x ∈ smallChains U n) : f.hom x ∈ smallChains U j := by
  have hle : smallChains U n ≤ (smallChains U j).comap f.hom := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨σ, i, hσ, rfl⟩
    exact h σ i hσ
  exact hle hx

lemma sdSing_sElt {n : ℕ} (σ : C(Δt n, X)) :
    (sdSing X n).hom (sElt σ) = ((realChain σ).f n).hom ((sdHom n n).hom (elt (idTuple n))) := by
  rw [sElt_eq_realChain_elt]
  have h := congrArg (fun (g : (affChains n).X n ⟶ (singChains X).X n) =>
    g.hom (elt (idTuple n))) (realChain_sdSing (n := n) σ)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

lemma tdSing_sElt {n : ℕ} (σ : C(Δt n, X)) :
    (tdSing X n).hom (sElt σ) =
      ((realChain σ).f (n + 1)).hom ((tdHom n n).hom (elt (idTuple n))) := by
  have h := congrArg (fun (g : ModuleCat.of ℝ ℝ ⟶ (singChains X).X (n + 1)) => g.hom (1 : ℝ))
    (ιs_tdSing σ)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, sElt, elt] using h

/-- The subdivision operator preserves small chains. -/
lemma sdSing_mem_smallChains {U : ι → Set X} {n : ℕ} {x : (singChains X).X n}
    (hx : x ∈ smallChains U n) : (sdSing X n).hom x ∈ smallChains U n := by
  refine smallChains_map _ (fun σ i hσ => ?_) hx
  rw [sdSing_sElt]
  exact realChain_mem_smallChains hσ _

/-- The homotopy operator preserves small chains. -/
lemma tdSing_mem_smallChains {U : ι → Set X} {n : ℕ} {x : (singChains X).X n}
    (hx : x ∈ smallChains U n) : (tdSing X n).hom x ∈ smallChains U (n + 1) := by
  refine smallChains_map _ (fun σ i hσ => ?_) hx
  rw [tdSing_sElt]
  exact realChain_mem_smallChains hσ _

lemma sdIterMap_f_succ (X : TopCat.{0}) (m n : ℕ) :
    (sdIterMap X (m + 1)).f n = (sdIterMap X m).f n ≫ sdSing X n := rfl

lemma sdIterMap_mem_smallChains {U : ι → Set X} (m : ℕ) {n : ℕ} {x : (singChains X).X n}
    (hx : x ∈ smallChains U n) : ((sdIterMap X m).f n).hom x ∈ smallChains U n := by
  induction m with
  | zero => simpa using hx
  | succ m ih =>
    rw [sdIterMap_f_succ]
    change (sdSing X n).hom (((sdIterMap X m).f n).hom x) ∈ _
    exact sdSing_mem_smallChains ih

/-! ### The iterated homotopy operator -/

/-- The chain homotopy `Σ_{i < m} sd ^ i ≫ T` between `sd ^ m` and the
identity. -/
def tdIter (X : TopCat.{0}) : ℕ → (n : ℕ) → ((singChains X).X n ⟶ (singChains X).X (n + 1)) :=
  Nat.rec (fun _ => 0) (fun m prev n => prev n + (sdIterMap X m).f n ≫ tdSing X n)

@[simp] lemma tdIter_zero (X : TopCat.{0}) (n : ℕ) : tdIter X 0 n = 0 := rfl

lemma tdIter_succ (X : TopCat.{0}) (m n : ℕ) :
    tdIter X (m + 1) n = tdIter X m n + (sdIterMap X m).f n ≫ tdSing X n := rfl

lemma tdIter_mem_smallChains {U : ι → Set X} (m : ℕ) {n : ℕ} {x : (singChains X).X n}
    (hx : x ∈ smallChains U n) : ((tdIter X m n).hom x) ∈ smallChains U (n + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [tdIter_succ]
    change ((tdIter X m n).hom x) + (tdSing X n).hom (((sdIterMap X m).f n).hom x) ∈ _
    exact Submodule.add_mem _ ih (tdSing_mem_smallChains (sdIterMap_mem_smallChains m hx))

/-- **The homotopy identity in degree zero.** -/
theorem tdIter_d_zero (X : TopCat.{0}) (m : ℕ) :
    tdIter X m 0 ≫ (singChains X).d 1 0 = 𝟙 _ - (sdIterMap X m).f 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [tdIter_succ, Preadditive.add_comp, ih, Category.assoc, tdSing_d_zero,
      sdIterMap_f_succ, Preadditive.comp_sub, Category.comp_id]
    abel

/-- **The homotopy identity `∂ D + D ∂ = 1 - sd ^ m`.** -/
theorem tdIter_d (X : TopCat.{0}) (m n : ℕ) :
    tdIter X m (n + 1) ≫ (singChains X).d (n + 2) (n + 1) +
        (singChains X).d (n + 1) n ≫ tdIter X m n =
      𝟙 _ - (sdIterMap X m).f (n + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hcomm : (sdIterMap X m).f (n + 1) ≫ (singChains X).d (n + 1) n =
        (singChains X).d (n + 1) n ≫ (sdIterMap X m).f n :=
      (sdIterMap X m).comm (n + 1) n
    have hkey : ((sdIterMap X m).f (n + 1) ≫ tdSing X (n + 1)) ≫
          (singChains X).d (n + 2) (n + 1) +
        (singChains X).d (n + 1) n ≫ ((sdIterMap X m).f n ≫ tdSing X n) =
        (sdIterMap X m).f (n + 1) - (sdIterMap X (m + 1)).f (n + 1) := by
      rw [Category.assoc,
        ← Category.assoc ((singChains X).d (n + 1) n) ((sdIterMap X m).f n) (tdSing X n),
        ← hcomm, Category.assoc, ← Preadditive.comp_add, tdSing_d,
        Preadditive.comp_sub, Category.comp_id, sdIterMap_f_succ]
    rw [tdIter_succ, tdIter_succ, Preadditive.add_comp, Preadditive.comp_add]
    calc (tdIter X m (n + 1) ≫ (singChains X).d (n + 2) (n + 1) +
            ((sdIterMap X m).f (n + 1) ≫ tdSing X (n + 1)) ≫
              (singChains X).d (n + 2) (n + 1)) +
          ((singChains X).d (n + 1) n ≫ tdIter X m n +
            (singChains X).d (n + 1) n ≫ ((sdIterMap X m).f n ≫ tdSing X n))
        = (tdIter X m (n + 1) ≫ (singChains X).d (n + 2) (n + 1) +
            (singChains X).d (n + 1) n ≫ tdIter X m n) +
          (((sdIterMap X m).f (n + 1) ≫ tdSing X (n + 1)) ≫
              (singChains X).d (n + 2) (n + 1) +
            (singChains X).d (n + 1) n ≫ ((sdIterMap X m).f n ≫ tdSing X n)) := by abel
      _ = (𝟙 _ - (sdIterMap X m).f (n + 1)) +
          ((sdIterMap X m).f (n + 1) - (sdIterMap X (m + 1)).f (n + 1)) := by rw [ih, hkey]
      _ = 𝟙 _ - (sdIterMap X (m + 1)).f (n + 1) := by abel

/-- The homotopy identity, applied to a cycle. -/
lemma d_tdIter_apply (m : ℕ) {n : ℕ} (z : (singChains X).X n)
    (hz : ∀ j, ((singChains X).d n j).hom z = 0) :
    ((singChains X).d (n + 1) n).hom ((tdIter X m n).hom z) =
      z - ((sdIterMap X m).f n).hom z := by
  cases n with
  | zero =>
    have h := congrArg (fun (g : (singChains X).X 0 ⟶ (singChains X).X 0) => g.hom z)
      (tdIter_d_zero X m)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sub,
      ModuleCat.hom_id, LinearMap.sub_apply, LinearMap.id_apply] using h
  | succ k =>
    have h := congrArg (fun (g : (singChains X).X (k + 1) ⟶ (singChains X).X (k + 1)) => g.hom z)
      (tdIter_d X m k)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add,
      ModuleCat.hom_sub, ModuleCat.hom_id, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.id_apply] at h
    rw [hz k, map_zero, add_zero] at h
    exact h

/-! ### The two halves of the small chain theorem -/

/-- **Every singular cycle is homologous to a small cycle.** -/
theorem exists_small_cycle_homologous (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcov : ∀ x : X, ∃ i, x ∈ U i) {n : ℕ} (z : (singChains X).X n)
    (hz : ∀ j, ((singChains X).d n j).hom z = 0) :
    ∃ z' : (singChains X).X n, z' ∈ smallChains U n ∧
      (∀ j, ((singChains X).d n j).hom z' = 0) ∧
      ∃ w : (singChains X).X (n + 1), z - z' = ((singChains X).d (n + 1) n).hom w := by
  obtain ⟨m, hm⟩ := exists_sdIterMap_mem_smallChains U hU hcov z
  refine ⟨((sdIterMap X m).f n).hom z, hm, fun j => ?_, (tdIter X m n).hom z, ?_⟩
  · have h := congrArg (fun (g : (singChains X).X n ⟶ (singChains X).X j) => g.hom z)
      ((sdIterMap X m).comm n j)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [h, hz j, map_zero]
  · rw [d_tdIter_apply m z hz]

/-- **A small cycle that bounds, bounds a small chain.** -/
theorem small_boundary_of_boundary (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcov : ∀ x : X, ∃ i, x ∈ U i) {n : ℕ} (z : (singChains X).X n)
    (hzs : z ∈ smallChains U n) (w : (singChains X).X (n + 1))
    (hw : ((singChains X).d (n + 1) n).hom w = z) :
    ∃ w' : (singChains X).X (n + 1), w' ∈ smallChains U (n + 1) ∧
      ((singChains X).d (n + 1) n).hom w' = z := by
  -- `z` is a cycle
  have hz : ∀ j, ((singChains X).d n j).hom z = 0 := by
    intro j
    rw [← hw]
    have h := congrArg (fun (g : (singChains X).X (n + 1) ⟶ (singChains X).X j) => g.hom w)
      (HomologicalComplex.d_comp_d (singChains X) (n + 1) n j)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h
  obtain ⟨m, hm⟩ := exists_sdIterMap_mem_smallChains U hU hcov w
  refine ⟨((sdIterMap X m).f (n + 1)).hom w + (tdIter X m n).hom z,
    Submodule.add_mem _ hm (tdIter_mem_smallChains m hzs), ?_⟩
  have h1 : ((singChains X).d (n + 1) n).hom (((sdIterMap X m).f (n + 1)).hom w) =
      ((sdIterMap X m).f n).hom z := by
    have h := congrArg (fun (g : (singChains X).X (n + 1) ⟶ (singChains X).X n) => g.hom w)
      ((sdIterMap X m).comm (n + 1) n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [h, hw]
  rw [map_add, h1, d_tdIter_apply m z hz]
  abel

end AffChain

end AffineTverberg
