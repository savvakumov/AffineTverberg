import AffineTverberg.CoefficientSmallSingular
import AffineTverberg.SmallChainTheorem

set_option linter.style.header false

/-!
# The small-chain theorem with arbitrary field coefficients

This is the actual small-chain argument over any field. All cycles, boundaries
and induced homology maps refer to Mathlib's singular chain complex; no
vanishing or comparison premise is built into the definitions.
-/

noncomputable section

open CategoryTheory Limits Simplicial Metric AffineTverberg.AffChain
open scoped BigOperators

namespace AffineTverberg.Coefficients.AffChain

variable (𝕜 : Type) [Field 𝕜]
variable {X : TopCat.{0}} {ι : Type}

/-! ### Affine chains are spanned by their basis elements -/

lemma affChains_span_elt (k n : ℕ) :
    Submodule.span 𝕜 (Set.range (fun w : Fin (n + 1) → Δt k => elt 𝕜 w)) = ⊤ := by
  set S := Submodule.span 𝕜 (Set.range (fun w : Fin (n + 1) → Δt k => elt 𝕜 w)) with hS
  have hmem : ∀ (w : Fin (n + 1) → Δt k) (r : 𝕜), (ιa 𝕜 w).hom r ∈ S := by
    intro w r
    have hr : (ιa 𝕜 w).hom r = r • elt 𝕜 w := by
      rw [elt, ← map_smul]
      congr 1
      simp
    rw [hr]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self w))
  have hq : (ModuleCat.ofHom S.mkQ :
      (affChains 𝕜 k).X n ⟶ ModuleCat.of 𝕜 (((affChains 𝕜 k).X n) ⧸ S)) = 0 := by
    refine affChains_hom_ext 𝕜 fun w => ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
    change S.mkQ ((ιa 𝕜 w).hom r) = (0 : ((affChains 𝕜 k).X n) ⧸ S)
    exact (Submodule.Quotient.mk_eq_zero _).2 (hmem w r)
  refine eq_top_iff.2 fun x _ => ?_
  have hx := congrArg (fun (g : (affChains 𝕜 k).X n ⟶
    ModuleCat.of 𝕜 (((affChains 𝕜 k).X n) ⧸ S)) => g.hom x) hq
  exact (Submodule.Quotient.mk_eq_zero _).1 hx

/-! ### Smallness is inherited by everything realized along a small simplex -/

/-- Everything realized along a singular simplex with image in one member of
the cover is a small chain. -/
lemma realChain_mem_smallChains {U : ι → Set X} {n j : ℕ} {σ : C(Δt n, X)} {i : ι}
    (hσ : ∀ t, σ t ∈ U i) (y : (affChains 𝕜 n).X j) :
    ((realChain 𝕜 σ).f j).hom y ∈ smallChains 𝕜 U j := by
  have hy : y ∈ Submodule.span 𝕜 (Set.range (fun w : Fin (j + 1) → Δt n => elt 𝕜 w)) := by
    rw [affChains_span_elt 𝕜]; trivial
  induction hy using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨w, rfl⟩ := ha
    rw [realChain_sElt 𝕜]
    exact sElt_mem_smallChains 𝕜 (i := i) fun t => hσ _
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

/-- To check that a map preserves small chains it suffices to check it on
small basis chains. -/
lemma smallChains_map {U : ι → Set X} {n j : ℕ}
    (f : (singChains 𝕜 X).X n ⟶ (singChains 𝕜 X).X j)
    (h : ∀ (σ : C(Δt n, X)) (i : ι), (∀ t, σ t ∈ U i) → f.hom (sElt 𝕜 σ) ∈ smallChains 𝕜 U j)
    {x : (singChains 𝕜 X).X n} (hx : x ∈ smallChains 𝕜 U n) : f.hom x ∈ smallChains 𝕜 U j := by
  have hle : smallChains 𝕜 U n ≤ (smallChains 𝕜 U j).comap f.hom := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨σ, i, hσ, rfl⟩
    exact h σ i hσ
  exact hle hx

lemma sdSing_sElt {n : ℕ} (σ : C(Δt n, X)) :
    (sdSing 𝕜 X n).hom (sElt 𝕜 σ) =
      ((realChain 𝕜 σ).f n).hom ((sdHom 𝕜 n n).hom (elt 𝕜 (idTuple n))) := by
  rw [sElt_eq_realChain_elt 𝕜]
  have h := congrArg (fun (g : (affChains 𝕜 n).X n ⟶ (singChains 𝕜 X).X n) =>
    g.hom (elt 𝕜 (idTuple n))) (realChain_sdSing 𝕜 (n := n) σ)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

lemma tdSing_sElt {n : ℕ} (σ : C(Δt n, X)) :
    (tdSing 𝕜 X n).hom (sElt 𝕜 σ) =
      ((realChain 𝕜 σ).f (n + 1)).hom ((tdHom 𝕜 n n).hom (elt 𝕜 (idTuple n))) := by
  have h := congrArg (fun (g : ModuleCat.of 𝕜 𝕜 ⟶ (singChains 𝕜 X).X (n + 1)) => g.hom (1 : 𝕜))
    (ιs_tdSing 𝕜 σ)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, sElt, elt] using h

/-- The subdivision operator preserves small chains. -/
lemma sdSing_mem_smallChains {U : ι → Set X} {n : ℕ} {x : (singChains 𝕜 X).X n}
    (hx : x ∈ smallChains 𝕜 U n) : (sdSing 𝕜 X n).hom x ∈ smallChains 𝕜 U n := by
  refine smallChains_map 𝕜 _ (fun σ i hσ => ?_) hx
  rw [sdSing_sElt 𝕜]
  exact realChain_mem_smallChains 𝕜 hσ _

/-- The homotopy operator preserves small chains. -/
lemma tdSing_mem_smallChains {U : ι → Set X} {n : ℕ} {x : (singChains 𝕜 X).X n}
    (hx : x ∈ smallChains 𝕜 U n) : (tdSing 𝕜 X n).hom x ∈ smallChains 𝕜 U (n + 1) := by
  refine smallChains_map 𝕜 _ (fun σ i hσ => ?_) hx
  rw [tdSing_sElt 𝕜]
  exact realChain_mem_smallChains 𝕜 hσ _

lemma sdIterMap_f_succ (X : TopCat.{0}) (m n : ℕ) :
    (sdIterMap 𝕜 X (m + 1)).f n = (sdIterMap 𝕜 X m).f n ≫ sdSing 𝕜 X n := rfl

lemma sdIterMap_mem_smallChains {U : ι → Set X} (m : ℕ) {n : ℕ} {x : (singChains 𝕜 X).X n}
    (hx : x ∈ smallChains 𝕜 U n) : ((sdIterMap 𝕜 X m).f n).hom x ∈ smallChains 𝕜 U n := by
  induction m with
  | zero => simpa using hx
  | succ m ih =>
    rw [sdIterMap_f_succ 𝕜]
    change (sdSing 𝕜 X n).hom (((sdIterMap 𝕜 X m).f n).hom x) ∈ _
    exact sdSing_mem_smallChains 𝕜 ih

/-! ### The iterated homotopy operator -/

/-- The chain homotopy `Σ_{i < m} sd ^ i ≫ T` between `sd ^ m` and the
identity. -/
def tdIter (X : TopCat.{0}) : ℕ → (n : ℕ) → ((singChains 𝕜 X).X n ⟶ (singChains 𝕜 X).X (n + 1)) :=
  Nat.rec (fun _ => 0) (fun m prev n => prev n + (sdIterMap 𝕜 X m).f n ≫ tdSing 𝕜 X n)

@[simp] lemma tdIter_zero (X : TopCat.{0}) (n : ℕ) : tdIter 𝕜 X 0 n = 0 := rfl

lemma tdIter_succ (X : TopCat.{0}) (m n : ℕ) :
    tdIter 𝕜 X (m + 1) n = tdIter 𝕜 X m n + (sdIterMap 𝕜 X m).f n ≫ tdSing 𝕜 X n := rfl

lemma tdIter_mem_smallChains {U : ι → Set X} (m : ℕ) {n : ℕ} {x : (singChains 𝕜 X).X n}
    (hx : x ∈ smallChains 𝕜 U n) : ((tdIter 𝕜 X m n).hom x) ∈ smallChains 𝕜 U (n + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [tdIter_succ 𝕜]
    change ((tdIter 𝕜 X m n).hom x) + (tdSing 𝕜 X n).hom (((sdIterMap 𝕜 X m).f n).hom x) ∈ _
    exact Submodule.add_mem _ ih (tdSing_mem_smallChains 𝕜 (sdIterMap_mem_smallChains 𝕜 m hx))

/-- **The homotopy identity in degree zero.** -/
theorem tdIter_d_zero (X : TopCat.{0}) (m : ℕ) :
    tdIter 𝕜 X m 0 ≫ (singChains 𝕜 X).d 1 0 = 𝟙 _ - (sdIterMap 𝕜 X m).f 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [tdIter_succ 𝕜, Preadditive.add_comp, ih, Category.assoc, tdSing_d_zero 𝕜,
      sdIterMap_f_succ 𝕜, Preadditive.comp_sub, Category.comp_id]
    abel

/-- **The homotopy identity `∂ D + D ∂ = 1 - sd ^ m`.** -/
theorem tdIter_d (X : TopCat.{0}) (m n : ℕ) :
    tdIter 𝕜 X m (n + 1) ≫ (singChains 𝕜 X).d (n + 2) (n + 1) +
        (singChains 𝕜 X).d (n + 1) n ≫ tdIter 𝕜 X m n =
      𝟙 _ - (sdIterMap 𝕜 X m).f (n + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hcomm : (sdIterMap 𝕜 X m).f (n + 1) ≫ (singChains 𝕜 X).d (n + 1) n =
        (singChains 𝕜 X).d (n + 1) n ≫ (sdIterMap 𝕜 X m).f n :=
      (sdIterMap 𝕜 X m).comm (n + 1) n
    have hkey : ((sdIterMap 𝕜 X m).f (n + 1) ≫ tdSing 𝕜 X (n + 1)) ≫
          (singChains 𝕜 X).d (n + 2) (n + 1) +
        (singChains 𝕜 X).d (n + 1) n ≫ ((sdIterMap 𝕜 X m).f n ≫ tdSing 𝕜 X n) =
        (sdIterMap 𝕜 X m).f (n + 1) - (sdIterMap 𝕜 X (m + 1)).f (n + 1) := by
      rw [Category.assoc,
        ← Category.assoc ((singChains 𝕜 X).d (n + 1) n) ((sdIterMap 𝕜 X m).f n) (tdSing 𝕜 X n),
        ← hcomm, Category.assoc, ← Preadditive.comp_add, tdSing_d 𝕜,
        Preadditive.comp_sub, Category.comp_id, sdIterMap_f_succ 𝕜]
    rw [tdIter_succ 𝕜, tdIter_succ 𝕜, Preadditive.add_comp, Preadditive.comp_add]
    calc (tdIter 𝕜 X m (n + 1) ≫ (singChains 𝕜 X).d (n + 2) (n + 1) +
            ((sdIterMap 𝕜 X m).f (n + 1) ≫ tdSing 𝕜 X (n + 1)) ≫
              (singChains 𝕜 X).d (n + 2) (n + 1)) +
          ((singChains 𝕜 X).d (n + 1) n ≫ tdIter 𝕜 X m n +
            (singChains 𝕜 X).d (n + 1) n ≫ ((sdIterMap 𝕜 X m).f n ≫ tdSing 𝕜 X n))
        = (tdIter 𝕜 X m (n + 1) ≫ (singChains 𝕜 X).d (n + 2) (n + 1) +
            (singChains 𝕜 X).d (n + 1) n ≫ tdIter 𝕜 X m n) +
          (((sdIterMap 𝕜 X m).f (n + 1) ≫ tdSing 𝕜 X (n + 1)) ≫
              (singChains 𝕜 X).d (n + 2) (n + 1) +
            (singChains 𝕜 X).d (n + 1) n ≫ ((sdIterMap 𝕜 X m).f n ≫ tdSing 𝕜 X n)) := by abel
      _ = (𝟙 _ - (sdIterMap 𝕜 X m).f (n + 1)) +
          ((sdIterMap 𝕜 X m).f (n + 1) - (sdIterMap 𝕜 X (m + 1)).f (n + 1)) := by rw [ih, hkey]
      _ = 𝟙 _ - (sdIterMap 𝕜 X (m + 1)).f (n + 1) := by abel

/-- The homotopy identity, applied to a cycle. -/
lemma d_tdIter_apply (m : ℕ) {n : ℕ} (z : (singChains 𝕜 X).X n)
    (hz : ∀ j, ((singChains 𝕜 X).d n j).hom z = 0) :
    ((singChains 𝕜 X).d (n + 1) n).hom ((tdIter 𝕜 X m n).hom z) =
      z - ((sdIterMap 𝕜 X m).f n).hom z := by
  cases n with
  | zero =>
    have h := congrArg (fun (g : (singChains 𝕜 X).X 0 ⟶ (singChains 𝕜 X).X 0) => g.hom z)
      (tdIter_d_zero 𝕜 X m)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sub,
      ModuleCat.hom_id, LinearMap.sub_apply, LinearMap.id_apply] using h
  | succ k =>
    have h := congrArg
      (fun (g : (singChains 𝕜 X).X (k + 1) ⟶ (singChains 𝕜 X).X (k + 1)) => g.hom z)
      (tdIter_d 𝕜 X m k)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add,
      ModuleCat.hom_sub, ModuleCat.hom_id, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.id_apply] at h
    rw [hz k, map_zero, add_zero] at h
    exact h

/-! ### The two halves of the small chain theorem -/

/-- **Every singular cycle is homologous to a small cycle.** -/
theorem exists_small_cycle_homologous (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcov : ∀ x : X, ∃ i, x ∈ U i) {n : ℕ} (z : (singChains 𝕜 X).X n)
    (hz : ∀ j, ((singChains 𝕜 X).d n j).hom z = 0) :
    ∃ z' : (singChains 𝕜 X).X n, z' ∈ smallChains 𝕜 U n ∧
      (∀ j, ((singChains 𝕜 X).d n j).hom z' = 0) ∧
      ∃ w : (singChains 𝕜 X).X (n + 1), z - z' = ((singChains 𝕜 X).d (n + 1) n).hom w := by
  obtain ⟨m, hm⟩ := exists_sdIterMap_mem_smallChains 𝕜 U hU hcov z
  refine ⟨((sdIterMap 𝕜 X m).f n).hom z, hm, fun j => ?_, (tdIter 𝕜 X m n).hom z, ?_⟩
  · have h := congrArg (fun (g : (singChains 𝕜 X).X n ⟶ (singChains 𝕜 X).X j) => g.hom z)
      ((sdIterMap 𝕜 X m).comm n j)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [h, hz j, map_zero]
  · rw [d_tdIter_apply 𝕜 m z hz]

/-- **A small cycle that bounds, bounds a small chain.** -/
theorem small_boundary_of_boundary (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcov : ∀ x : X, ∃ i, x ∈ U i) {n : ℕ} (z : (singChains 𝕜 X).X n)
    (hzs : z ∈ smallChains 𝕜 U n) (w : (singChains 𝕜 X).X (n + 1))
    (hw : ((singChains 𝕜 X).d (n + 1) n).hom w = z) :
    ∃ w' : (singChains 𝕜 X).X (n + 1), w' ∈ smallChains 𝕜 U (n + 1) ∧
      ((singChains 𝕜 X).d (n + 1) n).hom w' = z := by
  -- `z` is a cycle
  have hz : ∀ j, ((singChains 𝕜 X).d n j).hom z = 0 := by
    intro j
    rw [← hw]
    have h := congrArg (fun (g : (singChains 𝕜 X).X (n + 1) ⟶ (singChains 𝕜 X).X j) => g.hom w)
      (HomologicalComplex.d_comp_d (singChains 𝕜 X) (n + 1) n j)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h
  obtain ⟨m, hm⟩ := exists_sdIterMap_mem_smallChains 𝕜 U hU hcov w
  refine ⟨((sdIterMap 𝕜 X m).f (n + 1)).hom w + (tdIter 𝕜 X m n).hom z,
    Submodule.add_mem _ hm (tdIter_mem_smallChains 𝕜 m hzs), ?_⟩
  have h1 : ((singChains 𝕜 X).d (n + 1) n).hom (((sdIterMap 𝕜 X m).f (n + 1)).hom w) =
      ((sdIterMap 𝕜 X m).f n).hom z := by
    have h := congrArg (fun (g : (singChains 𝕜 X).X (n + 1) ⟶ (singChains 𝕜 X).X n) => g.hom w)
      ((sdIterMap 𝕜 X m).comm (n + 1) n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [h, hw]
  rw [map_add, h1, d_tdIter_apply 𝕜 m z hz]
  abel

end AffineTverberg.Coefficients.AffChain
