import AffineTverberg.SingularSubdivision

set_option linter.style.header false

/-!
# Iterated subdivision and the metric estimates for small chains

This file continues the small-chain (excision) argument begun in
`AffineTverberg.SingularSubdivision`. It contains

* the iterated subdivision chain map `sdIterMap X m` together with an actual
  chain homotopy `sdIterHomotopy X m` to the identity, hence
  `homologyMap_sdIterMap`: every iterate induces the identity on singular
  homology;
* the two metric estimates on which the classical "subdivision makes simplices
  small" statement rests:
  `dist_affPoint_le` (an affine combination stays inside a ball around the
  vertices) and `dist_bary_le` (the barycentre of `n + 1` points of mutual
  distance at most `D` is at distance at most `n / (n + 1) * D` from each of
  them);
* the *hull* predicate `InHull` recording that a point is an affine
  combination of a given vertex tuple, with the closure properties used in the
  induction over the subdivision, and the resulting diameter estimate
  `dist_bary_inHull_le`.

## Continuation of the small-chain theorem

The mesh estimate itself is proved below (`sdHom_elt_mem_spanTuples`): one
barycentric subdivision of an affine `n`-simplex of diameter at most `D` is a
combination of affine `n`-simplices inside its hull, of diameter at most
`n / (n + 1) * D`. The following stages are now proved here and in the
subsequent modules:

1. `sdIterHom_elt_mem_spanTuples` below: `sd ^ m` is spanned by
   tuples of diameter at most `(n / (n + 1)) ^ m * D`, which tends to `0`;
2. `SmallSingular`: given an open cover of a space `X` and a singular
   simplex `σ : Δ n → X`, a Lebesgue number for the open cover
   `{σ ⁻¹' U}` of the compact metric space `Δ n` turns 1 into the statement
   that `sd ^ m σ` is a combination of singular simplices each of which has
   image in one member of the cover;
3. `SmallChainTheorem` and `SmallChainQuasiIso`: the inclusion of the subcomplex of
   cover-small chains into the singular chain complex is a quasi-isomorphism
   (for which 1 and 2 give the surjectivity half, together with the homotopy
   `tdSing` restricted to small chains).

Singular Mayer–Vietoris and the general simplicial-to-singular comparison
still require further arguments; none of these modules claims them.
-/

noncomputable section

open CategoryTheory Limits Simplicial
open scoped BigOperators

namespace AffineTverberg

namespace AffChain

/-! ### Iterated subdivision -/

/-- The `m`-fold barycentric subdivision as a chain map. -/
def sdIterMap (X : TopCat.{0}) : (m : ℕ) → (singChains X ⟶ singChains X) :=
  Nat.rec (𝟙 _) (fun _ prev => prev ≫ sdChainMap X)

@[simp] lemma sdIterMap_zero (X : TopCat.{0}) : sdIterMap X 0 = 𝟙 _ := rfl

lemma sdIterMap_succ (X : TopCat.{0}) (m : ℕ) :
    sdIterMap X (m + 1) = sdIterMap X m ≫ sdChainMap X := rfl

/-- **Every iterate of the barycentric subdivision is chain homotopic to the
identity.** -/
def sdIterHomotopy (X : TopCat.{0}) :
    (m : ℕ) → Homotopy (sdIterMap X m) (𝟙 (singChains X)) :=
  Nat.rec (Homotopy.refl _) (fun _m prev =>
    (prev.compRight (sdChainMap X)).trans
      ((Homotopy.ofEq (Category.id_comp (sdChainMap X))).trans (sdHomotopy X)))

/-- Every iterate of the subdivision induces the identity on singular
homology. -/
theorem homologyMap_sdIterMap (X : TopCat.{0}) (m n : ℕ) :
    HomologicalComplex.homologyMap (sdIterMap X m) n = 𝟙 _ := by
  rw [(sdIterHomotopy X m).homologyMap_eq, HomologicalComplex.homologyMap_id]

/-! ### Metric estimates -/

lemma dist_coord_le {k : ℕ} (x y : Δt k) (c : Fin (k + 1)) :
    |(x : Fin (k + 1) → ℝ) c - (y : Fin (k + 1) → ℝ) c| ≤ dist x y := by
  have h : dist ((x : Fin (k + 1) → ℝ) c) ((y : Fin (k + 1) → ℝ) c) ≤
      dist (x : Fin (k + 1) → ℝ) (y : Fin (k + 1) → ℝ) := dist_le_pi_dist _ _ c
  rwa [Real.dist_eq] at h

lemma dist_le_of_coords {k : ℕ} (x y : Δt k) (D : ℝ) (hD : 0 ≤ D)
    (h : ∀ c, |(x : Fin (k + 1) → ℝ) c - (y : Fin (k + 1) → ℝ) c| ≤ D) :
    dist x y ≤ D := by
  rw [Subtype.dist_eq]
  refine (dist_pi_le_iff hD).2 fun c => ?_
  rw [Real.dist_eq]
  exact h c

/-- An affine combination of points that are all within `D` of `y` is itself
within `D` of `y`. -/
theorem dist_affPoint_le {k j : ℕ} (y : Δt k) (v : Fin (j + 1) → Δt k) (t : Δt j)
    (D : ℝ) (hD : 0 ≤ D) (h : ∀ a, dist y (v a) ≤ D) :
    dist y (affPoint v t) ≤ D := by
  have hsum : ∑ a, t a = 1 := t.2.2
  have hnn : ∀ a, 0 ≤ t a := t.2.1
  refine dist_le_of_coords _ _ D hD fun c => ?_
  have hy : (y : Fin (k + 1) → ℝ) c = ∑ a, t a * (y : Fin (k + 1) → ℝ) c := by
    rw [← Finset.sum_mul, hsum, one_mul]
  have hp : (affPoint v t : Fin (k + 1) → ℝ) c = ∑ a, t a * (v a) c := affPoint_apply v t c
  rw [hy, hp, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hbound : ∀ a ∈ Finset.univ,
      |t a * (y : Fin (k + 1) → ℝ) c - t a * (v a) c| ≤ t a * D := by
    intro a _
    rw [← mul_sub, abs_mul, abs_of_nonneg (hnn a)]
    exact mul_le_mul_of_nonneg_left ((dist_coord_le y (v a) c).trans (h a)) (hnn a)
  refine (Finset.sum_le_sum hbound).trans ?_
  rw [← Finset.sum_mul, hsum, one_mul]

/-- **The barycentre estimate**: the barycentre of `n + 1` points of mutual
distance at most `D` is at distance at most `n / (n + 1) * D` from each of
them. -/
theorem dist_bary_le {k n : ℕ} (v : Fin (n + 1) → Δt k) (D : ℝ) (hD : 0 ≤ D)
    (h : ∀ a b, dist (v a) (v b) ≤ D) (i : Fin (n + 1)) :
    dist (bary v) (v i) ≤ (n : ℝ) / ((n : ℝ) + 1) * D := by
  classical
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine dist_le_of_coords _ _ _ (by positivity) fun c => ?_
  have hb : (bary v : Fin (k + 1) → ℝ) c = ∑ a, ((n : ℝ) + 1)⁻¹ * (v a) c := by
    rw [bary, affPoint_apply]
    rfl
  have hvi : (v i : Fin (k + 1) → ℝ) c
      = ∑ _a : Fin (n + 1), ((n : ℝ) + 1)⁻¹ * (v i : Fin (k + 1) → ℝ) c := by
    rw [← Finset.sum_mul]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  rw [hb, hvi, ← Finset.sum_sub_distrib]
  have hterm : ∀ a ∈ Finset.univ,
      |((n : ℝ) + 1)⁻¹ * (v a) c - ((n : ℝ) + 1)⁻¹ * (v i) c| ≤
        if a = i then 0 else ((n : ℝ) + 1)⁻¹ * D := by
    intro a _
    by_cases ha : a = i
    · subst ha; simp
    · rw [ite_eq_right ha, ← mul_sub, abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ ((n:ℝ) + 1)⁻¹)]
      exact mul_le_mul_of_nonneg_left ((dist_coord_le (v a) (v i) c).trans (h a i))
        (by positivity)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  have hcount : ∑ a : Fin (n + 1), (if a = i then (0 : ℝ) else ((n : ℝ) + 1)⁻¹ * D)
      = (n : ℝ) * (((n : ℝ) + 1)⁻¹ * D) := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
    have h1 : (Finset.univ.filter (fun a : Fin (n + 1) => a = i)) = {i} := by
      ext a; simp
    have h2 : (Finset.univ.filter (fun a : Fin (n + 1) => ¬ a = i)) = Finset.univ.erase i := by
      ext a; simp [Finset.mem_erase, and_comm]
    rw [h1, h2, Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_fin, smul_zero,
      zero_add, nsmul_eq_mul, Nat.add_sub_cancel]
  rw [hcount]
  apply le_of_eq
  field_simp

/-! ### The hull of a vertex tuple -/

/-- A point of the standard simplex is in the hull of a vertex tuple if it is
an affine combination of its entries. -/
def InHull {k j : ℕ} (v : Fin (j + 1) → Δt k) (x : Δt k) : Prop :=
  ∃ t : Δt j, x = affPoint v t

lemma inHull_self {k j : ℕ} (v : Fin (j + 1) → Δt k) (a : Fin (j + 1)) : InHull v (v a) :=
  ⟨stdSimplex.vertex a, (affPoint_vertex v a).symm⟩

lemma inHull_bary {k j : ℕ} (v : Fin (j + 1) → Δt k) : InHull v (bary v) := ⟨center j, rfl⟩

lemma inHull_affPoint {k j i : ℕ} (v : Fin (j + 1) → Δt k) (w : Fin (i + 1) → Δt k)
    (hw : ∀ a, InHull v (w a)) (t : Δt i) : InHull v (affPoint w t) := by
  choose s hs using hw
  refine ⟨affPoint s t, ?_⟩
  rw [affPoint_comp v s t]
  exact congrArg (fun u : Fin (i + 1) → Δt k => affPoint u t) (funext hs)

/-- Every point of the hull of a tuple of mutual distance at most `D` is within
`n / (n + 1) * D` of the barycentre. -/
theorem dist_bary_inHull_le {k n : ℕ} (v : Fin (n + 1) → Δt k) (D : ℝ) (hD : 0 ≤ D)
    (h : ∀ a b, dist (v a) (v b) ≤ D) {x : Δt k} (hx : InHull v x) :
    dist (bary v) x ≤ (n : ℝ) / ((n : ℝ) + 1) * D := by
  obtain ⟨t, rfl⟩ := hx
  exact dist_affPoint_le (bary v) v t _ (by positivity) (fun a => dist_bary_le v D hD h a)

/-! ### The support of the subdivision: the mesh estimate

The elements `elt w` (the basis elements of the affine chain groups) span the
chain group; the subdivision of a simplex is supported on tuples that stay
inside the hull of the original simplex and whose diameter has shrunk by the
factor `n / (n + 1)`. This is the genuine mesh estimate for barycentric
subdivision.
-/

/-- The basis element of the affine chain group attached to a vertex tuple. -/
def elt {k n : ℕ} (w : Fin (n + 1) → Δt k) : (affChains k).X n := (ιa w).hom (1 : ℝ)

/-- The submodule of affine chains spanned by the tuples satisfying `P`. -/
def spanTuples {k n : ℕ} (P : (Fin (n + 1) → Δt k) → Prop) : Submodule ℝ ((affChains k).X n) :=
  Submodule.span ℝ {x | ∃ w, P w ∧ x = elt w}

lemma elt_mem_spanTuples {k n : ℕ} {P : (Fin (n + 1) → Δt k) → Prop} {w} (h : P w) :
    elt w ∈ spanTuples P :=
  Submodule.subset_span ⟨w, h, rfl⟩

lemma spanTuples_mono {k n : ℕ} {P Q : (Fin (n + 1) → Δt k) → Prop} (h : ∀ w, P w → Q w) :
    spanTuples P ≤ spanTuples Q := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨w, hw, rfl⟩
  exact elt_mem_spanTuples (h w hw)

lemma map_mem_of_mem_spanTuples {k n : ℕ} {Z : ModuleCat.{0} ℝ} {P : (Fin (n + 1) → Δt k) → Prop}
    (f : (affChains k).X n ⟶ Z) {T : Submodule ℝ Z}
    (h : ∀ w, P w → f.hom (elt w) ∈ T) {x : (affChains k).X n} (hx : x ∈ spanTuples P) :
    f.hom x ∈ T := by
  have hle : spanTuples P ≤ T.comap f.hom := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨w, hw, rfl⟩
    exact h w hw
  exact hle hx

lemma elt_coneHom {k n : ℕ} (b : Δt k) (w : Fin (n + 1) → Δt k) :
    (coneHom b n).hom (elt w) = elt (Fin.cons b w) := by
  have h2 := congrArg (fun (g : ModuleCat.of ℝ ℝ ⟶ (affChains k).X (n + 1)) => g.hom (1 : ℝ))
    (ιa_coneHom b w)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2

lemma elt_d {k n : ℕ} (v : Fin (n + 2) → Δt k) :
    ((affChains k).d (n + 1) n).hom (elt v) =
      ∑ i : Fin (n + 2), (-1 : ℝ) ^ (i : ℕ) • elt (v ∘ i.succAbove) := by
  have h := ιa_d v
  have h2 := congrArg (fun (g : ModuleCat.of ℝ ℝ ⟶ (affChains k).X n) => g.hom (1 : ℝ)) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [show ((∑ i : Fin (n + 2), (-1 : ℝ) ^ (i : ℕ) • ιa (v ∘ i.succAbove)).hom (1 : ℝ)) =
      ∑ i : Fin (n + 2), (-1 : ℝ) ^ (i : ℕ) • ((ιa (v ∘ i.succAbove)).hom (1 : ℝ)) by
    simp] at h2
  exact h2

lemma elt_sdHom_succ {k n : ℕ} (v : Fin (n + 2) → Δt k) :
    (sdHom k (n + 1)).hom (elt v) =
      (coneHom (bary v) n).hom ((sdHom k n).hom
        (((affChains k).d (n + 1) n).hom (elt v))) := by
  have h2 := congrArg (fun (g : ModuleCat.of ℝ ℝ ⟶ (affChains k).X (n + 1)) => g.hom (1 : ℝ))
    (ιa_sdHom_succ v)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2

/-- Points of the hull of a face are in the hull of the whole simplex. -/
lemma inHull_face {k n : ℕ} (v : Fin (n + 2) → Δt k) (i : Fin (n + 2)) {x : Δt k}
    (hx : InHull (v ∘ i.succAbove) x) : InHull v x := by
  obtain ⟨t, rfl⟩ := hx
  exact ⟨stdSimplex.map i.succAbove t, affPoint_map v i.succAbove t⟩

lemma ratio_mono (n : ℕ) : (n : ℝ) / ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) / ((n : ℝ) + 1 + 1) := by
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (n : ℝ) + 1 + 1 := by positivity
  rw [div_le_div_iff₀ h1 h2]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- **The mesh estimate for barycentric subdivision.** The subdivision of an
affine `n`-simplex `v` of diameter at most `D` is a linear combination of affine
`n`-simplices whose vertices lie in the hull of `v` and whose diameter is at
most `n / (n + 1) * D`. -/
theorem sdHom_elt_mem_spanTuples {k : ℕ} :
    ∀ (n : ℕ) (v : Fin (n + 1) → Δt k) (D : ℝ), 0 ≤ D → (∀ a b, dist (v a) (v b) ≤ D) →
      (sdHom k n).hom (elt v) ∈ spanTuples (fun w : Fin (n + 1) → Δt k =>
        (∀ a, InHull v (w a)) ∧ ∀ a b, dist (w a) (w b) ≤ (n : ℝ) / ((n : ℝ) + 1) * D) := by
  intro n
  induction n with
  | zero =>
    intro v D hD _
    rw [sdHom_zero]
    refine elt_mem_spanTuples ⟨fun a => inHull_self v a, fun a b => ?_⟩
    have hab : a = b := by
      have ha := a.isLt
      have hb := b.isLt
      exact Fin.ext (by omega)
    rw [hab, dist_self]
    simp
  | succ m ih =>
    intro v D hD hdiam
    rw [elt_sdHom_succ, elt_d]
    -- the boundary lies in the span of the faces
    have hbd : ∑ i : Fin (m + 2), (-1 : ℝ) ^ (i : ℕ) • elt (v ∘ i.succAbove) ∈
        spanTuples (fun u : Fin (m + 1) → Δt k => ∃ i : Fin (m + 2), u = v ∘ i.succAbove) := by
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      exact elt_mem_spanTuples ⟨i, rfl⟩
    -- the subdivision of each face has small support
    set Q : (Fin (m + 1) → Δt k) → Prop := fun w =>
      (∀ a, InHull v (w a)) ∧
        ∀ a b, dist (w a) (w b) ≤ ((m : ℝ) + 1) / (((m : ℝ) + 1) + 1) * D with hQ
    have hface : ∀ u : Fin (m + 1) → Δt k, (∃ i : Fin (m + 2), u = v ∘ i.succAbove) →
        (sdHom k m).hom (elt u) ∈ spanTuples Q := by
      rintro u ⟨i, rfl⟩
      have hd' : ∀ a b, dist ((v ∘ i.succAbove) a) ((v ∘ i.succAbove) b) ≤ D :=
        fun a b => hdiam _ _
      refine le_trans (spanTuples_mono (P := fun w : Fin (m + 1) → Δt k =>
          (∀ a, InHull (v ∘ i.succAbove) (w a)) ∧
            ∀ a b, dist (w a) (w b) ≤ (m : ℝ) / ((m : ℝ) + 1) * D) ?_) le_rfl
        (ih (v ∘ i.succAbove) D hD hd')
      rintro w ⟨hw1, hw2⟩
      refine ⟨fun a => inHull_face v i (hw1 a), fun a b => (hw2 a b).trans ?_⟩
      exact mul_le_mul_of_nonneg_right (ratio_mono m) hD
    have hsub : (sdHom k m).hom
        (∑ i : Fin (m + 2), (-1 : ℝ) ^ (i : ℕ) • elt (v ∘ i.succAbove)) ∈ spanTuples Q :=
      map_mem_of_mem_spanTuples _ hface hbd
    -- coning with the barycentre keeps the estimate
    refine map_mem_of_mem_spanTuples (P := Q) (coneHom (bary v) m) ?_ hsub
    rintro w ⟨hw1, hw2⟩
    rw [elt_coneHom]
    refine elt_mem_spanTuples ⟨fun a => ?_, fun a b => ?_⟩
    · induction a using Fin.cases with
      | zero => simpa using inHull_bary v
      | succ a => simpa using hw1 a
    · have hbaryest : ∀ x : Δt k, InHull v x →
          dist (bary v) x ≤ ((m : ℝ) + 1) / (((m : ℝ) + 1) + 1) * D := by
        intro x hx
        have := dist_bary_inHull_le v D hD hdiam hx
        simpa using this
      induction a using Fin.cases with
      | zero =>
        induction b using Fin.cases with
        | zero => simpa using by positivity
        | succ b => simpa using hbaryest (w b) (hw1 b)
      | succ a =>
        induction b using Fin.cases with
        | zero =>
          rw [dist_comm]
          simpa using hbaryest (w a) (hw1 a)
        | succ b => simpa using hw2 a b

/-! ### Iterating the mesh estimate -/

/-- The `m`-fold barycentric subdivision operator on affine chains. -/
def sdIterHom (k : ℕ) : ℕ → (n : ℕ) → ((affChains k).X n ⟶ (affChains k).X n) :=
  Nat.rec (fun _ => 𝟙 _) (fun _ prev n => prev n ≫ sdHom k n)

@[simp] lemma sdIterHom_zero (k n : ℕ) : sdIterHom k 0 n = 𝟙 _ := rfl

lemma sdIterHom_succ (k m n : ℕ) :
    sdIterHom k (m + 1) n = sdIterHom k m n ≫ sdHom k n := rfl

/-- Membership in the hull is transitive. -/
lemma inHull_trans {k n j : ℕ} (v : Fin (n + 1) → Δt k) (w : Fin (j + 1) → Δt k)
    (hw : ∀ a, InHull v (w a)) {x : Δt k} (hx : InHull w x) : InHull v x := by
  obtain ⟨t, rfl⟩ := hx
  exact inHull_affPoint v w hw t

/-- **The iterated mesh estimate.** The `m`-fold barycentric subdivision of an
affine `n`-simplex `v` of diameter at most `D` is a linear combination of
affine `n`-simplices whose vertices lie in the hull of `v` and whose diameter
is at most `(n / (n + 1)) ^ m * D`. -/
theorem sdIterHom_elt_mem_spanTuples {k n : ℕ} :
    ∀ (m : ℕ) (v : Fin (n + 1) → Δt k) (D : ℝ), 0 ≤ D → (∀ a b, dist (v a) (v b) ≤ D) →
      (sdIterHom k m n).hom (elt v) ∈ spanTuples (fun w : Fin (n + 1) → Δt k =>
        (∀ a, InHull v (w a)) ∧
          ∀ a b, dist (w a) (w b) ≤ ((n : ℝ) / ((n : ℝ) + 1)) ^ m * D) := by
  intro m
  induction m with
  | zero =>
    intro v D _ hdiam
    refine elt_mem_spanTuples ⟨fun a => inHull_self v a, fun a b => ?_⟩
    simpa using hdiam a b
  | succ m ih =>
    intro v D hD hdiam
    have hr : (0 : ℝ) ≤ (n : ℝ) / ((n : ℝ) + 1) := by positivity
    rw [sdIterHom_succ]
    change (sdHom k n).hom ((sdIterHom k m n).hom (elt v)) ∈ _
    refine map_mem_of_mem_spanTuples (sdHom k n) ?_ (ih v D hD hdiam)
    rintro w ⟨hw1, hw2⟩
    have hDm : (0 : ℝ) ≤ ((n : ℝ) / ((n : ℝ) + 1)) ^ m * D := by positivity
    refine le_trans (spanTuples_mono (P := fun u : Fin (n + 1) → Δt k =>
        (∀ a, InHull w (u a)) ∧
          ∀ a b, dist (u a) (u b) ≤
            (n : ℝ) / ((n : ℝ) + 1) * (((n : ℝ) / ((n : ℝ) + 1)) ^ m * D)) ?_) le_rfl
      (sdHom_elt_mem_spanTuples n w _ hDm hw2)
    rintro u ⟨hu1, hu2⟩
    refine ⟨fun a => inHull_trans v w hw1 (hu1 a), fun a b => (hu2 a b).trans (le_of_eq ?_)⟩
    ring

end AffChain

end AffineTverberg
