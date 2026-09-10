import AffineTverberg.CoefficientSingularSubdivision
import AffineTverberg.SmallChains

set_option linter.style.header false

/-!
# Small affine chains over arbitrary fields

Subdivision and its iterates are supported on real affine simplices of shrinking
mesh, independently of the field used for their coefficients. The existing real
metric estimates are reused unchanged.
-/

noncomputable section

open CategoryTheory Limits Simplicial AffineTverberg.AffChain
open scoped BigOperators

namespace AffineTverberg.Coefficients.AffChain

variable (𝕜 : Type) [Field 𝕜]

/-- The `m`-fold barycentric subdivision as a chain map. -/
def sdIterMap (X : TopCat.{0}) : (m : ℕ) → (singChains 𝕜 X ⟶ singChains 𝕜 X) :=
  Nat.rec (𝟙 _) (fun _ prev => prev ≫ sdChainMap 𝕜 X)

@[simp] lemma sdIterMap_zero (X : TopCat.{0}) : sdIterMap 𝕜 X 0 = 𝟙 _ := rfl

lemma sdIterMap_succ (X : TopCat.{0}) (m : ℕ) :
    sdIterMap 𝕜 X (m + 1) = sdIterMap 𝕜 X m ≫ sdChainMap 𝕜 X := rfl

/-- **Every iterate of the barycentric subdivision is chain homotopic to the
identity.** -/
def sdIterHomotopy (X : TopCat.{0}) :
    (m : ℕ) → Homotopy (sdIterMap 𝕜 X m) (𝟙 (singChains 𝕜 X)) :=
  Nat.rec (Homotopy.refl _) (fun _m prev =>
    (prev.compRight (sdChainMap 𝕜 X)).trans
      ((Homotopy.ofEq (Category.id_comp (sdChainMap 𝕜 X))).trans (sdHomotopy 𝕜 X)))

/-- Every iterate of the subdivision induces the identity on singular
homology. -/
theorem homologyMap_sdIterMap (X : TopCat.{0}) (m n : ℕ) :
    HomologicalComplex.homologyMap (sdIterMap 𝕜 X m) n = 𝟙 _ := by
  rw [(sdIterHomotopy 𝕜 X m).homologyMap_eq, HomologicalComplex.homologyMap_id]

/-- The basis element of the affine chain group attached to a vertex tuple. -/
def elt {k n : ℕ} (w : Fin (n + 1) → Δt k) : (affChains 𝕜 k).X n := (ιa 𝕜 w).hom (1 : 𝕜)

/-- The submodule of affine chains spanned by the tuples satisfying `P`. -/
def spanTuples {k n : ℕ} (P : (Fin (n + 1) → Δt k) → Prop) : Submodule 𝕜 ((affChains 𝕜 k).X n) :=
  Submodule.span 𝕜 {x | ∃ w, P w ∧ x = elt 𝕜 w}

lemma elt_mem_spanTuples {k n : ℕ} {P : (Fin (n + 1) → Δt k) → Prop} {w} (h : P w) :
    elt 𝕜 w ∈ spanTuples 𝕜 P :=
  Submodule.subset_span ⟨w, h, rfl⟩

lemma spanTuples_mono {k n : ℕ} {P Q : (Fin (n + 1) → Δt k) → Prop} (h : ∀ w, P w → Q w) :
    spanTuples 𝕜 P ≤ spanTuples 𝕜 Q := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨w, hw, rfl⟩
  exact elt_mem_spanTuples 𝕜 (h w hw)

lemma map_mem_of_mem_spanTuples {k n : ℕ} {Z : ModuleCat.{0} 𝕜} {P : (Fin (n + 1) → Δt k) → Prop}
    (f : (affChains 𝕜 k).X n ⟶ Z) {T : Submodule 𝕜 Z}
    (h : ∀ w, P w → f.hom (elt 𝕜 w) ∈ T) {x : (affChains 𝕜 k).X n} (hx : x ∈ spanTuples 𝕜 P) :
    f.hom x ∈ T := by
  have hle : spanTuples 𝕜 P ≤ T.comap f.hom := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨w, hw, rfl⟩
    exact h w hw
  exact hle hx

lemma elt_coneHom {k n : ℕ} (b : Δt k) (w : Fin (n + 1) → Δt k) :
    (coneHom 𝕜 b n).hom (elt 𝕜 w) = elt 𝕜 (Fin.cons b w) := by
  have h2 := congrArg (fun (g : ModuleCat.of 𝕜 𝕜 ⟶ (affChains 𝕜 k).X (n + 1)) => g.hom (1 : 𝕜))
    (ιa_coneHom 𝕜 b w)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2

lemma elt_d {k n : ℕ} (v : Fin (n + 2) → Δt k) :
    ((affChains 𝕜 k).d (n + 1) n).hom (elt 𝕜 v) =
      ∑ i : Fin (n + 2), (-1 : 𝕜) ^ (i : ℕ) • elt 𝕜 (v ∘ i.succAbove) := by
  have h := ιa_d 𝕜 v
  have h2 := congrArg (fun (g : ModuleCat.of 𝕜 𝕜 ⟶ (affChains 𝕜 k).X n) => g.hom (1 : 𝕜)) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [show ((∑ i : Fin (n + 2), (-1 : 𝕜) ^ (i : ℕ) • ιa 𝕜 (v ∘ i.succAbove)).hom (1 : 𝕜)) =
      ∑ i : Fin (n + 2), (-1 : 𝕜) ^ (i : ℕ) • ((ιa 𝕜 (v ∘ i.succAbove)).hom (1 : 𝕜)) by
    simp] at h2
  exact h2

lemma elt_sdHom_succ {k n : ℕ} (v : Fin (n + 2) → Δt k) :
    (sdHom 𝕜 k (n + 1)).hom (elt 𝕜 v) =
      (coneHom 𝕜 (bary v) n).hom ((sdHom 𝕜 k n).hom
        (((affChains 𝕜 k).d (n + 1) n).hom (elt 𝕜 v))) := by
  have h2 := congrArg (fun (g : ModuleCat.of 𝕜 𝕜 ⟶ (affChains 𝕜 k).X (n + 1)) => g.hom (1 : 𝕜))
    (ιa_sdHom_succ 𝕜 v)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2

/-- **The mesh estimate for barycentric subdivision.** The subdivision of an
affine `n`-simplex `v` of diameter at most `D` is a linear combination of affine
`n`-simplices whose vertices lie in the hull of `v` and whose diameter is at
most `n / (n + 1) * D`. -/
theorem sdHom_elt_mem_spanTuples {k : ℕ} :
    ∀ (n : ℕ) (v : Fin (n + 1) → Δt k) (D : ℝ), 0 ≤ D → (∀ a b, dist (v a) (v b) ≤ D) →
      (sdHom 𝕜 k n).hom (elt 𝕜 v) ∈ spanTuples 𝕜 (fun w : Fin (n + 1) → Δt k =>
        (∀ a, InHull v (w a)) ∧ ∀ a b, dist (w a) (w b) ≤ (n : ℝ) / ((n : ℝ) + 1) * D) := by
  intro n
  induction n with
  | zero =>
    intro v D hD _
    rw [sdHom_zero 𝕜]
    refine elt_mem_spanTuples 𝕜 ⟨fun a => inHull_self v a, fun a b => ?_⟩
    have hab : a = b := by
      have ha := a.isLt
      have hb := b.isLt
      exact Fin.ext (by omega)
    rw [hab, dist_self]
    simp
  | succ m ih =>
    intro v D hD hdiam
    rw [elt_sdHom_succ 𝕜, elt_d 𝕜]
    -- the boundary lies in the span of the faces
    have hbd : ∑ i : Fin (m + 2), (-1 : 𝕜) ^ (i : ℕ) • elt 𝕜 (v ∘ i.succAbove) ∈
        spanTuples 𝕜 (fun u : Fin (m + 1) → Δt k => ∃ i : Fin (m + 2), u = v ∘ i.succAbove) := by
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      exact elt_mem_spanTuples 𝕜 ⟨i, rfl⟩
    -- the subdivision of each face has small support
    set Q : (Fin (m + 1) → Δt k) → Prop := fun w =>
      (∀ a, InHull v (w a)) ∧
        ∀ a b, dist (w a) (w b) ≤ ((m : ℝ) + 1) / (((m : ℝ) + 1) + 1) * D with hQ
    have hface : ∀ u : Fin (m + 1) → Δt k, (∃ i : Fin (m + 2), u = v ∘ i.succAbove) →
        (sdHom 𝕜 k m).hom (elt 𝕜 u) ∈ spanTuples 𝕜 Q := by
      rintro u ⟨i, rfl⟩
      have hd' : ∀ a b, dist ((v ∘ i.succAbove) a) ((v ∘ i.succAbove) b) ≤ D :=
        fun a b => hdiam _ _
      refine le_trans (spanTuples_mono 𝕜 (P := fun w : Fin (m + 1) → Δt k =>
          (∀ a, InHull (v ∘ i.succAbove) (w a)) ∧
            ∀ a b, dist (w a) (w b) ≤ (m : ℝ) / ((m : ℝ) + 1) * D) ?_) le_rfl
        (ih (v ∘ i.succAbove) D hD hd')
      rintro w ⟨hw1, hw2⟩
      refine ⟨fun a => inHull_face v i (hw1 a), fun a b => (hw2 a b).trans ?_⟩
      exact mul_le_mul_of_nonneg_right (ratio_mono m) hD
    have hsub : (sdHom 𝕜 k m).hom
        (∑ i : Fin (m + 2), (-1 : 𝕜) ^ (i : ℕ) • elt 𝕜 (v ∘ i.succAbove)) ∈ spanTuples 𝕜 Q :=
      map_mem_of_mem_spanTuples 𝕜 _ hface hbd
    -- coning with the barycentre keeps the estimate
    refine map_mem_of_mem_spanTuples 𝕜 (P := Q) (coneHom 𝕜 (bary v) m) ?_ hsub
    rintro w ⟨hw1, hw2⟩
    rw [elt_coneHom 𝕜]
    refine elt_mem_spanTuples 𝕜 ⟨fun a => ?_, fun a b => ?_⟩
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
def sdIterHom (k : ℕ) : ℕ → (n : ℕ) → ((affChains 𝕜 k).X n ⟶ (affChains 𝕜 k).X n) :=
  Nat.rec (fun _ => 𝟙 _) (fun _ prev n => prev n ≫ sdHom 𝕜 k n)

@[simp] lemma sdIterHom_zero (k n : ℕ) : sdIterHom 𝕜 k 0 n = 𝟙 _ := rfl

lemma sdIterHom_succ (k m n : ℕ) :
    sdIterHom 𝕜 k (m + 1) n = sdIterHom 𝕜 k m n ≫ sdHom 𝕜 k n := rfl

/-- **The iterated mesh estimate.** The `m`-fold barycentric subdivision of an
affine `n`-simplex `v` of diameter at most `D` is a linear combination of
affine `n`-simplices whose vertices lie in the hull of `v` and whose diameter
is at most `(n / (n + 1)) ^ m * D`. -/
theorem sdIterHom_elt_mem_spanTuples {k n : ℕ} :
    ∀ (m : ℕ) (v : Fin (n + 1) → Δt k) (D : ℝ), 0 ≤ D → (∀ a b, dist (v a) (v b) ≤ D) →
      (sdIterHom 𝕜 k m n).hom (elt 𝕜 v) ∈ spanTuples 𝕜 (fun w : Fin (n + 1) → Δt k =>
        (∀ a, InHull v (w a)) ∧
          ∀ a b, dist (w a) (w b) ≤ ((n : ℝ) / ((n : ℝ) + 1)) ^ m * D) := by
  intro m
  induction m with
  | zero =>
    intro v D _ hdiam
    refine elt_mem_spanTuples 𝕜 ⟨fun a => inHull_self v a, fun a b => ?_⟩
    simpa using hdiam a b
  | succ m ih =>
    intro v D hD hdiam
    have hr : (0 : ℝ) ≤ (n : ℝ) / ((n : ℝ) + 1) := by positivity
    rw [sdIterHom_succ 𝕜]
    change (sdHom 𝕜 k n).hom ((sdIterHom 𝕜 k m n).hom (elt 𝕜 v)) ∈ _
    refine map_mem_of_mem_spanTuples 𝕜 (sdHom 𝕜 k n) ?_ (ih v D hD hdiam)
    rintro w ⟨hw1, hw2⟩
    have hDm : (0 : ℝ) ≤ ((n : ℝ) / ((n : ℝ) + 1)) ^ m * D := by positivity
    refine le_trans (spanTuples_mono 𝕜 (P := fun u : Fin (n + 1) → Δt k =>
        (∀ a, InHull w (u a)) ∧
          ∀ a b, dist (u a) (u b) ≤
            (n : ℝ) / ((n : ℝ) + 1) * (((n : ℝ) / ((n : ℝ) + 1)) ^ m * D)) ?_) le_rfl
      (sdHom_elt_mem_spanTuples 𝕜 n w _ hDm hw2)
    rintro u ⟨hu1, hu2⟩
    refine ⟨fun a => inHull_trans v w hw1 (hu1 a), fun a b => (hu2 a b).trans (le_of_eq ?_)⟩
    ring

end AffineTverberg.Coefficients.AffChain

