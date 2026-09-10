import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

set_option linter.style.header false

/-!
# Affine chains in a standard simplex and barycentric subdivision

This file builds, entirely from scratch, the *linear* (affine) chain complex of
the standard topological simplex `Δt k = stdSimplex ℝ (Fin (k+1))`, the classical
cone operator, the barycentric subdivision operator `sdHom` and the chain
homotopy `tdHom` between `sdHom` and the identity.

An affine `n`-simplex in `Δt k` is recorded by its vertex tuple
`v : Fin (n+1) → Δt k`; the associated continuous map `Δt n → Δt k` is
`affMap v`. Vertex tuples form a simplicial set `affSSet k` (precomposition
with the monotone maps of the simplex category), so the associated free chain
complex `affChains k` is Mathlib's chain complex of a simplicial set and its
differential is the alternating sum of the face maps *by construction*. In
particular `d ∘ d = 0` and all naturality statements below are inherited.

The main results are

* `coneHom_d` / `coneHom_d_zero` — the boundary of a cone;
* `sdHom_d` — the subdivision is a chain map;
* `tdHom_d` / `tdHom_d_zero` — the chain homotopy identity `∂T + T∂ = 1 - S`;
* `pushChain_sdHom` / `pushChain_tdHom` — naturality of both operators under
  affine maps.

Nothing here is assumed: every identity is proved from the actual alternating
face maps and the actual barycentres.
-/

noncomputable section

open CategoryTheory Limits Simplicial
open scoped BigOperators

namespace AffineTverberg

namespace AffChain

/-- The standard topological `k`-simplex. -/
abbrev Δt (k : ℕ) := stdSimplex ℝ (Fin (k + 1))

/-! ### Affine combinations -/

/-- The affine combination of the vertex tuple `w` with barycentric weights `t`. -/
def affPoint {k j : ℕ} (w : Fin (j + 1) → Δt k) (t : Δt j) : Δt k :=
  ⟨∑ a, t a • (w a : Fin (k + 1) → ℝ), (convex_stdSimplex ℝ (Fin (k + 1))).sum_mem
    (fun i _ => t.2.1 i) t.2.2 (fun i _ => (w i).2)⟩

lemma affPoint_apply {k j : ℕ} (w : Fin (j + 1) → Δt k) (t : Δt j) (b : Fin (k + 1)) :
    affPoint w t b = ∑ a, t a * w a b := by
  change (∑ a, t a • ((w a : Δt k) : Fin (k + 1) → ℝ)) b = _
  simp [Finset.sum_apply]

lemma continuous_affPoint {k j : ℕ} (w : Fin (j + 1) → Δt k) : Continuous (affPoint w) := by
  apply Continuous.subtype_mk
  apply continuous_finsetSum
  intro a _
  exact ((continuous_apply a).comp continuous_subtype_val).smul continuous_const

/-- The affine singular simplex with vertex tuple `w`. -/
def affMap {k j : ℕ} (w : Fin (j + 1) → Δt k) : C(Δt j, Δt k) :=
  ⟨affPoint w, continuous_affPoint w⟩

@[simp] lemma affMap_apply {k j : ℕ} (w : Fin (j + 1) → Δt k) (t : Δt j) :
    affMap w t = affPoint w t := rfl

/-- An affine simplex takes the `i`-th vertex of its domain to `w i`. -/
lemma affPoint_vertex {k j : ℕ} (w : Fin (j + 1) → Δt k) (i : Fin (j + 1)) :
    affPoint w (stdSimplex.vertex i) = w i := by
  apply Subtype.ext; funext b
  rw [show ((affPoint w (stdSimplex.vertex i)).1 b) = affPoint w (stdSimplex.vertex i) b from rfl,
    affPoint_apply]
  simp [Pi.single_apply, Finset.sum_ite_eq']
  rfl

/-- The affine simplex whose vertices are the vertices of `Δt k` is the identity. -/
lemma affPoint_id {k : ℕ} (t : Δt k) :
    affPoint (fun i => stdSimplex.vertex i) t = t := by
  apply Subtype.ext; funext b
  rw [show ((affPoint (fun i => stdSimplex.vertex (S := ℝ) i) t).1 b)
      = affPoint (fun i => stdSimplex.vertex (S := ℝ) i) t b from rfl, affPoint_apply]
  simp [Pi.single_apply, eq_comm]
  rfl

/-- Reindexing the vertex tuple is precomposition with the induced map of simplices. -/
lemma affPoint_map {k j i : ℕ} (w : Fin (j + 1) → Δt k) (f : Fin (i + 1) → Fin (j + 1))
    (t : Δt i) :
    affPoint (fun a => w (f a)) t = affPoint w (stdSimplex.map f t) := by
  apply Subtype.ext; funext c
  rw [show ((affPoint (fun a => w (f a)) t).1 c) = affPoint (fun a => w (f a)) t c from rfl,
    affPoint_apply,
    show ((affPoint w (stdSimplex.map f t)).1 c) = affPoint w (stdSimplex.map f t) c from rfl,
    affPoint_apply]
  have hmap : ∀ a, (stdSimplex.map f t) a = ∑ b ∈ Finset.univ.filter (fun b => f b = a), t b := by
    intro a
    change (FunOnFinite.linearMap ℝ ℝ f (t : Fin (i + 1) → ℝ)) a = _
    rw [FunOnFinite.linearMap_apply_apply]
  simp only [hmap, Finset.sum_mul]
  rw [← Finset.sum_fiberwise Finset.univ f (fun b => t b * w (f b) c)]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  simp only [Finset.mem_filter] at hb
  rw [hb.2]

/-- Composition of affine simplices. -/
lemma affPoint_comp {k j i : ℕ} (w : Fin (j + 1) → Δt k) (v : Fin (i + 1) → Δt j) (t : Δt i) :
    affPoint w (affPoint v t) = affPoint (fun a => affPoint w (v a)) t := by
  apply Subtype.ext; funext c
  rw [show ((affPoint w (affPoint v t)).1 c) = affPoint w (affPoint v t) c from rfl,
    affPoint_apply,
    show ((affPoint (fun a => affPoint w (v a)) t).1 c)
      = affPoint (fun a => affPoint w (v a)) t c from rfl, affPoint_apply]
  simp only [affPoint_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

/-- The barycentre of the standard `j`-simplex. -/
def center (j : ℕ) : Δt j :=
  ⟨fun _ => ((j : ℝ) + 1)⁻¹, fun _ => by positivity, by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h : ((j : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp⟩

/-- The barycentre of an affine simplex. -/
def bary {k j : ℕ} (v : Fin (j + 1) → Δt k) : Δt k := affPoint v (center j)

/-- Barycentres are natural for affine maps. -/
lemma affPoint_bary {k l j : ℕ} (w : Fin (k + 1) → Δt l) (v : Fin (j + 1) → Δt k) :
    affPoint w (bary v) = bary (fun a => affPoint w (v a)) := by
  rw [bary, bary, affPoint_comp]

/-! ### The simplicial set of affine simplices -/

/-- The simplicial set whose `n`-simplices are the vertex tuples of affine
`n`-simplices in `Δt k`. -/
def affSSet (k : ℕ) : SSet.{0} where
  obj n := Fin (n.unop.len + 1) → Δt k
  map {n _} f := TypeCat.ofHom (fun (v : Fin (n.unop.len + 1) → Δt k) => v ∘ f.unop.toOrderHom)
  map_id := by intro n; rfl
  map_comp := by intro a b c f g; rfl

lemma affSSet_δ (k : ℕ) {n : ℕ} (i : Fin (n + 2)) (v : Fin (n + 2) → Δt k) :
    (affSSet k).δ i v = v ∘ i.succAbove := rfl

/-- The chain complex of affine chains in `Δt k`, with real coefficients. -/
abbrev affChains (k : ℕ) : ChainComplex (ModuleCat.{0} ℝ) ℕ :=
  (affSSet k).chainComplex (ModuleCat.of ℝ ℝ)

/-- The basis element of the affine chain complex given by a vertex tuple. -/
abbrev ιa {k n : ℕ} (v : Fin (n + 1) → Δt k) : ModuleCat.of ℝ ℝ ⟶ (affChains k).X n :=
  (affSSet k).ιChainComplex v

lemma ιa_d {k n : ℕ} (v : Fin (n + 2) → Δt k) :
    ιa v ≫ (affChains k).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℝ) ^ (i : ℕ) • ιa (v ∘ i.succAbove) := by
  have h := (affSSet k).ιChainComplex_d (ModuleCat.of ℝ ℝ) v
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show ((ConcreteCategory.hom ((affSSet k).δ i)) v) = v ∘ i.succAbove from rfl,
    ← Int.cast_smul_eq_zsmul ℝ ((-1 : ℤ) ^ (i : ℕ))]
  push_cast
  rfl

/-- Morphisms out of the affine chain group are determined by their values on
vertex tuples. -/
lemma affChains_hom_ext {k n : ℕ} {T : ModuleCat.{0} ℝ} {f g : (affChains k).X n ⟶ T}
    (h : ∀ v : Fin (n + 1) → Δt k, ιa v ≫ f = ιa v ≫ g) : f = g :=
  SSet.chainComplex_hom_ext h

/-! ### Realization and pushforward -/

/-- Realizing affine simplices of `Δt k` inside a space along a singular simplex
`σ`, as a map of simplicial sets. -/
def realSMap {X : TopCat.{0}} {k : ℕ} (σ : C(Δt k, X)) : affSSet k ⟶ TopCat.toSSet.obj X where
  app n := TypeCat.ofHom (fun (v : Fin (n.unop.len + 1) → Δt k) =>
    (X.toSSetObjEquiv n).symm (σ.comp (affMap v)))
  naturality := by
    intro n m f
    ext v
    apply (X.toSSetObjEquiv m).injective
    ext t
    exact congrArg σ (affPoint_map (v : Fin (n.unop.len + 1) → Δt k) f.unop.toOrderHom t)

/-- The pushforward of affine simplices along the affine map with vertices `w`. -/
def pushSMap {k l : ℕ} (w : Fin (k + 1) → Δt l) : affSSet k ⟶ affSSet l where
  app n := TypeCat.ofHom (fun (v : Fin (n.unop.len + 1) → Δt k) => fun a => affPoint w (v a))
  naturality := by intro n m f; rfl

/-- The induced chain map of a pushforward. -/
abbrev pushChain {k l : ℕ} (w : Fin (k + 1) → Δt l) : affChains k ⟶ affChains l :=
  SSet.chainComplexMap (pushSMap w) (ModuleCat.of ℝ ℝ)

/-- The induced chain map of a realization. -/
abbrev realChain {X : TopCat.{0}} {k : ℕ} (σ : C(Δt k, X)) :
    affChains k ⟶ (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℝ ℝ) :=
  SSet.chainComplexMap (realSMap σ) (ModuleCat.of ℝ ℝ)

lemma ιa_pushChain {k l n : ℕ} (w : Fin (k + 1) → Δt l) (v : Fin (n + 1) → Δt k) :
    ιa v ≫ (pushChain w).f n = ιa (fun a => affPoint w (v a)) :=
  SSet.ι_chainComplexMap_f _ _ _ _ _

lemma ιa_realChain {X : TopCat.{0}} {k n : ℕ} (σ : C(Δt k, X)) (v : Fin (n + 1) → Δt k) :
    ιa v ≫ (realChain σ).f n =
      (TopCat.toSSet.obj X).ιChainComplex ((X.toSSetObjEquiv _).symm (σ.comp (affMap v))) :=
  SSet.ι_chainComplexMap_f _ _ _ _ _

/-! ### The cone operator -/

/-- The cone with apex `b` on affine chains. -/
def coneHom {k : ℕ} (b : Δt k) (n : ℕ) : (affChains k).X n ⟶ (affChains k).X (n + 1) :=
  Sigma.desc (fun (v : Fin (n + 1) → Δt k) => ιa (Fin.cons b v))

@[simp] lemma ιa_coneHom {k n : ℕ} (b : Δt k) (v : Fin (n + 1) → Δt k) :
    ιa v ≫ coneHom b n = ιa (Fin.cons b v) :=
  Sigma.ι_desc _ _

/-- The augmentation of affine `0`-chains. -/
def epsHom (k : ℕ) : (affChains k).X 0 ⟶ ModuleCat.of ℝ ℝ :=
  Sigma.desc (fun (_ : Fin 1 → Δt k) => 𝟙 (ModuleCat.of ℝ ℝ))

@[simp] lemma ιa_epsHom {k : ℕ} (v : Fin 1 → Δt k) :
    ιa v ≫ epsHom k = 𝟙 (ModuleCat.of ℝ ℝ) :=
  Sigma.ι_desc _ _

/-- Deleting the `0`-th vertex of a cone gives back the base. -/
lemma cons_comp_succAbove_zero {n : ℕ} {α : Type*} (b : α) (v : Fin (n + 1) → α) :
    (Fin.cons b v : Fin (n + 2) → α) ∘ (0 : Fin (n + 2)).succAbove = v := by
  funext a; simp [Fin.succAbove_zero]

/-- Deleting a later vertex of a cone gives the cone on the corresponding face. -/
lemma cons_comp_succAbove_succ {n : ℕ} {α : Type*} (b : α) (v : Fin (n + 2) → α)
    (j : Fin (n + 2)) :
    (Fin.cons b v : Fin (n + 3) → α) ∘ (j.succ).succAbove =
      Fin.cons b (v ∘ j.succAbove) := by
  funext a
  induction a using Fin.cases with
  | zero => simp
  | succ a => simp [Fin.succ_succAbove_succ]

/-- The boundary of a cone in positive degrees. -/
theorem coneHom_d {k n : ℕ} (b : Δt k) :
    coneHom b (n + 1) ≫ (affChains k).d (n + 2) (n + 1) =
      𝟙 _ - (affChains k).d (n + 1) n ≫ coneHom b n := by
  refine affChains_hom_ext fun v => ?_
  have hL : ιa v ≫ coneHom b (n + 1) ≫ (affChains k).d (n + 2) (n + 1) =
      ∑ i : Fin (n + 3), (-1 : ℝ) ^ (i : ℕ) •
        ιa ((Fin.cons b v : Fin (n + 3) → Δt k) ∘ i.succAbove) := by
    rw [← Category.assoc, ιa_coneHom, ιa_d]
  have hR : ιa v ≫ (𝟙 _ - (affChains k).d (n + 1) n ≫ coneHom b n) =
      ιa v - ∑ j : Fin (n + 2), (-1 : ℝ) ^ (j : ℕ) •
        ιa (Fin.cons b ((v : Fin (n + 2) → Δt k) ∘ j.succAbove)) := by
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, ιa_d,
      Preadditive.sum_comp]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Linear.smul_comp, ιa_coneHom]
  rw [hL, hR, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ,
    cons_comp_succAbove_zero, cons_comp_succAbove_succ]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← neg_smul]
  congr 1
  ring

/-- The boundary of a cone in degree zero. -/
theorem coneHom_d_zero {k : ℕ} (b : Δt k) :
    coneHom b 0 ≫ (affChains k).d 1 0 = 𝟙 _ - epsHom k ≫ ιa (fun _ : Fin 1 => b) := by
  refine affChains_hom_ext fun v => ?_
  have hL : ιa v ≫ coneHom b 0 ≫ (affChains k).d 1 0 =
      ∑ i : Fin 2, (-1 : ℝ) ^ (i : ℕ) • ιa ((Fin.cons b v : Fin 2 → Δt k) ∘ i.succAbove) := by
    rw [← Category.assoc, ιa_coneHom, ιa_d]
  have h0 : (Fin.cons b v : Fin 2 → Δt k) ∘ (0 : Fin 2).succAbove = v :=
    cons_comp_succAbove_zero b v
  have h1 : (Fin.cons b v : Fin 2 → Δt k) ∘ (1 : Fin 2).succAbove = (fun _ : Fin 1 => b) := by
    funext a
    fin_cases a
    rfl
  rw [hL, Preadditive.comp_sub, Category.comp_id, ← Category.assoc, ιa_epsHom,
    Category.id_comp, Fin.sum_univ_two, h0, h1]
  simp [sub_eq_add_neg]

/-- The augmentation kills boundaries. -/
theorem d_epsHom {k : ℕ} : (affChains k).d 1 0 ≫ epsHom k = 0 := by
  refine affChains_hom_ext fun v => ?_
  rw [← Category.assoc, ιa_d, Preadditive.sum_comp, comp_zero, Fin.sum_univ_two]
  simp

/-- Reassociated form of `d_epsHom`. -/
lemma d_epsHom_comp {k : ℕ} {Z : ModuleCat.{0} ℝ} (g : ModuleCat.of ℝ ℝ ⟶ Z) :
    (affChains k).d 1 0 ≫ epsHom k ≫ g = 0 := by
  rw [← Category.assoc, d_epsHom, Limits.zero_comp]

/-! ### Barycentric subdivision and its homotopy -/

/-- The barycentric subdivision operator on affine chains. -/
def sdHom (k : ℕ) : (n : ℕ) → ((affChains k).X n ⟶ (affChains k).X n) :=
  Nat.rec (motive := fun n => (affChains k).X n ⟶ (affChains k).X n) (𝟙 _)
    (fun n prev => Sigma.desc (fun (v : Fin (n + 2) → Δt k) =>
      ιa v ≫ (affChains k).d (n + 1) n ≫ prev ≫ coneHom (bary v) n))

lemma sdHom_zero (k : ℕ) : sdHom k 0 = 𝟙 _ := rfl

lemma ιa_sdHom_succ {k n : ℕ} (v : Fin (n + 2) → Δt k) :
    ιa v ≫ sdHom k (n + 1) =
      ιa v ≫ (affChains k).d (n + 1) n ≫ sdHom k n ≫ coneHom (bary v) n :=
  Sigma.ι_desc _ _

/-- The chain homotopy between the barycentric subdivision and the identity. -/
def tdHom (k : ℕ) : (n : ℕ) → ((affChains k).X n ⟶ (affChains k).X (n + 1)) :=
  Nat.rec (motive := fun n => (affChains k).X n ⟶ (affChains k).X (n + 1))
    (Sigma.desc (fun (v : Fin 1 → Δt k) => ιa v ≫ coneHom (bary v) 0))
    (fun n prev => Sigma.desc (fun (v : Fin (n + 2) → Δt k) =>
      (ιa v - ιa v ≫ (affChains k).d (n + 1) n ≫ prev) ≫ coneHom (bary v) (n + 1)))

lemma ιa_tdHom_zero {k : ℕ} (v : Fin 1 → Δt k) :
    ιa v ≫ tdHom k 0 = ιa v ≫ coneHom (bary v) 0 :=
  Sigma.ι_desc _ _

lemma ιa_tdHom_succ {k n : ℕ} (v : Fin (n + 2) → Δt k) :
    ιa v ≫ tdHom k (n + 1) =
      (ιa v - ιa v ≫ (affChains k).d (n + 1) n ≫ tdHom k n) ≫ coneHom (bary v) (n + 1) :=
  Sigma.ι_desc _ _

/-- The barycentre of a `0`-simplex is its unique vertex. -/
lemma bary_zero {k : ℕ} (v : Fin 1 → Δt k) : (fun _ : Fin 1 => bary v) = v := by
  have hb : bary v = v 0 := by
    apply Subtype.ext; funext c
    change affPoint v (center 0) c = (v 0 : Δt k) c
    rw [affPoint_apply, Fin.sum_univ_one]
    change ((0 : ℕ) + 1 : ℝ)⁻¹ * (v 0) c = (v 0) c
    norm_num
  funext a
  rw [hb, Subsingleton.elim a 0]

/-- Reassociated form of the recursion for the subdivision. -/
lemma ιa_sdHom_succ_comp {k n : ℕ} (v : Fin (n + 2) → Δt k) {Z : ModuleCat.{0} ℝ}
    (g : (affChains k).X (n + 1) ⟶ Z) :
    ιa v ≫ sdHom k (n + 1) ≫ g =
      ιa v ≫ (affChains k).d (n + 1) n ≫ sdHom k n ≫ coneHom (bary v) n ≫ g := by
  rw [← Category.assoc, ιa_sdHom_succ]
  simp only [Category.assoc]

/-- Reassociated form of the recursion for the homotopy. -/
lemma ιa_tdHom_succ_comp {k n : ℕ} (v : Fin (n + 2) → Δt k) {Z : ModuleCat.{0} ℝ}
    (g : (affChains k).X (n + 2) ⟶ Z) :
    ιa v ≫ tdHom k (n + 1) ≫ g =
      (ιa v - ιa v ≫ (affChains k).d (n + 1) n ≫ tdHom k n) ≫ coneHom (bary v) (n + 1) ≫ g := by
  rw [← Category.assoc, ιa_tdHom_succ]
  simp only [Category.assoc]

/-- Reassociated form of the boundary of a cone. -/
lemma coneHom_d_comp {k n : ℕ} (b : Δt k) {Z : ModuleCat.{0} ℝ}
    (g : (affChains k).X (n + 1) ⟶ Z) :
    coneHom b (n + 1) ≫ (affChains k).d (n + 2) (n + 1) ≫ g =
      g - (affChains k).d (n + 1) n ≫ coneHom b n ≫ g := by
  rw [← Category.assoc, coneHom_d, Preadditive.sub_comp, Category.id_comp, Category.assoc]

/-- Reassociated form of the boundary of a cone in degree zero. -/
lemma coneHom_d_zero_comp {k : ℕ} (b : Δt k) {Z : ModuleCat.{0} ℝ}
    (g : (affChains k).X 0 ⟶ Z) :
    coneHom b 0 ≫ (affChains k).d 1 0 ≫ g =
      g - epsHom k ≫ ιa (fun _ : Fin 1 => b) ≫ g := by
  rw [← Category.assoc, coneHom_d_zero, Preadditive.sub_comp, Category.id_comp, Category.assoc]

/-- **The barycentric subdivision is a chain map.** -/
theorem sdHom_d (k n : ℕ) :
    sdHom k (n + 1) ≫ (affChains k).d (n + 1) n = (affChains k).d (n + 1) n ≫ sdHom k n := by
  induction n with
  | zero =>
    refine affChains_hom_ext fun v => ?_
    change ιa v ≫ sdHom k 1 ≫ (affChains k).d 1 0 = ιa v ≫ (affChains k).d 1 0 ≫ sdHom k 0
    rw [ιa_sdHom_succ_comp, sdHom_zero, Category.id_comp,
      show (affChains k).d (0 + 1) 0 = (affChains k).d 1 0 from rfl, coneHom_d_zero]
    simp only [Preadditive.comp_sub, Category.comp_id, d_epsHom_comp, sub_zero]
  | succ m ih =>
    refine affChains_hom_ext fun v => ?_
    rw [ιa_sdHom_succ_comp, coneHom_d, Preadditive.comp_sub, Category.comp_id,
      Preadditive.comp_sub, Preadditive.comp_sub,
      ← Category.assoc (sdHom k (m + 1)) ((affChains k).d (m + 1) m), ih, Category.assoc,
      ← Category.assoc ((affChains k).d (m + 1 + 1) (m + 1)) ((affChains k).d (m + 1) m),
      HomologicalComplex.d_comp_d, Limits.zero_comp, comp_zero, sub_zero]

/-- **The homotopy identity in degree zero.** -/
theorem tdHom_d_zero (k : ℕ) : tdHom k 0 ≫ (affChains k).d 1 0 = 𝟙 _ - sdHom k 0 := by
  refine affChains_hom_ext fun v => ?_
  rw [← Category.assoc, ιa_tdHom_zero, Category.assoc, coneHom_d_zero,
    Preadditive.comp_sub, Category.comp_id, ← Category.assoc, ιa_epsHom, Category.id_comp,
    bary_zero, sdHom_zero, Preadditive.comp_sub, Category.comp_id]

/-- The homotopy identity in degree `n + 1`, assuming the consequence
`∂T∂ = ∂ - ∂S` of the homotopy identity one degree down. -/
lemma tdHom_d_of_comp (k n : ℕ)
    (hcomp : (affChains k).d (n + 1) n ≫ tdHom k n ≫ (affChains k).d (n + 1) n =
      (affChains k).d (n + 1) n - (affChains k).d (n + 1) n ≫ sdHom k n) :
    tdHom k (n + 1) ≫ (affChains k).d (n + 2) (n + 1) +
        (affChains k).d (n + 1) n ≫ tdHom k n =
      𝟙 _ - sdHom k (n + 1) := by
  refine affChains_hom_ext fun v => ?_
  have h1 : ιa v ≫ tdHom k (n + 1) =
      (ιa v - ιa v ≫ (affChains k).d (n + 1) n ≫ tdHom k n) ≫ coneHom (bary v) (n + 1) :=
    ιa_tdHom_succ v
  have h2 : coneHom (bary v) (n + 1) ≫ (affChains k).d (n + 2) (n + 1) =
      𝟙 _ - (affChains k).d (n + 1) n ≫ coneHom (bary v) n := coneHom_d _
  have h3 : ιa v ≫ (affChains k).d (n + 1) n ≫ tdHom k n ≫ (affChains k).d (n + 1) n =
      ιa v ≫ (affChains k).d (n + 1) n -
        ιa v ≫ (affChains k).d (n + 1) n ≫ sdHom k n := by
    rw [hcomp, Preadditive.comp_sub]
  have h4 : ιa v ≫ sdHom k (n + 1) =
      ιa v ≫ (affChains k).d (n + 1) n ≫ sdHom k n ≫ coneHom (bary v) n :=
    ιa_sdHom_succ v
  have hX : (ιa v ≫ (affChains k).d (n + 1) n ≫ tdHom k n) ≫
        ((affChains k).d (n + 1) n ≫ coneHom (bary v) n) =
      ιa v ≫ (affChains k).d (n + 1) n ≫ coneHom (bary v) n -
        ιa v ≫ sdHom k (n + 1) := by
    have e : (ιa v ≫ (affChains k).d (n + 1) n ≫ tdHom k n) ≫
          ((affChains k).d (n + 1) n ≫ coneHom (bary v) n) =
        (ιa v ≫ (affChains k).d (n + 1) n ≫ tdHom k n ≫ (affChains k).d (n + 1) n) ≫
          coneHom (bary v) n := by
      simp only [Category.assoc]
    rw [e, h3, Preadditive.sub_comp, h4]
    simp only [Category.assoc]
  have hmain : ιa v ≫ tdHom k (n + 1) ≫ (affChains k).d (n + 2) (n + 1) =
      ιa v - ιa v ≫ (affChains k).d (n + 1) n ≫ tdHom k n - ιa v ≫ sdHom k (n + 1) := by
    rw [ιa_tdHom_succ_comp, h2, Preadditive.comp_sub, Category.comp_id,
      Preadditive.sub_comp, hX]
    abel
  rw [Preadditive.comp_add, hmain]
  rw [Preadditive.comp_sub, Category.comp_id]
  abel

/-- **The homotopy identity `∂T + T∂ = 1 - S`.** -/
theorem tdHom_d (k n : ℕ) :
    tdHom k (n + 1) ≫ (affChains k).d (n + 2) (n + 1) +
        (affChains k).d (n + 1) n ≫ tdHom k n =
      𝟙 _ - sdHom k (n + 1) := by
  induction n with
  | zero =>
    refine tdHom_d_of_comp k 0 ?_
    have h := tdHom_d_zero k
    rw [sdHom_zero, sub_self] at h
    change (affChains k).d 1 0 ≫ tdHom k 0 ≫ (affChains k).d 1 0 =
      (affChains k).d 1 0 - (affChains k).d 1 0 ≫ sdHom k 0
    rw [h, comp_zero, sdHom_zero, Category.comp_id, sub_self]
  | succ m ih =>
    refine tdHom_d_of_comp k (m + 1) ?_
    have h : tdHom k (m + 1) ≫ (affChains k).d (m + 2) (m + 1) =
        𝟙 _ - sdHom k (m + 1) - (affChains k).d (m + 1) m ≫ tdHom k m := by
      rw [← ih]; abel
    change (affChains k).d (m + 2) (m + 1) ≫ tdHom k (m + 1) ≫ (affChains k).d (m + 2) (m + 1) =
      (affChains k).d (m + 2) (m + 1) -
        (affChains k).d (m + 2) (m + 1) ≫ sdHom k (m + 1)
    rw [h, Preadditive.comp_sub, Preadditive.comp_sub, Category.comp_id,
      ← Category.assoc, HomologicalComplex.d_comp_d, Limits.zero_comp, sub_zero]

/-! ### Naturality under affine maps -/

/-- The pushforward of a cone is the cone on the pushforward. -/
lemma pushV_cons {k l n : ℕ} (w : Fin (k + 1) → Δt l) (b : Δt k) (v : Fin (n + 1) → Δt k) :
    (fun a => affPoint w ((Fin.cons b v : Fin (n + 2) → Δt k) a)) =
      Fin.cons (affPoint w b) (fun a => affPoint w (v a)) := by
  funext a
  induction a using Fin.cases with
  | zero => simp
  | succ a => simp

lemma pushChain_coneHom {k l n : ℕ} (w : Fin (k + 1) → Δt l) (b : Δt k) :
    coneHom b n ≫ (pushChain w).f (n + 1) =
      (pushChain w).f n ≫ coneHom (affPoint w b) n := by
  refine affChains_hom_ext fun v => ?_
  rw [← Category.assoc, ιa_coneHom, ιa_pushChain, ← Category.assoc, ιa_pushChain,
    ιa_coneHom, pushV_cons]

/-- Reassociated form of `pushChain_coneHom`. -/
lemma pushChain_coneHom_comp {k l n : ℕ} (w : Fin (k + 1) → Δt l) (b : Δt k)
    {Z : ModuleCat.{0} ℝ} (g : (affChains l).X (n + 1) ⟶ Z) :
    coneHom b n ≫ (pushChain w).f (n + 1) ≫ g =
      (pushChain w).f n ≫ coneHom (affPoint w b) n ≫ g := by
  rw [← Category.assoc, pushChain_coneHom, Category.assoc]

/-- Barycentres are natural for pushforwards. -/
lemma bary_pushV {k l n : ℕ} (w : Fin (k + 1) → Δt l) (v : Fin (n + 1) → Δt k) :
    bary (fun a => affPoint w (v a)) = affPoint w (bary v) :=
  (affPoint_bary w v).symm

theorem pushChain_sdHom {k l : ℕ} (w : Fin (k + 1) → Δt l) (n : ℕ) :
    sdHom k n ≫ (pushChain w).f n = (pushChain w).f n ≫ sdHom l n := by
  induction n with
  | zero => rw [sdHom_zero, sdHom_zero, Category.id_comp, Category.comp_id]
  | succ m ih =>
    refine affChains_hom_ext fun v => ?_
    have hR : ιa v ≫ (pushChain w).f (m + 1) ≫ sdHom l (m + 1) =
        ιa (fun a => affPoint w (v a)) ≫ (affChains l).d (m + 1) m ≫ sdHom l m ≫
          coneHom (bary (fun a => affPoint w (v a))) m := by
      rw [← Category.assoc (ιa v) ((pushChain w).f (m + 1)), ιa_pushChain, ιa_sdHom_succ]
    rw [ιa_sdHom_succ_comp, hR, pushChain_coneHom, ← Category.assoc (sdHom k m), ih,
      Category.assoc, ← Category.assoc ((affChains k).d (m + 1) m),
      ← (pushChain w).comm (m + 1) m, Category.assoc,
      ← Category.assoc (ιa v) ((pushChain w).f (m + 1)), ιa_pushChain, bary_pushV]

theorem pushChain_tdHom {k l : ℕ} (w : Fin (k + 1) → Δt l) (n : ℕ) :
    tdHom k n ≫ (pushChain w).f (n + 1) = (pushChain w).f n ≫ tdHom l n := by
  induction n with
  | zero =>
    refine affChains_hom_ext fun v => ?_
    rw [← Category.assoc, ιa_tdHom_zero, Category.assoc, pushChain_coneHom,
      ← Category.assoc, ιa_pushChain, ← Category.assoc (ιa v), ιa_pushChain,
      ιa_tdHom_zero, bary_pushV]
  | succ m ih =>
    refine affChains_hom_ext fun v => ?_
    have hR : ιa v ≫ (pushChain w).f (m + 1) ≫ tdHom l (m + 1) =
        (ιa (fun a => affPoint w (v a)) -
          (ιa (fun a => affPoint w (v a)) ≫ (affChains l).d (m + 1) m ≫ tdHom l m)) ≫
          coneHom (bary (fun a => affPoint w (v a))) (m + 1) := by
      rw [← Category.assoc (ιa v) ((pushChain w).f (m + 1)), ιa_pushChain, ιa_tdHom_succ]
    have hcross : (ιa (fun a => affPoint w (v a)) ≫ (affChains l).d (m + 1) m ≫ tdHom l m) =
        ιa v ≫ (affChains k).d (m + 1) m ≫ tdHom k m ≫ (pushChain w).f (m + 1) := by
      symm
      rw [ih, ← Category.assoc ((affChains k).d (m + 1) m) ((pushChain w).f m) (tdHom l m),
        ← (pushChain w).comm (m + 1) m,
        Category.assoc ((pushChain w).f (m + 1)) ((affChains l).d (m + 1) m) (tdHom l m),
        ← Category.assoc (ιa v) ((pushChain w).f (m + 1)), ιa_pushChain]
    rw [ιa_tdHom_succ_comp, hR, hcross, pushChain_coneHom, bary_pushV,
      Preadditive.sub_comp, Preadditive.sub_comp,
      ← Category.assoc (ιa v) ((pushChain w).f (m + 1)), ιa_pushChain]
    simp only [Category.assoc]

end AffChain

end AffineTverberg
