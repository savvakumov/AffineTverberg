import AffineTverberg.AffineChains

set_option linter.style.header false

/-!
# Affine subdivision with arbitrary field coefficients

The standard simplices, barycentres and affine maps remain real. The free
chain modules have coefficients in an arbitrary field, including characteristic
two. Cone, subdivision and homotopy identities are derived from the actual
simplicial-set differentials, with no coefficient comparison assumed.
-/

noncomputable section

open CategoryTheory Limits Simplicial AffineTverberg.AffChain
open scoped BigOperators

namespace AffineTverberg.Coefficients.AffChain

variable (𝕜 : Type) [Field 𝕜]

/-- The chain complex of affine chains in `Δt k`, with arbitrary field coefficients. -/
abbrev affChains (k : ℕ) : ChainComplex (ModuleCat.{0} 𝕜) ℕ :=
  (affSSet k).chainComplex (ModuleCat.of 𝕜 𝕜)

/-- The basis element of the affine chain complex given by a vertex tuple. -/
abbrev ιa {k n : ℕ} (v : Fin (n + 1) → Δt k) : ModuleCat.of 𝕜 𝕜 ⟶ (affChains 𝕜 k).X n :=
  (affSSet k).ιChainComplex v

lemma ιa_d {k n : ℕ} (v : Fin (n + 2) → Δt k) :
    ιa 𝕜 v ≫ (affChains 𝕜 k).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : 𝕜) ^ (i : ℕ) • ιa 𝕜 (v ∘ i.succAbove) := by
  have h := (affSSet k).ιChainComplex_d (ModuleCat.of 𝕜 𝕜) v
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show ((ConcreteCategory.hom ((affSSet k).δ i)) v) = v ∘ i.succAbove from rfl,
    ← Int.cast_smul_eq_zsmul 𝕜 ((-1 : ℤ) ^ (i : ℕ))]
  push_cast
  rfl

/-- Morphisms out of the affine chain group are determined by their values on
vertex tuples. -/
lemma affChains_hom_ext {k n : ℕ} {T : ModuleCat.{0} 𝕜} {f g : (affChains 𝕜 k).X n ⟶ T}
    (h : ∀ v : Fin (n + 1) → Δt k, ιa 𝕜 v ≫ f = ιa 𝕜 v ≫ g) : f = g :=
  SSet.chainComplex_hom_ext h


/-- The induced chain map of a pushforward. -/
abbrev pushChain {k l : ℕ} (w : Fin (k + 1) → Δt l) : affChains 𝕜 k ⟶ affChains 𝕜 l :=
  SSet.chainComplexMap (pushSMap w) (ModuleCat.of 𝕜 𝕜)

/-- The induced chain map of a realization. -/
abbrev realChain {X : TopCat.{0}} {k : ℕ} (σ : C(Δt k, X)) :
    affChains 𝕜 k ⟶ (TopCat.toSSet.obj X).chainComplex (ModuleCat.of 𝕜 𝕜) :=
  SSet.chainComplexMap (realSMap σ) (ModuleCat.of 𝕜 𝕜)

lemma ιa_pushChain {k l n : ℕ} (w : Fin (k + 1) → Δt l) (v : Fin (n + 1) → Δt k) :
    ιa 𝕜 v ≫ (pushChain 𝕜 w).f n = ιa 𝕜 (fun a => affPoint w (v a)) :=
  SSet.ι_chainComplexMap_f _ _ _ _ _

lemma ιa_realChain {X : TopCat.{0}} {k n : ℕ} (σ : C(Δt k, X)) (v : Fin (n + 1) → Δt k) :
    ιa 𝕜 v ≫ (realChain 𝕜 σ).f n =
      (TopCat.toSSet.obj X).ιChainComplex ((X.toSSetObjEquiv _).symm (σ.comp (affMap v))) :=
  SSet.ι_chainComplexMap_f _ _ _ _ _

/-! ### The cone operator -/

/-- The cone with apex `b` on affine chains. -/
def coneHom {k : ℕ} (b : Δt k) (n : ℕ) : (affChains 𝕜 k).X n ⟶ (affChains 𝕜 k).X (n + 1) :=
  Sigma.desc (fun (v : Fin (n + 1) → Δt k) => ιa 𝕜 (Fin.cons b v))

@[simp] lemma ιa_coneHom {k n : ℕ} (b : Δt k) (v : Fin (n + 1) → Δt k) :
    ιa 𝕜 v ≫ coneHom 𝕜 b n = ιa 𝕜 (Fin.cons b v) :=
  Sigma.ι_desc _ _

/-- The augmentation of affine `0`-chains. -/
def epsHom (k : ℕ) : (affChains 𝕜 k).X 0 ⟶ ModuleCat.of 𝕜 𝕜 :=
  Sigma.desc (fun (_ : Fin 1 → Δt k) => 𝟙 (ModuleCat.of 𝕜 𝕜))

@[simp] lemma ιa_epsHom {k : ℕ} (v : Fin 1 → Δt k) :
    ιa 𝕜 v ≫ epsHom 𝕜 k = 𝟙 (ModuleCat.of 𝕜 𝕜) :=
  Sigma.ι_desc _ _

/-- The boundary of a cone in positive degrees. -/
theorem coneHom_d {k n : ℕ} (b : Δt k) :
    coneHom 𝕜 b (n + 1) ≫ (affChains 𝕜 k).d (n + 2) (n + 1) =
      𝟙 _ - (affChains 𝕜 k).d (n + 1) n ≫ coneHom 𝕜 b n := by
  refine affChains_hom_ext 𝕜 fun v => ?_
  have hL : ιa 𝕜 v ≫ coneHom 𝕜 b (n + 1) ≫ (affChains 𝕜 k).d (n + 2) (n + 1) =
      ∑ i : Fin (n + 3), (-1 : 𝕜) ^ (i : ℕ) •
        ιa 𝕜 ((Fin.cons b v : Fin (n + 3) → Δt k) ∘ i.succAbove) := by
    rw [← Category.assoc, ιa_coneHom 𝕜, ιa_d 𝕜]
  have hR : ιa 𝕜 v ≫ (𝟙 _ - (affChains 𝕜 k).d (n + 1) n ≫ coneHom 𝕜 b n) =
      ιa 𝕜 v - ∑ j : Fin (n + 2), (-1 : 𝕜) ^ (j : ℕ) •
        ιa 𝕜 (Fin.cons b ((v : Fin (n + 2) → Δt k) ∘ j.succAbove)) := by
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, ιa_d 𝕜,
      Preadditive.sum_comp]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Linear.smul_comp, ιa_coneHom 𝕜]
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
    coneHom 𝕜 b 0 ≫ (affChains 𝕜 k).d 1 0 = 𝟙 _ - epsHom 𝕜 k ≫ ιa 𝕜 (fun _ : Fin 1 => b) := by
  refine affChains_hom_ext 𝕜 fun v => ?_
  have hL : ιa 𝕜 v ≫ coneHom 𝕜 b 0 ≫ (affChains 𝕜 k).d 1 0 =
      ∑ i : Fin 2, (-1 : 𝕜) ^ (i : ℕ) • ιa 𝕜 ((Fin.cons b v : Fin 2 → Δt k) ∘ i.succAbove) := by
    rw [← Category.assoc, ιa_coneHom 𝕜, ιa_d 𝕜]
  have h0 : (Fin.cons b v : Fin 2 → Δt k) ∘ (0 : Fin 2).succAbove = v :=
    cons_comp_succAbove_zero b v
  have h1 : (Fin.cons b v : Fin 2 → Δt k) ∘ (1 : Fin 2).succAbove = (fun _ : Fin 1 => b) := by
    funext a
    fin_cases a
    rfl
  rw [hL, Preadditive.comp_sub, Category.comp_id, ← Category.assoc, ιa_epsHom 𝕜,
    Category.id_comp, Fin.sum_univ_two, h0, h1]
  simp [sub_eq_add_neg]

/-- The augmentation kills boundaries. -/
theorem d_epsHom {k : ℕ} : (affChains 𝕜 k).d 1 0 ≫ epsHom 𝕜 k = 0 := by
  refine affChains_hom_ext 𝕜 fun v => ?_
  rw [← Category.assoc, ιa_d 𝕜, Preadditive.sum_comp, comp_zero, Fin.sum_univ_two]
  simp

/-- Reassociated form of `d_epsHom 𝕜`. -/
lemma d_epsHom_comp {k : ℕ} {Z : ModuleCat.{0} 𝕜} (g : ModuleCat.of 𝕜 𝕜 ⟶ Z) :
    (affChains 𝕜 k).d 1 0 ≫ epsHom 𝕜 k ≫ g = 0 := by
  rw [← Category.assoc, d_epsHom 𝕜, Limits.zero_comp]

/-! ### Barycentric subdivision and its homotopy -/

/-- The barycentric subdivision operator on affine chains. -/
def sdHom (k : ℕ) : (n : ℕ) → ((affChains 𝕜 k).X n ⟶ (affChains 𝕜 k).X n) :=
  Nat.rec (motive := fun n => (affChains 𝕜 k).X n ⟶ (affChains 𝕜 k).X n) (𝟙 _)
    (fun n prev => Sigma.desc (fun (v : Fin (n + 2) → Δt k) =>
      ιa 𝕜 v ≫ (affChains 𝕜 k).d (n + 1) n ≫ prev ≫ coneHom 𝕜 (bary v) n))

lemma sdHom_zero (k : ℕ) : sdHom 𝕜 k 0 = 𝟙 _ := rfl

lemma ιa_sdHom_succ {k n : ℕ} (v : Fin (n + 2) → Δt k) :
    ιa 𝕜 v ≫ sdHom 𝕜 k (n + 1) =
      ιa 𝕜 v ≫ (affChains 𝕜 k).d (n + 1) n ≫ sdHom 𝕜 k n ≫ coneHom 𝕜 (bary v) n :=
  Sigma.ι_desc _ _

/-- The chain homotopy between the barycentric subdivision and the identity. -/
def tdHom (k : ℕ) : (n : ℕ) → ((affChains 𝕜 k).X n ⟶ (affChains 𝕜 k).X (n + 1)) :=
  Nat.rec (motive := fun n => (affChains 𝕜 k).X n ⟶ (affChains 𝕜 k).X (n + 1))
    (Sigma.desc (fun (v : Fin 1 → Δt k) => ιa 𝕜 v ≫ coneHom 𝕜 (bary v) 0))
    (fun n prev => Sigma.desc (fun (v : Fin (n + 2) → Δt k) =>
      (ιa 𝕜 v - ιa 𝕜 v ≫ (affChains 𝕜 k).d (n + 1) n ≫ prev) ≫ coneHom 𝕜 (bary v) (n + 1)))

lemma ιa_tdHom_zero {k : ℕ} (v : Fin 1 → Δt k) :
    ιa 𝕜 v ≫ tdHom 𝕜 k 0 = ιa 𝕜 v ≫ coneHom 𝕜 (bary v) 0 :=
  Sigma.ι_desc _ _

lemma ιa_tdHom_succ {k n : ℕ} (v : Fin (n + 2) → Δt k) :
    ιa 𝕜 v ≫ tdHom 𝕜 k (n + 1) =
      (ιa 𝕜 v - ιa 𝕜 v ≫ (affChains 𝕜 k).d (n + 1) n ≫ tdHom 𝕜 k n) ≫ coneHom 𝕜 (bary v) (n + 1) :=
  Sigma.ι_desc _ _

/-- Reassociated form of the recursion for the subdivision. -/
lemma ιa_sdHom_succ_comp {k n : ℕ} (v : Fin (n + 2) → Δt k) {Z : ModuleCat.{0} 𝕜}
    (g : (affChains 𝕜 k).X (n + 1) ⟶ Z) :
    ιa 𝕜 v ≫ sdHom 𝕜 k (n + 1) ≫ g =
      ιa 𝕜 v ≫ (affChains 𝕜 k).d (n + 1) n ≫ sdHom 𝕜 k n ≫ coneHom 𝕜 (bary v) n ≫ g := by
  rw [← Category.assoc, ιa_sdHom_succ 𝕜]
  simp only [Category.assoc]

/-- Reassociated form of the recursion for the homotopy. -/
lemma ιa_tdHom_succ_comp {k n : ℕ} (v : Fin (n + 2) → Δt k) {Z : ModuleCat.{0} 𝕜}
    (g : (affChains 𝕜 k).X (n + 2) ⟶ Z) :
    ιa 𝕜 v ≫ tdHom 𝕜 k (n + 1) ≫ g =
      (ιa 𝕜 v - ιa 𝕜 v ≫ (affChains 𝕜 k).d (n + 1) n ≫ tdHom 𝕜 k n) ≫
        coneHom 𝕜 (bary v) (n + 1) ≫ g := by
  rw [← Category.assoc, ιa_tdHom_succ 𝕜]
  simp only [Category.assoc]

/-- Reassociated form of the boundary of a cone. -/
lemma coneHom_d_comp {k n : ℕ} (b : Δt k) {Z : ModuleCat.{0} 𝕜}
    (g : (affChains 𝕜 k).X (n + 1) ⟶ Z) :
    coneHom 𝕜 b (n + 1) ≫ (affChains 𝕜 k).d (n + 2) (n + 1) ≫ g =
      g - (affChains 𝕜 k).d (n + 1) n ≫ coneHom 𝕜 b n ≫ g := by
  rw [← Category.assoc, coneHom_d 𝕜, Preadditive.sub_comp, Category.id_comp, Category.assoc]

/-- Reassociated form of the boundary of a cone in degree zero. -/
lemma coneHom_d_zero_comp {k : ℕ} (b : Δt k) {Z : ModuleCat.{0} 𝕜}
    (g : (affChains 𝕜 k).X 0 ⟶ Z) :
    coneHom 𝕜 b 0 ≫ (affChains 𝕜 k).d 1 0 ≫ g =
      g - epsHom 𝕜 k ≫ ιa 𝕜 (fun _ : Fin 1 => b) ≫ g := by
  rw [← Category.assoc, coneHom_d_zero 𝕜, Preadditive.sub_comp, Category.id_comp, Category.assoc]

/-- **The barycentric subdivision is a chain map.** -/
theorem sdHom_d (k n : ℕ) :
    sdHom 𝕜 k (n + 1) ≫ (affChains 𝕜 k).d (n + 1) n =
      (affChains 𝕜 k).d (n + 1) n ≫ sdHom 𝕜 k n := by
  induction n with
  | zero =>
    refine affChains_hom_ext 𝕜 fun v => ?_
    change ιa 𝕜 v ≫ sdHom 𝕜 k 1 ≫ (affChains 𝕜 k).d 1 0 =
      ιa 𝕜 v ≫ (affChains 𝕜 k).d 1 0 ≫ sdHom 𝕜 k 0
    rw [ιa_sdHom_succ_comp 𝕜, sdHom_zero 𝕜, Category.id_comp,
      show (affChains 𝕜 k).d (0 + 1) 0 = (affChains 𝕜 k).d 1 0 from rfl, coneHom_d_zero 𝕜]
    simp only [Preadditive.comp_sub, Category.comp_id, d_epsHom_comp 𝕜, sub_zero]
  | succ m ih =>
    refine affChains_hom_ext 𝕜 fun v => ?_
    rw [ιa_sdHom_succ_comp 𝕜, coneHom_d 𝕜, Preadditive.comp_sub, Category.comp_id,
      Preadditive.comp_sub, Preadditive.comp_sub,
      ← Category.assoc (sdHom 𝕜 k (m + 1)) ((affChains 𝕜 k).d (m + 1) m), ih, Category.assoc,
      ← Category.assoc ((affChains 𝕜 k).d (m + 1 + 1) (m + 1)) ((affChains 𝕜 k).d (m + 1) m),
      HomologicalComplex.d_comp_d, Limits.zero_comp, comp_zero, sub_zero]

/-- **The homotopy identity in degree zero.** -/
theorem tdHom_d_zero (k : ℕ) : tdHom 𝕜 k 0 ≫ (affChains 𝕜 k).d 1 0 = 𝟙 _ - sdHom 𝕜 k 0 := by
  refine affChains_hom_ext 𝕜 fun v => ?_
  rw [← Category.assoc, ιa_tdHom_zero 𝕜, Category.assoc, coneHom_d_zero 𝕜,
    Preadditive.comp_sub, Category.comp_id, ← Category.assoc, ιa_epsHom 𝕜, Category.id_comp,
    bary_zero, sdHom_zero 𝕜, Preadditive.comp_sub, Category.comp_id]

/-- The homotopy identity in degree `n + 1`, assuming the consequence
`∂T∂ = ∂ - ∂S` of the homotopy identity one degree down. -/
lemma tdHom_d_of_comp (k n : ℕ)
    (hcomp : (affChains 𝕜 k).d (n + 1) n ≫ tdHom 𝕜 k n ≫ (affChains 𝕜 k).d (n + 1) n =
      (affChains 𝕜 k).d (n + 1) n - (affChains 𝕜 k).d (n + 1) n ≫ sdHom 𝕜 k n) :
    tdHom 𝕜 k (n + 1) ≫ (affChains 𝕜 k).d (n + 2) (n + 1) +
        (affChains 𝕜 k).d (n + 1) n ≫ tdHom 𝕜 k n =
      𝟙 _ - sdHom 𝕜 k (n + 1) := by
  refine affChains_hom_ext 𝕜 fun v => ?_
  have h1 : ιa 𝕜 v ≫ tdHom 𝕜 k (n + 1) =
      (ιa 𝕜 v - ιa 𝕜 v ≫ (affChains 𝕜 k).d (n + 1) n ≫ tdHom 𝕜 k n) ≫ coneHom 𝕜 (bary v) (n + 1) :=
    ιa_tdHom_succ 𝕜 v
  have h2 : coneHom 𝕜 (bary v) (n + 1) ≫ (affChains 𝕜 k).d (n + 2) (n + 1) =
      𝟙 _ - (affChains 𝕜 k).d (n + 1) n ≫ coneHom 𝕜 (bary v) n := coneHom_d 𝕜 _
  have h3 : ιa 𝕜 v ≫ (affChains 𝕜 k).d (n + 1) n ≫ tdHom 𝕜 k n ≫ (affChains 𝕜 k).d (n + 1) n =
      ιa 𝕜 v ≫ (affChains 𝕜 k).d (n + 1) n -
        ιa 𝕜 v ≫ (affChains 𝕜 k).d (n + 1) n ≫ sdHom 𝕜 k n := by
    rw [hcomp, Preadditive.comp_sub]
  have h4 : ιa 𝕜 v ≫ sdHom 𝕜 k (n + 1) =
      ιa 𝕜 v ≫ (affChains 𝕜 k).d (n + 1) n ≫ sdHom 𝕜 k n ≫ coneHom 𝕜 (bary v) n :=
    ιa_sdHom_succ 𝕜 v
  have hX : (ιa 𝕜 v ≫ (affChains 𝕜 k).d (n + 1) n ≫ tdHom 𝕜 k n) ≫
        ((affChains 𝕜 k).d (n + 1) n ≫ coneHom 𝕜 (bary v) n) =
      ιa 𝕜 v ≫ (affChains 𝕜 k).d (n + 1) n ≫ coneHom 𝕜 (bary v) n -
        ιa 𝕜 v ≫ sdHom 𝕜 k (n + 1) := by
    have e : (ιa 𝕜 v ≫ (affChains 𝕜 k).d (n + 1) n ≫ tdHom 𝕜 k n) ≫
          ((affChains 𝕜 k).d (n + 1) n ≫ coneHom 𝕜 (bary v) n) =
        (ιa 𝕜 v ≫ (affChains 𝕜 k).d (n + 1) n ≫ tdHom 𝕜 k n ≫ (affChains 𝕜 k).d (n + 1) n) ≫
          coneHom 𝕜 (bary v) n := by
      simp only [Category.assoc]
    rw [e, h3, Preadditive.sub_comp, h4]
    simp only [Category.assoc]
  have hmain : ιa 𝕜 v ≫ tdHom 𝕜 k (n + 1) ≫ (affChains 𝕜 k).d (n + 2) (n + 1) =
      ιa 𝕜 v - ιa 𝕜 v ≫ (affChains 𝕜 k).d (n + 1) n ≫ tdHom 𝕜 k n - ιa 𝕜 v ≫ sdHom 𝕜 k (n + 1) := by
    rw [ιa_tdHom_succ_comp 𝕜, h2, Preadditive.comp_sub, Category.comp_id,
      Preadditive.sub_comp, hX]
    abel
  rw [Preadditive.comp_add, hmain]
  rw [Preadditive.comp_sub, Category.comp_id]
  abel

/-- **The homotopy identity `∂T + T∂ = 1 - S`.** -/
theorem tdHom_d (k n : ℕ) :
    tdHom 𝕜 k (n + 1) ≫ (affChains 𝕜 k).d (n + 2) (n + 1) +
        (affChains 𝕜 k).d (n + 1) n ≫ tdHom 𝕜 k n =
      𝟙 _ - sdHom 𝕜 k (n + 1) := by
  induction n with
  | zero =>
    refine tdHom_d_of_comp 𝕜 k 0 ?_
    have h := tdHom_d_zero 𝕜 k
    rw [sdHom_zero 𝕜, sub_self] at h
    change (affChains 𝕜 k).d 1 0 ≫ tdHom 𝕜 k 0 ≫ (affChains 𝕜 k).d 1 0 =
      (affChains 𝕜 k).d 1 0 - (affChains 𝕜 k).d 1 0 ≫ sdHom 𝕜 k 0
    rw [h, comp_zero, sdHom_zero 𝕜, Category.comp_id, sub_self]
  | succ m ih =>
    refine tdHom_d_of_comp 𝕜 k (m + 1) ?_
    have h : tdHom 𝕜 k (m + 1) ≫ (affChains 𝕜 k).d (m + 2) (m + 1) =
        𝟙 _ - sdHom 𝕜 k (m + 1) - (affChains 𝕜 k).d (m + 1) m ≫ tdHom 𝕜 k m := by
      rw [← ih]; abel
    change (affChains 𝕜 k).d (m + 2) (m + 1) ≫ tdHom 𝕜 k (m + 1) ≫
        (affChains 𝕜 k).d (m + 2) (m + 1) =
      (affChains 𝕜 k).d (m + 2) (m + 1) -
        (affChains 𝕜 k).d (m + 2) (m + 1) ≫ sdHom 𝕜 k (m + 1)
    rw [h, Preadditive.comp_sub, Preadditive.comp_sub, Category.comp_id,
      ← Category.assoc, HomologicalComplex.d_comp_d, Limits.zero_comp, sub_zero]

lemma pushChain_coneHom {k l n : ℕ} (w : Fin (k + 1) → Δt l) (b : Δt k) :
    coneHom 𝕜 b n ≫ (pushChain 𝕜 w).f (n + 1) =
      (pushChain 𝕜 w).f n ≫ coneHom 𝕜 (affPoint w b) n := by
  refine affChains_hom_ext 𝕜 fun v => ?_
  rw [← Category.assoc, ιa_coneHom 𝕜, ιa_pushChain 𝕜, ← Category.assoc, ιa_pushChain 𝕜,
    ιa_coneHom 𝕜, pushV_cons]

/-- Reassociated form of `pushChain_coneHom 𝕜`. -/
lemma pushChain_coneHom_comp {k l n : ℕ} (w : Fin (k + 1) → Δt l) (b : Δt k)
    {Z : ModuleCat.{0} 𝕜} (g : (affChains 𝕜 l).X (n + 1) ⟶ Z) :
    coneHom 𝕜 b n ≫ (pushChain 𝕜 w).f (n + 1) ≫ g =
      (pushChain 𝕜 w).f n ≫ coneHom 𝕜 (affPoint w b) n ≫ g := by
  rw [← Category.assoc, pushChain_coneHom 𝕜, Category.assoc]

theorem pushChain_sdHom {k l : ℕ} (w : Fin (k + 1) → Δt l) (n : ℕ) :
    sdHom 𝕜 k n ≫ (pushChain 𝕜 w).f n = (pushChain 𝕜 w).f n ≫ sdHom 𝕜 l n := by
  induction n with
  | zero => rw [sdHom_zero 𝕜, sdHom_zero 𝕜, Category.id_comp, Category.comp_id]
  | succ m ih =>
    refine affChains_hom_ext 𝕜 fun v => ?_
    have hR : ιa 𝕜 v ≫ (pushChain 𝕜 w).f (m + 1) ≫ sdHom 𝕜 l (m + 1) =
        ιa 𝕜 (fun a => affPoint w (v a)) ≫ (affChains 𝕜 l).d (m + 1) m ≫ sdHom 𝕜 l m ≫
          coneHom 𝕜 (bary (fun a => affPoint w (v a))) m := by
      rw [← Category.assoc (ιa 𝕜 v) ((pushChain 𝕜 w).f (m + 1)), ιa_pushChain 𝕜, ιa_sdHom_succ 𝕜]
    rw [ιa_sdHom_succ_comp 𝕜, hR, pushChain_coneHom 𝕜, ← Category.assoc (sdHom 𝕜 k m), ih,
      Category.assoc, ← Category.assoc ((affChains 𝕜 k).d (m + 1) m),
      ← (pushChain 𝕜 w).comm (m + 1) m, Category.assoc,
      ← Category.assoc (ιa 𝕜 v) ((pushChain 𝕜 w).f (m + 1)), ιa_pushChain 𝕜, bary_pushV]

theorem pushChain_tdHom {k l : ℕ} (w : Fin (k + 1) → Δt l) (n : ℕ) :
    tdHom 𝕜 k n ≫ (pushChain 𝕜 w).f (n + 1) = (pushChain 𝕜 w).f n ≫ tdHom 𝕜 l n := by
  induction n with
  | zero =>
    refine affChains_hom_ext 𝕜 fun v => ?_
    rw [← Category.assoc, ιa_tdHom_zero 𝕜, Category.assoc, pushChain_coneHom 𝕜,
      ← Category.assoc, ιa_pushChain 𝕜, ← Category.assoc (ιa 𝕜 v), ιa_pushChain 𝕜,
      ιa_tdHom_zero 𝕜, bary_pushV]
  | succ m ih =>
    refine affChains_hom_ext 𝕜 fun v => ?_
    have hR : ιa 𝕜 v ≫ (pushChain 𝕜 w).f (m + 1) ≫ tdHom 𝕜 l (m + 1) =
        (ιa 𝕜 (fun a => affPoint w (v a)) -
          (ιa 𝕜 (fun a => affPoint w (v a)) ≫ (affChains 𝕜 l).d (m + 1) m ≫ tdHom 𝕜 l m)) ≫
          coneHom 𝕜 (bary (fun a => affPoint w (v a))) (m + 1) := by
      rw [← Category.assoc (ιa 𝕜 v) ((pushChain 𝕜 w).f (m + 1)), ιa_pushChain 𝕜, ιa_tdHom_succ 𝕜]
    have hcross : (ιa 𝕜 (fun a => affPoint w (v a)) ≫ (affChains 𝕜 l).d (m + 1) m ≫ tdHom 𝕜 l m) =
        ιa 𝕜 v ≫ (affChains 𝕜 k).d (m + 1) m ≫ tdHom 𝕜 k m ≫ (pushChain 𝕜 w).f (m + 1) := by
      symm
      rw [ih, ← Category.assoc ((affChains 𝕜 k).d (m + 1) m) ((pushChain 𝕜 w).f m) (tdHom 𝕜 l m),
        ← (pushChain 𝕜 w).comm (m + 1) m,
        Category.assoc ((pushChain 𝕜 w).f (m + 1)) ((affChains 𝕜 l).d (m + 1) m) (tdHom 𝕜 l m),
        ← Category.assoc (ιa 𝕜 v) ((pushChain 𝕜 w).f (m + 1)), ιa_pushChain 𝕜]
    rw [ιa_tdHom_succ_comp 𝕜, hR, hcross, pushChain_coneHom 𝕜, bary_pushV,
      Preadditive.sub_comp, Preadditive.sub_comp,
      ← Category.assoc (ιa 𝕜 v) ((pushChain 𝕜 w).f (m + 1)), ιa_pushChain 𝕜]
    simp only [Category.assoc]

end AffineTverberg.Coefficients.AffChain
