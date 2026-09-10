import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Topology.Category.TopCat.Basic

set_option linter.style.header false

/-!
# The final cohomological obstruction

This file formalizes the diagram chase in lines 462--481 of
`affine-tverberg17.tex`.  It is deliberately independent of a particular
construction of reduced cohomology: any contravariant functor from spaces to
modules has the required functoriality.

For maps `Y → X → S`, the pullback `H(S) → H(Y)` factors through `H(X)`.
Consequently it cannot be injective when `H(S)` is nontrivial and `H(X)` is
trivial.  In the application, `S` is the sphere, `X` is the face-incidence
space, and `Y` is the top-locus incidence space.
-/

noncomputable section

open CategoryTheory

namespace AffineTverberg

section LinearDiagram

variable {𝕜 A B C : Type*} [Semiring 𝕜]
  [AddCommMonoid A] [Module 𝕜 A]
  [AddCommMonoid B] [Module 𝕜 B]
  [AddCommMonoid C] [Module 𝕜 C]

/-- An injective composite cannot factor through a subsingleton module when
its source module is nontrivial. -/
theorem not_injective_comp_of_subsingleton
    [Nontrivial A] [Subsingleton B]
    (f : A →ₗ[𝕜] B) (g : B →ₗ[𝕜] C) :
    ¬ Function.Injective (g.comp f) := by
  intro hinjective
  obtain ⟨a, b, hab⟩ := exists_pair_ne A
  apply hab
  apply hinjective
  exact congrArg g (Subsingleton.elim (f a) (f b))

end LinearDiagram

section ContravariantFunctor

universe u v w q

variable {𝕜 : Type u} [Ring 𝕜]
  {C : Type v} [Category.{w} C]

/-- The final obstruction in functorial form.  If `H` is a contravariant
cohomology functor and `Y → X → S` is the projection factorization from the
paper, injectivity of the pullback `H(S) → H(Y)` contradicts vanishing of
`H(X)` and nonvanishing of `H(S)`.

This theorem contains only the formal diagram chase; the two substantive
inputs in the paper are supplied separately by Leray--Vietoris--Begle and the
deleted-join acyclicity lemma. -/
theorem cohomological_obstruction
    (H : Cᵒᵖ ⥤ ModuleCat.{q} 𝕜)
    {S X Y : C} (i : Y ⟶ X) (p : X ⟶ S)
    [Nontrivial (H.obj (Opposite.op S))]
    [Subsingleton (H.obj (Opposite.op X))] :
    ¬ Function.Injective (H.map (i ≫ p).op) := by
  intro hinjective
  apply not_injective_comp_of_subsingleton
    (H.map p.op).hom (H.map i.op).hom
  intro a b hab
  apply hinjective
  rw [show (i ≫ p).op = p.op ≫ i.op by rfl, Functor.map_comp]
  exact hab

/-- Equivalent map-equality form, convenient when the projection on `Y` is
named separately and then identified with the composite `Y → X → S`. -/
theorem cohomological_obstruction_of_projection_eq
    (H : Cᵒᵖ ⥤ ModuleCat.{q} 𝕜)
    {S X Y : C} (i : Y ⟶ X) (pX : X ⟶ S) (pY : Y ⟶ S)
    (hpY : pY = i ≫ pX)
    [Nontrivial (H.obj (Opposite.op S))]
    [Subsingleton (H.obj (Opposite.op X))] :
    ¬ Function.Injective (H.map pY.op) := by
  subst pY
  exact cohomological_obstruction H i pX

end ContravariantFunctor

end AffineTverberg
