/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusTransition
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Final

/-! # Inverse systems of generalized Jacobians and cofinal modulus families -/

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {A : Type v} [Preorder A] (degree : A → ℕ)
  (D : ∀ a : A, RelEffCartierDiv c (degree a) (𝟙 (Spec (CommRingCat.of K))))
  (hD : ∀ {a b : A}, a ≤ b → (D b).I ≤ (D a).I)

/-- A growing family of actual divisors gives an inverse system of their constructed groups. -/
def transitionDiagram : Aᵒᵖ ⥤ CommGrp (Over (Spec (CommRingCat.of K))) where
  obj a := groupScheme c (D a.unop)
  map {a b} f := transition c (D a.unop) (D b.unop) (hD f.unop.le)
  map_id a := transition_id c (D a.unop)
  map_comp f g := (transition_comp c _ _ _ (hD f.unop.le) (hD g.unop.le)).symm

/-- Reindexing a family uses exactly the same whole-modulus restriction morphisms. -/
theorem transitionDiagram_reindex {B : Type w} [Preorder B]
    (f : B → A) (hf : Monotone f) :
    transitionDiagram c (degree ∘ f) (fun b => D (f b)) (fun h => hD (hf h)) =
      hf.functor.op ⋙ transitionDiagram c degree D hD := rfl

/-- Cofinal modulus subfamilies give equivalent categories of compatible cones.
This does not assume that an inverse limit group scheme exists. -/
def transitionDiagramCofinalConesEquiv {B : Type w} [Preorder B] [IsDirectedOrder B]
    (f : B → A) (hf : Monotone f) (hcofinal : ∀ a : A, ∃ b : B, a ≤ f b) :
    Cone (transitionDiagram c (degree ∘ f) (fun b => D (f b)) (fun h => hD (hf h))) ≌
      Cone (transitionDiagram c degree D hD) := by
  have : hf.functor.Final := hf.final_functor_iff.mpr hcofinal
  exact Functor.Initial.conesEquiv hf.functor.op (transitionDiagram c degree D hD)

end AlgebraicGeometry.GeneralizedJacobian
