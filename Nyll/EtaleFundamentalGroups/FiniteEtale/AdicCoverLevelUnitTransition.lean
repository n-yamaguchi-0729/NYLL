/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelUnit
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLevelPullbackModules

/-!
# Transition compatibility of the original cover quotient comparisons

The comparison from the actual quotient of a quasicoherent module to a
cover module retains the supplied map before restriction. The epimorphic
original quotient units therefore force these comparisons to commute
with the original transitions whenever the supplied maps do.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))
  (M : X.Modules) [M.IsQuasicoherent]
  (σ : ∀ n : ℕ, M ⟶ moduleSheaf f I V n)
  [∀ n : ℕ, IsIso
    ((Scheme.Modules.pullback (Limits.pullback.fst f (baseInclusion I n))).map (σ n))]
  (hσ : ∀ n : ℕ, σ (n + 1) ≫ moduleTransition f I V n = σ n)

include hσ

/-- The comparisons intertwine the actual quotient and cover transitions. -/
theorem moduleSheafLevelQuotientIso_hom_transition (n : ℕ) :
    (moduleSheafLevelQuotientIso f I V M (n + 1) (σ (n + 1))).hom ≫
        moduleTransition f I V n =
      levelPullbackTransition f I M n ≫
        (moduleSheafLevelQuotientIso f I V M n (σ n)).hom := by
  let e (k : ℕ) := moduleSheafLevelQuotientIso f I V M k (σ k)
  let η (k : ℕ) := levelPullbackUnit f I M k
  let t := moduleTransition f I V n
  let q := levelPullbackTransition f I M n
  apply (cancel_epi (η (n + 1))).mp
  calc
    η (n + 1) ≫ ((e (n + 1)).hom ≫ t) =
        (η (n + 1) ≫ (e (n + 1)).hom) ≫ t := (Category.assoc _ _ _).symm
    _ = σ (n + 1) ≫ t :=
      congrArg (fun a => a ≫ t)
        (levelUnit_moduleSheafLevelQuotientIso_hom f I V M (n + 1) (σ (n + 1)))
    _ = σ n := hσ n
    _ = η n ≫ (e n).hom :=
      (levelUnit_moduleSheafLevelQuotientIso_hom f I V M n (σ n)).symm
    _ = (η (n + 1) ≫ q) ≫ (e n).hom :=
      congrArg (fun a => a ≫ (e n).hom) (levelPullbackUnit_transition f I M n).symm
    _ = η (n + 1) ≫ (q ≫ (e n).hom) := Category.assoc _ _ _

/-- The inverse comparisons transport the original compatible cover maps
to compatible maps into the actual module quotients. -/
theorem moduleSheafLevelQuotientIso_inv_transition (n : ℕ) :
    (moduleSheafLevelQuotientIso f I V M (n + 1) (σ (n + 1))).inv ≫
        levelPullbackTransition f I M n =
      moduleTransition f I V n ≫
        (moduleSheafLevelQuotientIso f I V M n (σ n)).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact (moduleSheafLevelQuotientIso_hom_transition f I V M σ hσ n).symm

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
