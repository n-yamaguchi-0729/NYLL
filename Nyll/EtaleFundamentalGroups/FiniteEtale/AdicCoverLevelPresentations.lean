/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelTwists
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLevelPullbackModules
import Nyll.SchemeTheory.Modules.Functoriality.ClosedImmersionUnit
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.EpiMono

/-!
# Presentations on the original closed levels

A morphism into a twisted cover module factors through the actual
pullback quotient of its source. The factor is constructed by the
original adjunction and the proved direct-image comparison. It retains
the prescribed source map after composition with the original unit.

Epimorphic source maps therefore give epimorphic presentations on the
closed levels. Compatible source maps give a commuting square with the
original level transitions. In particular, free source maps constructed
from compatible global generators give presentations by the free modules
on the thickenings themselves.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))
  (L P : X.Modules) [L.IsQuasicoherent]

/-- The original adjoint gives a presentation whose source is the actual
pullback quotient on the specified closed level. -/
def levelPresentation (n : ℕ) (α : P ⟶ moduleSheaf f I V n ⊗ L) :
    levelPullbackModule f I P n ⟶ moduleSheaf f I V n ⊗ L :=
  let i : level f I n ⟶ X := Limits.pullback.fst f (baseInclusion I n)
  let C : (level f I n).Modules := coverLevelTwistedModule f I V L n
  let e : moduleSheaf f I V n ⊗ L ≅ (pushforward i).obj C :=
    moduleSheafTwistedLevelIso f I V L n
  pushforwardAdjointFactor i (α ≫ e.hom) ≫ e.inv

/-- The constructed level presentation recovers the original source map. -/
theorem levelUnit_levelPresentation (n : ℕ) (α : P ⟶ moduleSheaf f I V n ⊗ L) :
    levelPullbackUnit f I P n ≫ levelPresentation f I V L P n α = α := by
  let i : level f I n ⟶ X := Limits.pullback.fst f (baseInclusion I n)
  let C : (level f I n).Modules := coverLevelTwistedModule f I V L n
  let e : moduleSheaf f I V n ⊗ L ≅ (pushforward i).obj C :=
    moduleSheafTwistedLevelIso f I V L n
  let η : P ⟶ (pushforward i).obj ((Scheme.Modules.pullback i).obj P) :=
    (pullbackPushforwardAdjunction i).unit.app P
  let β : (pushforward i).obj ((Scheme.Modules.pullback i).obj P) ⟶
      (pushforward i).obj C := pushforwardAdjointFactor i (α ≫ e.hom)
  have h : η ≫ β = α ≫ e.hom := unit_pushforwardAdjointFactor i (α ≫ e.hom)
  calc
    η ≫ (β ≫ e.inv) = (η ≫ β) ≫ e.inv := (Category.assoc η β e.inv).symm
    _ = (α ≫ e.hom) ≫ e.inv := congrArg (fun k => k ≫ e.inv) h
    _ = α := by rw [Category.assoc, e.hom_inv_id, Category.comp_id]

/-- An epimorphic source map gives an epimorphic actual level presentation. -/
theorem levelPresentation_epi (n : ℕ) (α : P ⟶ moduleSheaf f I V n ⊗ L) [Epi α] :
    Epi (levelPresentation f I V L P n α) :=
  epi_of_epi_fac (levelUnit_levelPresentation f I V L P n α)

variable [P.IsQuasicoherent]
  (α : ∀ n : ℕ, P ⟶ moduleSheaf f I V n ⊗ L)
  (hα : ∀ n : ℕ, α (n + 1) ≫ (moduleTransition f I V n ▷ L) = α n)

include hα in
/-- Compatibility on the ambient module descends to the original quotient
modules, because their original units are epimorphisms. -/
theorem levelPresentation_transition (n : ℕ) :
    levelPresentation f I V L P (n + 1) (α (n + 1)) ≫
        (moduleTransition f I V n ▷ L) =
      levelPullbackTransition f I P n ≫ levelPresentation f I V L P n (α n) := by
  let η₁ : P ⟶ levelPullbackModule f I P (n + 1) := levelPullbackUnit f I P (n + 1)
  let η₀ : P ⟶ levelPullbackModule f I P n := levelPullbackUnit f I P n
  let π₁ : levelPullbackModule f I P (n + 1) ⟶ moduleSheaf f I V (n + 1) ⊗ L :=
    levelPresentation f I V L P (n + 1) (α (n + 1))
  let π₀ : levelPullbackModule f I P n ⟶ moduleSheaf f I V n ⊗ L :=
    levelPresentation f I V L P n (α n)
  let δ : levelPullbackModule f I P (n + 1) ⟶ levelPullbackModule f I P n :=
    levelPullbackTransition f I P n
  let τ : moduleSheaf f I V (n + 1) ⊗ L ⟶ moduleSheaf f I V n ⊗ L :=
    moduleTransition f I V n ▷ L
  have : Epi η₁ := levelPullbackUnit_epi f I P (n + 1)
  have h₁ : η₁ ≫ π₁ = α (n + 1) :=
    levelUnit_levelPresentation f I V L P (n + 1) (α (n + 1))
  have h₀ : η₀ ≫ π₀ = α n := levelUnit_levelPresentation f I V L P n (α n)
  have hδ : η₁ ≫ δ = η₀ := levelPullbackUnit_transition f I P n
  apply (cancel_epi η₁).mp
  calc
    η₁ ≫ (π₁ ≫ τ) = (η₁ ≫ π₁) ≫ τ := (Category.assoc η₁ π₁ τ).symm
    _ = α (n + 1) ≫ τ := congrArg (fun k => k ≫ τ) h₁
    _ = α n := hα n
    _ = η₀ ≫ π₀ := h₀.symm
    _ = (η₁ ≫ δ) ≫ π₀ := congrArg (fun k => k ≫ π₀) hδ.symm
    _ = η₁ ≫ (δ ≫ π₀) := Category.assoc η₁ δ π₀

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
