/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.HenselianNoetherianImageStages
import Nyll.SchemeTheory.Descent.FgSubalgebraProperFlatPullback

/-!
# Proper finitely presented models over actual henselian image stages

First descend the original proper finitely presented morphism to an actual
finite-type coefficient subalgebra using the existing model, separatedness,
and properness descent. Base change along its constructed inclusion into
the actual henselization image supplies a proper model over the same
henselian Noetherian approximation family. No flatness assumption is used.

The finite-presentation hypothesis is explicit here; it is not added to
the final arbitrary-proper henselian comparison.
-/

noncomputable section

universe u

open CategoryTheory Limits
open AlgebraicCurves.Geometry.Schemes.Proofs.ProperFlatFinitePresentationDescent.ApproxAux

namespace AlgebraicGeometry.HenselianNoetherianImageStages

variable (R A : Type u) [CommRing R] [IsNoetherianRing R]
  [CommRing A] [Algebra R A] [HenselianLocalRing A]

/-- An original proper finitely presented morphism descends to an actual
henselian image stage, retaining any specified finite set of coefficients. -/
theorem exists_proper_finitePresentation_model
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [IsProper f] [LocallyOfFinitePresentation f] (s : Finset A) :
    ∃ (i : FGSubalgebra R A), (↑s : Set A) ⊆ image R A i ∧
      ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of (image R A i)))
        (π : X ⟶ X₀), IsProper f₀ ∧ LocallyOfFinitePresentation f₀ ∧
          IsPullback π f f₀ (Spec.map (CommRingCat.ofHom (image R A i).val.toRingHom)) := by
  classical
  obtain ⟨T, hT, hs, X₁, f₁, π₁, hprop₁, hlfp₁, sq₁⟩ :=
    ProperFinitePresentationDescent (A₀ := R) f s
  let i : FGSubalgebra R A := ⟨T, hT⟩
  let κ : Spec (CommRingCat.of (image R A i)) ⟶ Spec (CommRingCat.of T) :=
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (subalgebra_le_image R A i)).toRingHom)
  let σ : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (image R A i)) :=
    Spec.map (CommRingCat.ofHom (image R A i).val.toRingHom)
  have hκ : σ ≫ κ = Spec.map (CommRingCat.ofHom (algebraMap T A)) := by
    dsimp only [σ, κ]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  obtain ⟨π₀, sq₀⟩ := exists_isPullback_of_fac sq₁ κ σ hκ
  have : IsProper f₁ := hprop₁
  have : LocallyOfFinitePresentation f₁ := hlfp₁
  have : MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    locallyOfFinitePresentation_isStableUnderBaseChange
  have hlfp₀ : LocallyOfFinitePresentation (pullback.snd f₁ κ) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback f₁ κ) hlfp₁
  refine ⟨i, ?_, pullback f₁ κ, pullback.snd f₁ κ, π₀, inferInstance, hlfp₀, sq₀⟩
  intro a ha
  exact subalgebra_le_image R A i (hs ha)

end AlgebraicGeometry.HenselianNoetherianImageStages
