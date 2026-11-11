/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.HenselianNoetherianClosedFiberDiagram
public import Nyll.SchemeTheory.FiniteEtale.InverseLimitEquality
public import Nyll.SchemeTheory.FiniteEtale.InverseLimitIsoModels
public import Mathlib.CategoryTheory.Limits.IsLimit

/-!
# Finite-stage equalities and isomorphisms in the native closed-fibre system

The existing native closed-fibre diagram and limit retain the original
closed-fibre projections. They are reused without constructing a second
diagram, cone, or comparison.

Finite-etale equality and isomorphism descent are then applied to this
actual diagram and actual limit. No affine-transition, limit-comparison,
or finite-stage descent assumption is added to the proper-model inputs.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.HenselianNoetherianImageStages

attribute [local instance] FiniteEtale.finiteEtaleOverCategoryCoherence
  FiniteEtale.finiteEtaleHasPullbacksAlongCoherence
  FiniteEtale.finiteEtaleStableUnderBaseChangeAlongCoherence

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [HenselianLocalRing A]
variable {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of R))
variable {Z : Scheme.{u}}
  (j : Z ⟶ (SubalgebraImageApproximation.ambientCone (images R A) f₀).pt)

/-- Equality of two maps between native finite-etale stage covers which
holds over the original closed fibre already holds at an actual later stage. -/
theorem exists_native_closedFiber_stage_map_eq [IsProper f₀] [IsClosedImmersion j]
    (f : Z ⟶ Spec (CommRingCat.of A)) (hf : originalSchemeBaseMap R A f₀ j = f)
    (i : (FGSubalgebra R A)ᵒᵖ) {V W : FiniteEtale (stageClosedFiber R A f₀ j i)}
    (a b : V ⟶ W)
    (hab : (FiniteEtale.pullback (closedFiberStageMapOfBaseEq R A f₀ j f hf i)).map a =
      (FiniteEtale.pullback (closedFiberStageMapOfBaseEq R A f₀ j f hf i)).map b) :
    ∃ (k : (FGSubalgebra R A)ᵒᵖ) (hki : k ⟶ i),
      (FiniteEtale.pullback ((nativeClosedFiberDiagram R A f₀ j).map hki)).map a =
        (FiniteEtale.pullback ((nativeClosedFiberDiagram R A f₀ j).map hki)).map b :=
  FiniteEtale.exists_inverse_limit_stage_map_eq (nativeClosedFiberDiagram R A f₀ j)
    (nativeClosedFiberConeOfBaseEq R A f₀ j f hf)
    (nativeClosedFiberConeOfBaseEqIsLimit R A f₀ j f hf) i a b hab

/-- An actual isomorphism over the original closed fibre descends to an
actual isomorphism of native covers at a later henselian image stage,
retaining its original map through the canonical pullback comparison. -/
theorem exists_native_closedFiber_stage_iso [IsProper f₀] [IsClosedImmersion j]
    (f : Z ⟶ Spec (CommRingCat.of A)) (hf : originalSchemeBaseMap R A f₀ j = f)
    (i : (FGSubalgebra R A)ᵒᵖ) (V W : FiniteEtale (stageClosedFiber R A f₀ j i))
    (a : (FiniteEtale.pullback (closedFiberStageMapOfBaseEq R A f₀ j f hf i)).obj V ≅
      (FiniteEtale.pullback (closedFiberStageMapOfBaseEq R A f₀ j f hf i)).obj W) :
    ∃ (k : (FGSubalgebra R A)ᵒᵖ) (hki : k ⟶ i)
      (b : (FiniteEtale.pullback ((nativeClosedFiberDiagram R A f₀ j).map hki)).obj V ≅
        (FiniteEtale.pullback ((nativeClosedFiberDiagram R A f₀ j).map hki)).obj W),
      (FiniteEtale.inverseLimitPullbackComparison (nativeClosedFiberDiagram R A f₀ j)
        (nativeClosedFiberConeOfBaseEq R A f₀ j f hf) hki).hom.app V ≫
          (FiniteEtale.pullback (closedFiberStageMapOfBaseEq R A f₀ j f hf k)).map b.hom =
        a.hom ≫
          (FiniteEtale.inverseLimitPullbackComparison (nativeClosedFiberDiagram R A f₀ j)
            (nativeClosedFiberConeOfBaseEq R A f₀ j f hf) hki).hom.app W :=
  FiniteEtale.exists_inverse_limit_stage_iso (nativeClosedFiberDiagram R A f₀ j)
    (nativeClosedFiberConeOfBaseEq R A f₀ j f hf)
    (nativeClosedFiberConeOfBaseEqIsLimit R A f₀ j f hf) i V W a

end AlgebraicGeometry.HenselianNoetherianImageStages
