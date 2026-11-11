/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.HenselianNoetherianClosedFiberModels

/-!
# Recovery of the original closed fibre from an actual stage lift

An actual finite-etale lift on a henselian image stage pulls back along
its original scheme-cone projection. The proved closed-fibre square gives
a canonical pullback comparison, so this cover recovers the original
closed-fibre cover whenever the supplied stage lift recovers its actual
finite-stage model.

This is the recovery operation, not an existence theorem for stage lifts.
No completion, excellence, or approximation assertion is assumed or made.
-/

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

/-- Pulling a stage cover to the original scheme and then its closed fibre
agrees canonically with first restricting to the native stage closed fibre
and then pulling along the original native closed-fibre projection. -/
def nativeStageClosedFiberPullbackComparison
    (f : Z ⟶ Spec (CommRingCat.of A)) (hf : originalSchemeBaseMap R A f₀ j = f)
    (k : (FGSubalgebra R A)ᵒᵖ) :
    FiniteEtale.pullback ((schemeCone R A f₀ j).π.app k) ⋙
        FiniteEtale.pullback
          (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) ≅
      FiniteEtale.pullback
          (Limits.pullback.fst (schemeBaseMap R A f₀ j k)
            (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (image R A k.unop))))) ⋙
        FiniteEtale.pullback (closedFiberStageMapOfBaseEq R A f₀ j f hf k) := by
  let π : Z ⟶ (schemeDiagram R A f₀ j).obj k := (schemeCone R A f₀ j).π.app k
  let a : Limits.pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ⟶ Z :=
    Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))
  let q : stageClosedFiber R A f₀ j k ⟶ (schemeDiagram R A f₀ j).obj k :=
    Limits.pullback.fst (schemeBaseMap R A f₀ j k)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (image R A k.unop))))
  let t : Limits.pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ⟶
      stageClosedFiber R A f₀ j k := closedFiberStageMapOfBaseEq R A f₀ j f hf k
  have hsq : t ≫ q = a ≫ π := closedFiberStageMapOfBaseEq_fst R A f₀ j f hf k
  let c₁ : FiniteEtale.pullback (a ≫ π) ≅
      FiniteEtale.pullback π ⋙ FiniteEtale.pullback a :=
    MorphismProperty.Over.pullbackComp
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
      a π (a ≫ π) rfl
  let c₂ : FiniteEtale.pullback (a ≫ π) ≅
      FiniteEtale.pullback q ⋙ FiniteEtale.pullback t :=
    MorphismProperty.Over.pullbackComp
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
      t q (a ≫ π) hsq.symm
  exact c₁.symm ≪≫ c₂

/-- The concrete pullback of a supplied stage lift recovers the original
cover, using the supplied stage recovery and the original model recovery. -/
def nativeStageLiftClosedFiberIso
    (f : Z ⟶ Spec (CommRingCat.of A)) (hf : originalSchemeBaseMap R A f₀ j = f)
    (k : (FGSubalgebra R A)ᵒᵖ)
    (V : FiniteEtale ((schemeDiagram R A f₀ j).obj k))
    (Wk : FiniteEtale (stageClosedFiber R A f₀ j k))
    (e : (FiniteEtale.pullback
      (Limits.pullback.fst (schemeBaseMap R A f₀ j k)
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (image R A k.unop)))))).obj V ≅ Wk)
    (W : FiniteEtale
      (Limits.pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))))
    (hW : (FiniteEtale.pullback
      (closedFiberStageMapOfBaseEq R A f₀ j f hf k)).obj Wk ≅ W) :
    (FiniteEtale.pullback
      (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))).obj
        ((FiniteEtale.pullback ((schemeCone R A f₀ j).π.app k)).obj V) ≅ W :=
  (nativeStageClosedFiberPullbackComparison R A f₀ j f hf k).app V ≪≫
    (FiniteEtale.pullback (closedFiberStageMapOfBaseEq R A f₀ j f hf k)).mapIso e ≪≫ hW

/-- An actual lift of an actual finite-stage closed-fibre model gives a
finite-etale lift on the original scheme. The chosen lift is exactly the
pullback along the original scheme-cone projection. -/
theorem exists_finiteEtale_lift_of_native_stage_lift
    (f : Z ⟶ Spec (CommRingCat.of A)) (hf : originalSchemeBaseMap R A f₀ j = f)
    (k : (FGSubalgebra R A)ᵒᵖ)
    (V : FiniteEtale ((schemeDiagram R A f₀ j).obj k))
    (Wk : FiniteEtale (stageClosedFiber R A f₀ j k))
    (e : (FiniteEtale.pullback
      (Limits.pullback.fst (schemeBaseMap R A f₀ j k)
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (image R A k.unop)))))).obj V ≅ Wk)
    (W : FiniteEtale
      (Limits.pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))))
    (hW : (FiniteEtale.pullback
      (closedFiberStageMapOfBaseEq R A f₀ j f hf k)).obj Wk ≅ W) :
    ∃ U : FiniteEtale Z,
      Nonempty ((FiniteEtale.pullback
        (Limits.pullback.fst f
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))).obj U ≅ W) :=
  ⟨(FiniteEtale.pullback ((schemeCone R A f₀ j).π.app k)).obj V,
    ⟨nativeStageLiftClosedFiberIso R A f₀ j f hf k V Wk e W hW⟩⟩

end AlgebraicGeometry.HenselianNoetherianImageStages
