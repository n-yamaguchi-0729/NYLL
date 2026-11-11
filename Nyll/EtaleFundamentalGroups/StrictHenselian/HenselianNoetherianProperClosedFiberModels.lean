/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.HenselianNoetherianProperModel
import Nyll.EtaleFundamentalGroups.StrictHenselian.HenselianNoetherianClosedFiberModels

/-!
# Actual closed-fiber limits and cover models for proper finitely presented families

The proper model is constructed from the original finitely presented
family. Its original cartesian comparison is an isomorphism to the fixed
proper ambient base change, and hence supplies the closed embedding needed
by the actual image approximation. The resulting cone has the literal
original native closed fiber as its vertex. Finite étale covers recover
along the actual native stage projections.

This is the finitely presented part of the arbitrary-base argument.
No flatness, completion, G-ring property, or stage essential-surjectivity
hypothesis is inserted. The non-finitely-presented proper case is separate.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.HenselianNoetherianImageStages

variable (R A : Type u) [CommRing R] [IsNoetherianRing R]
  [CommRing A] [Algebra R A] [HenselianLocalRing A]

/-- The original proper finitely presented family supplies an actual
proper henselian model, an actual native closed-fiber limit, and recovered
finite étale models over the native closed fibers of its image stages. -/
theorem exists_proper_model_closedFiber_limit_and_cover_models
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [IsProper f] [LocallyOfFinitePresentation f] (s : Finset A) :
    ∃ (i : FGSubalgebra R A), (↑s : Set A) ⊆ image R A i ∧
      ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of (image R A i)))
        (π : X ⟶ X₀) (_hprop : IsProper f₀) (_hlfp : LocallyOfFinitePresentation f₀)
        (sq : IsPullback π f f₀
          (Spec.map (CommRingCat.ofHom (image R A i).val.toRingHom))),
      Nonempty (IsLimit (closedFiberConeOfBaseEq (image R A i) A f₀ sq.isoPullback.hom
        f sq.isoPullback_hom_snd)) ∧
      ∀ V : FiniteEtale (pullback f
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))),
        ∃ (k : (FGSubalgebra (image R A i) A)ᵒᵖ)
          (W : FiniteEtale
            (stageClosedFiber (image R A i) A f₀ sq.isoPullback.hom k)),
          Nonempty ((FiniteEtale.pullback
            (closedFiberStageMapOfBaseEq (image R A i) A f₀ sq.isoPullback.hom
              f sq.isoPullback_hom_snd k)).obj W ≅ V) := by
  obtain ⟨i, hs, X₀, f₀, π, hprop, hlfp, sq⟩ :=
    exists_proper_finitePresentation_model R A f s
  have : IsProper f₀ := hprop
  let e : X ≅
      (SubalgebraImageApproximation.ambientCone (images (image R A i) A) f₀).pt :=
    sq.isoPullback
  have : IsClosedImmersion e.hom := inferInstance
  refine ⟨i, hs, X₀, f₀, π, hprop, hlfp, sq, ?_, ?_⟩
  · exact ⟨closedFiberConeOfBaseEqIsLimit
      (image R A i) A f₀ e.hom f sq.isoPullback_hom_snd⟩
  · intro V
    exact exists_native_closedFiber_finiteEtale_model_of_base_eq
      (image R A i) A f₀ e.hom f sq.isoPullback_hom_snd V

end AlgebraicGeometry.HenselianNoetherianImageStages
