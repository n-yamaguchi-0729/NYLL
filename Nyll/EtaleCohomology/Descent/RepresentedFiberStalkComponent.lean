/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
public import Nyll.EtaleCohomology.Descent.RepresentedGeometricFiberComponent
public import Nyll.EtaleCohomology.Descent.RepresentedGeometricFiberSections
public import Nyll.EtaleCohomology.Descent.RepresentedSectionEvaluationNaturality
public import Nyll.EtaleCohomology.Sites.PushforwardStalkComparison

/-!
# The original affine stalk component is geometric restriction

The general original germ calculation specializes to the existing affine
strict-local comparison followed by its original geometric evaluation.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace EtaleCohomology

variable {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
  (φ : R →+* Ω) {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of R))
  (s : Spec (CommRingCat.of Ω) ⟶ Y)
  (hs : s ≫ q = Spec.map (CommRingCat.ofHom φ)) (W : Y.Etale)

/-- The original direct-image stalk component at the specified lift is
the actual geometric-fiber section comparison followed by literal
restriction to that lift, through the existing represented-stalk iso. -/
theorem etaleSetPushforwardRepresentableGeometricFiberSections_component :
    etalePushforwardStalkComponent q (Spec.map (CommRingCat.ofHom φ)) ⟨s, hs⟩
        (Y.smallEtaleTopology.yoneda.obj W) ≫
      (representableSheafFiberIso (Scheme.pointSmallEtale s)).hom.app W =
    etaleSetPushforwardRepresentableGeometricFiberSections φ q W ≫
      representedGeometricFiberRestriction q (Spec.map (CommRingCat.ofHom φ)) s hs W := by
  have h := etaleSetPushforwardRepresentableFiberSections_component q
    (Spec.map (CommRingCat.ofHom φ)) s hs W
  have he := etaleSetPushforwardRepresentableFiberSections_eq_affine φ q W
  exact h.trans (congrArg
    (fun c => c ≫ representedGeometricFiberRestriction q
      (Spec.map (CommRingCat.ofHom φ)) s hs W) he)

end EtaleCohomology
