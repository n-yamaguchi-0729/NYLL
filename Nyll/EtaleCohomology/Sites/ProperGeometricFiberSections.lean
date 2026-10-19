/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.GeometricStalkEvaluationCompatibility
import Nyll.EtaleCohomology.Sites.GeometricStalkSectionSurjectivity
import Nyll.EtaleCohomology.Sites.ProperGeometricStalkSections
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Proper geometric-fibre sections over an affine base

The actual direct-image stalk first maps to sections over the constructed
strictly local base. Evaluation then restricts these sections to the actual
geometric fibre. Both maps are proved bijective for proper morphisms and
arbitrary module sheaves. The value on every represented germ is the literal
inverse-image section map through the native geometric pullback.

Reference: Stacks Project, Lemma 59.91.4 (degree zero).
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

variable {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
  (φ : R →+* Ω) {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (Λ : Type u) [CommRing Λ]
  (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))

/-- The constructed comparison from a direct-image stalk to sections on
its actual geometric fibre, with no properness hypothesis in its definition. -/
def etalePushforwardGeometricFiberSections :
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).sheafFiber.obj
      ((etalePushforward f Λ).obj F) ⟶
        ((etalePullback (pullback.snd (Spec.map (CommRingCat.ofHom φ)) f) Λ).obj F).obj.obj
          (op (Scheme.Etale.mk (𝟙 _))) :=
  etalePushforwardGeometricStalkSections φ f Λ F ≫
    etaleGeometricStalkEvaluationSections φ f Λ F

/-- The geometric-fibre comparison sends a represented direct-image germ
to the actual inverse-image section through its native geometric factor. -/
theorem toPresheafFiber_etalePushforwardGeometricFiberSections
    (U : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.obj U) :
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).toPresheafFiber U v
        ((etalePushforward f Λ).obj F).obj ≫
      etalePushforwardGeometricFiberSections φ f Λ F =
      etalePullbackSectionMap
        (pullback.snd (Spec.map (CommRingCat.ofHom φ)) f) Λ F
        (U := Scheme.Etale.mk (𝟙 _)) (V := (etaleBaseChange f).obj U)
        ((Over.pullback f).map
          (show Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ Over.mk U.hom from v)).left
        ((((Over.pullback f).map
          (show Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ Over.mk U.hom from v)).w).trans
            (Category.id_comp _).symm) :=
  toPresheafFiber_geometricStalkSections_evaluation φ f Λ F U v

/-- For a proper morphism, the actual strict-local section comparison is
bijective for every module sheaf, without torsion or noetherian hypotheses. -/
theorem etalePushforwardGeometricStalkSections_bijective [IsProper f] :
    Function.Bijective (etalePushforwardGeometricStalkSections φ f Λ F) :=
  ⟨etalePushforwardGeometricStalkSections_injective φ f Λ F,
    etalePushforwardGeometricStalkSections_surjective φ f Λ F⟩

/-- Proper direct-image geometric stalks identify with sections on the
actual geometric fibre for every module sheaf. -/
theorem etalePushforwardGeometricFiberSections_bijective [IsProper f] :
    Function.Bijective (etalePushforwardGeometricFiberSections φ f Λ F) :=
  (etaleGeometricStalkEvaluationSections_bijective φ f Λ F).comp
    (etalePushforwardGeometricStalkSections_bijective φ f Λ F)

/-- The actual proper geometric-fibre comparison is an isomorphism of
coefficient modules. -/
instance etalePushforwardGeometricFiberSections_isIso [IsProper f] :
    IsIso (etalePushforwardGeometricFiberSections φ f Λ F) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (etalePushforwardGeometricFiberSections_bijective φ f Λ F)

end EtaleCohomology
