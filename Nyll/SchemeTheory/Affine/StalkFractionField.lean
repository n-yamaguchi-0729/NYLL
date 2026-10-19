/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Actual affine-stalk fraction rings over the original scheme

The affine stalk isomorphism induces its fraction-ring isomorphism.
Its inverse Spec map intertwines the original localization morphism with
`fromSpecStalk`, including the fraction-ring maps. This comparison supplies
the actual scheme-stalk coordinates for generic fibres calculated in a
prime-localization model. No ring map comparison is an input.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- The fraction rings of the actual affine stalk and its prime-localization
model, using the existing canonical stalk isomorphism. -/
def Spec.stalkFractionRingEquiv (A : CommRingCat.{u}) (x : PrimeSpectrum A) :
    FractionRing ((Spec A).presheaf.stalk x) ≃+*
      FractionRing (Localization.AtPrime x.asIdeal) :=
  IsFractionRing.ringEquivOfRingEquiv (Spec.stalkIso A x).commRingCatIsoToRingEquiv

/-- The localization-model generic map and the actual stalk generic map
agree as morphisms to the original affine scheme. -/
theorem Spec.stalkFractionRingEquiv_over_base
    (A : CommRingCat.{u}) (x : PrimeSpectrum A) :
    Spec.map (CommRingCat.ofHom (Spec.stalkFractionRingEquiv A x).symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (Localization.AtPrime x.asIdeal)
            (FractionRing (Localization.AtPrime x.asIdeal)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime x.asIdeal))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap ((Spec A).presheaf.stalk x)
          (FractionRing ((Spec A).presheaf.stalk x)))) ≫
        (Spec A).fromSpecStalk x := by
  let R : CommRingCat.{u} := (Spec A).presheaf.stalk x
  let V := Localization.AtPrime x.asIdeal
  let e : R ≃+* V := (Spec.stalkIso A x).commRingCatIsoToRingEquiv
  have hcoeff :
      (Spec.stalkFractionRingEquiv A x).symm.toRingHom.comp
          (algebraMap V (FractionRing V)) =
        (algebraMap R (FractionRing R)).comp (Spec.stalkIso A x).inv.hom := by
    apply RingHom.ext
    intro v
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap e.symm v
  have hgeneric :
      Spec.map (CommRingCat.ofHom (Spec.stalkFractionRingEquiv A x).symm.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) =
        Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫
          Spec.map (Spec.stalkIso A x).inv := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext hcoeff)
  rw [← Category.assoc, hgeneric, Category.assoc, ← Spec.map_comp,
    Spec.algebraMap_stalkIso_inv]
  exact congrArg
    (fun φ : Spec R ⟶ Spec A =>
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ φ)
    (Spec.fromSpecStalk_eq A x).symm

end AlgebraicGeometry
