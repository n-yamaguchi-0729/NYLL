/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.FrameCoordinates
import Nyll.SchemeTheory.Affine.FiniteSchemeScalarFunctor

/-! The intrinsic modulus-unit functor on actual affine tests. -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open SchemeTheory.Affine SchemeTheory.Affine.FiniteScheme

namespace AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

variable {K : Type u} [Field K] {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of K))

/-- The actual affine parameter scheme with its given coefficient action. -/
abbrev spectrumTest (A : CommAlgCat.{u} K) : Over (Spec (CommRingCat.of K)) :=
  Over.mk (coefficientMap (K := K) A)

/-- A homomorphism of test algebras gives the corresponding parameter morphism. -/
def spectrumTestMap {A B : CommAlgCat.{u} K} (g : A ⟶ B) :
    spectrumTest B ⟶ spectrumTest A :=
  Over.homMk (Spec.map (CommRingCat.ofHom g.hom.toRingHom)) (coefficientMap_naturality g.hom)

/-- The two conventions for the fibre product give canonically isomorphic unit groups. -/
def affineFlipUnitsEquiv (A : CommAlgCat.{u} K) :
    Γ(pullback q (coefficientMap (K := K) A), ⊤)ˣ ≃* ModulusUnits q (spectrumTest A) :=
  Units.mapEquiv (Scheme.Γ.mapIso
    (pullbackSymmetry (coefficientMap (K := K) A) q).op).commRingCatIsoToRingEquiv.toMulEquiv

theorem affineFlipUnitsEquiv_scalar (A : CommAlgCat.{u} K)
    (s : Γ(Spec (CommRingCat.of A), ⊤)ˣ) :
    affineFlipUnitsEquiv q A
        (Units.map (pullback.snd q (coefficientMap (K := K) A)).appTop.hom.toMonoidHom s) =
      Units.map (modulusProjection q (spectrumTest A)).appTop.hom.toMonoidHom s := by
  apply Units.ext
  exact congrArg (fun f : Γ(Spec (CommRingCat.of A), ⊤) ⟶
    Γ(pullback (coefficientMap (K := K) A) q, ⊤) => f (s : Γ(Spec (CommRingCat.of A), ⊤)))
      (congrArg Scheme.Hom.appTop (pullbackSymmetry_hom_comp_snd (coefficientMap (K := K) A) q))

/-- Swapping the pullback factors preserves precisely the actual scalar subgroup. -/
def affineFlipScalarQuotientEquiv (A : CommAlgCat.{u} K) :
    BaseChangedScalarQuotient (A := A) q ≃*
      (modulusUnitQuotientPresheaf q).obj (op (spectrumTest A)) :=
  QuotientGroup.congr _ _ (affineFlipUnitsEquiv q A) (by
    ext a
    constructor
    · rintro ⟨x, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, (affineFlipUnitsEquiv_scalar q A s).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨Units.map
        (pullback.snd q (coefficientMap (K := K) A)).appTop.hom.toMonoidHom s,
        ⟨s, rfl⟩, affineFlipUnitsEquiv_scalar q A s⟩)

theorem nativeAffineMap_fst {A B : CommAlgCat.{u} K} (g : A ⟶ B) :
    ((Over.pullback q).map (spectrumTestMap g)).left ≫
        pullback.fst (coefficientMap (K := K) A) q =
      pullback.fst (coefficientMap (K := K) B) q ≫ Spec.map (CommRingCat.ofHom g.hom.toRingHom) :=
  pullback.lift_fst _ _ _

theorem nativeAffineMap_snd {A B : CommAlgCat.{u} K} (g : A ⟶ B) :
    ((Over.pullback q).map (spectrumTestMap g)).left ≫
        pullback.snd (coefficientMap (K := K) A) q =
      pullback.snd (coefficientMap (K := K) B) q := pullback.lift_snd _ _ _

theorem affineFlip_square {A B : CommAlgCat.{u} K} (g : A ⟶ B) :
    ((Over.pullback q).map (spectrumTestMap g)).left ≫
        (pullbackSymmetry (coefficientMap (K := K) A) q).hom =
      (pullbackSymmetry (coefficientMap (K := K) B) q).hom ≫ coefficientPullbackMap q g.hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_fst,
      coefficientPullbackMap_fst]
    exact nativeAffineMap_snd q g
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_snd,
      coefficientPullbackMap_snd]
    rw [← Category.assoc, pullbackSymmetry_hom_comp_snd]
    exact nativeAffineMap_fst q g

/-- Restriction of units commutes with the actual pullback symmetry. -/
theorem affineFlipUnitsEquiv_naturality {A B : CommAlgCat.{u} K} (g : A ⟶ B)
    (a : Γ(pullback q (coefficientMap (K := K) A), ⊤)ˣ) :
    affineFlipUnitsEquiv q B
        (Units.map (coefficientPullbackMap q g.hom).appTop.hom.toMonoidHom a) =
      modulusUnitMap q (spectrumTestMap g) (affineFlipUnitsEquiv q A a) := by
  apply Units.ext
  exact (congrArg (fun f : Γ(pullback q (coefficientMap (K := K) A), ⊤) ⟶
    Γ(pullback (coefficientMap (K := K) B) q, ⊤) =>
      f (a : Γ(pullback q (coefficientMap (K := K) A), ⊤)))
        (congrArg Scheme.Hom.appTop (affineFlip_square q g))).symm

theorem affineFlipScalarQuotientEquiv_naturality {A B : CommAlgCat.{u} K} (g : A ⟶ B)
    (x : BaseChangedScalarQuotient (A := A) q) :
    affineFlipScalarQuotientEquiv q B (baseChangedScalarQuotientMap q g.hom x) =
      modulusUnitQuotientMap q (spectrumTestMap g) (affineFlipScalarQuotientEquiv q A x) := by
  refine QuotientGroup.induction_on x fun a => ?_
  exact congrArg (fun a : ModulusUnits q (spectrumTest B) =>
    (QuotientGroup.mk a : ModulusUnits q (spectrumTest B) ⧸ modulusScalars q (spectrumTest B)))
      (affineFlipUnitsEquiv_naturality q g a)

variable [IsFinite q]

/-- The intrinsic scheme-valued unit quotient has the proved geometric affine restriction. -/
def modulusUnitAffineRestrictionIso :
    (opOpEquivalence (CommAlgCat.{u} K)).functor ⋙ baseChangedScalarQuotientFunctor q ≅
      (specOverFunctor (CommRingCat.of K)).op ⋙ modulusUnitQuotientPresheaf q :=
  NatIso.ofComponents
    (fun A => (affineFlipScalarQuotientEquiv q A.unop.unop).toCommGrpIso)
    (fun g => by
      apply ConcreteCategory.hom_ext
      exact affineFlipScalarQuotientEquiv_naturality q g.unop.unop)

/-- Algebraic scalar classes and intrinsic modulus classes agree naturally on affine tests. -/
def algebraicModulusUnitAffineIso :
    (opOpEquivalence (CommAlgCat.{u} K)).functor ⋙
        ScalarQuotientPresheaf.quotientFunctor K (coordinateAlgebra q) ≅
      (specOverFunctor (CommRingCat.of K)).op ⋙ modulusUnitQuotientPresheaf q :=
  Functor.isoWhiskerLeft _ (baseChangedScalarQuotientFunctorIso q) ≪≫
    modulusUnitAffineRestrictionIso q

end AlgebraicGeometry.GeneralizedJacobian.ScalarFrames
