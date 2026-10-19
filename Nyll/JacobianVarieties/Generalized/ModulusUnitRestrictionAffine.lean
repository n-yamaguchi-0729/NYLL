/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusUnitRestriction
import Nyll.SchemeTheory.Affine.FiniteSchemeUnitRestrictionGeometry
import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientRestrictionSheaf

/-! # Actual affine comparison for changing the modulus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open SchemeTheory.Affine SchemeTheory.Affine.FiniteScheme
open scoped TensorProduct

namespace SchemeTheory.Affine.ScalarQuotientPresheaf

variable {R A B S T : Type u} [CommRing R] [CommRing A] [CommRing B]
  [CommRing S] [CommRing T] [Algebra R A] [Algebra R B] [Algebra R S] [Algebra R T]

/-- Algebra restriction commutes with change of the parameter algebra on scalar classes. -/
theorem algebraQuotientRestriction_naturality (f : A →ₐ[R] B) (g : S →ₐ[R] T)
    (x : ScalarQuotient (R := R) (A := A) (S := S)) :
    algebraQuotientRestriction f (quotientMap g x) =
      quotientMap g (algebraQuotientRestriction f x) := by
  refine QuotientGroup.induction_on x fun a => ?_
  exact congrArg QuotientGroup.mk (algebraUnitRestriction_naturality f g a)

end SchemeTheory.Affine.ScalarQuotientPresheaf

namespace AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

variable {K : Type u} [Field K] {Y Y' : Scheme.{u}}
  {q : Y ⟶ Spec (CommRingCat.of K)} {q' : Y' ⟶ Spec (CommRingCat.of K)}
  (j : Y' ⟶ Y) (w : j ≫ q = q')

/-- The actual affine-test restriction in the modulus-first pullback convention. -/
def affineUnitRestrictionPullback (S : CommAlgCat.{u} K) :
    pullback q' (coefficientMap (K := K) S) ⟶ pullback q (coefficientMap (K := K) S) :=
  pullback.lift (pullback.fst q' _ ≫ j) (pullback.snd q' _) (by
    rw [Category.assoc, w, pullback.condition])

@[reassoc] theorem affineUnitRestrictionPullback_fst (S : CommAlgCat.{u} K) :
    affineUnitRestrictionPullback j w S ≫ pullback.fst q (coefficientMap (K := K) S) =
      pullback.fst q' (coefficientMap (K := K) S) ≫ j := pullback.lift_fst _ _ _

@[reassoc] theorem affineUnitRestrictionPullback_snd (S : CommAlgCat.{u} K) :
    affineUnitRestrictionPullback j w S ≫ pullback.snd q (coefficientMap (K := K) S) =
      pullback.snd q' (coefficientMap (K := K) S) := pullback.lift_snd _ _ _

/-- Pullback of sections restricts the actual modulus factor. -/
theorem affineUnitRestrictionPullback_source (S : CommAlgCat.{u} K) (x : Γ(Y, ⊤)) :
    (affineUnitRestrictionPullback j w S).appTop
        ((pullback.fst q (coefficientMap (K := K) S)).appTop x) =
      (pullback.fst q' (coefficientMap (K := K) S)).appTop (j.appTop x) :=
  congrArg (fun f : Γ(Y, ⊤) ⟶ Γ(pullback q' (coefficientMap (K := K) S), ⊤) => f x)
    (congrArg Scheme.Hom.appTop (affineUnitRestrictionPullback_fst j w S))

/-- Pullback of sections fixes the actual coefficient scalar. -/
theorem affineUnitRestrictionPullback_scalar (S : CommAlgCat.{u} K) (a : S) :
    (affineUnitRestrictionPullback j w S).appTop (coefficientScalarMap q S a) =
      coefficientScalarMap q' S a :=
  congrArg (fun f : Γ(Spec (CommRingCat.of S), ⊤) ⟶
      Γ(pullback q' (coefficientMap (K := K) S), ⊤) =>
    f ((Scheme.ΓSpecIso (CommRingCat.of S)).inv a))
      (congrArg Scheme.Hom.appTop (affineUnitRestrictionPullback_snd j w S))

variable [IsFinite q] [IsFinite q']

/-- The canonical tensor-to-sections equivalence commutes with restriction of the
actual finite modulus, as a computation on both tensor factors. -/
theorem coordinateAlgebraBaseChangeEquiv_restriction (S : CommAlgCat.{u} K)
    (x : S ⊗[K] coordinateAlgebra q) :
    coordinateAlgebraBaseChangeEquiv (A := S) q'
        (Algebra.TensorProduct.map (AlgHom.id K S) (coordinateRestriction q q' j w) x) =
      (affineUnitRestrictionPullback j w S).appTop
        (coordinateAlgebraBaseChangeEquiv (A := S) q x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    exact (map_add (affineUnitRestrictionPullback j w S).appTop.hom
      (coordinateAlgebraBaseChangeEquiv (A := S) q x)
      (coordinateAlgebraBaseChangeEquiv (A := S) q y)).symm
  | tmul a x =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have hm := congrArg₂
      (fun a b : Γ(pullback q' (coefficientMap (K := K) S), ⊤) => a * b)
      (affineUnitRestrictionPullback_scalar j w S a).symm
      (affineUnitRestrictionPullback_source j w S x).symm
    have hmul := (map_mul (affineUnitRestrictionPullback j w S).appTop.hom
      (coefficientScalarMap q S a)
      ((pullback.fst q (coefficientMap (K := K) S)).appTop x)).symm
    have ht := congrArg (affineUnitRestrictionPullback j w S).appTop
      (coordinateAlgebraBaseChangeEquiv_tmul q a x).symm
    exact (coordinateAlgebraBaseChangeEquiv_tmul q' a
      (coordinateRestriction q q' j w x)).trans (hm.trans (hmul.trans ht))

omit [IsFinite q] [IsFinite q'] in
/-- The intrinsic and modulus-first conventions commute with the same actual restriction. -/
theorem affineFlip_restriction_square (S : CommAlgCat.{u} K) :
    unitRestrictionPullback j w (spectrumTest S) ≫
        (pullbackSymmetry (coefficientMap (K := K) S) q).hom =
      (pullbackSymmetry (coefficientMap (K := K) S) q').hom ≫
        affineUnitRestrictionPullback j w S := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_fst,
      affineUnitRestrictionPullback_fst]
    rw [← Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact unitRestrictionPullback_snd j w (spectrumTest S)
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_snd,
      affineUnitRestrictionPullback_snd]
    exact unitRestrictionPullback_fst j w (spectrumTest S)

omit [IsFinite q] [IsFinite q'] in
/-- Swapping the pullback factors preserves actual unit restriction. -/
theorem affineFlipUnitsEquiv_restriction (S : CommAlgCat.{u} K)
    (a : Γ(pullback q (coefficientMap (K := K) S), ⊤)ˣ) :
    affineFlipUnitsEquiv q' S
        (Units.map (affineUnitRestrictionPullback j w S).appTop.hom.toMonoidHom a) =
      modulusUnitsRestriction j w (spectrumTest S) (affineFlipUnitsEquiv q S a) := by
  apply Units.ext
  exact (congrArg (fun f : Γ(pullback q (coefficientMap (K := K) S), ⊤) ⟶
      Γ(pullback (coefficientMap (K := K) S) q', ⊤) =>
    f (a : Γ(pullback q (coefficientMap (K := K) S), ⊤)))
      (congrArg Scheme.Hom.appTop (affineFlip_restriction_square j w S))).symm

/-- The proved affine scalar-class comparison preserves changing-modulus restriction. -/
theorem algebraicModulusUnitAffineIso_restriction (S : CommAlgCat.{u} K)
    (x : ScalarQuotientPresheaf.ScalarQuotient
      (R := K) (A := coordinateAlgebra q) (S := S)) :
    ((algebraicModulusUnitAffineIso q').hom.app (op (op S)))
        (ScalarQuotientPresheaf.algebraQuotientRestriction (coordinateRestriction q q' j w) x) =
      modulusUnitQuotientRestriction j w (spectrumTest S)
        (((algebraicModulusUnitAffineIso q).hom.app (op (op S))) x) := by
  refine QuotientGroup.induction_on x fun a => ?_
  change QuotientGroup.mk (affineFlipUnitsEquiv q' S
      (Units.mapEquiv (coordinateAlgebraBaseChangeEquiv (A := S) q').toMulEquiv
        (ScalarQuotientPresheaf.algebraUnitRestriction (coordinateRestriction q q' j w) a))) =
    QuotientGroup.mk (modulusUnitsRestriction j w (spectrumTest S)
      (affineFlipUnitsEquiv q S
        (Units.mapEquiv (coordinateAlgebraBaseChangeEquiv (A := S) q).toMulEquiv a)))
  apply congrArg QuotientGroup.mk
  have hu : Units.mapEquiv (coordinateAlgebraBaseChangeEquiv (A := S) q').toMulEquiv
      (ScalarQuotientPresheaf.algebraUnitRestriction (coordinateRestriction q q' j w) a) =
    Units.map (affineUnitRestrictionPullback j w S).appTop.hom.toMonoidHom
      (Units.mapEquiv (coordinateAlgebraBaseChangeEquiv (A := S) q).toMulEquiv a) := by
    apply Units.ext
    exact coordinateAlgebraBaseChangeEquiv_restriction j w S (a : S ⊗[K] coordinateAlgebra q)
  rw [hu]
  exact affineFlipUnitsEquiv_restriction j w S _

/-- Relative Gamma--Spec comparison retains this same changing-modulus map. -/
theorem scalarQuotientAffineIso_restriction (S : CommAlgCat.{u} K)
    (x : ScalarQuotientPresheaf.ScalarQuotient
      (R := K) (A := coordinateAlgebra q)
      (S := ScalarQuotientSchemePresheaf.sectionsAlgebra K (spectrumTest S))) :
    ((scalarQuotientAffineIso q').hom.app (op (op S)))
        (ScalarQuotientPresheaf.algebraQuotientRestriction (coordinateRestriction q q' j w) x) =
      modulusUnitQuotientRestriction j w (spectrumTest S)
        (((scalarQuotientAffineIso q).hom.app (op (op S))) x) := by
  let g : ScalarQuotientSchemePresheaf.sectionsAlgebra K (spectrumTest S) →ₐ[K] S :=
    ((relativeSpectrumSectionsIso (CommRingCat.of K)).inv.app (op S)).unop.hom
  change ((algebraicModulusUnitAffineIso q').hom.app (op (op S)))
      (ScalarQuotientPresheaf.quotientMap g
        (ScalarQuotientPresheaf.algebraQuotientRestriction (coordinateRestriction q q' j w) x)) =
    modulusUnitQuotientRestriction j w (spectrumTest S)
      (((algebraicModulusUnitAffineIso q).hom.app (op (op S)))
        (ScalarQuotientPresheaf.quotientMap g x))
  exact (congrArg ((algebraicModulusUnitAffineIso q').hom.app (op (op S)))
    (ScalarQuotientPresheaf.algebraQuotientRestriction_naturality
      (coordinateRestriction q q' j w) g x).symm).trans
        (algebraicModulusUnitAffineIso_restriction j w S _)

/-- The full affine comparison square commutes as a morphism of group presheaves. -/
theorem scalarQuotientAffineIso_restriction_square :
    Functor.whiskerLeft (specOverFunctor (CommRingCat.of K)).op
        (ScalarQuotientSchemePresheaf.algebraRestrictionPresheaf
          (coordinateRestriction q q' j w)) ≫ (scalarQuotientAffineIso q').hom =
      (scalarQuotientAffineIso q).hom ≫
        Functor.whiskerLeft (specOverFunctor (CommRingCat.of K)).op
          (modulusUnitRestrictionPresheaf j w) := by
  apply NatTrans.ext
  funext S
  apply ConcreteCategory.hom_ext
  exact scalarQuotientAffineIso_restriction j w S.unop.unop

end AlgebraicGeometry.GeneralizedJacobian.ScalarFrames
