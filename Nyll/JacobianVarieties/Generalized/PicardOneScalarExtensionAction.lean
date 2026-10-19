/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardOneDivisorScalarExtension
import Nyll.JacobianVarieties.Generalized.DivisorScalarExtensionSheaf
import Nyll.JacobianVarieties.Generalized.PicardOneIntrinsicAction

/-! # Actual tensor action and scalar extension of the full relative divisor -/

noncomputable section

universe u v w

open CategoryTheory Opposite MonoidalCategory
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

private theorem actionComparisonOnGenerators
    {A₀ P₀ A P B₀ Q₀ B Q : Type*}
    (a₀ : A₀ → P₀ → P₀) (a : A → P → P)
    (b₀ : B₀ → Q₀ → Q₀) (b : B → Q → Q)
    (eA : A₀ → A) (eP : P₀ → P) (eB : B₀ → B) (eQ : Q₀ → Q)
    (rA₀ : A₀ → B₀) (rP₀ : P₀ → Q₀) (rA : A → B) (rP : P → Q)
    (ha : ∀ g x, a (eA g) (eP x) = eP (a₀ g x))
    (hb : ∀ g x, b (eB g) (eQ x) = eQ (b₀ g x))
    (hraw : ∀ g x, rP₀ (a₀ g x) = b₀ (rA₀ g) (rP₀ x))
    (hA : ∀ g, rA (eA g) = eB (rA₀ g))
    (hP : ∀ x, rP (eP x) = eQ (rP₀ x)) (g : A₀) (x : P₀) :
    rP (a (eA g) (eP x)) = b (rA (eA g)) (rP (eP x)) := by
  rw [ha, hP, hraw, hA, hP, hb]

private theorem locallySurjectivePairExt {B : Type v} [Category.{w} B]
    (J : GrothendieckTopology B) {A₀ A : Bᵒᵖ ⥤ CommGrpCat.{u}}
    {P₀ P : Bᵒᵖ ⥤ Type u} (ηA : A₀ ⟶ A) (ηP : P₀ ⟶ P)
    [Presheaf.IsLocallySurjective J ηA] [Presheaf.IsLocallySurjective J ηP]
    (Q : Sheaf J (Type u))
    (f g : (A ⋙ forget CommGrpCat.{u}) ⊗ P ⟶ Q.obj)
    (h : ∀ (T : B) (a : A₀.obj (op T)) (p : P₀.obj (op T)),
      f.app (op T) ((ηA.app (op T)).hom a, ηP.app (op T) p) =
        g.app (op T) ((ηA.app (op T)).hom a, ηP.app (op T) p)) : f = g := by
  apply NatTrans.ext
  funext T
  apply TypeCat.homEquiv.injective
  funext z
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 Q.2).isSeparated _
    (J.intersection_covering (Presheaf.imageSieve_mem J ηA z.1)
      (Presheaf.imageSieve_mem J ηP z.2))).ext
  rintro Y q ⟨⟨a, ha⟩, ⟨p, hp⟩⟩
  have hz : ((A ⋙ forget CommGrpCat.{u}) ⊗ P).map q.op z =
      ((ηA.app (op Y)).hom a, ηP.app (op Y) p) := Prod.ext ha.symm hp.symm
  exact (f.naturality_apply q.op z).symm.trans
    ((congrArg (f.app (op Y)) hz).trans
      ((h Y a p).trans ((congrArg (g.app (op Y)) hz).symm.trans
        (g.naturality_apply q.op z))))

private theorem actualActionComparison
    {R S : Type u} [CommRing R] [CommRing S] {C D E F : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsClosedImmersion i]
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (c' : E ⟶ Spec (CommRingCat.of S)) (i' : F ⟶ E) [IsClosedImmersion i']
    [IsProper c'] [SmoothOfRelativeDimension 1 c'] [GeometricallyIntegral c']
    (H : Over (Spec (CommRingCat.of S)) ⥤ Over (Spec (CommRingCat.of R)))
    (rG : modulusPicardZeroGroupPresheaf c' i' ⟶ H.op ⋙ modulusPicardZeroGroupPresheaf c i)
    (rP : modulusPicardOnePresheaf c' i' ⟶ H.op ⋙ modulusPicardOnePresheaf c i)
    (sG : (modulusPicardZeroGroupSheaf c' i').obj ⟶
      H.op ⋙ (modulusPicardZeroGroupSheaf c i).obj)
    (sP : (modulusPicardOneSheaf c' i').obj ⟶ H.op ⋙ (modulusPicardOneSheaf c i).obj)
    (hG : toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of S)))
      (modulusPicardZeroGroupPresheaf c' i') ≫ sG = rG ≫ Functor.whiskerLeft H.op
        (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
          (modulusPicardZeroGroupPresheaf c i)))
    (hP : toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of S)))
      (modulusPicardOnePresheaf c' i') ≫ sP = rP ≫ Functor.whiskerLeft H.op
        (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
          (modulusPicardOnePresheaf c i)))
    (ha : ∀ (T : Over (Spec (CommRingCat.of S)))
      (g : (modulusPicardZeroGroupPresheaf c' i').obj (op T))
      (x : (modulusPicardOnePresheaf c' i').obj (op T)),
      rP.app (op T) (modulusPicardOneAction c' i' T g x) =
        modulusPicardOneAction c i (H.obj T) ((rG.app (op T)).hom g) (rP.app (op T) x))
    (T : Over (Spec (CommRingCat.of S)))
    (g : (modulusPicardZeroGroupPresheaf c' i').obj (op T))
    (x : (modulusPicardOnePresheaf c' i').obj (op T)) :
    let etaG := toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of S)))
      (modulusPicardZeroGroupPresheaf c' i')
    let etaP := toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of S)))
      (modulusPicardOnePresheaf c' i')
    sP.app (op T) (modulusPicardOneIntrinsicAction c' i' T
      ((etaG.app (op T)).hom g) (etaP.app (op T) x)) =
        modulusPicardOneIntrinsicAction c i (H.obj T)
          ((sG.app (op T)).hom ((etaG.app (op T)).hom g))
          (sP.app (op T) (etaP.app (op T) x)) := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of R))
  let J' := Scheme.fppfTopology.over (Spec (CommRingCat.of S))
  exact actionComparisonOnGenerators
    (modulusPicardOneAction c' i' T) (modulusPicardOneIntrinsicAction c' i' T)
    (modulusPicardOneAction c i (H.obj T)) (modulusPicardOneIntrinsicAction c i (H.obj T))
    ((toSheafify J' (modulusPicardZeroGroupPresheaf c' i')).app (op T)).hom
    ((toSheafify J' (modulusPicardOnePresheaf c' i')).app (op T))
    ((toSheafify J (modulusPicardZeroGroupPresheaf c i)).app (op (H.obj T))).hom
    ((toSheafify J (modulusPicardOnePresheaf c i)).app (op (H.obj T)))
    (rG.app (op T)).hom (rP.app (op T)) (sG.app (op T)).hom (sP.app (op T))
    (modulusPicardOneIntrinsicAction_actual c' i' T)
    (modulusPicardOneIntrinsicAction_actual c i (H.obj T)) (ha T)
    (fun a => ConcreteCategory.congr_hom (NatTrans.congr_app hG (op T)) a)
    (fun p => ConcreteCategory.congr_hom (NatTrans.congr_app hP (op T)) p) g x

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)}
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (L : Type u) [Field L] [Algebra K L]

/-- The zero-presheaf comparison for the actual scalar-extended divisor. -/
def modulusPicardZeroGroup_divisorScalarExtensionIso :
    modulusPicardZeroGroupPresheaf (baseChange K c L)
        (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))) ≅
      (Over.map (specMap K L)).op ⋙ modulusPicardZeroGroupPresheaf c (modulusCurveMap D) :=
  (modulusPicardZeroGroupModulusIso (baseChange K c L)
    (divisorScalarExtensionModulusIso D L)
    (divisorScalarExtensionModulusIso_square D L)).symm ≪≫
      modulusPicardZeroGroupScalarExtensionIso c (modulusCurveMap D) L

omit [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] in
/-- Its fppf sheaf comparison retains the actual class map on every raw section. -/
@[reassoc] theorem toSheafify_modulusPicardZeroGroup_divisorScalarExtension :
    toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of L)))
        (modulusPicardZeroGroupPresheaf (baseChange K c L)
          (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))) ≫
      (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L).hom.hom =
        (modulusPicardZeroGroup_divisorScalarExtensionIso D L).hom ≫
          Functor.whiskerLeft (Over.map (specMap K L)).op
            (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
              (modulusPicardZeroGroupPresheaf c (modulusCurveMap D))) := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of L))
  let a := modulusPicardZeroGroupModulusIso (baseChange K c L)
    (divisorScalarExtensionModulusIso D L) (divisorScalarExtensionModulusIso_square D L)
  let η := toSheafify J (modulusPicardZeroGroupPresheaf (baseChange K c L)
    (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))))
  let η' := toSheafify J (modulusPicardZeroGroupPresheaf (baseChange K c L)
    (modulusBaseChange c (modulusCurveMap D) (specMap K L)))
  let e := (modulusPicardZeroGroupSheafScalarExtensionIso c (modulusCurveMap D) L).hom.hom
  let q := (modulusPicardZeroGroupScalarExtensionIso c (modulusCurveMap D) L).hom
  let η₀ := Functor.whiskerLeft (Over.map (specMap K L)).op
    (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (modulusPicardZeroGroupPresheaf c (modulusCurveMap D)))
  exact (Category.assoc η (sheafifyMap J a.inv) e).symm.trans
    ((congrArg (fun z => z ≫ e) (toSheafify_naturality J a.inv).symm).trans
      ((Category.assoc a.inv η' e).trans
        ((congrArg (fun z => a.inv ≫ z)
          (toSheafify_modulusPicardZeroGroupScalarExtension c (modulusCurveMap D) L)).trans
            (Category.assoc a.inv q η₀).symm)))

/-- Scalar extension of the actual divisor preserves the actual raw tensor action. -/
theorem modulusPicardOne_divisorScalarExtension_action
    (T : Over (Spec (CommRingCat.of L)))
    (g : (modulusPicardZeroGroupPresheaf (baseChange K c L)
      (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).obj (op T))
    (x : (modulusPicardOnePresheaf (baseChange K c L)
      (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).obj (op T)) :
    (modulusPicardOne_divisorScalarExtensionIso D L).hom.app (op T)
        (modulusPicardOneAction (baseChange K c L)
          (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))) T g x) =
      modulusPicardOneAction c (modulusCurveMap D) ((Over.map (specMap K L)).obj T)
        (((modulusPicardZeroGroup_divisorScalarExtensionIso D L).hom.app (op T)).hom g)
        ((modulusPicardOne_divisorScalarExtensionIso D L).hom.app (op T) x) := by
  apply Subtype.ext
  let a := (modulusIsoClassesEquiv (baseChange K c L)
    (divisorScalarExtensionModulusIso D L)
    (divisorScalarExtensionModulusIso_square D L) T.hom).symm
  let b := scalarExtensionClassesEquiv c (modulusCurveMap D) L T.hom
  exact (a.trans b).map_mul g.val x.val

/-- The actual scalar-extension comparison preserves the action on every raw section. -/
theorem modulusPicardOneSheaf_divisorScalarExtension_action_actual
    (T : Over (Spec (CommRingCat.of L)))
    (g : (modulusPicardZeroGroupPresheaf (baseChange K c L)
      (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).obj (op T))
    (x : (modulusPicardOnePresheaf (baseChange K c L)
      (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).obj (op T)) :
    let ηG := toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of L)))
      (modulusPicardZeroGroupPresheaf (baseChange K c L)
        (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))))
    let ηP := toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of L)))
      (modulusPicardOnePresheaf (baseChange K c L)
        (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))))
    (modulusPicardOneSheaf_divisorScalarExtensionIso D L).hom.hom.app (op T)
        (modulusPicardOneIntrinsicAction (baseChange K c L)
          (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))) T
          ((ηG.app (op T)).hom g) (ηP.app (op T) x)) =
      modulusPicardOneIntrinsicAction c (modulusCurveMap D) ((Over.map (specMap K L)).obj T)
        (((modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L).hom.hom.app (op T)).hom
          ((ηG.app (op T)).hom g))
        ((modulusPicardOneSheaf_divisorScalarExtensionIso D L).hom.hom.app (op T)
          (ηP.app (op T) x)) := by
  exact actualActionComparison c (modulusCurveMap D) (baseChange K c L)
    (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))) (Over.map (specMap K L))
    (modulusPicardZeroGroup_divisorScalarExtensionIso D L).hom
    (modulusPicardOne_divisorScalarExtensionIso D L).hom
    (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L).hom.hom
    (modulusPicardOneSheaf_divisorScalarExtensionIso D L).hom.hom
    (toSheafify_modulusPicardZeroGroup_divisorScalarExtension D L)
    (toSheafify_modulusPicardOne_divisorScalarExtension D L)
    (modulusPicardOne_divisorScalarExtension_action D L) T g x


/-- The intrinsic sheaf action commutes with arbitrary extension of the ground field. -/
theorem modulusPicardOneSheaf_divisorScalarExtension_action
    (T : Over (Spec (CommRingCat.of L)))
    (g : (modulusPicardZeroGroupSheaf (baseChange K c L)
      (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).obj.obj (op T))
    (x : (modulusPicardOneSheaf (baseChange K c L)
      (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).obj.obj (op T)) :
    (modulusPicardOneSheaf_divisorScalarExtensionIso D L).hom.hom.app (op T)
        (modulusPicardOneIntrinsicAction (baseChange K c L)
          (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))) T g x) =
      modulusPicardOneIntrinsicAction c (modulusCurveMap D) ((Over.map (specMap K L)).obj T)
        (((modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L).hom.hom.app (op T)).hom g)
        ((modulusPicardOneSheaf_divisorScalarExtensionIso D L).hom.hom.app (op T) x) := by
  let c' := baseChange K c L
  let i' := modulusCurveMap (D.changeBaseOfIdentity (specMap K L))
  let J' := Scheme.fppfTopology.over (Spec (CommRingCat.of L))
  let F := Over.map (specMap K L)
  let ηG := toSheafify J' (modulusPicardZeroGroupPresheaf c' i')
  let ηP := toSheafify J' (modulusPicardOnePresheaf c' i')
  let rG := (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L).hom
  let rP := (modulusPicardOneSheaf_divisorScalarExtensionIso D L).hom
  let Q := (Scheme.fppfTopology.overMapPullback (Type (u + 1)) (specMap K L)).obj
    (modulusPicardOneSheaf c (modulusCurveMap D))
  let S := ((modulusPicardZeroGroupSheaf c' i').obj ⋙ forget CommGrpCat.{u + 1}) ⊗
    (modulusPicardOneSheaf c' i').obj
  let a : S ⟶ Q.obj := modulusPicardOneIntrinsicActionMap c' i' ≫ rP.hom
  let b : S ⟶ Q.obj :=
    (Functor.whiskerRight rG.hom (forget CommGrpCat.{u + 1}) ⊗ₘ rP.hom) ≫
      Functor.whiskerLeft F.op (modulusPicardOneIntrinsicActionMap c (modulusCurveMap D))
  have h : a = b := locallySurjectivePairExt J' ηG ηP Q a b (by
    intro Y g₀ x₀
    exact modulusPicardOneSheaf_divisorScalarExtension_action_actual D L Y g₀ x₀)
  let z : S.obj (op T) := (g, x)
  exact congrArg (fun q : S ⟶ Q.obj => q.app (op T) z) h

end AlgebraicGeometry.GeneralizedJacobian
