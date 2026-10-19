/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.ModulusTransitionScalarExtensionSheaf
import Nyll.JacobianVarieties.Generalized.PicardOneScalarExtensionScheme
import Nyll.JacobianVarieties.Generalized.PicardOneRestrictionScheme

/-! # The actual Picard-one transition square under extension of the ground field -/

noncomputable section

universe u v w

open CategoryTheory Opposite
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

private theorem representableSquare {B : Type v} [Category.{w} B]
    {F G H I : Bᵒᵖ ⥤ Type u} {X Y Z W : B}
    (eF : F.RepresentableBy X) (eG : G.RepresentableBy Y)
    (eH : H.RepresentableBy Z) (eI : I.RepresentableBy W)
    (a : F ⟶ H) (b : G ⟶ I) (r : F ⟶ G) (s : H ⟶ I)
    (x : X ⟶ Z) (y : Y ⟶ W) (t : X ⟶ Y) (q : Z ⟶ W)
    (hx : ∀ {T} (f : T ⟶ X), eH.homEquiv (f ≫ x) = a.app (op T) (eF.homEquiv f))
    (hy : ∀ {T} (f : T ⟶ Y), eI.homEquiv (f ≫ y) = b.app (op T) (eG.homEquiv f))
    (ht : ∀ {T} (f : T ⟶ X), eG.homEquiv (f ≫ t) = r.app (op T) (eF.homEquiv f))
    (hq : ∀ {T} (f : T ⟶ Z), eI.homEquiv (f ≫ q) = s.app (op T) (eH.homEquiv f))
    (hs : a ≫ s = r ≫ b) : x ≫ q = t ≫ y := by
  have hx₀ : eH.homEquiv x = a.app (op X) (eF.homEquiv (𝟙 X)) := by
    simpa only [Category.id_comp] using hx (𝟙 X)
  have ht₀ : eG.homEquiv t = r.app (op X) (eF.homEquiv (𝟙 X)) := by
    simpa only [Category.id_comp] using ht (𝟙 X)
  have hh : s.app (op X) (a.app (op X) (eF.homEquiv (𝟙 X))) =
      b.app (op X) (r.app (op X) (eF.homEquiv (𝟙 X))) :=
    congrArg (fun m : F ⟶ I => m.app (op X) (eF.homEquiv (𝟙 X))) hs
  apply eI.homEquiv.injective
  exact (hq x).trans ((congrArg (s.app (op X)) hx₀).trans
    (hh.trans ((congrArg (b.app (op X)) ht₀).symm.trans (hy t).symm)))

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d d' : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (D' : RelEffCartierDiv c d' (𝟙 (Spec (CommRingCat.of K))))
  (j : D'.I.subscheme ⟶ D.I.subscheme)
  (w : modulusCurveMap D' = j ≫ modulusCurveMap D)
  (L : Type u) [Field L] [Algebra K L]

/-- The actual pullback of the transition classifies the original restricted rigidification. -/
theorem picardOneTransitionAlong_pullback_classifies
    {T : Over (Spec (CommRingCat.of L))}
    (x : T ⟶ (Over.pullback (specMap K L)).obj (picardOne c D)) :
    (picardOneScalarExtensionRepresentable c D' L).homEquiv
        (x ≫ (Over.pullback (specMap K L)).map (picardOneTransitionAlong c D D' j w)) =
      (modulusRestrictionOneSheaf c j w).hom.app (op ((Over.map (specMap K L)).obj T))
        ((picardOneScalarExtensionRepresentable c D L).homEquiv x) := by
  let adj := Over.mapPullbackAdj (specMap K L)
  change (picardOneRepresentable c D').homEquiv
    ((adj.homEquiv T (picardOne c D')).symm
      (x ≫ (Over.pullback (specMap K L)).map (picardOneTransitionAlong c D D' j w))) = _
  exact (congrArg (picardOneRepresentable c D').homEquiv
    (adj.homEquiv_naturality_right_symm x (picardOneTransitionAlong c D D' j w))).trans
      (picardOneTransitionAlong_classifies c D D' j w ((adj.homEquiv T _).symm x))

/-- The same scalar-extension isomorphisms used for the Abel map and torsor action
commute with the actual scheme transition. -/
theorem picardOneTransitionAlong_scalarExtension_square :
    (picardOneScalarExtensionIso c D L).hom ≫
        picardOneTransitionAlong (baseChange K c L)
          (D.changeBaseOfIdentity (specMap K L)) (D'.changeBaseOfIdentity (specMap K L))
          (divisorRestrictionScalarMap D D' j w L) (divisorRestrictionScalarMap_square D D' j w L) =
      (Over.pullback (specMap K L)).map (picardOneTransitionAlong c D D' j w) ≫
        (picardOneScalarExtensionIso c D' L).hom := by
  exact representableSquare
    (picardOneScalarExtensionRepresentable c D L) (picardOneScalarExtensionRepresentable c D' L)
    (picardOneRepresentable (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)))
    (picardOneRepresentable (baseChange K c L) (D'.changeBaseOfIdentity (specMap K L)))
    (modulusPicardOneSheaf_divisorScalarExtensionIso D L).inv.hom
    (modulusPicardOneSheaf_divisorScalarExtensionIso D' L).inv.hom
    (Functor.whiskerLeft (Over.map (specMap K L)).op (modulusRestrictionOneSheaf c j w).hom)
    (modulusRestrictionOneSheaf (baseChange K c L)
      (divisorRestrictionScalarMap D D' j w L)
      (divisorRestrictionScalarMap_square D D' j w L)).hom
    (picardOneScalarExtensionIso c D L).hom (picardOneScalarExtensionIso c D' L).hom
    ((Over.pullback (specMap K L)).map (picardOneTransitionAlong c D D' j w))
    (picardOneTransitionAlong (baseChange K c L)
      (D.changeBaseOfIdentity (specMap K L)) (D'.changeBaseOfIdentity (specMap K L))
      (divisorRestrictionScalarMap D D' j w L) (divisorRestrictionScalarMap_square D D' j w L))
    (picardOneScalarExtensionIso_homEquiv c D L)
    (picardOneScalarExtensionIso_homEquiv c D' L)
    (picardOneTransitionAlong_pullback_classifies c D D' j w L)
    (picardOneTransitionAlong_classifies (baseChange K c L)
      (D.changeBaseOfIdentity (specMap K L)) (D'.changeBaseOfIdentity (specMap K L))
      (divisorRestrictionScalarMap D D' j w L) (divisorRestrictionScalarMap_square D D' j w L))
    (congrArg (fun m :
      (Scheme.fppfTopology.overMapPullback (Type (u + 1)) (specMap K L)).obj
        (modulusPicardOneSheaf c (modulusCurveMap D)) ⟶
      modulusPicardOneSheaf (baseChange K c L)
        (modulusCurveMap (D'.changeBaseOfIdentity (specMap K L))) => m.hom)
      (modulusRestrictionOneSheaf_divisorScalarExtension_inv D D' j w L))

end AlgebraicGeometry.GeneralizedJacobian
