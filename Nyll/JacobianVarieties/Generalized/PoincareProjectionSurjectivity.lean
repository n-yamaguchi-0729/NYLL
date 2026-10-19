/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PoincareProjectionGeometry
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Fppf local surjectivity of the modulus-forgetting group morphism

Pulling the constructed smooth surjective projection back along the actual
ordinary classifying point gives an fppf cover and a modulus lift on that
cover. Thus the group sheaf projection is an epimorphism without any claim
of surjectivity on rational points.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
  {J : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J) (hd : 0 < d)

include h hd

/-- Every ordinary zero group section has an actual modulus lift on an fppf cover. -/
theorem forgetModulusZeroGroupSheaf_isLocallySurjective :
    Sheaf.IsLocallySurjective (forgetModulusZeroGroupSheaf c (modulusCurveMap D)) := by
  let W := (poincareModulusCommGroupScheme D h hd).X
  let Y := (ordinaryZeroCommGroupScheme h).X
  let m : W ⟶ Y := (poincareModulusGroupProjection D h hd).hom.hom.hom
  let eF : ((modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj ⋙
      forget CommGrpCat.{u + 1}).RepresentableBy W :=
    poincareModulusPicardZeroGroupRepresentable D h hd
  let eG : ((ordinaryRelativePicardZeroGroupSheaf c).obj ⋙
      forget CommGrpCat.{u + 1}).RepresentableBy Y := ordinaryZeroGroupSheafRepresentable h
  have : SmoothOfRelativeDimension (d - 1) m.left :=
    poincareModulusGroupProjection_smoothOfRelativeDimension D h hd
  have : Smooth m.left := SmoothOfRelativeDimension.smooth (d - 1) m.left
  have : Surjective m.left := poincareModulusGroupProjection_surjective D h hd
  constructor
  intro T x
  let g : T ⟶ Y := eG.homEquiv.symm x
  let U : Over (Spec (CommRingCat.of K)) :=
    Over.mk (pullback.snd m.left g.left ≫ T.hom)
  let p : U ⟶ T := Over.homMk (pullback.snd m.left g.left) rfl
  let f : U ⟶ W := Over.homMk (pullback.fst m.left g.left) (by
    rw [← Over.w m, ← Category.assoc, pullback.condition, Category.assoc, Over.w g]
    rfl)
  have hcover : Sieve.ofArrows (fun _ : PUnit.{1} => U) (fun _ => p) ∈
      (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    change Sieve.generate (Presieve.ofArrows (fun _ : PUnit.{1} => pullback m.left g.left)
      (fun _ => pullback.snd m.left g.left)) ∈ Scheme.fppfTopology T.left
    rw [Presieve.ofArrows_pUnit]
    exact Precoverage.generate_mem_toGrothendieck
      (Scheme.Hom.singleton_mem_fppfPrecoverage (pullback.snd m.left g.left))
  apply (Scheme.fppfTopology.over (Spec (CommRingCat.of K))).superset_covering ?_ hcover
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro j
  refine ⟨eF.homEquiv f, ?_⟩
  have hm := poincareModulusGroupProjection_homEquiv D h hd f
  change eG.homEquiv (f ≫ m) =
    ((forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom.app (op U)).hom
      (eF.homEquiv f) at hm
  have hp : f ≫ m = p ≫ g := by
    apply Over.OverMorphism.ext
    exact pullback.condition
  change ((forgetModulusZeroGroupSheaf c (modulusCurveMap D)).hom.app (op U)).hom
      (eF.homEquiv f) = ((ordinaryRelativePicardZeroGroupSheaf c).obj.map p.op).hom x
  rw [← hm, hp, eG.homEquiv_comp]
  change ((ordinaryRelativePicardZeroGroupSheaf c).obj.map p.op).hom
    (eG.homEquiv (eG.homEquiv.symm x)) = _
  rw [Equiv.apply_symm_apply]

/-- The forgetful morphism is an epimorphism of actual fppf commutative group sheaves. -/
theorem forgetModulusZeroGroupSheaf_epi :
    Epi (forgetModulusZeroGroupSheaf c (modulusCurveMap D)) := by
  have : Sheaf.IsLocallySurjective (forgetModulusZeroGroupSheaf c (modulusCurveMap D)) :=
    forgetModulusZeroGroupSheaf_isLocallySurjective D h hd
  infer_instance

end AlgebraicGeometry.GeneralizedJacobian
