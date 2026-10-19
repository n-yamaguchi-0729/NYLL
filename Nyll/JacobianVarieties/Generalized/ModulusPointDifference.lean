/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedTensor
import Nyll.AlgebraicCurves.Geometry.Picard.Representability.AbelJacobiPicardRepresentability

/-!
# Algebraic triviality of actual rigidified point differences

The line-bundle comparison in the ordinary Abel construction supplies algebraic
triviality on a field-valued fibre. Tensor cancellation then applies this result
to actual modulus-rigidified point line bundles, retaining their chosen frames.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory NeronModelInfra
open AlgebraicGeometry.RelPicard
open JacobianVarieties.Picard.Proofs
open Exists_abelJacobi_of_representsRelSubPic.AlgebraicGeometry.RelPicard.AbelJacobiGlue

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

/-- Point-minus-basepoint is algebraically trivial on the actual scalar-extended curve. -/
theorem pointDifference_algEquivZero
    (k : Type u) [Field k] (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t c) :
    IsAlgEquivZero (pullback.snd c t)
      ((RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
          ((Category.assoc _ _ _).trans
            ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule) := by
  rcases x with ⟨s, hs⟩
  subst t
  obtain ⟨e⟩ := nonempty_pullback_fst_pointBundle_iso_pointSubBasepointModule R c ε k s
  exact IsAlgEquivZero.of_iso_pointSubBasepoint
    ⟨graphOver c s rfl, graphOver_snd c s rfl⟩
    ⟨rigSection c (s ≫ c) ε, rigSection_snd c (s ≫ c) ε⟩ e

/-- Any actual rigidifications on those two point line bundles give the same zero condition. -/
theorem rigidifiedPointDifference_algEquivZero
    (k : Type u) [Field k] (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t c) {D : Scheme.{u}} (i : D ⟶ pullback c t)
    (M N : RigidifiedLineBundle i)
    (eM : M.L ≅ (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle)
    (eN : N.L ≅ (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
      ((Category.assoc _ _ _).trans
        ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).lineBundle) :
    IsAlgEquivZero (pullback.snd c t) (M.tensor N.dual).L := by
  let E := RelEffCartierDiv.ofPoint c (t ≫ ε.1)
    ((Category.assoc _ _ _).trans
      ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))
  have hE : E.I.IsInvertible := RelEffCartierDiv.isInvertible_I E
  have hInv : Nonempty (E.lineBundle ⊗ E.idealModule ≅ 𝟙_ (pullback c t).Modules) :=
    Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso hE
  obtain ⟨eDual⟩ := MonoidalCategory.nonempty_iso_of_tensor_iso_tensorUnit
    eN ⟨N.evaluation⟩ hInv
  exact (pointDifference_algEquivZero c ε k t x).of_iso (eM ⊗ᵢ eDual).symm

end AlgebraicGeometry.GeneralizedJacobian
