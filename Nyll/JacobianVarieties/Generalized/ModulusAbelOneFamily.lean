/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardOne

/-! # The intrinsic modulus Picard-one Abel family without a basepoint -/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsClosedImmersion i]
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

/-- The original canonically rigidified point class has the intrinsic degree-one condition. -/
def modulusAbelOnePresheafMap :
    uliftYoneda.{u + 1}.obj
        (Over.mk ((modulusComplement i).ι ≫ c)) ⟶
      modulusPicardOnePresheaf c i where
  app T := TypeCat.ofHom (fun (x : ULift.{u + 1}
      (T.unop ⟶ Over.mk ((modulusComplement i).ι ≫ c))) =>
    ⟨modulusAbelPointClass c i (T := T.unop) x.down, by
      intro k _ _ t s
      refine ⟨s ≫ x.down, ?_⟩
      let m : RigidifiedLineBundle.Classes (modulusBaseChange c i T.unop.hom) →*
          RigidifiedLineBundle.Classes (modulusBaseChange c i t) :=
        ((modulusPicardGroupPresheaf c i).map s.op).hom
      let b : RigidifiedLineBundle.Classes (modulusBaseChange c i t) :=
        modulusAbelPointClass c i (T := Over.mk t) (s ≫ x.down)
      have h : m (modulusAbelPointClass c i (T := T.unop) x.down) = b :=
        modulusAbelPointClass_naturality c i s x.down
      change m (modulusAbelPointClass c i (T := T.unop) x.down) / b ∈ _
      rw [h, div_self']
      exact (modulusPicardZeroSubgroup c i (Over.mk t)).one_mem⟩)
  naturality {T T'} f := by
    apply TypeCat.homEquiv.injective
    funext x
    apply Subtype.ext
    exact (modulusAbelPointClass_naturality c i f.unop x.down).symm

omit [GeometricallyIntegral c] in
/-- Forgetting the degree condition recovers the original diagonal-family Abel map. -/
theorem modulusAbelOnePresheafMap_forget :
    modulusAbelOnePresheafMap c i ≫ (modulusPicardOneSubfunctor c i).ι =
      modulusAbelPresheafMap c i := by
  ext T x
  rfl

/-- The fppf Picard-one class of the original Abel family. -/
def modulusAbelOneSheafMap :
    uliftYoneda.{u + 1}.obj
        (Over.mk ((modulusComplement i).ι ≫ c)) ⟶
      (modulusPicardOneSheaf c i).obj :=
  modulusAbelOnePresheafMap c i ≫
    toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (modulusPicardOnePresheaf c i)

end AlgebraicGeometry.GeneralizedJacobian
