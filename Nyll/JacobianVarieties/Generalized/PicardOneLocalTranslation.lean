/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PicardOne
import Nyll.JacobianVarieties.Generalized.ModulusTwoPointDifference
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Actual local translations of intrinsic Picard-one

A point over any base change identifies the restriction of intrinsic Picard-one
with the restriction of Picard-zero. The construction works on the original
curve and its actual point classes, without assuming a ground-field point.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsClosedImmersion i]
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

/-- Any actual point on a test scheme detects its intrinsic degree-one classes. -/
theorem modulusPicardOne_iff_translatePoint
    {T : Over (Spec (CommRingCat.of R))}
    (P : T ⟶ Over.mk ((modulusComplement i).ι ≫ c))
    (x : RigidifiedLineBundle.Classes (modulusBaseChange c i T.hom)) :
    x ∈ (modulusPicardOneSubfunctor c i).obj (op T) ↔
      x / modulusAbelPointClass c i P ∈ modulusPicardZeroSubgroup c i T := by
  constructor
  · intro hx
    apply modulusPicardZero_of_fieldRestrictions c i T.hom
    intro k _ _ s
    let S := Over.mk (s ≫ T.hom)
    let f : S ⟶ T := Over.homMk s rfl
    let m : RigidifiedLineBundle.Classes (modulusBaseChange c i T.hom) →*
        RigidifiedLineBundle.Classes (modulusBaseChange c i S.hom) :=
      ((modulusPicardGroupPresheaf c i).map f.op).hom
    have hP : m (modulusAbelPointClass c i P) = modulusAbelPointClass c i (f ≫ P) :=
      modulusAbelPointClass_naturality c i f P
    change m (x / modulusAbelPointClass c i P) ∈ _
    rw [m.map_div, hP]
    obtain ⟨Q, hQ⟩ := hx k S.hom f
    have hdiff := modulusAbelPointClass_div_mem_zero c i Q (f ≫ P)
    have hmul := (modulusPicardZeroSubgroup c i S).mul_mem hQ hdiff
    rw [div_mul_div_cancel] at hmul
    exact hmul
  · intro hx k _ _ t f
    refine ⟨f ≫ P, ?_⟩
    let m : RigidifiedLineBundle.Classes (modulusBaseChange c i T.hom) →*
        RigidifiedLineBundle.Classes (modulusBaseChange c i t) :=
      ((modulusPicardGroupPresheaf c i).map f.op).hom
    have hP : m (modulusAbelPointClass c i P) = modulusAbelPointClass c i (f ≫ P) :=
      modulusAbelPointClass_naturality c i f P
    have hz := (modulusPicardZeroSubfunctor c i).map f.op hx
    change m (x / modulusAbelPointClass c i P) ∈ modulusPicardZeroSubgroup c i (Over.mk t) at hz
    rw [m.map_div, hP] at hz
    exact hz

variable {S' : Scheme.{u}} (s : S' ⟶ Spec (CommRingCat.of R))
  (P : Over.mk s ⟶ Over.mk ((modulusComplement i).ι ≫ c))

/-- The actual pullback of the local point to a test object of the new slice. -/
def modulusLocalPoint (T : Over S') :
    (Over.map s).obj T ⟶ Over.mk ((modulusComplement i).ι ≫ c) :=
  (Over.homMk T.hom rfl : (Over.map s).obj T ⟶ Over.mk s) ≫ P

omit [IsClosedImmersion i] [IsProper c] [SmoothOfRelativeDimension 1 c]
  [GeometricallyIntegral c] in
/-- The same local point family commutes with restriction. -/
theorem modulusLocalPoint_naturality {T T' : Over S'} (f : T' ⟶ T) :
    (Over.map s).map f ≫ modulusLocalPoint c i s P T = modulusLocalPoint c i s P T' := by
  apply Over.OverMorphism.ext
  change f.left ≫ (T.hom ≫ P.left) = T'.hom ≫ P.left
  rw [← Category.assoc, Over.w f]

/-- Tensoring with the local point identifies the two actual restricted class sets. -/
def modulusPicardOneLocalTranslationEquiv (T : Over S') :
    ((Over.map s).op ⋙ modulusPicardZeroPresheaf c i).obj (op T) ≃
      ((Over.map s).op ⋙ modulusPicardOnePresheaf c i).obj (op T) where
  toFun x := by
    let a : RigidifiedLineBundle.Classes (modulusBaseChange c i ((Over.map s).obj T).hom) :=
      x.val
    let b : RigidifiedLineBundle.Classes (modulusBaseChange c i ((Over.map s).obj T).hom) :=
      modulusAbelPointClass c i (modulusLocalPoint c i s P T)
    exact ⟨a * b,
      (modulusPicardOne_iff_translatePoint c i (modulusLocalPoint c i s P T) _).mpr
        (by
          change a * b / b ∈ modulusPicardZeroSubgroup c i ((Over.map s).obj T)
          rw [mul_div_cancel_right]
          exact x.property)⟩
  invFun x := by
    let a : RigidifiedLineBundle.Classes (modulusBaseChange c i ((Over.map s).obj T).hom) :=
      x.val
    let b : RigidifiedLineBundle.Classes (modulusBaseChange c i ((Over.map s).obj T).hom) :=
      modulusAbelPointClass c i (modulusLocalPoint c i s P T)
    exact ⟨a / b,
      (modulusPicardOne_iff_translatePoint c i (modulusLocalPoint c i s P T) a).mp x.property⟩
  left_inv x := by
    apply Subtype.ext
    let a : RigidifiedLineBundle.Classes (modulusBaseChange c i ((Over.map s).obj T).hom) :=
      x.val
    let b : RigidifiedLineBundle.Classes (modulusBaseChange c i ((Over.map s).obj T).hom) :=
      modulusAbelPointClass c i (modulusLocalPoint c i s P T)
    change a * b / b = a
    exact mul_div_cancel_right a b
  right_inv x := by
    apply Subtype.ext
    let a : RigidifiedLineBundle.Classes (modulusBaseChange c i ((Over.map s).obj T).hom) :=
      x.val
    let b : RigidifiedLineBundle.Classes (modulusBaseChange c i ((Over.map s).obj T).hom) :=
      modulusAbelPointClass c i (modulusLocalPoint c i s P T)
    change a / b * b = a
    exact div_mul_cancel a b

/-- The local point translation is a natural isomorphism of the actual restrictions. -/
def modulusPicardOneLocalTranslationIso :
    (Over.map s).op ⋙ modulusPicardZeroPresheaf c i ≅
      (Over.map s).op ⋙ modulusPicardOnePresheaf c i :=
  NatIso.ofComponents
    (fun T => Equiv.toIso (modulusPicardOneLocalTranslationEquiv c i s P T.unop))
    (fun {T T'} f => by
      apply TypeCat.homEquiv.injective
      funext x
      apply Subtype.ext
      let m : RigidifiedLineBundle.Classes
          (modulusBaseChange c i ((Over.map s).obj T.unop).hom) →*
            RigidifiedLineBundle.Classes
              (modulusBaseChange c i ((Over.map s).obj T'.unop).hom) :=
        ((modulusPicardGroupPresheaf c i).map ((Over.map s).map f.unop).op).hom
      let a : RigidifiedLineBundle.Classes
          (modulusBaseChange c i ((Over.map s).obj T.unop).hom) := x.val
      change m a * modulusAbelPointClass c i (modulusLocalPoint c i s P T'.unop) =
        m (a * modulusAbelPointClass c i (modulusLocalPoint c i s P T.unop))
      rw [m.map_mul]
      have h := modulusAbelPointClass_naturality c i ((Over.map s).map f.unop)
        (modulusLocalPoint c i s P T.unop)
      rw [modulusLocalPoint_naturality] at h
      exact congrArg (m a * ·) h.symm)

/-- Restricting actual fppf sheaves retains the local tensor translation. -/
def modulusPicardOneLocalTranslationSheafIso :
    (Over.map s).op ⋙ (modulusPicardZeroSheaf c i).obj ≅
      (Over.map s).op ⋙ (modulusPicardOneSheaf c i).obj :=
  ((sheafToPresheaf (Scheme.fppfTopology.over S') (Type (u + 1))).mapIso
    (((Over.map s).pushforwardContinuousSheafificationCompatibility (Type (u + 1))
      (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))).app
        (modulusPicardZeroPresheaf c i))).symm ≪≫
  ((sheafToPresheaf (Scheme.fppfTopology.over S') (Type (u + 1))).mapIso
    ((presheafToSheaf (Scheme.fppfTopology.over S') (Type (u + 1))).mapIso
      (modulusPicardOneLocalTranslationIso c i s P))) ≪≫
  ((sheafToPresheaf (Scheme.fppfTopology.over S') (Type (u + 1))).mapIso
    (((Over.map s).pushforwardContinuousSheafificationCompatibility (Type (u + 1))
      (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))).app
        (modulusPicardOnePresheaf c i)))

end AlgebraicGeometry.GeneralizedJacobian
