/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardOneTorsor
import Nyll.JacobianVarieties.Generalized.PicardZeroGroupSheaf

/-! # The Picard-one sheaf torsor supplied by actual point translation -/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsClosedImmersion i]
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (ε : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶
    Over.mk ((modulusComplement i).ι ≫ c))

/-- Actual point translation identifies the tensor group sheaf with intrinsic Picard-one. -/
def modulusPicardOneGroupTranslationIso :
    (modulusPicardZeroGroupSheaf c i).obj ⋙ forget CommGrpCat.{u + 1} ≅
      (modulusPicardOneSheaf c i).obj :=
  modulusPicardZeroGroupSheafForgetIso c i ≪≫
    (sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (Type (u + 1))).mapIso (modulusPicardOneTranslationSheafIso c i ε)

/-- Point translation on every test, using the actual sheafification comparison. -/
def modulusPicardOneSheafTranslationEquiv (T : Over (Spec (CommRingCat.of R))) :
    (modulusPicardZeroGroupSheaf c i).obj.obj (op T) ≃
      (modulusPicardOneSheaf c i).obj.obj (op T) :=
  ((modulusPicardOneGroupTranslationIso c i ε).app (op T)).toEquiv

/-- The sheaf translation commutes with every test-scheme pullback. -/
theorem modulusPicardOneSheafTranslationEquiv_naturality
    {T T' : Over (Spec (CommRingCat.of R))} (f : T' ⟶ T)
    (g : (modulusPicardZeroGroupSheaf c i).obj.obj (op T)) :
    (modulusPicardOneSheaf c i).obj.map f.op
        (modulusPicardOneSheafTranslationEquiv c i ε T g) =
      modulusPicardOneSheafTranslationEquiv c i ε T'
        ((modulusPicardZeroGroupSheaf c i).obj.map f.op g) :=
  (ConcreteCategory.congr_hom
    ((modulusPicardOneGroupTranslationIso c i ε).hom.naturality f.op) g).symm

/-- Its inverse coordinate map is natural as well. -/
theorem modulusPicardOneSheafTranslationEquiv_symm_naturality
    {T T' : Over (Spec (CommRingCat.of R))} (f : T' ⟶ T)
    (x : (modulusPicardOneSheaf c i).obj.obj (op T)) :
    (modulusPicardZeroGroupSheaf c i).obj.map f.op
        ((modulusPicardOneSheafTranslationEquiv c i ε T).symm x) =
      (modulusPicardOneSheafTranslationEquiv c i ε T').symm
        ((modulusPicardOneSheaf c i).obj.map f.op x) :=
  (ConcreteCategory.congr_hom
    ((modulusPicardOneGroupTranslationIso c i ε).inv.naturality f.op) x).symm

/-- Tensor action on the Picard-one sheaf in the trivialization given by the actual point. -/
def modulusPicardOneSheafAction (T : Over (Spec (CommRingCat.of R)))
    (g : (modulusPicardZeroGroupSheaf c i).obj.obj (op T))
    (x : (modulusPicardOneSheaf c i).obj.obj (op T)) :
    (modulusPicardOneSheaf c i).obj.obj (op T) :=
  modulusPicardOneSheafTranslationEquiv c i ε T
    (g * (modulusPicardOneSheafTranslationEquiv c i ε T).symm x)

/-- Difference of two sheaf classes is a class of the actual tensor group sheaf. -/
def modulusPicardOneSheafDifference (T : Over (Spec (CommRingCat.of R)))
    (x y : (modulusPicardOneSheaf c i).obj.obj (op T)) :
    (modulusPicardZeroGroupSheaf c i).obj.obj (op T) :=
  (modulusPicardOneSheafTranslationEquiv c i ε T).symm x /
    (modulusPicardOneSheafTranslationEquiv c i ε T).symm y

/-- The sheaf tensor action commutes with every pullback of actual sheaf sections. -/
theorem modulusPicardOneSheafAction_naturality
    {T T' : Over (Spec (CommRingCat.of R))} (f : T' ⟶ T)
    (g : (modulusPicardZeroGroupSheaf c i).obj.obj (op T))
    (x : (modulusPicardOneSheaf c i).obj.obj (op T)) :
    (modulusPicardOneSheaf c i).obj.map f.op (modulusPicardOneSheafAction c i ε T g x) =
      modulusPicardOneSheafAction c i ε T'
        ((modulusPicardZeroGroupSheaf c i).obj.map f.op g)
        ((modulusPicardOneSheaf c i).obj.map f.op x) := by
  let E := modulusPicardOneSheafTranslationEquiv c i ε T
  let E' := modulusPicardOneSheafTranslationEquiv c i ε T'
  let m := ((modulusPicardZeroGroupSheaf c i).obj.map f.op).hom
  exact (modulusPicardOneSheafTranslationEquiv_naturality c i ε f (g * E.symm x)).trans
    ((congrArg E' (m.map_mul g (E.symm x))).trans
      (congrArg (fun z => E' (m g * z))
        (modulusPicardOneSheafTranslationEquiv_symm_naturality c i ε f x)))

/-- Difference of sheaf sections commutes with every pullback. -/
theorem modulusPicardOneSheafDifference_naturality
    {T T' : Over (Spec (CommRingCat.of R))} (f : T' ⟶ T)
    (x y : (modulusPicardOneSheaf c i).obj.obj (op T)) :
    (modulusPicardZeroGroupSheaf c i).obj.map f.op
        (modulusPicardOneSheafDifference c i ε T x y) =
      modulusPicardOneSheafDifference c i ε T'
        ((modulusPicardOneSheaf c i).obj.map f.op x)
        ((modulusPicardOneSheaf c i).obj.map f.op y) := by
  let E := modulusPicardOneSheafTranslationEquiv c i ε T
  let m := ((modulusPicardZeroGroupSheaf c i).obj.map f.op).hom
  exact (m.map_div (E.symm x) (E.symm y)).trans
    (congrArg₂ (fun a b => a / b)
      (modulusPicardOneSheafTranslationEquiv_symm_naturality c i ε f x)
      (modulusPicardOneSheafTranslationEquiv_symm_naturality c i ε f y))

/-- The point translation supplies a free transitive action on all sheaf sections. -/
@[instance_reducible] def modulusPicardOneSheafTorsor
    (T : Over (Spec (CommRingCat.of R))) :
    Torsor ((modulusPicardZeroGroupSheaf c i).obj.obj (op T))
      ((modulusPicardOneSheaf c i).obj.obj (op T)) where
  smul := modulusPicardOneSheafAction c i ε T
  one_smul x := by
    change modulusPicardOneSheafAction c i ε T 1 x = x
    simp only [modulusPicardOneSheafAction, one_mul, Equiv.apply_symm_apply]
  mul_smul g h x := by
    change modulusPicardOneSheafAction c i ε T (g * h) x =
      modulusPicardOneSheafAction c i ε T g (modulusPicardOneSheafAction c i ε T h x)
    simp only [modulusPicardOneSheafAction, Equiv.symm_apply_apply, mul_assoc]
  sdiv := modulusPicardOneSheafDifference c i ε T
  nonempty := ⟨modulusPicardOneSheafTranslationEquiv c i ε T 1⟩
  sdiv_smul' x y := by
    change modulusPicardOneSheafAction c i ε T
      (modulusPicardOneSheafDifference c i ε T x y) y = x
    simp only [modulusPicardOneSheafAction, modulusPicardOneSheafDifference,
      div_mul_cancel, Equiv.apply_symm_apply]
  smul_sdiv' g x := by
    change modulusPicardOneSheafDifference c i ε T
      (modulusPicardOneSheafAction c i ε T g x) x = g
    simp only [modulusPicardOneSheafAction, modulusPicardOneSheafDifference,
      Equiv.symm_apply_apply, mul_div_cancel_right]

/-- Tensor translation respects the original actual class before sheafification. -/
theorem modulusPicardOneSheafTranslationEquiv_actual
    (T : Over (Spec (CommRingCat.of R))) (g : modulusPicardZeroSubgroup c i T) :
    modulusPicardOneSheafTranslationEquiv c i ε T
      (((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (modulusPicardZeroGroupPresheaf c i)).app (op T)).hom g) =
      (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (modulusPicardOnePresheaf c i)).app (op T)
          (modulusPicardOneTranslationEquiv c i ε T g) := by
  have h₀ := ConcreteCategory.congr_hom
    (NatTrans.congr_app (toModulusPicardZeroGroupSheaf_forgetIso c i) (op T)) g
  have h₁ := ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_naturality
      (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (modulusPicardOneTranslationIso c i ε).hom) (op T)) g
  change (modulusPicardOneTranslationSheafIso c i ε).hom.hom.app (op T)
      ((modulusPicardZeroGroupSheafForgetIso c i).hom.app (op T)
        (((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
          (modulusPicardZeroGroupPresheaf c i)).app (op T)).hom g)) = _
  change (modulusPicardZeroGroupSheafForgetIso c i).hom.app (op T)
      (((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (modulusPicardZeroGroupPresheaf c i)).app (op T)).hom g) = _ at h₀
  rw [h₀]
  exact h₁.symm

/-- The sheaf action on actual classes is the original rigidified tensor product. -/
theorem modulusPicardOneSheafAction_actual
    (T : Over (Spec (CommRingCat.of R)))
    (g : modulusPicardZeroSubgroup c i T) (x : ModulusPicardOneClasses c i T) :
    modulusPicardOneSheafAction c i ε T
      (((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (modulusPicardZeroGroupPresheaf c i)).app (op T)).hom g)
      ((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (modulusPicardOnePresheaf c i)).app (op T) x) =
      (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (modulusPicardOnePresheaf c i)).app (op T)
          (modulusPicardOneAction c i T g x) := by
  let ηZ : modulusPicardZeroSubgroup c i T →*
      (modulusPicardZeroGroupSheaf c i).obj.obj (op T) :=
    ((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (modulusPicardZeroGroupPresheaf c i)).app (op T)).hom
  let ηP : ModulusPicardOneClasses c i T → (modulusPicardOneSheaf c i).obj.obj (op T) :=
    (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (modulusPicardOnePresheaf c i)).app (op T)
  let E := modulusPicardOneSheafTranslationEquiv c i ε T
  let e : modulusPicardZeroSubgroup c i T ≃ ModulusPicardOneClasses c i T :=
    modulusPicardOneTranslationEquiv c i ε T
  have hx : ηP x = E (ηZ (e.symm x)) := by
    have h := modulusPicardOneSheafTranslationEquiv_actual c i ε T (e.symm x)
    change E (ηZ (e.symm x)) = ηP (e (e.symm x)) at h
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  change E (ηZ g * E.symm (ηP x)) = ηP (modulusPicardOneAction c i T g x)
  rw [hx, Equiv.symm_apply_apply, ← ηZ.map_mul]
  exact (modulusPicardOneSheafTranslationEquiv_actual c i ε T (g * e.symm x)).trans
    (congrArg ηP (modulusPicardOneTranslationEquiv_action c i ε T g x))

/-- The sheaf difference on actual classes is the original rigidified tensor quotient. -/
theorem modulusPicardOneSheafDifference_actual
    (T : Over (Spec (CommRingCat.of R))) (x y : ModulusPicardOneClasses c i T) :
    modulusPicardOneSheafDifference c i ε T
      ((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (modulusPicardOnePresheaf c i)).app (op T) x)
      ((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (modulusPicardOnePresheaf c i)).app (op T) y) =
      ((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (modulusPicardZeroGroupPresheaf c i)).app (op T)).hom
          (modulusPicardOneDifference c i T x y) := by
  let ηZ : modulusPicardZeroSubgroup c i T →*
      (modulusPicardZeroGroupSheaf c i).obj.obj (op T) :=
    ((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (modulusPicardZeroGroupPresheaf c i)).app (op T)).hom
  let ηP : ModulusPicardOneClasses c i T → (modulusPicardOneSheaf c i).obj.obj (op T) :=
    (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
      (modulusPicardOnePresheaf c i)).app (op T)
  let E := modulusPicardOneSheafTranslationEquiv c i ε T
  let e : modulusPicardZeroSubgroup c i T ≃ ModulusPicardOneClasses c i T :=
    modulusPicardOneTranslationEquiv c i ε T
  have hp (z : ModulusPicardOneClasses c i T) : E.symm (ηP z) = ηZ (e.symm z) := by
    apply E.injective
    rw [Equiv.apply_symm_apply]
    have h := modulusPicardOneSheafTranslationEquiv_actual c i ε T (e.symm z)
    change E (ηZ (e.symm z)) = ηP (e (e.symm z)) at h
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  change E.symm (ηP x) / E.symm (ηP y) = ηZ (modulusPicardOneDifference c i T x y)
  rw [hp x, hp y, ← ηZ.map_div]
  exact congrArg ηZ (modulusPicardOneTranslationEquiv_difference c i ε T x y)

end AlgebraicGeometry.GeneralizedJacobian
