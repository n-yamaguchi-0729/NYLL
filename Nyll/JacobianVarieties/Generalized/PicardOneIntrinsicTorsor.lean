/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardOneTorsor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# The intrinsic Picard-one torsor isomorphism

The actual tensor action and difference give an isomorphism of presheaf
products. Left exact fppf sheafification carries this isomorphism to the
intrinsic sheaves. The construction and both inverse identities use no point.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsClosedImmersion i]
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

/-- The intrinsic actual tensor action, as a natural transformation on a product. -/
def modulusPicardOneActionMap :
    modulusPicardZeroPresheaf c i ⨯ modulusPicardOnePresheaf c i ⟶
      modulusPicardOnePresheaf c i where
  app T := TypeCat.ofHom (fun x => modulusPicardOneAction c i T.unop
    ((prod.fst : modulusPicardZeroPresheaf c i ⨯ modulusPicardOnePresheaf c i ⟶ _).app T x)
    ((prod.snd : modulusPicardZeroPresheaf c i ⨯ modulusPicardOnePresheaf c i ⟶ _).app T x))
  naturality {T T'} f := by
    apply TypeCat.homEquiv.injective
    funext x
    have hf := ConcreteCategory.congr_hom
      ((prod.fst : modulusPicardZeroPresheaf c i ⨯ modulusPicardOnePresheaf c i ⟶ _).naturality f) x
    have hs := ConcreteCategory.congr_hom
      ((prod.snd : modulusPicardZeroPresheaf c i ⨯ modulusPicardOnePresheaf c i ⟶ _).naturality f) x
    change modulusPicardOneAction c i T'.unop
      ((prod.fst : modulusPicardZeroPresheaf c i ⨯ modulusPicardOnePresheaf c i ⟶ _).app T'
        ((modulusPicardZeroPresheaf c i ⨯ modulusPicardOnePresheaf c i).map f x))
      ((prod.snd : modulusPicardZeroPresheaf c i ⨯ modulusPicardOnePresheaf c i ⟶ _).app T'
        ((modulusPicardZeroPresheaf c i ⨯ modulusPicardOnePresheaf c i).map f x)) = _
    exact (congrArg₂ (modulusPicardOneAction c i T'.unop) hf hs).trans
      (modulusPicardOneAction_naturality c i f.unop _ _).symm

/-- The intrinsic actual difference of two degree-one classes, as a natural transformation. -/
def modulusPicardOneDifferenceMap :
    modulusPicardOnePresheaf c i ⨯ modulusPicardOnePresheaf c i ⟶
      modulusPicardZeroPresheaf c i where
  app T := TypeCat.ofHom (fun x => modulusPicardOneDifference c i T.unop
    ((prod.fst : modulusPicardOnePresheaf c i ⨯ modulusPicardOnePresheaf c i ⟶ _).app T x)
    ((prod.snd : modulusPicardOnePresheaf c i ⨯ modulusPicardOnePresheaf c i ⟶ _).app T x))
  naturality {T T'} f := by
    apply TypeCat.homEquiv.injective
    funext x
    have hf := ConcreteCategory.congr_hom
      ((prod.fst : modulusPicardOnePresheaf c i ⨯ modulusPicardOnePresheaf c i ⟶ _).naturality f) x
    have hs := ConcreteCategory.congr_hom
      ((prod.snd : modulusPicardOnePresheaf c i ⨯ modulusPicardOnePresheaf c i ⟶ _).naturality f) x
    change modulusPicardOneDifference c i T'.unop
      ((prod.fst : modulusPicardOnePresheaf c i ⨯ modulusPicardOnePresheaf c i ⟶ _).app T'
        ((modulusPicardOnePresheaf c i ⨯ modulusPicardOnePresheaf c i).map f x))
      ((prod.snd : modulusPicardOnePresheaf c i ⨯ modulusPicardOnePresheaf c i ⟶ _).app T'
        ((modulusPicardOnePresheaf c i ⨯ modulusPicardOnePresheaf c i).map f x)) = _
    exact (congrArg₂ (modulusPicardOneDifference c i T'.unop) hf hs).trans
      (modulusPicardOneDifference_naturality c i f.unop _ _).symm

/-- Actual tensor action and actual difference satisfy the presheaf torsor identity. -/
def modulusPicardOnePresheafTorsorIso :
    modulusPicardZeroPresheaf c i ⨯ modulusPicardOnePresheaf c i ≅
      modulusPicardOnePresheaf c i ⨯ modulusPicardOnePresheaf c i where
  hom := prod.lift (modulusPicardOneActionMap c i) prod.snd
  inv := prod.lift (modulusPicardOneDifferenceMap c i) prod.snd
  hom_inv_id := by
    apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, Category.id_comp]
      ext T x
      change modulusPicardOneDifference c i T.unop
        ((prod.fst : modulusPicardOnePresheaf c i ⨯ modulusPicardOnePresheaf c i ⟶ _).app T
          ((prod.lift (modulusPicardOneActionMap c i) prod.snd).app T x))
        ((prod.snd : modulusPicardOnePresheaf c i ⨯ modulusPicardOnePresheaf c i ⟶ _).app T
          ((prod.lift (modulusPicardOneActionMap c i) prod.snd).app T x)) = _
      have hf := ConcreteCategory.congr_hom
        (NatTrans.congr_app (prod.lift_fst (modulusPicardOneActionMap c i) prod.snd) T) x
      have hs := ConcreteCategory.congr_hom
        (NatTrans.congr_app (prod.lift_snd (modulusPicardOneActionMap c i) prod.snd) T) x
      exact (congrArg₂ (modulusPicardOneDifference c i T.unop) hf hs).trans
        (modulusPicardOneAction_difference c i T.unop _ _)
    · simp only [Category.assoc, prod.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, Category.id_comp]
      ext T x
      change modulusPicardOneAction c i T.unop
        ((prod.fst : modulusPicardZeroPresheaf c i ⨯ modulusPicardOnePresheaf c i ⟶ _).app T
          ((prod.lift (modulusPicardOneDifferenceMap c i) prod.snd).app T x))
        ((prod.snd : modulusPicardZeroPresheaf c i ⨯ modulusPicardOnePresheaf c i ⟶ _).app T
          ((prod.lift (modulusPicardOneDifferenceMap c i) prod.snd).app T x)) = _
      have hf := ConcreteCategory.congr_hom
        (NatTrans.congr_app (prod.lift_fst (modulusPicardOneDifferenceMap c i) prod.snd) T) x
      have hs := ConcreteCategory.congr_hom
        (NatTrans.congr_app (prod.lift_snd (modulusPicardOneDifferenceMap c i) prod.snd) T) x
      exact (congrArg₂ (modulusPicardOneAction c i T.unop) hf hs).trans
        (modulusPicardOneDifference_action c i T.unop _ _)
    · simp only [Category.assoc, prod.lift_snd, Category.id_comp]

/-- The intrinsic fppf sheaves satisfy the same torsor identity, independently of a point. -/
def modulusPicardOneSheafTorsorIso :
    modulusPicardZeroSheaf c i ⨯ modulusPicardOneSheaf c i ≅
      modulusPicardOneSheaf c i ⨯ modulusPicardOneSheaf c i :=
  (PreservesLimitPair.iso
      (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1)))
      (modulusPicardZeroPresheaf c i) (modulusPicardOnePresheaf c i)).symm ≪≫
    (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1))).mapIso
      (modulusPicardOnePresheafTorsorIso c i) ≪≫
    PreservesLimitPair.iso
      (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1)))
      (modulusPicardOnePresheaf c i) (modulusPicardOnePresheaf c i)

/-- Its action component is precisely sheafification of the intrinsic raw tensor action. -/
theorem modulusPicardOneSheafTorsorIso_action :
    (modulusPicardOneSheafTorsorIso c i).hom ≫ prod.fst =
      (PreservesLimitPair.iso
        (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1)))
        (modulusPicardZeroPresheaf c i) (modulusPicardOnePresheaf c i)).inv ≫
      (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1))).map
        (modulusPicardOneActionMap c i) := by
  let S := presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1))
  let F := modulusPicardZeroPresheaf c i
  let P := modulusPicardOnePresheaf c i
  change (PreservesLimitPair.iso S F P).inv ≫
    S.map (prod.lift (modulusPicardOneActionMap c i) prod.snd) ≫
      prodComparison S P P ≫ prod.fst = _
  rw [prodComparison_fst, ← S.map_comp, prod.lift_fst]

/-- The intrinsic torsor isomorphism leaves the second degree-one class fixed. -/
theorem modulusPicardOneSheafTorsorIso_snd :
    (modulusPicardOneSheafTorsorIso c i).hom ≫ prod.snd = prod.snd := by
  let S := presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1))
  let F := modulusPicardZeroPresheaf c i
  let P := modulusPicardOnePresheaf c i
  change (PreservesLimitPair.iso S F P).inv ≫
    S.map (prod.lift (modulusPicardOneActionMap c i) prod.snd) ≫
      prodComparison S P P ≫ prod.snd = _
  rw [prodComparison_snd, ← S.map_comp, prod.lift_snd]
  exact PreservesLimitPair.iso_inv_snd S F P

/-- The inverse rigidified-difference isomorphism likewise retains the second class. -/
theorem modulusPicardOneSheafTorsorIso_inv_snd :
    (modulusPicardOneSheafTorsorIso c i).inv ≫ prod.snd = prod.snd := by
  rw [← modulusPicardOneSheafTorsorIso_snd c i, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

end AlgebraicGeometry.GeneralizedJacobian
