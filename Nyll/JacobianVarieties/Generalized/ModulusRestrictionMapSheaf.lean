/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusRestrictionMap
import Nyll.JacobianVarieties.Generalized.PicardZeroGroupSheaf

/-! # Restriction maps of actual modulus Picard-zero group sheaves -/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D D' : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) {i : D ⟶ C} {i' : D' ⟶ C}
  (j : D' ⟶ D) (w : i' = j ≫ i)

/-- Restriction of the actual trivialization preserves the Picard-zero subgroup. -/
def modulusRestrictionZeroClasses (T : Over (Spec (CommRingCat.of R))) :
    (modulusPicardZeroGroupPresheaf c i).obj (op T) →*
      (modulusPicardZeroGroupPresheaf c i').obj (op T) where
  toFun x := ⟨modulusRestrictionClasses c j w T.hom x.val,
    (modulusRestrictionClasses_zero_iff c j w T.hom x.val).mpr x.property⟩
  map_one' := Subtype.ext (modulusRestrictionClasses c j w T.hom).map_one
  map_mul' x y := Subtype.ext ((modulusRestrictionClasses c j w T.hom).map_mul x.val y.val)

/-- The tensor-preserving natural restriction map before sheafification. -/
def modulusRestrictionZeroPresheaf :
    modulusPicardZeroGroupPresheaf c i ⟶ modulusPicardZeroGroupPresheaf c i' where
  app T := CommGrpCat.ofHom (modulusRestrictionZeroClasses c j w T.unop)
  naturality {T T'} f := by
    refine CommGrpCat.hom_ext (MonoidHom.ext fun x => ?_)
    apply Subtype.ext
    exact modulusRestrictionClasses_naturality c j w f.unop x.val

theorem modulusRestrictionZeroPresheaf_id :
    modulusRestrictionZeroPresheaf c (𝟙 D) (Category.id_comp i).symm =
      𝟙 (modulusPicardZeroGroupPresheaf c i) := by
  apply NatTrans.ext
  funext T
  refine CommGrpCat.hom_ext (MonoidHom.ext fun x => ?_)
  apply Subtype.ext
  exact modulusRestrictionClasses_id c T.unop.hom x.val

theorem modulusRestrictionZeroPresheaf_comp {D'' : Scheme.{u}} {i'' : D'' ⟶ C}
    (k : D'' ⟶ D') (w' : i'' = k ≫ i') :
    modulusRestrictionZeroPresheaf c j w ≫ modulusRestrictionZeroPresheaf c k w' =
      modulusRestrictionZeroPresheaf c (k ≫ j) (by rw [w', w, Category.assoc]) := by
  apply NatTrans.ext
  funext T
  refine CommGrpCat.hom_ext (MonoidHom.ext fun x => ?_)
  apply Subtype.ext
  exact modulusRestrictionClasses_comp c j w k w' T.unop.hom x.val

/-- Fppf sheafification of the actual rigidification restriction homomorphism. -/
def modulusRestrictionZeroSheaf :
    modulusPicardZeroGroupSheaf c i ⟶ modulusPicardZeroGroupSheaf c i' :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    CommGrpCat.{u + 1}).map (modulusRestrictionZeroPresheaf c j w)

/-- The sheaf map agrees with restriction on every actual rigidified class. -/
@[reassoc] theorem toSheafify_modulusRestrictionZeroSheaf :
    toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (modulusPicardZeroGroupPresheaf c i) ≫ (modulusRestrictionZeroSheaf c j w).hom =
      modulusRestrictionZeroPresheaf c j w ≫
        toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
          (modulusPicardZeroGroupPresheaf c i') :=
  (toSheafify_naturality (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (modulusRestrictionZeroPresheaf c j w)).symm

theorem modulusRestrictionZeroSheaf_id :
    modulusRestrictionZeroSheaf c (𝟙 D) (Category.id_comp i).symm =
      𝟙 (modulusPicardZeroGroupSheaf c i) := by
  let H := presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    CommGrpCat.{u + 1}
  exact (congrArg (fun v => H.map v)
    (modulusRestrictionZeroPresheaf_id c (i := i))).trans (H.map_id _)

theorem modulusRestrictionZeroSheaf_comp {D'' : Scheme.{u}} {i'' : D'' ⟶ C}
    (k : D'' ⟶ D') (w' : i'' = k ≫ i') :
    modulusRestrictionZeroSheaf c j w ≫ modulusRestrictionZeroSheaf c k w' =
      modulusRestrictionZeroSheaf c (k ≫ j) (by rw [w', w, Category.assoc]) := by
  let H := presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    CommGrpCat.{u + 1}
  exact (H.map_comp (modulusRestrictionZeroPresheaf c j w)
    (modulusRestrictionZeroPresheaf c k w')).symm.trans
      (congrArg (fun v => H.map v) (modulusRestrictionZeroPresheaf_comp c j w k w'))

end AlgebraicGeometry.GeneralizedJacobian
