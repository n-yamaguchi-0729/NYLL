/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.ModulusAbelRestriction
import Nyll.JacobianVarieties.Generalized.ModulusAbelOneFamily
import Nyll.JacobianVarieties.Generalized.ModulusRestrictionMapSheaf
import Nyll.JacobianVarieties.Generalized.PicardOneTorsor

/-! # Restriction of actual intrinsic Picard-one classes and the Abel square -/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D D' : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) {i : D ⟶ C} {i' : D' ⟶ C}
  [IsClosedImmersion i] [IsClosedImmersion i'] (j : D' ⟶ D) (w : i' = j ≫ i)
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

/-- Restricting the specified modulus frame preserves the intrinsic degree-one condition. -/
def modulusRestrictionOneClasses (T : Over (Spec (CommRingCat.of R))) :
    ModulusPicardOneClasses c i T → ModulusPicardOneClasses c i' T := fun x =>
  ⟨modulusRestrictionClasses c j w T.hom x.val, by
    intro k _ _ t s
    obtain ⟨P, hP⟩ := x.property k t s
    refine ⟨P ≫ modulusComplementRestriction c j w, ?_⟩
    let m : RigidifiedLineBundle.Classes (modulusBaseChange c i T.hom) →*
        RigidifiedLineBundle.Classes (modulusBaseChange c i t) :=
      ((modulusPicardGroupPresheaf c i).map s.op).hom
    let m' : RigidifiedLineBundle.Classes (modulusBaseChange c i' T.hom) →*
        RigidifiedLineBundle.Classes (modulusBaseChange c i' t) :=
      ((modulusPicardGroupPresheaf c i').map s.op).hom
    let r := modulusRestrictionClasses c j w t
    let b : RigidifiedLineBundle.Classes (modulusBaseChange c i t) :=
      modulusAbelPointClass c i (T := Over.mk t) P
    let b' : RigidifiedLineBundle.Classes (modulusBaseChange c i' t) :=
      modulusAbelPointClass c i' (T := Over.mk t) (P ≫ modulusComplementRestriction c j w)
    have hn : r (m x.val) = m' (modulusRestrictionClasses c j w T.hom x.val) :=
      modulusRestrictionClasses_naturality c j w s x.val
    have hb : r b = b' := modulusRestrictionClasses_abelPoint c j w P
    change m' (modulusRestrictionClasses c j w T.hom x.val) / b' ∈ _
    rw [← hn, ← hb, ← r.map_div]
    exact (modulusRestrictionClasses_zero_iff c j w t (m x.val / b)).mpr hP⟩

/-- Actual degree-one restriction commutes with every test-scheme pullback. -/
def modulusRestrictionOnePresheaf :
    modulusPicardOnePresheaf c i ⟶ modulusPicardOnePresheaf c i' where
  app T := TypeCat.ofHom (modulusRestrictionOneClasses c j w T.unop)
  naturality {T T'} f := by
    apply TypeCat.homEquiv.injective
    funext x
    apply Subtype.ext
    exact modulusRestrictionClasses_naturality c j w f.unop x.val

omit [GeometricallyIntegral c] in
/-- Restricting a full modulus to itself is the identity on actual degree-one classes. -/
theorem modulusRestrictionOnePresheaf_id :
    modulusRestrictionOnePresheaf c (𝟙 D) (Category.id_comp i).symm =
      𝟙 (modulusPicardOnePresheaf c i) := by
  ext T x
  apply Subtype.ext
  exact modulusRestrictionClasses_id c T.unop.hom x.val

omit [GeometricallyIntegral c] in
/-- Successive restrictions use the composite morphism of whole moduli. -/
theorem modulusRestrictionOnePresheaf_comp {D'' : Scheme.{u}} {i'' : D'' ⟶ C}
    [IsClosedImmersion i''] (k : D'' ⟶ D') (w' : i'' = k ≫ i') :
    modulusRestrictionOnePresheaf c j w ≫ modulusRestrictionOnePresheaf c k w' =
      modulusRestrictionOnePresheaf c (k ≫ j) (by rw [w', w, Category.assoc]) := by
  ext T x
  apply Subtype.ext
  exact modulusRestrictionClasses_comp c j w k w' T.unop.hom x.val

omit [GeometricallyIntegral c] in
/-- Degree-one restriction is equivariant for restriction of actual tensor classes. -/
theorem modulusRestrictionOneClasses_action (T : Over (Spec (CommRingCat.of R)))
    (g : modulusPicardZeroSubgroup c i T) (x : ModulusPicardOneClasses c i T) :
    modulusRestrictionOneClasses c j w T (modulusPicardOneAction c i T g x) =
      modulusPicardOneAction c i' T (modulusRestrictionZeroClasses c j w T g)
        (modulusRestrictionOneClasses c j w T x) :=
  Subtype.ext ((modulusRestrictionClasses c j w T.hom).map_mul g.val x.val)

/-- The actual degree-one restriction after fppf sheafification. -/
def modulusRestrictionOneSheaf : modulusPicardOneSheaf c i ⟶ modulusPicardOneSheaf c i' :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (Type (u + 1))).map (modulusRestrictionOnePresheaf c j w)

omit [GeometricallyIntegral c] in
/-- The sheaf map agrees with restriction of every actual rigidified degree-one class. -/
@[reassoc] theorem toSheafify_modulusRestrictionOneSheaf :
    toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
        (modulusPicardOnePresheaf c i) ≫ (modulusRestrictionOneSheaf c j w).hom =
      modulusRestrictionOnePresheaf c j w ≫
        toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
          (modulusPicardOnePresheaf c i') :=
  (toSheafify_naturality (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (modulusRestrictionOnePresheaf c j w)).symm

omit [GeometricallyIntegral c] in
/-- The intrinsic degree-one sheaf restriction has the same identity law. -/
theorem modulusRestrictionOneSheaf_id :
    modulusRestrictionOneSheaf c (𝟙 D) (Category.id_comp i).symm =
      𝟙 (modulusPicardOneSheaf c i) := by
  let H := presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1))
  exact (congrArg (fun v => H.map v) (modulusRestrictionOnePresheaf_id c (i := i))).trans
    (H.map_id _)

omit [GeometricallyIntegral c] in
/-- Sheafifying actual frame restriction preserves its composition law. -/
theorem modulusRestrictionOneSheaf_comp {D'' : Scheme.{u}} {i'' : D'' ⟶ C}
    [IsClosedImmersion i''] (k : D'' ⟶ D') (w' : i'' = k ≫ i') :
    modulusRestrictionOneSheaf c j w ≫ modulusRestrictionOneSheaf c k w' =
      modulusRestrictionOneSheaf c (k ≫ j) (by rw [w', w, Category.assoc]) := by
  let H := presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1))
  exact (H.map_comp (modulusRestrictionOnePresheaf c j w)
    (modulusRestrictionOnePresheaf c k w')).symm.trans
      (congrArg (fun v => H.map v) (modulusRestrictionOnePresheaf_comp c j w k w'))

omit [GeometricallyIntegral c] in
/-- The original canonical Abel families commute with restriction before sheafification. -/
theorem modulusAbelOnePresheafMap_restriction :
    modulusAbelOnePresheafMap c i ≫ modulusRestrictionOnePresheaf c j w =
      uliftYoneda.map (modulusComplementRestriction c j w) ≫
        modulusAbelOnePresheafMap c i' := by
  apply NatTrans.ext
  funext T
  apply TypeCat.homEquiv.injective
  funext x
  apply Subtype.ext
  exact modulusRestrictionClasses_abelPoint c j w x.down

omit [GeometricallyIntegral c] in
/-- The Abel square after sheafification is induced by equality of the actual point frames. -/
theorem modulusAbelOneSheafMap_restriction :
    modulusAbelOneSheafMap c i ≫ (modulusRestrictionOneSheaf c j w).hom =
      uliftYoneda.map (modulusComplementRestriction c j w) ≫
        modulusAbelOneSheafMap c i' := by
  let A := modulusAbelOnePresheafMap c i
  let B := modulusAbelOnePresheafMap c i'
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of R))
  let η := toSheafify J (modulusPicardOnePresheaf c i)
  let η' := toSheafify J (modulusPicardOnePresheaf c i')
  let r := modulusRestrictionOnePresheaf c j w
  let r' := (modulusRestrictionOneSheaf c j w).hom
  let f := uliftYoneda.map (modulusComplementRestriction c j w)
  exact (Category.assoc A η r').trans
    ((congrArg (fun z => A ≫ z) (toSheafify_modulusRestrictionOneSheaf c j w)).trans
      ((Category.assoc A r η').symm.trans
        ((congrArg (fun z => z ≫ η') (modulusAbelOnePresheafMap_restriction c j w)).trans
          (Category.assoc f B η'))))

end AlgebraicGeometry.GeneralizedJacobian
