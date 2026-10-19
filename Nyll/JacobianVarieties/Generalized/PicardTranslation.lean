/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardZeroGroupFunctor
import Mathlib.Algebra.Torsor.Defs

/-!
# Actual translations of the modulus Picard-zero presheaf

An actual rigidified class over the ground scheme determines its pullbacks on
all test schemes. Classes whose difference from this family is algebraically
trivial form a natural torsor under the modulus Picard-zero presheaf.
Translation gives a natural isomorphism with Picard-zero, and therefore an
isomorphism of their fppf sheafifications. No representability hypothesis enters
this construction. For the class of a point outside the modulus this is the
pointed degree-one component; identifying it independently of a point is separate.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C)
  (b : RigidifiedLineBundle.Classes (modulusBaseChange c i (𝟙 (Spec (CommRingCat.of R)))))

/-- Pull back a specified ground-scheme class to an arbitrary test scheme. -/
def modulusGroundClass (T : Over (Spec (CommRingCat.of R))) :
    RigidifiedLineBundle.Classes (modulusBaseChange c i T.hom) := by
  let p : T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of R))) :=
    Over.homMk T.hom (Category.comp_id T.hom)
  exact ((modulusPicardGroupPresheaf c i).map p.op).hom b

/-- These are restrictions of the same actual class, so the origins are natural. -/
theorem modulusGroundClass_naturality
    {T T' : Over (Spec (CommRingCat.of R))} (f : T' ⟶ T) :
    (modulusPicardGroupPresheaf c i).map f.op (modulusGroundClass c i b T) =
      modulusGroundClass c i b T' := by
  let p : T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of R))) :=
    Over.homMk T.hom (Category.comp_id T.hom)
  let p' : T' ⟶ Over.mk (𝟙 (Spec (CommRingCat.of R))) :=
    Over.homMk T'.hom (Category.comp_id T'.hom)
  have hp : f ≫ p = p' := by
    apply Over.OverMorphism.ext
    exact Over.w f
  change (modulusPicardGroupPresheaf c i).obj
    (op (Over.mk (𝟙 (Spec (CommRingCat.of R))))) at b
  change (modulusPicardGroupPresheaf c i).map f.op
      ((modulusPicardGroupPresheaf c i).map p.op b) =
        (modulusPicardGroupPresheaf c i).map p'.op b
  rw [← CommGrpCat.comp_apply, ← Functor.map_comp]
  exact congrArg (fun q => (modulusPicardGroupPresheaf c i).map q b)
    (congrArg Quiver.Hom.op hp)

/-- Classes algebraically equivalent to the specified actual ground class. -/
def modulusPicardTranslateSubfunctor : Subfunctor (modulusPicardPresheaf c i) where
  obj T := {x : RigidifiedLineBundle.Classes (modulusBaseChange c i T.unop.hom) |
    x / modulusGroundClass c i b T.unop ∈
    modulusPicardZeroSubgroup c i T.unop}
  map {T T'} f := by
    intro x hx
    change RigidifiedLineBundle.Classes (modulusBaseChange c i T.unop.hom) at x
    let m : RigidifiedLineBundle.Classes (modulusBaseChange c i T.unop.hom) →*
        RigidifiedLineBundle.Classes (modulusBaseChange c i T'.unop.hom) :=
      ((modulusPicardGroupPresheaf c i).map f).hom
    have hm : m (modulusGroundClass c i b T.unop) = modulusGroundClass c i b T'.unop :=
      modulusGroundClass_naturality c i b f.unop
    have h := (modulusPicardZeroSubfunctor c i).map f hx
    change m (x / modulusGroundClass c i b T.unop) ∈
      modulusPicardZeroSubgroup c i T'.unop at h
    rw [m.map_div, hm] at h
    exact h

/-- The actual translated Picard presheaf, retaining the chosen modulus trivialization. -/
def modulusPicardTranslatePresheaf :
    (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type (u + 1) :=
  (modulusPicardTranslateSubfunctor c i b).toFunctor

/-- Concrete classes in the translated component, with their original rigidifications. -/
abbrev ModulusPicardTranslateClasses (T : Over (Spec (CommRingCat.of R))) :=
  {x : RigidifiedLineBundle.Classes (modulusBaseChange c i T.hom) //
    x / modulusGroundClass c i b T ∈ modulusPicardZeroSubgroup c i T}

/-- Tensoring with the chosen family identifies zero classes with its translate. -/
def modulusPicardTranslationEquiv (T : Over (Spec (CommRingCat.of R))) :
    modulusPicardZeroSubgroup c i T ≃
      ModulusPicardTranslateClasses c i b T where
  toFun x := ⟨x.1 * modulusGroundClass c i b T, by
    change x.1 * modulusGroundClass c i b T / modulusGroundClass c i b T ∈ _
    rw [mul_div_cancel_right]
    exact x.2⟩
  invFun y := ⟨y.1 / modulusGroundClass c i b T, y.2⟩
  left_inv x := Subtype.ext (mul_div_cancel_right x.1 (modulusGroundClass c i b T))
  right_inv y := Subtype.ext (div_mul_cancel y.1 (modulusGroundClass c i b T))

/-- The classifying equivalence respects every change of test scheme. -/
def modulusPicardTranslationIso :
    modulusPicardZeroPresheaf c i ≅ modulusPicardTranslatePresheaf c i b :=
  NatIso.ofComponents (fun T => Equiv.toIso (modulusPicardTranslationEquiv c i b T.unop))
    (fun {T T'} f => by
      apply TypeCat.homEquiv.injective
      funext x
      apply Subtype.ext
      change modulusPicardZeroSubgroup c i T.unop at x
      let m : RigidifiedLineBundle.Classes (modulusBaseChange c i T.unop.hom) →*
          RigidifiedLineBundle.Classes (modulusBaseChange c i T'.unop.hom) :=
        ((modulusPicardGroupPresheaf c i).map f).hom
      have hm : m (modulusGroundClass c i b T.unop) = modulusGroundClass c i b T'.unop :=
        modulusGroundClass_naturality c i b f.unop
      change m x.1 * modulusGroundClass c i b T'.unop =
        m (x.1 * modulusGroundClass c i b T.unop)
      rw [m.map_mul, hm])

/-- The fppf sheaf of classes algebraically equivalent to the selected family. -/
def modulusPicardTranslateSheaf :
    Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (Type (u + 1))).obj (modulusPicardTranslatePresheaf c i b)

/-- The actual tensor translation also identifies the fppf sheafifications. -/
def modulusPicardTranslationSheafIso :
    modulusPicardZeroSheaf c i ≅ modulusPicardTranslateSheaf c i b :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    (Type (u + 1))).mapIso (modulusPicardTranslationIso c i b)

/-- Tensor product by a zero class acts on the actual translated classes. -/
def modulusPicardTranslateAction (T : Over (Spec (CommRingCat.of R)))
    (g : modulusPicardZeroSubgroup c i T)
    (x : ModulusPicardTranslateClasses c i b T) :
    ModulusPicardTranslateClasses c i b T :=
  ⟨g.1 * x.1, by
    change g.1 * x.1 / modulusGroundClass c i b T ∈ _
    rw [mul_div_assoc]
    exact (modulusPicardZeroSubgroup c i T).mul_mem g.2 x.2⟩

/-- Difference of two translated classes is an actual modulus zero class. -/
def modulusPicardTranslateDifference (T : Over (Spec (CommRingCat.of R)))
    (x y : ModulusPicardTranslateClasses c i b T) :
    modulusPicardZeroSubgroup c i T :=
  ⟨x.1 / y.1, by
    have h := (modulusPicardZeroSubgroup c i T).div_mem x.2 y.2
    rw [div_div_div_cancel_right] at h
    exact h⟩

/-- Actual tensor product and division give a free transitive action on each test. -/
@[instance_reducible] def modulusPicardTranslateTorsor (T : Over (Spec (CommRingCat.of R))) :
    Torsor (modulusPicardZeroSubgroup c i T)
      (ModulusPicardTranslateClasses c i b T) where
  smul := modulusPicardTranslateAction c i b T
  one_smul x := Subtype.ext (one_mul x.1)
  mul_smul g h x := Subtype.ext (mul_assoc g.1 h.1 x.1)
  sdiv := modulusPicardTranslateDifference c i b T
  nonempty := ⟨modulusPicardTranslationEquiv c i b T 1⟩
  sdiv_smul' x y := Subtype.ext (div_mul_cancel x.1 y.1)
  smul_sdiv' g x := Subtype.ext (mul_div_cancel_right g.1 x.1)

/-- Pullback respects the actual tensor action, not merely a transported bijection. -/
theorem modulusPicardTranslateAction_naturality
    {T T' : Over (Spec (CommRingCat.of R))} (f : T' ⟶ T)
    (g : modulusPicardZeroSubgroup c i T)
    (x : ModulusPicardTranslateClasses c i b T) :
    (modulusPicardTranslatePresheaf c i b).map f.op
        (modulusPicardTranslateAction c i b T g x) =
      modulusPicardTranslateAction c i b T'
        ((modulusPicardZeroGroupPresheaf c i).map f.op g)
        ((modulusPicardTranslatePresheaf c i b).map f.op x) := by
  apply Subtype.ext
  exact ((modulusPicardGroupPresheaf c i).map f.op).hom.map_mul g.1 x.1

end AlgebraicGeometry.GeneralizedJacobian
