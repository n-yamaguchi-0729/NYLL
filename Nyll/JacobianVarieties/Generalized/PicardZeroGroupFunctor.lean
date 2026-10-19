/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PicardZero
import Nyll.JacobianVarieties.Generalized.PicardGroupFunctor
import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicEquivalence.AlgEquivZeroGroupCut
import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# The commutative group presheaf of modulus Picard-zero classes

The geometric-fibre zero condition is closed under the actual rigidified tensor
product and inverse. The subgroup retains the chosen trivialization on the full
modulus. Pullback gives group homomorphisms on these actual subgroups.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {X D : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of R)) (i : D ⟶ X)

/-- The unit with its canonical modulus trivialization is fibrewise algebraically trivial. -/
theorem one_mem_modulusPicardZero (T : Over (Spec (CommRingCat.of R))) :
    (1 : RigidifiedLineBundle.Classes (modulusBaseChange c i T.hom)) ∈
      (modulusPicardZeroSubfunctor c i).obj (op T) := by
  intro k _ _ s
  let f := pullback.fst (pullback.snd c T.hom) s
  let a := fibreAt c T.hom s
  refine ⟨Spec (CommRingCat.of k), 𝟙 _, inferInstance, geometricallyIntegral_id_Spec k,
    𝟙_ (pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules,
    Scheme.Modules.isInvertible_unit _, ⟨𝟙 _, Category.comp_id _⟩,
    ⟨𝟙 _, Category.comp_id _⟩, ⟨Scheme.Modules.pullbackUnitIso _⟩, ⟨?_⟩⟩
  exact Scheme.Modules.pullbackUnitIso _ ≪≫
    (Scheme.Modules.pullbackUnitIso (pullback.fst a (𝟙 _))).symm ≪≫
    (Scheme.Modules.pullback (pullback.fst a (𝟙 _))).mapIso
      (Scheme.Modules.pullbackUnitIso f).symm

/-- Tensor product preserves the geometric-fibre zero condition on actual modulus classes. -/
theorem mul_mem_modulusPicardZero (T : Over (Spec (CommRingCat.of R)))
    {x y : RigidifiedLineBundle.Classes (modulusBaseChange c i T.hom)}
    (hx : x ∈ (modulusPicardZeroSubfunctor c i).obj (op T))
    (hy : y ∈ (modulusPicardZeroSubfunctor c i).obj (op T)) :
    x * y ∈ (modulusPicardZeroSubfunctor c i).obj (op T) := by
  induction x using Quotient.ind with
  | _ M =>
    induction y using Quotient.ind with
    | _ N =>
      intro k _ _ s
      exact ((hx k s).tensor (hy k s)).of_iso
        (Scheme.Modules.pullbackTensorObjIso _ M.L N.L).symm

/-- The chosen rigidified dual preserves the same zero condition. -/
theorem inv_mem_modulusPicardZero (T : Over (Spec (CommRingCat.of R)))
    {x : RigidifiedLineBundle.Classes (modulusBaseChange c i T.hom)}
    (hx : x ∈ (modulusPicardZeroSubfunctor c i).obj (op T)) :
    x⁻¹ ∈ (modulusPicardZeroSubfunctor c i).obj (op T) := by
  induction x using Quotient.ind with
  | _ M =>
    change (RigidifiedLineBundle.classOf M)⁻¹ ∈ _
    rw [← RigidifiedLineBundle.classOf_dual]
    intro k _ _ s
    apply (hx k s).of_tensor_iso_unit
    exact (Scheme.Modules.pullbackTensorObjIso _ M.L M.dual.L).symm ≪≫
      (Scheme.Modules.pullback _).mapIso M.evaluation ≪≫ Scheme.Modules.pullbackUnitIso _

/-- The actual subgroup of compatible-isomorphism classes satisfying Picard-zero. -/
def modulusPicardZeroSubgroup (T : Over (Spec (CommRingCat.of R))) :
    Subgroup (RigidifiedLineBundle.Classes (modulusBaseChange c i T.hom)) where
  carrier := (modulusPicardZeroSubfunctor c i).obj (op T)
  one_mem' := one_mem_modulusPicardZero c i T
  mul_mem' := mul_mem_modulusPicardZero c i T
  inv_mem' := inv_mem_modulusPicardZero c i T

/-- Pullback of actual modulus zero classes is a commutative-group-valued presheaf. -/
def modulusPicardZeroGroupPresheaf :
    (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ CommGrpCat.{u + 1} where
  obj T := CommGrpCat.of (modulusPicardZeroSubgroup c i T.unop)
  map {T T'} s := CommGrpCat.ofHom
    (MonoidHom.mk' ((modulusPicardZeroPresheaf c i).map s)
      (fun x y => Subtype.ext (((modulusPicardGroupPresheaf c i).map s).hom.map_mul x.val y.val)))
  map_id T := by
    refine CommGrpCat.hom_ext (MonoidHom.ext fun x => ?_)
    exact ConcreteCategory.congr_hom ((modulusPicardZeroPresheaf c i).map_id T) x
  map_comp s r := by
    refine CommGrpCat.hom_ext (MonoidHom.ext fun x => ?_)
    exact ConcreteCategory.congr_hom ((modulusPicardZeroPresheaf c i).map_comp s r) x

/-- Forgetting the group law recovers precisely the existing modulus zero presheaf. -/
theorem modulusPicardZeroGroupPresheaf_forget :
    modulusPicardZeroGroupPresheaf c i ⋙ forget CommGrpCat =
      modulusPicardZeroPresheaf c i := rfl

end AlgebraicGeometry.GeneralizedJacobian
