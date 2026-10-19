/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Picard.GroupLaw.RelativeGroupLaw
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Relative point laws of actual commutative group schemes

The operations are transported from the existing group object. The additive
point evaluator identifies the relative-law coordinates with the same actual
point group, so regular divisor sums can target any commutative group scheme.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory NeronModelInfra
open scoped CategoryTheory.MonObj

namespace GoodReductionJacobian

variable {R : Type u} [CommRing R]
  (G : CommGrp (Over (Spec (CommRingCat.of R))))

/-- Relative scheme maps and actual points of the given group object. -/
def commGroupPointEquiv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    SchemeHomOver t G.X.hom ≃ (Over.mk t ⟶ G.X) where
  toFun x := Over.homMk x.1 x.2
  invFun x := ⟨x.left, Over.w x⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Composition of relative scheme maps gives composition in the original over category. -/
theorem commGroupPointEquiv_comp {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t' t) (q : SchemeHomOver t G.X.hom) :
    commGroupPointEquiv G t' (NeronModelInfra.schemeHomOverComp x q) =
      (Over.homMk x.1 x.2 : Over.mk t' ⟶ Over.mk t) ≫ commGroupPointEquiv G t q := rfl

private theorem commGroupPointEquiv_natural {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (f : T' ⟶ T) (hf : f ≫ t = t') (x : SchemeHomOver t G.X.hom) :
    commGroupPointEquiv G t' (schemeHomOverComp f hf x) =
      (Over.homMk f hf : Over.mk t' ⟶ Over.mk t) ≫ commGroupPointEquiv G t x :=
  commGroupPointEquiv_comp G t t' ⟨f, hf⟩ x

/-- The natural relative group law carried by an actual commutative group scheme. -/
def commGroupRelativeLaw : RelativeGroupLaw R G.X.hom where
  mul t x y := (commGroupPointEquiv G t).symm
    (commGroupPointEquiv G t x * commGroupPointEquiv G t y)
  one t := (commGroupPointEquiv G t).symm 1
  inv t x := (commGroupPointEquiv G t).symm ((commGroupPointEquiv G t x)⁻¹)
  mul_assoc t x y z := by
    apply (commGroupPointEquiv G t).injective
    simp only [Equiv.apply_symm_apply]
    exact mul_assoc _ _ _
  one_mul t x := by
    apply (commGroupPointEquiv G t).injective
    simp only [Equiv.apply_symm_apply, one_mul]
  mul_one t x := by
    apply (commGroupPointEquiv G t).injective
    simp only [Equiv.apply_symm_apply, mul_one]
  inv_mul_cancel t x := by
    apply (commGroupPointEquiv G t).injective
    simp only [Equiv.apply_symm_apply, inv_mul_cancel]
  mul_natural t t' f hf x y := by
    apply (commGroupPointEquiv G t').injective
    rw [commGroupPointEquiv_natural]
    simp only [Equiv.apply_symm_apply, commGroupPointEquiv_natural]
    exact MonObj.comp_mul _ _ _

/-- The relative point law retains commutativity of the original group scheme. -/
theorem commGroupRelativeLaw_isCommutative : (commGroupRelativeLaw G).IsCommutative := by
  intro T t x y
  apply (commGroupPointEquiv G t).injective
  simp only [commGroupRelativeLaw, Equiv.apply_symm_apply]
  exact mul_comm _ _

/-- The additive evaluator uses the actual point group of the original scheme. -/
def commGroupPointValue {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t G.X.hom) : Additive (Over.mk t ⟶ G.X) :=
  Additive.ofMul (commGroupPointEquiv G t x)

/-- Actual additive point coordinates detect relative points. -/
theorem commGroupPointValue_injective {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Function.Injective (commGroupPointValue G t) :=
  (Additive.ofMul : (Over.mk t ⟶ G.X) ≃ Additive (Over.mk t ⟶ G.X)).injective.comp
    (commGroupPointEquiv G t).injective

/-- The identity of the relative law evaluates to zero in the actual point group. -/
theorem commGroupPointValue_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    commGroupPointValue G t ((commGroupRelativeLaw G).one t) = 0 := by
  change Additive.ofMul ((commGroupPointEquiv G t) ((commGroupPointEquiv G t).symm 1)) = 0
  rw [Equiv.apply_symm_apply]
  rfl

/-- Relative multiplication evaluates to addition in the actual point group. -/
theorem commGroupPointValue_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t G.X.hom) :
    commGroupPointValue G t ((commGroupRelativeLaw G).mul t x y) =
      commGroupPointValue G t x + commGroupPointValue G t y := by
  change Additive.ofMul ((commGroupPointEquiv G t) ((commGroupPointEquiv G t).symm _)) = _
  rw [Equiv.apply_symm_apply]
  rfl

end GoodReductionJacobian
