/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.ExtCompEq
import Nyll.SchemeTheory.GroupSchemes.GeometricPointHom

/-! # Actual group homomorphisms detected on algebraically closed ground-field points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupSchemes

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X Y : Over (Spec (CommRingCat.of K))}

/-- The ground-field version for reduced schemes locally of finite type. -/
theorem hom_ext_algebraicallyClosedPoints [LocallyOfFiniteType X.hom]
    [IsReduced X.left] [IsSeparated Y.hom] (f g : X ⟶ Y)
    (h : ∀ p : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ X, p ≫ f = p ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  apply ext_of_forall_comp_eq_of_isAlgClosed X.hom Y.hom (Over.w f) (Over.w g)
  intro p hp
  exact congrArg Over.Hom.left (h (Over.homMk p hp))

variable (G H : CommGrp (Over (Spec (CommRingCat.of K))))

/-- Actual regular group-law compatibility follows from the products of K-points,
when K is algebraically closed and the source product is reduced and locally finite type. -/
theorem isMonHom_of_algebraicallyClosedPoints
    [LocallyOfFiniteType (G.X ⊗ G.X).hom] [IsReduced (G.X ⊗ G.X).left]
    [IsSeparated H.X.hom] (f : G.X ⟶ H.X)
    (hmul : ∀ x y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X,
      (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f := by
  have hone : (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) ≫ f = 1 := by
    have h := hmul 1 1
    rw [one_mul] at h
    exact (mul_left_cancel (show
      ((1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) ≫ f) * 1 =
        ((1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) ≫ f) *
          ((1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) ≫ f) from
            (mul_one _).trans h)).symm
  constructor
  · change (1 : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X) ≫ f = 1 at hone
    simpa only [Hom.one_def, toUnit_unit, Category.id_comp] using hone
  · apply hom_ext_algebraicallyClosedPoints
    intro p
    have h := hmul (p ≫ fst G.X G.X) (p ≫ snd G.X G.X)
    simp only [Hom.mul_def] at h
    rw [← lift_map (p ≫ fst G.X G.X) (p ≫ snd G.X G.X) f f,
      lift_comp_fst_snd] at h
    simpa only [Category.assoc] using h

/-- Bundle the same actual regular morphism as a group-scheme homomorphism. -/
def homOfAlgebraicallyClosedPoints
    [LocallyOfFiniteType (G.X ⊗ G.X).hom] [IsReduced (G.X ⊗ G.X).left]
    [IsSeparated H.X.hom] (f : G.X ⟶ H.X)
    (hmul : ∀ x y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X,
      (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : G ⟶ H := by
  have := isMonHom_of_algebraicallyClosedPoints G H f hmul
  exact InducedCategory.homMk (Grp.homMk f)

end AlgebraicGeometry.GroupSchemes
