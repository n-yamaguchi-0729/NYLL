/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.GeneralGroupLocalSymbolExistence
import Nyll.AlgebraicCurves.Divisors.Modulus.ModulusFunctoriality
import Nyll.AlgebraicCurves.Divisors.Principal.PrincipalEvaluation
import Nyll.AlgebraicCurves.Models.Charts.OpenPointValues
import Nyll.AlgebraicCurves.Models.FunctionFields.CurveRingEquivFunctionField
import Nyll.SchemeTheory.GroupSchemes.AbelianScheme
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

/-! # The conductor of an actual product-valued map

The actual maps supply their least full conductors. The conductor of their
product is the coefficientwise supremum, so a pole in one coordinate cannot
be cancelled by the other coordinate.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj CategoryTheory.Obj BigOperators

namespace AlgebraicGeometry.GeneralizedJacobian

private theorem regularMapValues_product_hasModulus_iff
    {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [HasPrincipalDivisors K F] (M : CurveModel K F) (U : M.C.Opens)
    (G H : CommGrp (Over (Spec (.of K))))
    (q : Over.mk (U.ι ≫ M.toBase) ⟶ (GroupSchemes.product G H).X)
    (D : Modulus K F) :
    D.HasModulus (M.regularMapValues U (GroupSchemes.product G H)
      ((commGroupPointEquiv (GroupSchemes.product G H) _).symm q)) ↔
      D.HasModulus (M.regularMapValues U G
        ((commGroupPointEquiv G _).symm (q ≫ fst G.X H.X))) ∧
      D.HasModulus (M.regularMapValues U H
        ((commGroupPointEquiv H _).symm (q ≫ snd G.X H.X))) := by
  have hfst : IsMonHom (fst G.X H.X) := inferInstance
  have hsnd : IsMonHom (snd G.X H.X) := inferInstance
  let P := GroupSchemes.product G H
  let π₁ : P ⟶ G := InducedCategory.homMk
    (Grp.homMk' { hom := fst G.X H.X, isMonHom_hom := hfst })
  let π₂ : P ⟶ H := InducedCategory.homMk
    (Grp.homMk' { hom := snd G.X H.X, isMonHom_hom := hsnd })
  have hπ₁ : π₁.hom.hom.hom = (show P.X ⟶ G.X from fst G.X H.X) := rfl
  have hπ₂ : π₂.hom.hom.hom = (show P.X ⟶ H.X from snd G.X H.X) := rfl
  let A := Additive (Over.mk (𝟙 (Spec (.of K))) ⟶ P.X)
  let a : Place K F → A :=
    M.regularMapValues U P ((commGroupPointEquiv P _).symm q)
  let b := M.regularMapValues U G ((commGroupPointEquiv G _).symm (q ≫ fst G.X H.X))
  let d := M.regularMapValues U H ((commGroupPointEquiv H _).symm (q ≫ snd G.X H.X))
  let f := (IsMonHom.monoidHom π₁.hom.hom.hom
    (Over.mk (𝟙 (Spec (.of K))))).toAdditive
  let g := (IsMonHom.monoidHom π₂.hom.hom.hom
    (Over.mk (𝟙 (Spec (.of K))))).toAdditive
  have hpoint := (commGroupPointEquiv P (U.ι ≫ M.toBase)).apply_symm_apply q
  have hf (w : Place K F) : f (a w) = b w := by
    have he := (M.regularMapValues_comp U P G
      ((commGroupPointEquiv P _).symm q) π₁ w).symm
    have hcomp := (congrArg
      (fun z : Over.mk (U.ι ≫ M.toBase) ⟶ P.X => z ≫ π₁.hom.hom.hom) hpoint).trans
        (congrArg (fun z : P.X ⟶ G.X => q ≫ z) hπ₁)
    exact he.trans (congrArg
      (fun z : Over.mk (U.ι ≫ M.toBase) ⟶ G.X =>
        M.regularMapValues U G ((commGroupPointEquiv G _).symm z) w) hcomp)
  have hg (w : Place K F) : g (a w) = d w := by
    have he := (M.regularMapValues_comp U P H
      ((commGroupPointEquiv P _).symm q) π₂ w).symm
    have hcomp := (congrArg
      (fun z : Over.mk (U.ι ≫ M.toBase) ⟶ P.X => z ≫ π₂.hom.hom.hom) hpoint).trans
        (congrArg (fun z : P.X ⟶ H.X => q ≫ z) hπ₂)
    exact he.trans (congrArg
      (fun z : Over.mk (U.ι ≫ M.toBase) ⟶ H.X =>
        M.regularMapValues U H ((commGroupPointEquiv H _).symm z) w) hcomp)
  change D.HasModulus a ↔ D.HasModulus b ∧ D.HasModulus d
  constructor
  · intro ha
    exact ⟨by simpa only [hf] using ha.map f, by simpa only [hg] using ha.map g⟩
  · rintro ⟨hb, hd⟩ r hr
    have hf0 : f (∑ᶠ w : Place K F, w.ord (r : F) • a w) = 0 := by
      rw [f.map_finsum (principalEvaluation_finiteSupport a r)]
      simpa only [map_zsmul, hf] using hb r hr
    have hg0 : g (∑ᶠ w : Place K F, w.ord (r : F) • a w) = 0 := by
      rw [g.map_finsum (principalEvaluation_finiteSupport a r)]
      simpa only [map_zsmul, hg] using hd r hr
    apply Additive.toMul.injective
    exact CartesianMonoidalCategory.hom_ext (X := G.X) (Y := H.X)
      (show Over.mk (𝟙 (Spec (.of K))) ⟶ G.X ⊗ H.X from
        Additive.toMul (∑ᶠ w : Place K F, w.ord (r : F) • a w))
      (show Over.mk (𝟙 (Spec (.of K))) ⟶ G.X ⊗ H.X from Additive.toMul (0 : A))
      (congrArg Additive.toMul (hf0.trans (map_zero f).symm))
      (congrArg Additive.toMul (hg0.trans (map_zero g).symm))

/-- Two actual regular maps construct least conductors for each coordinate and
for their actual product map. The product conductor is exactly the
coefficientwise supremum of the coordinate conductors. -/
theorem exists_group_regularMap_product_conductors
    {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    (U : C.Opens) (hU : (U : Set C).Nonempty)
    (G H : CommGrp (Over (Spec (.of K))))
    [IsSeparated G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsSeparated H.X.hom] [LocallyOfFiniteType H.X.hom]
    (q : Over.mk (U.ι ≫ c) ⟶ G.X) (r : Over.mk (U.ι ≫ c) ⟶ H.X) :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    let M := CurveModel.ofSmoothProperCurve c
    let _ : IsCurveOver K C.functionField :=
      isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
        c (RingEquiv.refl _) (fun _ => rfl)
    let a := M.regularMapValues U G ((commGroupPointEquiv G _).symm q)
    let b := M.regularMapValues U H ((commGroupPointEquiv H _).symm r)
    let ab := M.regularMapValues U (GroupSchemes.product G H)
      ((commGroupPointEquiv (GroupSchemes.product G H) _).symm (lift q r))
    ∃ D₁ D₂ D : Modulus K C.functionField,
      (∀ E : Modulus K C.functionField, E.HasModulus a ↔ D₁ ≤ E) ∧
      (∀ E : Modulus K C.functionField, E.HasModulus b ↔ D₂ ≤ E) ∧
      (∀ E : Modulus K C.functionField, E.HasModulus ab ↔ D ≤ E) ∧ D = D₁ ⊔ D₂ := by
  intro algC M curveC a b ab
  obtain ⟨D₁, hD₁, _⟩ := existsUnique_group_regularMap_modulus_classification
    c U hU G ((commGroupPointEquiv G _).symm q)
  obtain ⟨D₂, hD₂, _⟩ := existsUnique_group_regularMap_modulus_classification
    c U hU H ((commGroupPointEquiv H _).symm r)
  have hfstValues :
      M.regularMapValues U G
        ((commGroupPointEquiv G _).symm (lift q r ≫ fst G.X H.X)) = a :=
    congrArg (fun z : Over.mk (U.ι ≫ c) ⟶ G.X =>
      M.regularMapValues U G ((commGroupPointEquiv G _).symm z)) (lift_fst q r)
  have hsndValues :
      M.regularMapValues U H
        ((commGroupPointEquiv H _).symm (lift q r ≫ snd G.X H.X)) = b :=
    congrArg (fun z : Over.mk (U.ι ≫ c) ⟶ H.X =>
      M.regularMapValues U H ((commGroupPointEquiv H _).symm z)) (lift_snd q r)
  have hprod (E : Modulus K C.functionField) :
      E.HasModulus ab ↔ E.HasModulus a ∧ E.HasModulus b :=
    (regularMapValues_product_hasModulus_iff M U G H (lift q r) E).trans
      (and_congr (Iff.of_eq (congrArg E.HasModulus hfstValues))
        (Iff.of_eq (congrArg E.HasModulus hsndValues)))
  refine ⟨D₁, D₂, D₁ ⊔ D₂, hD₁.1, hD₂.1, ?_, rfl⟩
  intro E
  exact (hprod E).trans ((and_congr (hD₁.1 E) (hD₂.1 E)).trans sup_le_iff.symm)

end AlgebraicGeometry.GeneralizedJacobian
