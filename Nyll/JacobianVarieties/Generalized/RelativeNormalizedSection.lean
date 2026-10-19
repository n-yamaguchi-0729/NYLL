/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.NormalizedSectionLift
import Nyll.AlgebraicCurves.Cohomology.Cech.Comparison.FiniteModules
import Nyll.AlgebraicCurves.Cohomology.Cech.Comparison.FiniteToOrderedAffineCoverIff
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChart.TwoAffineCoverCechSectionsOfBaseChangeEquiv
import Nyll.AlgebraicCurves.Geometry.Schemes.Cohomology.TwoAffineCoverSubsingletonH1SectionsOfField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Actual normalized sections over a noetherian affine base

Proper cohomological finiteness and fibrewise vanishing kill the Cech
obstruction over the entire base. The resulting section restricts to the
specified frame on the whole Cartier modulus, including its nilpotents.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of R)) [IsProper c] (𝒱 : X.TwoAffineOpenCover)
  (I : X.IdealSheafData) (hI : I.IsInvertible)
  (M : RigidifiedLineBundle I.subschemeι)

include hI in
/-- Fibrewise vanishing of the actual restriction kernel produces a normalized family section. -/
theorem exists_normalizedSection_of_fibre_H1
    (hfib : ∀ (k : Type u) [Field k] [Algebra R k],
      Subsingleton ((𝒱.pullback c k).sectionsOf
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))
        ((Scheme.Modules.pullback
          (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R k))).obj
            (M.L ⊗ I.module))).H1) :
    ∃ s : 𝟙_ X.Modules ⟶ M.L,
      pullbackSection I.subschemeι s ≫ M.trivialization.hom =
        𝟙 (𝟙_ I.subscheme.Modules) := by
  let F := M.L ⊗ I.module
  have hF : IsInvertible F := M.isInvertible.tensor hI.isInvertible_module
  have hfin := (OModulePresheaf.cechFinite_toOrderedAffineCover_iff
    (OModulePresheaf.ofModules c F) 𝒱).mp
      (OModulePresheaf.cechFinite_ofModules_of_locallyTrivial c F
        hF.exists_trivialization 𝒱.toOrderedAffineCover)
  have hvan : Subsingleton (𝒱.sectionsOf c F).H1 :=
    Scheme.TwoAffineOpenCover.subsingleton_H1_sectionsOf_of_forall_field
      c 𝒱 F hF.exists_trivialization hfin.2 hfib
  exact exists_normalizedSection_of_H1 c 𝒱 I hI M

include hI in
/-- Geometric field fibres already suffice for a section on the entire noetherian affine base. -/
theorem exists_normalizedSection_of_geometric_H1
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k] [Algebra R k],
      Subsingleton ((𝒱.pullback c k).sectionsOf
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))
        ((Scheme.Modules.pullback
          (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R k))).obj
            (M.L ⊗ I.module))).H1) :
    ∃ s : 𝟙_ X.Modules ⟶ M.L,
      pullbackSection I.subschemeι s ≫ M.trivialization.hom =
        𝟙 (𝟙_ I.subscheme.Modules) := by
  apply exists_normalizedSection_of_fibre_H1 c 𝒱 I hI M
  intro k _ _
  let F := M.L ⊗ I.module
  have hF : IsInvertible F := M.isInvertible.tensor hI.isInvertible_module
  let A := AlgebraicClosure k
  obtain ⟨⟨eA⟩, _, _⟩ :=
    Scheme.TwoAffineOpenCover.exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial
      𝒱 c F hF.exists_trivialization A
  have : Subsingleton ((𝒱.pullback c A).sectionsOf
      (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
      ((Scheme.Modules.pullback
        (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj F)).H1 := hfib A
  have : Subsingleton (A ⊗[R] (𝒱.sectionsOf c F).H1) := eA.symm.toEquiv.subsingleton
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange R k A A
    (𝒱.sectionsOf c F).H1
  have : Subsingleton (A ⊗[k] (k ⊗[R] (𝒱.sectionsOf c F).H1)) := e.toEquiv.subsingleton
  have : Subsingleton (k ⊗[R] (𝒱.sectionsOf c F).H1) :=
    (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right k A).mp inferInstance
  obtain ⟨⟨ek⟩, _, _⟩ :=
    Scheme.TwoAffineOpenCover.exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial
      𝒱 c F hF.exists_trivialization k
  exact ek.toEquiv.subsingleton

include hI in
/-- Relative Riemann--Roch lifts the frame when every geometric kernel has large degree. -/
theorem exists_normalizedSection_of_geometric_eulerChar_bound
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (hbound : ∀ (k : Type u) [Field k] [IsAlgClosed k] [Algebra R k],
      let f := pullback.fst c (Scheme.TwoAffineOpenCover.specMap R k)
      let π := pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k)
      let 𝒲 := 𝒱.pullback c k
      let F := (Scheme.Modules.pullback f).obj (M.L ⊗ I.module)
      2 * (Module.finrank k (𝒲.sectionsOf π (𝟙_ _)).H1 : ℤ) - 1 ≤
        ((Module.finrank k (𝒲.sectionsOf π F).H0 : ℤ) -
          Module.finrank k (𝒲.sectionsOf π F).H1) -
        ((Module.finrank k (𝒲.sectionsOf π (𝟙_ _)).H0 : ℤ) -
          Module.finrank k (𝒲.sectionsOf π (𝟙_ _)).H1)) :
    ∃ s : 𝟙_ X.Modules ⟶ M.L,
      pullbackSection I.subschemeι s ≫ M.trivialization.hom =
        𝟙 (𝟙_ I.subscheme.Modules) := by
  apply exists_normalizedSection_of_geometric_H1 c 𝒱 I hI M
  intro k _ _ _
  let σ := Scheme.TwoAffineOpenCover.specMap R k
  let f := pullback.fst c σ
  let π := pullback.snd c σ
  have : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (g : X ⟶ Y) => SmoothOfRelativeDimension 1 g) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  have : SmoothOfRelativeDimension 1 π :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {X Y : Scheme.{u}} (g : X ⟶ Y) => SmoothOfRelativeDimension 1 g)
      (IsPullback.of_hasPullback c σ) inferInstance
  have : IsIntegral (Limits.pullback c σ) :=
    GeometricallyIntegral.geometrically_isIntegral σ f π (IsPullback.of_hasPullback c σ)
  exact IsInvertible.subsingleton_H1_sectionsOf_of_le_eulerChar_sub k π
    ((Scheme.Modules.pullback f).obj (M.L ⊗ I.module))
    ((M.isInvertible.tensor hI.isInvertible_module).pullback f) (𝒱.pullback c k) (hbound k)

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
