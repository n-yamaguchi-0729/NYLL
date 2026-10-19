/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionFieldNormalization
import Nyll.EtaleFundamentalGroups.FiniteEtale.GenericFiber.WholeFractionField
import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.Finite

/-!
# The actual generic fibre of an affine finite étale cover

The coordinate algebra of a finite étale cover of `Spec R` is given its
literal `R`-action through the canonical global-section comparison. For a
connected cover over a normal domain, its whole generic fibre is identified
with its original function field, over any compatible chosen fraction
field of `R`.

The construction retains the original structure morphism and the maps of
global sections. It is used to compare a normalized root extension with
the actual original cover, before extending the comparison over overlaps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory
open scoped TensorProduct

namespace EtaleFundamentalGroups

universe u

/-- The actual action of the affine base ring on the global sections of
a finite étale cover. -/
@[instance_reducible] def finiteEtaleAffineSectionAlgebra
    (R : CommRingCat.{u}) (Y : FiniteEtale (Spec R)) : Algebra R Γ(Y.left, ⊤) :=
  ((Y.hom : Y.left ⟶ Spec R).appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom).toAlgebra

/-- The literal coordinate algebra supplied by the original cover is
finite étale over the literal affine base ring. -/
theorem finiteEtaleAffineSections_finite_etale
    (R : CommRingCat.{u}) (Y : FiniteEtale (Spec R)) :
    let : Algebra R Γ(Y.left, ⊤) := finiteEtaleAffineSectionAlgebra R Y
    Module.Finite R Γ(Y.left, ⊤) ∧ Algebra.Etale R Γ(Y.left, ⊤) := by
  intro aRT
  let f : Y.left ⟶ Spec R := Y.hom
  have : IsFiniteEtale f := Y.prop
  have : IsAffine Y.left := isAffine_of_isAffineHom f
  let e : Γ(Spec R, ⊤) ≃+* R := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  have hFinite : RingHom.Finite (algebraMap R Γ(Y.left, ⊤)) :=
    RingHom.finite_respectsIso.2 f.appTop.hom e.symm f.finite_appTop
  have hEtale : RingHom.Etale (algebraMap R Γ(Y.left, ⊤)) :=
    RingHom.Etale.respectsIso.2 f.appTop.hom e.symm
      ((HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := f)).mp
        (inferInstance : Etale f))
  exact ⟨RingHom.finite_algebraMap.mp hFinite, RingHom.etale_algebraMap.mp hEtale⟩

/-- The actual affine section comparison is over the original base, with
the original cover morphism. -/
theorem finiteEtaleAffineSectionsIso_hom_base
    (R : CommRingCat.{u}) (Y : FiniteEtale (Spec R)) :
    let : Algebra R Γ(Y.left, ⊤) := finiteEtaleAffineSectionAlgebra R Y
    let : IsAffine Y.left :=
      isAffine_of_isAffineHom (X := Y.left) (Y := Spec R) Y.hom
    Y.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(Y.left, ⊤))) =
      Y.hom := by
  intro aRT hAffineY
  let f : Y.left ⟶ Spec R := Y.hom
  change Y.left.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appTop) = f
  rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality f,
    Category.assoc, ← Scheme.isoSpec_Spec_inv, Iso.hom_inv_id, Category.comp_id]

/-- The coefficient map to the actual function field agrees with the
map through the actual affine section algebra of the cover. -/
theorem finiteEtaleAffineSections_functionField_isScalarTower
    (R : CommRingCat.{u}) [IsDomain R] [IsIntegrallyClosed R]
    (Y : FiniteEtale (Spec R)) [IsConnected Y] :
    let : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let : Algebra R Γ(Y.left, ⊤) := finiteEtaleAffineSectionAlgebra R Y
    let : Algebra Γ(Y.left, ⊤) Y.left.functionField := topSectionFunctionFieldAlgebra Y.left
    let : Algebra R Y.left.functionField := finiteEtaleSpecFunctionFieldAlgebra R Y
    IsScalarTower R Γ(Y.left, ⊤) Y.left.functionField := by
  intro hIntegralY aRT aTL aRL
  let A := Γ(Spec R, ⊤)
  let T := Γ(Y.left, ⊤)
  let L := Y.left.functionField
  let : Algebra A T := Y.hom.appTop.hom.toAlgebra
  let : Algebra A L := finiteEtaleSectionFunctionFieldAlgebra Y
  have : IsScalarTower A T L := finiteEtale_sectionFunctionField_isScalarTower Y
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change algebraMap A L ((Scheme.ΓSpecIso R).inv r) =
    algebraMap T L (Y.hom.appTop ((Scheme.ΓSpecIso R).inv r))
  exact IsScalarTower.algebraMap_apply A T L _

/-- The whole generic fibre of the actual coordinate algebra is the
original function field of the connected cover, over a chosen compatible
fraction field of its affine base. -/
def finiteEtaleAffineGenericFiberAlgEquiv
    (R : CommRingCat.{u}) [IsDomain R] [IsIntegrallyClosed R]
    (Y : FiniteEtale (Spec R)) [IsConnected Y] :
    let : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let T := Γ(Y.left, ⊤)
    let : Algebra R T := finiteEtaleAffineSectionAlgebra R Y
    let : Algebra R Y.left.functionField := finiteEtaleSpecFunctionFieldAlgebra R Y
    ∀ (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
      [Algebra K Y.left.functionField] [IsScalarTower R K Y.left.functionField],
      let : Algebra K (T ⊗[R] K) := Algebra.TensorProduct.rightAlgebra
      T ⊗[R] K ≃ₐ[K] Y.left.functionField := by
  intro hIntegralY T aRT aRL K hFieldK aRK hFractionRK aKL hRKL aKG
  have : IsAffine Y.left :=
    isAffine_of_isAffineHom (X := Y.left) (Y := Spec R) Y.hom
  have : Nonempty (⊤ : Y.left.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty Y.left), trivial⟩⟩
  have : Module.Finite R T := (finiteEtaleAffineSections_finite_etale R Y).1
  have : Algebra.Etale R T := (finiteEtaleAffineSections_finite_etale R Y).2
  let L := Y.left.functionField
  let : Algebra T L := topSectionFunctionFieldAlgebra Y.left
  have : IsScalarTower R T L := finiteEtaleAffineSections_functionField_isScalarTower R Y
  have : IsFractionRing T L :=
    functionField_isFractionRing_of_isAffineOpen Y.left ⊤ (isAffineOpen_top Y.left)
  exact finiteEtaleGenericFiberFractionFieldEquiv R T K L

/-- The actual affine generic comparison sends a pure tensor to the
product of the original section germ and the chosen field scalar. -/
theorem finiteEtaleAffineGenericFiberAlgEquiv_tmul
    (R : CommRingCat.{u}) [IsDomain R] [IsIntegrallyClosed R]
    (Y : FiniteEtale (Spec R)) [IsConnected Y] :
    let : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let T := Γ(Y.left, ⊤)
    let : Algebra R T := finiteEtaleAffineSectionAlgebra R Y
    let : Algebra T Y.left.functionField := topSectionFunctionFieldAlgebra Y.left
    let : Algebra R Y.left.functionField := finiteEtaleSpecFunctionFieldAlgebra R Y
    ∀ (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
      [Algebra K Y.left.functionField] [IsScalarTower R K Y.left.functionField],
      let : Algebra K (T ⊗[R] K) := Algebra.TensorProduct.rightAlgebra
      ∀ (t : T) (k : K), finiteEtaleAffineGenericFiberAlgEquiv R Y K (t ⊗ₜ[R] k) =
        algebraMap T Y.left.functionField t * algebraMap K Y.left.functionField k := by
  intro hIntegralY T aRT aTL aRL K hFieldK aRK hFractionRK aKL hRKL aKG t k
  have : IsScalarTower R T Y.left.functionField :=
    finiteEtaleAffineSections_functionField_isScalarTower R Y
  exact finiteEtaleGenericFiberToFractionField_tmul t k

end EtaleFundamentalGroups
