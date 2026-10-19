/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Functoriality.DirectImageAlgebra
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeOfFiniteSections
import Nyll.SchemeTheory.Modules.Quasicoherent.DirectImageAlgebraQuasicoherent
import Nyll.SchemeTheory.Modules.Sections.AffineEpi
import Nyll.SchemeTheory.Modules.Sections.ImageSections
import Nyll.SchemeTheory.Modules.Sections.InverseLimit
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-!
# The actual image sheaf of a direct-image structure map

The original scheme morphism defines a morphism from the unit module
to its actual direct-image algebra. Its abelian image is a native
module sheaf. For an affine morphism, that sheaf is quasicoherent and
of finite type, and its affine sections are the image of the original
map on regular functions.

This construction supplies the native finite-type sheaf associated
with the Rees image in the formal algebraization argument.
-/

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.DirectImageAlgebra

universe u

variable {T X : Scheme.{u}} (g : T ⟶ X)

private theorem epi_factorThruImage {M N : X.Modules} (φ : M ⟶ N) :
    Epi (Abelian.factorThruImage φ) := inferInstance

/-- The unit-to-algebra map is the original map on regular functions. -/
def unitMap : Modules.Hom (X := X) (SheafOfModules.unit X.ringCatSheaf)
    (RelativeSpec.underlyingModule (structureMap g)) := by
  let φ (U : X.Opensᵒᵖ) :
      (SheafOfModules.unit X.ringCatSheaf).val.obj U ⟶
        (RelativeSpec.underlyingModule (structureMap g)).val.obj U :=
    ModuleCat.ofHom
      (X := (SheafOfModules.unit X.ringCatSheaf).val.obj U)
      (Y := (RelativeSpec.underlyingModule (structureMap g)).val.obj U)
      { toFun := fun a => g.app U.unop a
        map_add' := fun a b => (g.app U.unop).hom.map_add a b
        map_smul' := fun a b => (g.app U.unop).hom.map_mul a b }
  refine ⟨{ app := φ, naturality := ?_ }⟩
  intro U V i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun ψ : Γ(X, U.unop) ⟶ Γ(T, g ⁻¹ᵁ V.unop) => ψ x)
    (g.c.naturality i)

/-- The constructed unit map retains the original scheme section map. -/
theorem unitMap_app_apply (U : X.Opens) (a : Γ(X, U)) :
    (unitMap g).app U a = g.app U a := rfl

/-- The native image sheaf of the original structural map. -/
def imageModule : X.Modules := Abelian.image (C := X.Modules) (unitMap g)

/-- The original inclusion of the image into the direct-image algebra. -/
def imageModuleInclusion : imageModule g ⟶
    RelativeSpec.underlyingModule (structureMap g) :=
  Abelian.image.ι (C := X.Modules) (unitMap g)

/-- The original corestriction of the structural map to its image. -/
def imageModuleProjection : Modules.Hom (X := X) (SheafOfModules.unit X.ringCatSheaf)
    (imageModule g) := Abelian.factorThruImage (C := X.Modules) (unitMap g)

/-- The factorization retains the original structural map on each section. -/
theorem imageModule_factorization (U : X.Opens) (a : Γ(X, U)) :
    (imageModuleInclusion g).app U ((imageModuleProjection g).app U a) = g.app U a :=
  congrArg
    (fun ψ : Modules.Hom (X := X) (SheafOfModules.unit X.ringCatSheaf)
      (RelativeSpec.underlyingModule (structureMap g)) => ψ.app U a)
    (Abelian.image.fac (C := X.Modules) (unitMap g))

variable [IsAffineHom g]

/-- The actual image of the affine direct-image structural map is quasicoherent. -/
theorem isQuasicoherent_imageModule : (imageModule g).IsQuasicoherent := by
  have : (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsQuasicoherent :=
    Modules.isQuasicoherent_unit X
  have : (RelativeSpec.underlyingModule (structureMap g)).IsQuasicoherent :=
    isQuasicoherent_underlyingModule g
  exact Modules.isQuasicoherent_abelianImage (unitMap g)

/-- The actual image sheaf is of finite type, as proved by its original
affine section generators coming from the unit sheaf. -/
theorem isFiniteType_imageModule : (imageModule g).IsFiniteType := by
  have : (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsQuasicoherent :=
    Modules.isQuasicoherent_unit X
  have : (imageModule g).IsQuasicoherent := isQuasicoherent_imageModule g
  apply Modules.isFiniteType_of_finite_affine_sections (imageModule g)
  intro U hU
  let Q := Modules.moduleSectionsFunctor U
  let p := (Q.map (imageModuleProjection g)).hom
  have : Module.Finite Γ(X, U)
      (Q.obj (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :=
    inferInstanceAs (Module.Finite Γ(X, U) Γ(X, U))
  have hp : Epi (C := X.Modules) (imageModuleProjection g) :=
    epi_factorThruImage (unitMap g)
  exact Module.Finite.of_surjective p
    (Modules.Hom.app_surjective_of_epi_of_isAffineOpen (imageModuleProjection g) U hU)

/-- Every affine section of the native image sheaf comes from an actual
regular function on that affine open. -/
theorem imageModuleProjection_app_surjective (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective ((imageModuleProjection g).app U) := by
  have : (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsQuasicoherent :=
    Modules.isQuasicoherent_unit X
  have : (imageModule g).IsQuasicoherent := isQuasicoherent_imageModule g
  have hp : Epi (C := X.Modules) (imageModuleProjection g) :=
    epi_factorThruImage (unitMap g)
  exact Modules.Hom.app_surjective_of_epi_of_isAffineOpen (imageModuleProjection g) U hU

end AlgebraicGeometry.Scheme.DirectImageAlgebra
