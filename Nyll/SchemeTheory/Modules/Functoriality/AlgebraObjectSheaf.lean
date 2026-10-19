/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Functoriality.AlgebraObjectSections
import Nyll.SchemeTheory.Modules.Functoriality.FiniteRelativeSpec
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeAffineSections
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeLocality
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.Forget

/-!
# The actual algebra sheaf of a commutative module-algebra object

The section rings and original restrictions form a sheaf of commutative
rings because their underlying presheaf of types is the original module
presheaf. The original unit gives the structure morphism. Its underlying
module is isomorphic to the original module by identity additive maps;
linearity is the proved compatibility between structural coefficients and
the original scalar action. Quasicoherence and finite type consequently
give the actual finite relative spectrum without a separate sheaf model.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Modules.AlgebraObject

variable {X : Scheme.{u}} (F : X.Modules) [MonObj F] [IsCommMonObj F]

/-- The ring presheaf retains the original section types and restriction functions. -/
def ringPresheaf : TopCat.Presheaf CommRingCat.{u} X where
  obj U := sectionRing F U.unop
  map {U V} i := ConcreteCategory.ofHom (C := CommRingCat)
    (X := sectionRing F U.unop) (Y := sectionRing F V.unop) (restriction F i.unop)
  map_id U := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact congrArg (fun k : F.presheaf.obj U ⟶ F.presheaf.obj U => k x)
      (F.presheaf.map_id U)
  map_comp {U V W} i j := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact congrArg (fun k : F.presheaf.obj U ⟶ F.presheaf.obj W => k x)
      (F.presheaf.map_comp i j)

private theorem ringPresheaf_isSheaf : (ringPresheaf F).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
    (CategoryTheory.forget CommRingCat.{u}) (ringPresheaf F)).mpr
  exact (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
    (CategoryTheory.forget AddCommGrpCat.{u}) F.presheaf).mp F.isSheaf

/-- The actual sheaf of commutative rings associated with the algebra object. -/
def sheaf : TopCat.Sheaf CommRingCat.{u} X :=
  ⟨ringPresheaf F, ringPresheaf_isSheaf F⟩

/-- The original algebra unit supplies the structure morphism on every open. -/
def structureMap : X.sheaf ⟶ sheaf F where
  hom :=
    { app := fun U => ConcreteCategory.ofHom (C := CommRingCat)
        (X := Γ(X, U.unop)) (Y := sectionRing F U.unop) (coefficientMap F U.unop)
      naturality := fun {U V} i => by
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro r
        exact (restriction_coefficientMap F i.unop r).symm }

private def underlyingSectionIso (U : X.Opensᵒᵖ) :
    (RelativeSpec.underlyingModule (structureMap F)).val.obj U ≅ F.val.obj U := by
  refine ModuleCat.isoMk (Iso.refl _) ?_
  intro r
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  exact (coefficientMap_mul F U.unop r x).symm

/-- The algebra sheaf recovers the original native module and its scalar action. -/
def underlyingModuleIso : RelativeSpec.underlyingModule (structureMap F) ≅ F := by
  apply (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso
  refine PresheafOfModules.isoMk (underlyingSectionIso F) ?_
  intro U V i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- Recovery is the identity on every original section. -/
theorem underlyingModuleIso_hom_app (U : X.Opens)
    (x : Γ(RelativeSpec.underlyingModule (structureMap F), U)) :
    (underlyingModuleIso F).hom.app U x = (show Γ(F, U) from x) := rfl

/-- The inverse recovery also retains every original section. -/
theorem underlyingModuleIso_inv_app (U : X.Opens) (x : Γ(F, U)) :
    (underlyingModuleIso F).inv.app U x =
      (show Γ(RelativeSpec.underlyingModule (structureMap F), U) from x) := rfl

/-- Native quasicoherence passes to the algebra sheaf through the actual module isomorphism. -/
instance underlyingModule_isQuasicoherent [F.IsQuasicoherent] :
    (RelativeSpec.underlyingModule (structureMap F)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (underlyingModuleIso F).symm inferInstance

/-- Native finite type passes through the same module isomorphism. -/
instance underlyingModule_isFiniteType [F.IsFiniteType] :
    (RelativeSpec.underlyingModule (structureMap F)).IsFiniteType :=
  SheafOfModules.IsFiniteType.of_iso (C := X.Opens) (R := X.ringCatSheaf)
    (M := F) (N := RelativeSpec.underlyingModule (structureMap F))
    (underlyingModuleIso F).symm inferInstance

/-- The actual relative spectrum of a finite-type quasicoherent algebra object is finite. -/
theorem isFinite_toBase [F.IsQuasicoherent] [F.IsFiniteType] :
    IsFinite (RelativeSpec.toBase (structureMap F)) := by
  apply RelativeSpec.isFinite_toBase (structureMap F)
  intro U
  exact moduleFinite_sections_of_isFiniteType
    (RelativeSpec.underlyingModule (structureMap F)) U.1 U.2

end AlgebraicGeometry.Scheme.Modules.AlgebraObject
