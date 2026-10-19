/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafHom
import Nyll.SchemeTheory.Modules.Sections.SectionsAlgebra
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentAffineLocalization
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeAffineSections
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# The actual section presheaf of a native module sheaf

A native module sheaf supplies an `OModulePresheaf` through its original
section modules and restriction maps. The base action is restriction of
scalars along the given structural morphism. The structural sheaf action
is retained, including its compatibility with the base action.

Native morphisms give the same maps of sections in the Čech input category.
Native quasicoherence supplies the concrete basic-open localization
conditions. Native quasicoherence and finite type supply finite sections
on every affine open, hence the existing Čech coherence condition.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R))

/-- The actual section module, restricted along the original structural
coefficient homomorphism. This fixes the base action once. -/
def sectionModuleOverBase (M : X.Modules) (U : X.Opens) : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars (f.constToPresheaf.app (op U)).hom).obj
    (M.val.obj (op U))

/-- Restriction of the original sections is linear for the original
base action, by naturality of the structural coefficient map. -/
def sectionRestrictionOverBase (M : X.Modules) {U V : X.Opens} (h : U ≤ V) :
    sectionModuleOverBase f M V →ₗ[R] sectionModuleOverBase f M U where
  toFun := fun x => (M.presheaf.map (homOfLE h).op).hom (show Γ(M, V) from x)
  map_add' := fun x y => (M.presheaf.map (homOfLE h).op).hom.map_add
    (show Γ(M, V) from x) (show Γ(M, V) from y)
  map_smul' := by
    intro a x
    let y : Γ(M, V) := x
    change M.presheaf.map (homOfLE h).op ((f.constToPresheaf.app (op V)).hom a • y) =
      (f.constToPresheaf.app (op U)).hom a • M.presheaf.map (homOfLE h).op y
    rw [M.map_smul]
    have hcoef : X.presheaf.map (homOfLE h).op ((f.constToPresheaf.app (op V)).hom a) =
        (f.constToPresheaf.app (op U)).hom a :=
      (congrArg (fun k : CommRingCat.of R ⟶ Γ(X, U) => k a)
        (f.constToPresheaf.naturality (homOfLE h).op)).symm
    exact congrArg (fun b : Γ(X, U) => b • M.presheaf.map (homOfLE h).op y) hcoef

/-- The original native restrictions, with their structural actions,
form the actual presheaf used by the existing Čech constructions. -/
def toOModulePresheaf (M : X.Modules) : OModulePresheaf f where
  obj U := sectionModuleOverBase f M U
  addCommGroup U := inferInstance
  module U := inferInstance
  moduleSections U := inferInstanceAs (Module Γ(X, U) Γ(M, U))
  isScalarTower U := by
    let : Algebra R Γ(X, U) := Scheme.TwoAffineOpenCover.algebraOfHom f U
    exact IsScalarTower.of_compHom R Γ(X, U) Γ(M, U)
  res h := sectionRestrictionOverBase f M h
  res_smul h a x := M.map_smul (homOfLE h) a x
  res_refl U := by
    apply LinearMap.ext
    intro x
    change M.presheaf.map (𝟙 (op U)) x = x
    exact congrArg (fun k : Γ(M, U) ⟶ Γ(M, U) => k x) (M.presheaf.map_id (op U))
  res_comp {U V W} h h' := by
    apply LinearMap.ext
    intro x
    change M.presheaf.map ((homOfLE h').op ≫ (homOfLE h).op) x =
      M.presheaf.map (homOfLE h).op (M.presheaf.map (homOfLE h').op x)
    exact congrArg (fun k : Γ(M, W) ⟶ Γ(M, U) => k x)
      (M.presheaf.map_comp (homOfLE h').op (homOfLE h).op)

/-- The Čech restriction acts on the literal original section. -/
theorem toOModulePresheaf_res_apply (M : X.Modules) {U V : X.Opens}
    (h : U ≤ V) (x : Γ(M, V)) :
    (toOModulePresheaf f M).res h x = M.presheaf.map (homOfLE h).op x := rfl

/-- A native sheaf morphism gives its original section maps in the Čech
presheaf category, with both base and structural scalar compatibility. -/
def toOModulePresheafHom {M N : X.Modules} (φ : M ⟶ N) :
    OModulePresheaf.Hom (toOModulePresheaf f M) (toOModulePresheaf f N) where
  app U :=
    { toFun := fun x => (φ.app U).hom (show Γ(M, U) from x)
      map_add' := fun x y => (φ.app U).hom.map_add
        (show Γ(M, U) from x) (show Γ(M, U) from y)
      map_smul' := by
        intro a x
        let y : Γ(M, U) := x
        change φ.app U ((f.constToPresheaf.app (op U)).hom a • y) =
          (f.constToPresheaf.app (op U)).hom a • φ.app U y
        exact φ.app_smul ((f.constToPresheaf.app (op U)).hom a) y }
  app_smul U a x := φ.app_smul a x
  naturality {U V} h := by
    apply LinearMap.ext
    intro x
    exact congrArg (fun k : Γ(M, V) ⟶ Γ(N, U) => k x)
      (φ.mapPresheaf.naturality (homOfLE h).op)

/-- The conversion of a morphism retains its exact original component. -/
theorem toOModulePresheafHom_app_apply {M N : X.Modules} (φ : M ⟶ N)
    (U : X.Opens) (x : Γ(M, U)) :
    (toOModulePresheafHom f φ).app U x = φ.app U x := rfl

/-- Native quasicoherence supplies the localization conditions of the
actual section presheaf, without introducing an independent presentation. -/
theorem toOModulePresheaf_isQuasicoherent (M : X.Modules) [M.IsQuasicoherent] :
    (toOModulePresheaf f M).IsQuasicoherent := by
  intro U a
  exact basicOpenLocalization_of_isQuasicoherent M U a

/-- A native finite-type quasicoherent sheaf has precisely the affine
section finiteness required by the existing Čech coherence notion. -/
theorem toOModulePresheaf_isCoherent (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] : (toOModulePresheaf f M).IsCoherent := by
  intro U
  exact moduleFinite_sections_of_isFiniteType M U.1 U.2

end AlgebraicGeometry.Scheme.Modules
