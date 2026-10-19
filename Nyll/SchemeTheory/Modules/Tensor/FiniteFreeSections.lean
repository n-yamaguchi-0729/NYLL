/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentLocal
import Nyll.SchemeTheory.Modules.Sections.InverseLimit
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Actual sections of a finite free tensor product

Tensoring the actual free module sheaf by a module sheaf gives the finite
biproduct of copies of that sheaf. Evaluation preserves its product cone,
so its sections are the corresponding tuples of original sections.

The section comparison is linear over the structural coefficient ring
and commutes with the original restriction maps. No quasicoherence or
flatness hypothesis is needed.
-/

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] Abelian.hasFiniteBiproducts

variable {X : Scheme.{u}} (J : Type u) [Finite J]

/-- Tensor distributes over the actual finite free sheaf, with its
original coproduct, to give the finite biproduct of copies of `L`. -/
def finiteFreeTensorIsoBiproduct (L : X.Modules) :
    tensor (X := X) (show X.Modules from SheafOfModules.free J) L ≅
      ⨁ (fun _ : J => L) := by
  let E : X.Modules ≌ SheafOfModules.{u} X.ringCatSheaf := sheafOfModulesEquivalence X
  let T : SheafOfModules.{u} X.ringCatSheaf ⥤ X.Modules := E.inverse ⋙ tensorRight L
  let A : J → SheafOfModules.{u} X.ringCatSheaf :=
    fun _ => SheafOfModules.unit X.ringCatSheaf
  have : E.inverse.IsLeftAdjoint := E.symm.toAdjunction.isLeftAdjoint
  have : (tensorRight L).IsLeftAdjoint := inferInstance
  have : PreservesColimitsOfSize.{u, u} T := inferInstance
  have : T.PreservesZeroMorphisms := inferInstance
  have : PreservesBiproduct A T := preservesBiproduct_of_preservesCoproduct T
  exact T.mapIso (biproduct.isoCoproduct A).symm ≪≫ T.mapBiproduct A ≪≫
    biproduct.mapIso (fun _ : J => (λ_ L))

variable (A : J → X.Modules) (U : X.Opens)

private def biproductSectionsIsLimit : IsLimit
    (Fan.mk ((moduleSectionsFunctor U).obj (⨁ A))
      (fun j => (moduleSectionsFunctor U).map (biproduct.π A j))) := by
  let Q := moduleSectionsFunctor U
  have : PreservesLimit (Discrete.functor A) Q :=
    inferInstanceAs (PreservesLimit (Discrete.functor A)
      ((sheafOfModulesEquivalence X).functor ⋙
        SheafOfModules.evaluation X.ringCatSheaf (op U)))
  exact isLimitFanMkObjOfIsLimit Q A (biproduct.π A) (biproduct.isLimit A)

/-- Sections of the actual finite biproduct are tuples of the original
section modules, over the original ring of regular functions. -/
def biproductSectionsEquiv : Γ(⨁ A, U) ≃ₗ[Γ(X, U)] (∀ j : J, Γ(A j, U)) := by
  let Q := moduleSectionsFunctor U
  let e := (biproductSectionsIsLimit J A U).conePointUniqueUpToIso
    (ModuleCat.productConeIsLimit (fun j => Q.obj (A j)))
  exact e.toLinearEquiv

/-- Each coordinate of the section comparison is the original projection. -/
theorem biproductSectionsEquiv_apply (x : Γ(⨁ A, U)) (j : J) :
    biproductSectionsEquiv J A U x j = (biproduct.π A j).app U x := by
  let Q := moduleSectionsFunctor U
  have h := IsLimit.conePointUniqueUpToIso_hom_comp
    (biproductSectionsIsLimit J A U)
    (ModuleCat.productConeIsLimit (fun j => Q.obj (A j))) (Discrete.mk j)
  exact congrArg (fun a : Q.obj (⨁ A) ⟶ Q.obj (A j) => a.hom x) h

/-- The tuple comparison retains the original restriction on each component. -/
theorem biproductSectionsEquiv_restriction {V : X.Opens} (h : V ≤ U)
    (x : Γ(⨁ A, U)) (j : J) :
    biproductSectionsEquiv J A V ((⨁ A).presheaf.map (homOfLE h).op x) j =
      (A j).presheaf.map (homOfLE h).op (biproductSectionsEquiv J A U x j) := by
  rw [biproductSectionsEquiv_apply, biproductSectionsEquiv_apply]
  exact congrArg (fun a : Γ(⨁ A, U) ⟶ Γ(A j, V) => a.hom x)
    ((biproduct.π A j).mapPresheaf.naturality (homOfLE h).op)

variable {R : Type u} [CommRing R] (f : X ⟶ Spec (.of R)) (L : X.Modules)

/-- Sections of `free J ⊗ L` are the actual tuples of sections of `L`,
with the original coefficient action supplied by `f`. -/
def finiteFreeTensorSectionsEquiv :
    sectionModuleOverBase f
      (tensor (X := X) (show X.Modules from SheafOfModules.free J) L) U ≃ₗ[R]
        (J → sectionModuleOverBase f L U) := by
  let e₀ := (moduleSectionsFunctor U).mapIso (finiteFreeTensorIsoBiproduct J L)
  let e := e₀.toLinearEquiv.trans (biproductSectionsEquiv J (fun _ : J => L) U)
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro a x
  exact e.map_smul ((f.constToPresheaf.app (op U)).hom a) x

/-- The comparison uses the actual tensor-coproduct isomorphism and
the original sheaf projection at every open. -/
theorem finiteFreeTensorSectionsEquiv_apply
    (x : sectionModuleOverBase f
      (tensor (X := X) (show X.Modules from SheafOfModules.free J) L) U) (j : J) :
    finiteFreeTensorSectionsEquiv J U f L x j =
      ((finiteFreeTensorIsoBiproduct J L).hom ≫
        biproduct.π (fun _ : J => L) j).app U x :=
  biproductSectionsEquiv_apply J (fun _ : J => L) U
    ((finiteFreeTensorIsoBiproduct J L).hom.app U x) j

/-- Restricting a section restricts each of its original tuple coordinates. -/
theorem finiteFreeTensorSectionsEquiv_restriction {V : X.Opens} (h : V ≤ U)
    (x : sectionModuleOverBase f
      (tensor (X := X) (show X.Modules from SheafOfModules.free J) L) U) (j : J) :
    finiteFreeTensorSectionsEquiv J V f L
        (sectionRestrictionOverBase f
          (tensor (X := X) (show X.Modules from SheafOfModules.free J) L) h x) j =
      sectionRestrictionOverBase f L h (finiteFreeTensorSectionsEquiv J U f L x j) := by
  rw [finiteFreeTensorSectionsEquiv_apply, finiteFreeTensorSectionsEquiv_apply]
  let p := (finiteFreeTensorIsoBiproduct J L).hom ≫ biproduct.π (fun _ : J => L) j
  exact congrArg
    (fun a : Γ(tensor (X := X) (show X.Modules from SheafOfModules.free J) L, U) ⟶
      Γ(L, V) => a.hom x) (p.mapPresheaf.naturality (homOfLE h).op)

end AlgebraicGeometry.Scheme.Modules
