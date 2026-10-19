/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafHom
import Nyll.SchemeTheory.Cohomology.Sheaves.ReesTensorRestrictions
import Nyll.SchemeTheory.Modules.Sections.SectionsAlgebra
import Nyll.SchemeTheory.RingTheory.AdicCompletion.ReesTensorCoefficients
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.ReesAlgebra

/-!
# The actual Rees tensor presheaf and its homogeneous retracts

For every open `U`, take the original Rees algebra of the extended base
ideal in `Γ(X, U)`, then tensor it with the original sections `Γ(M, U)`.
Restriction of scalars along the original structural map fixes its base
action. The actual polynomial and module restrictions give an
`OModulePresheaf`, as do the tensors with the original ideal powers.

Coefficient extraction and homogeneous insertion are morphisms of these
actual presheaves. Their composite in each degree is the identity.
The construction applies to every module sheaf, with no flatness or
noetherian assumption and no comparison with a sheaf taken as input.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules.ReesTensor

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A) (M : X.Modules)

/-- The actual Rees tensor on an open, with its original base-ring action. -/
def reesTensorSectionsOverBase (U : X.Opens) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (f.constToPresheaf.app (op U)).hom).obj
    (ModuleCat.of Γ(X, U) (↥(reesAlgebra (sectionsIdeal f I U)) ⊗[Γ(X, U)] Γ(M, U)))

/-- The actual ideal-power tensor on an open, with its original base-ring action. -/
def idealTensorSectionsOverBase (n : ℕ) (U : X.Opens) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (f.constToPresheaf.app (op U)).hom).obj
    (ModuleCat.of Γ(X, U) (↥((sectionsIdeal f I U) ^ n) ⊗[Γ(X, U)] Γ(M, U)))

private def restrictionOverBase {U W : X.Opens} (h : W ≤ U)
    (P : ModuleCat.{u} Γ(X, U)) (Q : ModuleCat.{u} Γ(X, W))
    (φ : P →ₛₗ[(X.presheaf.map (homOfLE h).op).hom] Q) :
    (ModuleCat.restrictScalars (f.constToPresheaf.app (op U)).hom).obj P →ₗ[A]
      (ModuleCat.restrictScalars (f.constToPresheaf.app (op W)).hom).obj Q where
  toFun := φ
  map_add' := φ.map_add
  map_smul' := by
    intro a z
    let z0 : P := z
    have hφ := φ.map_smulₛₗ ((f.constToPresheaf.app (op U)).hom a) z0
    have hcoef : (X.presheaf.map (homOfLE h).op).hom
        ((f.constToPresheaf.app (op U)).hom a) =
      (f.constToPresheaf.app (op W)).hom a :=
      DFunLike.congr_fun (structuralMap_restriction f h) a
    exact hφ.trans (congrArg (fun b : Γ(X, W) => b • φ z0) hcoef)

/-- Actual Rees tensors and actual restrictions, bundled over the original base ring. -/
def reesTensorPresheaf : OModulePresheaf f where
  obj U := reesTensorSectionsOverBase f I M U
  addCommGroup U := inferInstance
  module U := inferInstance
  moduleSections U := inferInstanceAs
    (Module Γ(X, U) (↥(reesAlgebra (sectionsIdeal f I U)) ⊗[Γ(X, U)] Γ(M, U)))
  isScalarTower U := by
    let : Algebra A Γ(X, U) := Scheme.TwoAffineOpenCover.algebraOfHom f U
    exact IsScalarTower.of_compHom A Γ(X, U)
      (↥(reesAlgebra (sectionsIdeal f I U)) ⊗[Γ(X, U)] Γ(M, U))
  res {U W} h := restrictionOverBase f h
    (ModuleCat.of Γ(X, W) (↥(reesAlgebra (sectionsIdeal f I W)) ⊗[Γ(X, W)] Γ(M, W)))
    (ModuleCat.of Γ(X, U) (↥(reesAlgebra (sectionsIdeal f I U)) ⊗[Γ(X, U)] Γ(M, U)))
    (reesTensorRestriction f I M h)
  res_smul h a z := (reesTensorRestriction f I M h).map_smulₛₗ a z
  res_refl U := by
    apply LinearMap.ext
    intro z
    exact reesTensorRestriction_refl f I M U z
  res_comp h h' := by
    apply LinearMap.ext
    intro z
    exact reesTensorRestriction_comp f I M h h' z

/-- Actual ideal-power tensors and actual restrictions, bundled over the original base ring. -/
def idealTensorPresheaf (n : ℕ) : OModulePresheaf f where
  obj U := idealTensorSectionsOverBase f I M n U
  addCommGroup U := inferInstance
  module U := inferInstance
  moduleSections U := inferInstanceAs
    (Module Γ(X, U) (↥((sectionsIdeal f I U) ^ n) ⊗[Γ(X, U)] Γ(M, U)))
  isScalarTower U := by
    let : Algebra A Γ(X, U) := Scheme.TwoAffineOpenCover.algebraOfHom f U
    exact IsScalarTower.of_compHom A Γ(X, U)
      (↥((sectionsIdeal f I U) ^ n) ⊗[Γ(X, U)] Γ(M, U))
  res {U W} h := restrictionOverBase f h
    (ModuleCat.of Γ(X, W) (↥((sectionsIdeal f I W) ^ n) ⊗[Γ(X, W)] Γ(M, W)))
    (ModuleCat.of Γ(X, U) (↥((sectionsIdeal f I U) ^ n) ⊗[Γ(X, U)] Γ(M, U)))
    (idealTensorRestriction f I M h n)
  res_smul h a z := (idealTensorRestriction f I M h n).map_smulₛₗ a z
  res_refl U := by
    apply LinearMap.ext
    intro z
    exact idealTensorRestriction_refl f I M U n z
  res_comp h h' := by
    apply LinearMap.ext
    intro z
    exact idealTensorRestriction_comp f I M h h' n z

/-- The bundled Rees restriction retains the original tensor restriction. -/
theorem reesTensorPresheaf_res_apply {U W : X.Opens} (h : W ≤ U)
    (z : ↥(reesAlgebra (sectionsIdeal f I U)) ⊗[Γ(X, U)] Γ(M, U)) :
    (reesTensorPresheaf f I M).res h z = reesTensorRestriction f I M h z := rfl

/-- The bundled ideal-power restriction retains the original tensor restriction. -/
theorem idealTensorPresheaf_res_apply {U W : X.Opens} (h : W ≤ U) (n : ℕ)
    (z : ↥((sectionsIdeal f I U) ^ n) ⊗[Γ(X, U)] Γ(M, U)) :
    (idealTensorPresheaf f I M n).res h z = idealTensorRestriction f I M h n z := rfl

/-- Extraction of the original tensor coefficient is a morphism of actual presheaves. -/
def coefficient (n : ℕ) :
    OModulePresheaf.Hom (reesTensorPresheaf f I M) (idealTensorPresheaf f I M n) where
  app U :=
    { toFun := ReesTensorCoefficients.coefficient (sectionsIdeal f I U) Γ(M, U) n
      map_add' := (ReesTensorCoefficients.coefficient (sectionsIdeal f I U) Γ(M, U) n).map_add
      map_smul' := by
        intro a z
        exact (ReesTensorCoefficients.coefficient (sectionsIdeal f I U) Γ(M, U) n).map_smul
          ((f.constToPresheaf.app (op U)).hom a) z }
  app_smul U a z :=
    (ReesTensorCoefficients.coefficient (sectionsIdeal f I U) Γ(M, U) n).map_smul a z
  naturality h := by
    apply LinearMap.ext
    intro z
    exact coefficient_restriction f I M h n z

/-- Insertion of an original homogeneous coefficient is a morphism of actual presheaves. -/
def homogeneous (n : ℕ) :
    OModulePresheaf.Hom (idealTensorPresheaf f I M n) (reesTensorPresheaf f I M) where
  app U :=
    { toFun := ReesTensorCoefficients.homogeneous (sectionsIdeal f I U) Γ(M, U) n
      map_add' := (ReesTensorCoefficients.homogeneous (sectionsIdeal f I U) Γ(M, U) n).map_add
      map_smul' := by
        intro a z
        exact (ReesTensorCoefficients.homogeneous (sectionsIdeal f I U) Γ(M, U) n).map_smul
          ((f.constToPresheaf.app (op U)).hom a) z }
  app_smul U a z :=
    (ReesTensorCoefficients.homogeneous (sectionsIdeal f I U) Γ(M, U) n).map_smul a z
  naturality h := by
    apply LinearMap.ext
    intro z
    exact (restriction_homogeneous f I M h n z).symm

/-- The coefficient morphism has the original sectionwise coefficient map. -/
theorem coefficient_app (n : ℕ) (U : X.Opens)
    (z : (reesTensorPresheaf f I M).obj U) :
    (coefficient f I M n).app U z =
      ReesTensorCoefficients.coefficient (sectionsIdeal f I U) Γ(M, U) n z := rfl

/-- The homogeneous morphism has the original sectionwise insertion map. -/
theorem homogeneous_app (n : ℕ) (U : X.Opens)
    (z : (idealTensorPresheaf f I M n).obj U) :
    (homogeneous f I M n).app U z =
      ReesTensorCoefficients.homogeneous (sectionsIdeal f I U) Γ(M, U) n z := rfl

private theorem hom_ext {F G : OModulePresheaf f} {φ ψ : OModulePresheaf.Hom F G}
    (h : ∀ U, φ.app U = ψ.app U) : φ = ψ := by
  cases φ with
  | mk app hscalar hnat =>
      cases ψ with
      | mk app' hscalar' hnat' =>
          have happ : app = app' := funext h
          subst app'
          rfl

/-- Extracting the inserted degree is the identity morphism of the actual ideal tensor presheaf. -/
theorem coefficient_homogeneous (n : ℕ) :
    (coefficient f I M n).comp (homogeneous f I M n) =
      OModulePresheaf.Hom.id (idealTensorPresheaf f I M n) := by
  apply hom_ext
  intro U
  apply LinearMap.ext
  intro z
  exact ReesTensorCoefficients.coefficient_homogeneous (sectionsIdeal f I U) Γ(M, U) n z

/-- A homogeneous insertion has zero coefficient in every distinct degree. -/
theorem coefficient_homogeneous_ne (n k : ℕ) (h : k ≠ n) (U : X.Opens)
    (z : (idealTensorPresheaf f I M n).obj U) :
    (coefficient f I M k).app U ((homogeneous f I M n).app U z) = 0 :=
  ReesTensorCoefficients.coefficient_homogeneous_ne (sectionsIdeal f I U) Γ(M, U) n k h z

/-- The actual coefficient morphisms jointly detect equality on each open. -/
theorem ext_coefficients (U : X.Opens) {z w : (reesTensorPresheaf f I M).obj U}
    (h : ∀ n, (coefficient f I M n).app U z = (coefficient f I M n).app U w) : z = w :=
  ReesTensorCoefficients.ext_coefficients (sectionsIdeal f I U) Γ(M, U) h

end AlgebraicGeometry.Scheme.Modules.ReesTensor
