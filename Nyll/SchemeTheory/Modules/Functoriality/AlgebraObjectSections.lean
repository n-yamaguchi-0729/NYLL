/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Tensor.TensorSectionAssociator
import Nyll.SchemeTheory.Modules.Tensor.TensorSectionBraiding
import Nyll.SchemeTheory.Modules.Tensor.TensorSectionNaturality
import Nyll.SchemeTheory.Modules.Tensor.TensorSectionRightUnitor
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Mathlib.CategoryTheory.Monoidal.Internal.Module

/-!
# The actual section algebras of a commutative algebra object

The original unit and multiplication of a module-sheaf algebra object
give an internal monoid on its native module of sections. The existing
module-monoid construction supplies its ring and algebra structures,
retaining the original additive group and scalar action. Braiding gives
commutativity. Restrictions are the original module restriction maps.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Modules.AlgebraObject

variable {X : Scheme.{u}} (F : X.Modules) [MonObj F]

private abbrev sectionModule (U : X.Opens) : ModuleCat.{u} Γ(X, U) :=
  ModuleCat.of Γ(X, U) Γ(F, U)

private theorem section_one_mul (U : X.Opens) (r : Γ(X, U)) (x : Γ(F, U)) :
    μ[F].app U (tensorSections (η[F].app U r) x) = r • x := by
  have h := congrArg (fun f : (𝟙_ X.Modules) ⊗ F ⟶ F =>
    f.app U (tensorSections (L := 𝟙_ X.Modules) (M := F) r x)) (MonObj.one_mul F)
  calc
    μ[F].app U (tensorSections (η[F].app U r) x) =
        μ[F].app U ((η[F] ▷ F).app U
          (tensorSections (L := 𝟙_ X.Modules) (M := F) r x)) :=
      (congrArg (μ[F].app U)
        (whiskerRight_app_tensorSections (η[F]) F (U := U) r x)).symm
    _ = (λ_ F).hom.app U (tensorSections (L := 𝟙_ X.Modules) (M := F) r x) := h
    _ = r • x := leftUnitor_hom_app_tensorSections r x

private theorem section_mul_one (U : X.Opens) (x : Γ(F, U)) (r : Γ(X, U)) :
    μ[F].app U (tensorSections x (η[F].app U r)) = r • x := by
  have h := congrArg (fun f : F ⊗ (𝟙_ X.Modules) ⟶ F =>
    f.app U (tensorSections (L := F) (M := 𝟙_ X.Modules) x r)) (MonObj.mul_one F)
  calc
    μ[F].app U (tensorSections x (η[F].app U r)) =
        μ[F].app U ((F ◁ η[F]).app U
          (tensorSections (L := F) (M := 𝟙_ X.Modules) x r)) :=
      (congrArg (μ[F].app U)
        (whiskerLeft_app_tensorSections F (η[F]) (U := U) x r)).symm
    _ = (ρ_ F).hom.app U (tensorSections (L := F) (M := 𝟙_ X.Modules) x r) := h
    _ = r • x := rightUnitor_hom_app_tensorSections x r

private theorem section_mul_assoc (U : X.Opens) (x y z : Γ(F, U)) :
    μ[F].app U (tensorSections (μ[F].app U (tensorSections x y)) z) =
      μ[F].app U (tensorSections x (μ[F].app U (tensorSections y z))) := by
  have h := congrArg (fun f : (F ⊗ F) ⊗ F ⟶ F =>
    f.app U (tensorSections (tensorSections x y) z)) (MonObj.mul_assoc F)
  simpa only [Hom.comp_app, CategoryTheory.comp_apply, whiskerRight_app_tensorSections,
    associator_hom_app_tensorSections, whiskerLeft_app_tensorSections] using h

@[instance_reducible] private def sectionMonoid (U : X.Opens) :
    MonObj (sectionModule F U) where
  one := ModuleCat.ofHom
    (show Γ(X, U) →ₗ[Γ(X, U)] Γ(F, U) from (η[F].val.app (op U)).hom)
  mul := by
    let m : Γ(F ⊗ F, U) →ₗ[Γ(X, U)] Γ(F, U) := (μ[F].val.app (op U)).hom
    exact ModuleCat.ofHom (m.comp (TensorProduct.lift (tensorSectionsBilin F F U)))
  one_mul := by
    apply ModuleCat.hom_ext
    refine TensorProduct.ext (LinearMap.ext fun r => LinearMap.ext fun x => ?_)
    change μ[F].app U (tensorSections (η[F].app U r) x) =
      (λ_ (sectionModule F U)).hom (r ⊗ₜ[Γ(X, U)] x)
    exact (section_one_mul F U r x).trans
      (ModuleCat.MonoidalCategory.leftUnitor_hom_apply r x).symm
  mul_one := by
    apply ModuleCat.hom_ext
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun r => ?_)
    change μ[F].app U (tensorSections x (η[F].app U r)) =
      (ρ_ (sectionModule F U)).hom (x ⊗ₜ[Γ(X, U)] r)
    exact (section_mul_one F U x r).trans
      (ModuleCat.MonoidalCategory.rightUnitor_hom_apply x r).symm
  mul_assoc := by
    apply ModuleCat.hom_ext
    refine TensorProduct.ext (TensorProduct.ext
      (LinearMap.ext fun x => LinearMap.ext fun y => LinearMap.ext fun z => ?_))
    change μ[F].app U (tensorSections (μ[F].app U (tensorSections x y)) z) =
      μ[F].app U (tensorSections x (μ[F].app U (tensorSections y z)))
    exact section_mul_assoc F U x y z

variable [IsCommMonObj F]

@[instance_reducible] private def sectionCommRing (U : X.Opens) :
    CommRing (sectionModule F U) := by
  let : MonObj (sectionModule F U) := sectionMonoid F U
  refine { ModuleCat.MonModuleEquivalenceAlgebra.MonObj.toRing (sectionModule F U) with
    mul_comm := ?_ }
  intro x y
  change μ[F].app U (tensorSections x y) = μ[F].app U (tensorSections y x)
  have h := congrArg (fun f : F ⊗ F ⟶ F => f.app U (tensorSections x y))
    (IsCommMonObj.mul_comm F)
  simpa only [Hom.comp_app, CategoryTheory.comp_apply, braiding_hom_app_tensorSections]
    using h.symm

/-- The commutative section ring on the original module's section type. -/
def sectionRing (U : X.Opens) : CommRingCat.{u} :=
  let : CommRing (sectionModule F U) := sectionCommRing F U
  CommRingCat.of (sectionModule F U)

/-- The section algebra uses exactly the original base-section scalar action. -/
@[instance_reducible]
def sectionAlgebra (U : X.Opens) : Algebra Γ(X, U) (sectionRing F U) := by
  let : MonObj (sectionModule F U) := sectionMonoid F U
  exact ModuleCat.MonModuleEquivalenceAlgebra.Algebra_of_Mon_ (sectionModule F U)

/-- The section-ring unit is the original module-algebra unit on the unit section. -/
theorem sectionRing_one (U : X.Opens) :
    (1 : sectionRing F U) = (η[F].app U (unitSection U) : Γ(F, U)) := rfl

/-- The section-ring product is the original sheaf multiplication on tensor sections. -/
theorem sectionRing_mul (U : X.Opens) (x y : Γ(F, U)) :
    (show sectionRing F U from x) * (show sectionRing F U from y) =
      μ[F].app U (tensorSections x y) := rfl

/-- The structural ring homomorphism of the actual section algebra. -/
def coefficientMap (U : X.Opens) : Γ(X, U) →+* sectionRing F U :=
  let : Algebra Γ(X, U) (sectionRing F U) := sectionAlgebra F U
  algebraMap Γ(X, U) (sectionRing F U)

/-- The coefficient homomorphism is the original unit morphism on sections. -/
theorem coefficientMap_apply (U : X.Opens) (r : Γ(X, U)) :
    coefficientMap F U r = (η[F].app U r : Γ(F, U)) := rfl

/-- Multiplication by a structural coefficient equals the original module action. -/
theorem coefficientMap_mul (U : X.Opens) (r : Γ(X, U)) (x : Γ(F, U)) :
    coefficientMap F U r * (show sectionRing F U from x) = (r • x : Γ(F, U)) :=
  section_one_mul F U r x

/-- The original module restriction, now a homomorphism of the section rings. -/
def restriction {U V : X.Opens} (i : V ⟶ U) : sectionRing F U →+* sectionRing F V where
  toFun x := F.presheaf.map i.op x
  map_zero' := (F.presheaf.map i.op).hom.map_zero
  map_add' := (F.presheaf.map i.op).hom.map_add
  map_one' := by
    change F.presheaf.map i.op (η[F].app U (unitSection U)) = η[F].app V (unitSection V)
    have h := congrArg (fun k : Γ(𝟙_ X.Modules, U) ⟶ Γ(F, V) => k (unitSection U))
      (η[F].mapPresheaf.naturality i.op)
    exact h.symm.trans (congrArg (η[F].app V) (map_unitSection i))
  map_mul' x y := by
    change F.presheaf.map i.op (μ[F].app U (tensorSections x y)) =
      μ[F].app V (tensorSections (F.presheaf.map i.op x) (F.presheaf.map i.op y))
    have h := congrArg (fun k : Γ(F ⊗ F, U) ⟶ Γ(F, V) => k (tensorSections x y))
      (μ[F].mapPresheaf.naturality i.op)
    exact h.symm.trans (congrArg (μ[F].app V) (map_tensorSections i x y))

/-- Restriction retains the original additive-presheaf map on every section. -/
theorem restriction_apply {U V : X.Opens} (i : V ⟶ U) (x : Γ(F, U)) :
    restriction F i x = F.presheaf.map i.op x := rfl

/-- The actual restrictions commute with the original structural coefficients. -/
theorem restriction_coefficientMap {U V : X.Opens} (i : V ⟶ U) (r : Γ(X, U)) :
    restriction F i (coefficientMap F U r) =
      coefficientMap F V (X.presheaf.map i.op r) := by
  exact (congrArg (fun k : Γ(𝟙_ X.Modules, U) ⟶ Γ(F, V) => k r)
    (η[F].mapPresheaf.naturality i.op)).symm

end AlgebraicGeometry.Scheme.Modules.AlgebraObject
