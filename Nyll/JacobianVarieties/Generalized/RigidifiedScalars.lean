/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Repository: https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedLineBundle
import Nyll.SchemeTheory.Modules.Invertible.UnitAutomorphisms
import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
import Nyll.SchemeTheory.Modules.Tensor.PullbackTensorUnitObjIsoHomAppPullbackLocalSectionUnitSection

/-!
# Scalar equivalence of chosen trivializations

For the trivial underlying line bundle, compatible isomorphisms identify two
trivializations exactly when their ratio is the restriction of a global unit.
The restriction is the actual map on global functions of the scheme morphism.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicCurves.Geometry.Sheaves.Proofs
  Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection
open AlgebraicGeometry.Scheme.Modules.PullbackTensorSections

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

variable {X D : Scheme.{u}} (i : D ⟶ X)

/-- Restricting an automorphism of the unit sheaf restricts its global unit. -/
theorem unitAutEquivUnits_restrict (e : 𝟙_ X.Modules ≅ 𝟙_ X.Modules) :
    unitAutEquivUnits D (restrictUnitAut i e) =
      Units.map i.appTop.hom.toMonoidHom (unitAutEquivUnits X e) := by
  apply Units.ext
  change unitEndValue D (restrictUnitAut i e).hom =
    i.appTop (unitEndValue X e.hom)
  let j := Scheme.Modules.pullbackTensorUnitObjIso i
  have h : j.hom ≫ (restrictUnitAut i e).hom =
      (Scheme.Modules.pullback i).map e.hom ≫ j.hom := by
    change j.hom ≫ (j.inv ≫ (Scheme.Modules.pullback i).map e.hom ≫ j.hom) = _
    exact j.hom_inv_id_assoc _
  have hs := congrArg (fun f => f.app ⊤
    (pullbackLocalSection i (unitSection (⊤ : X.Opens)))) h
  change (restrictUnitAut i e).hom.app ⊤
      (j.hom.app ⊤ (pullbackLocalSection i (unitSection (⊤ : X.Opens)))) =
    j.hom.app ⊤ (((Scheme.Modules.pullback i).map e.hom).app ⊤
      (pullbackLocalSection i (unitSection (⊤ : X.Opens)))) at hs
  have h1 : j.hom.app ⊤ (pullbackLocalSection i (unitSection (⊤ : X.Opens))) =
      unitSection (⊤ : D.Opens) :=
    Scheme.Modules.pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection i ⊤
  have h2 : ((Scheme.Modules.pullback i).map e.hom).app ⊤
      (pullbackLocalSection i (unitSection (⊤ : X.Opens))) =
      pullbackLocalSection i (e.hom.app ⊤ (unitSection (⊤ : X.Opens))) :=
    (pullbackLocalSection_app i e.hom (unitSection (⊤ : X.Opens))).symm
  have h3 := pullbackTensorUnitObjIso_hom_app_pullbackLocalSection' i ⊤
    (e.hom.app ⊤ (unitSection (⊤ : X.Opens)))
  exact (congrArg ((restrictUnitAut i e).hom.app ⊤) h1).symm.trans
    (hs.trans ((congrArg (j.hom.app ⊤) h2).trans h3))

/-- Scalar trivializations of the trivial bundle are identified precisely
modulo the actual image of global units on `X`. No choice of trivialization
on `D` is discarded before passing to this relation. -/
theorem unitWith_scalars_iso_iff (a b : Γ(D, ⊤)ˣ) :
    Nonempty (Iso (unitWith i ((unitAutEquivUnits D).symm a))
      (unitWith i ((unitAutEquivUnits D).symm b))) ↔
      ∃ c : Γ(X, ⊤)ˣ, Units.map i.appTop.hom.toMonoidHom c * b = a := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := (unitWith_iso_iff (i := i)
      ((unitAutEquivUnits D).symm a) ((unitAutEquivUnits D).symm b)).mp h
    refine ⟨unitAutEquivUnits X e, ?_⟩
    calc
      _ = unitAutEquivUnits D (restrictUnitAut i e) *
          unitAutEquivUnits D ((unitAutEquivUnits D).symm b) := by
        rw [unitAutEquivUnits_restrict, MulEquiv.apply_symm_apply]
      _ = unitAutEquivUnits D
          (restrictUnitAut i e ≪≫ (unitAutEquivUnits D).symm b) :=
        (unitAutEquivUnits_isoTrans D _ _).symm
      _ = a := (congrArg (unitAutEquivUnits D) he).trans
        ((unitAutEquivUnits D).apply_symm_apply a)
  · rintro ⟨c, hc⟩
    apply (unitWith_iso_iff (i := i)
      ((unitAutEquivUnits D).symm a) ((unitAutEquivUnits D).symm b)).mpr
    refine ⟨(unitAutEquivUnits X).symm c, ?_⟩
    apply (unitAutEquivUnits D).injective
    calc
      _ = unitAutEquivUnits D (restrictUnitAut i ((unitAutEquivUnits X).symm c)) *
          unitAutEquivUnits D ((unitAutEquivUnits D).symm b) :=
        unitAutEquivUnits_isoTrans D _ _
      _ = Units.map i.appTop.hom.toMonoidHom c * b :=
        congrArg₂ (fun x y : Γ(D, ⊤)ˣ => x * y)
          ((unitAutEquivUnits_restrict i ((unitAutEquivUnits X).symm c)).trans
            (congrArg (Units.map i.appTop.hom.toMonoidHom)
              ((unitAutEquivUnits X).apply_symm_apply c)))
          ((unitAutEquivUnits D).apply_symm_apply b)
      _ = a := hc
      _ = _ := ((unitAutEquivUnits D).apply_symm_apply a).symm

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
