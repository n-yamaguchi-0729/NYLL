/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_unitAutSection_trans_and_unitAutSection_refl.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
public import Nyll.AlgebraicCurves.Geometry.Schemes.Covers.OrderedAffineCoverComap
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.AlgebraicCurves.Geometry.Picard.Deformation.CechObstruction

/-!
# Scheme Modules unit Aut Section trans and unit Aut Section refl
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules (unitAutSectionValue)

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.UnitAutomorphisms


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace


universe u

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (Scheme Scheme.Modules Scheme.Modules.unitAutSection)

namespace Scheme

export _root_.AlgebraicGeometry.Scheme (ringCatSheaf Γ topIso Modules Opens PresheafOfModules
  Modules.unitAutSection)

namespace Modules

export _root_.AlgebraicGeometry.Scheme.Modules (presheaf map_smul unitAutSection)


open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry


variable {Y : Scheme.{u}}

/-- Evaluate a unit automorphism on the unit section of the open subscheme. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.unitAutSection_eq (W : Y.Opens)
    (e : @Iso ((W : Scheme.{u}).Modules) _
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)) :
    unitAutSection W e = W.topIso.hom.hom (unitAutSectionValue W e 1) := rfl

private theorem uapp_mul (W : Y.Opens)
    (e : @Iso ((W : Scheme.{u}).Modules) _
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf))
    (x y : (W : Scheme.{u}).presheaf.obj (op ⊤)) : unitAutSectionValue W e (x * y) = x *
      unitAutSectionValue W e y :=
  ((e.hom.val.app (op ⊤)).hom).map_smul (show ((W : Scheme.{u}).ringCatSheaf.obj.obj (op ⊤)) from
    x) y

private theorem uapp_trans (W : Y.Opens)
    (e e' : @Iso ((W : Scheme.{u}).Modules) _
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf))
    (x : (W : Scheme.{u}).presheaf.obj (op ⊤)) : unitAutSectionValue W (e ≪≫ e') x =
      unitAutSectionValue W e' (unitAutSectionValue W e x) :=
  rfl

private theorem uapp_refl (W : Y.Opens) (x : (W : Scheme.{u}).presheaf.obj (op ⊤)) :
    unitAutSectionValue W (Iso.refl _) x = x :=
  rfl

/-- Composition of unit automorphisms multiplies their sections. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.unitAutSection_trans (W : Y.Opens)
    (e e' : @Iso ((W : Scheme.{u}).Modules) _
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)) :
    unitAutSection W (e ≪≫ e') = unitAutSection W e * unitAutSection W e' := by
  change W.topIso.hom.hom (unitAutSectionValue W (e ≪≫ e') 1) =
    W.topIso.hom.hom (unitAutSectionValue W e 1) *
      W.topIso.hom.hom (unitAutSectionValue W e' 1)
  rw [← map_mul, uapp_trans, ← uapp_mul, mul_one]

/-- The identity unit automorphism gives the unit section. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.unitAutSection_refl (W : Y.Opens) :
    unitAutSection W (Iso.refl _) = 1 :=
  (congrArg W.topIso.hom.hom (uapp_refl W 1)).trans (map_one _)

/-- The inverse section multiplied by the original section is one. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.unitAutSection_symm_mul (W : Y.Opens)
    (e : @Iso ((W : Scheme.{u}).Modules) _
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)) :
    unitAutSection W e.symm * unitAutSection W e = 1 := by
  exact (unitAutSection_trans W e.symm e).symm.trans
    ((congrArg (unitAutSection W) (Iso.symm_self_id e)).trans (unitAutSection_refl W))

/-- The original section multiplied by the inverse section is one. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.unitAutSection_mul_symm (W : Y.Opens)
    (e : @Iso ((W : Scheme.{u}).Modules) _
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)) :
    unitAutSection W e * unitAutSection W e.symm = 1 := by
  exact (unitAutSection_trans W e e.symm).symm.trans
    ((congrArg (unitAutSection W) (Iso.self_symm_id e)).trans (unitAutSection_refl W))

/-- A unit automorphism of an open subscheme gives an invertible section. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isUnit_unitAutSection (W : Y.Opens)
    (e : @Iso ((W : Scheme.{u}).Modules) _
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)) :
    IsUnit (unitAutSection W e) :=
  ⟨⟨_, _, unitAutSection_mul_symm W e, unitAutSection_symm_mul W e⟩, rfl⟩

end AlgebraicGeometry.Scheme.Modules

theorem _root_.AlgebraicGeometry.Scheme.Modules.unitAutSection_trans_and_unitAutSection_refl
    {Y : Scheme.{u}} (W : Y.Opens) :
    (∀ e e' : @Iso ((W : Scheme.{u}).Modules) _
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf)
      (SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf),
        Scheme.Modules.unitAutSection W (e ≪≫ e') =
          Scheme.Modules.unitAutSection W e * Scheme.Modules.unitAutSection W e') ∧
      Scheme.Modules.unitAutSection W (Iso.refl _) = 1 :=
  ⟨fun e e' => _root_.AlgebraicGeometry.Scheme.Modules.unitAutSection_trans W e e',
    _root_.AlgebraicGeometry.Scheme.Modules.unitAutSection_refl W⟩
end AlgebraicCurves.Geometry.Sheaves.Proofs.UnitAutomorphisms
end ProofImplementation
