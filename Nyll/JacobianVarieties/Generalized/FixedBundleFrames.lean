/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.InvertibleScalars
import Nyll.JacobianVarieties.Generalized.RigidifiedLineBundle

/-!
# Scalar frames classify chosen rigidifications of a fixed line bundle

The scalar group here is the actual global-unit group of the ambient scheme.
The proof uses the automorphisms of the given invertible module, including
nontrivial modules, and keeps the compatibility of the chosen trivializations.
Replacing ambient units by parameter units requires a separate comparison.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicCurves.Geometry.Picard.Proofs
  RigidifiedLineBundle_exists_iso_map_pullback_rigSection_comp_eq.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

variable {X D : Scheme.{u}} (i : D ⟶ X) {M : X.Modules}
  (hM : Scheme.Modules.IsInvertible M)

/-- The fixed actual line bundle with the specified frame on the modulus. -/
def withFrame (e : (Scheme.Modules.pullback i).obj M ≅ 𝟙_ D.Modules) :
    RigidifiedLineBundle i where
  L := M
  isInvertible := hM
  trivialization := e

/-- Compatible isomorphism is precisely the actual ambient-scalar frame relation. -/
theorem withFrame_iso_iff (e f : (Scheme.Modules.pullback i).obj M ≅ 𝟙_ D.Modules) :
    Nonempty (Iso (withFrame i hM e) (withFrame i hM f)) ↔
      (scalarFrameSetoid i ((Scheme.Modules.pullback i).obj M)).r e f := by
  constructor
  · rintro ⟨v⟩
    obtain ⟨a, ha⟩ := Scalars.exists_scalarAut hM v.toIso
    have hv : (Scheme.Modules.pullback i).mapIso v.toIso ≪≫ f = e :=
      CategoryTheory.Iso.ext v.compatible
    have hs : smulIso (Units.map i.appTop.hom.toMonoidHom a)
        ((Scheme.Modules.pullback i).obj M) ≪≫ f = e :=
      (congrArg (fun α : Aut ((Scheme.Modules.pullback i).obj M) => α ≪≫ f)
        (pullback_mapIso_smulIso i a M).symm).trans
          ((congrArg (fun α : Aut M => (Scheme.Modules.pullback i).mapIso α ≪≫ f) ha).trans hv)
    apply (scalarFrameSetoid i ((Scheme.Modules.pullback i).obj M)).symm
    exact ⟨a, (Scalars.frameRatio_scalar f (Units.map i.appTop.hom.toMonoidHom a)).symm.trans
      (congrArg (fun z : (Scheme.Modules.pullback i).obj M ≅ 𝟙_ D.Modules => frameRatio f z) hs)⟩
  · intro hr
    obtain ⟨a, ha⟩ := (scalarFrameSetoid i ((Scheme.Modules.pullback i).obj M)).symm hr
    have hs : smulIso (Units.map i.appTop.hom.toMonoidHom a)
        ((Scheme.Modules.pullback i).obj M) ≪≫ f = e :=
      (frameCoordinates f).injective
        ((Scalars.frameRatio_scalar f (Units.map i.appTop.hom.toMonoidHom a)).trans ha)
    refine ⟨⟨smulIso a M, ?_⟩⟩
    exact congrArg CategoryTheory.Iso.hom
      ((congrArg (fun α : Aut ((Scheme.Modules.pullback i).obj M) => α ≪≫ f)
        (pullback_mapIso_smulIso i a M)).trans hs)

/-- An actual scalar-frame class determines a compatible-isomorphism class. -/
def frameClass : ScalarFrameClasses i ((Scheme.Modules.pullback i).obj M) → Classes i :=
  Quotient.lift (fun e => classOf (withFrame i hM e))
    (fun e f h => (classOf_eq_iff _ _).mpr ((withFrame_iso_iff i hM e f).mpr h))

/-- No further identifications are introduced by viewing the frames as rigidified bundles. -/
theorem frameClass_injective : Function.Injective (frameClass i hM) := by
  intro x y hxy
  induction x using Quotient.ind with
  | _ e =>
    induction y using Quotient.ind with
    | _ f =>
      apply Quotient.sound
      exact (withFrame_iso_iff i hM e f).mp ((classOf_eq_iff _ _).mp hxy)

/-- Equality with a given rigidified bundle is an actual compatible underlying isomorphism. -/
theorem frameClass_eq_iff (e : (Scheme.Modules.pullback i).obj M ≅ 𝟙_ D.Modules)
    (N : RigidifiedLineBundle i) :
    frameClass i hM (Quotient.mk _ e) = classOf N ↔
      ∃ a : M ≅ N.L, (Scheme.Modules.pullback i).mapIso a ≪≫ N.trivialization = e := by
  constructor
  · intro h
    obtain ⟨a⟩ := (classOf_eq_iff (withFrame i hM e) N).mp h
    exact ⟨a.toIso, CategoryTheory.Iso.ext a.compatible⟩
  · rintro ⟨a, ha⟩
    apply (classOf_eq_iff (withFrame i hM e) N).mpr
    exact ⟨⟨a, congrArg CategoryTheory.Iso.hom ha⟩⟩

/-- The image consists exactly of bundles with the given underlying isomorphism class. -/
theorem exists_frameClass_eq_iff (N : RigidifiedLineBundle i) :
    (∃ x : ScalarFrameClasses i ((Scheme.Modules.pullback i).obj M),
      frameClass i hM x = classOf N) ↔ Nonempty (M ≅ N.L) := by
  constructor
  · rintro ⟨x, hx⟩
    induction x using Quotient.ind with
    | _ e =>
      obtain ⟨a, _⟩ := (frameClass_eq_iff i hM e N).mp hx
      exact ⟨a⟩
  · rintro ⟨a⟩
    refine ⟨Quotient.mk _ ((Scheme.Modules.pullback i).mapIso a ≪≫ N.trivialization), ?_⟩
    exact (frameClass_eq_iff i hM _ N).mpr ⟨a, rfl⟩

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
