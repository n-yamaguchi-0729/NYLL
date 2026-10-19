/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.GeometricModulusTorsorDescent
import Nyll.JacobianVarieties.Generalized.GeometricModulusEmptyRegularMap
import Nyll.JacobianVarieties.Generalized.ModulusComplementFiniteExtension
import Nyll.JacobianVarieties.Generalized.GeometricModulusMapCondition

/-! # The full unpointed geometric-modulus universal property

The empty modulus is included. A finite separable extension supplies the
first complement point; a further such extension supplies a point outside
its degree-one divisor. Each actual equivariant factor descends with its
Abel identity, so no ground-field rational point or splitting is assumed.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry.SmoothProperCurve
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

/-- For the empty modulus, a chosen complement point constructs a unique
equivariant Abel factor over the original field. The second point needed
for the degree-one comparison is constructed over a finite extension and
both morphisms are then descended. -/
theorem existsUnique_picardOneMapFromGeometricModulus_zero
    (D : RelEffCartierDiv c 0 (𝟙 (Spec (CommRingCat.of K))))
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
    (H : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated H.X.hom]
    (Q : Over (Spec (CommRingCat.of K))) [ModObj H.X Q]
    [IsIso (ModObj.leftSMul H.X Q)]
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q)
    (hmod : geometricTorsorMapHasModulus c D H Q q) :
    ∃! fg : (groupScheme c D ⟶ H) × (picardOne c D ⟶ Q),
      abelOneMap c D ≫ fg.2 = q ∧
        ∀ (T : Over (Spec (CommRingCat.of K)))
          (g : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D),
          (g • x) ≫ fg.2 = (g ≫ fg.1.hom.hom.hom) • (x ≫ fg.2) := by
  obtain ⟨E, hfinite, hseparable, hE⟩ :=
    exists_finiteSeparableExtension_picardOneMap_zero c D ε H Q q hmod (AlgebraicClosure K)
  have : Module.Finite K E := hfinite
  have : Algebra.IsSeparable K E := hseparable
  let F := Over.pullback (specMap K E)
  let HE := (GroupSchemes.baseChange (specMap K E)).obj H
  let _ : ModObj HE.X (F.obj Q) := F.modObjObj H.X Q
  obtain ⟨fgE, hfgE, _⟩ := hE
  obtain ⟨fg, hfg, _⟩ := existsUnique_equivariantPair_descends_finiteSeparable
    c D H Q q E hmod fgE.1 fgE.2 hfgE.1 hfgE.2
  refine ⟨fg, hfg.2.2, ?_⟩
  intro fg' hfg'
  obtain ⟨hφ, hf⟩ := abelOneMap_equivariantPair_ext_unpointed c D
    fg'.1 fg.1 fg'.2 fg.2 hfg'.2 hfg.2.2.2 (hfg'.1.trans hfg.2.2.1.symm)
  exact Prod.ext hφ hf

variable {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (H : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated H.X.hom]
  (Q : Over (Spec (CommRingCat.of K))) [ModObj H.X Q]
  [IsIso (ModObj.leftSMul H.X Q)]
  (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q)

/-- Full geometric modulus gives the unique regular equivariant Abel factor
over any field, in every degree, without a rational basepoint. -/
theorem existsUnique_picardOneMapFromGeometricModulus_unpointed
    (hmod : geometricTorsorMapHasModulus c D H Q q) :
    ∃! fg : (groupScheme c D ⟶ H) × (picardOne c D ⟶ Q),
      abelOneMap c D ≫ fg.2 = q ∧
        ∀ (T : Over (Spec (CommRingCat.of K)))
          (g : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D),
          (g • x) ≫ fg.2 = (g ≫ fg.1.hom.hom.hom) • (x ≫ fg.2) := by
  obtain hd | hd := Nat.eq_zero_or_pos d
  · subst d
    obtain ⟨E, hfinite, hseparable, ⟨εE⟩⟩ :=
      modulusComplement_finiteSeparableExtension_point c D (AlgebraicClosure K)
    have : Module.Finite K E := hfinite
    have : Algebra.IsSeparable K E := hseparable
    let cE := baseChange K c E
    let DE := D.changeBaseOfIdentity (specMap K E)
    let F := Over.pullback (specMap K E)
    let HE := (GroupSchemes.baseChange (specMap K E)).obj H
    let _ : ModObj HE.X (F.obj Q) := F.modObjObj H.X Q
    have : IsIso (ModObj.leftSMul HE.X (F.obj Q)) := F.isIso_leftSMul_modObjObj H.X Q
    have : IsSeparated HE.X.hom := by
      change IsSeparated (Limits.pullback.snd H.X.hom (specMap K E))
      infer_instance
    obtain ⟨fgE, hfgE, _⟩ := existsUnique_picardOneMapFromGeometricModulus_zero
      cE DE εE HE (F.obj Q) (modulusMapScalarExtension c D E Q q)
      (geometricTorsorMapHasModulus_scalarExtension c D H Q q hmod E)
    obtain ⟨fg, hfg, _⟩ := existsUnique_equivariantPair_descends_finiteSeparable
      c D H Q q E hmod fgE.1 fgE.2 hfgE.1 hfgE.2
    refine ⟨fg, hfg.2.2, ?_⟩
    intro fg' hfg'
    obtain ⟨hφ, hf⟩ := abelOneMap_equivariantPair_ext_unpointed c D
      fg'.1 fg.1 fg'.2 fg.2 hfg'.2 hfg.2.2.2 (hfg'.1.trans hfg.2.2.1.symm)
    exact Prod.ext hφ hf
  · exact existsUnique_picardOneMapFromGeometricModulus_positive_unpointed c D H Q q hd hmod

/-- The intrinsic principal-divisor condition is exactly the universal
factorization property; the reverse implication uses the actual Abel map's
modulus and equivariant composition. -/
theorem geometricTorsorMapHasModulus_iff_existsUnique_equivariantPair :
    geometricTorsorMapHasModulus c D H Q q ↔
      ∃! fg : (groupScheme c D ⟶ H) × (picardOne c D ⟶ Q),
        abelOneMap c D ≫ fg.2 = q ∧
          ∀ (T : Over (Spec (CommRingCat.of K)))
            (g : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D),
            (g • x) ≫ fg.2 = (g ≫ fg.1.hom.hom.hom) • (x ≫ fg.2) := by
  constructor
  · exact existsUnique_picardOneMapFromGeometricModulus_unpointed c D H Q q
  · rintro ⟨fg, hfg, _⟩
    rw [← hfg.1]
    exact geometricTorsorMapHasModulus_comp c D (groupScheme c D) H
      (picardOne c D) Q (abelOneMap c D) (geometricTorsorMapHasModulus_abelOne c D)
      fg.1 fg.2 hfg.2

end AlgebraicGeometry.GeneralizedJacobian
