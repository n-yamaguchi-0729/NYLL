/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusScalarExtensionPoints
import Nyll.JacobianVarieties.Generalized.ModulusAbelCanonicalPoint
import Nyll.JacobianVarieties.Generalized.ModulusAbelZeroClass
import Nyll.JacobianVarieties.Generalized.RigidifiedIdealPullbackComparison
import Nyll.AlgebraicCurves.Geometry.Schemes.BaseChange.HomPullbackKerPowInvModuleIso

/-! # Scalar extension preserves the actual normalized Abel class -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory NeronModelInfra
open AlgebraicGeometry.RelPicard AlgebraicGeometry.RelPicard.BaseChange
open AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.Scheme.Modules
open AlgebraicCurves.Geometry.Schemes.Proofs
open Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso.AlgebraicGeometry.BCKerGlue

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C)
  [IsClosedImmersion i] [IsProper c] [SmoothOfRelativeDimension 1 c]
  (R' : Type u) [CommRing R'] [Algebra R R']

omit [SmoothOfRelativeDimension 1 c] in
/-- The entire moving-point ideal is preserved by the canonical scalar-extension square. -/
theorem scalarExtensionPointIdeal_comap {T : Over (Spec (CommRingCat.of R'))}
    (P : T ⟶ Over.mk ((modulusComplement (modulusBaseChange c i (specMap R R'))).ι ≫
      baseChange R c R')) :
    let c' := baseChange R c R'
    let i' := modulusBaseChange c i (specMap R R')
    let P₀ := modulusScalarExtensionPoint c i R' P
    (RelEffCartierDiv.ofPoint c' (P.left ≫ (modulusComplement i').ι)
      ((Category.assoc _ _ _).trans (Over.w P))).I.comap (κ c R' T.hom).inv =
      (RelEffCartierDiv.ofPoint c (P₀.left ≫ (modulusComplement i).ι)
        ((Category.assoc _ _ _).trans (Over.w P₀))).I := by
  let c' := baseChange R c R'
  let i' := modulusBaseChange c i (specMap R R')
  let x : SchemeHomOver T.hom ((modulusComplement i').ι ≫ c') := ⟨P.left, Over.w P⟩
  let P₀ := modulusScalarExtensionPoint c i R' P
  let x₀ : SchemeHomOver (T.hom ≫ specMap R R') ((modulusComplement i).ι ≫ c) :=
    ⟨P₀.left, Over.w P₀⟩
  let xc : SchemeHomOver T.hom c' :=
    ⟨x.1 ≫ (modulusComplement i').ι, (Category.assoc _ _ _).trans x.2⟩
  let xc₀ : SchemeHomOver (T.hom ≫ specMap R R') c :=
    ⟨x₀.1 ≫ (modulusComplement i).ι, (Category.assoc _ _ _).trans x₀.2⟩
  have hgraph : graphOver c' xc.1 xc.2 ≫ (κ c R' T.hom).hom =
      graphOver c xc₀.1 xc₀.2 := by
    apply pullback.hom_ext
    · rw [Category.assoc, κ_hom_fst, graphOver_fst_assoc, graphOver_fst]
      change (P.left ≫ (modulusComplement i').ι) ≫ pullback.fst c (specMap R R') =
        (P.left ≫ modulusComplementBaseChangeMap c i (specMap R R')) ≫
          (modulusComplement i).ι
      exact (congrArg (P.left ≫ ·)
        (modulusComplementBaseChangeMap_ι c i (specMap R R'))).symm.trans
          (Category.assoc _ _ _).symm
    · rw [Category.assoc, κ_hom_snd, graphOver_snd, graphOver_snd]
  have hgraphInv : graphOver c xc₀.1 xc₀.2 ≫ (κ c R' T.hom).inv =
      graphOver c' xc.1 xc.2 := by
    rw [← hgraph, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact ker_comap_eq_ker (κ c R' T.hom).inv
    (graphOver c' xc.1 xc.2) (graphOver c xc₀.1 xc₀.2) hgraphInv

/-- The canonical graph bundle and its normalization are preserved by scalar extension. -/
def modulusCanonicalPointScalarExtensionIso {T : Over (Spec (CommRingCat.of R'))}
    (P : T ⟶ Over.mk ((modulusComplement (modulusBaseChange c i (specMap R R'))).ι ≫
      baseChange R c R')) :
    RigidifiedLineBundle.Iso
      ((modulusCanonicalPointBundle (baseChange R c R')
        (modulusBaseChange c i (specMap R R')) ⟨P.left, Over.w P⟩).pullback
          (κ c R' T.hom).inv (modulusScalarExtensionIso c i R' T.hom).inv
          (RigidifiedLineBundle.inverse_square _ _
            (modulusScalarExtension_square c i R' T.hom)))
      (modulusCanonicalPointBundle c i
        ⟨(modulusScalarExtensionPoint c i R' P).left,
          Over.w (modulusScalarExtensionPoint c i R' P)⟩) := by
  exact RigidifiedLineBundle.ofInvertibleIdealPullbackIsoOfEq
    (κ c R' T.hom).inv (modulusScalarExtensionIso c i R' T.hom).inv
    (RigidifiedLineBundle.inverse_square _ _ (modulusScalarExtension_square c i R' T.hom))
    _ (RelEffCartierDiv.isInvertible_I _)
    (modulusPointDivisor_avoids (baseChange R c R') (modulusBaseChange c i (specMap R R'))
      ⟨P.left, Over.w P⟩)
    _ (RelEffCartierDiv.isInvertible_I _)
    (modulusPointDivisor_avoids c i
      ⟨(modulusScalarExtensionPoint c i R' P).left,
        Over.w (modulusScalarExtensionPoint c i R' P)⟩)
    (scalarExtensionPointIdeal_comap c i R' P)

/-- Scalar extension preserves the actual Abel class, including its full modulus frame. -/
theorem scalarExtensionClassesEquiv_abelPoint
    {T : Over (Spec (CommRingCat.of R'))}
    (P : T ⟶ Over.mk ((modulusComplement (modulusBaseChange c i (specMap R R'))).ι ≫
      baseChange R c R')) :
    scalarExtensionClassesEquiv c i R' T.hom
        (modulusAbelPointClass (baseChange R c R') (modulusBaseChange c i (specMap R R'))
          (T := T) P) =
      modulusAbelPointClass c i (T := (Over.map (specMap R R')).obj T)
        (modulusScalarExtensionPoint c i R' P) := by
  apply (RigidifiedLineBundle.classOf_eq_iff _ _).mpr
  exact ⟨((modulusAbelBundleAtCanonicalIso (baseChange R c R')
    (modulusBaseChange c i (specMap R R')) ⟨P.left, Over.w P⟩).pullback _ _ _).trans
      ((modulusCanonicalPointScalarExtensionIso c i R' P).trans
        (modulusAbelBundleAtCanonicalIso c i
          ⟨(modulusScalarExtensionPoint c i R' P).left,
            Over.w (modulusScalarExtensionPoint c i R' P)⟩).symm)⟩

end AlgebraicGeometry.GeneralizedJacobian
