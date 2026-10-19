/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusScalarExtensionPoints
import Nyll.JacobianVarieties.Generalized.ModulusAbelZeroClass
import Nyll.AlgebraicCurves.Geometry.Schemes.BaseChange.HomPullbackKerPowInvModuleIso

/-! # Scalar extension of actual Abel point classes modulo Picard-zero -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite NeronModelInfra
open AlgebraicGeometry.RelPicard AlgebraicGeometry.RelPicard.BaseChange
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C)

/-- Isomorphic underlying line bundles have an actual Picard-zero rigidified quotient. -/
theorem rigidifiedClassDifference_mem_zero_of_iso {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R))
    (M N : RigidifiedLineBundle (modulusBaseChange c i t)) (e : M.L ≅ N.L) :
    RigidifiedLineBundle.classOf M / RigidifiedLineBundle.classOf N ∈
      modulusPicardZeroSubgroup c i (Over.mk t) := by
  rw [div_eq_mul_inv, ← RigidifiedLineBundle.classOf_dual]
  let eUnit : (M.tensor N.dual).L ≅ 𝟙_ (pullback c t).Modules :=
    (e ⊗ᵢ Iso.refl N.dual.L) ≪≫ N.evaluation
  intro k _ _ s
  have h := one_mem_modulusPicardZero c i (Over.mk t) k s
  exact h.of_iso
    ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).mapIso eUnit).symm

variable [IsClosedImmersion i] [IsProper c] [SmoothOfRelativeDimension 1 c]
  (R' : Type u) [CommRing R'] [Algebra R R']

/-- The two actual Abel bundles are the same graph line bundle under the canonical fibre iso. -/
def scalarExtensionAbelBundleUnderlyingIso {T : Over (Spec (CommRingCat.of R'))}
    (P : T ⟶ Over.mk ((modulusComplement (modulusBaseChange c i (specMap R R'))).ι ≫
      baseChange R c R')) :
    (Scheme.Modules.pullback (κ c R' T.hom).inv).obj
        (modulusAbelBundleAt (baseChange R c R') (modulusBaseChange c i (specMap R R'))
          ⟨P.left, Over.w P⟩).L ≅
      (modulusAbelBundleAt c i
        ⟨(modulusScalarExtensionPoint c i R' P).left,
          Over.w (modulusScalarExtensionPoint c i R' P)⟩).L := by
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
  have hI : (graphOver c' xc.1 xc.2).ker.IsInvertible :=
    RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint c' xc.1 xc.2)
  have hI₀ : (graphOver c xc₀.1 xc₀.2).ker.IsInvertible :=
    RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint c xc₀.1 xc₀.2)
  let ePow := Classical.choice (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso
    (κ c R' T.hom).inv (graphOver c' xc.1 xc.2) (graphOver c xc₀.1 xc₀.2)
    hgraphInv hI hI₀ 1).1
  let eGraph : (Scheme.Modules.pullback (κ c R' T.hom).inv).obj
      (graphOver c' xc.1 xc.2).ker.invModule ≅ (graphOver c xc₀.1 xc₀.2).ker.invModule :=
    (Scheme.Modules.pullback (κ c R' T.hom).inv).mapIso
        (eqToIso (congrArg Scheme.IdealSheafData.invModule (pow_one _).symm)) ≪≫
      ePow ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule (pow_one _))
  exact (Scheme.Modules.pullback (κ c R' T.hom).inv).mapIso
      (modulusAbelBundlePullbackIso c' i' x) ≪≫
    eGraph ≪≫ (modulusAbelBundlePullbackIso c i x₀).symm

/-- Scalar extension preserves the actual Abel origin modulo the actual zero subgroup. -/
theorem scalarExtensionAbelClass_div_mem_zero
    {T : Over (Spec (CommRingCat.of R'))}
    (P : T ⟶ Over.mk ((modulusComplement (modulusBaseChange c i (specMap R R'))).ι ≫
      baseChange R c R')) :
    let a : RigidifiedLineBundle.Classes (modulusBaseChange c i (T.hom ≫ specMap R R')) :=
      scalarExtensionClassesEquiv c i R' T.hom
        (modulusAbelPointClass (baseChange R c R') (modulusBaseChange c i (specMap R R'))
          (T := T) P)
    let b : RigidifiedLineBundle.Classes (modulusBaseChange c i (T.hom ≫ specMap R R')) :=
      modulusAbelPointClass c i (T := (Over.map (specMap R R')).obj T)
        (modulusScalarExtensionPoint c i R' P)
    a / b ∈ modulusPicardZeroSubgroup c i ((Over.map (specMap R R')).obj T) := by
  exact rigidifiedClassDifference_mem_zero_of_iso c i (T.hom ≫ specMap R R')
    _ _ (scalarExtensionAbelBundleUnderlyingIso c i R' P)

end AlgebraicGeometry.GeneralizedJacobian
