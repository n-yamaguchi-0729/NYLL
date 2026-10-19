/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusFrameTest
import Nyll.JacobianVarieties.Generalized.FrameBaseChange
import Nyll.JacobianVarieties.Generalized.ModulusUnitRelativeRepresentation

/-!
# The zero fibre of the Poincaré frame scheme

The actual zero-section trivialization of the ordinary Poincaré bundle
trivializes its restriction to the full modulus. Scalar-frame coordinates
then identify the scheme fibre with the already constructed scalar-unit
quotient, including nonreduced moduli.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard
open SchemeTheory.WeilRestriction AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
  {P : SubPicCondition c ε} {J : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε P J)

/-- The supplied ordinary zero-section trivialization gives an actual frame on its modulus. -/
def poincareZeroModulusFrame :
    (Scheme.Modules.pullback
      (pullback.fst (pullback.snd (modulusBaseMap D) J.toBase) J.zeroSection)).obj
        (poincareModulusBundle D h) ≅
          𝟙_ (pullback (pullback.snd (modulusBaseMap D) J.toBase) J.zeroSection).Modules := by
  let g : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) J.toBase :=
    ⟨J.zeroSection, J.zeroSection_toBase⟩
  let a : Over.mk (baseChangeSnd (modulusBaseMap D) g) ≅
      Over.mk (pullback.fst (pullback.snd (modulusBaseMap D) J.toBase) J.zeroSection) :=
    Over.isoMk (isPullback_baseChangeSnd (modulusBaseMap D) g).isoPullback
      (isPullback_baseChangeSnd (modulusBaseMap D) g).isoPullback_hom_fst
  let e : (Scheme.Modules.pullback (baseChangeSnd (modulusBaseMap D) g)).obj
      (poincareModulusBundle D h) ≅ 𝟙_ (pullback (modulusBaseMap D) (𝟙 _)).Modules :=
    ((RigidifiedLineBundle.restrictionComparison
      (baseChangeSnd c g) (baseChangeSnd (modulusBaseMap D) g)
      (modulusFamilyInclusion_naturality D g)).app h.poincare.L).symm ≪≫
        (Scheme.Modules.pullback (modulusFamilyInclusion D (𝟙 _))).mapIso h.zero.some ≪≫
          Scheme.Modules.pullbackUnitIso (modulusFamilyInclusion D (𝟙 _))
  exact ((framePresheaf (poincareModulusBundle D h)).mapIso a.op).toEquiv.symm e

/-- The actual scheme fibre over the designated zero is the full modulus unit quotient. -/
def poincareZeroFibreIso (hd : 0 < d) :
    (Over.pullback J.zeroSection).obj (poincareFrameQuotient D h hd) ≅
      (modulusUnitQuotient D hd).X := by
  let : IsFinite (modulusBaseMap D) := D.isFinite
  let q := pullback.snd (modulusBaseMap D) J.toBase
  let M := poincareModulusBundle D h
  let r := representableByBaseChange J.zeroSection (poincareFrameQuotientRepresentable D h hd)
  let e := r.ofIso
    ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (Type (u + 1))).mapIso
        (scalarFrameSheafBaseChangeIso q J.zeroSection M ≪≫
          scalarFrameSheafCoordinatesIso (pullback.snd q J.zeroSection)
            (poincareZeroModulusFrame D h)))
  let U : Over (Spec (CommRingCat.of K)) := (modulusUnitQuotient D hd).X
  let rU : (modulusUnitQuotientSheaf (modulusBaseMap D)).obj.RepresentableBy U :=
    modulusUnitSheafRepresentable (modulusBaseMap D) (positiveModulusBasis D hd)
  let eU := modulusUnitRepresentableBaseChange q J.zeroSection
    (modulusUnitRepresentableBaseChange (modulusBaseMap D) J.toBase rU)
  exact e.uniqueUpToIso eU ≪≫ ((Over.pullbackComp J.zeroSection J.toBase).app U).symm ≪≫
    eqToIso (congrArg (fun f => (Over.pullback f).obj U) J.zeroSection_toBase) ≪≫
      Over.pullbackId.app U

end AlgebraicGeometry.GeneralizedJacobian
