/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Classical.PullbackSiteComparison

/-!
# Coefficient-linear pullback under a site isomorphism

The actual module and abelian inverse-image comparisons are compatible with
forgetting coefficients. Their compatibility follows from the defining
adjunction units and gives equality of the existing cohomological pullbacks.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

variable {X : Scheme.{u}} {f g : X ⟶ X} (e : etaleBaseChange f ≅ etaleBaseChange g)
  (R : Type u) [CommRing R]

/-- The module inverse-image comparison induced by an actual site isomorphism. -/
def etalePullbackSiteIso : etalePullback f R ≅ etalePullback g R :=
  (etalePullbackPushforwardAdjunction f R).leftAdjointUniq
    ((etalePullbackPushforwardAdjunction g R).ofNatIsoRight
      (Functor.sheafPushforwardContinuousIso e (ModuleCat.{u} R)
        X.smallEtaleTopology X.smallEtaleTopology).symm)

/-- The actual site comparison commutes with the actual forget-coefficients
comparison; both are characterized by their inverse-image adjunction units. -/
theorem etalePullbackSiteIso_forget
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    Classical.forgetCoefficients.{u + 1, u, u, u}.map
        ((etalePullbackSiteIso e R).hom.app F) ≫
      (etalePullbackForgetCoefficientsIso g R).hom.app F =
    (etalePullbackForgetCoefficientsIso f R).hom.app F ≫
      (etaleAbelianPullbackSiteIso e).hom.app
        (Classical.forgetCoefficients.{u + 1, u, u, u}.obj F) := by
  let U := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := R)
  let amf := etalePullbackPushforwardAdjunction f R
  let amg := etalePullbackPushforwardAdjunction g R
  let aaf := etaleAbelianPullbackPushforwardAdjunction f
  let aag := etaleAbelianPullbackPushforwardAdjunction g
  let βm : etalePushforward f R ≅ etalePushforward g R :=
    Functor.sheafPushforwardContinuousIso e (ModuleCat.{u} R)
      X.smallEtaleTopology X.smallEtaleTopology
  let βa : etaleAbelianPushforward f ≅ etaleAbelianPushforward g :=
    Functor.sheafPushforwardContinuousIso e AddCommGrpCat.{u}
      X.smallEtaleTopology X.smallEtaleTopology
  let ηmf : F ⟶ (etalePushforward f R).obj ((etalePullback f R).obj F) :=
    amf.unit.app F
  let ηmg : F ⟶ (etalePushforward g R).obj ((etalePullback g R).obj F) :=
    amg.unit.app F
  let ηaf : U.obj F ⟶ (etaleAbelianPushforward f).obj
      ((etaleAbelianPullback f).obj (U.obj F)) := aaf.unit.app (U.obj F)
  let ηag : U.obj F ⟶ (etaleAbelianPushforward g).obj
      ((etaleAbelianPullback g).obj (U.obj F)) := aag.unit.app (U.obj F)
  let νmf : U.obj F ⟶ (etaleAbelianPushforward f).obj
      (U.obj ((etalePullback f R).obj F)) := U.map ηmf
  let νmg : U.obj F ⟶ (etaleAbelianPushforward g).obj
      (U.obj ((etalePullback g R).obj F)) := U.map ηmg
  let τm : (etalePullback f R).obj F ⟶ (etalePullback g R).obj F :=
    (etalePullbackSiteIso e R).hom.app F
  let τa : (etaleAbelianPullback f).obj (U.obj F) ⟶
      (etaleAbelianPullback g).obj (U.obj F) :=
    (etaleAbelianPullbackSiteIso e).hom.app (U.obj F)
  let ef : U.obj ((etalePullback f R).obj F) ≅
      (etaleAbelianPullback f).obj (U.obj F) :=
    (etalePullbackForgetCoefficientsIso f R).app F
  let eg : U.obj ((etalePullback g R).obj F) ≅
      (etaleAbelianPullback g).obj (U.obj F) :=
    (etalePullbackForgetCoefficientsIso g R).app F
  have huf : νmf ≫ (etaleAbelianPushforward f).map ef.hom = ηaf :=
    etalePullbackForgetCoefficientsIso_unit f R F
  have hug : νmg ≫ (etaleAbelianPushforward g).map eg.hom = ηag :=
    etalePullbackForgetCoefficientsIso_unit g R F
  have hufi : ηaf ≫ (etaleAbelianPushforward f).map ef.inv = νmf := by
    rw [← huf, Category.assoc, ← Functor.map_comp, ef.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  have hm := Adjunction.unit_leftAdjointUniq_hom_app
    amf (amg.ofNatIsoRight βm.symm) F
  change ηmf ≫ (etalePushforward f R).map τm =
    ηmg ≫ βm.inv.app ((etalePullback g R).obj F) at hm
  have hm' := congrArg (fun φ => U.map φ) hm
  rw [Functor.map_comp, Functor.map_comp] at hm'
  change νmf ≫ (etaleAbelianPushforward f).map (U.map τm) =
    νmg ≫ βa.inv.app (U.obj ((etalePullback g R).obj F)) at hm'
  have ha := Adjunction.unit_leftAdjointUniq_hom_app
    aaf (aag.ofNatIsoRight βa.symm) (U.obj F)
  change ηaf ≫ (etaleAbelianPushforward f).map τa =
    ηag ≫ βa.inv.app ((etaleAbelianPullback g).obj (U.obj F)) at ha
  have hψ : ef.inv ≫ U.map τm ≫ eg.hom = τa := by
    apply (aaf.homEquiv (U.obj F) ((etaleAbelianPullback g).obj (U.obj F))).injective
    change ηaf ≫ (etaleAbelianPushforward f).map (ef.inv ≫ U.map τm ≫ eg.hom) =
      ηaf ≫ (etaleAbelianPushforward f).map τa
    rw [ha]
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, hufi,
      ← Category.assoc, hm', Category.assoc,
      ← βa.inv.naturality eg.hom, ← Category.assoc, hug]
  change U.map τm ≫ eg.hom = ef.hom ≫ τa
  calc
    _ = ef.hom ≫ (ef.inv ≫ U.map τm ≫ eg.hom) := by
      rw [← Category.assoc, ef.hom_inv_id, Category.id_comp]
    _ = ef.hom ≫ τa := congrArg (fun φ => ef.hom ≫ φ) hψ

/-- Actual coefficient-linear pullback is unchanged under the comparison
of inverse-image functors induced by a site isomorphism. -/
theorem etaleCohomologyPullbackMap_siteIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ)
    (x : etaleCohomology X R F n) :
    Classical.cohomologyMap.{u + 1, u, u, u, u} ((etalePullbackSiteIso e R).hom.app F) n
        (etaleCohomologyPullbackMap f R F n x) =
      etaleCohomologyPullbackMap g R F n x := by
  let U := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := R)
  let ef : U.obj ((etalePullback f R).obj F) ≅
      (etaleAbelianPullback f).obj (U.obj F) :=
    (etalePullbackForgetCoefficientsIso f R).app F
  let eg : U.obj ((etalePullback g R).obj F) ≅
      (etaleAbelianPullback g).obj (U.obj F) :=
    (etalePullbackForgetCoefficientsIso g R).app F
  let τm : (etalePullback f R).obj F ⟶ (etalePullback g R).obj F :=
    (etalePullbackSiteIso e R).hom.app F
  let τa : (etaleAbelianPullback f).obj (U.obj F) ⟶
      (etaleAbelianPullback g).obj (U.obj F) :=
    (etaleAbelianPullbackSiteIso e).hom.app (U.obj F)
  have h : U.map τm ≫ eg.hom = ef.hom ≫ τa := etalePullbackSiteIso_forget e R F
  have hi : ef.inv ≫ U.map τm = τa ≫ eg.inv := by
    apply (cancel_mono eg.hom).mp
    rw [Category.assoc, h, ← Category.assoc, ef.inv_hom_id, Category.id_comp,
      Category.assoc, eg.inv_hom_id, Category.comp_id]
  change Sheaf.H.{u} (U.obj F) n at x
  change Sheaf.H.map (U.map τm) n
      (Sheaf.H.map ef.inv n (etaleAbelianCohomologyPullbackMap f (U.obj F) n x)) =
    Sheaf.H.map eg.inv n (etaleAbelianCohomologyPullbackMap g (U.obj F) n x)
  rw [← Sheaf.H.map_comp_apply, hi, Sheaf.H.map_comp_apply]
  exact congrArg (fun z => Sheaf.H.map eg.inv n z)
    (etaleAbelianCohomologyPullbackMap_siteIso e (U.obj F) n x)

/-- The actual module site comparison intertwines the canonical constant
coefficient isomorphisms. -/
theorem etalePullbackSiteIso_constant (M : ModuleCat.{u} R) :
    (etalePullbackSiteIso e R).hom.app
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M) ≫
      (etalePullbackConstantIso g R).hom.app M =
    (etalePullbackConstantIso f R).hom.app M :=
  Sites.constantSheafCompLeftAdjointIso_hom_comp_of_siteIso
    X.smallEtaleTopology (ModuleCat.{u} R) (etaleBaseChange f) (etaleBaseChange g) e
    terminalIsTerminal
    (terminalIsTerminal.isTerminalObj (etaleBaseChange f) (⊤_ X.Etale))
    (terminalIsTerminal.isTerminalObj (etaleBaseChange g) (⊤_ X.Etale))
    (etalePullback f R) (etalePullback g R)
    (etalePullbackPushforwardAdjunction f R)
    (etalePullbackPushforwardAdjunction g R) M

end EtaleCohomology
