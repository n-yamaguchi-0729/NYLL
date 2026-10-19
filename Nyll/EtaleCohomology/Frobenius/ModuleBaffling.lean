/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Frobenius.Baffling

/-!
# Absolute Frobenius on arbitrary module-valued étale cohomology

The actual module and abelian Frobenius comparisons commute with forgetting
coefficients, as follows from their defining adjunction units. The native
coefficient-linear pullback is therefore the identity after the actual
Frobenius sheaf comparison, for every module sheaf and every degree.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

variable (k : Type u) [Field k] [Fintype k] (X : Scheme.{u})
  [X.Over (Spec (.of k))] (R : Type u) [CommRing R]

/-- Forgetting coefficients intertwines the actual module and abelian
Frobenius identity comparisons. -/
theorem etaleFrobeniusPullbackIso_forget
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    Classical.forgetCoefficients.{u + 1, u, u, u}.map
        ((etaleFrobeniusPullbackIso k X R).hom.app F) =
      (etalePullbackForgetCoefficientsIso (X.finiteFieldFrobenius k) R).hom.app F ≫
        (etaleAbelianFrobeniusPullbackIso k X).hom.app
          (Classical.forgetCoefficients.{u + 1, u, u, u}.obj F) := by
  let f := X.finiteFieldFrobenius k
  let U := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := R)
  let am := etalePullbackPushforwardAdjunction f R
  let aa := etaleAbelianPullbackPushforwardAdjunction f
  let βm : etalePushforward f R ≅ 𝟭 _ := etaleFrobeniusPushforwardIso k X R
  let βa : etaleAbelianPushforward f ≅ 𝟭 _ := etaleAbelianFrobeniusPushforwardIso k X
  let τm : (etalePullback f R).obj F ⟶ F :=
    (etaleFrobeniusPullbackIso k X R).hom.app F
  let τa : (etaleAbelianPullback f).obj (U.obj F) ⟶ U.obj F :=
    (etaleAbelianFrobeniusPullbackIso k X).hom.app (U.obj F)
  let ηm : F ⟶ (etalePushforward f R).obj ((etalePullback f R).obj F) := am.unit.app F
  let ηa : U.obj F ⟶ (etaleAbelianPushforward f).obj
      ((etaleAbelianPullback f).obj (U.obj F)) := aa.unit.app (U.obj F)
  let νm : U.obj F ⟶ (etaleAbelianPushforward f).obj
      (U.obj ((etalePullback f R).obj F)) := U.map ηm
  let e : U.obj ((etalePullback f R).obj F) ≅
      (etaleAbelianPullback f).obj (U.obj F) :=
    (etalePullbackForgetCoefficientsIso f R).app F
  have hu : νm ≫ (etaleAbelianPushforward f).map e.hom = ηa :=
    etalePullbackForgetCoefficientsIso_unit f R F
  have hui : ηa ≫ (etaleAbelianPushforward f).map e.inv = νm := by
    rw [← hu, Category.assoc, ← Functor.map_comp, e.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  have hm := Adjunction.unit_leftAdjointUniq_hom_app
    am (Adjunction.id.ofNatIsoRight βm.symm) F
  change ηm ≫ (etalePushforward f R).map τm = 𝟙 F ≫ βm.inv.app F at hm
  rw [Category.id_comp] at hm
  have hm' := congrArg (fun φ => U.map φ) hm
  rw [Functor.map_comp] at hm'
  change νm ≫ (etaleAbelianPushforward f).map (U.map τm) = βa.inv.app (U.obj F) at hm'
  have ha := Adjunction.unit_leftAdjointUniq_hom_app
    aa (Adjunction.id.ofNatIsoRight βa.symm) (U.obj F)
  change ηa ≫ (etaleAbelianPushforward f).map τa =
    𝟙 (U.obj F) ≫ βa.inv.app (U.obj F) at ha
  rw [Category.id_comp] at ha
  have h : e.inv ≫ U.map τm = τa := by
    apply (aa.homEquiv (U.obj F) (U.obj F)).injective
    change ηa ≫ (etaleAbelianPushforward f).map (e.inv ≫ U.map τm) =
      ηa ≫ (etaleAbelianPushforward f).map τa
    rw [Functor.map_comp, ← Category.assoc, hui, hm', ha]
  change U.map τm = e.hom ≫ τa
  rw [← h, ← Category.assoc, e.hom_inv_id, Category.id_comp]

/-- The original coefficient-linear pullback under absolute finite-field
Frobenius is the identity under its canonical sheaf comparison, for arbitrary
module coefficients. -/
theorem etaleCohomologyFrobeniusPullback_eq
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ)
    (x : etaleCohomology X R F n) :
    Classical.cohomologyMap.{u + 1, u, u, u, u}
        ((etaleFrobeniusPullbackIso k X R).hom.app F) n
        (etaleCohomologyPullbackMap (X.finiteFieldFrobenius k) R F n x) = x := by
  let U := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := R)
  let e := (etalePullbackForgetCoefficientsIso (X.finiteFieldFrobenius k) R).app F
  let τm := (etaleFrobeniusPullbackIso k X R).hom.app F
  let τa := (etaleAbelianFrobeniusPullbackIso k X).hom.app (U.obj F)
  have h : U.map τm = e.hom ≫ τa := etaleFrobeniusPullbackIso_forget k X R F
  have hi : e.inv ≫ U.map τm = τa := by
    rw [h, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  change Sheaf.H.{u} (U.obj F) n at x
  change Sheaf.H.map (U.map τm) n
      (Sheaf.H.map e.inv n
        (etaleAbelianCohomologyPullbackMap (X.finiteFieldFrobenius k) (U.obj F) n x)) = x
  rw [← Sheaf.H.map_comp_apply, hi]
  exact etaleAbelianCohomologyFrobeniusPullback_eq k X (U.obj F) n x

end EtaleCohomology
