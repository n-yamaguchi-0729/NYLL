/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.DominantPreimmersionPullback
import Nyll.EtaleFundamentalGroups.GeometricFiber.OpenImmersionSurjective
import Nyll.SchemeTheory.LocalGeometry.AffineAwayChart
import Nyll.SchemeTheory.LocalGeometry.SmoothGenericNormal
import Nyll.SchemeTheory.LocalGeometry.SmoothPrimeFiberCharts
import Nyll.SchemeTheory.Normalization.Normal
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Galois.GaloisObjects
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Irreducible

/-!
# A common Galois order on the actual smooth generic charts

For a smooth geometrically connected family over a DVR, every point of
the closed fibre has an affine smooth domain chart with prime special
fibre. The actual generic chart maps into the actual global generic
scheme. Restricting a given global finite étale Galois cover along this
map remains Galois and preserves its automorphism-group order.

Normality and integrality of the global generic scheme are supplied by
smoothness and geometric connectedness. The affine chart and its prime
parameter are constructed geometrically. Nonemptiness of its generic
open gives dominance, and full faithfulness of restriction supplies the
actual automorphism equivalence. Thus all such local normalizations can
use one global Galois order as their root exponent.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

universe u

/-- The prime-fibre affine chart of a closed-fibre point carries the
actual restriction of a global Galois cover, with the same Galois order.
All geometric and connectedness inputs for this restriction are supplied
by the smooth geometrically connected family. -/
theorem exists_smoothGenericGaloisChart
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of B))
    [Smooth f] [GeometricallyConnected f] (π : B) (hπ : Prime π) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away π)))
    let U := pullback f η
    let : IsIntegral U :=
      Smooth.isIntegral_awayBaseChange_of_geometricallyConnected f π hπ.ne_zero
    let : IsNormalIntegral U :=
      Smooth.isNormalIntegral_awayBaseChange_of_geometricallyConnected f π hπ.ne_zero
    let j : U ⟶ X := pullback.fst f η
    let s := Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))
    let Z : Scheme.{u} := pullback f s
    let i : Z ⟶ X := pullback.fst f s
    ∀ (Y : FiniteEtale U) [IsGalois Y] (z : Z),
      ∃ (A : CommAlgCat B) (hA : IsDomain A),
        let : IsDomain A := hA
        ∃ hr : Prime (algebraMap B A π),
          Algebra.Smooth B A ∧
          ∃ v : Spec (.of A) ⟶ X,
            IsOpenImmersion v ∧ i z ∈ Set.range v ∧
            v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B A)) ∧
            let T := Localization.Away (algebraMap B A π)
            let : IsDomain T := IsLocalization.Away.isDomain T hr.ne_zero
            ∃ w : Spec (.of T) ⟶ U,
              IsOpenImmersion w ∧
              IsPullback (Spec.map (CommRingCat.ofHom (algebraMap A T))) w v j ∧
              IsGalois ((FiniteEtale.pullback w).obj Y) ∧
              Nat.card (Aut ((FiniteEtale.pullback w).obj Y)) = Nat.card (Aut Y) := by
  intro η U hIntegralU hNormalU j s Z i Y hGaloisY z
  obtain ⟨V, _, hizV, hA, hSmooth, hr, e, he⟩ :=
    Smooth.exists_primeUniformizer_affineChart f π hπ z
  let A : CommAlgCat B := ((algΓ (.of B)).obj (Over.mk (V.ι ≫ f))).unop
  have : IsDomain A := hA
  have : Algebra.Smooth B A := hSmooth
  let eA : V.toScheme ≅ Spec (.of A) := e
  let t : Spec (.of A) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom (algebraMap B A))
  have heA : eA.hom ≫ t = V.ι ≫ f := he
  let v : Spec (.of A) ⟶ X := eA.inv ≫ V.ι
  have hv : IsOpenImmersion v := inferInstance
  have hmodel : v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B A)) := by
    calc
      v ≫ f = eA.inv ≫ (V.ι ≫ f) := Category.assoc eA.inv V.ι f
      _ = eA.inv ≫ (eA.hom ≫ t) :=
        congrArg (fun h : V.toScheme ⟶ Spec (.of B) ↦ eA.inv ≫ h) heA.symm
      _ = t := Iso.inv_hom_id_assoc eA t
  have hizRange : i z ∈ Set.range v := by
    let x : V.toScheme := ⟨i z, hizV⟩
    refine ⟨eA.hom x, ?_⟩
    calc
      v (eA.hom x) = (eA.hom ≫ v) x := (Scheme.Hom.comp_apply _ _ _).symm
      _ = V.ι x := congrArg (fun h : V.toScheme ⟶ X ↦ h x) (Iso.hom_inv_id_assoc eA V.ι)
      _ = i z := rfl
  let T := Localization.Away (algebraMap B A π)
  have : IsDomain T := IsLocalization.Away.isDomain T hr.ne_zero
  obtain ⟨w, hw, hChart, _⟩ :=
    SchemeTheory.exists_affineAwaySchemeChart B A f v hmodel π
  have : IsOpenImmersion w := hw
  have : IsDominant w :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace w w.isOpenEmbedding.isOpenMap⟩
  have : IsLocallyNoetherian U :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f η)
  have hGalois : IsGalois ((FiniteEtale.pullback w).obj Y) :=
    FiniteEtale.pullback_obj_isGalois_of_isPreimmersion_of_isDominant w Y hGaloisY
  obtain ⟨hRestriction⟩ := FiniteEtale.pullback_fullyFaithful_of_preserves_connected w
    (fun Z hZ ↦ by
      have : IsConnected Z := hZ
      exact FiniteEtale.pullback_obj_isConnected_of_isPreimmersion_of_isDominant w Z)
  let eAut : Aut Y ≃* Aut ((FiniteEtale.pullback w).obj Y) :=
    hRestriction.autMulEquivOfFullyFaithful Y
  exact ⟨A, hA, hr, hSmooth, v, hv, hizRange, hmodel,
    w, hw, hChart, hGalois, (Nat.card_congr eAut.toEquiv).symm⟩

end EtaleFundamentalGroups
