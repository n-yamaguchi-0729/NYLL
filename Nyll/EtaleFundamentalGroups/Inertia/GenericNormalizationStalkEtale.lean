/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.GenericNormalizationStalkPrime
public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationStalkLocalization
public import Nyll.EtaleFundamentalGroups.Normalization.GlobalLocalUnramifiedCriterion

/-!
# Étale normalization from the original generic field source

The integral closure of an actual local ring computes the stalk pullback of
normalization through its canonical normalization comparison. Consequently,
étaleness of these original local integral closures gives a finite étale
normalization of the same generic field extension, with no replacement of its
field spectrum or structural morphism.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.FiniteEtale CategoryTheory
open CategoryTheory.Limits SchemeTheory

namespace EtaleFundamentalGroups.Inertia

universe u

/-- Étaleness of the literal local integral closure transports to the
actual stalk pullback of the original field-source normalization. -/
theorem etale_fieldSourceNormalization_stalk_of_integralClosure_etale
    {X : Scheme.{u}} [IsIntegral X]
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (p : Spec (.of K) ⟶ X) [IsDominant p] [IsPreimmersion p]
    [QuasiCompact p] [QuasiSeparated p] (x : X)
    [Algebra (X.presheaf.stalk x) K] [IsFractionRing (X.presheaf.stalk x) K]
    [Algebra (X.presheaf.stalk x) L] [IsScalarTower (X.presheaf.stalk x) K L]
    (hsource : Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) K)) ≫
      X.fromSpecStalk x = p)
    (hEtale : Algebra.Etale (X.presheaf.stalk x)
      (integralClosure (X.presheaf.stalk x) L)) :
    Etale (pullback.snd (ξ K L ≫ p).fromNormalization (X.fromSpecStalk x)) := by
  let f := ξ K L ≫ p
  let b := X.fromSpecStalk x
  have hSpec : Etale (Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) (integralClosure (X.presheaf.stalk x) L)))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr hEtale)
  have hlocal : Etale (pullback.snd f b).fromNormalization := by
    rw [← genericNormalizationStalkIso_base K L p x hsource]
    infer_instance
  have : IsIso (f.normalizationPullback b) :=
    isIso_normalizationPullback_fromSpecStalk f x
  have hbase : pullback.snd f.fromNormalization b =
      inv (f.normalizationPullback b) ≫ (pullback.snd f b).fromNormalization := by
    exact (IsIso.inv_hom_id_assoc (f.normalizationPullback b)
      (pullback.snd f.fromNormalization b)).symm.trans
        (congrArg (fun q => inv (f.normalizationPullback b) ≫ q)
          (Scheme.Hom.normalizationPullback_snd f b))
  change Etale (pullback.snd f.fromNormalization b)
  rw [hbase]
  infer_instance

/-- A finite extension of an actual generic field source has finite étale
normalization when the integral closure of every original stalk is étale.
The local coefficient maps are constructed from that same generic source. -/
theorem finiteEtale_fieldSourceNormalization_of_stalk_integralClosure_etale
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (p : Spec (.of K) ⟶ X) [IsDominant p] [IsPreimmersion p]
    [QuasiCompact p] [QuasiSeparated p]
    (hlocal : ∀ x : X,
      let _ : Algebra (X.presheaf.stalk x) K := genericFieldSourceStalkAlgebra p x
      let _ : Algebra (X.presheaf.stalk x) L :=
        ((algebraMap K L).comp (algebraMap (X.presheaf.stalk x) K)).toAlgebra
      Algebra.Etale (X.presheaf.stalk x) (integralClosure (X.presheaf.stalk x) L)) :
    IsFiniteEtale (ξ K L ≫ p).fromNormalization := by
  let e := genericFieldSourceRingEquiv p
  let : Algebra X.functionField L := ((algebraMap K L).comp e.toRingHom).toAlgebra
  have hcoeff : (algebraMap X.functionField L).comp e.symm.toRingHom =
      (RingEquiv.refl L).toRingHom.comp (algebraMap K L) := by
    ext a
    change algebraMap K L (e (e.symm a)) = algebraMap K L a
    rw [e.apply_symm_apply]
  have : FiniteDimensional X.functionField L :=
    Module.Finite.of_equiv_equiv e.symm (RingEquiv.refl L) hcoeff
  have hsource : X.genericExtensionMorphism L = ξ K L ≫ p := by
    change Spec.map (CommRingCat.ofHom e.toRingHom ≫
      CommRingCat.ofHom (algebraMap K L)) ≫
        X.fromSpecStalk (genericPoint X) = _
    rw [Spec.map_comp, Category.assoc]
    exact congrArg (fun q => ξ K L ≫ q) (genericFieldSourceIso_hom_fromSpecStalk p)
  have hstalk (x : X) :
      Etale (pullback.snd (ξ K L ≫ p).fromNormalization (X.fromSpecStalk x)) := by
    let : Algebra (X.presheaf.stalk x) K := genericFieldSourceStalkAlgebra p x
    have : IsFractionRing (X.presheaf.stalk x) K :=
      genericFieldSourceStalk_isFractionRing p x
    let : Algebra (X.presheaf.stalk x) L :=
      ((algebraMap K L).comp (algebraMap (X.presheaf.stalk x) K)).toAlgebra
    have : IsScalarTower (X.presheaf.stalk x) K L := IsScalarTower.of_algebraMap_eq' rfl
    exact etale_fieldSourceNormalization_stalk_of_integralClosure_etale K L p x
      (genericFieldSourceStalkMap_fromSpecStalk p x) (hlocal x)
  obtain ⟨hfinite, hetale⟩ := finiteEtale_normalization_of_stalk_unramified X L (fun x => by
    rw [hsource]
    have : Etale (pullback.snd (ξ K L ≫ p).fromNormalization (X.fromSpecStalk x)) :=
      hstalk x
    exact ⟨inferInstance, inferInstance⟩)
  rw [hsource] at hfinite hetale
  exact { toIsFinite := hfinite, toEtale := hetale }

end EtaleFundamentalGroups.Inertia
