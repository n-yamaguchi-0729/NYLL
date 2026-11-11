/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperCompleteSubalgebraImages
public import Nyll.EtaleFundamentalGroups.StrictHenselian.HenselianNoetherianCompletionProperModel
public import Nyll.EtaleFundamentalGroups.StrictHenselian.HenselianNoetherianCompletionLocal

/-!
# Proper closed-fiber comparison over the actual completion colimit

Every closed-fiber cover lifts on the constructed faithfully flat local
extension of the original henselian ring. The cover is constructed from
actual complete Noetherian images and an actual proper ambient, with no
Noetherian hypothesis on the original ring or finite-presentation
hypothesis on the original proper morphism.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits
open EtaleFundamentalGroups.Inertia

namespace AlgebraicGeometry.FiniteEtale

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

private theorem essSurj_nativeResidue_of_maximalResidue
    (R : Type u) [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [(FiniteEtale.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (algebraMap R (IsLocalRing.maximalIdeal R).ResidueField))))).EssSurj] :
    (FiniteEtale.pullback (pullback.fst f
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))).EssSurj := by
  let m := IsLocalRing.maximalIdeal R
  let e : m.ResidueField ≃+* IsLocalRing.ResidueField R :=
    (maximalQuotientResidueEquiv m).symm
  let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let s := Spec.map (CommRingCat.ofHom (algebraMap R m.ResidueField))
  let k := Spec.map e.toCommRingCatIso.hom
  have hk : k ≫ s = r := by
    change Spec.map e.toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R m.ResidueField)) = _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change e (algebraMap R m.ResidueField a) = IsLocalRing.residue R a
    have ha := RingHom.congr_fun (maximalQuotientResidueEquiv_comp_quotient m) a
    exact (congrArg e ha).symm.trans
      ((maximalQuotientResidueEquiv m).symm_apply_apply (IsLocalRing.residue R a))
  let d : Limits.pullback f r ≅ Limits.pullback f s :=
    asIso (pullback.map f r f s (𝟙 X) k (𝟙 (Spec (CommRingCat.of R)))
      (by rw [Category.comp_id, Category.id_comp])
      (by rw [Category.comp_id, hk]))
  have hd : d.hom ≫ pullback.fst f s = pullback.fst f r := by
    change pullback.lift _ _ _ ≫ pullback.fst f s = _
    rw [pullback.lift_fst, Category.comp_id]
  let c : FiniteEtale.pullback (pullback.fst f r) ≅
      FiniteEtale.pullback (pullback.fst f s) ⋙ FiniteEtale.pullback d.hom :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      d.hom (pullback.fst f s) (pullback.fst f r) hd.symm
  have : (FiniteEtale.pullback d.hom).IsEquivalence :=
    (MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme.{u})
      ⊤ d.symm).isEquivalence_functor
  exact Functor.essSurj_of_iso c.symm

open HenselianNoetherianImageStages SubalgebraImageApproximation

/-- Every original closed-fiber cover of a proper scheme over the constructed
completion colimit lifts. The original henselian ring may be non-Noetherian. -/
theorem pullback_essSurj_closedFiber_completionColimit
    (R A : Type u) [CommRing R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] [HenselianLocalRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (completionColimit R A)) [IsProper f] :
    (FiniteEtale.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue (completionColimit R A)))))).EssSurj := by
  obtain ⟨i, X₀, f₀, hf₀, _hfp₀, j, hj, hbase⟩ :=
    exists_proper_completionImage_ambient R A f
  have : IsProper f₀ := hf₀
  have : IsClosedImmersion j := hj
  have hprime := pullback_essSurj_of_exhaustive_complete_subalgebras
    (completionImagesAfter R A i) (completionImagesAfter_exhaustive R A i) f₀ j
  rw [hbase] at hprime
  exact @essSurj_nativeResidue_of_maximalResidue (completionColimit R A) _
    (completionColimit_isLocalRing R A) X f hprime

/-- Restriction along the actual closed-fiber projection is an equivalence
for every proper scheme over the constructed completion colimit. -/
theorem pullback_isEquivalence_closedFiber_completionColimit
    (R A : Type u) [CommRing R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] [HenselianLocalRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (completionColimit R A)) [IsProper f] :
    (FiniteEtale.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue (completionColimit R A)))))).IsEquivalence := by
  let F := FiniteEtale.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom
    (IsLocalRing.residue (completionColimit R A)))))
  have : F.EssSurj := pullback_essSurj_closedFiber_completionColimit R A f
  let h := @pullbackFullyFaithful_closedFiber_of_isProper_of_henselianLocalRing
    (completionColimit R A) _ (completionColimit_henselianLocalRing R A) X f
    (inferInstance : IsProper f)
  have : F.Full := h.full
  have : F.Faithful := h.faithful
  exact Functor.IsEquivalence.mk

end AlgebraicGeometry.FiniteEtale
