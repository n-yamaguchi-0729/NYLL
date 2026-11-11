/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperCompleteFiniteEtale
public import Nyll.SchemeTheory.Descent.NoetherianImageResidueLimit
public import Nyll.SchemeTheory.FiniteEtale.InverseLimitEssentialSurjectivity
public import Nyll.SchemeTheory.RingTheory.Ramification.NativeMaximalResidue

/-!
# Actual closed-fiber covers over exhaustive complete local subalgebras

Every closed-fiber cover descends to one actual proper image over a complete
Noetherian local subalgebra. The proved complete-local comparison lifts it
there, and native pullback recovers the prescribed original cover.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite
open EtaleFundamentalGroups.Inertia

namespace AlgebraicGeometry.FiniteEtale

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

/-- Complete-local comparison with the actual prime-residue field at the
maximal ideal, retaining the original algebra-map fiber projection. -/
theorem pullback_isEquivalence_complete_maximalResidue
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (p : Ideal R) [p.IsPrime] (hp : p = IsLocalRing.maximalIdeal R) :
    (FiniteEtale.pullback (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField))))).IsEquivalence := by
  subst p
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
  have : (FiniteEtale.pullback (pullback.fst f r)).IsEquivalence :=
    pullback_isEquivalence_closedFiber_of_isProper_of_isAdicComplete R f
  have : (FiniteEtale.pullback (pullback.fst f s) ⋙
      FiniteEtale.pullback d.hom).IsEquivalence := Functor.isEquivalence_of_iso c
  have : (FiniteEtale.pullback d.hom).IsEquivalence :=
    (MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme.{u})
      ⊤ d.symm).isEquivalence_functor
  exact Functor.isEquivalence_of_comp_right
    (FiniteEtale.pullback (pullback.fst f s)) (FiniteEtale.pullback d.hom)

end AlgebraicGeometry.FiniteEtale

namespace AlgebraicGeometry.SubalgebraImageApproximation

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [IsLocalRing A]
  {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
  (S : ι →o Subalgebra R A)
  [∀ i, IsLocalRing (S i)] [∀ i, IsNoetherianRing (S i)]
  [∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (S i)) (S i)]
  [∀ i, IsLocalHom (S i).val.toRingHom]
  (hS : ∀ a : A, ∃ i, a ∈ S i)
  {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of R)) [IsProper f₀]
  {Z : Scheme.{u}} (j : Z ⟶ (ambientCone S f₀).pt) [IsClosedImmersion j]

omit [IsDirected ι (· ≤ ·)] [Nonempty ι] [IsClosedImmersion j] in
/-- Each actual contracted residue-fiber restriction is an equivalence,
because its original stage is proper over a complete Noetherian local ring. -/
theorem completeImageStage_pullback_isEquivalence (i : ιᵒᵖ) :
    (FiniteEtale.pullback
      ((residueFiberFst S f₀ j (IsLocalRing.maximalIdeal A)).app i)).IsEquivalence := by
  apply FiniteEtale.pullback_isEquivalence_complete_maximalResidue
    (S i.unop) (baseMap S f₀ j i)
    (SubalgebraStages.residuePrime S (IsLocalRing.maximalIdeal A) i.unop)
  exact IsLocalRing.maximalIdeal_comap (S i.unop).val.toRingHom

include hS in
/-- Every original closed-fiber cover lifts along the original projection
over an exhaustive family of complete Noetherian local subalgebras. The
cover is constructed from the actual image-stage model, not supplied. -/
theorem pullback_essSurj_of_exhaustive_complete_subalgebras :
    (FiniteEtale.pullback (pullback.fst (originalBaseMap S f₀ j)
      (SubalgebraStages.residueSpecBaseTop (IsLocalRing.maximalIdeal A)))).EssSurj := by
  apply FiniteEtale.pullback_essSurj_of_inverse_limit_stage_essSurj
    (residueFiberDiagram S f₀ j (IsLocalRing.maximalIdeal A)) (diagram S f₀ j)
    (residueFiberCone S f₀ j (IsLocalRing.maximalIdeal A)) (cone S f₀ j)
    (residueFiberConeIsLimit S f₀ j (IsLocalRing.maximalIdeal A) hS)
    (residueFiberFst S f₀ j (IsLocalRing.maximalIdeal A))
    (pullback.fst (originalBaseMap S f₀ j)
      (SubalgebraStages.residueSpecBaseTop (IsLocalRing.maximalIdeal A)))
  · intro i
    exact (residueFiberLeg_fst S f₀ j (IsLocalRing.maximalIdeal A) i).symm
  · intro i
    have : (FiniteEtale.pullback
        ((residueFiberFst S f₀ j (IsLocalRing.maximalIdeal A)).app i)).IsEquivalence :=
      completeImageStage_pullback_isEquivalence S f₀ j i
    infer_instance

end AlgebraicGeometry.SubalgebraImageApproximation
