/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.NativeBoundaryFillingInertia

/-!
# The original normalization prime generates the filling kernel

The actual strict-local source at the chosen normalization prime gives
one geometric path for which its image is the original ideal-inertia
image. The boundary exact sequence then identifies the original filling
kernel with its closed normal closure. This comparison precedes every
abelian quotient and retains the entire wild inertia subgroup.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory
open Yamaguchi26SolvableCoverings
open EtaleFundamentalGroups.StrictHenselian EtaleFundamentalGroups.Inertia

namespace EtaleFundamentalGroups.Cohomology

universe u

/-- The original map induced by a scheme morphism and a geometric path. -/
def geometricSourceHom {U T : Scheme.{u}} {Ω Ξ : Type u} [Field Ω] [Field Ξ]
    (j : T ⟶ U) (xi : Spec (.of Ω) ⟶ T)
    (point : Spec (.of Ξ) ⟶ U) (t : fiber (xi ≫ j) ≅ fiber point) :
    π₁ᵉᵗ(xi) →ₜ* π₁ᵉᵗ(point) :=
  (ContinuousMonoidHom.toContinuousMonoidHom (continuousConjAut t)).comp
    (fundamentalGroupHom j xi)

private theorem conjAut_eqToIso_point_eq {Ω : Type u} [Field Ω] {S : Scheme.{u}}
    {p q : Spec (.of Ω) ⟶ S} (h : p = q) (a : π₁ᵉᵗ(p)) :
    (eqToIso (congrArg fiber h)).conjAut a = h ▸ a := by
  subst q
  rfl

/-- An isomorphism of the actual source schemes allows a geometric path
for which the original, nonabelian image subgroups coincide. -/
theorem exists_path_geometricSourceHom_range_eq_of_iso
    {U T T' : Scheme.{u}} [ConnectedSpace T] [ConnectedSpace T']
    {Ω Ω' Ξ : Type u} [Field Ω] [IsSepClosed Ω]
    [Field Ω'] [IsSepClosed Ω'] [Field Ξ]
    (j : T ⟶ U) (j' : T' ⟶ U) (e : T' ≅ T) (he : e.hom ≫ j = j')
    (xi : Spec (.of Ω) ⟶ T) (xi' : Spec (.of Ω') ⟶ T')
    (point : Spec (.of Ξ) ⟶ U) (t' : fiber (xi' ≫ j') ≅ fiber point) :
    ∃ t : fiber (xi ≫ j) ≅ fiber point,
      (geometricSourceHom j xi point t).toMonoidHom.range =
        (geometricSourceHom j' xi' point t').toMonoidHom.range := by
  subst j'
  let E : FiniteEtale T ≌ FiniteEtale T' :=
    MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ e.symm
  have : (pullback e.hom).IsEquivalence := E.isEquivalence_functor
  let eπ := fundamentalGroupEquivOfPullbackEquivalence e.hom xi'
  obtain ⟨s⟩ := nonempty_fiber_iso (xi' ≫ e.hom) xi
  let sU := (pullbackFiberIso j (xi' ≫ e.hom)).symm ≪≫
    Functor.isoWhiskerLeft (pullback j) s ≪≫ pullbackFiberIso j xi
  let hpoint : (xi' ≫ e.hom) ≫ j = xi' ≫ (e.hom ≫ j) := Category.assoc xi' e.hom j
  let c := eqToIso (congrArg fiber hpoint)
  let t := sU.symm ≪≫ c ≪≫ t'
  refine ⟨t, ?_⟩
  have hvalue (a : π₁ᵉᵗ(xi')) :
      geometricSourceHom (e.hom ≫ j) xi' point t' a =
        geometricSourceHom j xi point t (s.conjAut (eπ a)) := by
    have hcomp : c.conjAut (fundamentalGroupHom j (xi' ≫ e.hom) (eπ a)) =
        fundamentalGroupHom (e.hom ≫ j) xi' a :=
      (conjAut_eqToIso_point_eq hpoint _).trans
        (fundamentalGroupHom_comp_of_eq e.hom j (e.hom ≫ j) rfl xi' hpoint a)
    have hs := fundamentalGroupHom_conjAut j (xi' ≫ e.hom) xi s (eπ a)
    change t'.conjAut (fundamentalGroupHom (e.hom ≫ j) xi' a) =
      t.conjAut (fundamentalGroupHom j xi (s.conjAut (eπ a)))
    rw [← hcomp, ← hs]
    change t'.conjAut (c.conjAut (fundamentalGroupHom j (xi' ≫ e.hom) (eπ a))) =
      (sU.symm ≪≫ c ≪≫ t').conjAut
        (sU.conjAut (fundamentalGroupHom j (xi' ≫ e.hom) (eπ a)))
    have hcancel (b : Aut (fiber ((xi' ≫ e.hom) ≫ j))) :
        sU.symm.conjAut (sU.conjAut b) = b := by
      rw [← sU.trans_conjAut sU.symm, sU.self_symm_id]
      apply Aut.ext
      apply Iso.ext
      exact congrArg End.asHom (Iso.refl_conj b.toEnd)
    rw [Iso.trans_conjAut, Iso.trans_conjAut, hcancel]
  ext z
  constructor
  · rintro ⟨b, rfl⟩
    obtain ⟨a, ha⟩ := eπ.surjective (s.conjAut.symm b)
    refine ⟨a, ?_⟩
    change geometricSourceHom (e.hom ≫ j) xi' point t' a =
      geometricSourceHom j xi point t b
    rw [hvalue, ha, s.conjAut.apply_symm_apply]
  · rintro ⟨a, rfl⟩
    exact ⟨s.conjAut (eπ a), (hvalue a).symm⟩

/-- The actual field-source map commutes with scalar restriction under the
specified equality of the original generic geometric points. -/
theorem fieldSource_restriction_eq_point_transport
    (F E Ω : Type u) [Field F] [Field E] [Field Ω]
    [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω]
    [IsSepClosure F Ω] [IsSepClosure E Ω] [IsSepClosed Ω]
    {U : Scheme.{u}} [IsIntegral U]
    (p : Spec (.of F) ⟶ U) (r : Spec (.of E) ⟶ U)
    (hpoint : ξ E Ω ≫ r = ξ F Ω ≫ p) (σ : Gal(Ω/E)) :
    continuousConjAut (eqToIso (congrArg fiber hpoint))
        (fieldSourceAbsoluteGaloisHom E Ω r σ) =
      fieldSourceAbsoluteGaloisHom F Ω p (σ.restrictScalars F) := by
  have hE := fundamentalGroupHom_point_of_point_action r (ξ E Ω)
    (suppliedGaloisEquivFundamentalGroup E Ω σ) σ.toRingHom
    (suppliedGaloisEquivFundamentalGroup_point E Ω σ)
  have hF := fundamentalGroupHom_point_of_point_action p (ξ F Ω)
    (suppliedGaloisEquivFundamentalGroup F Ω (σ.restrictScalars F))
    (σ.restrictScalars F).toRingHom
    (suppliedGaloisEquivFundamentalGroup_point F Ω (σ.restrictScalars F))
  apply Aut.ext
  ext W w
  apply (fiberObjEquivHom (ξ F Ω ≫ p) W).injective
  apply Over.OverMorphism.ext
  exact (point_action_of_eqToIso hpoint _ σ.toRingHom hE W w).trans (hF W w).symm

/-- The original strict-local source image is the restriction image of its
actual absolute Galois group, before taking any abelian quotient. -/
theorem geometricSourceHom_range_fieldTower
    (F E Ω : Type u) [Field F] [Field E] [Field Ω]
    [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω]
    [IsSepClosure F Ω] [IsSepClosure E Ω] [IsSepClosed Ω]
    {U : Scheme.{u}} [IsIntegral U]
    (p : Spec (.of F) ⟶ U) (r : Spec (.of E) ⟶ U)
    (hpoint : ξ E Ω ≫ r = ξ F Ω ≫ p) :
    (geometricSourceHom r (ξ E Ω) (ξ F Ω ≫ p)
        (eqToIso (congrArg fiber hpoint))).toMonoidHom.range =
      (AlgEquiv.restrictScalarsHom F : Gal(Ω/E) →* Gal(Ω/F)).range.map
        (fieldSourceAbsoluteGaloisHom F Ω p).toMonoidHom := by
  let c := suppliedGaloisEquivFundamentalGroup E Ω
  let a := geometricSourceHom r (ξ E Ω) (ξ F Ω ≫ p)
    (eqToIso (congrArg fiber hpoint))
  let q := fieldSourceAbsoluteGaloisHom F Ω p
  have hvalue (σ : Gal(Ω/E)) : a (c σ) = q (σ.restrictScalars F) :=
    fieldSource_restriction_eq_point_transport F E Ω p r hpoint σ
  ext z
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨σ, rfl⟩ := c.surjective g
    exact ⟨σ.restrictScalars F, ⟨σ, rfl⟩, (hvalue σ).symm⟩
  · rintro ⟨σ, ⟨τ, rfl⟩, rfl⟩
    exact ⟨c τ, hvalue τ⟩

/-- For one boundary component it suffices to use any one actual path. -/
theorem boundaryStrictInertiaClosure_eq_single_range
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport)
    [Subsingleton (Component D)] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (point : Spec (.of Ω) ⟶ D.1.supportComplement) (E : Component D) :
    let : Field (boundaryStrictFractionField D E) := boundaryStrictFractionFieldField D hreg E
    ∀ t : fiber (boundaryStrictGenericPoint D hreg E ≫ boundaryStrictGenericMorphism D hreg E) ≅
        fiber point,
      boundaryStrictInertiaClosure D hreg point =
        (Subgroup.normalClosure
          ((geometricSourceHom (boundaryStrictGenericMorphism D hreg E)
            (boundaryStrictGenericPoint D hreg E) point t).toMonoidHom.range :
              Set π₁ᵉᵗ(point))).topologicalClosure := by
  intro hField t
  apply congrArg Subgroup.topologicalClosure
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro g ⟨E', t', a, rfl⟩
    have hE : E' = E := Subsingleton.elim E' E
    subst E'
    rw [continuousConjAut_eq_conj t t']
    have ha : geometricSourceHom (boundaryStrictGenericMorphism D hreg E)
        (boundaryStrictGenericPoint D hreg E) point t a ∈
        (geometricSourceHom (boundaryStrictGenericMorphism D hreg E)
          (boundaryStrictGenericPoint D hreg E) point t).toMonoidHom.range := ⟨a, rfl⟩
    exact Subgroup.Normal.conj_mem inferInstance _
      (Subgroup.subset_normalClosure ha) _
  · apply Subgroup.normalClosure_mono
    rintro g ⟨a, rfl⟩
    exact ⟨E, t, a, rfl⟩

attribute [local instance] normalizationInertiaImageAction

/-- The original nonabelian filling map has kernel generated, as a closed
normal subgroup, by the original inertia image at the chosen prime. -/
theorem boundaryFilling_ker_eq_normalClosure_normalizationInertia
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport)
    [Subsingleton (Component D)] [IsIntegral (D.1.supportComplement : Scheme)]
    (E₀ : Component D) (K Ω : Type u) [Field K] [Field Ω]
    [Algebra K Ω] [IsSepClosure K Ω] [IsSepClosed Ω]
    [Algebra (X.presheaf.stalk (componentPoint D E₀)) K]
    [IsFractionRing (X.presheaf.stalk (componentPoint D E₀)) K]
    [Algebra (X.presheaf.stalk (componentPoint D E₀)) Ω]
    [IsScalarTower (X.presheaf.stalk (componentPoint D E₀)) K Ω]
    (p : Spec (.of K) ⟶ D.1.supportComplement)
    (hp : p ≫ D.1.supportComplement.ι =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (componentPoint D E₀)) K)) ≫
        X.fromSpecStalk (componentPoint D E₀))
    (Q : Ideal (integralClosure (X.presheaf.stalk (componentPoint D E₀)) Ω)) [Q.IsMaximal] :
    (fundamentalGroupHom D.1.supportComplement.ι (ξ K Ω ≫ p)).toMonoidHom.ker =
      (Subgroup.normalClosure
        ((Q.inertia Gal(Ω/K)).map (fieldSourceAbsoluteGaloisHom K Ω p).toMonoidHom :
          Set π₁ᵉᵗ(ξ K Ω ≫ p))).topologicalClosure := by
  let x := componentPoint D E₀
  let A := X.presheaf.stalk x
  have : IsIntegrallyClosed A := IsNormalIntegral.stalk_isIntegrallyClosed x
  have : Algebra.IsAlgebraic A Ω :=
    (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := Ω)).mpr inferInstance
  have : FaithfulSMul A Ω :=
    (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := Ω)).mp
      (Module.IsTorsionFree.trans_faithfulSMul A K Ω)
  have : HenselianLocalRing (Localization.AtPrime Q) :=
    (integralClosure_primeLocalization_strictHenselian_of_algebraic A Ω Q).1
  have : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
    (integralClosure_primeLocalization_strictHenselian_of_algebraic A Ω Q).2
  let ψ := (IsLocalRing.residue (Localization.AtPrime Q)).comp
    (integralClosurePrimeBaseMap A Ω Q)
  have : IsLocalHom ψ := normalizationResiduePoint_isLocalHom A Ω Q
  let S := geometricStalk (Spec.map (CommRingCat.ofHom ψ))
  let E := FractionRing S
  let : Algebra K E := (normalizationStalkFractionBaseMap A K Ω Q).toAlgebra
  let : Algebra E Ω := (geometricStalkFractionToNormalizationField A Ω Q).toAlgebra
  have : IsScalarTower K E Ω := normalizationStalkFractionField_isScalarTower A K Ω Q
  have : IsSepClosure E Ω := normalizationStalkFractionField_isSepClosure A K Ω Q
  let r : Spec (.of E) ⟶ D.1.supportComplement := geometricStalkFractionFieldToComplement D x ψ
  have hcoeff : (algebraMap K E).comp (algebraMap A K) =
      (algebraMap S E).comp (geometricStalkStructureMap ψ) := by
    apply RingHom.ext
    intro a
    exact normalizationStalkFractionBaseMap_algebraMap A K Ω Q a
  have hr : ξ K E ≫ p = r := by
    apply (cancel_mono D.1.supportComplement.ι).mp
    rw [Category.assoc, hp]
    change Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ X.fromSpecStalk x) =
      r ≫ D.1.supportComplement.ι
    have hspec : Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A K)) =
      Spec.map (CommRingCat.ofHom ((algebraMap S E).comp (geometricStalkStructureMap ψ))) :=
      (Spec.map_comp (CommRingCat.ofHom (algebraMap A K))
        (CommRingCat.ofHom (algebraMap K E))).symm.trans
          (congrArg (fun f : A →+* E => Spec.map (CommRingCat.ofHom f)) hcoeff)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ X.fromSpecStalk x) hspec).trans
        (geometricStalkFractionFieldToComplement_comp_ι D x ψ).symm)
  have hpoint : ξ E Ω ≫ r = ξ K Ω ≫ p :=
    (congrArg (fun f => ξ E Ω ≫ f) hr.symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ p) (fieldGeometricPoint_comp K E Ω)))
  let tQ := eqToIso (congrArg fiber hpoint)
  have hnative := geometricSourceHom_range_fieldTower K E Ω p r hpoint
  have hrestriction : (AlgEquiv.restrictScalarsHom K : Gal(Ω/E) →* Gal(Ω/K)).range =
      Q.inertia Gal(Ω/K) := geometricStalkAbsoluteGalois_restriction_range A K Ω Q
  have : IsDiscreteValuationRing A := isDiscreteValuationRing_stalk_componentPoint D hreg E₀
  let : Field (boundaryStrictFractionField D E₀) := boundaryStrictFractionFieldField D hreg E₀
  obtain ⟨e, he⟩ := exists_boundaryStrictGenericMorphism_iso D hreg E₀ ψ
  obtain ⟨t, ht⟩ := exists_path_geometricSourceHom_range_eq_of_iso
    (boundaryStrictGenericMorphism D hreg E₀) r e he
    (boundaryStrictGenericPoint D hreg E₀) (ξ E Ω) (ξ K Ω ≫ p) tQ
  calc
    _ = boundaryStrictInertiaClosure D hreg (ξ K Ω ≫ p) :=
      ((boundary_quotient_1_1 D hreg).choose_spec Ω (ξ K Ω ≫ p)).2
    _ = (Subgroup.normalClosure
        ((geometricSourceHom (boundaryStrictGenericMorphism D hreg E₀)
          (boundaryStrictGenericPoint D hreg E₀) (ξ K Ω ≫ p) t).toMonoidHom.range :
            Set π₁ᵉᵗ(ξ K Ω ≫ p))).topologicalClosure :=
      boundaryStrictInertiaClosure_eq_single_range D hreg (ξ K Ω ≫ p) E₀ t
    _ = _ := congrArg (fun I : Subgroup π₁ᵉᵗ(ξ K Ω ≫ p) =>
        (Subgroup.normalClosure (I : Set π₁ᵉᵗ(ξ K Ω ≫ p))).topologicalClosure)
      (ht.trans (hnative.trans
        (congrArg (Subgroup.map (fieldSourceAbsoluteGaloisHom K Ω p).toMonoidHom) hrestriction)))

end EtaleFundamentalGroups.Cohomology
