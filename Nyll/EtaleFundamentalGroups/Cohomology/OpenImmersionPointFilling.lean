/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.CurvePointFillingInertia
public import Nyll.EtaleFundamentalGroups.Cohomology.NativeBoundaryNormalClosure
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceStalk
public import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisNaturality
public import Nyll.ProCGroups.Presentations.Profinite
public import Nyll.ProCGroups.Topologies.ContinuousMulEquiv

/-!
# The full filling kernel for the original open immersion

An open immersion whose omitted set is the specified rational point is
compared with that point's actual Cartier-divisor complement. The induced
isomorphism retains the original generic source and its literal Galois map.
Consequently the kernel of the original filling homomorphism is generated
by the full inertia at the same prime of the same local normalization.
-/

@[expose] public section

universe uGeom uField₁ uField₂

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale EtaleFundamentalGroups.Inertia
open ProCGroups.Presentations Yamaguchi26SolvableCoverings

namespace EtaleFundamentalGroups.Cohomology

private theorem closedNormalClosure_comap_equiv
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) (I : Subgroup H) :
    (closedNormalClosure (I : Set H)).comap e.toMonoidHom =
      closedNormalClosure (I.comap e.toMonoidHom : Set G) := by
  let N := closedNormalClosure (I.comap e.toMonoidHom : Set G)
  have hN : closedNormalClosure (I : Set H) ≤ N.comap e.symm.toMonoidHom := by
    apply closedNormalClosure_le_closed_normal
      ((closedNormalClosure_isClosed _).preimage e.symm.continuous_toFun)
    intro x hx
    apply subset_closedNormalClosure
    change e (e.symm x) ∈ I
    rw [e.apply_symm_apply]
    exact hx
  apply le_antisymm
  · intro x hx
    have h := hN hx
    change e.symm (e x) ∈ N at h
    rwa [e.symm_apply_apply] at h
  · apply closedNormalClosure_le_closed_normal
      ((closedNormalClosure_isClosed _).preimage e.continuous_toFun)
    intro x hx
    exact subset_closedNormalClosure (I : Set H) hx

private theorem pointedFundamentalGroupHom_ker
    {S T : Scheme.{uGeom}} {Ω : Type uGeom} [Field Ω]
    (f : S ⟶ T) (x : Spec (.of Ω) ⟶ S) (y : Spec (.of Ω) ⟶ T)
    (h : x ≫ f = y) :
    (pointedFundamentalGroupHom f x y h).toMonoidHom.ker =
      (fundamentalGroupHom f x).toMonoidHom.ker := by
  subst y
  rfl

private theorem pointedFundamentalGroupHom_fieldSource
    (K Ω : Type uGeom) [Field K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] [IsSepClosed Ω]
    {U V : Scheme.{uGeom}} [IsIntegral U] [IsIntegral V]
    (f : U ⟶ V) (g : Spec (.of K) ⟶ U) (g' : Spec (.of K) ⟶ V)
    (h : (ξ K Ω ≫ g) ≫ f = ξ K Ω ≫ g') (σ : Gal(Ω/K)) :
    pointedFundamentalGroupHom f (ξ K Ω ≫ g) (ξ K Ω ≫ g') h
        (fieldSourceAbsoluteGaloisHom K Ω g σ) =
      fieldSourceAbsoluteGaloisHom K Ω g' σ := by
  have htransport {x y : Spec (.of Ω) ⟶ V} (he : x = y) (a : π₁ᵉᵗ(x)) :
      continuousConjAut (eqToIso (congrArg fiber he)) a = he ▸ a := by
    subst y
    rfl
  have hσ : σ.restrictScalars K = σ := by
    ext z
    rfl
  have hn := fieldSourceAbsoluteGaloisHom_naturality K K Ω f g g' h σ
  exact (pointedFundamentalGroupHom_apply f (ξ K Ω ≫ g) (ξ K Ω ≫ g') h
    (fieldSourceAbsoluteGaloisHom K Ω g σ)).trans
      ((htransport h _).symm.trans
        (hn.trans (congrArg (fieldSourceAbsoluteGaloisHom K Ω g') hσ)))

private local instance integralOpenDominant
    {X U : Scheme.{uGeom}} [IsIntegral X] [IsIntegral U]
    (j : U ⟶ X) [IsOpenImmersion j] : IsDominant j :=
  ⟨j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j⟩

attribute [local instance] normalizationInertiaImageAction

private theorem boundaryFilling_ker_at_specified_point
    {X : Scheme.{uGeom}} [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport)
    [Subsingleton (Component D)] [IsIntegral (D.1.supportComplement : Scheme.{uGeom})]
    (E : Component D) (x : X) (hx : componentPoint D E = x)
    (K Ω : Type uGeom) [Field K] [Field Ω]
    [Algebra K Ω] [IsSepClosure K Ω] [IsSepClosed Ω]
    [Algebra (X.presheaf.stalk x) K] [IsFractionRing (X.presheaf.stalk x) K]
    [Algebra (X.presheaf.stalk x) Ω] [IsScalarTower (X.presheaf.stalk x) K Ω]
    (g : Spec (.of K) ⟶ D.1.supportComplement)
    (hg : g ≫ D.1.supportComplement.ι =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) K)) ≫
        X.fromSpecStalk x)
    (Q : Ideal (integralClosure (X.presheaf.stalk x) Ω)) [Q.IsMaximal] :
    (fundamentalGroupHom D.1.supportComplement.ι (ξ K Ω ≫ g)).toMonoidHom.ker =
      closedNormalClosure
        ((Q.inertia Gal(Ω/K)).map (fieldSourceAbsoluteGaloisHom K Ω g).toMonoidHom :
          Set π₁ᵉᵗ(ξ K Ω ≫ g)) := by
  subst x
  exact boundaryFilling_ker_eq_normalClosure_normalizationInertia D hreg E K Ω g hg Q

/-- Filling exactly the original rational point kills the full inertia of
the original local normalization prime. The comparison with a divisor
complement, and both generic-source maps, are constructed in the proof. -/
theorem singlePointOpenFilling_ker_eq_normalClosure
    {k : Type uGeom} [Field k] {X U : Scheme.{uGeom}}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] [IsIntegral U]
    (c : X ⟶ Spec (.of k)) [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (P : Spec (.of k) ⟶ X) (hP : P ≫ c = 𝟙 _)
    (j : U ⟶ X) [IsOpenImmersion j]
    (hrange : Set.range j = ({P (IsLocalRing.closedPoint k)} : Set X)ᶜ)
    (K Ω : Type uGeom) [Field K] [Field Ω]
    [Algebra K Ω] [IsSepClosure K Ω] [IsSepClosed Ω]
    (g : Spec (.of K) ⟶ U) [IsDominant g] [IsPreimmersion g] :
    let : IsDominant j :=
      ⟨j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j⟩
    let x := P (IsLocalRing.closedPoint k)
    let A := X.presheaf.stalk x
    let : Algebra A K := genericFieldSourceStalkAlgebra (g ≫ j) x
    let : IsFractionRing A K := genericFieldSourceStalk_isFractionRing (g ≫ j) x
    let : Algebra A Ω := ((algebraMap K Ω).comp (algebraMap A K)).toAlgebra
    let : IsScalarTower A K Ω := IsScalarTower.of_algebraMap_eq' rfl
    ∀ (Q : Ideal (integralClosure A Ω)) [Q.IsMaximal],
      (fundamentalGroupHom j (ξ K Ω ≫ g)).toMonoidHom.ker =
        closedNormalClosure
          ((Q.inertia Gal(Ω/K)).map (fieldSourceAbsoluteGaloisHom K Ω g).toMonoidHom :
            Set π₁ᵉᵗ(ξ K Ω ≫ g)) := by
  intro hDominant x A instAK fraction instAΩ tower Q hQ
  let D := curvePointDivisor c P hP
  have : IsIntegral (D.1.supportComplement : Scheme.{uGeom}) :=
    curvePointComplement_isIntegral c P hP
  have : Subsingleton (Component D) := curvePointDivisor_component_subsingleton c P hP
  have hr : Set.range j = Set.range D.1.supportComplement.ι := by
    rw [Scheme.Opens.range_ι]
    change Set.range j = (D.1.support : Set X)ᶜ
    rw [curvePointDivisor_support, hrange]
  let e := IsOpenImmersion.isoOfRangeEq j D.1.supportComplement.ι hr
  have he : e.hom ≫ D.1.supportComplement.ι = j :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let gD := g ≫ e.hom
  let xi := ξ K Ω ≫ g
  let xiD := ξ K Ω ≫ gD
  have hpoint : xi ≫ e.hom = xiD := Category.assoc _ _ _
  have htarget : xiD ≫ D.1.supportComplement.ι = xi ≫ j := by
    rw [← hpoint, Category.assoc, he]
  let E : FiniteEtale (D.1.supportComplement : Scheme.{uGeom}) ≌ FiniteEtale U :=
    MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme.{uGeom}) ⊤ e.symm
  have : (pullback e.hom).IsEquivalence := E.isEquivalence_functor
  let eπ : π₁ᵉᵗ(xi) ≃ₜ* π₁ᵉᵗ(xiD) :=
    ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
      (pointedFundamentalGroupHom e.hom xi xiD hpoint).toMonoidHom
      (pointedFundamentalGroupHom e.hom xi xiD hpoint).continuous_toFun
      (pointedFundamentalGroupHom_bijective e.hom xi xiD hpoint
        (fundamentalGroupHom_bijective_of_pullback_isEquivalence e.hom xi))
  let fD := pointedFundamentalGroupHom D.1.supportComplement.ι xiD (xi ≫ j) htarget
  have hchange (j' : U ⟶ X) (he' : j' = j) (h' : xi ≫ j' = xi ≫ j) :
      pointedFundamentalGroupHom j' xi (xi ≫ j) h' = fundamentalGroupHom j xi := by
    subst j'
    rfl
  have hcomp : fD.comp (ContinuousMonoidHom.toContinuousMonoidHom eπ) =
      fundamentalGroupHom j xi := by
    change (pointedFundamentalGroupHom D.1.supportComplement.ι xiD (xi ≫ j) htarget).comp
      (pointedFundamentalGroupHom e.hom xi xiD hpoint) = _
    exact (pointedFundamentalGroupHom_comp e.hom D.1.supportComplement.ι
      xi xiD (xi ≫ j) hpoint htarget).trans (hchange _ he _)
  let q := fieldSourceAbsoluteGaloisHom K Ω g
  let qD := fieldSourceAbsoluteGaloisHom K Ω gD
  have hq (σ : Gal(Ω/K)) : eπ (q σ) = qD σ :=
    pointedFundamentalGroupHom_fieldSource K Ω e.hom g gD hpoint σ
  let I := (Q.inertia Gal(Ω/K)).map q.toMonoidHom
  let ID := (Q.inertia Gal(Ω/K)).map qD.toMonoidHom
  have hI : ID.comap eπ.toMonoidHom = I := by
    ext a
    constructor
    · rintro ⟨σ, hσ, hσa⟩
      exact ⟨σ, hσ, eπ.injective ((hq σ).trans hσa)⟩
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨σ, hσ, (hq σ).symm⟩
  have hgeneric : gD ≫ D.1.supportComplement.ι =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ X.fromSpecStalk x := by
    change (g ≫ e.hom) ≫ D.1.supportComplement.ι = _
    rw [Category.assoc, he]
    exact (genericFieldSourceStalkMap_fromSpecStalk (g ≫ j) x).symm
  have hkerD : fD.toMonoidHom.ker = closedNormalClosure (ID : Set π₁ᵉᵗ(xiD)) := by
    rw [pointedFundamentalGroupHom_ker]
    exact boundaryFilling_ker_at_specified_point D
      (curvePointDivisor_isAmbientRegularAlongSupport c P hP)
      (curvePointDivisorComponent c P hP) x (curvePointDivisor_componentPoint c P hP)
      K Ω gD hgeneric Q
  have hker : (fundamentalGroupHom j xi).toMonoidHom.ker =
      fD.toMonoidHom.ker.comap eπ.toMonoidHom := by
    ext a
    change fundamentalGroupHom j xi a = 1 ↔ fD (eπ a) = 1
    rw [← hcomp]
    rfl
  rw [hker, hkerD, closedNormalClosure_comap_equiv, hI]

end EtaleFundamentalGroups.Cohomology
