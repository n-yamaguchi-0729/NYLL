/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.NativeBoundaryFillingInertia
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceStalk
public import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.HomInvertibleKerCompEqId
public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.EffectiveCartierIdeal
public import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.SmoothOfRelativeDimensionDVRStalkSection

/-!
# Filling an actual point of a smooth curve

The divisor is the kernel ideal of the specified rational point. Its
support is that point, it has exactly one component, and smoothness gives
the required regular local ring. The normalization inertia formula uses
the original generic field source and its induced local-ring algebra.
No boundary-component or generic-source comparison is additional input.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory
open ProCGroups.Abelian Yamaguchi26SolvableCoverings
open EtaleFundamentalGroups.Inertia

namespace EtaleFundamentalGroups.Cohomology

section PointDivisor

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (c : X ⟶ Spec (.of k)) [IsSeparated c] [SmoothOfRelativeDimension 1 c]
  (p : Spec (.of k) ⟶ X) (hp : p ≫ c = 𝟙 _)

/-- The effective Cartier divisor defined by the original rational point. -/
def curvePointDivisor : X.EffectiveCartierDivisor :=
  ⟨p.ker, (Scheme.Hom.isInvertible_ker_of_comp_eq_id p hp).isEffectiveCartier⟩

/-- The constructed divisor has exactly the specified point as support. -/
theorem curvePointDivisor_support :
    ((curvePointDivisor c p hp).1.support : Set X) = {p (IsLocalRing.closedPoint k)} := by
  have : IsClosedImmersion p := isClosedImmersion_of_comp_eq_id c p hp
  change (p.ker.support : Set X) = _
  rw [Scheme.Hom.support_ker, p.isClosedEmbedding.isClosed_range.closure_eq]
  exact Set.range_eq_singleton_iff.mpr fun y => congrArg p (Subsingleton.elim y _)

include c hp in
private theorem curvePointDivisor_subschemeι_eq (z : p.ker.subscheme) :
    p.ker.subschemeι z = p (IsLocalRing.closedPoint k) := by
  have hr : Set.range p.ker.subschemeι = {p (IsLocalRing.closedPoint k)} :=
    p.ker.range_subschemeι.trans (curvePointDivisor_support c p hp)
  exact Set.mem_singleton_iff.mp (hr ▸ Set.mem_range_self z)

private theorem curvePointDivisor_subscheme_subsingleton :
    Subsingleton (curvePointDivisor c p hp).1.subscheme := by
  constructor
  intro a b
  apply p.ker.subschemeι.isEmbedding.injective
  exact (curvePointDivisor_subschemeι_eq c p hp a).trans
    (curvePointDivisor_subschemeι_eq c p hp b).symm

/-- The subscheme defined by the rational point is irreducible. -/
theorem curvePointDivisor_subscheme_irreducible :
    IrreducibleSpace (curvePointDivisor c p hp).1.subscheme := by
  have : Subsingleton (curvePointDivisor c p hp).1.subscheme :=
    curvePointDivisor_subscheme_subsingleton c p hp
  have : Nonempty (curvePointDivisor c p hp).1.subscheme :=
    ⟨p.toImage (IsLocalRing.closedPoint k)⟩
  exact { toPreirreducibleSpace := inferInstance, toNonempty := inferInstance }

/-- There is only one boundary component; this is proved from the actual
point ideal, rather than imposed on the curve. -/
theorem curvePointDivisor_component_subsingleton :
    Subsingleton (Component (curvePointDivisor c p hp)) := by
  have : IrreducibleSpace p.ker.subscheme :=
    curvePointDivisor_subscheme_irreducible c p hp
  constructor
  intro E F
  apply Subtype.ext
  have hE : E.val = (Set.univ : Set p.ker.subscheme) := by
    have h : E.val ∈ irreducibleComponents p.ker.subscheme := E.property
    have hmem : E.val ∈ ({Set.univ} : Set (Set p.ker.subscheme)) :=
      (irreducibleComponents_eq_singleton (X := p.ker.subscheme)) ▸ h
    exact Set.mem_singleton_iff.mp hmem
  have hF : F.val = (Set.univ : Set p.ker.subscheme) := by
    have h : F.val ∈ irreducibleComponents p.ker.subscheme := F.property
    have hmem : F.val ∈ ({Set.univ} : Set (Set p.ker.subscheme)) :=
      (irreducibleComponents_eq_singleton (X := p.ker.subscheme)) ▸ h
    exact Set.mem_singleton_iff.mp hmem
  exact hE.trans hF.symm

/-- The unique component of the actual point divisor. -/
def curvePointDivisorComponent : Component (curvePointDivisor c p hp) := by
  have : IrreducibleSpace (curvePointDivisor c p hp).1.subscheme :=
    curvePointDivisor_subscheme_irreducible c p hp
  exact ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; exact Set.mem_singleton _⟩

/-- Its component generic point is the original rational point. -/
theorem curvePointDivisor_componentPoint :
    componentPoint (curvePointDivisor c p hp) (curvePointDivisorComponent c p hp) =
      p (IsLocalRing.closedPoint k) := by
  exact curvePointDivisor_subschemeι_eq c p hp _

variable [IsIntegral X]

/-- Smoothness makes the ambient curve regular at the actual divisor. -/
theorem curvePointDivisor_isAmbientRegularAlongSupport :
    (curvePointDivisor c p hp).IsAmbientRegularAlongSupport := by
  intro x hx
  have hx' : x = p (IsLocalRing.closedPoint k) := by
    rwa [curvePointDivisor_support c p hp, Set.mem_singleton_iff] at hx
  subst x
  have : IsDiscreteValuationRing (X.presheaf.stalk (p (IsLocalRing.closedPoint k))) :=
    SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_section c p hp
  exact inferInstanceAs (IsRegularLocalRing (X.presheaf.stalk (p (IsLocalRing.closedPoint k))))

variable [IsLocallyNoetherian X]

/-- Removing the actual point leaves an integral open curve. -/
theorem curvePointComplement_isIntegral :
    IsIntegral ((curvePointDivisor c p hp).1.supportComplement : Scheme.{u}) := by
  have : ConnectedSpace (curvePointDivisor c p hp).1.supportComplement :=
    boundaryComplement_connectedSpace (curvePointDivisor c p hp)
      (curvePointDivisor_isAmbientRegularAlongSupport c p hp)
  exact isIntegral_of_isOpenImmersion (curvePointDivisor c p hp).1.supportComplement.ι

end PointDivisor

local instance boundaryInclusionDominant {X : Scheme.{u}}
    (D : X.EffectiveCartierDivisor) : IsDominant D.1.supportComplement.ι :=
  AlgebraicGeometry.Opens.isDominant_ι D.dense_supportComplement

attribute [local instance] normalizationInertiaImageAction

/-- The original generic source supplies the entire local coefficient
square in the native boundary inertia formula. -/
theorem boundaryFillingAbelianization_ker_eq_normalizationInertia_of_genericSource
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport)
    [Subsingleton (Component D)] [IsIntegral (D.1.supportComplement : Scheme.{u})]
    (E : Component D) (x : X) (hx : componentPoint D E = x)
    (K Ω : Type u) [Field K] [Field Ω]
    [Algebra K Ω] [IsSepClosure K Ω] [IsSepClosed Ω]
    (g : Spec (.of K) ⟶ D.1.supportComplement) [IsDominant g] [IsPreimmersion g] :
    let A := X.presheaf.stalk x
    let : Algebra A K := genericFieldSourceStalkAlgebra (g ≫ D.1.supportComplement.ι) x
    let : IsFractionRing A K :=
      genericFieldSourceStalk_isFractionRing (g ≫ D.1.supportComplement.ι) x
    let : Algebra A Ω := ((algebraMap K Ω).comp (algebraMap A K)).toAlgebra
    let : IsScalarTower A K Ω := IsScalarTower.of_algebraMap_eq' rfl
    ∀ (Q : Ideal (integralClosure A Ω)) [Q.IsMaximal],
      (TopologicalAbelianization.map
          (fundamentalGroupHom D.1.supportComplement.ι (ξ K Ω ≫ g))).toMonoidHom.ker =
        (Q.inertia Gal(Ω/K)).map
          ((TopologicalAbelianization.mk π₁ᵉᵗ(ξ K Ω ≫ g)).comp
            (fieldSourceAbsoluteGaloisHom K Ω g).toMonoidHom) := by
  subst x
  intro A instAK fraction instAΩ tower Q hQ
  exact boundaryFillingAbelianization_ker_eq_normalizationInertia D hreg E K Ω g
    (genericFieldSourceStalkMap_fromSpecStalk
      (g ≫ D.1.supportComplement.ι) (componentPoint D E)).symm Q

/-- For the actual point ideal, filling the point kills exactly the image
of the original chosen normalization-prime inertia, including wild inertia. -/
theorem curvePointFillingAbelianization_ker_eq_normalizationInertia
    {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (c : X ⟶ Spec (.of k)) [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (p : Spec (.of k) ⟶ X) (hp : p ≫ c = 𝟙 _)
    (K Ω : Type u) [Field K] [Field Ω]
    [Algebra K Ω] [IsSepClosure K Ω] [IsSepClosed Ω] :
    let D := curvePointDivisor c p hp
    let : IsIntegral (D.1.supportComplement : Scheme.{u}) := curvePointComplement_isIntegral c p hp
    ∀ (g : Spec (.of K) ⟶ D.1.supportComplement) [IsDominant g] [IsPreimmersion g],
      let A := X.presheaf.stalk (p (IsLocalRing.closedPoint k))
      let : Algebra A K := genericFieldSourceStalkAlgebra (g ≫ D.1.supportComplement.ι)
        (p (IsLocalRing.closedPoint k))
      let : IsFractionRing A K := genericFieldSourceStalk_isFractionRing
        (g ≫ D.1.supportComplement.ι) (p (IsLocalRing.closedPoint k))
      let : Algebra A Ω := ((algebraMap K Ω).comp (algebraMap A K)).toAlgebra
      let : IsScalarTower A K Ω := IsScalarTower.of_algebraMap_eq' rfl
      ∀ (Q : Ideal (integralClosure A Ω)) [Q.IsMaximal],
        (TopologicalAbelianization.map
            (fundamentalGroupHom D.1.supportComplement.ι (ξ K Ω ≫ g))).toMonoidHom.ker =
          (Q.inertia Gal(Ω/K)).map
            ((TopologicalAbelianization.mk π₁ᵉᵗ(ξ K Ω ≫ g)).comp
              (fieldSourceAbsoluteGaloisHom K Ω g).toMonoidHom) := by
  intro D hIntegral g hgdom hgpre
  have : Subsingleton (Component D) := curvePointDivisor_component_subsingleton c p hp
  exact boundaryFillingAbelianization_ker_eq_normalizationInertia_of_genericSource
    D (curvePointDivisor_isAmbientRegularAlongSupport c p hp)
    (curvePointDivisorComponent c p hp) (p (IsLocalRing.closedPoint k))
    (curvePointDivisor_componentPoint c p hp) K Ω g

end EtaleFundamentalGroups.Cohomology
