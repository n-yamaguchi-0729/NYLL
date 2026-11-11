/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.CartierBoundary.Quotient
public import Nyll.ProCGroups.Abelian.TopologicalAbelianizationKernel
public import Nyll.ProCGroups.Topologies.ContinuousMulEquiv
public import Nyll.ProCGroups.Topologies.QuotientMaps
public import Mathlib.CategoryTheory.Endomorphism
public import Nyll.ProCGroups.Topologies.ContinuousMonoidHom

/-!
# Filling one boundary component on the full abelian fundamental group

The boundary exact sequence uses the original strict-Henselian generic
morphism. After abelianization, changing its geometric path has no effect.
If the boundary has one component, its image is already a closed subgroup:
it is the continuous image of a compact fundamental group. Consequently
the kernel of the filling map is this actual inertia image, without taking
any prime-to-characteristic quotient or discarding wild inertia.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory
open ProCGroups.Abelian
open Yamaguchi26SolvableCoverings

namespace EtaleFundamentalGroups.Cohomology

private theorem map_conj_to_commGroup {G A : Type*} [Group G] [CommGroup A]
    (f : G →* A) (g a : G) : f (MulAut.conj g a) = f a := by
  change f (g * a * g⁻¹) = f a
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (point : Spec (.of Ω) ⟶ D.1.supportComplement)

/-- The original strict-local inertia map, transported to the specified
base point and then mapped to the full topological abelianization. -/
def strictBoundaryAbelianizationHom (E : Component D) :
    let : Field (boundaryStrictFractionField D E) := boundaryStrictFractionFieldField D hreg E
    (fiber (boundaryStrictGenericPoint D hreg E ≫ boundaryStrictGenericMorphism D hreg E) ≅
      fiber point) →
      π₁ᵉᵗ(boundaryStrictGenericPoint D hreg E) →ₜ*
        TopologicalAbelianization π₁ᵉᵗ(point) := by
  intro hField t
  exact (TopologicalAbelianization.mkₜ π₁ᵉᵗ(point)).comp
    ((ContinuousMonoidHom.toContinuousMonoidHom (continuousConjAut t)).comp
      (fundamentalGroupHom (boundaryStrictGenericMorphism D hreg E)
        (boundaryStrictGenericPoint D hreg E)))

omit [IsSepClosed Ω] in
/-- The full abelian inertia map does not depend on its geometric path. -/
theorem strictBoundaryAbelianizationHom_eq (E : Component D) :
    let : Field (boundaryStrictFractionField D E) := boundaryStrictFractionFieldField D hreg E
    ∀ (t₁ t₂ :
      fiber (boundaryStrictGenericPoint D hreg E ≫ boundaryStrictGenericMorphism D hreg E) ≅
        fiber point),
      strictBoundaryAbelianizationHom D hreg point E t₁ =
        strictBoundaryAbelianizationHom D hreg point E t₂ := by
  intro hField t₁ t₂
  apply ContinuousMonoidHom.ext
  intro a
  change TopologicalAbelianization.mk π₁ᵉᵗ(point)
      (continuousConjAut t₁
        (fundamentalGroupHom (boundaryStrictGenericMorphism D hreg E)
          (boundaryStrictGenericPoint D hreg E) a)) =
    TopologicalAbelianization.mk π₁ᵉᵗ(point)
      (continuousConjAut t₂
        (fundamentalGroupHom (boundaryStrictGenericMorphism D hreg E)
          (boundaryStrictGenericPoint D hreg E) a))
  exact ((congrArg (TopologicalAbelianization.mk π₁ᵉᵗ(point))
    (continuousConjAut_eq_conj t₁ t₂
      (fundamentalGroupHom (boundaryStrictGenericMorphism D hreg E)
        (boundaryStrictGenericPoint D hreg E) a))).trans
    (map_conj_to_commGroup (TopologicalAbelianization.mk π₁ᵉᵗ(point))
      (Aut.of (t₁.symm ≪≫ t₂)) _)).symm

variable [ConnectedSpace X] [Subsingleton (Component D)]

/-- Filling a single regular boundary component kills exactly its actual
strict-local inertia image in the full abelian fundamental group. -/
theorem boundaryFillingAbelianization_ker (E : Component D) :
    let : Field (boundaryStrictFractionField D E) := boundaryStrictFractionFieldField D hreg E
    ∀ (t :
      fiber (boundaryStrictGenericPoint D hreg E ≫ boundaryStrictGenericMorphism D hreg E) ≅
        fiber point),
      (TopologicalAbelianization.map
        (fundamentalGroupHom D.1.supportComplement.ι point)).toMonoidHom.ker =
          (strictBoundaryAbelianizationHom D hreg point E t).toMonoidHom.range := by
  intro hField t
  have : ConnectedSpace D.1.supportComplement := boundaryComplement_connectedSpace D hreg
  let q := TopologicalAbelianization.mkₜ π₁ᵉᵗ(point)
  let localMap := strictBoundaryAbelianizationHom D hreg point E t
  let I := localMap.toMonoidHom.range
  have hIclosed : IsClosed (I : Set (TopologicalAbelianization π₁ᵉᵗ(point))) :=
    ProCGroups.ContinuousMonoidHom.isClosed_range localMap
  have hgenerators : boundaryStrictInertiaGenerators D hreg point ⊆
      I.comap q.toMonoidHom := by
    rintro g ⟨E', t', a, rfl⟩
    have hE : E' = E := Subsingleton.elim E' E
    subst E'
    refine ⟨a, ?_⟩
    exact DFunLike.congr_fun
      (strictBoundaryAbelianizationHom_eq D hreg point E t t') a
  have hclosure : boundaryStrictInertiaClosure D hreg point ≤
      I.comap q.toMonoidHom :=
    Subgroup.topologicalClosure_minimal _
      (Subgroup.normalClosure_le_normal hgenerators)
      (hIclosed.preimage q.continuous_toFun)
  have hkernel : (fundamentalGroupHom D.1.supportComplement.ι point).toMonoidHom.ker =
      boundaryStrictInertiaClosure D hreg point :=
    ((boundary_quotient_1_1 D hreg).choose_spec Ω point).2
  rw [TopologicalAbelianization.ker_map_of_surjective
    (fundamentalGroupHom D.1.supportComplement.ι point)
    (boundaryComplement_fundamentalGroupHom_surjective D hreg point), hkernel]
  apply le_antisymm
  · rintro a ⟨g, hg, rfl⟩
    exact hclosure hg
  · rintro a ⟨γ, rfl⟩
    refine ⟨continuousConjAut t
      (fundamentalGroupHom (boundaryStrictGenericMorphism D hreg E)
        (boundaryStrictGenericPoint D hreg E) γ), ?_, rfl⟩
    exact Subgroup.le_topologicalClosure _
      (Subgroup.subset_normalClosure ⟨E, t, γ, rfl⟩)

/-- The original filling map identifies the quotient by the full inertia
image with the full abelian fundamental group of the filled curve. -/
def boundaryFillingAbelianizationEquiv (E : Component D) :
    let : Field (boundaryStrictFractionField D E) := boundaryStrictFractionFieldField D hreg E
    ∀ (t :
      fiber (boundaryStrictGenericPoint D hreg E ≫ boundaryStrictGenericMorphism D hreg E) ≅
        fiber point),
      (TopologicalAbelianization π₁ᵉᵗ(point) ⧸
        (strictBoundaryAbelianizationHom D hreg point E t).toMonoidHom.range) ≃ₜ*
          TopologicalAbelianization π₁ᵉᵗ(point ≫ D.1.supportComplement.ι) := by
  intro hField t
  have : ConnectedSpace D.1.supportComplement := boundaryComplement_connectedSpace D hreg
  let f := TopologicalAbelianization.map
    (fundamentalGroupHom D.1.supportComplement.ι point)
  let I := (strictBoundaryAbelianizationHom D hreg point E t).toMonoidHom.range
  have hker : f.toMonoidHom.ker = I := boundaryFillingAbelianization_ker D hreg point E t
  let F := ProCGroups.QuotientGroup.liftₜ I f hker.symm.le
  apply ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
    F.toMonoidHom F.continuous_toFun
  constructor
  · apply (QuotientGroup.injective_lift_iff I f.toMonoidHom hker.symm.le).mpr
    exact hker.symm
  · intro y
    obtain ⟨a, ha⟩ := TopologicalAbelianization.surjective_map_of_surjective
      (fundamentalGroupHom D.1.supportComplement.ι point)
      (boundaryComplement_fundamentalGroupHom_surjective D hreg point) y
    exact ⟨QuotientGroup.mk' I a, ha⟩

/-- The quotient equivalence retains the original inclusion-induced map
on every original fundamental-group element. -/
theorem boundaryFillingAbelianizationEquiv_apply_mk (E : Component D) :
    let : Field (boundaryStrictFractionField D E) := boundaryStrictFractionFieldField D hreg E
    ∀ (t :
      fiber (boundaryStrictGenericPoint D hreg E ≫ boundaryStrictGenericMorphism D hreg E) ≅
        fiber point) (g : π₁ᵉᵗ(point)),
      boundaryFillingAbelianizationEquiv D hreg point E t
        (QuotientGroup.mk' (strictBoundaryAbelianizationHom D hreg point E t).toMonoidHom.range
          (TopologicalAbelianization.mk π₁ᵉᵗ(point) g)) =
        TopologicalAbelianization.mk π₁ᵉᵗ(point ≫ D.1.supportComplement.ι)
          (fundamentalGroupHom D.1.supportComplement.ι point g) := by
  intro hField t g
  rfl

end EtaleFundamentalGroups.Cohomology
