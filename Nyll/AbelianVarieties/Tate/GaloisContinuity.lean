/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AbelianVarieties.Tate.FullTateModule
public import Nyll.AbelianVarieties.Tate.RestrictedComparison
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Mathlib.Topology.ContinuousOn
public import Nyll.AbelianVarieties.Tate.Representation

/-!
# Continuous Galois action on geometric Tate modules

The finite-level action is transported from the existing continuous action on points
of the actual finite étale multiplication kernel. The inverse-limit topology then
makes the action jointly continuous in the automorphism and the Tate vector.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra ProCGroups
open scoped AlgebraicGeometry.FiniteEtale

namespace GoodReductionJacobian.RelativeGroupLaw

variable {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
  {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
  (L : RelativeGroupLaw K f) (hc : L.IsCommutative)

/-- Restrict the actual coefficient-field action to a torsion level. -/
def geometricTorsionAction (n : ℕ+) (σ : Ω ≃ₐ[K] Ω)
    (x : torsionLevel (L.AlgPoints hc Ω) n) : torsionLevel (L.AlgPoints hc Ω) n :=
  ⟨σ • x.val, by
    change (n : ℕ) • DistribSMul.toAddMonoidHom (L.AlgPoints hc Ω) σ x.val = 0
    rw [← map_nsmul, x.property, map_zero]⟩

attribute [local instance] FullTateModule.torsionLevelTopology

variable [IsProper f] (d : ℕ) [SmoothOfRelativeDimension d f]

include d

/-- Joint continuity on prime-to-characteristic torsion follows from the finite étale
kernel, without assuming continuity of the point action as an extra hypothesis. -/
theorem continuous_geometricTorsionAction (n : ℕ+) (hn : (n : K) ≠ 0) :
    Continuous (fun z : (Ω ≃ₐ[K] Ω) × torsionLevel (L.AlgPoints hc Ω) n =>
      L.geometricTorsionAction hc n z.1 z.2) := by
  have : DiscreteTopology (torsionLevel (L.AlgPoints hc Ω) n) := discreteTopology_bot _
  let X := L.finiteEtaleTorsion hc d n hn
  let e : torsionLevel (L.AlgPoints hc Ω) n ≃
      (Over.mk (Spec.algebraMap K Ω) ⟶ X.toComma) :=
    (L.torsionLevelEquivAlgSchemeKerPoints hc Ω n).trans
      (schemeHomOverEquivOverHom (Spec.algebraMap K Ω) (L.schemeKerStr (n : ℕ)))
  have equivariant (σ : Ω ≃ₐ[K] Ω) (x : torsionLevel (L.AlgPoints hc Ω) n) :
      e (L.geometricTorsionAction hc n σ x) = σ • e x := by
    apply Over.OverMorphism.ext
    exact L.torsionLevelEquivAlgSchemeKerPoints_map hc σ.toAlgHom n x
      (L.geometricTorsionAction hc n σ x) rfl
  apply continuous_prod_of_discrete_right.mpr
  intro x
  have : DiscreteTopology (Over.mk (Spec.algebraMap K Ω) ⟶ X.toComma) :=
    discreteTopology_bot _
  have he : Continuous e.symm := continuous_of_discreteTopology
  have horbit : Continuous (fun σ : Ω ≃ₐ[K] Ω => σ • e x) :=
    continuous_id.smul continuous_const
  have h := he.comp horbit
  apply h.congr
  intro σ
  exact (congrArg e.symm (equivariant σ x)).symm.trans (e.symm_apply_apply _)

/-- The actual prime-power representation is jointly continuous for the Krull topology
and the canonical inverse-limit topology on the Tate module. -/
theorem continuous_geometricPrimePowerTateAction
    (p : ℕ) [Fact p.Prime] (hp : (p : K) ≠ 0) :
    Continuous (fun z : (Ω ≃ₐ[K] Ω) × TateModule p (L.AlgPoints hc Ω) =>
      TateModule.rep p (L.AlgPoints hc Ω) (Ω ≃ₐ[K] Ω) z.1 z.2) := by
  apply TateModule.continuous_rep_of_continuous_levels
  intro n
  have hn : (n.1 : K) ≠ 0 := by
    obtain ⟨k, hk⟩ := n.property
    rw [← hk]
    change (((p ^ k : ℕ) : K)) ≠ 0
    rw [Nat.cast_pow]
    exact pow_ne_zero k hp
  exact L.continuous_geometricTorsionAction hc d n.1 hn

end GoodReductionJacobian.RelativeGroupLaw
