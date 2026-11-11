/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationFiberAction
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianUnitMultiplicationAlgebraicPoints
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.AlgebraicPoints
public import Mathlib.Algebra.Algebra.Hom

/-!
# Actual multiplication fibres as algebraic division points

The fibre point is converted to the additive group of actual algebraic
points. Its division equation and monodromy translation are consequences
of the original finite étale cover and group scheme law.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry NeronModelInfra
open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_schemeNsmul_comp_eq_comp_schemeNsmul_of_hom.S17Glue

namespace GoodReductionJacobian.RelativeGroupLaw

variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
  {A : Scheme} {f : A ⟶ Spec (.of K)} [IsProper f] [Smooth f]
  (G : RelativeGroupLaw K f) (hc : G.IsCommutative)
  {Ω : Type} [Field Ω] [IsSepClosed Ω] [Algebra K Ω]

omit [IsAlgClosed K] in
/-- An actual multiplication-cover fibre point, expressed as an algebraic point. -/
def multiplicationFiberAlgPoint
    (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) f)
    (n : ℕ+) (z : (FiniteEtale.fiber ξ.1).obj (G.multiplicationCover hc n)) :
    G.AlgPoints hc Ω :=
  AlgPoints.ofPoint
    ⟨(G.multiplicationFiberPoint hc ξ.1 n z).1,
      (G.multiplicationFiberPoint hc ξ.1 n z).2.trans ξ.2⟩

omit [IsAlgClosed K] in
/-- The algebraic point constructed from the fibre satisfies its actual division equation. -/
theorem nsmul_multiplicationFiberAlgPoint
    (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) f)
    (n : ℕ+) (z : (FiniteEtale.fiber ξ.1).obj (G.multiplicationCover hc n)) :
    (n : ℕ) • G.multiplicationFiberAlgPoint hc ξ n z = AlgPoints.ofPoint ξ := by
  have hn : IsUnit ((n : ℕ) : K) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.ne_zero)
  exact UnitMultiplication.nsmul_fiberAlgPoint G hc ξ ⟨n, hn⟩ z

/-- Actual monodromy on the fibre is addition of the actual torsion point,
also after passage to the algebraic-point group over the geometric field. -/
theorem multiplicationFiberAlgPoint_smul
    (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) f)
    (n : ℕ+)
    (τ : FiniteEtale.fiber ξ.1 ≅ FiniteEtale.fiber (G.one (𝟙 (Spec (.of K)))).1)
    (g : π₁ᵉᵗ(ξ.1))
    (z : (FiniteEtale.fiber ξ.1).obj (G.multiplicationCover hc n)) :
    G.multiplicationFiberAlgPoint hc ξ n (g • z) =
      G.multiplicationFiberAlgPoint hc ξ n z +
        AlgPoints.map (L := G) (hc := hc) (T := K) (T' := Ω) (Algebra.ofId K Ω)
          (G.multiplicationMonodromy hc n (continuousConjAut τ g)).1 := by
  have hn : IsUnit ((n : ℕ) : K) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.ne_zero)
  exact UnitMultiplication.fiberAlgPoint_smul G hc ξ ⟨n, hn⟩ τ g z

end GoodReductionJacobian.RelativeGroupLaw
