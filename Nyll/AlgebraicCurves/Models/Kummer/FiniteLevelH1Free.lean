/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AbelianVarieties.Tate.AlgebraicPoints
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.SchemeTheory.Morphisms.GeometricallyIntegralAlgClosed
public import Nyll.AlgebraicCurves.Geometry.Picard.CurveModelAlgebraicPoints
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Pic0EquivPointsPicardRepresentability
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Kummer.AdicH1TateComparison
public import Nyll.AlgebraicCurves.Models.Points.RationalPointExistence
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdditiveCoefficientAction
public import Nyll.ProCGroups.Abelian.AddCommGroupBasisZmodPow
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Module.ULift
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.EssentialFiniteness

/-!
# Finite free cohomology at the original finite coefficient levels

The actual Picard representative gives one dimension and all prime-power
torsion cardinalities. The existing torsion-basis theorem then gives a
finite basis of the original finite-level cohomology through its actual
Kummer equivalence. The module structure is the original coefficient
action, obtained by applying cohomology to scalar endomorphisms.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicCurve GoodReductionJacobian
open JacobianVarieties.Picard.Proofs.Pic0PointsAbelJacobi.AlgebraicGeometry.RelPicard
open EtaleCohomology.Classical

namespace AlgebraicCurve.CurveModel

variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [IsCurveOver K F] (M : CurveModel K F)
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

include hℓ in
/-- The original finite coefficient groups in degree one have finite bases
of the same rank at every level, with their actual coefficient actions. -/
theorem exists_finiteLevelH1_basis :
    ∃ d : ℕ, ∀ n : ℕ,
      let : Module (ZMod (ℓ ^ (n + 1))) (finiteLevelCohomology M.C ℓ n 1) :=
        additiveCoefficientModule
          (constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{0} ⋙
            Sheaf.functorH M.C.smallEtaleTopology 1)
          (ZMod (ℓ ^ (n + 1))) (ellPowerCoefficients ℓ n)
      Nonempty (Module.Basis (Fin (2 * d)) (ZMod (ℓ ^ (n + 1)))
        (finiteLevelCohomology M.C ℓ n 1)) := by
  have : Algebra.EssFiniteType K F := DictGlue.essFiniteType_of_curveModel M
  have : IsIntegral M.C := M.isIntegral
  have : SmoothOfRelativeDimension 1 M.toBase := M.smooth
  have : GeometricallyIntegral M.toBase := geometricallyIntegral_of_isAlgClosed M.toBase
  obtain ⟨ε⟩ := M.nonempty_rationalPoint
  obtain ⟨A, f, G, hc, d, hA, hd, ⟨e⟩⟩ := M.exists_pic0_addEquiv_abelianPoints ε
  have : SmoothOfRelativeDimension d f := hd
  refine ⟨d, fun n => ?_⟩
  let : Module (ZMod (ℓ ^ (n + 1))) (finiteLevelCohomology M.C ℓ n 1) :=
    additiveCoefficientModule
      (constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{0} ⋙
        Sheaf.functorH M.C.smallEtaleTopology 1)
      (ZMod (ℓ ^ (n + 1))) (ellPowerCoefficients ℓ n)
  let E : Pic0.torsion K F (ℓ ^ (n + 1)) ≃+
      finiteLevelCohomology M.C ℓ n 1 :=
    M.kummerEllPowerCohomologyEquiv ε.1 ℓ hℓ n
  let ι : finiteLevelCohomology M.C ℓ n 1 →+ G.AlgPoints hc K :=
    e.toAddMonoidHom.comp
      ((Pic0.torsion K F (ℓ ^ (n + 1))).subtype.comp E.symm.toAddMonoidHom)
  have hι : Function.Injective ι := by
    intro a b hab
    apply E.symm.injective
    apply Subtype.ext
    exact e.injective hab
  have hιr : ∀ x : G.AlgPoints hc K,
      x ∈ ι.range ↔ ((ℓ ^ (n + 1) : ℕ) : ℤ) • x = 0 := by
    intro x
    constructor
    · rintro ⟨a, rfl⟩
      change ((ℓ ^ (n + 1) : ℕ) : ℤ) • e (E.symm a).val = 0
      rw [← map_zsmul]
      exact (congrArg e (Pic0.mem_torsion.mp (E.symm a).property)).trans e.map_zero
    · intro hx
      have ht : e.symm x ∈ Pic0.torsion K F (ℓ ^ (n + 1)) := by
        apply Pic0.mem_torsion.mpr
        apply e.injective
        rw [map_zsmul, e.apply_symm_apply, map_zero]
        exact hx
      let t : Pic0.torsion K F (ℓ ^ (n + 1)) := ⟨e.symm x, ht⟩
      refine ⟨E t, ?_⟩
      change e (E.symm (E t)).val = x
      exact (congrArg (fun z : Pic0.torsion K F (ℓ ^ (n + 1)) => e z.val)
        (E.symm_apply_apply t)).trans (e.apply_symm_apply x)
  apply AddCommGroup.nonempty_basis_zmod_pow_of_card_torsionBy ℓ
    (M := G.AlgPoints hc K) (2 * d) (n + 1) _ ι hι hιr
  intro j _
  exact G.natCard_algPoints_torsionBy hc hA d (ℓ ^ j)
    (by simpa only [Nat.cast_pow] using pow_ne_zero j hℓ.ne_zero)

include hℓ in
/-- Each original finite-level H¹ is finite free over its original cyclic
coefficient ring, in every characteristic with the exponent invertible. -/
theorem finite_free_finiteLevelH1 (n : ℕ) :
    let : Module (ZMod (ℓ ^ (n + 1))) (finiteLevelCohomology M.C ℓ n 1) :=
      additiveCoefficientModule
        (constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{0} ⋙
          Sheaf.functorH M.C.smallEtaleTopology 1)
        (ZMod (ℓ ^ (n + 1))) (ellPowerCoefficients ℓ n)
    Module.Free (ZMod (ℓ ^ (n + 1))) (finiteLevelCohomology M.C ℓ n 1) ∧
      Module.Finite (ZMod (ℓ ^ (n + 1))) (finiteLevelCohomology M.C ℓ n 1) := by
  intro sharedOwner1
  obtain ⟨d, hd⟩ := M.exists_finiteLevelH1_basis ℓ hℓ
  obtain ⟨basis⟩ := hd n
  exact ⟨Module.Free.of_basis basis, Module.Finite.of_basis basis⟩

end AlgebraicCurve.CurveModel
