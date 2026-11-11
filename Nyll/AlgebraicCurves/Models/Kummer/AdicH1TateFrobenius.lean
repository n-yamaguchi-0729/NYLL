/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AbelianVarieties.Tate.PrimePower
public import Nyll.AbelianVarieties.Tate.Representation
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.ConstantExtension.SemilinearAction
public import Nyll.AlgebraicCurves.Models.Kummer.AdicH1TateComparison
public import Nyll.AlgebraicCurves.Models.Kummer.DivisorClassCohomologyInjection
public import Nyll.AlgebraicCurves.Models.Kummer.FiniteAdicH1
public import Nyll.AlgebraicCurves.Models.Kummer.ProperKummerFrobenius
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Frobenius.RationalAdic
public import Nyll.EtaleFundamentalGroups.Cohomology.AdicH1IsomorphismPullback
public import Nyll.EtaleFundamentalGroups.Cohomology.KummerPowerCoefficients
public import Nyll.EtaleFundamentalGroups.Cohomology.SchemePullback
public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChange
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Logic.Function.Iterate

/-!
# Original Tate action and geometric Frobenius on classical adic H¹

The finite proper Kummer Frobenius formula passes through the existing
compatible roots coordinates, actual integral inverse limit, and original
rational tensor product. The comparison retains pullback by the specified
isomorphism from the curve model to the literal constant extension. No
arithmetic equivariance of the chosen primitive roots is assumed.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open EtaleCohomology EtaleCohomology.Classical EtaleFundamentalGroups.Cohomology
open scoped TensorProduct

namespace AlgebraicCurve.CurveModel

/-- Scalar extension preserves the proved intertwining square of the same linear equivalence. -/
private theorem linearEquiv_baseChange_intertwines
    {R : Type*} {S : Type*} {V : Type*} {W : Type*}
    [CommSemiring R] [Semiring S] [Algebra R S]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    (E : V ≃ₗ[R] W) (b : Module.End R V) (a : Module.End R W)
    (h : ∀ v : V, a (E v) = E (b v)) (x : TensorProduct R S V) :
    a.baseChange S (E.baseChange R S V W x) =
      E.baseChange R S V W (b.baseChange S x) := by
  have hm : a.comp E.toLinearMap = E.toLinearMap.comp b := LinearMap.ext h
  have hq := congrArg (fun t : V →ₗ[R] W => t.baseChange S) hm
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at hq
  exact LinearMap.congr_fun hq x

variable {k K F : Type} [Field k] [Fintype k] [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K]
  [Field F] [Algebra K F] [Algebra.EssFiniteType K F] [IsCurveOver K F]
  (M : CurveModel K F) (C : Scheme) [C.Over (Spec (.of k))]
  (e : M.C ≅ pullback (C ↘ Spec (.of k)) (SmoothProperCurve.specMap k K))
  (he : e.hom ≫ pullback.snd (C ↘ Spec (.of k))
    (SmoothProperCurve.specMap k K) = M.toBase)
  {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ M.C)
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

local notation "Y" => pullback (C ↘ Spec (CommRingCat.of k)) (SmoothProperCurve.specMap k K)

/-- Finite cyclic coordinates retain the actual geometric Frobenius and
the original `q`-weighted inverse arithmetic action on Pic0 torsion. -/
theorem kummerEllPowerCohomologyEquiv_geometricFrobenius (n : ℕ)
    (x : Pic0.torsion K F (ℓ ^ (n + 1))) :
    let g := M.constantSemilinearAction (C ↘ Spec (.of k)) e he
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K)
    finiteLevelCohomologyPullback ℓ (Scheme.constantBaseChangeFrobenius k K C) n 1
        (finiteLevelCohomologyPullback ℓ e.inv n 1
          (M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n x)) =
      finiteLevelCohomologyPullback ℓ e.inv n 1
        (M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n ((Fintype.card k) • (g⁻¹ • x))) := by
  intro g
  let N : ℕ+ := ⟨ℓ ^ (n + 1), pow_pos (Fact.out : ℓ.Prime).pos (n + 1)⟩
  have hN : IsUnit ((N : ℕ) : K) := by
    change IsUnit ((ℓ ^ (n + 1) : ℕ) : K)
    simpa only [Nat.cast_pow] using hℓ.pow (n + 1)
  let A := ellPowerCoefficients.{0} ℓ n
  let B := AddCommGrpCat.of (Additive (rootsOfUnity (ℓ ^ (n + 1)) K))
  let α : A ≅ B := (ellPowerRootsCoefficientEquiv K ℓ hℓ n).toAddCommGrpIso
  let H := constantSheaf (Y).smallEtaleTopology AddCommGrpCat.{0} ⋙
    Sheaf.functorH (Y).smallEtaleTopology 1
  let κ (z : Pic0.torsion K F (ℓ ^ (n + 1))) :=
    finiteLevelCohomologyPullback ℓ e.inv n 1
      (M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n z)
  let ρ (z : Pic0.torsion K F (ℓ ^ (n + 1))) :=
    constantCohomologyPullback e.inv B 1 (M.kummerTorsionCohomology N hN xi z)
  have hκ (z : Pic0.torsion K F (ℓ ^ (n + 1))) : H.map α.hom (κ z) = ρ z := by
    have hn := constantCohomologyPullback_naturality e.inv A B α.hom 1
      (M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n z)
    exact hn.trans (congrArg (constantCohomologyPullback e.inv B 1)
      (M.kummerEllPowerCohomologyEquiv_roots xi ℓ hℓ n z))
  apply (H.mapIso α).addCommGroupIsoToAddEquiv.injective
  have hn := constantCohomologyPullback_naturality
    (Scheme.constantBaseChangeFrobenius k K C) A B α.hom 1 (κ x)
  have hf := M.kummerTorsionCohomology_geometricFrobenius C e he N hN xi x
  exact hn.trans ((congrArg
    (constantCohomologyPullback (Scheme.constantBaseChangeFrobenius k K C) B 1)
      (hκ x)).trans (hf.trans (hκ ((Fintype.card k) • (g⁻¹ • x))).symm))

/-- The original Kummer integral comparison transported by the actual
inverse scheme isomorphism to the literal constant extension. -/
def kummerTateEllAdicH1BaseChangeEquiv :
    TateModule ℓ (Pic0 K F) ≃ₗ[ℤ_[ℓ]] ellAdicCohomology Y ℓ 1 := by
  have : IsIntegral M.C := M.isIntegral
  have : IsIntegral Y := IsIntegral.of_isIso e.hom
  exact (M.kummerTateEllAdicH1Equiv xi ℓ hℓ).trans
    (ellAdicH1PullbackEquiv ℓ e xi).symm

omit [Fintype k] [Algebra.IsAlgebraic k K] in
/-- Each projection keeps the specified inverse-morphism pullback of the
original finite Kummer comparison at Tate coordinate `n+1`. -/
theorem kummerTateEllAdicH1BaseChangeEquiv_projection
    (x : TateModule ℓ (Pic0 K F)) (n : ℕ) :
    ellAdicProjection Y ℓ 1 n (M.kummerTateEllAdicH1BaseChangeEquiv C e xi ℓ hℓ x) =
      finiteLevelCohomologyPullback ℓ e.inv n 1
        (M.kummerEllPowerCohomologyEquiv xi ℓ hℓ n
          ⟨x.val (n + 1), Pic0.mem_torsion.mpr (TateModule.torsion x (n + 1))⟩) := rfl

/-- The `q`-weighted inverse arithmetic operator on the original prime-power
Tate module, formed using its existing representation. -/
def kummerPic0TateFrobenius : Module.End ℤ_[ℓ] (TateModule ℓ (Pic0 K F)) :=
  (Fintype.card k) • TateModule.rep ℓ (Pic0 K F) (SemilinearAut K F)
    (M.constantSemilinearAction (C ↘ Spec (.of k)) e he
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K))⁻¹

/-- The original integral Kummer equivalence intertwines native geometric
Frobenius and the actual weighted inverse arithmetic Tate operator. -/
theorem kummerTateEllAdicH1BaseChangeEquiv_frobenius (x : TateModule ℓ (Pic0 K F)) :
    finiteFieldFrobeniusEllAdicCohomology k K C ℓ 1
        (M.kummerTateEllAdicH1BaseChangeEquiv C e xi ℓ hℓ x) =
      M.kummerTateEllAdicH1BaseChangeEquiv C e xi ℓ hℓ
        (M.kummerPic0TateFrobenius C e he ℓ x) := by
  apply ellAdicCohomology_ext Y ℓ 1
  intro n
  let xn : Pic0.torsion K F (ℓ ^ (n + 1)) :=
    ⟨x.val (n + 1), Pic0.mem_torsion.mpr (TateModule.torsion x (n + 1))⟩
  exact M.kummerEllPowerCohomologyEquiv_geometricFrobenius C e he xi ℓ hℓ n xn

/-- Every integral Frobenius power is intertwined with the same original
Tate operator, including the retained coefficient twist. -/
theorem kummerTateEllAdicH1BaseChangeEquiv_frobenius_pow
    (m : ℕ) (x : TateModule ℓ (Pic0 K F)) :
    ((finiteFieldFrobeniusEllAdicCohomology k K C ℓ 1) ^ m)
        (M.kummerTateEllAdicH1BaseChangeEquiv C e xi ℓ hℓ x) =
      M.kummerTateEllAdicH1BaseChangeEquiv C e xi ℓ hℓ
        (((M.kummerPic0TateFrobenius C e he ℓ) ^ m) x) := by
  have h : Function.Semiconj (M.kummerTateEllAdicH1BaseChangeEquiv C e xi ℓ hℓ)
      (M.kummerPic0TateFrobenius C e he ℓ)
      (finiteFieldFrobeniusEllAdicCohomology k K C ℓ 1) :=
    fun x => (M.kummerTateEllAdicH1BaseChangeEquiv_frobenius C e he xi ℓ hℓ x).symm
  simpa only [Module.End.pow_apply] using (h.iterate_right m x).symm

/-- The same actual base-change comparison on the original rational tensors. -/
def kummerTateRationalEllAdicH1BaseChangeEquiv :
    TensorProduct ℤ_[ℓ] ℚ_[ℓ] (TateModule ℓ (Pic0 K F)) ≃ₗ[ℚ_[ℓ]]
      rationalEllAdicCohomology ℓ Y 1 :=
  (M.kummerTateEllAdicH1BaseChangeEquiv C e xi ℓ hℓ).baseChange ℤ_[ℓ] ℚ_[ℓ]
    (TateModule ℓ (Pic0 K F)) (ellAdicCohomology Y ℓ 1)

/-- The rational Tate action is scalar extension of the original integral
weighted inverse arithmetic action. -/
def kummerPic0RationalTateFrobenius :
    Module.End ℚ_[ℓ] (TensorProduct ℤ_[ℓ] ℚ_[ℓ] (TateModule ℓ (Pic0 K F))) :=
  (M.kummerPic0TateFrobenius C e he ℓ).baseChange ℚ_[ℓ]

/-- Scalar extension preserves the actual Frobenius comparison on the
original rational cohomology and original rational Tate module. -/
theorem kummerTateRationalEllAdicH1BaseChangeEquiv_frobenius
    (x : TensorProduct ℤ_[ℓ] ℚ_[ℓ] (TateModule ℓ (Pic0 K F))) :
    finiteFieldFrobeniusRationalEllAdicCohomology k K C ℓ 1
        (M.kummerTateRationalEllAdicH1BaseChangeEquiv C e xi ℓ hℓ x) =
      M.kummerTateRationalEllAdicH1BaseChangeEquiv C e xi ℓ hℓ
        (M.kummerPic0RationalTateFrobenius C e he ℓ x) :=
  linearEquiv_baseChange_intertwines (R := ℤ_[ℓ]) (S := ℚ_[ℓ])
    (M.kummerTateEllAdicH1BaseChangeEquiv C e xi ℓ hℓ)
    (M.kummerPic0TateFrobenius C e he ℓ)
    (finiteFieldFrobeniusEllAdicCohomology k K C ℓ 1)
    (M.kummerTateEllAdicH1BaseChangeEquiv_frobenius C e he xi ℓ hℓ) x

/-- All rational Frobenius powers retain the same original Tate comparison. -/
theorem kummerTateRationalEllAdicH1BaseChangeEquiv_frobenius_pow
    (m : ℕ) (x : TensorProduct ℤ_[ℓ] ℚ_[ℓ] (TateModule ℓ (Pic0 K F))) :
    ((finiteFieldFrobeniusRationalEllAdicCohomology k K C ℓ 1) ^ m)
        (M.kummerTateRationalEllAdicH1BaseChangeEquiv C e xi ℓ hℓ x) =
      M.kummerTateRationalEllAdicH1BaseChangeEquiv C e xi ℓ hℓ
        (((M.kummerPic0RationalTateFrobenius C e he ℓ) ^ m) x) := by
  have h : Function.Semiconj (M.kummerTateRationalEllAdicH1BaseChangeEquiv C e xi ℓ hℓ)
      (M.kummerPic0RationalTateFrobenius C e he ℓ)
      (finiteFieldFrobeniusRationalEllAdicCohomology k K C ℓ 1) :=
    fun x => (M.kummerTateRationalEllAdicH1BaseChangeEquiv_frobenius C e he xi ℓ hℓ x).symm
  simpa only [Module.End.pow_apply] using (h.iterate_right m x).symm

include xi hℓ in
/-- The traces of every original rational Frobenius power agree under the
proved Kummer comparison with the original rational Tate operator. -/
theorem trace_rationalEllAdicH1_frobenius_pow (m : ℕ) :
    LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ Y 1)
        ((finiteFieldFrobeniusRationalEllAdicCohomology k K C ℓ 1) ^ m) =
      LinearMap.trace ℚ_[ℓ]
        (TensorProduct ℤ_[ℓ] ℚ_[ℓ] (TateModule ℓ (Pic0 K F)))
        ((M.kummerPic0RationalTateFrobenius C e he ℓ) ^ m) := by
  let E := M.kummerTateRationalEllAdicH1BaseChangeEquiv C e xi ℓ hℓ
  let a := (finiteFieldFrobeniusRationalEllAdicCohomology k K C ℓ 1) ^ m
  let b := (M.kummerPic0RationalTateFrobenius C e he ℓ) ^ m
  have h : E.conj b = a := by
    apply LinearMap.ext
    intro y
    change E (b (E.symm y)) = a y
    exact (M.kummerTateRationalEllAdicH1BaseChangeEquiv_frobenius_pow
      C e he xi ℓ hℓ m (E.symm y)).symm.trans (congrArg a (E.apply_symm_apply y))
  exact (congrArg (LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ Y 1)) h).symm.trans
    (LinearMap.trace_conj' b E)

omit [Fintype k] [Algebra.IsAlgebraic k K] [Algebra.EssFiniteType K F] in
include e xi hℓ in
/-- The original rational cohomology of the literal constant extension is finite-dimensional. -/
theorem finiteDimensional_rationalEllAdicH1_baseChange :
    FiniteDimensional ℚ_[ℓ] (rationalEllAdicCohomology ℓ Y 1) := by
  have : IsIntegral M.C := M.isIntegral
  have : IsIntegral Y := IsIntegral.of_isIso e.hom
  have : FiniteDimensional ℚ_[ℓ] (rationalEllAdicCohomology ℓ M.C 1) :=
    M.finiteDimensional_rationalEllAdicH1 ℓ hℓ
  let E := rationalEllAdicH1PullbackEquiv ℓ e xi
  exact Module.Finite.of_surjective E.symm.toLinearMap E.symm.surjective

end AlgebraicCurve.CurveModel
