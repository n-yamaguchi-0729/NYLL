/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.OpenKummerArithmeticRootTorsor
import Nyll.AnabelianGeometry.WeightFiltration.ArithmeticKummerRootsRestriction
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGalois

/-!
# Semilinearity on the original arithmetic Kummer-cover fiber

The full coefficient torsor and its generic Galois evaluation formula are
combined with the actual generic surjection and the original arithmetic
projection. No preservation of a character or of the arithmetic label is
assumed. The input base-point square is the geometric square already supplied
by the rational-configuration generic-point owners.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.FiniteEtale JacobianVarieties.Kummer TopologicalSpace
open scoped FintypeCatDiscrete

namespace AlgebraicCurve.CurveModel.OpenKummer

/-- The original arithmetic monodromy is cyclotomically semilinear for the
full roots-of-unity torsor on the original named arithmetic Kummer fiber. -/
theorem exists_arithmeticKummerFiber_semilinearTorsor
    {K F : Type} [Field K] [Field F] [Algebra K F]
    (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
    (w : Pic0.openKummerUnits K F S n)
    {X : Scheme} [IsIntegral X] [IsNormalIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hi : ∀ (y : X) (x : closedPoints M.C), x.val = j y → M.placeOfPoint x ∉ S)
    (hn : IsUnit ((n : ℕ) : K))
    {κ Ω : Type} [Field κ] [Field Ω] [IsAlgClosed κ] [IsSepClosed Ω]
    [Algebra K X.functionField] [Algebra K κ] [Algebra K Ω]
    [Algebra X.functionField Ω] [Algebra κ Ω]
    [IsScalarTower K X.functionField Ω] [IsScalarTower K κ Ω]
    [IsSepClosure K κ] [IsSepClosure X.functionField Ω]
    (hbase : (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
      X.fromSpecStalk (genericPoint X)) ≫ (j ≫ M.toBase) =
        Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let xi := η ≫ X.fromSpecStalk (genericPoint X)
    let W := M.openKummerCover S n hn w j hj hi
    let q := arithmeticFundamentalGroupHom K κ (j ≫ M.toBase) xi
    ∃ a : Ωˣ, ∃ e : (fiber xi).obj W ≃ {β : Ω // β ^ (n : ℕ) = (a : Ω)},
      ∃ t : Torsor (rootsOfUnity (n : ℕ) κ) ((fiber xi).obj W),
        (∀ (ζ : rootsOfUnity (n : ℕ) κ) x,
          (e (t.toMulAction.toSMul.smul ζ x)).val =
            algebraMap κ Ω (ζ.val : κ) * (e x).val) ∧
        ∀ (p : π₁ᵉᵗ(xi)) (ζ : rootsOfUnity (n : ℕ) κ) x,
          p • (t.toMulAction.toSMul.smul ζ x) =
            t.toMulAction.toSMul.smul
              (restrictRootsOfUnity (q p).toRingHom (n : ℕ) ζ) (p • x) := by
  intro η xi W q
  have hnκ : IsUnit ((n : ℕ) : κ) := by
    simpa only [map_natCast] using hn.map (algebraMap K κ)
  obtain ⟨a, e, t, ht, hg⟩ := exists_arithmeticKummerFiber_fullRootTorsor
    M S n w j hj hi hn (algebraMap κ Ω) hnκ
  let genericMap := X.fromSpecStalk (genericPoint X)
  let θ := fieldSourceAbsoluteGaloisHom X.functionField Ω genericMap
  let : IsDominant genericMap := genericPoint_isDominant X
  let : QuasiCompact genericMap :=
    { isCompact_preimage := fun V _ _ => (Set.toFinite (genericMap ⁻¹' V)).isCompact }
  have hsurj : Function.Surjective θ :=
    fieldSourceAbsoluteGaloisHom_surjective X.functionField Ω genericMap
  have hθ (σ : Gal(Ω/X.functionField)) :
      θ σ = fundamentalGroupHom genericMap η
        (toAut (fiber η) Gal(Ω/X.functionField) σ) := by
    change fundamentalGroupHom genericMap η
      (toAutHomeo (fib X.functionField Ω) Gal(Ω/X.functionField) σ) = _
    rw [toAutHomeo_apply]
  refine ⟨a, e, t, ht, ?_⟩
  intro p ζ x
  obtain ⟨σ, rfl⟩ := hsurj p
  apply e.injective
  apply Subtype.ext
  have hgeneric :
      (e (θ σ • (t.toMulAction.toSMul.smul ζ x))).val =
        σ (algebraMap κ Ω (ζ.val : κ)) * (e (θ σ • x)).val := by
    rw [hθ σ]
    exact hg σ ζ x
  have hcoeff := fieldSource_arithmetic_roots_restriction
    K X.functionField κ Ω (j ≫ M.toBase) genericMap hbase (n : ℕ) hnκ σ ζ
  have hroot := ht (restrictRootsOfUnity (q (θ σ)).toRingHom (n : ℕ) ζ) (θ σ • x)
  change (e (t.toMulAction.toSMul.smul
    (restrictRootsOfUnity (q (θ σ)).toRingHom (n : ℕ) ζ) (θ σ • x))).val =
      algebraMap κ Ω (q (θ σ) (ζ.val : κ)) * (e (θ σ • x)).val at hroot
  exact hgeneric.trans
    ((congrArg (fun c : Ω => c * (e (θ σ • x)).val) hcoeff).trans hroot.symm)

end AlgebraicCurve.CurveModel.OpenKummer
