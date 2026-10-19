/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.JacobianVarieties.Kummer.OpenKummerGenericRootLift
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # The same generic fibre root in its actual rational model chart

Compose the retained normalization-lift equation with the actual model chart.
The resulting RatFunc embedding sends X to the very same chosen fibre root.
No equality between separately chosen fibre coordinates is postulated.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory TopologicalSpace
open JacobianVarieties.Kummer
open scoped FintypeCatDiscrete

namespace AlgebraicCurve.CurveModel.OpenKummer

private theorem compose_lift_model
    {D : Type*} [Category D] {A B C T R : D}
    {l : T ⟶ B} {ρ : T ⟶ A} {a : A ⟶ B} {h : B ⟶ C}
    {v : A ⟶ R} {q : R ⟶ C} {ψ : T ⟶ R}
    (hl : l = ρ ≫ a) (ha : a ≫ h = v ≫ q) (hρ : ρ ≫ v = ψ) :
    l ≫ h = ψ ≫ q := by
  rw [hl, Category.assoc, ha, ← Category.assoc, hρ]

/-- A model chart carrying the original quotient root to X reads each actual
geometric fibre point at its same root value, with the original group actions. -/
theorem exists_arithmeticKummerFiber_genericModelCoordinate
    {K F : Type} [Field K] [Field F] [Algebra K F]
    (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
    (w : Pic0.openKummerUnits K F S n)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hi : ∀ (y : X) (x : closedPoints M.C), x.val = j y → M.placeOfPoint x ∉ S)
    (hn : IsUnit ((n : ℕ) : K))
    {Ω : Type} [Field Ω] [IsSepClosed Ω] [Algebra X.functionField Ω]
    [IsSepClosure X.functionField Ω]
    (C : Scheme) (q : Spec (.of (RatFunc K)) ⟶ C) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    let W := M.openKummerCover S n hn w j hj hi
    let g := j.functionFieldMap hj (M.ffEquiv (w.val : F))
    let A := AdjoinRoot (Polynomial.X ^ (n : ℕ) - Polynomial.C g)
    letI := kummerGeometricRootAction M S n w j hj hi hn ξ
    ∀ (h : W.left ⟶ C) (eRoot : A ≃+* RatFunc K),
      eRoot (AdjoinRoot.root (Polynomial.X ^ (n : ℕ) - Polynomial.C g)) = RatFunc.X →
      (M.openKummerGenericMap S n w j hj).toNormalization ≫ h =
        Spec.map (CommRingCat.ofHom eRoot.symm.toRingHom) ≫ q →
      ∃ e : (FiniteEtale.fiber ξ).obj W ≃
          {β : Ω // β ^ (n : ℕ) = algebraMap X.functionField Ω g},
        (∀ (ζ : rootsOfUnity (n : ℕ) K) x,
          (e (ζ • x)).val = pointScalar (j ≫ M.toBase) ξ (ζ.val : K) * (e x).val) ∧
        (∀ (σ : Ω ≃ₐ[X.functionField] Ω) x,
          (e (FiniteEtale.fundamentalGroupHom (X.fromSpecStalk (genericPoint X)) η
            (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[X.functionField] Ω) σ) • x)).val =
            σ (e x).val) ∧
        ∀ β : {z : Ω // z ^ (n : ℕ) = algebraMap X.functionField Ω g},
          ∃ ψ : RatFunc K →+* Ω, ψ RatFunc.X = β.val ∧
            (fiberLiftEquiv ξ W (e.symm β)).val ≫ h =
              Spec.map (CommRingCat.ofHom ψ) ≫ q := by
  intro η ξ W g A h eRoot hroot hmodel
  let := kummerGeometricRootAction M S n w j hj hi hn ξ
  obtain ⟨e, hscale, hG, hLift⟩ :=
    exists_arithmeticKummerFiber_genericRootEquiv_with_lift (Ω := Ω) M S n w j hj hi hn
  refine ⟨e, hscale, hG, fun β => ?_⟩
  let ρ : A →ₐ[X.functionField] Ω :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId X.functionField Ω) β.val (by
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C]
      exact sub_eq_zero.mpr β.property)
  let ψ := ρ.toRingHom.comp eRoot.symm.toRingHom
  have hsymm : eRoot.symm RatFunc.X =
      AdjoinRoot.root (Polynomial.X ^ (n : ℕ) - Polynomial.C g) := by
    apply eRoot.injective
    rw [eRoot.apply_symm_apply, hroot]
  refine ⟨ψ, ?_, ?_⟩
  · change ρ (eRoot.symm RatFunc.X) = β.val
    rw [hsymm]
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  · have hLiftβ : (fiberLiftEquiv ξ W (e.symm β)).val =
        Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫
          (M.openKummerGenericMap S n w j hj).toNormalization := hLift β
    have hcomp : Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom eRoot.symm.toRingHom) =
          Spec.map (CommRingCat.ofHom ψ) := by
      rw [← Spec.map_comp]
      rfl
    exact compose_lift_model hLiftβ hmodel hcomp

end AlgebraicCurve.CurveModel.OpenKummer
