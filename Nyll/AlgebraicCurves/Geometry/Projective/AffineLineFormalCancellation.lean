/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.AffineLineGroupFormalDifference
import Nyll.SchemeTheory.FunctionFields.AffineFunctionFieldNaturality
import Nyll.AlgebraicCurves.Places.Rational.InfinityArithmetic
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Detecting actual constancy from the full formal difference

The actual homomorphism `K[y][x] → K[z][[T]]`, with `x ↦ z + T`
and `y ↦ z`, is the Taylor automorphism followed by the polynomial inclusion.
It is injective, so equality after this formal test detects morphisms from
the affine plane to a separated target. Setting `y = 0` then detects constancy.

For a group-valued affine-line map, the identity-neighborhood coordinates
already constructed in `AffineLineGroupFormalDifference` are polynomial
coefficients. Positive order at infinity forces each such positive-degree
coefficient to vanish. The argument uses the full series, in every degree.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.AffineLineGroupFormalDifference

variable {K : Type u} [Field K]


/-- The actual pair `(z + T, z)` on the affine plane, as a ring homomorphism. -/
def formalPair : Polynomial (Polynomial K) →+* PowerSeries (Polynomial K) :=
  Polynomial.coeToPowerSeries.ringHom.comp
    (Polynomial.taylorEquiv (Polynomial.X : Polynomial K)).toRingHom

/-- Formal translation tests both affine-plane variables faithfully. -/
theorem formalPair_injective : Function.Injective (formalPair (K := K)) :=
  (Polynomial.coe_injective (Polynomial K)).comp
    (Polynomial.taylorEquiv (Polynomial.X : Polynomial K)).injective

private theorem formalPair_first :
    (formalPair (K := K)).comp (Polynomial.mapRingHom Polynomial.C) =
      (shift (K := K)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C]
    change ((Polynomial.taylor (Polynomial.X : Polynomial K)
      (Polynomial.C (Polynomial.C a))) : PowerSeries (Polynomial K)) =
        Polynomial.aeval (PowerSeries.C Polynomial.X + PowerSeries.X) (Polynomial.C a)
    rw [Polynomial.taylor_C, Polynomial.coe_C, Polynomial.aeval_C]
    exact (PowerSeries.algebraMap_apply (r := a)).symm
  · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X]
    change ((Polynomial.taylor (Polynomial.X : Polynomial K)
      Polynomial.X) : PowerSeries (Polynomial K)) =
        Polynomial.aeval (PowerSeries.C Polynomial.X + PowerSeries.X) Polynomial.X
    rw [Polynomial.taylor_X, Polynomial.coe_add, Polynomial.coe_X,
      Polynomial.coe_C, Polynomial.aeval_X, add_comm]

private theorem formalPair_second :
    (formalPair (K := K)).comp Polynomial.C = PowerSeries.C := by
  apply RingHom.ext
  intro a
  change ((Polynomial.taylor (Polynomial.X : Polynomial K)
    (Polynomial.C a)) : PowerSeries (Polynomial K)) = PowerSeries.C a
  rw [Polynomial.taylor_C, Polynomial.coe_C]

private theorem zeroSection_first :
    (Polynomial.mapRingHom (Polynomial.evalRingHom (0 : K))).comp
      (Polynomial.mapRingHom Polynomial.C) = RingHom.id (Polynomial K) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
      Polynomial.coe_evalRingHom, Polynomial.eval_C, RingHom.id_apply]
  · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
      RingHom.id_apply]

private theorem zeroSection_second :
    (Polynomial.mapRingHom (Polynomial.evalRingHom (0 : K))).comp Polynomial.C =
      Polynomial.C.comp (Polynomial.evalRingHom (0 : K)) :=
  Polynomial.mapRingHom_comp_C _

/-- Equality at the actual formal pair implies constancy of a morphism
from the affine line to a separated scheme over the same field. -/
theorem constant_of_formal_pair {Y : Scheme.{u}}
    (s : Y ⟶ Spec (.of K)) [IsSeparated s]
    (q : Spec (.of (Polynomial K)) ⟶ Y)
    (hq : q ≫ s = Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K))))
    (h : Spec.map (CommRingCat.ofHom (shift (K := K)).toRingHom) ≫ q =
      Spec.map (CommRingCat.ofHom (PowerSeries.C (R := Polynomial K))) ≫ q) :
    q = Spec.map (CommRingCat.ofHom (Polynomial.C (R := K))) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : K))) ≫ q := by
  have hdom : IsDominant (Spec.map (CommRingCat.ofHom (formalPair (K := K)))) :=
    ⟨Scheme.Hom.affineSpecMap_denseRange_of_injective _ formalPair_injective⟩
  have hbase :
      (Polynomial.mapRingHom (Polynomial.C (R := K))).comp
          (algebraMap K (Polynomial K)) =
        (Polynomial.C (R := Polynomial K)).comp (algebraMap K (Polynomial K)) := by
    apply RingHom.ext
    intro a
    simp only [Polynomial.algebraMap_eq, RingHom.comp_apply,
      Polynomial.coe_mapRingHom, Polynomial.map_C]
  have hplane :
      Spec.map (CommRingCat.ofHom
          (Polynomial.mapRingHom (Polynomial.C (R := K)))) ≫ q =
        Spec.map (CommRingCat.ofHom (Polynomial.C (R := Polynomial K))) ≫ q := by
    apply ext_of_isDominant_of_isSeparated s ?_
      (Spec.map (CommRingCat.ofHom (formalPair (K := K))))
    · simpa only [← Category.assoc, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, formalPair_first, formalPair_second] using h
    · simp only [Category.assoc, hq, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, hbase]
  have hz := congrArg
    (fun f => Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (Polynomial.evalRingHom (0 : K)))) ≫ f) hplane
  simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at hz
  rw [zeroSection_first, zeroSection_second] at hz
  simpa only [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc] using hz

/-- A polynomial cannot have positive order at the point at infinity.
The nonzero premise keeps the convention `ord 0 = 0` explicit. -/
theorem polynomial_eq_zero_of_positive_infinity_order [DecidableEq (RatFunc K)]
    (p : Polynomial K)
    (h : p ≠ 0 → 0 < (AlgebraicCurve.RationalFunctionField.placeInfty K).ord
      (algebraMap (Polynomial K) (RatFunc K) p)) : p = 0 := by
  classical
  by_contra hp
  have hh := h hp
  rw [AlgebraicCurve.RationalFunctionField.ord_placeInfty_algebraMap hp] at hh
  exact (not_lt_of_ge (neg_nonpos.mpr (Int.natCast_nonneg p.natDegree))) hh

variable {G : Over (Spec (.of K))} [GrpObj G]

/-- Vanishing of every positive coordinate coefficient makes the full formal
difference the identity, and therefore makes the actual morphism constant. -/
theorem constant_of_coordinates_coeff_eq_zero [IsSeparated G.hom]
    (τ : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))) ⟶ G)
    (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V)
    (hcoeff : ∀ a : Γ(G.left, V), ∀ n : ℕ, 0 < n →
      PowerSeries.coeff n (coordinates τ V hV hunit a) = 0) :
    τ.left = Spec.map (CommRingCat.ofHom (Polynomial.C (R := K))) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : K))) ≫ τ.left := by
  let L : Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap K (PowerSeries (Polynomial K))))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (shift (K := K)).toRingHom)) (by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]
      apply congrArg (fun f : CommRingCat.of K ⟶
        CommRingCat.of (PowerSeries (Polynomial K)) => Spec.map f)
      exact CommRingCat.hom_ext (shift (K := K)).comp_algebraMap)
  let R : Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap K (PowerSeries (Polynomial K))))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (PowerSeries.C (R := Polynomial K)))) (by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]
      apply congrArg (fun f : CommRingCat.of K ⟶
        CommRingCat.of (PowerSeries (Polynomial K)) => Spec.map f)
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact (PowerSeries.algebraMap_apply (r := a)).symm)
  have hc : coordinates τ V hV hunit =
      PowerSeries.C.comp
        ((PowerSeries.constantCoeff (R := Polynomial K)).comp
          (coordinates τ V hV hunit)) := by
    apply RingHom.ext
    intro a
    apply PowerSeries.ext
    intro n
    cases n with
    | zero =>
      simp only [RingHom.comp_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.constantCoeff_C]
    | succ n =>
      rw [hcoeff a (n + 1) (Nat.succ_pos n)]
      simp only [RingHom.comp_apply, PowerSeries.coeff_C_of_ne_zero (Nat.succ_ne_zero n)]
  have hd : difference τ = R.left ≫
      (1 : Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap K (Polynomial K)))) ⟶ G).left := by
    calc
      difference τ = Spec.map (CommRingCat.ofHom (coordinates τ V hV hunit)) ≫
          hV.fromSpec := (coordinates_spec τ V hV hunit).symm
      _ = R.left ≫ Spec.map (CommRingCat.ofHom
            (PowerSeries.constantCoeff (R := Polynomial K))) ≫ difference τ := by
        conv_lhs => rw [hc]
        simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
          coordinates_spec]
        rfl
      _ = _ := by rw [difference_constant]
  have hmul : (L ≫ τ) * (R ≫ τ)⁻¹ = 1 := by
    apply Over.OverMorphism.ext
    change difference τ = (1 : Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap K (PowerSeries (Polynomial K))))) ⟶ G).left
    exact hd.trans (congrArg Over.Hom.left (MonObj.comp_one R))
  apply constant_of_formal_pair G.hom τ.left τ.w
  exact congrArg Over.Hom.left (mul_inv_eq_one.mp hmul)

/-- The all-orders positive-infinity estimate for the actual polynomial
coordinates implies constancy of the original group-valued morphism. -/
theorem constant_of_coordinates_positive_infinity_order [DecidableEq (RatFunc K)]
    [IsSeparated G.hom]
    (τ : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))) ⟶ G)
    (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V)
    (hord : ∀ a : Γ(G.left, V), ∀ n : ℕ, 0 < n →
      PowerSeries.coeff n (coordinates τ V hV hunit a) ≠ 0 →
      0 < (AlgebraicCurve.RationalFunctionField.placeInfty K).ord
        (algebraMap (Polynomial K) (RatFunc K)
          (PowerSeries.coeff n (coordinates τ V hV hunit a)))) :
    τ.left = Spec.map (CommRingCat.ofHom (Polynomial.C (R := K))) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : K))) ≫ τ.left := by
  apply constant_of_coordinates_coeff_eq_zero τ V hV hunit
  intro a n hn
  exact polynomial_eq_zero_of_positive_infinity_order _ (hord a n hn)

end AlgebraicGeometry.AffineLineGroupFormalDifference
