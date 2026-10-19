/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.VectorGroupRegularMapModulus
import Nyll.SchemeTheory.GroupSchemes.SplitTorusSchemePoints
import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientSchemePresheaf
import Nyll.AlgebraicCurves.FunctionFields.Rational.SeparatingRationalPresentation
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeFunctionField
import Nyll.AlgebraicCurves.Models.FunctionFields.CurveRingEquivFunctionField
import Nyll.AlgebraicCurves.Divisors.Modulus.SplitAffineModulus
import Nyll.AlgebraicCurves.Divisors.Modulus.MultiplicativeModulus
import Nyll.AlgebraicCurves.Models.Divisors.CartierIdealEquiv
import Nyll.JacobianVarieties.Generalized.ModulusMapCondition
import Nyll.JacobianVarieties.Generalized.ModulusAbelUniqueness
import Mathlib.Algebra.Group.Units.Equiv

/-! # Effective moduli for actual split-torus morphisms

A morphism from an open curve to the split torus supplies global unit
coordinates. Their function-field images remain units, and their residue
values are the original scheme point values. Weil reciprocity supplies a
common multiplicative modulus. Adding the finite boundary and realizing
the closed-point ideal product gives an actual relative Cartier modulus.
For a prescribed full divisor, every morphism on its complement already
has that divisor as modulus: the reduced zero and pole modulus of each
unit coordinate is bounded by the prescribed multiplicities.

The base field is algebraically closed. No assertion about a nonsplit torus
or an arbitrary commutative group is made here.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.GroupSchemes AlgebraicGeometry.GeneralizedJacobian
open SchemeTheory.Affine.ScalarQuotientSchemePresheaf
open scoped CategoryTheory.MonObj

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)

/-- The original split-torus point group in additive notation for unit coordinates. -/
def splitTorusPointCoordinates (n : ℕ) :
    Additive (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (splitTorus K n).X) ≃+
      (Fin n → Additive Kˣ) :=
  (((splitTorusPointEquiv K n (Over.mk (𝟙 _))).trans
    (MulEquiv.piCongrRight fun _ => Units.mapEquiv
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv)).toAdditive).trans
        (AddEquiv.piAdditive fun _ : Fin n => Kˣ)

/-- The nonzero rational coordinates are images of the actual global units
classified by the scheme morphism. -/
def splitTorusMapRationalCoordinates (U : M.C.Opens) [Nonempty U] (n : ℕ)
    (q : SchemeHomOver (U.ι ≫ M.toBase) (splitTorus K n).X.hom) : Fin n → Fˣ :=
  fun i => Units.map (M.openSectionFunction U).toMonoidHom
    (splitTorusPointEquiv K n (Over.mk (U.ι ≫ M.toBase))
      (commGroupPointEquiv (splitTorus K n) (U.ι ≫ M.toBase) q) i)

/-- Residue evaluation of every extracted unit is its original scheme point coordinate. -/
theorem splitTorusMapRationalCoordinates_eval (U : M.C.Opens) [Nonempty U] (n : ℕ)
    (q : SchemeHomOver (U.ι ≫ M.toBase) (splitTorus K n).X.hom)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ M.toBase)) (i : Fin n) :
    (M.openPointPlace U x).evalAt (M.splitTorusMapRationalCoordinates U n q i : F) =
      (Additive.toMul (splitTorusPointCoordinates (K := K) n
        (commGroupPointValue (splitTorus K n) (𝟙 _)
          (NeronModelInfra.schemeHomOverComp x q)) i)).val := by
  let s : (sectionsAlgebra K (Over.mk (U.ι ≫ M.toBase)))ˣ :=
    splitTorusPointEquiv K n (Over.mk (U.ι ≫ M.toBase))
      (commGroupPointEquiv (splitTorus K n) (U.ι ≫ M.toBase) q) i
  have heval := M.openSectionFunction_eval U s.val x
  have hnat := splitTorusPointEquiv_naturality K n
    (Over.homMk x.1 x.2 : Over.mk (𝟙 _) ⟶ Over.mk (U.ι ≫ M.toBase))
    (commGroupPointEquiv (splitTorus K n) (U.ι ≫ M.toBase) q) i
  have hvalue := congrArg
    (fun a : (sectionsAlgebra K (Over.mk (𝟙 (Spec (CommRingCat.of K)))))ˣ =>
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom a.val) hnat
  exact heval.trans hvalue.symm

/-- On the original open domain the multiplicative place values agree with
the actual unit coordinates; regularity supplies order zero there. -/
theorem splitTorusMapRationalCoordinates_values (U : M.C.Opens) [Nonempty U] (n : ℕ)
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F]
    (q : SchemeHomOver (U.ι ≫ M.toBase) (splitTorus K n).X.hom)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ M.toBase)) (i : Fin n) :
    Modulus.multiplicativeValues (M.splitTorusMapRationalCoordinates U n q i : F)
        (M.splitTorusMapRationalCoordinates U n q i).ne_zero (M.openPointPlace U x) =
      splitTorusPointCoordinates (K := K) n
        (commGroupPointValue (splitTorus K n) (𝟙 _)
          (NeronModelInfra.schemeHomOverComp x q)) i := by
  have heval := M.splitTorusMapRationalCoordinates_eval U n q x i
  have hnonzero : (M.openPointPlace U x).evalAt
      (M.splitTorusMapRationalCoordinates U n q i : F) ≠ 0 := by
    rw [heval]
    exact Units.ne_zero _
  have hord := (M.openPointPlace U x).ord_eq_zero_of_evalAt_ne_zero
    (M.openPointPlace U x).isRational_of_isAlgClosed hnonzero
  rw [Modulus.multiplicativeValues, dite_eq_left hord]
  apply Additive.toMul.injective
  apply Units.ext
  exact heval

/-- Every actual split-torus morphism on the complement of a given full
Cartier divisor has that same divisor as modulus, with no enlargement. -/
theorem splitTorus_regularMapHasModulus
    {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))
    (n : ℕ)
    (q : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)
      (splitTorus K n).X.hom) :
    M.regularMapHasModulus D (splitTorus K n) q := by
  let U := modulusComplement (modulusCurveMap D)
  let I := modulusCurveIdeal D
  have : Nonempty U := by
    refine ⟨⟨genericPoint M.C, ?_⟩⟩
    change genericPoint M.C ∉ I.support
    apply (I.stalkIdeal_eq_top_iff_notMem_support (genericPoint M.C)).mp
    exact (Ideal.eq_bot_or_top (I.stalkIdeal (genericPoint M.C))).resolve_left
      ((modulusCurveIdeal_isInvertible D).stalkIdeal_ne_bot (genericPoint M.C))
  have : IsCurveOver K F :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  have : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  have : Algebra.EssFiniteType K F := by
    let _ : Algebra K M.C.functionField := M.functionFieldAlgebra
    exact (Algebra.EssFiniteType.iff_of_algEquiv M.ffAlgEquiv).mpr
      (essFiniteType_functionField M.toBase)
  obtain ⟨rationalAlgebra, rationalTower, rationalFinite, _⟩ :=
    IsCurveOver.exists_separating_ratFunc_algebra (K := K) (F := F)
  let Δ := M.functionFieldModulus D
  let f := M.splitTorusMapRationalCoordinates U n q
  let e := splitTorusPointCoordinates (K := K) n
  have hcoords : Δ.HasModulus
      (fun w i => Modulus.multiplicativeValues (f i : F) (f i).ne_zero w) := by
    apply Modulus.hasModulus_pi_iff.mpr
    intro i
    obtain ⟨E, hE, hred, hm⟩ :=
      Modulus.exists_reduced_multiplicative_modulus (K := K) (f i : F) (f i).ne_zero
    refine hm.mono ?_
    intro w
    by_cases hw : Δ w = 0
    · obtain ⟨x, rfl⟩ := M.exists_modulusPlace_eq D w hw
      let y : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ M.toBase) :=
        ⟨x.left, Over.w x⟩
      have heval := M.splitTorusMapRationalCoordinates_eval U n q y i
      have hnonzero : (M.openPointPlace U y).evalAt (f i : F) ≠ 0 := by
        rw [heval]
        exact Units.ne_zero _
      have hord := (M.openPointPlace U y).ord_eq_zero_of_evalAt_ne_zero
        (M.openPointPlace U y).isRational_of_isAlgClosed hnonzero
      exact ((hE (M.modulusPlace D x)).mpr hord).le.trans (Nat.zero_le _)
    · exact (hred w).trans (Nat.one_le_iff_ne_zero.mpr hw)
  have hmod := hcoords.map e.symm.toAddMonoidHom
  apply hmod.congr
  intro w hw
  obtain ⟨x, rfl⟩ := M.exists_modulusPlace_eq D w hw
  let y : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ M.toBase) :=
    ⟨x.left, Over.w x⟩
  apply e.injective
  change e (e.symm (fun i =>
    Modulus.multiplicativeValues (f i : F) (f i).ne_zero (M.openPointPlace U y))) =
      e (M.regularMapValues U (splitTorus K n) q (M.openPointPlace U y))
  rw [e.apply_symm_apply, M.regularMapValues_apply]
  funext i
  exact M.splitTorusMapRationalCoordinates_values U n q y i

/-- Every actual split-torus morphism has a full modulus containing its
domain boundary. The finite rational presentation is constructed from the curve. -/
theorem exists_splitTorus_regularMap_modulus (U : M.C.Opens)
    (hU : (U : Set M.C).Nonempty) (n : ℕ)
    (q : SchemeHomOver (U.ι ≫ M.toBase) (splitTorus K n).X.hom) :
    ∃ D : Modulus K F,
      (∀ w, D w = 0 → (M.placeEquiv.symm w).1 ∈ U) ∧
      D.HasModulus (M.regularMapValues U (splitTorus K n) q) := by
  have : Nonempty U := ⟨⟨hU.choose, hU.choose_spec⟩⟩
  have : IsCurveOver K F :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  have : Algebra.EssFiniteType K F := by
    let _ : Algebra K M.C.functionField := M.functionFieldAlgebra
    exact (Algebra.EssFiniteType.iff_of_algEquiv M.ffAlgEquiv).mpr
      (essFiniteType_functionField M.toBase)
  obtain ⟨rationalAlgebra, rationalTower, rationalFinite, _⟩ :=
    IsCurveOver.exists_separating_ratFunc_algebra (K := K) (F := F)
  obtain ⟨E, hE⟩ := Modulus.exists_splitTorus_modulus (K := K)
    (fun i => (M.splitTorusMapRationalCoordinates U n q i : F))
    (fun i => (M.splitTorusMapRationalCoordinates U n q i).ne_zero)
  refine M.exists_regularMap_modulus_of_point_coordinates U hU (splitTorus K n) q
    (splitTorusPointCoordinates (K := K) n) _ E hE ?_
  intro x
  funext i
  exact M.splitTorusMapRationalCoordinates_values U n q x i

/-- The full split-torus modulus is realized by an effective Cartier ideal
on the original curve, with complement inside the original domain. -/
theorem exists_splitTorus_cartierModulus (U : M.C.Opens)
    (hU : (U : Set M.C).Nonempty) (n : ℕ)
    (q : SchemeHomOver (U.ι ≫ M.toBase) (splitTorus K n).X.hom) :
    ∃ (I : M.C.IdealSheafData) (hI : I.IsInvertible),
      I.support.compl ≤ U ∧
      (M.cartierModulus I hI).HasModulus (M.regularMapValues U (splitTorus K n) q) := by
  obtain ⟨D, hboundary, hD⟩ := M.exists_splitTorus_regularMap_modulus U hU n q
  let I := M.pointIdealProduct D
  have hI : I.IsInvertible := M.pointIdealProduct_isInvertible D
  refine ⟨I, hI, M.pointIdealProduct_complement_le U hU D hboundary, ?_⟩
  simpa only [I, M.cartierModulus_pointIdealProduct] using hD

/-- An actual split-torus morphism admits an actual relative effective
Cartier modulus for its restriction to the modulus complement. -/
theorem exists_splitTorus_regularMapHasModulus (U : M.C.Opens)
    (hU : (U : Set M.C).Nonempty) (n : ℕ)
    (q : SchemeHomOver (U.ι ≫ M.toBase) (splitTorus K n).X.hom) :
    ∃ (d : ℕ) (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))
      (hDU : modulusComplement (modulusCurveMap D) ≤ U),
      M.regularMapHasModulus D (splitTorus K n)
        ⟨M.C.homOfLE hDU ≫ q.1, by
          rw [Category.assoc, q.2, ← Category.assoc, Scheme.homOfLE_ι]⟩ := by
  obtain ⟨I, hI, hIU, hmod⟩ := M.exists_splitTorus_cartierModulus U hU n q
  obtain ⟨d, D, hDI⟩ := M.exists_relativeDivisor_ideal I hI
  have hVU : modulusComplement (modulusCurveMap D) ≤ U := by
    change (modulusCurveIdeal D).support.compl ≤ U
    rw [hDI]
    exact hIU
  refine ⟨d, D, hVU, ?_⟩
  apply M.regularMapHasModulus_restriction_of_values U (splitTorus K n) q D hVU
  simpa only [hDI] using hmod

end AlgebraicCurve.CurveModel
