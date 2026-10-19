/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Repository: https://github.com/n-yamaguchi-0729
-/

import Nyll.AlgebraicCurves.Divisors.Modulus.ModulusStalks
import Nyll.SchemeTheory.Divisors.LocalComplement
import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.IEqProper
import Nyll.AlgebraicCurves.RelativeDivisors.LineBundles.InvertibleI
import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.SmoothOfRelativeDimensionDVRStalkIsClosed
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# The actual ideal sheaf of a function-field modulus

For an integral proper smooth curve over an arbitrary field, take the product
of the ideals of the corresponding closed points with the specified
multiplicities. The stalk at each such point is the prescribed power of its
maximal ideal. In particular the construction retains infinitesimal thickness.

The comparison of the degree of the resulting finite scheme with the weighted
function-field degree, and compatibility with arbitrary field extension, are
separate assertions and are not assumed in this construction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace AlgebraicCurve.Modulus

private def closedPointIdeal {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X)) :
    X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩

private theorem mem_support_closedPointIdeal {X : Scheme.{u}} (x y : X)
    (hx : IsClosed ({x} : Set X)) : y ∈ (closedPointIdeal x hx).support ↔ y = x := by
  have hs : ((closedPointIdeal x hx).support : Set X) = {x} :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal ⟨{x}, hx⟩
  exact Set.ext_iff.mp hs y

private theorem stalkIdeal_closedPointIdeal_self {X : Scheme.{u}} (x : X)
    (hx : IsClosed ({x} : Set X)) :
    (closedPointIdeal x hx).stalkIdeal x = IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := x) (show x ∈ (⊤ : X.Opens) from trivial)
  have hpre : (fun p : PrimeSpectrum Γ(X, U) => hU.fromSpec p) ⁻¹' ({x} : Set X) =
      {hU.primeIdealOf ⟨x, hxU⟩} := by
    ext p
    change hU.fromSpec p = x ↔ p = hU.primeIdealOf ⟨x, hxU⟩
    constructor
    · intro hp
      exact hU.fromSpec.isOpenEmbedding.injective
        (hp.trans (hU.fromSpec_primeIdealOf ⟨x, hxU⟩).symm)
    · rintro rfl
      exact hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  rw [Scheme.IdealSheafData.stalkIdeal_eq_map_ideal _ x ⟨U, hU⟩ hxU,
    closedPointIdeal, Scheme.IdealSheafData.vanishingIdeal_ideal]
  change Ideal.map (X.presheaf.germ U x hxU).hom
    (PrimeSpectrum.vanishingIdeal
      ((fun p : PrimeSpectrum Γ(X, U) => hU.fromSpec p) ⁻¹' ({x} : Set X))) = _
  rw [hpre, PrimeSpectrum.vanishingIdeal_singleton]
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  have _ : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := hU.isLocalization_stalk ⟨x, hxU⟩
  exact IsLocalization.AtPrime.map_eq_maximalIdeal
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal (X.presheaf.stalk x)

private theorem stalkIdeal_eq_top_of_notMem_support {X : Scheme.{u}}
    (I : X.IdealSheafData) (x : X) (hx : x ∉ I.support) : I.stalkIdeal x = ⊤ := by
  by_contra hne
  have hmem := (I.mem_support_fromSpecStalk_iff_stalkIdeal_le x
    (IsLocalRing.closedPoint (X.presheaf.stalk x))).mpr (IsLocalRing.le_maximalIdeal hne)
  rw [Scheme.fromSpecStalk_closedPoint] at hmem
  exact hx hmem

private theorem stalkIdeal_closedPointIdeal_ne {X : Scheme.{u}} (x y : X)
    (hx : IsClosed ({x} : Set X)) (hne : y ≠ x) :
    (closedPointIdeal x hx).stalkIdeal y = ⊤ := by
  apply stalkIdeal_eq_top_of_notMem_support
  exact fun h => hne ((mem_support_closedPointIdeal x y hx).mp h)

private theorem stalkIdeal_pow {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) (n : ℕ) :
    (I ^ n).stalkIdeal x = I.stalkIdeal x ^ n := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := x) (show x ∈ (⊤ : X.Opens) from trivial)
  rw [Scheme.IdealSheafData.stalkIdeal_eq_map_ideal _ x ⟨U, hU⟩ hxU,
    Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Ideal.map_pow,
    Scheme.IdealSheafData.stalkIdeal_eq_map_ideal _ x ⟨U, hU⟩ hxU]

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]

/-- The unique actual closed point belonging to a function-field place. -/
def pointOfPlace :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    Place K C.functionField → C := by
  intro _functionFieldAlgebra v
  exact (existsUnique_closedPoint_of_place c v).choose

theorem pointOfPlace_closed :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    ∀ v : Place K C.functionField, IsClosed ({pointOfPlace c v} : Set C) := by
  intro _functionFieldAlgebra v
  exact (existsUnique_closedPoint_of_place c v).choose_spec.1.1

theorem pointOfPlace_range_stalk :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    ∀ v : Place K C.functionField,
      (algebraMap (C.presheaf.stalk (pointOfPlace c v)) C.functionField).range =
        v.toValuationSubring.toSubring := by
  intro _functionFieldAlgebra v
  exact (existsUnique_closedPoint_of_place c v).choose_spec.1.2

theorem pointOfPlace_injective :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    Function.Injective (pointOfPlace c) := by
  intro _functionFieldAlgebra v w hvw
  apply Place.ext
  apply SetLike.ext
  intro f
  change f ∈ v.toValuationSubring.toSubring ↔ f ∈ w.toValuationSubring.toSubring
  rw [← pointOfPlace_range_stalk c v, ← pointOfPlace_range_stalk c w, hvw]

/-- The defining ideal sheaf on the given curve: each closed-point ideal is
raised to the multiplicity retained by the original modulus. -/
def curveIdeal :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    Modulus K C.functionField → C.IdealSheafData := by
  intro _functionFieldAlgebra D
  exact ∏ v ∈ D.support, closedPointIdeal (pointOfPlace c v) (pointOfPlace_closed c v) ^ D v

/-- Zero modulus defines the empty subscheme. -/
theorem curveIdeal_zero :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    curveIdeal c (0 : Modulus K C.functionField) = ⊤ := by
  intro _functionFieldAlgebra
  change (0 : Modulus K C.functionField).prod (fun v n =>
    closedPointIdeal (pointOfPlace c v) (pointOfPlace_closed c v) ^ n) = ⊤
  rw [Finsupp.prod_zero_index, Scheme.IdealSheafData.one_eq_top]

/-- Adding effective multiplicities multiplies their actual ideal sheaves. -/
theorem curveIdeal_add :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    ∀ D E : Modulus K C.functionField,
      curveIdeal c (D + E) = curveIdeal c D * curveIdeal c E := by
  intro _functionFieldAlgebra D E
  change (D + E).prod (fun v n =>
      closedPointIdeal (pointOfPlace c v) (pointOfPlace_closed c v) ^ n) =
    D.prod (fun v n =>
      closedPointIdeal (pointOfPlace c v) (pointOfPlace_closed c v) ^ n) *
    E.prod (fun v n =>
      closedPointIdeal (pointOfPlace c v) (pointOfPlace_closed c v) ^ n)
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ => pow_add _)

/-- The stalk of the constructed ideal has exactly the specified multiplicity,
including multiplicity zero away from the modulus. -/
theorem curveIdeal_stalk_at_place :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    ∀ (D : Modulus K C.functionField) (v : Place K C.functionField),
      (curveIdeal c D).stalkIdeal (pointOfPlace c v) =
        (IsLocalRing.maximalIdeal (C.presheaf.stalk (pointOfPlace c v))) ^ D v := by
  intro _functionFieldAlgebra D v
  classical
  rw [curveIdeal, Scheme.IdealSheafData.stalkIdeal_finset_prod]
  have hother : ∀ w : Place K C.functionField, w ≠ v →
      (closedPointIdeal (pointOfPlace c w) (pointOfPlace_closed c w) ^ D w).stalkIdeal
        (pointOfPlace c v) = 1 := by
    intro w hw
    rw [stalkIdeal_pow, stalkIdeal_closedPointIdeal_ne _ _ _
      (fun he => hw ((pointOfPlace_injective c) he).symm), ← Ideal.one_eq_top, one_pow]
  by_cases hv : D v = 0
  · rw [hv, pow_zero]
    apply Finset.prod_eq_one
    intro w hw
    apply hother w
    intro he
    subst w
    exact (Finsupp.mem_support_iff.mp hw) hv
  · rw [Finset.prod_eq_single v (fun w _ hw => hother w hw)
      (fun h => (h (Finsupp.mem_support_iff.mpr hv)).elim), stalkIdeal_pow,
      stalkIdeal_closedPointIdeal_self]

/-- The multiplicity is the actual length of the local quotient of the curve
by the constructed modulus ideal. -/
theorem curveIdeal_local_length :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    ∀ (D : Modulus K C.functionField) (v : Place K C.functionField),
      Module.length (C.presheaf.stalk (pointOfPlace c v))
        ((C.presheaf.stalk (pointOfPlace c v)) ⧸
          (curveIdeal c D).stalkIdeal (pointOfPlace c v)) = (D v : ENat) := by
  intro _functionFieldAlgebra D v
  have _ : IsDiscreteValuationRing (C.presheaf.stalk (pointOfPlace c v)) :=
    SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed c
      (pointOfPlace c v) (pointOfPlace_closed c v)
  rw [curveIdeal_stalk_at_place c D v]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal
    (C.presheaf.stalk (pointOfPlace c v)) (D v)

/-- The actual ideal sheaf recovers every multiplicity, so this construction
does not identify distinct function-field moduli. -/
theorem curveIdeal_injective :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    Function.Injective (curveIdeal c) := by
  intro _functionFieldAlgebra D E hDE
  apply Finsupp.ext
  intro v
  apply ENat.natCast_inj.mp
  rw [← curveIdeal_local_length c D v, ← curveIdeal_local_length c E v, hDE]

private theorem mem_support_prod {X : Scheme.{u}} {ι : Type*} (s : Finset ι)
    (I : ι → X.IdealSheafData) (x : X) :
    x ∈ (∏ i ∈ s, I i).support ↔ ∃ i ∈ s, x ∈ (I i).support := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top,
      Scheme.IdealSheafData.support_top]
    change False ↔ ∃ i, i ∈ (∅ : Finset ι) ∧ x ∈ (I i).support
    constructor
    · exact False.elim
    · rintro ⟨i, hi, _⟩
      exact Finset.notMem_empty i hi
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Scheme.IdealSheafData.support_mul]
    change (x ∈ (I i).support ∨ x ∈ (∏ j ∈ s, I j).support) ↔ _
    rw [ih]
    constructor
    · rintro (hx | ⟨j, hj, hx⟩)
      · exact ⟨i, Finset.mem_insert_self _ _, hx⟩
      · exact ⟨j, Finset.mem_insert_of_mem hj, hx⟩
    · rintro ⟨j, hj, hx⟩
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact Or.inl hx
      · exact Or.inr ⟨j, hj, hx⟩

/-- The support of the ideal is precisely the specified finite set of places,
viewed as actual closed points. -/
theorem mem_support_curveIdeal :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    ∀ (D : Modulus K C.functionField) (x : C),
      x ∈ (curveIdeal c D).support ↔ ∃ v ∈ D.support, pointOfPlace c v = x := by
  intro _functionFieldAlgebra D x
  classical
  rw [curveIdeal, mem_support_prod]
  apply exists_congr
  intro v
  constructor
  · rintro ⟨hv, hx⟩
    rw [Scheme.IdealSheafData.support_pow _ _ (Finsupp.mem_support_iff.mp hv),
      mem_support_closedPointIdeal] at hx
    exact ⟨hv, hx.symm⟩
  · rintro ⟨hv, hx⟩
    refine ⟨hv, ?_⟩
    rw [Scheme.IdealSheafData.support_pow _ _ (Finsupp.mem_support_iff.mp hv),
      mem_support_closedPointIdeal]
    exact hx.symm

theorem curveIdeal_finite_support :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    ∀ D : Modulus K C.functionField, ((curveIdeal c D).support : Set C).Finite := by
  intro _functionFieldAlgebra D
  apply (D.support.finite_toSet.image (pointOfPlace c)).subset
  intro x hx
  obtain ⟨v, hv, he⟩ := (mem_support_curveIdeal c D x).mp hx
  exact ⟨v, hv, he⟩

/-- The constructed ideal is realized by an actual finite flat divisor, with
an invertible ideal on the curve. The pullback by the identity base map is the
ambient convention used by `RelEffCartierDiv`. -/
theorem exists_relativeDivisor_curveIdeal :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    ∀ D : Modulus K C.functionField,
      ∃ (r : ℕ) (E : RelEffCartierDiv c r (𝟙 (Spec (CommRingCat.of K)))),
        E.I = (curveIdeal c D).comap (pullback.fst c (𝟙 (Spec (CommRingCat.of K)))) ∧
          E.I.IsInvertible := by
  intro _functionFieldAlgebra D
  have hfinite : (((curveIdeal c D).comap
      (pullback.fst c (𝟙 (Spec (CommRingCat.of K))))).support :
        Set ↥(pullback c (𝟙 (Spec (CommRingCat.of K))))).Finite := by
    rw [Scheme.IdealSheafData.support_comap]
    change ((pullback.fst c (𝟙 (Spec (CommRingCat.of K)))) ⁻¹'
      ((curveIdeal c D).support : Set C)).Finite
    exact Set.Finite.preimage
      (pullback.fst c (𝟙 (Spec (CommRingCat.of K)))).isOpenEmbedding.injective.injOn
      (curveIdeal_finite_support c D)
  obtain ⟨r, E, hE⟩ := RelEffCartierDiv.exists_I_eq_of_isProper_of_support_finite
    (𝟙 (Spec (CommRingCat.of K))) _ hfinite
  exact ⟨r, E, hE, E.isInvertible_I⟩

end AlgebraicCurve.Modulus
