/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCovers.CurveRayArtinKernel
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.IntegralRayApproximation
public import Mathlib.GroupTheory.QuotientGroup.Finite

/-!
# Full boundary inertia images in the original curve abelianization

The full normalization inertia image is its actual local unit Artin image.
The proved generic-kernel comparison detects every relation by all ray
moduli supported at the original boundary. Integral ray approximation then
places each boundary component of such a relation in the finite group of
actual globally integral function values.

Consequently each full boundary inertia has infinite image, and the images
of distinct boundary places have finite intersection. Finite intersections
are retained; no disjointness of section-value cosets is asserted.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry AlgebraicGeometry.FiniteEtale AlgebraicCurve FunctionField
open ProCGroups.Abelian
open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

attribute [local instance]
  AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring

private theorem absoluteArtinComp_placeArtin
    {k : Type v} {K : Type u} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K]
    {G : Type*} [Group G] [TopologicalSpace G]
    (f : LocalClassFieldTheory.localAbsoluteAbelianProfinite K →ₜ* G)
    (v : Place k K) (u : v.adicCompletionˣ) :
    absoluteArtinComp f (IdeleClassGroup.mk (IdeleGroup.placeIdele v u)) =
      (f.comp (placeAbsoluteArtin v)) u := rfl

section Maps

variable {k : Type v} [Field k] [Finite k] (X : Scheme.{u}) [IsIntegral X]
  [Algebra k X.functionField] [Algebra (RatFunc k) X.functionField]
  [IsScalarTower k (RatFunc k) X.functionField] [FunctionField k X.functionField]
  [HasPrincipalDivisors k X.functionField]

/-- The original full local Artin map followed by the original generic
map on topological abelianizations. -/
def curvePlaceArtin (v : Place k X.functionField) :
    v.adicCompletionˣ →ₜ* TopologicalAbelianization
      (π₁ᵉᵗ(X.genericExtensionMorphism (AlgebraicClosure X.functionField))) :=
  (curveAbelianizationMap X).comp (placeAbsoluteArtin v)

private theorem curveArtin_placeIdele (v : Place k X.functionField)
    (u : v.adicCompletionˣ) :
    curveArtin X (IdeleClassGroup.mk (IdeleGroup.placeIdele v u)) =
      curvePlaceArtin X v u :=
  absoluteArtinComp_placeArtin (curveAbelianizationMap X) v u

/-- Full local units in the actual arithmetic curve abelianization. -/
def curveFullInertiaImage (v : Place k X.functionField) :
    Subgroup (TopologicalAbelianization
      (π₁ᵉᵗ(X.genericExtensionMorphism (AlgebraicClosure X.functionField)))) :=
  (RayClass.localHigherUnitGroup v 0).map (curvePlaceArtin X v).toMonoidHom

/-- This is the image of the original full normalization inertia under
the native generic absolute Galois map and the actual abelianization map. -/
theorem curveFullInertiaImage_eq_originalNormalization
    (v : Place k X.functionField)
    (Q : Ideal (integralClosure v.toValuationSubring (SeparableClosure X.functionField)))
    [Q.IsMaximal] :
    let _ : MulSemiringAction Gal(SeparableClosure X.functionField/X.functionField)
        (integralClosure v.toValuationSubring (SeparableClosure X.functionField)) :=
      IsIntegralClosure.MulSemiringAction v.toValuationSubring X.functionField
        (SeparableClosure X.functionField)
        (integralClosure v.toValuationSubring (SeparableClosure X.functionField))
    curveFullInertiaImage X v =
      (Q.inertia Gal(SeparableClosure X.functionField/X.functionField)).map
        ((TopologicalAbelianization.mkₜ _).comp
          (genericAbsoluteGaloisHom X)).toMonoidHom := by
  intro actualAction
  exact (absolute_place_inertia_image_eq_units_of_commutative
    ((TopologicalAbelianization.mkₜ _).comp (genericAbsoluteGaloisHom X)) v Q).symm

end Maps

private theorem placeIdele_mem_integralSubgroup
    {k : Type v} {K : Type u} [Field k] [Field K] [Algebra k K]
    (v : Place k K) (u : v.adicCompletionˣ)
    (hu : u ∈ RayClass.localHigherUnitGroup v 0) :
    IdeleGroup.placeIdele v u ∈ IdeleGroup.integralSubgroup := by
  classical
  intro w
  by_cases hw : w = v
  · subst w
    change IdeleGroup.component v (IdeleGroup.placeIdele v u) ∈ _
    rw [IdeleGroup.component_placeIdele_same]
    exact (RayClass.localHigherUnitGroup_zero v) ▸ hu
  · change IdeleGroup.component w (IdeleGroup.placeIdele v u) ∈ _
    rw [IdeleGroup.component_placeIdele_of_ne v w u hw]
    exact w.adicCompletionIntegers.units.one_mem

/-- Every boundary component of an integral idele relation in the
original curve abelianization is an actual global integral-function value. -/
theorem curveArtin_integral_ker_component_mem
    {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}
    [IsIntegral X] [IsNormalIntegral X]
    (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c] :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    ∀ [Algebra (RatFunc k) X.functionField]
      [IsScalarTower k (RatFunc k) X.functionField] [FunctionField k X.functionField]
      [HasPrincipalDivisors k X.functionField]
      (a : IdeleGroup k X.functionField),
      a ∈ IdeleGroup.integralSubgroup → curveArtin X (IdeleClassGroup.mk a) = 1 →
      ∀ (v : Place k X.functionField), v ∉ curveInteriorPlaces c →
        a v ∈ RayClass.localIntegralFunctionUnits v := by
  intro baseAlgebra rationalAlgebra rationalTower functionField principalDivisors a ha hker v hv
  apply RayClass.mem_localIntegralFunctionUnits_of_all_single_ray a ha v
  intro n
  apply curveArtin_ker_le_rayClassSubgroup c (Finsupp.single v n) ?_ hker
  intro w hw
  apply Finsupp.single_eq_of_ne
  intro h
  subst w
  exact hv hw

/-- The kernel on full local units at an actual boundary place is
contained in the finite group of original integral-function values. -/
theorem curvePlaceArtin_units_ker_le_localIntegralFunctionUnits
    {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}
    [IsIntegral X] [IsNormalIntegral X]
    (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c] :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    ∀ [Algebra (RatFunc k) X.functionField]
      [IsScalarTower k (RatFunc k) X.functionField] [FunctionField k X.functionField]
      [HasPrincipalDivisors k X.functionField]
      (v : Place k X.functionField), v ∉ curveInteriorPlaces c →
      RayClass.localHigherUnitGroup v 0 ⊓ (curvePlaceArtin X v).toMonoidHom.ker ≤
        RayClass.localIntegralFunctionUnits v := by
  intro baseAlgebra rationalAlgebra rationalTower functionField principalDivisors v hv
  rintro u ⟨hu, hzero⟩
  have hzeroArtin : curveArtin X
      (IdeleClassGroup.mk (IdeleGroup.placeIdele v u)) = 1 := by
    rw [curveArtin_placeIdele]
    exact MonoidHom.mem_ker.mp hzero
  have hlocal := curveArtin_integral_ker_component_mem c
    (IdeleGroup.placeIdele v u) (placeIdele_mem_integralSubgroup v u hu) hzeroArtin v hv
  change IdeleGroup.component v (IdeleGroup.placeIdele v u) ∈ _ at hlocal
  rw [IdeleGroup.component_placeIdele_same] at hlocal
  exact hlocal

/-- A full boundary inertia image has finite intersection with the
image at any distinct place. In particular distinct actual cusps have
finite intersection, including their entire wild parts. -/
theorem curveFullInertiaImage_finite_intersection
    {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}
    [IsIntegral X] [IsNormalIntegral X]
    (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c] :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    ∀ [Algebra (RatFunc k) X.functionField]
      [IsScalarTower k (RatFunc k) X.functionField] [FunctionField k X.functionField]
      [HasPrincipalDivisors k X.functionField]
      (v w : Place k X.functionField), v ∉ curveInteriorPlaces c → v ≠ w →
      (curveFullInertiaImage X v ⊓ curveFullInertiaImage X w).carrier.Finite := by
  intro baseAlgebra rationalAlgebra rationalTower functionField principalDivisors v w hv hvw
  apply ((RayClass.finite_localIntegralFunctionUnits v).image (curvePlaceArtin X v)).subset
  rintro z ⟨⟨u, hu, huz⟩, ⟨t, ht, htz⟩⟩
  let a : IdeleGroup k X.functionField :=
    IdeleGroup.placeIdele v u / IdeleGroup.placeIdele w t
  have ha : a ∈ IdeleGroup.integralSubgroup :=
    IdeleGroup.integralSubgroup.div_mem (placeIdele_mem_integralSubgroup v u hu)
      (placeIdele_mem_integralSubgroup w t ht)
  have hker : curveArtin X (IdeleClassGroup.mk a) = 1 := by
    change curveArtin X (IdeleClassGroup.mk
      (IdeleGroup.placeIdele v u / IdeleGroup.placeIdele w t)) = 1
    rw [map_div, map_div, curveArtin_placeIdele, curveArtin_placeIdele]
    exact div_eq_one.mpr (huz.trans htz.symm)
  have hlocal := curveArtin_integral_ker_component_mem c a ha hker v hv
  have hav : a v = u := by
    change IdeleGroup.component v
      (IdeleGroup.placeIdele v u / IdeleGroup.placeIdele w t) = u
    rw [map_div, IdeleGroup.component_placeIdele_same,
      IdeleGroup.component_placeIdele_of_ne w v t hvw, div_one]
  rw [hav] at hlocal
  exact ⟨u, hlocal, huz⟩

/-- The image of an infinite subgroup remains infinite when its kernel is
contained in a finite subgroup of the original source group. -/
private theorem infinite_subgroup_map_of_ker_le_finite
    {A B : Type*} [Group A] [Group B] (f : A →* B)
    (U C : Subgroup A) [Finite C] [Infinite U] (hker : U ⊓ f.ker ≤ C) :
    Infinite (U.map f) := by
  let H := U.map f
  have hU (u : U) : (f.comp U.subtype) u ∈ H :=
    ⟨(u : A), u.property, rfl⟩
  let g : U →* H := (f.comp U.subtype).codRestrict H hU
  have hkerG : g.ker = (f.comp U.subtype).ker :=
    MonoidHom.ker_codRestrict (S := Subgroup B) (f.comp U.subtype) H hU
  let b : g.ker → C := fun a =>
    ⟨(a.val : A), hker ⟨a.val.property, hkerG.le a.property⟩⟩
  have : Finite g.ker := Finite.of_injective b fun a a' haa' => by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c : C => (c : A)) haa'
  apply not_finite_iff_infinite.mp
  intro hfinite
  have : Finite H := hfinite
  let : Fintype H := Fintype.ofFinite H
  let : Fintype g.ker := Fintype.ofFinite g.ker
  let : Fintype U := Group.fintypeOfKerOfCodom g
  exact not_finite U

/-- The full inertia image at every actual boundary place is infinite.
Finiteness of its possible global-unit kernel cannot remove the infinite
local principal-unit direction. -/
theorem curveFullInertiaImage_infinite
    {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}
    [IsIntegral X] [IsNormalIntegral X]
    (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c] :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    ∀ [Algebra (RatFunc k) X.functionField]
      [IsScalarTower k (RatFunc k) X.functionField] [FunctionField k X.functionField]
      [HasPrincipalDivisors k X.functionField]
      (v : Place k X.functionField), v ∉ curveInteriorPlaces c →
      Infinite (curveFullInertiaImage X v) := by
  intro baseAlgebra rationalAlgebra rationalTower functionField principalDivisors v hv
  let U := RayClass.localHigherUnitGroup v 0
  let C := RayClass.localIntegralFunctionUnits v
  let f := curvePlaceArtin X v
  have sourceLaw :=
    @curvePlaceArtin_units_ker_le_localIntegralFunctionUnits
      k ‹Field k› ‹Finite k› X ‹IsIntegral X› ‹IsNormalIntegral X› c
      ‹SmoothOfRelativeDimension 1 c›
  have sourceLawAtInstances :=
    @sourceLaw rationalAlgebra rationalTower functionField principalDivisors
  have hker := sourceLawAtInstances v hv
  have hkerNormalized : U ⊓ f.toMonoidHom.ker ≤ C := by
    dsimp +instances only [U, C, f, baseAlgebra] at hker ⊢
    exact hker
  have : Finite C := RayClass.finite_localIntegralFunctionUnits v
  have : Infinite U := RayClass.infinite_localHigherUnitGroup_zero v
  have hinfinite := infinite_subgroup_map_of_ker_le_finite f.toMonoidHom U C hkerNormalized
  exact hinfinite

end EtaleFundamentalGroups.Inertia
