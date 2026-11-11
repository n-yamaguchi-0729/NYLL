/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.Tame.BoundaryWildRayComparison
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayDecomposition
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayInertia
public import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationInertiaTopology
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayEmbedding
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RayArtinRamification

/-!
# Original local normalization images through the original generic map

The source maps here are the actual valuation-normalization inertia and
decomposition inclusions followed by the original field-source map to
the original fundamental group. Their original abelian images are
compared with ordinary local Artin units and the absolute local Artin
closure using the actual induced generic abelian map.

Passing through the proved native boundary-wild/ray comparison sends the
original decomposition image to the actual closed local ray image. This
supplies the local-closure comparison from recovered original
decomposition data, without an extra equality-after-quotient premise.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open AlgebraicCurve SchemeTheory LocalClassFieldTheory TopologicalSpace

namespace EtaleFundamentalGroups.Tame

open Inertia

attribute [local instance]
  normalizationCommAlgGaloisAction
  Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring
  Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
  FunctionField.placeAmbientAlgebra
  FunctionField.placeAmbientTower
  FunctionField.placeStageAmbientTower

section NativeLocalImages

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
  {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The original inertia inclusion followed by an arbitrary original
absolute Galois map, formed before specializing its target. -/
def placeGaloisInertiaHom (f : Gal(SeparableClosure F/F) →ₜ* H)
    (v : Place k F)
    (Q : Ideal (normalizationCommAlgCat v.toValuationSubring (SeparableClosure F))) :
    (actualNormalizationInertiaGroup v.toValuationSubring F
      (SeparableClosure F) Q).carrier →ₜ* H :=
  { toMonoidHom := f.toMonoidHom.comp (Q.inertia Gal(SeparableClosure F/F)).subtype
    continuous_toFun := f.continuous_toFun.comp continuous_subtype_val }

/-- The same original decomposition inclusion with an abstract target. -/
def placeGaloisDecompositionHom (f : Gal(SeparableClosure F/F) →ₜ* H)
    (v : Place k F)
    (Q : Ideal (normalizationCommAlgCat v.toValuationSubring (SeparableClosure F))) :
    normalizationDecompositionGroup v.toValuationSubring F (SeparableClosure F) Q →* H :=
  f.toMonoidHom.comp
    (normalizationDecompositionInclusion v.toValuationSubring F (SeparableClosure F) Q)

/-- Decomposition naturality is checked on the native quotient before
any scheme fiber functor is substituted for the target group. -/
private theorem placeGaloisDecompositionHom_abelian_range
    (f : Gal(SeparableClosure F/F) →ₜ* H) (v : Place k F)
    (Q : Ideal (normalizationCommAlgCat v.toValuationSubring (SeparableClosure F))) :
    (placeGaloisDecompositionHom f v Q).range.map
      (ProCGroups.Abelian.TopologicalAbelianization.mk H) =
        (FunctionField.placeAbsoluteDecomposition v Q).map
          (ProCGroups.Abelian.TopologicalAbelianization.map f).toMonoidHom := by
  apply Subgroup.ext
  intro a
  constructor
  · rintro ⟨γ, ⟨d, rfl⟩, rfl⟩
    exact ⟨localAbsoluteAbelianizationQuotientMap F d.val, ⟨d, rfl⟩,
      ProCGroups.Abelian.TopologicalAbelianization.map_apply_mk f d.val⟩
  · rintro ⟨a, ⟨d, rfl⟩, rfl⟩
    exact ⟨f d.val, ⟨d, rfl⟩,
      (ProCGroups.Abelian.TopologicalAbelianization.map_apply_mk f d.val).symm⟩

/-- Naturality of the original inertia image on native quotient
representatives, before the local Artin map is introduced. -/
private theorem placeGaloisInertiaHom_abelian_absolute_range
    (f : Gal(SeparableClosure F/F) →ₜ* H) (v : Place k F)
    (Q : Ideal (normalizationCommAlgCat v.toValuationSubring (SeparableClosure F))) :
    (placeGaloisInertiaHom f v Q).toMonoidHom.range.map
      (ProCGroups.Abelian.TopologicalAbelianization.mk H) =
        (FunctionField.placeAbsoluteInertia v Q).map
          (ProCGroups.Abelian.TopologicalAbelianization.map f).toMonoidHom := by
  apply Subgroup.ext
  intro a
  constructor
  · rintro ⟨γ, ⟨σ, rfl⟩, rfl⟩
    exact ⟨localAbsoluteAbelianizationQuotientMap F σ.val, ⟨σ.val, σ.property, rfl⟩,
      ProCGroups.Abelian.TopologicalAbelianization.map_apply_mk f σ.val⟩
  · rintro ⟨a, ⟨σ, hσ, rfl⟩, rfl⟩
    exact ⟨f σ, ⟨⟨σ, hσ⟩, rfl⟩,
      (ProCGroups.Abelian.TopologicalAbelianization.map_apply_mk f σ).symm⟩

variable [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FunctionField k F] [HasPrincipalDivisors k F]

/-- Ordinary inertia comparison with the native absolute abelian map,
retaining the original place prime and an abstract target group. -/
private theorem placeGaloisInertiaHom_abelian_range
    (f : Gal(SeparableClosure F/F) →ₜ* H) (v : Place k F)
    (Q : Ideal (normalizationCommAlgCat v.toValuationSubring (SeparableClosure F)))
    [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring)] :
    (placeGaloisInertiaHom f v Q).toMonoidHom.range.map
      (ProCGroups.Abelian.TopologicalAbelianization.mk H) =
        (FunctionField.RayClass.placeArtinUnitImage v 0).map
          (ProCGroups.Abelian.TopologicalAbelianization.map f).toMonoidHom := by
  let q : Ideal (integralClosure v.toValuationSubring (SeparableClosure F)) := Q
  have qPrime : q.IsPrime := inferInstanceAs Q.IsPrime
  have qOver : q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring) :=
    inferInstanceAs (Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring))
  have hInertiaInferred :=
    @FunctionField.RayClass.placeAbsoluteInertia_eq_placeArtinUnitImage
      k F ‹Field k› ‹Finite k› ‹Field F› ‹Algebra k F›
      ‹Algebra (RatFunc k) F› ‹IsScalarTower k (RatFunc k) F›
      ‹FunctionField k F› ‹HasPrincipalDivisors k F› v q qPrime qOver
  have hInertia : FunctionField.placeAbsoluteInertia v q =
      FunctionField.RayClass.placeArtinUnitImage v 0 := hInertiaInferred
  exact (placeGaloisInertiaHom_abelian_absolute_range f v Q).trans
    (congrArg (fun S : Subgroup (localAbsoluteAbelianProfinite F) =>
      S.map (ProCGroups.Abelian.TopologicalAbelianization.map f).toMonoidHom) hInertia)

/-- The actual local Artin closure comparison is transported with an
abstract target, using the same native prime throughout. -/
private theorem placeGaloisDecompositionHom_abelian_localClosure
    (f : Gal(SeparableClosure F/F) →ₜ* H) (v : Place k F)
    (Q : Ideal (normalizationCommAlgCat v.toValuationSubring (SeparableClosure F)))
    [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring)] :
    (placeGaloisDecompositionHom f v Q).range.map
      (ProCGroups.Abelian.TopologicalAbelianization.mk H) =
        (FunctionField.placeAbsoluteArtin v).range.topologicalClosure.map
          (ProCGroups.Abelian.TopologicalAbelianization.map f).toMonoidHom := by
  let q : Ideal (integralClosure v.toValuationSubring (SeparableClosure F)) := Q
  have qPrime : q.IsPrime := inferInstanceAs Q.IsPrime
  have qOver : q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring) :=
    inferInstanceAs (Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring))
  have hDecompositionInferred :=
    @FunctionField.placeAbsoluteArtin_closure_eq_decomposition
      k F ‹Field k› ‹Finite k› ‹Field F› ‹Algebra k F›
      ‹Algebra (RatFunc k) F› ‹IsScalarTower k (RatFunc k) F›
      ‹FunctionField k F› ‹HasPrincipalDivisors k F› v q qPrime qOver
  have hDecomposition : (FunctionField.placeAbsoluteArtin v).range.topologicalClosure =
      FunctionField.placeAbsoluteDecomposition v q := hDecompositionInferred
  exact (placeGaloisDecompositionHom_abelian_range f v Q).trans
    (congrArg (fun S : Subgroup (localAbsoluteAbelianProfinite F) =>
      S.map (ProCGroups.Abelian.TopologicalAbelianization.map f).toMonoidHom)
      hDecomposition.symm)

end NativeLocalImages

section SuppliedSource

variable {k F : Type u} [Field k] [Finite k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FunctionField k F] [HasPrincipalDivisors k F]
  {U : Scheme.{u}} [IsIntegral U] (p : Spec (.of F) ⟶ U)

local notation "Ω" => SeparableClosure F
local notation "G" => Gal(SeparableClosure F/F)
local notation "Π" => π₁ᵉᵗ(ξ F (SeparableClosure F) ≫ p)
local notation "Ab" => ProCGroups.Abelian.TopologicalAbelianization.mk

/-- Original valuation-normalization inertia enters the original
fundamental group through its literal original generic Galois map. -/
def placeFieldSourceInertiaHom (v : Place k F)
    (Q : Ideal (normalizationCommAlgCat v.toValuationSubring Ω)) :
    (actualNormalizationInertiaGroup v.toValuationSubring F Ω Q).carrier →ₜ* Π :=
  placeGaloisInertiaHom (k := k) (F := F) (H := Π)
    (fieldSourceAbsoluteGaloisHom F Ω p) v Q

omit [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FunctionField k F] [HasPrincipalDivisors k F] [IsIntegral U] in
/-- The source element remains the same original field automorphism. -/
theorem placeFieldSourceInertiaHom_apply (v : Place k F)
    (Q : Ideal (normalizationCommAlgCat v.toValuationSubring Ω))
    (σ : (actualNormalizationInertiaGroup v.toValuationSubring F Ω Q).carrier) :
    placeFieldSourceInertiaHom p v Q σ = fieldSourceAbsoluteGaloisHom F Ω p σ.val := rfl

/-- Original valuation-normalization decomposition enters through the
same original field-source map, with its original stabilizer inclusion. -/
def placeFieldSourceDecompositionHom (v : Place k F)
    (Q : Ideal (normalizationCommAlgCat v.toValuationSubring Ω)) :
    normalizationDecompositionGroup v.toValuationSubring F Ω Q →* Π :=
  placeGaloisDecompositionHom (k := k) (F := F) (H := Π)
    (fieldSourceAbsoluteGaloisHom F Ω p) v Q

omit [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FunctionField k F] [HasPrincipalDivisors k F] [IsIntegral U] in
/-- Original decomposition representatives are not changed by the map. -/
theorem placeFieldSourceDecompositionHom_apply (v : Place k F)
    (Q : Ideal (normalizationCommAlgCat v.toValuationSubring Ω))
    (d : normalizationDecompositionGroup v.toValuationSubring F Ω Q) :
    placeFieldSourceDecompositionHom p v Q d =
      fieldSourceAbsoluteGaloisHom F Ω p d.val := rfl

omit [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FunctionField k F] [HasPrincipalDivisors k F] [IsIntegral U] in
/-- The actual source decomposition image is compact in the original
fundamental-group topology. -/
theorem isCompact_placeFieldSourceDecompositionHom_range (v : Place k F)
    (Q : Ideal (normalizationCommAlgCat v.toValuationSubring Ω)) :
    IsCompact ((placeFieldSourceDecompositionHom p v Q).range : Set Π) :=
  normalizationDecompositionImage_isCompact v.toValuationSubring F Ω Q
    (fieldSourceAbsoluteGaloisHom F Ω p)

omit [IsIntegral U] in
/-- The native inertia image in the original fundamental-group
abelianization is exactly the ordinary-unit image carried by the
original induced abelian generic map. Any actual prime over the place
maximal ideal gives this same image. -/
theorem placeFieldSourceInertiaHom_abelian_range (v : Place k F)
    (Q : Ideal (normalizationCommAlgCat v.toValuationSubring Ω))
    [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring)] :
    (placeFieldSourceInertiaHom p v Q).toMonoidHom.range.map (Ab Π) =
      (FunctionField.RayClass.placeArtinUnitImage v 0).map
        (ProCGroups.Abelian.TopologicalAbelianization.map
          (fieldSourceAbsoluteGaloisHom F Ω p)).toMonoidHom := by
  exact placeGaloisInertiaHom_abelian_range (k := k) (F := F) (H := Π)
    (fieldSourceAbsoluteGaloisHom F Ω p) v Q

omit [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FunctionField k F] [HasPrincipalDivisors k F] [IsIntegral U] in
/-- The original decomposition image has the original absolute
decomposition image under the same induced generic abelian map. -/
theorem placeFieldSourceDecompositionHom_abelian_range (v : Place k F)
    (Q : Ideal (normalizationCommAlgCat v.toValuationSubring Ω)) :
    (placeFieldSourceDecompositionHom p v Q).range.map (Ab Π) =
      (FunctionField.placeAbsoluteDecomposition v Q).map
        (ProCGroups.Abelian.TopologicalAbelianization.map
          (fieldSourceAbsoluteGaloisHom F Ω p)).toMonoidHom := by
  exact placeGaloisDecompositionHom_abelian_range (k := k) (F := F) (H := Π)
    (fieldSourceAbsoluteGaloisHom F Ω p) v Q

omit [IsIntegral U] in
/-- At an actual place prime, the original decomposition image is
precisely the transported closure of the actual one-place Artin image. -/
theorem placeFieldSourceDecompositionHom_abelian_localClosure (v : Place k F)
    (Q : Ideal (normalizationCommAlgCat v.toValuationSubring Ω))
    [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring)] :
    (placeFieldSourceDecompositionHom p v Q).range.map (Ab Π) =
      (FunctionField.placeAbsoluteArtin v).range.topologicalClosure.map
        (ProCGroups.Abelian.TopologicalAbelianization.map
          (fieldSourceAbsoluteGaloisHom F Ω p)).toMonoidHom := by
  exact placeGaloisDecompositionHom_abelian_localClosure (k := k) (F := F) (H := Π)
    (fieldSourceAbsoluteGaloisHom F Ω p) v Q

end SuppliedSource

section GenericRay

variable {k F : Type u} [Field k] [Finite k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FunctionField k F] [HasPrincipalDivisors k F]
  {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U] [IsNormalIntegral U]
  (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c] [IsProper c]
  (j : U ⟶ X) [IsOpenImmersion j]
  (p : Spec (.of F) ⟶ U) [IsDominant p] [IsPreimmersion p]
  (hp : p ≫ (j ≫ c) = Spec.map (CommRingCat.ofHom (algebraMap k F)))

local notation "Ω" => SeparableClosure F
local notation "m" => genericSourceBoundaryModulus c j p hp

/-- For an actual generic field source, the native decomposition image
maps onto the closure of its local ray Artin image. The same field
automorphism represents both sides of the comparison. -/
theorem placeFieldSourceDecompositionHom_genericRay_range (v : Place k F)
    (Q : Ideal (normalizationCommAlgCat v.toValuationSubring Ω))
    [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring)] :
    (placeFieldSourceDecompositionHom p v Q).range.map
        (genericBoundaryRayHom c j p hp).toMonoidHom =
      (FunctionField.RayClass.localRayAbsoluteArtin m v).range.topologicalClosure := by
  let q : Ideal (integralClosure v.toValuationSubring Ω) := Q
  have qPrime : q.IsPrime := inferInstanceAs Q.IsPrime
  have qOver : q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring) :=
    inferInstanceAs (Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring))
  have hDecomposition :=
    @FunctionField.RayClass.localRayAbsoluteArtin_closure_eq_decomposition
      k F ‹Field k› ‹Finite k› ‹Field F› ‹Algebra k F›
      ‹Algebra (RatFunc k) F› ‹IsScalarTower k (RatFunc k) F›
      ‹FunctionField k F› ‹HasPrincipalDivisors k F› m v q qPrime qOver
  rw [hDecomposition]
  apply Subgroup.ext
  intro a
  constructor
  · rintro ⟨γ, ⟨d, rfl⟩, rfl⟩
    exact ⟨d, (genericBoundaryRayHom_fieldSource c j p hp d.val).symm⟩
  · rintro ⟨d, rfl⟩
    exact ⟨fieldSourceAbsoluteGaloisHom F Ω p d.val, ⟨d, rfl⟩,
      genericBoundaryRayHom_fieldSource c j p hp d.val⟩

end GenericRay

section CanonicalRay

attribute [local instance] AlgebraicGeometry.FiniteEtale.genericPoint_isDominant

variable {k : Type u} [Field k] [Finite k]
  {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U] [IsNormalIntegral U]
  (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c] [IsProper c]
  (j : U ⟶ X) [IsOpenImmersion j]

local notation "p" => U.fromSpecStalk (genericPoint U)

/-- The original ray map sends the actual native decomposition image
onto exactly the actual closed local ray-Artin image. Thus recovered
original decomposition-image correspondence supplies the closed-local
condition used by multiplicative reconstruction. -/
theorem placeFieldSourceDecompositionHom_ray_range :
    let _ : Algebra k U.functionField := (baseToFunctionField (j ≫ c)).toAlgebra
    ∀ [Algebra (RatFunc k) U.functionField]
      [IsScalarTower k (RatFunc k) U.functionField]
      [FunctionField k U.functionField] [HasPrincipalDivisors k U.functionField],
    ∀ (v : Place k U.functionField)
    (Q : Ideal (normalizationCommAlgCat v.toValuationSubring (SeparableClosure U.functionField)))
    [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring)],
    (placeFieldSourceDecompositionHom p v Q).range.map
        (originalBoundaryRayHom c j).toMonoidHom =
      (FunctionField.RayClass.localRayAbsoluteArtin
        (openSourceBoundaryModulus c j) v).range.topologicalClosure := by
  intro baseAlgebra rationalAlgebra rationalTower functionField principalDivisors v Q hQ hQover
  exact placeFieldSourceDecompositionHom_genericRay_range c j p
    (fromSpecStalk_genericPoint_comp_base (j ≫ c)) v Q

end CanonicalRay

end EtaleFundamentalGroups.Tame
