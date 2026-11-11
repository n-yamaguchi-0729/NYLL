/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Normalization.AffineIntegralLift
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AffineFieldSource
public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationResidueEvaluation

/-!
# Specializing original finite-étale fibers at normalization primes

The original generic lift extends to the original integral closure. Its
specialization uses the prescribed constant-residue embedding of the same
normalization prime. The original field-source decomposition action then
specializes to its actual restriction to constants. This construction is
common to all finite-étale covers of the affine chart.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale SchemeTheory

namespace EtaleFundamentalGroups.Inertia

universe u

attribute [local instance] Ideal.Quotient.field normalizationCommAlgGaloisAction

variable (k R κ Ω : Type u)
  [Field k] [CommRing R] [Field κ] [Field Ω]
  [Algebra k R] [Algebra k κ] [Algebra k Ω]
  [Algebra R Ω] [Algebra κ Ω]
  [IsScalarTower k R Ω] [IsScalarTower k κ Ω]
  [Algebra.IsAlgebraic k κ] [Algebra.FiniteType k R] [IsAlgClosed κ]
  (Q : Ideal (normalizationCommAlgCat R Ω)) [Q.IsMaximal]

/-- The geometric residue point on the literal original integral closure. -/
def normalizationResiduePoint :
    Spec (.of κ) ⟶ Spec (.of (normalizationCommAlgCat R Ω)) :=
  Spec.map (CommRingCat.ofHom (normalizationResidueValue k R κ Ω Q))

/-- The coefficient map is the prescribed original geometric residue. -/
@[reassoc]
theorem normalizationResiduePoint_coefficient :
    normalizationResiduePoint k R κ Ω Q ≫
        Spec.algebraMap R (normalizationCommAlgCat R Ω) =
      Spec.map (CommRingCat.ofHom (normalizationResidueConstantMap k R κ Ω Q).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1

/-- Every prescribed constant is retained by the original specialization. -/
@[reassoc]
theorem normalizationResiduePoint_constants :
    normalizationResiduePoint k R κ Ω Q ≫
        Spec.map (CommRingCat.ofHom (arithmeticConstantNormalizationMap k R κ Ω)) =
      𝟙 (Spec (.of κ)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext a
  exact normalizationResidueValue_constant k R κ Ω Q a

variable (F : Type u) [Field F] [Algebra k F] [Algebra R F] [IsFractionRing R F]
  [Algebra F Ω] [IsScalarTower R F Ω] [IsScalarTower k F Ω]
  [IsGalois F Ω] [IsAlgClosure k κ]

/-- The same decomposition element acts on the original geometric
residue point by its literal restriction to the prescribed constants. -/
@[reassoc]
theorem normalizationResiduePoint_decomposition
    (d : normalizationDecompositionGroup R F Ω Q) :
    normalizationResiduePoint k R κ Ω Q ≫
        Spec.map (CommRingCat.ofHom
          (d.val.restrictScalars R).mapIntegralClosure.toRingHom) =
      Spec.map (CommRingCat.ofHom
          ((d.val.restrictScalars k).restrictNormal κ).toRingHom) ≫
        normalizationResiduePoint k R κ Ω Q := by
  let v : CommRingCat.of (normalizationCommAlgCat R Ω) ⟶ CommRingCat.of κ :=
    CommRingCat.ofHom (normalizationResidueValue k R κ Ω Q)
  let a : CommRingCat.of (normalizationCommAlgCat R Ω) ⟶
      CommRingCat.of (normalizationCommAlgCat R Ω) :=
    CommRingCat.ofHom (d.val.restrictScalars R).mapIntegralClosure.toRingHom
  let s : CommRingCat.of κ ⟶ CommRingCat.of κ :=
    CommRingCat.ofHom ((d.val.restrictScalars k).restrictNormal κ).toRingHom
  have h : a ≫ v = v ≫ s := by
    ext b
    have haction : (d.val.restrictScalars R).mapIntegralClosure b = d.val • b := by
      apply Subtype.ext
      exact congrArg (fun f : normalizationCommAlgCat R Ω →+* Ω => f b)
        (normalizationCommAlg_action_comp_inclusion R F Ω d.val)
    change normalizationResidueValue k R κ Ω Q
        ((d.val.restrictScalars R).mapIntegralClosure b) = _
    rw [haction]
    exact normalizationResidueValue_equivariant k R κ Ω Q F d b
  change Spec.map v ≫ Spec.map a = Spec.map s ≫ Spec.map v
  calc
    _ = Spec.map (a ≫ v) := (Spec.map_comp a v).symm
    _ = Spec.map (v ≫ s) := congrArg Spec.map h
    _ = _ := Spec.map_comp v s

variable [IsSepClosure F Ω] [IsSepClosed Ω]

/-- Specialization of an actual native finite-étale covering point at the
same original normalization prime and its fixed constant embedding. -/
def normalizationFiberSpecialization (W : FiniteEtale (Spec (.of R)))
    (z : (fiber (Spec.algebraMap R Ω)).obj W) : Spec (.of κ) ⟶ W.left :=
  normalizationResiduePoint k R κ Ω Q ≫
    affineNormalizationLift R Ω W.hom
      (fiberObjEquivHom (Spec.algebraMap R Ω) W z).left
      (Over.w (fiberObjEquivHom (Spec.algebraMap R Ω) W z))

omit [IsAlgClosure k κ] in
/-- The specialized lift is over the original geometric residue point. -/
@[reassoc]
theorem normalizationFiberSpecialization_comp
    (W : FiniteEtale (Spec (.of R)))
    (z : (fiber (Spec.algebraMap R Ω)).obj W) :
    normalizationFiberSpecialization k R κ Ω Q W z ≫ W.hom =
      Spec.map (CommRingCat.ofHom (normalizationResidueConstantMap k R κ Ω Q).toRingHom) := by
  let p : Spec (.of κ) ⟶ Spec (.of (normalizationCommAlgCat R Ω)) :=
    normalizationResiduePoint k R κ Ω Q
  let l : Spec (.of (normalizationCommAlgCat R Ω)) ⟶ W.left :=
    affineNormalizationLift R Ω W.hom
      (fiberObjEquivHom (Spec.algebraMap R Ω) W z).left
      (Over.w (fiberObjEquivHom (Spec.algebraMap R Ω) W z))
  have hl : l ≫ W.hom = Spec.algebraMap R (normalizationCommAlgCat R Ω) :=
    affineNormalizationLift_comp R Ω W.hom
      (fiberObjEquivHom (Spec.algebraMap R Ω) W z).left
      (Over.w (fiberObjEquivHom (Spec.algebraMap R Ω) W z))
  change (p ≫ l) ≫ W.hom = _
  exact (Category.assoc p l W.hom).trans
    ((congrArg (fun f : Spec (.of (normalizationCommAlgCat R Ω)) ⟶ Spec (.of R) =>
      p ≫ f) hl).trans (normalizationResiduePoint_coefficient k R κ Ω Q))

/-- The actual field-source action specializes to the actual residue
action; no comparison of actions is an input. -/
theorem normalizationFiberSpecialization_fieldSource
    (W : FiniteEtale (Spec (.of R)))
    (d : normalizationDecompositionGroup R F Ω Q)
    (z : (fiber (Spec.algebraMap R Ω)).obj W) :
    normalizationFiberSpecialization k R κ Ω Q W
        (affineFieldSourceHom R F Ω d.val • z) =
      Spec.map (CommRingCat.ofHom
          ((d.val.restrictScalars k).restrictNormal κ).toRingHom) ≫
        normalizationFiberSpecialization k R κ Ω Q W z := by
  have h := affineNormalizationLift_source R Ω W.hom
    (fiberObjEquivHom (Spec.algebraMap R Ω) W z).left
    (fiberObjEquivHom (Spec.algebraMap R Ω) W
      (affineFieldSourceHom R F Ω d.val • z)).left
    (Over.w (fiberObjEquivHom (Spec.algebraMap R Ω) W z))
    (Over.w (fiberObjEquivHom (Spec.algebraMap R Ω) W
      (affineFieldSourceHom R F Ω d.val • z)))
    (d.val.restrictScalars R) (affineFieldSource_fiberLift R F Ω W d.val z)
  let p : Spec (.of κ) ⟶ Spec (.of (normalizationCommAlgCat R Ω)) :=
    normalizationResiduePoint k R κ Ω Q
  let a : Spec (.of (normalizationCommAlgCat R Ω)) ⟶
      Spec (.of (normalizationCommAlgCat R Ω)) :=
    Spec.map (CommRingCat.ofHom (d.val.restrictScalars R).mapIntegralClosure.toRingHom)
  let s : Spec (.of κ) ⟶ Spec (.of κ) :=
    Spec.map (CommRingCat.ofHom ((d.val.restrictScalars k).restrictNormal κ).toRingHom)
  let l : Spec (.of (normalizationCommAlgCat R Ω)) ⟶ W.left :=
    affineNormalizationLift R Ω W.hom
      (fiberObjEquivHom (Spec.algebraMap R Ω) W z).left
      (Over.w (fiberObjEquivHom (Spec.algebraMap R Ω) W z))
  change p ≫ _ = s ≫ (p ≫ l)
  calc
    _ = p ≫ (a ≫ l) :=
      congrArg (fun f : Spec (.of (normalizationCommAlgCat R Ω)) ⟶ W.left => p ≫ f) h
    _ = (p ≫ a) ≫ l := (Category.assoc p a l).symm
    _ = (s ≫ p) ≫ l :=
      congrArg (fun f : Spec (.of κ) ⟶ Spec (.of (normalizationCommAlgCat R Ω)) => f ≫ l)
        (normalizationResiduePoint_decomposition k R κ Ω Q F d)
    _ = _ := Category.assoc s p l

end EtaleFundamentalGroups.Inertia
