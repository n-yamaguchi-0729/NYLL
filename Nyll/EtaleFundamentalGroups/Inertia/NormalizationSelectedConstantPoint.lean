/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NormalizationFiberSpecialization
import Nyll.EtaleFundamentalGroups.Cohomology.ClosedPointConstantFilling
import Nyll.GaloisCohomology.FieldTheory.FiniteFrobeniusTower

/-!
# The rational point selected by the original normalization residue

The finite constant field is the actual residue image of the given original
normalization prime in the prescribed closure. Its residue morphism gives
an actual rational point of the same constant cover. The original generic
constant-cover lift specializes at that prime to this very point, retaining
the prescribed residue embedding.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale SchemeTheory
open EtaleFundamentalGroups.Cohomology

namespace EtaleFundamentalGroups.Inertia

attribute [local instance] Ideal.Quotient.field

variable (k R κ Ω : Type)
  [Field k] [Finite k] [CommRing R] [Field κ] [Field Ω]
  [Algebra k R] [Algebra k κ] [Algebra k Ω]
  [Algebra R Ω] [Algebra κ Ω]
  [IsScalarTower k R Ω] [IsScalarTower k κ Ω]
  [Algebra.IsAlgebraic k κ] [Algebra.FiniteType k R] [IsAlgClosed κ]
  (Q : Ideal (normalizationCommAlgCat R Ω)) [Q.IsMaximal]

local notation "E" => normalizationResidueConstantField k R κ Ω Q
local notation "B" => normalizationCommAlgCat R Ω
local notation "c" => Spec.algebraMap k R

private local instance selectedConstantCoverFiniteEtale :
    IsFiniteEtale (Spec.algebraMap k E) := by
  have : FiniteDimensional k E :=
    normalizationResidueConstantField_finiteDimensional k R κ Ω Q
  exact constantField_specMap_isFiniteEtale k E

omit [Finite k] in
/-- The original residue morphism is over the original finite field. -/
theorem normalizationSelectedConstantPoint_over :
    Spec.map (CommRingCat.ofHom (normalizationResidueConstantPoint k R κ Ω Q).toRingHom) ≫
        c = ξ k E := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (normalizationResidueConstantPoint k R κ Ω Q).comp_algebraMap

/-- The actual rational point of the constant cover selected by the same
original normalization prime. -/
def normalizationSelectedConstantPoint :
    Spec (.of E) ⟶ constantBaseChangeCompactification k E c :=
  constantPointLift k E c
    (Spec.map (CommRingCat.ofHom (normalizationResidueConstantPoint k R κ Ω Q).toRingHom))
    (normalizationSelectedConstantPoint_over k R κ Ω Q)

/-- The selected point is rational over exactly the selected residue field. -/
@[reassoc]
theorem normalizationSelectedConstantPoint_structure :
    normalizationSelectedConstantPoint k R κ Ω Q ≫
      constantBaseChangeCompactificationStructure k E c = 𝟙 _ :=
  constantPointLift_structure k E c _ _

/-- The same original residue morphism is retained under the cover map. -/
@[reassoc]
theorem normalizationSelectedConstantPoint_original :
    normalizationSelectedConstantPoint k R κ Ω Q ≫
        ((FiniteEtale.pullback c).obj (originalConstantFieldCover k E)).hom =
      Spec.map (CommRingCat.ofHom (normalizationResidueConstantPoint k R κ Ω Q).toRingHom) :=
  constantPointLift_original k E c _ _

/-- The actual generic lift defined by the prescribed constant inclusion. -/
def normalizationSelectedConstantGenericLift :
    Spec (.of Ω) ⟶ constantBaseChangeCompactification k E c :=
  pullback.lift
    (Spec.map (CommRingCat.ofHom ((algebraMap κ Ω).comp (algebraMap E κ))))
    (Spec.algebraMap R Ω) (by
      change Spec.map (CommRingCat.ofHom ((algebraMap κ Ω).comp (algebraMap E κ))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k E)) =
        Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k R))
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext a
      change algebraMap κ Ω (algebraMap E κ (algebraMap k E a)) =
        algebraMap R Ω (algebraMap k R a)
      rw [← IsScalarTower.algebraMap_apply k E κ,
        ← IsScalarTower.algebraMap_apply k κ Ω,
        ← IsScalarTower.algebraMap_apply k R Ω])

/-- The actual generic lift lies over the original affine generic point. -/
@[reassoc]
theorem normalizationSelectedConstantGenericLift_original :
    normalizationSelectedConstantGenericLift k R κ Ω Q ≫
        ((FiniteEtale.pullback c).obj (originalConstantFieldCover k E)).hom =
      Spec.algebraMap R Ω := pullback.lift_snd _ _ _

/-- Its normalization extension still has the prescribed constant
coordinate, proved by equality at the original generic source. -/
@[reassoc]
theorem normalizationSelectedConstantGenericLift_normalization_structure :
    affineNormalizationLift R Ω
        ((FiniteEtale.pullback c).obj (originalConstantFieldCover k E)).hom
        (normalizationSelectedConstantGenericLift k R κ Ω Q)
        (normalizationSelectedConstantGenericLift_original k R κ Ω Q) ≫
      constantBaseChangeCompactificationStructure k E c =
        Spec.map (CommRingCat.ofHom
          ((arithmeticConstantNormalizationMap k R κ Ω).comp (algebraMap E κ))) := by
  have hfst : normalizationSelectedConstantGenericLift k R κ Ω Q ≫
      constantBaseChangeCompactificationStructure k E c =
      Spec.map (CommRingCat.ofHom ((algebraMap κ Ω).comp (algebraMap E κ))) :=
    pullback.lift_fst _ _ _
  apply affineNormalization_hom_ext R Ω
  rw [← Category.assoc, affineNormalizationLift_generic]
  have hcomp : CommRingCat.ofHom ((algebraMap κ Ω).comp (algebraMap E κ)) =
      CommRingCat.ofHom
        ((arithmeticConstantNormalizationMap k R κ Ω).comp (algebraMap E κ)) ≫
      CommRingCat.ofHom (integralClosure R Ω).val.toRingHom := by
    ext a
    rfl
  exact hfst.trans ((congrArg Spec.map hcomp).trans (Spec.map_comp _ _))

/-- Specializing the original generic constant-cover lift at the original
prime gives the selected rational point, with its fixed κ-embedding. -/
theorem normalizationSelectedConstantPoint_specialization :
    normalizationResiduePoint k R κ Ω Q ≫
        affineNormalizationLift R Ω
          ((FiniteEtale.pullback c).obj (originalConstantFieldCover k E)).hom
          (normalizationSelectedConstantGenericLift k R κ Ω Q)
          (normalizationSelectedConstantGenericLift_original k R κ Ω Q) =
      Spec.algebraMap E κ ≫ normalizationSelectedConstantPoint k R κ Ω Q := by
  let T : Scheme := constantBaseChangeCompactification k E c
  let f : T ⟶ Spec (.of R) :=
    ((FiniteEtale.pullback c).obj (originalConstantFieldCover k E)).hom
  let t : T ⟶ Spec (.of E) := constantBaseChangeCompactificationStructure k E c
  let v : Spec (.of κ) ⟶ Spec (.of B) := normalizationResiduePoint k R κ Ω Q
  let l : Spec (.of B) ⟶ T := affineNormalizationLift R Ω f
    (normalizationSelectedConstantGenericLift k R κ Ω Q)
    (normalizationSelectedConstantGenericLift_original k R κ Ω Q)
  let s : Spec (.of E) ⟶ T := normalizationSelectedConstantPoint k R κ Ω Q
  let e : Spec (.of κ) ⟶ Spec (.of E) := Spec.algebraMap E κ
  change v ≫ l = e ≫ s
  apply pullback.hom_ext
  · have hl : l ≫ t = Spec.map (CommRingCat.ofHom
        ((arithmeticConstantNormalizationMap k R κ Ω).comp (algebraMap E κ))) :=
      normalizationSelectedConstantGenericLift_normalization_structure k R κ Ω Q
    have hv : v ≫ Spec.map (CommRingCat.ofHom
        ((arithmeticConstantNormalizationMap k R κ Ω).comp (algebraMap E κ))) = e := by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]
      congr 1
      ext a
      exact normalizationResidueValue_constant k R κ Ω Q (algebraMap E κ a)
    have hs : s ≫ t = 𝟙 (Spec (.of E)) := normalizationSelectedConstantPoint_structure k R κ Ω Q
    change (v ≫ l) ≫ t = (e ≫ s) ≫ t
    exact ((Category.assoc v l t).trans
      ((congrArg (fun a : Spec (.of B) ⟶ Spec (.of E) => v ≫ a) hl).trans hv)).trans
      ((Category.assoc e s t).trans
        ((congrArg (fun a : Spec (.of E) ⟶ Spec (.of E) => e ≫ a) hs).trans
          (Category.comp_id e))).symm
  · have hl : l ≫ f = Spec.algebraMap R B := affineNormalizationLift_comp R Ω f
        (normalizationSelectedConstantGenericLift k R κ Ω Q)
        (normalizationSelectedConstantGenericLift_original k R κ Ω Q)
    have hs : s ≫ f =
        Spec.map (CommRingCat.ofHom (normalizationResidueConstantPoint k R κ Ω Q).toRingHom) :=
      normalizationSelectedConstantPoint_original k R κ Ω Q
    have he : Spec.map (CommRingCat.ofHom (normalizationResidueConstantMap k R κ Ω Q).toRingHom) =
        e ≫ Spec.map
          (CommRingCat.ofHom (normalizationResidueConstantPoint k R κ Ω Q).toRingHom) := by
      change Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp]
      congr 1
    change (v ≫ l) ≫ f = (e ≫ s) ≫ f
    exact ((Category.assoc v l f).trans
      ((congrArg (fun a : Spec (.of B) ⟶ Spec (.of R) => v ≫ a) hl).trans
        ((normalizationResiduePoint_coefficient k R κ Ω Q).trans he))).trans
      ((Category.assoc e s f).trans
        (congrArg (fun a : Spec (.of E) ⟶ Spec (.of R) => e ≫ a) hs)).symm

/-- Every selected closed-point constant field is fixed by a positive
power of the original arithmetic Frobenius, namely its actual degree. -/
theorem exists_normalizationResidue_frobeniusPower [Fintype k] :
    ∃ n : ℕ, n ≠ 0 ∧
      FiniteField.frobeniusAlgEquivOfAlgebraic k κ ^ n ∈
        (normalizationResidueConstantField k R κ Ω Q).fixingSubgroup := by
  have : FiniteDimensional k E :=
    normalizationResidueConstantField_finiteDimensional k R κ Ω Q
  have : Finite E := Module.finite_of_finite k
  let : Fintype E := Fintype.ofFinite E
  have : Algebra.IsAlgebraic E κ := Algebra.IsAlgebraic.tower_top (K := k) E
  refine ⟨Module.finrank k E, Module.finrank_pos.ne', ?_⟩
  rw [← FiniteField.frobeniusAlgEquiv_restrictScalars k E κ]
  apply (IntermediateField.mem_fixingSubgroup_iff E _).mpr
  intro x hx
  exact (FiniteField.frobeniusAlgEquivOfAlgebraic E κ).commutes ⟨x, hx⟩

end EtaleFundamentalGroups.Inertia
