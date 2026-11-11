/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicClosedProjectiveHomCompletion
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicClosedProjectiveHomFaithfulness
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLevelPullbackModules
public import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal
public import Nyll.SchemeTheory.Modules.Tensor.QuasicoherentTensor
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Actual closed-level compatibility of reconstructed morphisms

The original adjunction identifies the quotient-unit condition in coherent
Hom reconstruction with equality of the actual pullback morphisms. Thus
compatible morphisms on the original closed levels lift uniquely. Equality
of these pullbacks also detects equality before completion, and reflects
their identities, compositions, and tensor products to the original
coherent morphisms. The tensor comparison is the existing native pullback
monoidal comparison.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) (I : Ideal R) {M N : X.Modules}

/-- Equality of the actual pulled-back morphisms is exactly the original
quotient-unit condition after transposing by the native adjunction. -/
theorem levelPullback_map_eq_iff_comp_unit (k : ℕ) (a : M ⟶ N)
    (b : (Scheme.Modules.pullback (Limits.pullback.fst f (baseInclusion I k))).obj M ⟶
      (Scheme.Modules.pullback (Limits.pullback.fst f (baseInclusion I k))).obj N) :
    (Scheme.Modules.pullback (Limits.pullback.fst f (baseInclusion I k))).map a = b ↔
      a ≫ levelPullbackUnit f I N k =
        levelPullbackUnit f I M k ≫
          (pushforward (Limits.pullback.fst f (baseInclusion I k))).map b := by
  let adj := pullbackPushforwardAdjunction (Limits.pullback.fst f (baseInclusion I k))
  have h :
      (adj.homEquiv M
        ((Scheme.Modules.pullback (Limits.pullback.fst f (baseInclusion I k))).obj N))
          ((Scheme.Modules.pullback (Limits.pullback.fst f (baseInclusion I k))).map a) =
        a ≫ levelPullbackUnit f I N k :=
    (adj.homEquiv_unit M
      ((Scheme.Modules.pullback (Limits.pullback.fst f (baseInclusion I k))).obj N)
      ((Scheme.Modules.pullback (Limits.pullback.fst f (baseInclusion I k))).map a)).trans
        (adj.unit_naturality a)
  constructor
  · intro hab
    exact h.symm.trans (congrArg
      (adj.homEquiv M
        ((Scheme.Modules.pullback (Limits.pullback.fst f (baseInclusion I k))).obj N)) hab)
  · intro hab
    apply (adj.homEquiv M
      ((Scheme.Modules.pullback (Limits.pullback.fst f (baseInclusion I k))).obj N)).injective
    exact h.trans hab

end AlgebraicGeometry.FiniteEtale.AdicCoverTower

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules FiniteEtale.AdicCoverTower

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (n : ℕ)
  {Y : Scheme.{u}}
  (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
  [IsClosedImmersion j]

local notation "𝒫" k =>
  Scheme.Modules.pullback
    (Limits.pullback.fst (j ≫ π R n) (baseInclusion (IsLocalRing.maximalIdeal R) k))

variable (M N : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
  [N.IsQuasicoherent] [N.IsFiniteType]

/-- Original coherent morphisms are equal when their actual pullbacks
to every original closed level agree. Completeness is not needed. -/
theorem hom_eq_of_forall_levelPullback_map_eq (a b : M ⟶ N)
    (hab : ∀ k : ℕ, (𝒫 k).map a = (𝒫 k).map b) : a = b := by
  apply sub_eq_zero.mp
  apply hom_eq_zero_of_forall_levelPullbackUnit_comp_eq_zero R n j M N (a - b)
  intro k
  rw [Preadditive.sub_comp, sub_eq_zero]
  have ha := (levelPullback_map_eq_iff_comp_unit
    (j ≫ π R n) (IsLocalRing.maximalIdeal R) k a ((𝒫 k).map b)).mp (hab k)
  have hb := (levelPullback_map_eq_iff_comp_unit
    (j ≫ π R n) (IsLocalRing.maximalIdeal R) k b ((𝒫 k).map b)).mp rfl
  exact ha.trans hb.symm

section Complete

variable [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- A compatible family of actual morphisms between the closed-level
pullbacks comes from a unique original morphism. Compatibility uses the
original adjunction units and the actual quotient transitions. -/
theorem existsUnique_hom_of_compatible_levelPullbackMaps_to_locallyFree
    (hN : finiteFreeLocus N = ⊤)
    (a : ∀ k : ℕ, (𝒫 k).obj M ⟶ (𝒫 k).obj N)
    (ha : ∀ k : ℕ,
      (levelPullbackUnit (j ≫ π R n) (IsLocalRing.maximalIdeal R) M (k + 1) ≫
          (pushforward (Limits.pullback.fst (j ≫ π R n)
            (baseInclusion (IsLocalRing.maximalIdeal R) (k + 1)))).map (a (k + 1))) ≫
        levelPullbackTransition (j ≫ π R n) (IsLocalRing.maximalIdeal R) N k =
      levelPullbackUnit (j ≫ π R n) (IsLocalRing.maximalIdeal R) M k ≫
        (pushforward (Limits.pullback.fst (j ≫ π R n)
          (baseInclusion (IsLocalRing.maximalIdeal R) k))).map (a k)) :
    ∃! φ : M ⟶ N, ∀ k : ℕ, (𝒫 k).map φ = a k := by
  let γ (k : ℕ) : M ⟶
      levelPullbackModule (j ≫ π R n) (IsLocalRing.maximalIdeal R) N k :=
    levelPullbackUnit (j ≫ π R n) (IsLocalRing.maximalIdeal R) M k ≫
      (pushforward (Limits.pullback.fst (j ≫ π R n)
        (baseInclusion (IsLocalRing.maximalIdeal R) k))).map (a k)
  obtain ⟨φ, hφ, _⟩ :=
    existsUnique_hom_of_compatible_levelMaps_to_locallyFree R n j M N hN γ ha
  have hφ' (k : ℕ) : (𝒫 k).map φ = a k :=
    (levelPullback_map_eq_iff_comp_unit
      (j ≫ π R n) (IsLocalRing.maximalIdeal R) k φ (a k)).mpr (hφ k)
  refine ⟨φ, hφ', ?_⟩
  intro ψ hψ
  exact hom_eq_of_forall_levelPullback_map_eq R n j M N ψ φ
    (fun k => (hψ k).trans (hφ' k).symm)

end Complete

omit N [N.IsQuasicoherent] [N.IsFiniteType] in
/-- If all original closed-level reductions of a lifted endomorphism
are identities, the original endomorphism itself is the identity. -/
theorem hom_eq_id_of_forall_levelPullback_map_eq_id (a : M ⟶ M)
    (ha : ∀ k : ℕ, (𝒫 k).map a = 𝟙 ((𝒫 k).obj M)) : a = 𝟙 M := by
  apply hom_eq_of_forall_levelPullback_map_eq R n j M M a (𝟙 M)
  intro k
  exact (ha k).trans ((𝒫 k).map_id M).symm

variable (P : Y.Modules) [P.IsQuasicoherent] [P.IsFiniteType]

omit [N.IsQuasicoherent] [N.IsFiniteType] in
/-- A lift of the actual composites on all closed levels is the
composite of the original lifted morphisms. -/
theorem hom_eq_comp_of_forall_levelPullback_map_eq_comp
    (a : M ⟶ N) (b : N ⟶ P) (c : M ⟶ P)
    (hc : ∀ k : ℕ, (𝒫 k).map c = (𝒫 k).map a ≫ (𝒫 k).map b) : c = a ≫ b := by
  apply hom_eq_of_forall_levelPullback_map_eq R n j M P c (a ≫ b)
  intro k
  exact (hc k).trans ((𝒫 k).map_comp a b).symm

variable (Q : Y.Modules) [Q.IsQuasicoherent] [Q.IsFiniteType]

/-- A lift of the actual levelwise tensor of two lifted morphisms is
their original tensor product, with the native pullback tensor
comparisons. This reflection needs only coherence of the tensor targets,
not an additional local-freeness assumption on them. -/
theorem hom_eq_tensor_of_forall_levelPullback_map_eq_tensor
    (a : M ⟶ N) (b : P ⟶ Q) (c : M ⊗ P ⟶ N ⊗ Q)
    (hc : ∀ k : ℕ,
      (𝒫 k).map c =
        (pullbackTensorObjIso
          (Limits.pullback.fst (j ≫ π R n)
            (baseInclusion (IsLocalRing.maximalIdeal R) k)) M P).hom ≫
          ((𝒫 k).map a ⊗ₘ (𝒫 k).map b) ≫
            (pullbackTensorObjIso
              (Limits.pullback.fst (j ≫ π R n)
                (baseInclusion (IsLocalRing.maximalIdeal R) k)) N Q).inv) :
    c = a ⊗ₘ b := by
  have : (M ⊗ P).IsQuasicoherent := isQuasicoherent_tensor M P
  have : (M ⊗ P).IsFiniteType := isFiniteType_tensor M P
  have : (N ⊗ Q).IsQuasicoherent := isQuasicoherent_tensor N Q
  have : (N ⊗ Q).IsFiniteType := isFiniteType_tensor N Q
  apply hom_eq_of_forall_levelPullback_map_eq R n j (M ⊗ P) (N ⊗ Q) c (a ⊗ₘ b)
  intro k
  exact (hc k).trans (Functor.Monoidal.map_tensor (𝒫 k) a b).symm

end AlgebraicGeometry.ProjSpace
