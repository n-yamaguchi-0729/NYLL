/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAlgebraizedRelativeSpec
public import Nyll.SchemeTheory.Modules.Functoriality.AlgebraObjectSheaf
public import Nyll.SchemeTheory.ProjectiveSpace.Basic
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAlgebraizedMonoid
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAlgebraizedEtale
public import Nyll.EtaleFundamentalGroups.FiniteEtale.HenselianAscent
public import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperHenselianFullyFaithful
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Mathlib.CategoryTheory.EssentialImage

/-!
# Actual finite étale lifts over a complete local closed projective base

The constructed coherent algebra object has an actual finite étale
relative spectrum. Its original closed-level comparison is cartesian,
so the literal finite étale pullback recovers the given cover. This
supplies essential surjectivity from the original closed-projective data.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteEtale

open AdicCoverTower Scheme.Modules
open AlgebraicCurves.Cohomology.Sheaves.Proofs
open OModulePresheaf_Leray_isQuasicoherent_relHPresheaf_chow.AlgebraicGeometry.OModulePresheaf.Leray

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (n : ℕ)
  {Y : Scheme.{u}}
  (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
  [IsClosedImmersion j]

/-- A given finite étale cover of the original closed fiber has an
actual finite étale lift over the original closed-projective scheme. -/
theorem exists_closedProjective_finiteEtale_lift
    (V : FiniteEtale (level (j ≫ ProjSpace.π R n) (IsLocalRing.maximalIdeal R) 0)) :
    ∃ W : FiniteEtale Y,
      Nonempty ((FiniteEtale.pullback
        (Limits.pullback.fst (j ≫ ProjSpace.π R n)
          (baseInclusion (IsLocalRing.maximalIdeal R) 0))).obj W ≅ V) := by
  let f := j ≫ ProjSpace.π R n
  let I := IsLocalRing.maximalIdeal R
  let V' : MorphismProperty.Over
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0) :=
    MorphismProperty.Over.mk ⊤ V.hom ⟨inferInstance, inferInstance⟩
  obtain ⟨F, hFqc, hFft, hFfree, m, hm⟩ :=
    exists_closedProjective_commMonObj_algebraization R n j V'
  have : F.IsQuasicoherent := hFqc
  have : F.IsFiniteType := hFft
  let _ : MonObj F := m
  have : IsCommMonObj F := hm.1
  obtain ⟨s, hsIso, _hs, hsMon⟩ := hm.2
  have : IsMonHom (s 0) := hsMon 0
  have : IsIso
      ((Scheme.Modules.pullback (Limits.pullback.fst f (baseInclusion I 0))).map (s 0)) :=
    hsIso 0
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  let p := Scheme.RelativeSpec.toBase (AlgebraObject.structureMap F)
  have hfinite : IsFinite p := AlgebraObject.isFinite_toBase F
  have hetale : Etale p := algebraizedCover_etale f F V' (s 0) hFfree
  have : IsFiniteEtale p := ⟨⟩
  let W : FiniteEtale Y := FiniteEtale.mk p
  have hcart := algebraizedCoverMap_isPullback f I V' F 0 (s 0)
  refine ⟨W, ⟨?_⟩⟩
  exact MorphismProperty.Over.isoMk hcart.isoPullback.symm hcart.isoPullback_inv_snd

/-- The literal finite étale pullback to the zeroth adic level is
essentially surjective over a complete Noetherian local closed-projective
base. -/
theorem pullback_essSurj_closedProjective_of_isAdicComplete :
    (FiniteEtale.pullback
      (Limits.pullback.fst (j ≫ ProjSpace.π R n)
        (baseInclusion (IsLocalRing.maximalIdeal R) 0))).EssSurj where
  mem_essImage V := exists_closedProjective_finiteEtale_lift R n j V

/-- Complete-local closed-projective restriction is an equivalence.
Its full faithfulness is the existing proper henselian-local theorem,
and essential surjectivity is supplied by the actual relative spectrum. -/
theorem pullback_isEquivalence_closedProjective_of_isAdicComplete :
    (FiniteEtale.pullback
      (Limits.pullback.fst (j ≫ ProjSpace.π R n)
        (baseInclusion (IsLocalRing.maximalIdeal R) 0))).IsEquivalence := by
  have : HenselianLocalRing R :=
    EtaleFundamentalGroups.henselianLocalRing_of_finiteEtale_local_of_isAdicComplete
      (R := R) (S := R)
  let FF := pullbackFullyFaithful_closedFiber_of_isProper_of_henselianLocalRing
    (j ≫ ProjSpace.π R n)
  exact
    { faithful := FF.faithful
      full := FF.full
      essSurj := pullback_essSurj_closedProjective_of_isAdicComplete R n j }

/-- The comparison equivalence has the original closed-fiber pullback
as its forward functor. -/
def closedProjectiveFiniteEtaleEquivalence :
    FiniteEtale Y ≌
      FiniteEtale (level (j ≫ ProjSpace.π R n) (IsLocalRing.maximalIdeal R) 0) := by
  have : (FiniteEtale.pullback
      (Limits.pullback.fst (j ≫ ProjSpace.π R n)
        (baseInclusion (IsLocalRing.maximalIdeal R) 0))).IsEquivalence :=
    pullback_isEquivalence_closedProjective_of_isAdicComplete R n j
  exact (FiniteEtale.pullback
    (Limits.pullback.fst (j ≫ ProjSpace.π R n)
      (baseInclusion (IsLocalRing.maximalIdeal R) 0))).asEquivalence

end AlgebraicGeometry.FiniteEtale
