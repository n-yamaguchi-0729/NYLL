/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
import Nyll.SchemeTheory.Modules.Frames.Frames
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentLocal
import Nyll.SchemeTheory.Modules.Sections.FreeHomSections
import Nyll.SchemeTheory.Modules.Tensor.InvertibleExactness
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorNilpotentSections
import Nyll.SchemeTheory.Modules.Tensor.TensorPowerFrames
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafFiniteType
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.RingTheory.Ideal.Operations

/-!
# Actual compatible generators of every projective cover thickening

Start with original generating sections of the first twisted cover
module and a compatible family of their original global lifts. The
same index type then generates every stage of the finite étale tower.
The construction uses the original maps from the free sheaf, and these
maps commute with the original twisted cover transitions.

Generation at the next stage is proved on actual tensor frames. The
kernel containment and the nilpotent action come from the actual
untwisted cover section maps. Thus neither generation at later stages
nor the twisted kernel comparison is supplied as an additional input.
The existence of the compatible global lifts is supplied separately
by the proved uniform projective Rees vanishing theorem.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (I : Ideal R) (n : ℕ)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level (π R n) I 0))
  (d : ℕ)

local notation "X" => Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)

/-- The actual twisted module of the original cover at a specified stage. -/
abbrev projectiveTwistedModule (k : ℕ) : (X).Modules :=
  tensor (moduleSheaf (π R n) I V k) ((twistingSheaf R n).tensorPow d)

section Families

variable (K : Type u)
  (s : ∀ k : ℕ, K → Γ(projectiveTwistedModule R I n V d k, ⊤))

/-- The original native free-sheaf morphism of a family of actual
global sections at the specified adic stage. -/
def projectiveTwistedGeneratingMap (k : ℕ) :
    (show (X).Modules from SheafOfModules.free K) ⟶
      projectiveTwistedModule R I n V d k :=
  (sheafOfModulesEquivalence X).inverse.map
    ((projectiveTwistedModule R I n V d k).freeHomEquiv.symm
      (fun i : K => (projectiveTwistedModule R I n V d k).topSection (s k i)))

/-- The original free generator maps to exactly the prescribed global section. -/
theorem projectiveTwistedGeneratingMap_generator (k : ℕ) (i : K) :
    (projectiveTwistedGeneratingMap R I n V d K s k).app ⊤
        ((SheafOfModules.freeSection (R := (X).ringCatSheaf) i).val (op ⊤)) = s k i := by
  let M : (X).Modules := projectiveTwistedModule R I n V d k
  have h := SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
    (fun j : K => M.topSection (s k j)) i
  exact (congrArg (fun t : M.sections => t.val (op ⊤)) h).trans
    (SheafOfModules.topSection_top M (s k i))

/-- The native map is the inverse of the original global-sections
universal property of the free sheaf. -/
theorem projectiveTwistedGeneratingMap_eq_freeHomTopSections (k : ℕ) :
    projectiveTwistedGeneratingMap R I n V d K s k =
      (freeHomTopSectionsEquiv (projectiveTwistedModule R I n V d k) K).symm (s k) := by
  let M : (X).Modules := projectiveTwistedModule R I n V d k
  apply (freeHomTopSectionsEquiv M K).injective
  funext i
  have h := congrFun ((freeHomTopSectionsEquiv M K).apply_symm_apply (s k)) i
  exact (projectiveTwistedGeneratingMap_generator R I n V d K s k i).trans h.symm

/-- The original presenting maps commute with the original twisted
transition whenever the prescribed global sections do. -/
theorem projectiveTwistedGeneratingMap_compatible
    (hs : ∀ (k : ℕ) (i : K),
      (moduleTransition (π R n) I V k ▷ (twistingSheaf R n).tensorPow d).app ⊤
        (s (k + 1) i) = s k i) (k : ℕ) :
    projectiveTwistedGeneratingMap R I n V d K s (k + 1) ≫
        (moduleTransition (π R n) I V k ▷ (twistingSheaf R n).tensorPow d) =
      projectiveTwistedGeneratingMap R I n V d K s k := by
  let M : (X).Modules := projectiveTwistedModule R I n V d (k + 1)
  let N : (X).Modules := projectiveTwistedModule R I n V d k
  let q : M ⟶ N := moduleTransition (π R n) I V k ▷ (twistingSheaf R n).tensorPow d
  apply (freeHomTopSectionsEquiv N K).injective
  funext i
  have hnext : freeHomTopSectionsEquiv M K
      (projectiveTwistedGeneratingMap R I n V d K s (k + 1)) i = s (k + 1) i :=
    projectiveTwistedGeneratingMap_generator R I n V d K s (k + 1) i
  have hcurrent : freeHomTopSectionsEquiv N K
      (projectiveTwistedGeneratingMap R I n V d K s k) i = s k i :=
    projectiveTwistedGeneratingMap_generator R I n V d K s k i
  exact (freeHomTopSectionsEquiv_comp M K
    (projectiveTwistedGeneratingMap R I n V d K s (k + 1)) q i).trans
    ((congrArg (q.app ⊤) hnext).trans ((hs k i).trans hcurrent.symm))

end Families

variable (G : (projectiveTwistedModule R I n V d 0).GeneratingSections)
  (s : ∀ k : ℕ, G.I → Γ(projectiveTwistedModule R I n V d k, ⊤))
  (hzero : ∀ i : G.I, s 0 i = (G.s i).val (op ⊤))
  (hs : ∀ (k : ℕ) (i : G.I),
    (moduleTransition (π R n) I V k ▷ (twistingSheaf R n).tensorPow d).app ⊤
      (s (k + 1) i) = s k i)

include hzero

private theorem initial_generating_map_epi :
    Epi (projectiveTwistedGeneratingMap R I n V d G.I s 0) := by
  let M : (X).Modules := projectiveTwistedModule R I n V d 0
  let E : (X).Modules ≌ SheafOfModules.{u} (X).ringCatSheaf := sheafOfModulesEquivalence X
  have hsections : (fun i : G.I => M.topSection (s 0 i)) = G.s := by
    funext i
    apply (sectionsTopEquiv M).injective
    exact (SheafOfModules.topSection_top M (s 0 i)).trans (hzero i)
  have hmap : projectiveTwistedGeneratingMap R I n V d G.I s 0 =
      E.inverse.map G.π :=
    E.inverse.congr_map (congrArg M.freeHomEquiv.symm hsections)
  have : Epi G.π := G.epi
  have hepi : Epi (E.inverse.map G.π) := CategoryTheory.Functor.map_epi E.inverse G.π
  exact Eq.mp (congrArg (fun p : (show (X).Modules from SheafOfModules.free G.I) ⟶ M =>
    Epi p) hmap.symm) hepi

include hs

/-- The actual lift of the first generating family generates every
stage, by the original affine adic kernel and nilpotent action. -/
theorem projectiveTwistedGeneratingMap_epi (k : ℕ) :
    Epi (projectiveTwistedGeneratingMap R I n V d G.I s k) := by
  induction k with
  | zero => exact initial_generating_map_epi R I n V d G s hzero
  | succ k ih =>
    let P : (X).Modules := SheafOfModules.free G.I
    let L : (X).Modules := (twistingSheaf R n).tensorPow d
    let N : (X).Modules := moduleSheaf (π R n) I V k
    let M : (X).Modules := moduleSheaf (π R n) I V (k + 1)
    let q : M ⟶ N := moduleTransition (π R n) I V k
    let ψ : P ⟶ M ⊗ L := projectiveTwistedGeneratingMap R I n V d G.I s (k + 1)
    have : P.IsQuasicoherent := inferInstance
    have : (tensor N L).IsQuasicoherent :=
      isQuasicoherent_tensor_twistingSheaf R n N d
    have hfac : ψ ≫ (q ▷ L) = projectiveTwistedGeneratingMap R I n V d G.I s k :=
      projectiveTwistedGeneratingMap_compatible R I n V d G.I s hs k
    have : Epi (ψ ≫ (q ▷ L)) := Eq.mp
      (congrArg (fun p : P ⟶ N ⊗ L => Epi p) hfac.symm) ih
    obtain ⟨C, t, ht, hcover⟩ := (isInvertible_twistingSheaf R n).exists_frame_cover
    apply Hom.epi_of_tensor_nilpotent_quotient q ψ C
      (fun i => tensorPowSection (t i) d)
      (fun i => (ht i).tensorPowSection_monoidalV2 d) hcover
      (sectionsIdeal (π R n) I) (k + 2)
    · intro U hU
      have hker := moduleTransition_app_ker (π R n) I V k U hU
      exact hker.le.trans
        (Submodule.smul_mono (Ideal.pow_le_self (Nat.succ_ne_zero k)) le_rfl)
    · intro U _hU
      exact moduleSheaf_sections_annihilated (π R n) I V (k + 1) U

/-- The original compatible global lifts form native generating
sections at every stage, with the original common index type. -/
def projectiveTwistedGeneratingSections (k : ℕ) :
    (projectiveTwistedModule R I n V d k).GeneratingSections where
  I := G.I
  s i := (projectiveTwistedModule R I n V d k).topSection (s k i)
  epi := by
    have : Epi (projectiveTwistedGeneratingMap R I n V d G.I s k) :=
      projectiveTwistedGeneratingMap_epi R I n V d G s hzero hs k
    exact CategoryTheory.Functor.map_epi (sheafOfModulesEquivalence X).functor
      (projectiveTwistedGeneratingMap R I n V d G.I s k)

/-- Each constructed generator is the prescribed original global lift. -/
theorem projectiveTwistedGeneratingSections_top (k : ℕ) (i : G.I) :
    ((projectiveTwistedGeneratingSections R I n V d G s hzero hs k).s i).val (op ⊤) =
      s k i :=
  SheafOfModules.topSection_top (projectiveTwistedModule R I n V d k) (s k i)

/-- Finiteness is retained because the actual index type never changes. -/
theorem projectiveTwistedGeneratingSections_isFiniteType [G.IsFiniteType] (k : ℕ) :
    (projectiveTwistedGeneratingSections R I n V d G s hzero hs k).IsFiniteType :=
  ⟨SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := G)⟩

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
