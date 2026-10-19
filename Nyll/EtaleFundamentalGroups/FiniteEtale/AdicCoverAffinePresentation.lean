/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTwistedAffineSections
import Nyll.SchemeTheory.Modules.Frames.Frames
import Nyll.SchemeTheory.Modules.Invertible.Invertible
import Nyll.SchemeTheory.Modules.Sections.FiniteFreeSections
import Nyll.SchemeTheory.Modules.Sections.FreeHomSections
import Nyll.SchemeTheory.Modules.Tensor.InvertibleCoherence
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.RingTheory.AdicCompletion.QuotientFreeSequence
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# The original quotient-free presentations on an affine chart

Restrict the specified global sections to the original affine open, and
form their linear combination over its actual coefficient quotient.
The resulting presentation retains every original generator and factors
the original free-sheaf section map through the coefficient quotient.

The original global compatibility equation gives a commutative square
with the literal quotient-free transition. Actual epimorphic generating
maps give surjectivity of this constructed affine presentation. The twist
is a power of an invertible sheaf, so its quasicoherence is constructed
from the original frame cover and is not an additional hypothesis.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules AdicModuleSystem

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))
  (L : X.Modules) (d : ℕ) (K : Type u)
  (s : ∀ n : ℕ, K → Γ(tensor (moduleSheaf f I V n) (L.tensorPow d), ⊤))
  (U : X.affineOpens)

/-- The original global generator restricted to the original affine open. -/
def affinePresentationGenerator (n : ℕ) (k : K) :
    twistedAffineSectionModule f I V (L.tensorPow d) U n :=
  (tensor (moduleSheaf f I V n) (L.tensorPow d)).presheaf.map
    (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op (s n k)

variable (t : Γ(L.tensorPow d, U)) (ht : IsFrameOn t (U : X.Opens))

/-- The actual quotient-free linear combination of the original restricted generators. -/
def affineQuotientPresentation (n : ℕ) :
    let _ : Module (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
        (twistedAffineSectionModule f I V (L.tensorPow d) U n) :=
      twistedAffineSectionQuotientModule f I V (L.tensorPow d) U t ht n
    (K →₀ Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1)) →ₗ[
      Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1)]
        twistedAffineSectionModule f I V (L.tensorPow d) U n := by
  intro _moduleQ
  exact Finsupp.linearCombination (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
    (affinePresentationGenerator f I V L d K s U n)

/-- The same constructed presentation with the original affine scalar action. -/
def affinePresentationMap (n : ℕ) :
    (K →₀ Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1)) →ₗ[Γ(X, U)]
      twistedAffineSectionModule f I V (L.tensorPow d) U n := by
  let _moduleQ : Module (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
      (twistedAffineSectionModule f I V (L.tensorPow d) U n) :=
    twistedAffineSectionQuotientModule f I V (L.tensorPow d) U t ht n
  have : IsScalarTower Γ(X, U) (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
      (twistedAffineSectionModule f I V (L.tensorPow d) U n) :=
    twistedAffineSectionQuotient_isScalarTower f I V (L.tensorPow d) U t ht n
  exact (affineQuotientPresentation f I V L d K s U t ht n).restrictScalars Γ(X, U)

/-- Quotienting the original coefficients does not change the original linear combination. -/
theorem affinePresentationMap_coefficients (n : ℕ) (c : K →₀ Γ(X, U)) :
    affinePresentationMap f I V L d K s U t ht n
        (quotientFreeCoefficients ((sectionsIdeal f I U) ^ (n + 1)) K c) =
      Finsupp.linearCombination Γ(X, U) (affinePresentationGenerator f I V L d K s U n) c := by
  let _moduleQ : Module (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
      (twistedAffineSectionModule f I V (L.tensorPow d) U n) :=
    twistedAffineSectionQuotientModule f I V (L.tensorPow d) U t ht n
  have : IsScalarTower Γ(X, U) (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
      (twistedAffineSectionModule f I V (L.tensorPow d) U n) :=
    twistedAffineSectionQuotient_isScalarTower f I V (L.tensorPow d) U t ht n
  exact LinearMap.congr_fun
    (quotientLinearCombination_coefficients (K := K) ((sectionsIdeal f I U) ^ (n + 1))
      (affinePresentationGenerator f I V L d K s U n)) c

/-- Every original basis generator retains its specified original local section. -/
theorem affinePresentationMap_generator (n : ℕ) (k : K) :
    affinePresentationMap f I V L d K s U t ht n (Finsupp.single k 1) =
      affinePresentationGenerator f I V L d K s U n k := by
  simpa only [quotientFreeCoefficients_single, map_one,
    Finsupp.linearCombination_single, one_smul] using
      affinePresentationMap_coefficients f I V L d K s U t ht n (Finsupp.single k 1)

/-- The actual quotient presentation factors the original free-sheaf map on affine sections. -/
theorem affinePresentationMap_coefficients_free [Finite K] (n : ℕ) (c : K →₀ Γ(X, U)) :
    affinePresentationMap f I V L d K s U t ht n
        (quotientFreeCoefficients ((sectionsIdeal f I U) ^ (n + 1)) K c) =
      ((freeHomTopSectionsEquiv (tensor (moduleSheaf f I V n) (L.tensorPow d)) K).symm
        (s n)).app U (finiteFreeSectionsEquiv (X := X) K (U : X.Opens) c) :=
  (affinePresentationMap_coefficients f I V L d K s U t ht n c).trans
    (freeHomTopSectionsEquiv_app_linearCombination (X := X) K (U : X.Opens)
      (tensor (moduleSheaf f I V n) (L.tensorPow d)) (s n) c).symm

/-- Actual epimorphic global generators give a surjective quotient-free affine presentation. -/
theorem affinePresentationMap_surjective [Finite K] (hL : IsInvertible L) (n : ℕ)
    (hgen : Epi ((freeHomTopSectionsEquiv
      (tensor (moduleSheaf f I V n) (L.tensorPow d)) K).symm (s n))) :
    Function.Surjective (affinePresentationMap f I V L d K s U t ht n) := by
  have : (tensor (moduleSheaf f I V n) (L.tensorPow d)).IsQuasicoherent :=
    IsInvertible.isQuasicoherent_tensorPow (moduleSheaf f I V n) hL d
  have : Epi ((freeHomTopSectionsEquiv
      (tensor (moduleSheaf f I V n) (L.tensorPow d)) K).symm (s n)) := hgen
  intro y
  obtain ⟨c, hc⟩ := linearCombination_restriction_surjective_of_epi (X := X) K (U : X.Opens)
    (tensor (moduleSheaf f I V n) (L.tensorPow d)) (s n) U.property y
  exact ⟨quotientFreeCoefficients ((sectionsIdeal f I U) ^ (n + 1)) K c,
    (affinePresentationMap_coefficients f I V L d K s U t ht n c).trans hc⟩

variable (hs : ∀ (n : ℕ) (k : K),
  (moduleTransition f I V n ▷ L.tensorPow d).app ⊤ (s (n + 1) k) = s n k)

include hs

/-- Original global compatibility restricts to the same actual affine generator equation. -/
theorem affinePresentationGenerator_transition (n : ℕ) (k : K) :
    twistedAffineSectionTransition f I V (L.tensorPow d) U n
        (affinePresentationGenerator f I V L d K s U (n + 1) k) =
      affinePresentationGenerator f I V L d K s U n k := by
  let ψ : tensor (moduleSheaf f I V (n + 1)) (L.tensorPow d) ⟶
      tensor (moduleSheaf f I V n) (L.tensorPow d) :=
    moduleTransition f I V n ▷ L.tensorPow d
  have hnat := PresheafOfModules.naturality_apply ψ.val
    (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op (s (n + 1) k)
  exact hnat.trans (congrArg
    ((tensor (moduleSheaf f I V n) (L.tensorPow d)).presheaf.map
      (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op) (hs n k))

/-- The actual quotient-free presentations commute with both original transitions. -/
theorem affinePresentationMap_transition (n : ℕ) :
    (affinePresentationMap f I V L d K s U t ht n).comp
        (quotientFreeFactor K ((sectionsIdeal f I U) ^ (n + 1 + 1))
          (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) =
      (twistedAffineSectionTransition f I V (L.tensorPow d) U n).comp
        (affinePresentationMap f I V L d K s U t ht (n + 1)) := by
  let τ := twistedAffineSectionTransition f I V (L.tensorPow d) U n
  let v := affinePresentationGenerator f I V L d K s U n
  let v' := affinePresentationGenerator f I V L d K s U (n + 1)
  have hv : τ ∘ v' = v := funext (affinePresentationGenerator_transition f I V L d K s U hs n)
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ :=
    quotientFreeCoefficients_surjective ((sectionsIdeal f I U) ^ (n + 1 + 1)) K x
  have hc := LinearMap.congr_fun
    (quotientFreeFactor_coefficients K ((sectionsIdeal f I U) ^ (n + 1 + 1))
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) c
  calc
    affinePresentationMap f I V L d K s U t ht n
        (quotientFreeFactor K ((sectionsIdeal f I U) ^ (n + 1 + 1))
          (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
            (quotientFreeCoefficients ((sectionsIdeal f I U) ^ (n + 1 + 1)) K c)) =
        affinePresentationMap f I V L d K s U t ht n
          (quotientFreeCoefficients ((sectionsIdeal f I U) ^ (n + 1)) K c) :=
      congrArg (affinePresentationMap f I V L d K s U t ht n) hc
    _ = Finsupp.linearCombination Γ(X, U) v c :=
      affinePresentationMap_coefficients f I V L d K s U t ht n c
    _ = τ (Finsupp.linearCombination Γ(X, U) v' c) :=
      ((Finsupp.apply_linearCombination Γ(X, U) τ v' c).trans
        (congrArg (fun w => Finsupp.linearCombination Γ(X, U) w c) hv)).symm
    _ = τ (affinePresentationMap f I V L d K s U t ht (n + 1)
        (quotientFreeCoefficients ((sectionsIdeal f I U) ^ (n + 1 + 1)) K c)) :=
      congrArg τ (affinePresentationMap_coefficients f I V L d K s U t ht (n + 1) c).symm

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
