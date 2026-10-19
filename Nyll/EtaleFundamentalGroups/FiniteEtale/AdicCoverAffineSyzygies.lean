/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAffinePresentation
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTwistedAffineSections
import Nyll.SchemeTheory.Modules.Frames.Frames
import Nyll.SchemeTheory.Modules.Invertible.Invertible
import Nyll.SchemeTheory.Modules.Sections.FreeHomSections
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.RingTheory.AdicCompletion.ProjectivePresentationKernels
import Nyll.SchemeTheory.RingTheory.AdicCompletion.QuotientFreeSequence
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# Actual affine syzygies of the quotient-free cover presentations

The syzygy at each stage is the literal kernel of the constructed
quotient-free presentation, with the original restricted global
generators. The original coefficient transition restricts to these
kernels because the presenting square was proved to commute.

Actual quotient-ring projectivity of the finite étale cover supplies
a splitting, making the syzygy finite projective over the same quotient.
Correction inside the original ideal multiple proves surjectivity of
the kernel transition. The splitting also identifies its kernel with
the specified ideal power in the actual preceding syzygy.

The source is free over the thickening's coefficient quotient. None of
these assertions concerns the kernel of a free sheaf on the unreduced
ambient scheme, which would have a different annihilator.
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
  (U : X.affineOpens) (t : Γ(L.tensorPow d, U)) (ht : IsFrameOn t (U : X.Opens))

/-- The literal kernel of the original quotient-free affine presentation. -/
def affineSyzygyKernel (n : ℕ) :
    Submodule Γ(X, U) (K →₀ Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1)) :=
  (affinePresentationMap f I V L d K s U t ht n).ker

/-- The original quotient-linear presentation gives its actual kernel the same quotient action. -/
@[instance_reducible]
def affineSyzygyQuotientModule (n : ℕ) :
    Module (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
      (affineSyzygyKernel f I V L d K s U t ht n) := by
  let Q := Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1)
  let _moduleP : Module Q (twistedAffineSectionModule f I V (L.tensorPow d) U n) :=
    twistedAffineSectionQuotientModule f I V (L.tensorPow d) U t ht n
  exact inferInstanceAs
    (Module Q (affineQuotientPresentation f I V L d K s U t ht n).ker)

/-- The kernel's quotient action extends its original inherited affine scalar action. -/
theorem affineSyzygyQuotient_isScalarTower (n : ℕ) :
    let _ : Module (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
        (affineSyzygyKernel f I V L d K s U t ht n) :=
      affineSyzygyQuotientModule f I V L d K s U t ht n
    IsScalarTower Γ(X, U) (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
      (affineSyzygyKernel f I V L d K s U t ht n) := by
  intro _moduleQ
  refine ⟨fun a b x => Subtype.ext ?_⟩
  exact smul_assoc a b x.val

/-- The actual kernel is finite projective over the same thickening coefficient quotient. -/
theorem affineSyzygyKernel_finite_projective [Finite K] [IsLocallyNoetherian X]
    (hL : IsInvertible L) (n : ℕ)
    (hgen : Epi ((freeHomTopSectionsEquiv
      (tensor (moduleSheaf f I V n) (L.tensorPow d)) K).symm (s n))) :
    let _ : Module (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
        (affineSyzygyKernel f I V L d K s U t ht n) :=
      affineSyzygyQuotientModule f I V L d K s U t ht n
    Module.Finite (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
        (affineSyzygyKernel f I V L d K s U t ht n) ∧
      Module.Projective (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
        (affineSyzygyKernel f I V L d K s U t ht n) := by
  intro _moduleQ
  let Q := Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1)
  let _moduleP : Module Q (twistedAffineSectionModule f I V (L.tensorPow d) U n) :=
    twistedAffineSectionQuotientModule f I V (L.tensorPow d) U t ht n
  have : Module.Projective Q (twistedAffineSectionModule f I V (L.tensorPow d) U n) :=
    twistedAffineSectionQuotient_projective f I V (L.tensorPow d) U t ht n
  exact presentationKernel_finite_projective
    (affineQuotientPresentation f I V L d K s U t ht n)
    (affinePresentationMap_surjective f I V L d K s U t ht hL n hgen)

/-- The defining ideal power annihilates the actual kernel inside the quotient-free module. -/
theorem affineSyzygyKernel_annihilated (n : ℕ) :
    (sectionsIdeal f I U) ^ (n + 1) •
      (⊤ : Submodule Γ(X, U) (affineSyzygyKernel f I V L d K s U t ht n)) = ⊥ := by
  apply le_antisymm ?_ bot_le
  apply Submodule.smul_le.mpr
  intro a ha x _hx
  apply (Submodule.mem_bot Γ(X, U)).mpr
  apply Subtype.ext
  exact quotientFree_isTorsionBySet ((sectionsIdeal f I U) ^ (n + 1)) K
    (x := x.val) (a := ⟨a, ha⟩)

variable (hs : ∀ (n : ℕ) (k : K),
  (moduleTransition f I V n ▷ L.tensorPow d).app ⊤ (s (n + 1) k) = s n k)

/-- The literal coefficient transition restricted to the actual presentation kernels. -/
def affineSyzygyTransition (n : ℕ) :
    affineSyzygyKernel f I V L d K s U t ht (n + 1) →ₗ[Γ(X, U)]
      affineSyzygyKernel f I V L d K s U t ht n :=
  presentationKernelTransition
    (affinePresentationMap f I V L d K s U t ht (n + 1))
    (affinePresentationMap f I V L d K s U t ht n)
    (quotientFreeFactor K ((sectionsIdeal f I U) ^ (n + 1 + 1))
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
    (twistedAffineSectionTransition f I V (L.tensorPow d) U n)
    (affinePresentationMap_transition f I V L d K s U t ht hs n)

/-- The kernel transition preserves the original coefficient vector and its actual quotient map. -/
theorem affineSyzygyTransition_val (n : ℕ)
    (x : affineSyzygyKernel f I V L d K s U t ht (n + 1)) :
    (affineSyzygyTransition f I V L d K s U t ht hs n x).val =
      quotientFreeFactor K ((sectionsIdeal f I U) ^ (n + 1 + 1))
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) x.val := rfl

/-- Correction in the original ideal multiple makes the actual kernel transition surjective. -/
theorem affineSyzygyTransition_surjective [Finite K] (hL : IsInvertible L) (n : ℕ)
    (hgen : Epi ((freeHomTopSectionsEquiv
      (tensor (moduleSheaf f I V (n + 1)) (L.tensorPow d)) K).symm (s (n + 1)))) :
    Function.Surjective (affineSyzygyTransition f I V L d K s U t ht hs n) :=
  presentationKernelTransition_surjective ((sectionsIdeal f I U) ^ (n + 1))
    (affinePresentationMap f I V L d K s U t ht (n + 1))
    (affinePresentationMap f I V L d K s U t ht n)
    (quotientFreeFactor K ((sectionsIdeal f I U) ^ (n + 1 + 1))
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
    (twistedAffineSectionTransition f I V (L.tensorPow d) U n)
    (affinePresentationMap_transition f I V L d K s U t ht hs n)
    (affinePresentationMap_surjective f I V L d K s U t ht hL (n + 1) hgen)
    (quotientFreeFactor_surjective K ((sectionsIdeal f I U) ^ (n + 1 + 1))
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
    (twistedAffineSectionTransition_ker f I V (L.tensorPow d) U t ht n)
    (quotientFreeFactor_ker K ((sectionsIdeal f I U) ^ (n + 1 + 1))
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).ge

/-- The actual kernel transition has exactly the original adic ideal multiple as kernel. -/
theorem affineSyzygyTransition_ker [Finite K] [IsLocallyNoetherian X]
    (hL : IsInvertible L) (n : ℕ)
    (hgen : Epi ((freeHomTopSectionsEquiv
      (tensor (moduleSheaf f I V (n + 1)) (L.tensorPow d)) K).symm (s (n + 1)))) :
    (affineSyzygyTransition f I V L d K s U t ht hs n).ker =
      (sectionsIdeal f I U) ^ (n + 1) •
        (⊤ : Submodule Γ(X, U) (affineSyzygyKernel f I V L d K s U t ht (n + 1))) := by
  let Q := Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1 + 1)
  let _moduleP : Module Q (twistedAffineSectionModule f I V (L.tensorPow d) U (n + 1)) :=
    twistedAffineSectionQuotientModule f I V (L.tensorPow d) U t ht (n + 1)
  have : IsScalarTower Γ(X, U) Q
      (twistedAffineSectionModule f I V (L.tensorPow d) U (n + 1)) :=
    twistedAffineSectionQuotient_isScalarTower f I V (L.tensorPow d) U t ht (n + 1)
  have : Module.Projective Q
      (twistedAffineSectionModule f I V (L.tensorPow d) U (n + 1)) :=
    twistedAffineSectionQuotient_projective f I V (L.tensorPow d) U t ht (n + 1)
  exact presentationKernelTransition_ker_of_projective_quotient
    ((sectionsIdeal f I U) ^ (n + 1 + 1)) ((sectionsIdeal f I U) ^ (n + 1))
    (affinePresentationMap f I V L d K s U t ht (n + 1))
    (affinePresentationMap f I V L d K s U t ht n)
    (quotientFreeFactor K ((sectionsIdeal f I U) ^ (n + 1 + 1))
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
    (twistedAffineSectionTransition f I V (L.tensorPow d) U n)
    (affinePresentationMap_transition f I V L d K s U t ht hs n)
    (affinePresentationMap_surjective f I V L d K s U t ht hL (n + 1) hgen)
    (quotientFree_isTorsionBySet ((sectionsIdeal f I U) ^ (n + 1 + 1)) K)
    (quotientFreeFactor_ker K ((sectionsIdeal f I U) ^ (n + 1 + 1))
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
