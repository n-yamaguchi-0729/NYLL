/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.Algebra.PointSpecialization
import Mathlib.Algebra.Algebra.Hom
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Naturality of finite étale point specialization in the local ring

A compatible map between normal rings and their fraction fields preserves
the integral lift of a point. For a local map between Henselian rings,
reduction and its inverse commute with the native map of residue fields.
Together these facts give functoriality of the actual finite étale point
specialization, including its inverse.

The commutative square in the hypotheses consists of the original ring
maps, before any point specialization is performed. No compatibility of
specialization maps is assumed. This is an algebraic compatibility used
in specialization arguments; it does not assert construction of the
proper-family fundamental-group maps of Stacks, Section 58.16.

Mathematical context: https://stacks.math.columbia.edu/tag/0BUP
-/

noncomputable section

namespace SchemeTheory

universe u v w

section IntegralNaturality

variable (H R S : Type u) (L : Type v) (M : Type w) (T : Type u)
  [CommRing H] [CommRing R] [IsIntegrallyClosed R]
  [CommRing S] [IsIntegrallyClosed S] [Field L] [Field M]
  [Algebra H R] [Algebra H S]
  [Algebra R L] [IsFractionRing R L]
  [Algebra S M] [IsFractionRing S M]
  [Algebra H L] [IsScalarTower H R L]
  [Algebra H M] [IsScalarTower H S M]
  [CommRing T] [Algebra H T] [Algebra.IsIntegral H T]

/-- Integral lifts commute with compatible maps of normal rings and
fraction fields. This uses uniqueness inside the target fraction field. -/
theorem integralPointLift_map
    (ι : R →ₐ[H] S) (j : L →ₐ[H] M)
    (hι : ∀ r : R, j (algebraMap R L r) = algebraMap S M (ι r))
    (f : T →ₐ[H] L) :
    integralPointLift H S M T (j.comp f) =
      ι.comp (integralPointLift H R L T f) := by
  apply AlgHom.ext
  intro a
  apply IsFractionRing.injective S M
  calc
    algebraMap S M (integralPointLift H S M T (j.comp f) a) = j (f a) :=
      integralPointLift_evaluation H S M T (j.comp f) a
    _ = j (algebraMap R L (integralPointLift H R L T f a)) :=
      congrArg j (integralPointLift_evaluation H R L T f a).symm
    _ = algebraMap S M (ι (integralPointLift H R L T f a)) :=
      hι (integralPointLift H R L T f a)

end IntegralNaturality

section HenselianNaturality

variable (H R S T : Type u) [CommRing H]
  [CommRing R] [HenselianLocalRing R]
  [CommRing S] [HenselianLocalRing S]
  [Algebra H R] [Algebra H S]
  [CommRing T] [Algebra H T] [Algebra.Etale H T]

/-- Henselian reduction is natural for a local map of its target ring.
The lower map is the residue-field map constructed from that local map. -/
theorem henselianPointReductionEquiv_map
    (ι : R →ₐ[H] S) [IsLocalHom ι] (f : T →ₐ[H] R) :
    henselianPointReductionEquiv H S T (ι.comp f) =
      (IsLocalRing.ResidueField.mapAlgHom ι).comp
        (henselianPointReductionEquiv H R T f) := by
  apply AlgHom.ext
  intro a
  calc
    henselianPointReductionEquiv H S T (ι.comp f) a =
        IsLocalRing.residue S (ι (f a)) :=
      henselianPointReductionEquiv_apply H S T (ι.comp f) a
    _ = IsLocalRing.ResidueField.mapAlgHom ι (IsLocalRing.residue R (f a)) :=
      (IsLocalRing.ResidueField.mapAlgHom_residue ι (f a)).symm
    _ = IsLocalRing.ResidueField.mapAlgHom ι
        (henselianPointReductionEquiv H R T f a) :=
      congrArg (IsLocalRing.ResidueField.mapAlgHom ι)
        (henselianPointReductionEquiv_apply H R T f a).symm

/-- The unique Henselian lift of a residue point is preserved under a local
map of Henselian rings. The lift is the existing constructed inverse. -/
theorem henselianPointReductionEquiv_symm_map
    (ι : R →ₐ[H] S) [IsLocalHom ι]
    (f : T →ₐ[H] IsLocalRing.ResidueField R) :
    (henselianPointReductionEquiv H S T).symm
        ((IsLocalRing.ResidueField.mapAlgHom ι).comp f) =
      ι.comp ((henselianPointReductionEquiv H R T).symm f) := by
  apply (henselianPointReductionEquiv H S T).injective
  rw [Equiv.apply_symm_apply, henselianPointReductionEquiv_map,
    Equiv.apply_symm_apply]

end HenselianNaturality

section SpecializationNaturality

variable (H R S : Type u) (L : Type v) (M : Type w) (T : Type u)
  [CommRing H] [CommRing R] [HenselianLocalRing R] [IsIntegrallyClosed R]
  [CommRing S] [HenselianLocalRing S] [IsIntegrallyClosed S]
  [Field L] [Field M] [Algebra H R] [Algebra H S]
  [Algebra R L] [IsFractionRing R L]
  [Algebra S M] [IsFractionRing S M]
  [Algebra H L] [IsScalarTower H R L]
  [Algebra H M] [IsScalarTower H S M]
  [CommRing T] [Algebra H T] [Module.Finite H T] [Algebra.Etale H T]

/-- Generic-to-residue specialization of finite étale points commutes with
every compatible local ring map and fraction-field map. -/
theorem finiteEtalePointSpecialization_map
    (ι : R →ₐ[H] S) [IsLocalHom ι] (j : L →ₐ[H] M)
    (hι : ∀ r : R, j (algebraMap R L r) = algebraMap S M (ι r))
    (f : T →ₐ[H] L) :
    finiteEtalePointSpecialization H S M T (j.comp f) =
      (IsLocalRing.ResidueField.mapAlgHom ι).comp
        (finiteEtalePointSpecialization H R L T f) := by
  apply AlgHom.ext
  intro a
  calc
    finiteEtalePointSpecialization H S M T (j.comp f) a =
        IsLocalRing.residue S (integralPointLift H S M T (j.comp f) a) :=
      finiteEtalePointSpecialization_apply H S M T (j.comp f) a
    _ = IsLocalRing.residue S (ι (integralPointLift H R L T f a)) :=
      congrArg (IsLocalRing.residue S)
        (AlgHom.congr_fun (integralPointLift_map H R S L M T ι j hι f) a)
    _ = IsLocalRing.ResidueField.mapAlgHom ι
        (IsLocalRing.residue R (integralPointLift H R L T f a)) :=
      (IsLocalRing.ResidueField.mapAlgHom_residue ι
        (integralPointLift H R L T f a)).symm
    _ = IsLocalRing.ResidueField.mapAlgHom ι
        (finiteEtalePointSpecialization H R L T f a) :=
      congrArg (IsLocalRing.ResidueField.mapAlgHom ι)
        (finiteEtalePointSpecialization_apply H R L T f a).symm

/-- The generic point recovered from a specialized point commutes with
the same local ring map and its compatible fraction-field map. -/
theorem finiteEtalePointSpecialization_symm_map
    (ι : R →ₐ[H] S) [IsLocalHom ι] (j : L →ₐ[H] M)
    (hι : ∀ r : R, j (algebraMap R L r) = algebraMap S M (ι r))
    (f : T →ₐ[H] IsLocalRing.ResidueField R) :
    (finiteEtalePointSpecialization H S M T).symm
        ((IsLocalRing.ResidueField.mapAlgHom ι).comp f) =
      j.comp ((finiteEtalePointSpecialization H R L T).symm f) := by
  apply (finiteEtalePointSpecialization H S M T).injective
  rw [Equiv.apply_symm_apply,
    finiteEtalePointSpecialization_map H R S L M T ι j hι,
    Equiv.apply_symm_apply]

end SpecializationNaturality

end SchemeTheory
