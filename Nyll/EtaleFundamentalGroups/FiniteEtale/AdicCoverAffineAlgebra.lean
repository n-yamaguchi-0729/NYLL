/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAffineCompletion
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteAlgebraSystem
import Nyll.SchemeTheory.RingTheory.AdicCompletion.AdicCompletionNoetherian
import Nyll.SchemeTheory.RingTheory.AdicCompletion.IsLocalizationAtPrimeRingEquivAdicCompletionMaximalIdeal
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# The actual completed affine algebra of the finite étale cover tower

The algebra consists of compatible sequences in the original affine section
rings of the actual covers. The completed coefficient ring acts through its
literal quotient projections and the original coefficient maps. This gives
one compatible algebra structure at every stage, without assigning a ring
structure to a module completion.

The actual cover tower supplies finite stages, surjective transitions, exact
adic kernels, and annihilation. On a locally Noetherian scheme these facts
prove that the constructed algebra is finite over the completed affine ring.
Its algebra quotients recover the original section rings, including their
unit, multiplication, evaluation, and transition maps. A concrete linear
comparison also retains the previously constructed completed section module.

This is affine algebra effectivity for the genuine tower. It does not assert
coherent algebraization on the ordinary scheme or construct a finite cover
of that scheme.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite
open AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
open IsLocalization_AtPrime_exists_ringEquiv_adicCompletion_maximalIdeal.L1BAdic

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))

/-- The original section ring of the actual cover over the given affine open. -/
def affineSectionRing (U : X.affineOpens) (n : ℕ) : CommRingCat.{u} :=
  (algebraSheaf f I V n).obj.obj (op (U : X.Opens))

/-- Its coefficient action is the actual finite morphism's section map. -/
instance affineSectionRing_algebra (U : X.affineOpens) (n : ℕ) :
    Algebra Γ(X, U) (affineSectionRing f I V U n) :=
  ((coverToOriginal f I V n).app U).hom.toAlgebra

/-- The original algebra transition retains the actual cover's section map. -/
def affineSectionAlgebraTransition (U : X.affineOpens) (n : ℕ) :
    affineSectionRing f I V U (n + 1) →ₐ[Γ(X, U)] affineSectionRing f I V U n where
  __ := ((algebraTransition f I V n).hom.app (op (U : X.Opens))).hom
  commutes' a :=
    congrArg (fun k : X.sheaf ⟶ algebraSheaf f I V n =>
      (k.hom.app (op (U : X.Opens))).hom a) (algebraStructure_transition f I V n)

/-- The prescribed ideal power vanishes in the original section algebra. -/
theorem affineSectionRing_power_map_eq_bot (U : X.affineOpens) (n : ℕ) :
    ((sectionsIdeal f I U) ^ (n + 1)).map
      (algebraMap Γ(X, U) (affineSectionRing f I V U n)) = ⊥ := by
  apply (Ideal.map_eq_bot_iff_le_ker _).mpr
  intro a ha
  have hpow : (sectionsIdeal f I U) ^ (n + 1) •
      (⊤ : Submodule Γ(X, U) (affineSectionRing f I V U n)) = ⊥ :=
    moduleSheaf_sections_annihilated f I V n U
  have hmem : a • (1 : affineSectionRing f I V U n) ∈
      (sectionsIdeal f I U) ^ (n + 1) •
        (⊤ : Submodule Γ(X, U) (affineSectionRing f I V U n)) :=
    Submodule.smul_mem_smul ha (show (1 : affineSectionRing f I V U n) ∈
      (⊤ : Submodule Γ(X, U) (affineSectionRing f I V U n)) from trivial)
  rw [hpow] at hmem
  change algebraMap Γ(X, U) (affineSectionRing f I V U n) a * 1 = 0 at hmem
  rw [mul_one] at hmem
  exact hmem

/-- Original coefficients descend through the literal adic quotient. -/
def affineSectionQuotientAlgebraMap (U : X.affineOpens) (n : ℕ) :
    (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1)) →ₐ[Γ(X, U)]
      affineSectionRing f I V U n :=
  Ideal.Quotient.liftₐ ((sectionsIdeal f I U) ^ (n + 1))
    (Algebra.ofId Γ(X, U) (affineSectionRing f I V U n))
    (fun a ha =>
      show algebraMap Γ(X, U) (affineSectionRing f I V U n) a = 0 from
        (Ideal.map_eq_bot_iff_le_ker
          (algebraMap Γ(X, U) (affineSectionRing f I V U n))).mp
            (affineSectionRing_power_map_eq_bot f I V U n) ha)

/-- The completed coefficient map is the actual quotient projection followed
by the original section coefficient map. -/
def affineSectionCompletionCoefficient (U : X.affineOpens) (n : ℕ) :
    AdicCompletion (sectionsIdeal f I U) Γ(X, U) →ₐ[Γ(X, U)]
      affineSectionRing f I V U n :=
  (affineSectionQuotientAlgebraMap f I V U n).comp
    (AdicCompletion.evalₐ (sectionsIdeal f I U) (n + 1))

/-- The single completed-ring action on the original section ring. -/
instance affineSectionRing_completedAlgebra (U : X.affineOpens) (n : ℕ) :
    Algebra (AdicCompletion (sectionsIdeal f I U) Γ(X, U))
      (affineSectionRing f I V U n) :=
  (affineSectionCompletionCoefficient f I V U n).toRingHom.toAlgebra

/-- The completed coefficient action extends the original native action. -/
instance affineSectionRing_scalarTower (U : X.affineOpens) (n : ℕ) :
    IsScalarTower Γ(X, U) (AdicCompletion (sectionsIdeal f I U) Γ(X, U))
      (affineSectionRing f I V U n) :=
  IsScalarTower.of_algebraMap_eq
    (fun a => ((affineSectionCompletionCoefficient f I V U n).commutes a).symm)

/-- The actual transition preserves all completed coefficients. -/
theorem affineSectionTransition_completionCoefficient (U : X.affineOpens) (n : ℕ)
    (a : AdicCompletion (sectionsIdeal f I U) Γ(X, U)) :
    affineSectionAlgebraTransition f I V U n
        (affineSectionCompletionCoefficient f I V U (n + 1) a) =
      affineSectionCompletionCoefficient f I V U n a := by
  let q : (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1 + 1)) →+*
      (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1)) :=
    Ideal.Quotient.factorPow (sectionsIdeal f I U) (Nat.le_succ (n + 1))
  have hq (b : Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1 + 1)) :
      affineSectionAlgebraTransition f I V U n
          (affineSectionQuotientAlgebraMap f I V U (n + 1) b) =
        affineSectionQuotientAlgebraMap f I V U n (q b) := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
    change affineSectionAlgebraTransition f I V U n
        (algebraMap Γ(X, U) (affineSectionRing f I V U (n + 1)) r) =
      algebraMap Γ(X, U) (affineSectionRing f I V U n) r
    exact (affineSectionAlgebraTransition f I V U n).commutes r
  change affineSectionAlgebraTransition f I V U n
      (affineSectionQuotientAlgebraMap f I V U (n + 1)
        (AdicCompletion.evalₐ (sectionsIdeal f I U) (n + 1 + 1) a)) =
    affineSectionQuotientAlgebraMap f I V U n
      (AdicCompletion.evalₐ (sectionsIdeal f I U) (n + 1) a)
  rw [hq]
  exact congrArg (affineSectionQuotientAlgebraMap f I V U n)
    (factorPow_evalₐ (sectionsIdeal f I U) (Nat.le_succ (n + 1)) a)

/-- The original section transition as an algebra map over the completed ring. -/
def affineSectionCompletedTransition (U : X.affineOpens) (n : ℕ) :
    affineSectionRing f I V U (n + 1)
      →ₐ[AdicCompletion (sectionsIdeal f I U) Γ(X, U)] affineSectionRing f I V U n where
  __ := (affineSectionAlgebraTransition f I V U n).toRingHom
  commutes' := affineSectionTransition_completionCoefficient f I V U n

/-- The actual algebra of compatible original sections over the completed
original affine coefficient ring. Its ring operations are pointwise. -/
def completedAffineAlgebra (U : X.affineOpens) :
    Subalgebra (AdicCompletion (sectionsIdeal f I U) Γ(X, U))
      ((n : ℕ) → affineSectionRing f I V U n) :=
  AdicAlgebraSystem.sections (fun n => affineSectionRing f I V U n)
    (fun n => affineSectionCompletedTransition f I V U n)

/-- Evaluation in the original section ring, including its unit and multiplication. -/
def completedAffineAlgebraEval (U : X.affineOpens) (n : ℕ) :
    completedAffineAlgebra f I V U
      →ₐ[AdicCompletion (sectionsIdeal f I U) Γ(X, U)] affineSectionRing f I V U n :=
  AdicAlgebraSystem.eval (fun k => affineSectionRing f I V U k)
    (fun k => affineSectionCompletedTransition f I V U k) n

theorem completedAffineAlgebraEval_apply (U : X.affineOpens) (n : ℕ)
    (x : completedAffineAlgebra f I V U) :
    completedAffineAlgebraEval f I V U n x = x.val n := rfl

/-- The algebra evaluations preserve the actual cover transition. -/
theorem completedAffineAlgebraEval_transition (U : X.affineOpens) (n : ℕ)
    (x : completedAffineAlgebra f I V U) :
    affineSectionAlgebraTransition f I V U n
        (completedAffineAlgebraEval f I V U (n + 1) x) =
      completedAffineAlgebraEval f I V U n x :=
  x.property n

/-- The new algebra retains the literal original compatible-section module. -/
def affineSectionsAlgebraEquiv (U : X.affineOpens) :
    affineSections f I V U ≃ₗ[Γ(X, U)] completedAffineAlgebra f I V U where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The earlier completed native module recovers the same actual section sequences. -/
def completedAffineAlgebraModuleEquiv (U : X.affineOpens) :
    completedAffineSections f I V U ≃ₗ[Γ(X, U)] completedAffineAlgebra f I V U :=
  (affineSectionsCompletionEquiv f I V U).symm.trans (affineSectionsAlgebraEquiv f I V U)

/-- Algebra evaluation is the previously constructed original section evaluation. -/
theorem completedAffineAlgebraEval_moduleEquiv (U : X.affineOpens) (n : ℕ)
    (x : completedAffineSections f I V U) :
    completedAffineAlgebraEval f I V U n (completedAffineAlgebraModuleEquiv f I V U x) =
      completedAffineSectionsEval f I V U n x := rfl

/-- The prescribed completed ideal power extended to the actual affine algebra. -/
def completedAffineAlgebraIdeal (U : X.affineOpens) (n : ℕ) :
    Ideal (completedAffineAlgebra f I V U) :=
  (((sectionsIdeal f I U).map
    (algebraMap Γ(X, U) (AdicCompletion (sectionsIdeal f I U) Γ(X, U)))) ^ (n + 1)).map
      (algebraMap (AdicCompletion (sectionsIdeal f I U) Γ(X, U))
        (completedAffineAlgebra f I V U))

private theorem completedAffineAlgebra_properties [IsLocallyNoetherian X]
    (U : X.affineOpens) :
    Module.Finite (AdicCompletion (sectionsIdeal f I U) Γ(X, U))
        (completedAffineAlgebra f I V U) ∧
      (∀ n : ℕ, Function.Surjective (completedAffineAlgebraEval f I V U n)) ∧
      (∀ n : ℕ, RingHom.ker (completedAffineAlgebraEval f I V U n) =
        completedAffineAlgebraIdeal f I V U n) := by
  let R : CommRingCat.{u} := Γ(X, U)
  let J : Ideal R := sectionsIdeal f I U
  let Rh := AdicCompletion J R
  let Jh : Ideal Rh := J.map (algebraMap R Rh)
  let B : ℕ → Type u := fun n => affineSectionRing f I V U n
  let t : (n : ℕ) → B (n + 1) →ₐ[Rh] B n :=
    fun n => affineSectionCompletedTransition f I V U n
  have hR : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian U
  have hRh : IsNoetherianRing Rh := AdicCompletion.isNoetherianRing_of_isNoetherianRing J
  have hcomplete : IsAdicComplete J Rh :=
    AdicCompletion.isAdicComplete (I := J) (M := R) (IsNoetherian.noetherian J)
  have hcomplete' : IsAdicComplete Jh Rh :=
    (IsAdicComplete.map_algebraMap_iff (I := J) (S := Rh) (M := Rh)).mpr hcomplete
  have hfiniteR : ∀ n : ℕ, Module.Finite R (B n) :=
    fun n => (coverToOriginal f I V n).finite_app U U.property
  have hfinite : ∀ n : ℕ, Module.Finite Rh (B n) :=
    fun n => Module.Finite.of_restrictScalars_finite R Rh (B n)
  have ht : ∀ n : ℕ, Function.Surjective (t n) :=
    fun n => algebraTransition_app_surjective f I V n U U.property
  have hker : ∀ n : ℕ, RingHom.ker (t n).toRingHom =
      (Jh ^ (n + 1)).map (algebraMap Rh (B (n + 1))) := by
    intro n
    calc
      RingHom.ker (t n).toRingHom =
          (J ^ (n + 1)).map (algebraMap R (B (n + 1))) :=
        algebraTransition_app_ker f I V n U U.property
      _ = (Jh ^ (n + 1)).map (algebraMap Rh (B (n + 1))) := by
        change (J ^ (n + 1)).map (algebraMap R (B (n + 1))) =
          ((J.map (algebraMap R Rh)) ^ (n + 1)).map (algebraMap Rh (B (n + 1)))
        rw [← Ideal.map_pow, Ideal.map_map, ← IsScalarTower.algebraMap_eq R Rh (B (n + 1))]
  have hpow : ∀ n : ℕ, (Jh ^ (n + 1)).map (algebraMap Rh (B n)) = ⊥ := by
    intro n
    change ((J.map (algebraMap R Rh)) ^ (n + 1)).map (algebraMap Rh (B n)) = ⊥
    rw [← Ideal.map_pow, Ideal.map_map, ← IsScalarTower.algebraMap_eq R Rh (B n)]
    exact affineSectionRing_power_map_eq_bot f I V U n
  exact ⟨AdicAlgebraSystem.finite B t Jh ht hker hpow,
    fun n => AdicAlgebraSystem.eval_surjective B t Jh ht hker n,
    fun n => AdicAlgebraSystem.ker_eval B t Jh ht hker hpow n⟩

/-- The actual compatible-section algebra is finite over the completed affine ring. -/
theorem completedAffineAlgebra_finite [IsLocallyNoetherian X] (U : X.affineOpens) :
    Module.Finite (AdicCompletion (sectionsIdeal f I U) Γ(X, U))
      (completedAffineAlgebra f I V U) :=
  (completedAffineAlgebra_properties f I V U).1

/-- Each original section ring is reached by the actual algebra evaluation. -/
theorem completedAffineAlgebraEval_surjective [IsLocallyNoetherian X]
    (U : X.affineOpens) (n : ℕ) :
    Function.Surjective (completedAffineAlgebraEval f I V U n) :=
  (completedAffineAlgebra_properties f I V U).2.1 n

/-- The evaluation kernel is exactly the extended completed ideal power. -/
theorem completedAffineAlgebraEval_ker [IsLocallyNoetherian X]
    (U : X.affineOpens) (n : ℕ) :
    RingHom.ker (completedAffineAlgebraEval f I V U n) =
      completedAffineAlgebraIdeal f I V U n :=
  (completedAffineAlgebra_properties f I V U).2.2 n

/-- Algebra reduction of the constructed affine algebra recovers the actual
original section ring over the completed coefficient ring. -/
def completedAffineAlgebraReductionEquiv [IsLocallyNoetherian X]
    (U : X.affineOpens) (n : ℕ) :
    ((completedAffineAlgebra f I V U) ⧸ completedAffineAlgebraIdeal f I V U n)
      ≃ₐ[AdicCompletion (sectionsIdeal f I U) Γ(X, U)] affineSectionRing f I V U n :=
  (Ideal.quotientEquivAlgOfEq (AdicCompletion (sectionsIdeal f I U) Γ(X, U))
    (completedAffineAlgebraEval_ker f I V U n).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (completedAffineAlgebraEval_surjective f I V U n))

/-- The algebra reduction is induced by literal original section evaluation. -/
theorem completedAffineAlgebraReductionEquiv_mk [IsLocallyNoetherian X]
    (U : X.affineOpens) (n : ℕ) (x : completedAffineAlgebra f I V U) :
    completedAffineAlgebraReductionEquiv f I V U n
        (Ideal.Quotient.mk (completedAffineAlgebraIdeal f I V U n) x) =
      completedAffineAlgebraEval f I V U n x := by
  rw [completedAffineAlgebraReductionEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk]

/-- Algebra reduction also retains the earlier native-module evaluation. -/
theorem completedAffineAlgebraReductionEquiv_moduleEquiv [IsLocallyNoetherian X]
    (U : X.affineOpens) (n : ℕ) (x : completedAffineSections f I V U) :
    completedAffineAlgebraReductionEquiv f I V U n
        (Ideal.Quotient.mk (completedAffineAlgebraIdeal f I V U n)
          (completedAffineAlgebraModuleEquiv f I V U x)) =
      completedAffineSectionsEval f I V U n x := by
  rw [completedAffineAlgebraReductionEquiv_mk]
  exact completedAffineAlgebraEval_moduleEquiv f I V U n x

/-- Consecutive algebra reductions retain the actual cover transition. -/
theorem completedAffineAlgebraReductionEquiv_transition [IsLocallyNoetherian X]
    (U : X.affineOpens) (n : ℕ) (x : completedAffineAlgebra f I V U) :
    affineSectionAlgebraTransition f I V U n
        (completedAffineAlgebraReductionEquiv f I V U (n + 1)
          (Ideal.Quotient.mk (completedAffineAlgebraIdeal f I V U (n + 1)) x)) =
      completedAffineAlgebraReductionEquiv f I V U n
        (Ideal.Quotient.mk (completedAffineAlgebraIdeal f I V U n) x) := by
  rw [completedAffineAlgebraReductionEquiv_mk, completedAffineAlgebraReductionEquiv_mk]
  exact completedAffineAlgebraEval_transition f I V U n x

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
