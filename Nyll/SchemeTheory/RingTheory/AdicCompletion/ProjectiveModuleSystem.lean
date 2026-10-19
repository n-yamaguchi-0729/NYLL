/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.AdicProjectiveSplittings
import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModules
import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
import Nyll.SchemeTheory.RingTheory.AdicCompletion.ProjectiveQuotientLifting
import Nyll.SchemeTheory.RingTheory.AdicCompletion.ProjectiveSplittingLift
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# Effectivity of finite projective adic module systems

A surjection onto a module whose reductions are projective has splittings
at all finite levels. Successive lifting constructs these splittings with
compatibility along the native quotient maps. Completeness of the source
then produces an actual splitting of the original surjection.

Applied to a finite free presentation, this proves projectivity of a
finite module from projectivity of all its adic reductions. The final
theorem applies the criterion to the actual compatible-sequence module
constructed in `FiniteModuleSystem`: a finite projective adic system is
effective as a finite projective module, and the already constructed
quotient equivalences recover its supplied stages.
-/

noncomputable section

namespace AdicModuleSystem

universe u v w

variable {R : Type u} [CommRing R]

/-- Projectivity of all reductions constructs compatible splittings of
the reductions of the original surjection. -/
theorem exists_compatible_power_splittings (I : Ideal R)
    {F : Type v} [AddCommGroup F] [Module R F]
    {P : Type w} [AddCommGroup P] [Module R P]
    (f : F →ₗ[R] P) (hf : Function.Surjective f)
    (hproj : ∀ n : ℕ, Module.Projective (R ⧸ I ^ (n + 1))
      (P ⧸ (I ^ (n + 1) • (⊤ : Submodule R P)))) :
    ∃ s : (n : ℕ) →
      P ⧸ (I ^ (n + 1) • (⊤ : Submodule R P)) →ₗ[R]
        F ⧸ (I ^ (n + 1) • (⊤ : Submodule R F)),
      (∀ n : ℕ, (reduceMap (I ^ (n + 1)) f).comp (s n) = LinearMap.id) ∧
      (∀ n : ℕ, (Submodule.factorPow I F (Nat.le_succ (n + 1))).comp (s (n + 1)) =
        (s n).comp (Submodule.factorPow I P (Nat.le_succ (n + 1)))) := by
  let C (n : ℕ) : Type (max v w) :=
    { s : P ⧸ (I ^ (n + 1) • (⊤ : Submodule R P)) →ₗ[R]
        F ⧸ (I ^ (n + 1) • (⊤ : Submodule R F)) //
      (reduceMap (I ^ (n + 1)) f).comp s = LinearMap.id }
  have hzero : Nonempty (C 0) := by
    have hprojective : Module.Projective (R ⧸ I ^ (0 + 1))
        (P ⧸ (I ^ (0 + 1) • (⊤ : Submodule R P))) := hproj 0
    obtain ⟨s, hs⟩ := exists_lift_of_projective_quotient (I ^ (0 + 1))
      (Module.isTorsionBySet_quotient_ideal_smul F (I ^ (0 + 1)))
      (reduceMap (I ^ (0 + 1)) f) LinearMap.id
      (reduceMap_surjective (I ^ (0 + 1)) f hf)
    exact ⟨⟨s, hs⟩⟩
  have hnext : ∀ (n : ℕ) (s : C n), ∃ s' : C (n + 1),
      (Submodule.factorPow I F (Nat.le_succ (n + 1))).comp s'.val =
        s.val.comp (Submodule.factorPow I P (Nat.le_succ (n + 1))) := by
    intro n s
    have hprojective : Module.Projective (R ⧸ I ^ (n + 1 + 1))
        (P ⧸ (I ^ (n + 1 + 1) • (⊤ : Submodule R P))) := hproj (n + 1)
    obtain ⟨s', hs', hcompat⟩ := exists_compatible_quotient_splitting
      (I ^ (n + 1 + 1)) (I ^ (n + 1))
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) f hf s.val s.property
    exact ⟨⟨s', hs'⟩, hcompat⟩
  let next : (n : ℕ) → C n → C (n + 1) :=
    fun n s => Classical.choose (hnext n s)
  let s : (n : ℕ) → C n :=
    Nat.rec (Classical.choice hzero) (fun n s => next n s)
  refine ⟨fun n => (s n).val, fun n => (s n).property, ?_⟩
  intro n
  exact Classical.choose_spec (hnext n (s n))

/-- Compatible finite-level splittings converge to an actual splitting
when the source is complete and the target is separated. -/
theorem exists_splitting_of_projective_reductions (I : Ideal R)
    {F : Type v} [AddCommGroup F] [Module R F] [IsAdicComplete I F]
    {P : Type w} [AddCommGroup P] [Module R P] [IsHausdorff I P]
    (f : F →ₗ[R] P) (hf : Function.Surjective f)
    (hproj : ∀ n : ℕ, Module.Projective (R ⧸ I ^ (n + 1))
      (P ⧸ (I ^ (n + 1) • (⊤ : Submodule R P)))) :
    ∃ s : P →ₗ[R] F, f.comp s = LinearMap.id := by
  obtain ⟨s, hs, hcompat⟩ := exists_compatible_power_splittings I f hf hproj
  have ha : StrictMono (fun n : ℕ => n + 1) :=
    fun _ _ h => Nat.add_lt_add_right h 1
  let φ : (n : ℕ) → P →ₗ[R] F ⧸ (I ^ (n + 1) • (⊤ : Submodule R F)) :=
    fun n => (s n).comp (I ^ (n + 1) • (⊤ : Submodule R P)).mkQ
  have hφ : ∀ {n : ℕ},
      (Submodule.factorPow I F (ha.monotone n.le_succ)).comp (φ (n + 1)) = φ n := by
    intro n
    apply LinearMap.ext
    intro p
    calc
      Submodule.factorPow I F (ha.monotone n.le_succ)
          (s (n + 1) (Submodule.Quotient.mk p)) =
          s n (Submodule.factorPow I P (Nat.le_succ (n + 1))
            (Submodule.Quotient.mk p)) :=
        LinearMap.congr_fun (hcompat n) (Submodule.Quotient.mk p)
      _ = s n (Submodule.Quotient.mk p) :=
        congrArg (s n) (Submodule.factor_mk _ p)
  let l : P →ₗ[R] F := IsAdicComplete.StrictMono.lift I ha φ hφ
  have hl : ∀ (n : ℕ) (p : P),
      (Submodule.Quotient.mk (p := I ^ (n + 1) • (⊤ : Submodule R F)) (l p)) =
        s n (Submodule.Quotient.mk p) :=
    fun n p => IsAdicComplete.StrictMono.mk_lift I ha φ hφ (n := n) p
  refine ⟨l, ?_⟩
  apply DFunLike.coe_injective
  apply IsHausdorff.StrictMono.funext I ha
  intro n p
  calc
    Submodule.Quotient.mk (f (l p)) =
        reduceMap (I ^ (n + 1)) f (Submodule.Quotient.mk (l p)) :=
      (reduceMap_mk (I ^ (n + 1)) f (l p)).symm
    _ = reduceMap (I ^ (n + 1)) f (s n (Submodule.Quotient.mk p)) :=
      congrArg (reduceMap (I ^ (n + 1)) f) (hl n p)
    _ = Submodule.Quotient.mk p := LinearMap.congr_fun (hs n) (Submodule.Quotient.mk p)

/-- A finite module over a complete Noetherian ring is projective if all
of its actual adic reductions are projective over the quotient rings. -/
theorem projective_of_projective_reductions [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R]
    (P : Type v) [AddCommGroup P] [Module R P] [Module.Finite R P]
    (hproj : ∀ n : ℕ, Module.Projective (R ⧸ I ^ (n + 1))
      (P ⧸ (I ^ (n + 1) • (⊤ : Submodule R P)))) : Module.Projective R P := by
  obtain ⟨r, f, hf⟩ := Module.Finite.exists_fin' R P
  have hcompleteF : IsAdicComplete I (Fin r → R) :=
    IsAdicComplete.of_module_finite I (Fin r → R)
  have hcompleteP : IsAdicComplete I P := IsAdicComplete.of_module_finite I P
  obtain ⟨s, hs⟩ := exists_splitting_of_projective_reductions I f hf hproj
  exact Module.Projective.of_split s f hs

/-- The actual compatible-sequence module of a finite projective adic
system is projective. Each stage carries its supplied quotient-ring
action, and the comparison with the reduction of the limit is constructed
from the projection rather than assumed. -/
theorem projective [IsNoetherianRing R]
    (M : ℕ → Type v) [∀ n : ℕ, AddCommGroup (M n)] [∀ n : ℕ, Module R (M n)]
    (t : (n : ℕ) → M (n + 1) →ₗ[R] M n)
    (I : Ideal R) [IsAdicComplete I R]
    [∀ n : ℕ, Module.Finite R (M n)]
    [∀ n : ℕ, Module (R ⧸ I ^ (n + 1)) (M n)]
    [∀ n : ℕ, IsScalarTower R (R ⧸ I ^ (n + 1)) (M n)]
    [∀ n : ℕ, Module.Projective (R ⧸ I ^ (n + 1)) (M n)]
    (ht : ∀ n : ℕ, Function.Surjective (t n))
    (hker : ∀ n : ℕ, (t n).ker = I ^ (n + 1) • (⊤ : Submodule R (M (n + 1))))
    (hpow : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (M n)) = ⊥) :
    Module.Projective R (sections M t) := by
  have hfinite : Module.Finite R (sections M t) := finite M t I ht hker hpow
  apply projective_of_projective_reductions I (sections M t)
  intro n
  let e : ((sections M t) ⧸
      (I ^ (n + 1) • (⊤ : Submodule R (sections M t)))) ≃ₗ[R] M n :=
    quotientEquiv M t I ht hker hpow n
  let eQ : ((sections M t) ⧸
      (I ^ (n + 1) • (⊤ : Submodule R (sections M t)))) ≃ₗ[R ⧸ I ^ (n + 1)] M n :=
    LinearEquiv.ofBijective (overQuotientLinearMap (I ^ (n + 1)) e.toLinearMap) e.bijective
  exact Module.Projective.of_equiv' eQ.symm

end AdicModuleSystem
