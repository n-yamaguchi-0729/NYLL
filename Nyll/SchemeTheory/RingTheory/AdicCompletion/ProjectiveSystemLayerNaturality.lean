/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.ProjectiveSystemLayersOverCompletion
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Naturality of the original projective adic layers

Compatible semilinear stage maps act on the actual compatible sequences
and on the original transition kernels. The constructed ideal-tensor
comparison intertwines these maps with the tensor of the original
coefficient map and the first-stage map. The proof uses the actual
scalar/evaluation formula and the proved lifting of first-stage values.

In particular, a restriction map between affine section systems can use
its original coefficient-ideal restriction; no comparison naturality is
supplied as an additional hypothesis.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace AdicModuleSystem

universe u v w z

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]
  (M : ℕ → Type w) [∀ n : ℕ, AddCommGroup (M n)] [∀ n : ℕ, Module R (M n)]
  (tM : ∀ n : ℕ, M (n + 1) →ₗ[R] M n)
  (N : ℕ → Type z) [∀ n : ℕ, AddCommGroup (N n)] [∀ n : ℕ, Module S (N n)]
  (tN : ∀ n : ℕ, N (n + 1) →ₗ[S] N n)
  (ρ : R →+* S) (f : ∀ n : ℕ, M n →ₛₗ[ρ] N n)
  (hf : ∀ (n : ℕ) (x : M (n + 1)), tN n (f (n + 1) x) = f n (tM n x))

/-- The given compatible semilinear maps act componentwise on the
original compatible sections. -/
def semilinearSectionsMap : sections M tM →ₛₗ[ρ] sections N tN where
  toFun x := ⟨fun n => f n (x.val n), fun n =>
    (hf n (x.val (n + 1))).trans (congrArg (f n) (x.property n))⟩
  map_add' x y := Subtype.ext (funext fun n => (f n).map_add (x.val n) (y.val n))
  map_smul' a x := Subtype.ext (funext fun n => (f n).map_smulₛₗ a (x.val n))

/-- Projection retains the original semilinear map at that stage. -/
theorem eval_semilinearSectionsMap (n : ℕ) (x : sections M tM) :
    eval N tN n (semilinearSectionsMap M tM N tN ρ f hf x) = f n (eval M tM n x) := rfl

/-- Compatibility restricts the given next-stage map to the actual
transition kernels, with no new map chosen. -/
def semilinearTransitionKernelMap (n : ℕ) : (tM n).ker →ₛₗ[ρ] (tN n).ker where
  toFun x := ⟨f (n + 1) x.val,
    (hf n x.val).trans ((congrArg (f n) x.property).trans (f n).map_zero)⟩
  map_add' x y := Subtype.ext ((f (n + 1)).map_add x.val y.val)
  map_smul' a x := Subtype.ext ((f (n + 1)).map_smulₛₗ a x.val)

/-- The actual kernel map is the original next-stage map on underlying elements. -/
theorem semilinearTransitionKernelMap_apply (n : ℕ) (x : (tM n).ker) :
    (semilinearTransitionKernelMap M tM N tN ρ f hf n x).val = f (n + 1) x.val := rfl

variable [IsNoetherianRing R] [IsNoetherianRing S]
  (I : Ideal R) (J : Ideal S)
  [∀ n : ℕ, Module.Finite R (M n)] [∀ n : ℕ, Module.Finite S (N n)]
  (hpowM : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (M n)) = ⊥)
  (htM : ∀ n : ℕ, Function.Surjective (tM n))
  (hkerM : ∀ n : ℕ, (tM n).ker = I ^ (n + 1) • (⊤ : Submodule R (M (n + 1))))
  (hpowN : ∀ n : ℕ, J ^ (n + 1) • (⊤ : Submodule S (N n)) = ⊥)
  (htN : ∀ n : ℕ, Function.Surjective (tN n))
  (hkerN : ∀ n : ℕ, (tN n).ker = J ^ (n + 1) • (⊤ : Submodule S (N (n + 1))))
  [∀ n : ℕ, Module (R ⧸ I ^ (n + 1)) (M n)]
  [∀ n : ℕ, IsScalarTower R (R ⧸ I ^ (n + 1)) (M n)]
  [∀ n : ℕ, Module.Projective (R ⧸ I ^ (n + 1)) (M n)]
  [∀ n : ℕ, Module (S ⧸ J ^ (n + 1)) (N n)]
  [∀ n : ℕ, IsScalarTower S (S ⧸ J ^ (n + 1)) (N n)]
  [∀ n : ℕ, Module.Projective (S ⧸ J ^ (n + 1)) (N n)]

/-- The constructed ideal-tensor/kernel equivalence commutes with the
original compatible semilinear stage maps and original ideal-power map. -/
theorem projectiveOriginalTransitionKernelEquiv_naturality
    (n : ℕ) (rI : ↥(I ^ (n + 1)) →ₛₗ[ρ] ↥(J ^ (n + 1)))
    (hrI : ∀ a : ↥(I ^ (n + 1)), (rI a).val = ρ a.val)
    (z : ↥(I ^ (n + 1)) ⊗[R] M 0) :
    semilinearTransitionKernelMap M tM N tN ρ f hf n
        (projectiveOriginalTransitionKernelEquiv M tM I hpowM htM hkerM n z) =
      projectiveOriginalTransitionKernelEquiv N tN J hpowN htN hkerN n
        (TensorProduct.map rI (f 0) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a y =>
      obtain ⟨x, rfl⟩ := eval_zero_surjective M tM htM y
      let x' : sections N tN := semilinearSectionsMap M tM N tN ρ f hf x
      have hzero : f 0 (eval M tM 0 x) = eval N tN 0 x' := rfl
      apply Subtype.ext
      rw [semilinearTransitionKernelMap_apply,
        projectiveOriginalTransitionKernelEquiv_tmul_eval, TensorProduct.map_tmul,
        hzero, projectiveOriginalTransitionKernelEquiv_tmul_eval]
      exact ((f (n + 1)).map_smulₛₗ a.val (eval M tM (n + 1) x)).trans
        (congrArg (fun c : S => c • f (n + 1) (eval M tM (n + 1) x)) (hrI a).symm)
  | add x y hx hy =>
      simp only [map_add, hx, hy]

end AdicModuleSystem
