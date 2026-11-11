/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Pi

/-!
# Trace one for a finite faithfully flat torsor

The canonical torsor tensor map sends `x ⊗ y` to `(g ↦ x * g(y))`.
Its surjectivity gives a tensor above the delta function at the identity.
Summing its coordinates shows that the group traces generate the unit
ideal after faithfully flat extension, hence already over the base ring.
No division by the order of the group is used.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace GaloisCohomology.FiniteTorsor

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  {G : Type*} [Group G] (ρ : G →* (S ≃ₐ[R] S))

/-- The canonical coordinate map of the affine torsor diagram. -/
def tensorMap : S ⊗[R] S →ₐ[R] (G → S) :=
  AlgHom.pi fun g => Algebra.TensorProduct.lift (AlgHom.id R S) (ρ g).toAlgHom
    (fun _ _ => Commute.all _ _)

theorem tensorMap_tmul (x y : S) (g : G) :
    tensorMap R S ρ (x ⊗ₜ[R] y) g = x * ρ g y := rfl

variable [Fintype G] [Module.FaithfullyFlat R S]

omit [Module.FaithfullyFlat R S] in
private theorem sum_action_fixed (x : S) (g : G) :
    ρ g (∑ h, ρ h x) = ∑ h, ρ h x := by
  rw [map_sum]
  have hcomp (h : G) : ρ g (ρ h x) = ρ (g * h) x := by
    rw [map_mul]
    rfl
  simp only [hcomp]
  exact Fintype.sum_bijective (fun h : G => g * h)
    (Group.mulLeft_bijective g) _ _ (fun _ => rfl)

/-- A finite faithfully flat torsor has a section of group trace one,
including when the characteristic divides the group order. The fixed-ring
condition here is supplied by descent along the same affine torsor. -/
theorem exists_trace_one
    (hInv : ∀ x : S, (∀ g : G, ρ g x = x) → ∃ r : R, algebraMap R S r = x)
    (hTensor : Function.Surjective (tensorMap R S ρ)) :
    ∃ t : S, ∑ g, ρ g t = 1 := by
  classical
  have hinj := FaithfulSMul.algebraMap_injective R S
  have hdesc (x : S) : ∃ r : R, algebraMap R S r = ∑ g, ρ g x :=
    hInv _ (sum_action_fixed R S ρ x)
  let T : S →ₗ[R] R :=
    { toFun := fun x => (hdesc x).choose
      map_add' := by
        intro x y
        apply hinj
        rw [map_add, (hdesc (x + y)).choose_spec,
          (hdesc x).choose_spec, (hdesc y).choose_spec]
        simp only [map_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r x
        apply hinj
        rw [(hdesc (r • x)).choose_spec]
        change (∑ g, ρ g (r • x)) = algebraMap R S (r * (hdesc x).choose)
        rw [map_mul, (hdesc x).choose_spec, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g _
        rw [Algebra.smul_def, map_mul, (ρ g).commutes] }
  have hT (x : S) : algebraMap R S (T x) = ∑ g, ρ g x := (hdesc x).choose_spec
  let I : Ideal R := T.range
  have hmem (q : S ⊗[R] S) : (∑ g, tensorMap R S ρ q g) ∈ I.map (algebraMap R S) := by
    induction q using TensorProduct.inductionOn with
    | tmul x y =>
      simp only [tensorMap_tmul, ← Finset.mul_sum, ← hT]
      exact Ideal.mul_mem_left _ x (Ideal.mem_map_of_mem _ ⟨y, rfl⟩)
    | add q q' hq hq' =>
      have hsum : (∑ g, tensorMap R S ρ (q + q') g) =
          (∑ g, tensorMap R S ρ q g) + (∑ g, tensorMap R S ρ q' g) := by
        simp only [map_add, Pi.add_apply, Finset.sum_add_distrib]
      rw [hsum]
      exact Ideal.add_mem _ hq hq'
  obtain ⟨q, hq⟩ := hTensor (fun g => if g = 1 then 1 else 0)
  have hone : (1 : S) ∈ I.map (algebraMap R S) := by
    have h := hmem q
    rw [hq] at h
    simpa only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h
  have honeR : (1 : R) ∈ I := by
    rw [← I.comap_map_eq_self_of_faithfullyFlat (B := S)]
    change algebraMap R S 1 ∈ I.map (algebraMap R S)
    rwa [map_one]
  obtain ⟨t, ht⟩ := honeR
  exact ⟨t, (hT t).symm.trans ((congrArg (algebraMap R S) ht).trans (map_one _))⟩

end GaloisCohomology.FiniteTorsor
