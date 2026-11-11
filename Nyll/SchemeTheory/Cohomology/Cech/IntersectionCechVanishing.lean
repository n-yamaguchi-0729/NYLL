/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Čech vanishing from comparisons on actual intersections

Additive equivalences on the original cover intersections, commuting
with the original face restrictions, transfer vanishing of the actual
quotient Čech cohomology. Comparisons on unrelated affine opens are not
needed. The inverse cochain map constructs a preimage of each cocycle.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  {f : X ⟶ Spec (.of R)} (C : X.OrderedAffineCover) (F G : OModulePresheaf f)

/-- Actual compatible comparisons on the intersections transfer
vanishing by lifting each cocycle through the inverse cochain map. -/
theorem subsingleton_HSucc_of_intersectionEquiv
    (e : ∀ (r : ℕ) (s : C.Idx r), F.obj (C.inter s) ≃+ G.obj (C.inter s))
    (he : ∀ (r : ℕ) (s : C.Idx (r + 1)) (i : Fin (r + 2))
      (z : F.obj (C.inter (C.face s i))),
      e (r + 1) s (F.res (C.inter_le_inter_face s i) z) =
        G.res (C.inter_le_inter_face s i) (e r (C.face s i) z))
    (k : ℕ) [Subsingleton (F.HSucc C k)] : Subsingleton (G.HSucc C k) := by
  let E (r : ℕ) : F.cochain C r ≃+ G.cochain C r :=
    { toFun := fun z s => e r s (z s)
      invFun := fun z s => (e r s).symm (z s)
      left_inv := fun z => funext fun s => (e r s).symm_apply_apply (z s)
      right_inv := fun z => funext fun s => (e r s).apply_symm_apply (z s)
      map_add' := fun z w => funext fun s => (e r s).map_add (z s) (w s) }
  have hE (r : ℕ) (z : F.cochain C r) :
      E (r + 1) (F.d C r z) = G.d C r (E r z) := by
    funext s
    change e (r + 1) s (F.d C r z s) = G.d C r (E r z) s
    rw [d_apply, d_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [map_zsmul]
    exact congrArg (fun a : G.obj (C.inter s) => ((-1 : ℤ) ^ (i : ℕ)) • a)
      (he r s i (z (C.face s i)))
  rw [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff']
  intro z
  let v : F.cochain C (k + 1) := (E (k + 1)).symm z.val
  have hv : F.d C (k + 1) v = 0 := by
    apply (E (k + 2)).injective
    exact (hE (k + 1) v).trans
      ((congrArg (G.d C (k + 1)) ((E (k + 1)).apply_symm_apply z.val)).trans
        (z.property.trans (E (k + 2)).map_zero.symm))
  let w : LinearMap.ker (F.d C (k + 1)) := ⟨v, hv⟩
  have hw : (Submodule.Quotient.mk w : F.HSucc C k) = 0 := Subsingleton.elim _ _
  have hb : v ∈ LinearMap.range (F.d C k) :=
    (Submodule.Quotient.mk_eq_zero
      ((LinearMap.range (F.d C k)).comap (LinearMap.ker (F.d C (k + 1))).subtype)).mp hw
  obtain ⟨b, hb⟩ := hb
  change z.val ∈ LinearMap.range (G.d C k)
  refine ⟨E k b, ?_⟩
  exact (hE k b).symm.trans
    ((congrArg (E (k + 1)) hb).trans ((E (k + 1)).apply_symm_apply z.val))

end AlgebraicGeometry.OModulePresheaf
