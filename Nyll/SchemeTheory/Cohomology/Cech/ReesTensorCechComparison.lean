/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Cohomology.Sheaves.ModulePresheafDEqDDMemPow
import Nyll.SchemeTheory.Cohomology.Sheaves.ReesTensorAffineSections
import Nyll.SchemeTheory.Cohomology.Sheaves.ReesTensorModule
import Nyll.SchemeTheory.Cohomology.Sheaves.ReesTensorPresheaf
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# The actual Rees sheaf and the original Rees tensor Čech complex

The constructed affine section comparisons and the original cover index
equivalence give additive equivalences of the actual Čech cochains. The
actual face restrictions identify their alternating differentials.

These equivalences keep the original base action of each complex. The
comparison of additive groups is sufficient to construct each original
coboundary from a native sheaf coboundary, using the inverse cochain map.
In particular, vanishing for the native Rees sheaf implies vanishing for
the actual Rees tensor complex on the original scheme.
-/

noncomputable section

universe u

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.ReesCechApproximation.SolKS

open AlgebraicGeometry Scheme.Modules

variable {A : Type u} [CommRing A] (I : Ideal A)
  {P : Scheme.{u}} (q : P ⟶ Spec (.of A)) [IsSeparated q]
  (K : P.OrderedAffineCover) (M : P.Modules) [M.IsQuasicoherent]

local notation "F" => ReesTensor.reesTensorPresheaf q I M
local notation "G" => toOModulePresheaf (π' I q) (imageTensorModule I q M)

/-- The actual affine section equivalences, reindexed by the original
increasing tuples of the base changed cover. -/
def imageTensorCochainAddEquiv (n : ℕ) :
    (F).cochain K n ≃+ (G).cochain (K' I q K) n :=
  { (indexEquiv I q K).piCongr
      (fun s => (imageTensorAffineSectionsEquiv I q K M s).toEquiv) with
    map_add' := by
      intro c c'
      funext t
      obtain ⟨s, rfl⟩ := (indexEquiv I q K).surjective t
      simp only [Pi.add_apply]
      exact (imageTensorAffineSectionsEquiv I q K M s).map_add (c s) (c' s) }

/-- The cochain equivalence retains the actual affine section map at
the corresponding original intersection. -/
theorem imageTensorCochainAddEquiv_apply (n : ℕ) (c : (F).cochain K n) (s : K.Idx n) :
    imageTensorCochainAddEquiv I q K M n c (indexEquiv I q K s) =
      imageTensorAffineSectionsEquiv I q K M s (c s) :=
  Equiv.piCongr_apply_apply (indexEquiv I q K)
    (W := fun t : K.Idx n => (F).obj (K.inter t))
    (Z := fun t : (K' I q K).Idx n => (G).obj ((K' I q K).inter t))
    (fun t => (imageTensorAffineSectionsEquiv I q K M t).toEquiv) c s

/-- The inverse cochain equivalence uses the actual inverse affine
section comparison at the same original intersection. -/
theorem imageTensorCochainAddEquiv_symm_apply (n : ℕ)
    (c : (G).cochain (K' I q K) n) (s : K.Idx n) :
    (imageTensorCochainAddEquiv I q K M n).symm c s =
      (imageTensorAffineSectionsEquiv I q K M s).symm (c (indexEquiv I q K s)) := rfl

/-- The actual cochain equivalence commutes with the original
alternating differential, including its original face restrictions. -/
theorem imageTensorCochainAddEquiv_d (n : ℕ) (c : (F).cochain K n) :
    imageTensorCochainAddEquiv I q K M (n + 1) ((F).d K n c) =
      (G).d (K' I q K) n (imageTensorCochainAddEquiv I q K M n c) := by
  funext t
  obtain ⟨s, rfl⟩ := (indexEquiv I q K).surjective t
  refine (imageTensorCochainAddEquiv_apply I q K M (n + 1) ((F).d K n c) s).trans ?_
  let e : (F).obj (K.inter s) ≃+
      (G).obj ((K' I q K).inter (indexEquiv I q K s)) :=
    imageTensorAffineSectionsEquiv I q K M s
  change e ((F).d K n c s) =
    (G).d (K' I q K) n (imageTensorCochainAddEquiv I q K M n c) (indexEquiv I q K s)
  rw [OModulePresheaf.d_apply, OModulePresheaf.d_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [map_zsmul]
  have h₁ := imageTensorAffineSectionsEquiv_face I q K M s j (c (K.face s j))
  have h₂ := congrArg
    ((G).res (K'_inter_le_inter_face I q K s j))
    (imageTensorCochainAddEquiv_apply I q K M n c (K.face s j)).symm
  exact congrArg
    (fun z : (G).obj ((K' I q K).inter (indexEquiv I q K s)) =>
      ((-1 : ℤ) ^ (j : ℕ)) • z) (h₁.trans h₂)

/-- A native coboundary has an original Rees tensor preimage given by
the inverse actual cochain equivalence, and conversely. -/
theorem imageTensorCochainAddEquiv_mem_range_iff (n : ℕ) (c : (F).cochain K (n + 1)) :
    imageTensorCochainAddEquiv I q K M (n + 1) c ∈
        LinearMap.range ((G).d (K' I q K) n) ↔
      c ∈ LinearMap.range ((F).d K n) := by
  let E (r : ℕ) := imageTensorCochainAddEquiv I q K M r
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨(E n).symm b, ?_⟩
    apply (E (n + 1)).injective
    exact (imageTensorCochainAddEquiv_d I q K M n ((E n).symm b)).trans
      ((congrArg ((G).d (K' I q K) n) ((E n).apply_symm_apply b)).trans hb)
  · rintro ⟨b, hb⟩
    refine ⟨E n b, ?_⟩
    exact (imageTensorCochainAddEquiv_d I q K M n b).symm.trans
      (congrArg (E (n + 1)) hb)

/-- Vanishing for the actual native Rees coefficient sheaf implies
vanishing of the actual Rees tensor complex on the original cover. -/
theorem imageTensor_subsingleton_reesTensorHSucc (n : ℕ)
    [Subsingleton ((G).HSucc (K' I q K) n)] :
    Subsingleton ((F).HSucc K n) := by
  rw [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff']
  intro z
  let E (r : ℕ) := imageTensorCochainAddEquiv I q K M r
  have hcycle : (G).d (K' I q K) (n + 1) (E (n + 1) z.val) = 0 :=
    (imageTensorCochainAddEquiv_d I q K M (n + 1) z.val).symm.trans
      ((congrArg (E (n + 2)) z.property).trans (map_zero (E (n + 2))))
  let w : LinearMap.ker ((G).d (K' I q K) (n + 1)) := ⟨E (n + 1) z.val, hcycle⟩
  have hw : (Submodule.Quotient.mk w : (G).HSucc (K' I q K) n) = 0 :=
    Subsingleton.elim _ _
  have hb : E (n + 1) z.val ∈ LinearMap.range ((G).d (K' I q K) n) :=
    (Submodule.Quotient.mk_eq_zero
      ((LinearMap.range ((G).d (K' I q K) n)).comap
        (LinearMap.ker ((G).d (K' I q K) (n + 1))).subtype)).mp hw
  exact (imageTensorCochainAddEquiv_mem_range_iff I q K M n z.val).mp hb

end AlgebraicCurves.Cohomology.Sheaves.Proofs.ReesCechApproximation.SolKS
