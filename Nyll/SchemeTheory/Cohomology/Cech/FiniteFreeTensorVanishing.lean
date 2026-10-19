/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Modules.Tensor.FiniteFreeSections
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Čech vanishing after tensoring with an actual finite free sheaf

The section comparison for the actual tensor product identifies its
original Čech cochains with tuples of the original cochains. Naturality
of its original projections identifies the differentials componentwise.

Every cocycle is therefore an actual boundary as soon as this holds for
the original module sheaf. No quasicoherence or finite-presentation data
are needed for this finite free step of Serre vanishing.
-/

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) (L : X.Modules) (J : Type u) [Finite J]
  (K : X.OrderedAffineCover)

local notation "F" => toOModulePresheaf f
  (tensor (X := X) (SheafOfModules.free J : X.Modules) L)
local notation "G" => toOModulePresheaf f L

/-- The cochains of the actual finite free tensor product are the
tuples of original cochains, using the actual section comparison. -/
def finiteFreeTensorCochainEquiv (q : ℕ) :
    (F).cochain K q ≃ₗ[R] (J → (G).cochain K q) where
  toFun c j s := finiteFreeTensorSectionsEquiv J (K.inter s) f L (c s) j
  invFun c s := (finiteFreeTensorSectionsEquiv J (K.inter s) f L).symm (fun j => c j s)
  left_inv c := by
    funext s
    exact (finiteFreeTensorSectionsEquiv J (K.inter s) f L).symm_apply_apply (c s)
  right_inv c := by
    funext j s
    exact congrFun ((finiteFreeTensorSectionsEquiv J (K.inter s) f L).apply_symm_apply
      (fun j => c j s)) j
  map_add' c c' := by
    funext j s
    exact congrFun ((finiteFreeTensorSectionsEquiv J (K.inter s) f L).map_add (c s) (c' s)) j
  map_smul' a c := by
    funext j s
    exact congrFun ((finiteFreeTensorSectionsEquiv J (K.inter s) f L).map_smul a (c s)) j

/-- Each coordinate retains the original intersection and section. -/
theorem finiteFreeTensorCochainEquiv_apply (q : ℕ) (c : (F).cochain K q)
    (j : J) (s : K.Idx q) :
    finiteFreeTensorCochainEquiv f L J K q c j s =
      finiteFreeTensorSectionsEquiv J (K.inter s) f L (c s) j := rfl

/-- The original alternating Čech differential is the original
differential on each coordinate of the constructed comparison. -/
theorem finiteFreeTensorCochainEquiv_d (q : ℕ) (c : (F).cochain K q) :
    finiteFreeTensorCochainEquiv f L J K (q + 1) ((F).d K q c) =
      fun j => (G).d K q (finiteFreeTensorCochainEquiv f L J K q c j) := by
  funext j s
  let π : (F).obj (K.inter s) →ₗ[R] (G).obj (K.inter s) :=
    (LinearMap.proj j).comp (finiteFreeTensorSectionsEquiv J (K.inter s) f L).toLinearMap
  change π ((F).d K q c s) =
    (G).d K q (finiteFreeTensorCochainEquiv f L J K q c j) s
  rw [OModulePresheaf.d_apply, OModulePresheaf.d_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [map_zsmul]
  exact congrArg (fun x : (G).obj (K.inter s) => ((-1 : ℤ) ^ (k : ℕ)) • x)
    (finiteFreeTensorSectionsEquiv_restriction J (K.inter (K.face s k)) f L
      (K.inter_le_inter_face s k) (c (K.face s k)) j)

/-- Vanishing in a positive degree is preserved by tensoring with the
actual finite free module sheaf. The preceding boundary is constructed
from the original coordinate boundaries and the inverse cochain comparison. -/
theorem finiteFreeTensor_subsingleton_HSucc (q : ℕ) [Subsingleton ((G).HSucc K q)] :
    Subsingleton ((F).HSucc K q) := by
  rw [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff']
  intro z
  let E (r : ℕ) := finiteFreeTensorCochainEquiv f L J K r
  have hcycle (j : J) : (G).d K (q + 1) (E (q + 1) z.val j) = 0 := by
    calc
      (G).d K (q + 1) (E (q + 1) z.val j) =
          E (q + 2) ((F).d K (q + 1) z.val) j :=
        (congrFun (finiteFreeTensorCochainEquiv_d f L J K (q + 1) z.val) j).symm
      _ = E (q + 2) 0 j :=
        congrArg (fun x : (F).cochain K (q + 2) => E (q + 2) x j) z.property
      _ = 0 := congrFun (map_zero (E (q + 2))) j
  have hboundary (j : J) : ∃ y : (G).cochain K q, (G).d K q y = E (q + 1) z.val j := by
    let w : LinearMap.ker ((G).d K (q + 1)) := ⟨E (q + 1) z.val j, hcycle j⟩
    have hw : (Submodule.Quotient.mk w : (G).HSucc K q) = 0 := Subsingleton.elim _ _
    exact (Submodule.Quotient.mk_eq_zero
      ((LinearMap.range ((G).d K q)).comap (LinearMap.ker ((G).d K (q + 1))).subtype)).mp hw
  choose y hy using hboundary
  change z.val ∈ LinearMap.range ((F).d K q)
  refine ⟨(E q).symm y, ?_⟩
  apply (E (q + 1)).injective
  calc
    E (q + 1) ((F).d K q ((E q).symm y)) =
        fun j => (G).d K q (E q ((E q).symm y) j) :=
      finiteFreeTensorCochainEquiv_d f L J K q ((E q).symm y)
    _ = fun j => (G).d K q (y j) :=
      congrArg (fun x : J → (G).cochain K q => fun j => (G).d K q (x j))
        ((E q).apply_symm_apply y)
    _ = E (q + 1) z.val := funext hy

end AlgebraicGeometry.Scheme.Modules
