/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Modules.Sections.SectionsGluing
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Order.Fin.Tuple

/-!
# Actual global sections and zeroth ordered Čech cohomology

Restriction of a native global section defines a Čech cocycle. The
zeroth cocycle equation gives agreement on every pairwise intersection,
including both possible orders of the two chart indices. The native
sheaf gluing theorem constructs the unique global section with precisely
those restrictions.

The resulting linear equivalence preserves every original chart value.
It applies to arbitrary native module sheaves, without quasicoherence or
affineness of intersections. For a separated structural morphism it is
natural for the existing Čech maps defined on affine intersections.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R))

private theorem zeroIdx_ext (K : X.OrderedAffineCover) {s t : K.Idx 0}
    (h : s.val 0 = t.val 0) : s = t := by
  apply Subtype.ext
  funext j
  exact (congrArg s.val (Fin.eq_zero j)).trans
    (h.trans (congrArg t.val (Fin.eq_zero j).symm))

private theorem zeroInter_covers (K : X.OrderedAffineCover) :
    (⊤ : X.Opens) ≤ ⨆ s : K.Idx 0, K.inter s := by
  rw [← K.iSup_eq_top]
  apply iSup_le
  intro i
  exact le_iSup_of_le
    (⟨fun _ : Fin 1 => i, Subsingleton.strictMono (fun _ : Fin 1 => i)⟩ : K.Idx 0)
    (le_iInf fun _ => le_rfl)

private theorem restrictedCochainValue_eq (F : OModulePresheaf f)
    (K : X.OrderedAffineCover) (z : F.cochain K 0)
    {s t : K.Idx 0} (hst : s = t) {W : X.Opens}
    (hs : W ≤ K.inter s) (ht : W ≤ K.inter t) : F.res hs (z s) = F.res ht (z t) := by
  cases hst
  rfl

private theorem h0_pair_agrees_of_lt (F : OModulePresheaf f)
    (K : X.OrderedAffineCover) (z : F.H0 K) {s t : K.Idx 0}
    (hst : s.val 0 < t.val 0) {W : X.Opens}
    (hs : W ≤ K.inter s) (ht : W ≤ K.inter t) :
    F.res hs (z.val s) = F.res ht (z.val t) := by
  let ρ : K.Idx 1 :=
    ⟨Fin.cons (s.val 0) (fun _ : Fin 1 => t.val 0),
      Fin.strictMono_cons.mpr ⟨fun _ => hst, Subsingleton.strictMono _⟩⟩
  have hρ0 : K.face ρ 0 = t := by
    apply zeroIdx_ext K
    rfl
  have hρ1 : K.face ρ 1 = s := by
    apply zeroIdx_ext K
    rfl
  have hW : W ≤ K.inter ρ := by
    apply le_iInf
    intro j
    refine Fin.cases ?_ (fun _ => ?_) j
    · exact hs.trans (K.inter_le s 0)
    · exact ht.trans (K.inter_le t 0)
  have hz := congrFun (LinearMap.mem_ker.mp z.property) ρ
  rw [OModulePresheaf.d_apply] at hz
  change (∑ j : Fin 2, (-1 : ℤ) ^ (j : ℕ) •
    F.res (K.inter_le_inter_face ρ j) (z.val (K.face ρ j))) = 0 at hz
  rw [Fin.sum_univ_two] at hz
  have hδ :
      F.res (K.inter_le_inter_face ρ 0) (z.val (K.face ρ 0)) =
        F.res (K.inter_le_inter_face ρ 1) (z.val (K.face ρ 1)) := by
    simpa only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul,
      add_neg_eq_zero] using hz
  have he := congrArg (F.res hW) hδ
  rw [OModulePresheaf.res_res, OModulePresheaf.res_res] at he
  calc
    F.res hs (z.val s) =
        F.res (hW.trans (K.inter_le_inter_face ρ 1)) (z.val (K.face ρ 1)) :=
      (restrictedCochainValue_eq f F K z.val hρ1 _ hs).symm
    _ = F.res (hW.trans (K.inter_le_inter_face ρ 0)) (z.val (K.face ρ 0)) := he.symm
    _ = F.res ht (z.val t) := restrictedCochainValue_eq f F K z.val hρ0 _ ht

private theorem h0_compatible (F : OModulePresheaf f)
    (K : X.OrderedAffineCover) (z : F.H0 K) (s t : K.Idx 0) :
    F.res (inf_le_left : K.inter s ⊓ K.inter t ≤ K.inter s) (z.val s) =
      F.res (inf_le_right : K.inter s ⊓ K.inter t ≤ K.inter t) (z.val t) := by
  rcases lt_trichotomy (s.val 0) (t.val 0) with h | h | h
  · exact h0_pair_agrees_of_lt f F K z h inf_le_left inf_le_right
  · exact restrictedCochainValue_eq f F K z.val (zeroIdx_ext K h) inf_le_left inf_le_right
  · exact (h0_pair_agrees_of_lt f F K z h inf_le_right inf_le_left).symm

/-- Restriction of the original global section to every zeroth Čech chart. -/
def cechAugmentationCochain (M : X.Modules) (K : X.OrderedAffineCover) :
    sectionModuleOverBase f M ⊤ →ₗ[R] (toOModulePresheaf f M).cochain K 0 :=
  LinearMap.pi fun _s => (toOModulePresheaf f M).res le_top

/-- The augmentation cochain evaluates to the original restriction. -/
theorem cechAugmentationCochain_apply (M : X.Modules) (K : X.OrderedAffineCover)
    (x : sectionModuleOverBase f M ⊤) (s : K.Idx 0) :
    cechAugmentationCochain f M K x s =
      (toOModulePresheaf f M).res (show K.inter s ≤ ⊤ from le_top) x := rfl

private theorem cechAugmentationCochain_mem_ker (M : X.Modules)
    (K : X.OrderedAffineCover) (x : sectionModuleOverBase f M ⊤) :
    cechAugmentationCochain f M K x ∈ ((toOModulePresheaf f M).d K 0).ker := by
  apply LinearMap.mem_ker.mpr
  funext s
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul,
    Pi.zero_apply]
  rw [cechAugmentationCochain_apply, cechAugmentationCochain_apply]
  let F : OModulePresheaf f := toOModulePresheaf f M
  let y : F.obj ⊤ := x
  change F.res (K.inter_le_inter_face s 0)
      (F.res (show K.inter (K.face s 0) ≤ ⊤ from le_top) y) +
      -F.res (K.inter_le_inter_face s 1)
        (F.res (show K.inter (K.face s 1) ≤ ⊤ from le_top) y) = 0
  rw [OModulePresheaf.res_res, OModulePresheaf.res_res]
  exact add_neg_cancel _

/-- Restriction gives the actual native global section as a zeroth Čech cocycle. -/
def cechAugmentation (M : X.Modules) (K : X.OrderedAffineCover) :
    sectionModuleOverBase f M ⊤ →ₗ[R] (toOModulePresheaf f M).H0 K :=
  (cechAugmentationCochain f M K).codRestrict _
    (cechAugmentationCochain_mem_ker f M K)

/-- The constructed cocycle keeps the literal restriction of the given section. -/
theorem cechAugmentation_apply (M : X.Modules) (K : X.OrderedAffineCover)
    (x : sectionModuleOverBase f M ⊤) (s : K.Idx 0) :
    (cechAugmentation f M K x).val s =
      M.presheaf.map (homOfLE (show K.inter s ≤ ⊤ from le_top)).op x := rfl

/-- Native sheaf separatedness makes the original augmentation injective. -/
theorem cechAugmentation_injective (M : X.Modules) (K : X.OrderedAffineCover) :
    Function.Injective (cechAugmentation f M K) := by
  intro x y h
  apply (eq_of_forall_map_homOfLE_eq_and_exists_of_compatible M
    (K.inter (i := 0)) ⊤ (fun _ => le_top) (zeroInter_covers K)).1 x y
  intro s
  exact congrArg (fun z : (toOModulePresheaf f M).H0 K => z.val s) h

/-- Native sheaf gluing recovers an actual global section from every
zeroth Čech cocycle, with all prescribed chart restrictions. -/
theorem cechAugmentation_surjective (M : X.Modules) (K : X.OrderedAffineCover) :
    Function.Surjective (cechAugmentation f M K) := by
  intro z
  obtain ⟨x, hx⟩ := (eq_of_forall_map_homOfLE_eq_and_exists_of_compatible M
    (K.inter (i := 0)) ⊤ (fun _ => le_top) (zeroInter_covers K)).2
      z.val (h0_compatible f (toOModulePresheaf f M) K z)
  refine ⟨x, ?_⟩
  apply Subtype.ext
  funext s
  exact hx s

/-- The original native global-section module is linearly equivalent to
the actual zeroth Čech cohomology of its section presheaf. -/
def globalSectionsCechH0Equiv (M : X.Modules) (K : X.OrderedAffineCover) :
    sectionModuleOverBase f M ⊤ ≃ₗ[R] (toOModulePresheaf f M).H0 K :=
  LinearEquiv.ofBijective (cechAugmentation f M K)
    ⟨cechAugmentation_injective f M K, cechAugmentation_surjective f M K⟩

/-- The comparison is induced by the original restriction maps. -/
theorem globalSectionsCechH0Equiv_apply (M : X.Modules) (K : X.OrderedAffineCover)
    (x : sectionModuleOverBase f M ⊤) (s : K.Idx 0) :
    (globalSectionsCechH0Equiv f M K x).val s =
      M.presheaf.map (homOfLE (show K.inter s ≤ ⊤ from le_top)).op x := rfl

/-- Gluing the cocycle recovers each of its prescribed original sections. -/
theorem globalSectionsCechH0Equiv_symm_restrict (M : X.Modules)
    (K : X.OrderedAffineCover) (z : (toOModulePresheaf f M).H0 K) (s : K.Idx 0) :
    M.presheaf.map (homOfLE (show K.inter s ≤ ⊤ from le_top)).op
      ((globalSectionsCechH0Equiv f M K).symm z) = z.val s :=
  congrArg (fun w : (toOModulePresheaf f M).H0 K => w.val s)
    ((globalSectionsCechH0Equiv f M K).apply_symm_apply z)

/-- The comparison commutes with the existing maps on Čech cohomology
and the original native global-section morphism. -/
theorem globalSectionsCechH0Equiv_naturality [IsSeparated f]
    {M N : X.Modules} (φ : M ⟶ N) (K : X.OrderedAffineCover)
    (x : sectionModuleOverBase f M ⊤) :
    (toOModulePresheafHom f φ).toAffHom.H0Map K (globalSectionsCechH0Equiv f M K x) =
      globalSectionsCechH0Equiv f N K ((toOModulePresheafHom f φ).app ⊤ x) := by
  apply Subtype.ext
  funext s
  exact (toOModulePresheafHom f φ).naturality_apply
    (show K.inter s ≤ ⊤ from le_top) x

end AlgebraicGeometry.Scheme.Modules
