/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.DirectSumExactness
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.Tactic.Abel

/-!
# Actual stabilization of kernels in adic reductions

Artin--Rees gives a bound for the preimage of an ideal power under a
linear map with finite target. Consequently, the image of a sufficiently
late reduced kernel in a fixed quotient is the image of the original
kernel.

For a submodule of a finite module, a second Artin--Rees bound recovers
its own adic quotient from the reduced image in a sufficiently late
ambient quotient. The comparison is induced by the original element,
and it commutes with the actual ambient quotient transitions.

These are the two affine stabilization steps in the construction of
kernels of coherent formal modules. No stabilized image, quotient
comparison, or Artin--Rees bound is an input.

https://stacks.math.columbia.edu/tag/087X
-/

noncomputable section

namespace AdicKernel

universe u v w

variable {R : Type u} [CommRing R] (I : Ideal R)
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]

/-- A sufficiently deep approximate kernel differs from the actual kernel
by a prescribed ideal power. The source module need not be finite. -/
theorem exists_preimage_bound [IsNoetherianRing R] [Module.Finite R N]
    (f : M →ₗ[R] N) :
    ∃ c : ℕ, ∀ n : ℕ,
      (I ^ (n + c) • (⊤ : Submodule R N)).comap f ≤
        f.ker ⊔ I ^ n • (⊤ : Submodule R M) := by
  let q : M →ₗ[R] f.range := f.rangeRestrict
  have hq : Function.Surjective q := f.surjective_rangeRestrict
  obtain ⟨c, hc⟩ := AdicCompletion.exists_adic_bound_of_injective I
    f.range.subtype Subtype.val_injective
  refine ⟨c, ?_⟩
  intro n x hx
  have hy : q x ∈ I ^ n • (⊤ : Submodule R f.range) := hc n hx
  have hmap : (I ^ n • (⊤ : Submodule R M)).map q =
      I ^ n • (⊤ : Submodule R f.range) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hq]
  rw [← hmap] at hy
  obtain ⟨z, hz, he⟩ := Submodule.mem_map.mp hy
  have hfz : f z = f x := congrArg Subtype.val he
  apply Submodule.mem_sup.mpr
  refine ⟨x - z, ?_, z, hz, sub_add_cancel x z⟩
  change f (x - z) = 0
  rw [map_sub, hfz, sub_self]

/-- The actual reduced kernels have eventually constant images in every
fixed ambient quotient, with one uniform Artin--Rees shift. -/
theorem exists_kernel_image_stable [IsNoetherianRing R] [Module.Finite R N]
    (f : M →ₗ[R] N) :
    ∃ c : ℕ, ∀ (m l : ℕ) (hml : m ≤ l), m + c ≤ l →
      (((f.reduceModIdeal (I ^ l)).restrictScalars R).ker).map
          (Submodule.factorPow I M hml) =
        f.ker.map (I ^ m • (⊤ : Submodule R M)).mkQ := by
  obtain ⟨c, hc⟩ := exists_preimage_bound I f
  refine ⟨c, ?_⟩
  intro m l hml hl
  ext y
  constructor
  · intro hy
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hy
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
      (I ^ l • (⊤ : Submodule R M)) q
    have hfx : f x ∈ I ^ l • (⊤ : Submodule R N) := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      exact hq
    have hx : x ∈ f.ker ⊔ I ^ m • (⊤ : Submodule R M) :=
      hc m (Submodule.smul_mono_left (Ideal.pow_le_pow_right hl) hfx)
    obtain ⟨k, hk, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    apply Submodule.mem_map.mpr
    refine ⟨k, hk, ?_⟩
    change (Submodule.Quotient.mk k : M ⧸ (I ^ m • (⊤ : Submodule R M))) =
      Submodule.Quotient.mk (k + z)
    apply (Submodule.Quotient.eq _).mpr
    rw [show k - (k + z) = -z by abel]
    exact Submodule.neg_mem _ hz
  · intro hy
    obtain ⟨k, hk, rfl⟩ := Submodule.mem_map.mp hy
    apply Submodule.mem_map.mpr
    refine ⟨Submodule.Quotient.mk k, ?_, rfl⟩
    change (Submodule.Quotient.mk (f k) : N ⧸ (I ^ l • (⊤ : Submodule R N))) = 0
    rw [LinearMap.mem_ker.mp hk, Submodule.Quotient.mk_zero]

variable (P : Submodule R M)

/-- The image of the original submodule in the actual ambient adic quotient. -/
def imageAt (m : ℕ) : Submodule R (M ⧸ (I ^ m • (⊤ : Submodule R M))) :=
  P.map (I ^ m • (⊤ : Submodule R M)).mkQ

/-- Projection of an original submodule element to that actual image. -/
def imageProjection (m : ℕ) : P →ₗ[R] imageAt I P m :=
  (((I ^ m • (⊤ : Submodule R M)).mkQ).comp P.subtype).codRestrict
    (imageAt I P m) (fun x => Submodule.mem_map.mpr ⟨x.val, x.property, rfl⟩)

/-- The image projection uses the literal original quotient class. -/
theorem imageProjection_apply (m : ℕ) (x : P) :
    (imageProjection I P m x).val = Submodule.Quotient.mk x.val := rfl

theorem imageProjection_surjective (m : ℕ) : Function.Surjective (imageProjection I P m) := by
  intro y
  obtain ⟨x, hx, he⟩ := Submodule.mem_map.mp y.property
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

/-- Its kernel is precisely the filtration induced from the ambient module. -/
theorem imageProjection_ker (m : ℕ) :
    (imageProjection I P m).ker =
      (I ^ m • (⊤ : Submodule R M)).comap P.subtype := by
  ext x
  change imageProjection I P m x = 0 ↔ x.val ∈ I ^ m • (⊤ : Submodule R M)
  constructor
  · intro hx
    exact (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val hx)
  · intro hx
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx

/-- The original ambient quotient transition restricts to the images. -/
def imageTransition {m l : ℕ} (hml : m ≤ l) : imageAt I P l →ₗ[R] imageAt I P m :=
  ((Submodule.factorPow I M hml).domRestrict (imageAt I P l)).codRestrict
    (imageAt I P m) (by
      intro x
      obtain ⟨p, hp, he⟩ := Submodule.mem_map.mp x.property
      apply Submodule.mem_map.mpr
      refine ⟨p, hp, ?_⟩
      change (I ^ m • (⊤ : Submodule R M)).mkQ p = Submodule.factorPow I M hml x.val
      rw [← he]
      rfl)

/-- The restricted transition retains each original submodule element. -/
theorem imageTransition_imageProjection {m l : ℕ} (hml : m ≤ l) (x : P) :
    imageTransition I P hml (imageProjection I P l x) = imageProjection I P m x := by
  apply Subtype.ext
  rfl

section Noetherian

variable [IsNoetherianRing R] [Module.Finite R M]

/-- An actual Artin--Rees bound for the given submodule inclusion. -/
def imageBound : ℕ :=
  (AdicCompletion.exists_adic_bound_of_injective I P.subtype Subtype.val_injective).choose

/-- At the specified precision, the induced kernel lies in the submodule's
own adic power. -/
theorem imageBound_spec (n m : ℕ) (h : n + imageBound I P ≤ m) :
    (imageProjection I P m).ker ≤ I ^ n • (⊤ : Submodule R P) := by
  rw [imageProjection_ker]
  exact (Submodule.comap_mono (Submodule.pow_smul_top_le I M h)).trans
    ((AdicCompletion.exists_adic_bound_of_injective I P.subtype
      Subtype.val_injective).choose_spec n)

/-- After the actual bound, reduction of the image projection is bijective. -/
theorem imageProjection_reduce_bijective (n m : ℕ) (h : n + imageBound I P ≤ m) :
    Function.Bijective ((imageProjection I P m).reduceModIdeal (I ^ n)) := by
  let q : P →ₗ[R] imageAt I P m := imageProjection I P m
  have hq : Function.Surjective q := imageProjection_surjective I P m
  have hmap : (I ^ n • (⊤ : Submodule R P)).map q =
      I ^ n • (⊤ : Submodule R (imageAt I P m)) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hq]
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (I ^ n • (⊤ : Submodule R P)) z
    have hx : q x ∈ I ^ n • (⊤ : Submodule R (imageAt I P m)) :=
      (Submodule.Quotient.mk_eq_zero _).mp hz
    rw [← hmap] at hx
    obtain ⟨y, hy, he⟩ := Submodule.mem_map.mp hx
    have hxy : x - y ∈ q.ker := by
      change q (x - y) = 0
      rw [map_sub, he, sub_self]
    have hsmall : x - y ∈ I ^ n • (⊤ : Submodule R P) := imageBound_spec I P n m h hxy
    have hxmem : x ∈ I ^ n • (⊤ : Submodule R P) := by
      have hs := Submodule.add_mem (I ^ n • (⊤ : Submodule R P)) hsmall hy
      rw [sub_add_cancel] at hs
      exact hs
    exact (Submodule.Quotient.mk_eq_zero _).mpr hxmem
  · intro z
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective
      (I ^ n • (⊤ : Submodule R (imageAt I P m))) z
    obtain ⟨x, hx⟩ := hq y
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    change Submodule.Quotient.mk (q x) = Submodule.Quotient.mk y
    exact congrArg Submodule.Quotient.mk hx

/-- The reduced stable image recovers the original submodule's own adic
quotient, through the actual image projection. -/
def imageQuotientEquiv (n m : ℕ) (h : n + imageBound I P ≤ m) :
    (P ⧸ (I ^ n • (⊤ : Submodule R P))) ≃ₗ[R ⧸ I ^ n]
      ((imageAt I P m) ⧸ (I ^ n • (⊤ : Submodule R (imageAt I P m)))) :=
  LinearEquiv.ofBijective ((imageProjection I P m).reduceModIdeal (I ^ n))
    (imageProjection_reduce_bijective I P n m h)

/-- The comparison sends the class of an original element to the class
of its original image, without changing the representative. -/
theorem imageQuotientEquiv_mk (n m : ℕ) (h : n + imageBound I P ≤ m) (x : P) :
    imageQuotientEquiv I P n m h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (imageProjection I P m x) :=
  LinearMap.reduceModIdeal_apply (I ^ n) (imageProjection I P m) x

/-- The recovery isomorphisms commute with the original transitions
between all sufficiently late images. -/
theorem imageTransition_imageQuotientEquiv (n m l : ℕ) (hml : m ≤ l)
    (hm : n + imageBound I P ≤ m) (hl : n + imageBound I P ≤ l)
    (x : P ⧸ (I ^ n • (⊤ : Submodule R P))) :
    (imageTransition I P hml).reduceModIdeal (I ^ n) (imageQuotientEquiv I P n l hl x) =
      imageQuotientEquiv I P n m hm x := by
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective (I ^ n • (⊤ : Submodule R P)) x
  rw [imageQuotientEquiv_mk, imageQuotientEquiv_mk, LinearMap.reduceModIdeal_apply,
    imageTransition_imageProjection]

end Noetherian

end AdicKernel
