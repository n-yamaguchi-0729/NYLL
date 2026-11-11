/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.Ring
public import Nyll.SchemeTheory.GroupSchemes.HopfAlgebra.Basic
public import Nyll.SchemeTheory.GroupSchemes.HopfAlgebra.Quotients
public import Nyll.SchemeTheory.LocalGeometry.Points

/-!
# Flatness and freeness of Hopf subalgebras

Use the quotient torsor isomorphism to descend faithful flatness, prove surjectivity on
spectra over an algebraically closed field, and lift quotient bases through nilpotent ideals.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_faithfullyFlat_map_toAlgHom_tensor_of_free_map_of_ker_eq_span.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.HopfFaithfullyFlatBaseChange

open scoped TensorProduct

universe u v

open AbelianVarieties.NOSProofs.SubalgebraTensorQuotients

namespace TensorBaseChange
open TensorTorsor

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
variable (K' K : Subalgebra k H) [Algebra ↥K' ↥K] [IsScalarTower ↥K' ↥K H]
variable (hΔ' : ∀ x ∈ K', Coalgebra.comul (R := k) x ∈
  Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K', ∃ b ∈ K', t = a ⊗ₜ[k] b})
variable (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
  Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})

/-- The canonical inclusion of Hopf subalgebras. -/
noncomputable abbrev inclKH : ↥K →ₐ[↥K'] H := IsScalarTower.toAlgHom (↥K') (↥K) H

/-- Tensor the subalgebra inclusion with the identity. -/
noncomputable abbrev idIncl : H ⊗[↥K'] ↥K →ₐ[↥K'] H ⊗[↥K'] H :=
  Algebra.TensorProduct.map (AlgHom.id (↥K') H) (inclKH K' K)

/-- The image of the subalgebra in the augmentation quotient. -/
noncomputable abbrev Kbar : Subalgebra k (Q K') := K.map (π K')

/-- Include the quotient image after scalar extension. -/
noncomputable abbrev ιbar : H ⊗[k] ↥(Kbar K' K) →ₐ[k] C K' :=
  Algebra.TensorProduct.map (AlgHom.id k H) (Kbar K' K).val

omit [Algebra ↥K' ↥K] [IsScalarTower ↥K' ↥K H] in
theorem ιbar_injective : Function.Injective (ιbar K' K) := by
  have : Function.Injective ((Kbar K' K).val.toLinearMap.lTensor H) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  intro x y hxy
  exact this (by exact hxy)

/-- The torsor map composed with the tensor inclusion. -/
noncomputable def c : H ⊗[↥K'] ↥K →ₐ[k] C K' :=
  ((β K' hΔ').restrictScalars k).comp ((idIncl K' K).restrictScalars k)

theorem c_tmul (h : H) (a : ↥K) : c K' K hΔ' (h ⊗ₜ[↥K'] a) = (h ⊗ₜ[k] (1 : Q K')) * θ K'
    (Coalgebra.comul (R := k) (a : H)) := by
  simp only [c, AlgHom.comp_apply, AlgHom.restrictScalars_apply]
  exact β_tmul K' hΔ' h _

omit [Algebra ↥K' ↥K] [IsScalarTower ↥K' ↥K H] in
theorem θ_mem_range_of_mem_span (t : H ⊗[k] H)
    (ht : t ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b}) :
    θ K' t ∈ (ιbar K' K).range := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨x, hx, y, hy, rfl⟩ := ht
    refine ⟨x ⊗ₜ[k] ⟨π K' y, Subalgebra.mem_map.mpr ⟨y, hy, rfl⟩⟩, ?_⟩
    rfl
  | zero => rw [map_zero]; exact zero_mem _
  | add s t _ _ hs ht => rw [map_add]; exact add_mem hs ht
  | smul r t _ ht => rw [map_smul]; exact Subalgebra.smul_mem _ ht r

include hΔ in
theorem range_c_le : (c K' K hΔ').range ≤ (ιbar K' K).range := by
  rintro _ ⟨t, rfl⟩
  change c K' K hΔ' t ∈ _
  induction t using TensorProduct.inductionOn with
  | tmul h a =>
    rw [c_tmul]
    have hθ : θ K' (Coalgebra.comul (R := k) (a : H)) ∈ (ιbar K' K).range :=
      θ_mem_range_of_mem_span K' K _ (hΔ a a.2)
    have h1 : (h ⊗ₜ[k] (1 : Q K')) ∈ (ιbar K' K).range := ⟨h ⊗ₜ[k] 1, rfl⟩
    exact mul_mem h1 hθ
  | add s t hs ht => rw [map_add]; exact add_mem hs ht

include hΔ in
theorem le_range_c : (ιbar K' K).range ≤ (c K' K hΔ').range := by
  rw [Algebra.TensorProduct.map_range]
  apply sup_le
  · rintro _ ⟨h, rfl⟩
    refine ⟨h ⊗ₜ[↥K'] 1, ?_⟩
    change c K' K hΔ' (h ⊗ₜ[↥K'] 1) = h ⊗ₜ[k] (1 : Q K')
    rw [c_tmul, Subalgebra.coe_one, Bialgebra.comul_one, show (1 : H ⊗[k] H) = (1 : H) ⊗ₜ[k] (1 : H)
      from rfl,
      θ_tmul, map_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one]
  · rintro _ ⟨⟨_, ha⟩, rfl⟩
    obtain ⟨a, haK, rfl⟩ := Subalgebra.mem_map.mp ha
    have key' : ∀ t ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b},
        ∃ s : H ⊗[↥K'] ↥K, (idIncl K' K) s = mapK K' ((HopfAlgebra.antipode k).rTensor H t) := by
      intro t ht
      induction ht using Submodule.span_induction with
      | mem t ht =>
        obtain ⟨x, hx, y, hy, rfl⟩ := ht
        exact ⟨(HopfAlgebra.antipode k x) ⊗ₜ[↥K'] ⟨y, hy⟩, rfl⟩
      | zero => exact ⟨0, by rw [map_zero, map_zero, map_zero]⟩
      | add s t _ _ hs ht =>
        obtain ⟨s₁, hs₁⟩ := hs; obtain ⟨t₁, ht₁⟩ := ht
        exact ⟨s₁ + t₁, by rw [map_add, map_add, map_add, hs₁, ht₁]⟩
      | smul r t _ ht =>
        obtain ⟨t₁, ht₁⟩ := ht
        refine ⟨algebraMap k (↥K') r • t₁, ?_⟩
        rw [map_smul, ht₁, map_smul, algebraMap_smul, map_smul]
    obtain ⟨s, hs⟩ := key' _ (hΔ a haK)
    refine ⟨s, ?_⟩
    change (β K' hΔ') ((idIncl K' K) s) = (1 : H) ⊗ₜ[k] π K' a
    rw [hs, ← ψ₀_apply, β_ψ₀]

include hΔ in
theorem range_c_eq : (c K' K hΔ').range = (ιbar K' K).range :=
  le_antisymm (range_c_le K' K hΔ' hΔ) (le_range_c K' K hΔ' hΔ)

theorem nontrivial_Q : Nontrivial (Q K') := by
  refine ⟨⟨0, 1, fun h01 => ?_⟩⟩
  have h1 : J K' = ⊤ := Ideal.Quotient.zero_eq_one_iff.mp h01
  revert h1
  intro h1
  have hε : ∀ x ∈ J K', Coalgebra.counit (R := k) x = 0 := by
    intro x hx
    rw [J] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hx.2
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul r x _ hx => rw [smul_eq_mul, Bialgebra.counit_mul, hx, mul_zero]
  have := hε 1 ((Ideal.eq_top_iff_one _).mp h1)
  rw [Bialgebra.counit_one] at this
  exact one_ne_zero this

/-- The induced isomorphism onto the tensor product with the quotient image. -/
noncomputable def e₂ [Module.Flat (↥K') H] : (H ⊗[↥K'] ↥K) ≃ₐ[k] (H ⊗[k] ↥(Kbar K' K)) :=
  have hinj : Function.Injective (c K' K hΔ') := by
    have h1 : Function.Injective (idIncl K' K) := by
      have : Function.Injective ((inclKH K' K).toLinearMap.lTensor H) :=
        Module.Flat.lTensor_preserves_injective_linearMap _ (fun x y h => Subtype.ext h)
      intro x y hxy
      exact this (by exact hxy)
    intro x y hxy
    exact h1 ((βEquiv K' hΔ').injective hxy)
  (AlgEquiv.ofInjective (c K' K hΔ') hinj).trans
    ((Subalgebra.equivOfEq _ _ (range_c_eq K' K hΔ' hΔ)).trans
      (AlgEquiv.ofInjective (ιbar K' K) (ιbar_injective K' K)).symm)

theorem ιbar_e₂ [Module.Flat (↥K') H] (s : H ⊗[↥K'] ↥K) :
    ιbar K' K (e₂ K' K hΔ' hΔ s) = c K' K hΔ' s := by
  simp only [e₂, AlgEquiv.trans_apply]
  have h1 : ∀ y : ↥((ιbar K' K).range), ιbar K' K ((AlgEquiv.ofInjective (ιbar K' K) (ιbar_injective
    K' K)).symm y) = y := by
    intro y
    have := AlgEquiv.ofInjective_apply (ιbar K' K) (ιbar_injective K' K) ((AlgEquiv.ofInjective
      (ιbar K' K) (ιbar_injective K' K)).symm y)
    rw [AlgEquiv.apply_symm_apply] at this
    exact this.symm
  rw [h1]
  rfl

theorem idIncl_eq [Module.Flat (↥K') H] :
    (idIncl K' K).toRingHom = ((βEquiv K' hΔ').symm.toRingEquiv.toRingHom.comp (ιbar K'
      K).toRingHom).comp
      (e₂ K' K hΔ' hΔ).toRingEquiv.toRingHom := by
  apply RingHom.ext
  intro s
  change idIncl K' K s = (βEquiv K' hΔ').symm (ιbar K' K (e₂ K' K hΔ' hΔ s))
  rw [ιbar_e₂, AlgEquiv.eq_symm_apply]
  rfl

theorem respectsIso_left {R S T : Type v} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (e :
    S ≃+* T)
    (hf : f.FaithfullyFlat) : (e.toRingHom.comp f).FaithfullyFlat :=
  RingHom.FaithfullyFlat.respectsIso.1 f e hf

theorem respectsIso_right {R S T : Type v} [CommRing R] [CommRing S] [CommRing T] (f : S →+* T) (e :
    R ≃+* S)
    (hf : f.FaithfullyFlat) : (f.comp e.toRingHom).FaithfullyFlat :=
  RingHom.FaithfullyFlat.respectsIso.2 f e hf

theorem ff_map_val_id (L : Subalgebra k (Q K')) [Module.Free ↥L (Q K')] :
    (Algebra.TensorProduct.map L.val (AlgHom.id k H) : ↥L ⊗[k] H →ₐ[k] Q K' ⊗[k]
      H).toRingHom.FaithfullyFlat := by
  have : Nontrivial (Q K') := nontrivial_Q K'
  have : Module.FaithfullyFlat (↥L) (Q K') := inferInstance
  have : Module.FaithfullyFlat (↥L ⊗[k] H) ((↥L ⊗[k] H) ⊗[↥L] Q K') := inferInstance
  have h1 : (algebraMap (↥L ⊗[k] H) ((↥L ⊗[k] H) ⊗[↥L] Q K')).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  let e : ((↥L ⊗[k] H) ⊗[↥L] Q K') ≃ₐ[↥L] (Q K' ⊗[k] H) :=
    (Algebra.TensorProduct.comm (↥L) (↥L ⊗[k] H) (Q K')).trans
      (Algebra.TensorProduct.cancelBaseChange k (↥L) (↥L) (Q K') H)
  have h2 := respectsIso_left _ e.toRingEquiv h1
  convert h2 using 1
  apply RingHom.ext
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul a h =>
    change (a : Q K') ⊗ₜ[k] h = e ((a ⊗ₜ[k] h) ⊗ₜ[↥L] (1 : Q K'))
    simp only [e]
    erw [Algebra.TensorProduct.cancelBaseChange_tmul]
    rw [Algebra.smul_def, mul_one]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [Algebra ↥K' ↥K] [IsScalarTower ↥K' ↥K H] in
theorem ff_ιbar [Module.Free ↥(Kbar K' K) (Q K')] : (ιbar K' K).toRingHom.FaithfullyFlat := by
  have h := ff_map_val_id K' (Kbar K' K)
  have h2 := respectsIso_right _ (Algebra.TensorProduct.comm k H ↥(Kbar K' K)).toRingEquiv
    (respectsIso_left _ (Algebra.TensorProduct.comm k (Q K') H).toRingEquiv h)
  convert h2 using 1
  apply RingHom.ext
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul h a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

include hΔ' hΔ in
theorem ff_idIncl [Module.Flat (↥K') H] [Module.Free ↥(Kbar K' K) (Q K')] :
    (idIncl K' K).toRingHom.FaithfullyFlat := by
  rw [idIncl_eq K' K hΔ' hΔ]
  exact respectsIso_right _ _ (respectsIso_left _ _ (ff_ιbar K' K))

include hΔ' hΔ in
theorem ff_inclId [Module.Flat (↥K') H] [Module.Free ↥(Kbar K' K) (Q K')] :
    (Algebra.TensorProduct.map (inclKH K' K) (AlgHom.id (↥K') H)).toRingHom.FaithfullyFlat := by
  have h := ff_idIncl K' K hΔ' hΔ
  have h2 := respectsIso_right _ (Algebra.TensorProduct.comm (↥K') (↥K) H).toRingEquiv
    (respectsIso_left _ (Algebra.TensorProduct.comm (↥K') H H).toRingEquiv h)
  convert h2 using 1
  apply RingHom.ext
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul a h => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end TensorBaseChange

open TensorTorsor TensorBaseChange in
theorem _root_.HopfAlgebra.faithfullyFlat_map_toAlgHom_tensor_of_free_map_of_ker_eq_span
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    (K' K : Subalgebra k H) [Algebra ↥K' ↥K] [IsScalarTower ↥K' ↥K H]
    (hΔ' : ∀ x ∈ K', Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K', ∃ b ∈ K', t = a ⊗ₜ[k] b})
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    [Module.Flat ↥K' H]
    (Hb : Type v) [CommRing Hb] [Algebra k Hb] (π : H →ₐ[k] Hb) (hπ : Function.Surjective π)
    (hker : RingHom.ker π = Ideal.span {x : H | x ∈ K' ∧ Coalgebra.counit (R := k) x = 0})
    [Module.Free ↥(K.map π) Hb] :
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ↥K' ↥K H) (AlgHom.id ↥K'
      H)).toRingHom.FaithfullyFlat := by
  classical
  have hJ : J K' = RingHom.ker π := by rw [hker]; rfl
  let e : Q K' ≃ₐ[k] Hb :=
    (Ideal.quotientEquivAlgOfEq k hJ).trans (Ideal.quotientKerAlgEquivOfSurjective hπ)
  have he : ∀ x : H, e (TensorTorsor.π K' x) = π x := by
    intro x
    change (Ideal.quotientKerAlgEquivOfSurjective hπ) ((Ideal.quotientEquivAlgOfEq k hJ)
      (Ideal.Quotient.mkₐ k (J K') x)) = π x
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.quotientEquivAlgOfEq_mk]
    exact Ideal.quotientKerAlgEquivOfSurjective_apply hπ x
  have hmap : (Kbar K' K).map e.toAlgHom = K.map π := by
    rw [Kbar, Subalgebra.map_map]
    congr 1
  let eK : ↥(Kbar K' K) ≃ₐ[k] ↥(K.map π) :=
    ((Kbar K' K).equivMapOfInjective e.toAlgHom e.injective).trans (Subalgebra.equivOfEq _ _ hmap)
  have heK : ∀ a : ↥(Kbar K' K), ((eK a : ↥(K.map π)) : Hb) = e (a : Q K') := fun a => rfl
  have heK' : ∀ b : ↥(K.map π), ((eK.symm b : ↥(Kbar K' K)) : Q K') = e.symm (b : Hb) := by
    intro b
    apply e.injective
    rw [AlgEquiv.apply_symm_apply, ← heK, AlgEquiv.apply_symm_apply]
  have : Module.Free ↥(Kbar K' K) (Q K') := by
    let σ : ↥(K.map π) →+* ↥(Kbar K' K) := eK.symm.toRingEquiv.toRingHom
    let σ' : ↥(Kbar K' K) →+* ↥(K.map π) := eK.toRingEquiv.toRingHom
    have : RingHomInvPair σ σ' := RingHomInvPair.of_ringEquiv eK.symm.toRingEquiv
    have : RingHomInvPair σ' σ := RingHomInvPair.of_ringEquiv eK.toRingEquiv
    let f : Hb ≃ₛₗ[σ] Q K' :=
      { e.symm.toLinearEquiv.toAddEquiv with
        map_smul' := fun b x => by
          change e.symm ((b : Hb) * x) = (eK.symm b : Q K') * e.symm x
          rw [map_mul, heK'] }
    exact Module.Free.of_equiv f
  exact ff_inclId K' K hΔ' hΔ

end AbelianVarieties.NOSProofs.HopfFaithfullyFlatBaseChange
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_faithfullyFlat_of_flat_of_injective_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.HopfFaithfulFlatness

open scoped TensorProduct

universe u v w

namespace SpectrumSurjectivity

variable {k : Type u} [Field k]

theorem isOpen_range_comap (K : Type v) [CommRing K] [Algebra k K] [Algebra.FiniteType k K]
    (H : Type w) [CommRing H] [Algebra k H] [Algebra.FiniteType k H] [Algebra K H] [IsScalarTower k
      K H]
    [Module.Flat K H] : IsOpen (Set.range (PrimeSpectrum.comap (algebraMap K H))) := by
  have : IsNoetherianRing K := Algebra.FiniteType.isNoetherianRing k K
  have : Algebra.FiniteType K H := Algebra.FiniteType.of_restrictScalars_finiteType k K H
  have : Algebra.FinitePresentation K H := (Algebra.FinitePresentation.of_finiteType (R := K) (A :=
    H)).mp inferInstance
  have : Algebra.HasGoingDown K H := Algebra.HasGoingDown.of_flat
  exact (PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation (R := K) (S :=
    H)).isOpen_range

theorem algHom_eq_of_ker_eq {A : Type*} [CommRing A] [Algebra k A] (z z' : A →ₐ[k] k)
    (h : RingHom.ker z = RingHom.ker z') : z = z' := by
  apply AlgHom.ext
  intro x
  have hx : x - algebraMap k A (z x) ∈ RingHom.ker z := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
  rw [h, RingHom.mem_ker, map_sub, AlgHom.commutes] at hx
  exact (sub_eq_zero.mp hx).symm

theorem exists_algHom_of_finiteType [IsAlgClosed k] {A : Type*} [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] [Nontrivial A] : Nonempty (A →ₐ[k] k) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  have : M.IsMaximal := hM
  let : Field (A ⧸ M) := Ideal.Quotient.field M
  have : Algebra.FiniteType k (A ⧸ M) := inferInstance
  have : Module.Finite k (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ M)
  have : Algebra.IsIntegral k (A ⧸ M) := Algebra.IsIntegral.of_finite k (A ⧸ M)
  have hbij : Function.Bijective (algebraMap k (A ⧸ M)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : (A ⧸ M) ≃ₐ[k] k := (AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ M)) hbij).symm
  exact ⟨e.toAlgHom.comp (Ideal.Quotient.mkₐ k M)⟩

theorem mem_range_comap_iff_exists_lift [IsAlgClosed k] (K : Type v) [CommRing K] [Algebra k K]
    (H : Type w) [CommRing H] [Algebra k H] [Algebra.FiniteType k H] [Algebra K H] [IsScalarTower k
      K H]
    (z : K →ₐ[k] k) :
    (⟨RingHom.ker z.toRingHom, RingHom.ker_isPrime _⟩ : PrimeSpectrum K) ∈
        Set.range (PrimeSpectrum.comap (algebraMap K H)) ↔
      ∃ y : H →ₐ[k] k, y.comp (IsScalarTower.toAlgHom k K H) = z := by
  constructor
  · rintro ⟨P, hP⟩
    obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P.asIdeal P.isPrime.ne_top
    have : M.IsMaximal := hM
    have : Nontrivial (H ⧸ M) := Ideal.Quotient.nontrivial_iff.mpr hM.ne_top
    obtain ⟨y₀⟩ := exists_algHom_of_finiteType (k := k) (A := H ⧸ M)
    refine ⟨y₀.comp (Ideal.Quotient.mkₐ k M), ?_⟩
    have hzmax : (RingHom.ker z.toRingHom).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective z.toRingHom (fun c => ⟨algebraMap k K c, AlgHom.commutes z
        c⟩)
    symm
    apply algHom_eq_of_ker_eq
    apply hzmax.eq_of_le (RingHom.ker_ne_top _)
    intro x hx
    have hPx : (algebraMap K H x) ∈ P.asIdeal := by
      have := congrArg (fun Q : PrimeSpectrum K => x ∈ Q.asIdeal) hP
      simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, eq_iff_iff] at this
      exact this.mpr hx
    rw [RingHom.mem_ker]
    change y₀ (Ideal.Quotient.mk M (algebraMap K H x)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hPM hPx), map_zero]
  · rintro ⟨y, rfl⟩
    refine ⟨⟨RingHom.ker y.toRingHom, RingHom.ker_isPrime _⟩, ?_⟩
    ext x
    rfl

theorem faithfullyFlat_of_range_eq_univ (K : Type v) [CommRing K] (H : Type w) [CommRing H] [Algebra
    K H]
    [Module.Flat K H] (h : Set.range (PrimeSpectrum.comap (algebraMap K H)) = Set.univ) :
    Module.FaithfullyFlat K H :=
  Module.FaithfullyFlat.of_comap_surjective (Set.range_eq_univ.mp h)

end SpectrumSurjectivity

namespace SpectrumSurjectivity

variable {k : Type u} [Field k]

section Points
variable (K : Type v) [CommRing K] [HopfAlgebra k K]

/-- The canonical antipode as an algebra homomorphism. -/
noncomputable abbrev antipodeAlgHom : K →ₐ[k] K := HopfAlgebra.antipodeAlgHom k K

theorem antipodeAlgHom_apply (a : K) : antipodeAlgHom (k := k) K a = HopfAlgebra.antipode k a := rfl

theorem antipodeAlgHom_bijective : Function.Bijective (antipodeAlgHom (k := k) K) :=
  Function.Involutive.bijective (fun a => HopfAlgebra.antipode_antipode (R := k) a)

/-- Translation by an algebra-valued point. -/
noncomputable def transl (g : K →ₐ[k] k) : K →ₐ[k] K :=
  (Algebra.TensorProduct.lid k K).toAlgHom.comp
    ((Algebra.TensorProduct.map g (AlgHom.id k K)).comp (Bialgebra.comulAlgHom k K))

theorem transl_spec (g : K →ₐ[k] k) (h : K) :
    transl K g h = Algebra.TensorProduct.lid k K (Algebra.TensorProduct.map g (AlgHom.id k K)
      (Coalgebra.comul h)) :=
  rfl

variable {K}
variable {A : Type w} [CommRing A] [Algebra k A]

theorem comp_transl (g : K →ₐ[k] k) (x : K →ₐ[k] A) :
    x.comp (transl K g) = WithConv.ofConv (WithConv.toConv ((Algebra.ofId k A).comp g) *
      WithConv.toConv x) := by
  apply AlgHom.ext
  intro c
  rw [AlgHom.convMul_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv, AlgHom.comp_apply,
    transl_spec]
  induction (Coalgebra.comul (R := k) c) using TensorProduct.inductionOn with
  | tmul a b =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul,
        Algebra.TensorProduct.lift_tmul,
        map_smul, AlgHom.id_apply, AlgHom.comp_apply, Algebra.ofId_apply, Algebra.smul_def]
  | add y z hy hz => rw [map_add, map_add, map_add, hy, hz, map_add]

theorem comp_antipode_mul_self (x : K →ₐ[k] A) :
    WithConv.toConv (x.comp (antipodeAlgHom K)) * WithConv.toConv x = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro c
  rw [AlgHom.convMul_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv, AlgHom.convOne_apply]
  have h : ∀ t : K ⊗[k] K, Algebra.TensorProduct.lift (x.comp (antipodeAlgHom K)) x (fun _ _ =>
    Commute.all _ _) t
      = x (LinearMap.mul' k K (LinearMap.rTensor K (HopfAlgebra.antipode k (A := K)) t)) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      rw [Algebra.TensorProduct.lift_tmul, LinearMap.rTensor_tmul, LinearMap.mul'_apply,
        AlgHom.comp_apply, antipodeAlgHom_apply, map_mul]
    | add y z hy hz => rw [map_add, hy, hz, map_add, map_add, map_add]
  rw [h, HopfAlgebra.mul_antipode_rTensor_comul_apply, AlgHom.commutes]

theorem mul_comp_antipode_self (x : K →ₐ[k] A) :
    WithConv.toConv x * WithConv.toConv (x.comp (antipodeAlgHom K)) = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro c
  rw [AlgHom.convMul_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv, AlgHom.convOne_apply]
  have h : ∀ t : K ⊗[k] K, Algebra.TensorProduct.lift x (x.comp (antipodeAlgHom K)) (fun _ _ =>
    Commute.all _ _) t
      = x (LinearMap.mul' k K (LinearMap.lTensor K (HopfAlgebra.antipode k (A := K)) t)) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      rw [Algebra.TensorProduct.lift_tmul, LinearMap.lTensor_tmul, LinearMap.mul'_apply,
        AlgHom.comp_apply, antipodeAlgHom_apply, map_mul]
    | add y z hy hz => rw [map_add, hy, hz, map_add, map_add, map_add]
  rw [h, HopfAlgebra.mul_antipode_lTensor_comul_apply, AlgHom.commutes]

/-- The prime ideal defined by a rational point. -/
def pt (z : K →ₐ[k] k) : PrimeSpectrum K := ⟨RingHom.ker z.toRingHom, RingHom.ker_isPrime _⟩

theorem pt_isMaximal (z : K →ₐ[k] k) : (pt z).asIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective z.toRingHom (fun c => ⟨algebraMap k K c, AlgHom.commutes z c⟩)

theorem comap_pt (β : K →ₐ[k] K) (z : K →ₐ[k] k) :
    PrimeSpectrum.comap β.toRingHom (pt z) = pt (z.comp β) := by
  ext x
  rfl

end Points

theorem exists_pt_eq [IsAlgClosed k] (K : Type v) [CommRing K] [HopfAlgebra k K] [Algebra.FiniteType
    k K]
    (Q : PrimeSpectrum K) (hQ : Q.asIdeal.IsMaximal) : ∃ z : K →ₐ[k] k, pt z = Q := by
  have : Q.asIdeal.IsMaximal := hQ
  have : Nontrivial (K ⧸ Q.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr hQ.ne_top
  obtain ⟨y⟩ := exists_algHom_of_finiteType (k := k) (A := K ⧸ Q.asIdeal)
  refine ⟨y.comp (Ideal.Quotient.mkₐ k Q.asIdeal), ?_⟩
  apply PrimeSpectrum.ext
  change RingHom.ker _ = Q.asIdeal
  symm
  apply hQ.eq_of_le (RingHom.ker_ne_top _)
  intro x hx
  rw [RingHom.mem_ker]
  change y (Ideal.Quotient.mk Q.asIdeal x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

theorem exists_isMaximal_mem (K : Type v) [CommRing K] [IsJacobsonRing K] (W : Set (PrimeSpectrum
    K))
    (hW : IsOpen W) (hne : W.Nonempty) : ∃ P ∈ W, P.asIdeal.IsMaximal := by
  have h := JacobsonSpace.closure_inter_closedPoints_eq_closure (X := PrimeSpectrum K)
    hW.isLocallyClosed
  have hne' : (W ∩ closedPoints (PrimeSpectrum K)).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [hcon, closure_empty] at h
    exact hne.ne_empty (Set.eq_empty_of_subset_empty (h ▸ subset_closure))
  obtain ⟨P, hPW, hPc⟩ := hne'
  exact ⟨P, hPW, (PrimeSpectrum.isClosed_singleton_iff_isMaximal P).mp (mem_closedPoints_iff.mp
    hPc)⟩

theorem main [IsAlgClosed k]
    (K : Type v) [CommRing K] [HopfAlgebra k K] [Algebra.FiniteType k K]
    (H : Type w) [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    [Algebra K H] [IsScalarTower k K H] (hinj : Function.Injective (algebraMap K H))
    (hcomul : ∀ x : K, Coalgebra.comul (R := k) (algebraMap K H x) =
      TensorProduct.map (IsScalarTower.toAlgHom k K H).toLinearMap (IsScalarTower.toAlgHom k K
        H).toLinearMap
        (Coalgebra.comul (R := k) x))
    (hcounit : ∀ x : K, Coalgebra.counit (R := k) (algebraMap K H x) = Coalgebra.counit (R := k) x)
    [Module.Flat K H] :
    Module.FaithfullyFlat K H := by
  classical
  let ι : K →ₐ[k] H := IsScalarTower.toAlgHom k K H
  let ιb : K →ₐc[k] H :=
    BialgHom.mk
      { toLinearMap := ι.toLinearMap
        counit_comp := by ext x; exact hcounit x
        map_comp_comul := by ext x; exact (hcomul x).symm }
      (map_one ι) (map_mul ι)
  have hιb : ((ιb : K →ₐc[k] H) : K →ₐ[k] H) = ι := rfl
  let Lifts : (K →ₐ[k] k) → Prop := fun z => ∃ y : H →ₐ[k] k, y.comp ι = z
  have lifts_mul : ∀ z z', Lifts z → Lifts z' →
      Lifts (WithConv.ofConv (WithConv.toConv z * WithConv.toConv z')) := by
    rintro z z' ⟨y, rfl⟩ ⟨y', rfl⟩
    refine ⟨WithConv.ofConv (WithConv.toConv y * WithConv.toConv y'), ?_⟩
    rw [← hιb]
    exact AlgHom.convMul_comp_bialgHom_distrib (WithConv.toConv y) (WithConv.toConv y') ιb
  let U : Set (PrimeSpectrum K) := Set.range (PrimeSpectrum.comap (algebraMap K H))
  have hUopen : IsOpen U := isOpen_range_comap (k := k) K H
  have hUdense : Dense U := by
    have : DenseRange (PrimeSpectrum.comap (algebraMap K H)) :=
      (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
        (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
    exact this
  have hU_iff : ∀ z : K →ₐ[k] k, pt z ∈ U ↔ Lifts z := fun z => mem_range_comap_iff_exists_lift K H
    z
  have : IsJacobsonRing K := isJacobsonRing_of_finiteType (A := k) (B := K)
  obtain ⟨hbij, -, -⟩ :=
    HopfAlgebra.bijective_translate_and_map_mem_and_exists_comp_translate_eq (k := k) (H := K)
      (transl K) (fun g h => rfl)
  have key : ∀ z : K →ₐ[k] k, Lifts z := by
    intro z
    let β : K →ₐ[k] K := (antipodeAlgHom K).comp (transl K z)
    let V : Set (PrimeSpectrum K) := (PrimeSpectrum.comap β.toRingHom) ⁻¹' U
    have hVopen : IsOpen V := hUopen.preimage (PrimeSpectrum.continuous_comap β.toRingHom)
    have hβpt : ∀ x : K →ₐ[k] k, PrimeSpectrum.comap β.toRingHom (pt x) =
        pt (WithConv.ofConv (WithConv.toConv z * WithConv.toConv (x.comp (antipodeAlgHom K)))) := by
      intro x
      rw [comap_pt]
      congr 1
      change (x.comp (antipodeAlgHom K)).comp (transl K z) = _
      rw [comp_transl]
      congr 2
    have hzV : pt z ∈ V := by
      change PrimeSpectrum.comap β.toRingHom (pt z) ∈ U
      rw [hβpt, mul_comp_antipode_self, hU_iff]
      refine ⟨WithConv.ofConv 1, ?_⟩
      apply AlgHom.ext
      intro c
      rw [AlgHom.comp_apply, AlgHom.convOne_apply, AlgHom.convOne_apply]
      exact congrArg _ (hcounit c)
    obtain ⟨P, ⟨hPV, hPU⟩, hPmax⟩ :=
      exists_isMaximal_mem K (V ∩ U) (hVopen.inter hUopen) (hUdense.inter_open_nonempty V hVopen ⟨_,
        hzV⟩)
    obtain ⟨x, rfl⟩ := exists_pt_eq (k := k) K P hPmax
    have hx : Lifts x := (hU_iff x).mp hPU
    have hw : Lifts (WithConv.ofConv (WithConv.toConv z * WithConv.toConv (x.comp (antipodeAlgHom
      K)))) := by
      rw [← hU_iff, ← hβpt]
      exact hPV
    have := lifts_mul _ _ hw hx
    rwa [WithConv.toConv_ofConv, mul_assoc, comp_antipode_mul_self, mul_one, WithConv.ofConv_toConv]
      at this
  have hU : U = Set.univ := by
    apply PrimeSpectrum.eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal U hUopen
    · obtain ⟨y⟩ : Nonempty (K →ₐ[k] k) := by
        have : Nontrivial K := nontrivial_of_ne 1 0 (fun h10 => by
          have := congrArg (Coalgebra.counit (R := k) (A := K)) h10
          rw [Bialgebra.counit_one, map_zero] at this
          exact one_ne_zero this)
        exact exists_algHom_of_finiteType
      exact ⟨pt y, (hU_iff y).mpr (key y)⟩
    · intro P Q _ hQ _
      obtain ⟨z, rfl⟩ := exists_pt_eq (k := k) K Q hQ
      exact (hU_iff z).mpr (key z)
  exact faithfullyFlat_of_range_eq_univ K H hU

end SpectrumSurjectivity

theorem _root_.HopfAlgebra.faithfullyFlat_of_flat_of_injective_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    (K : Type v) [CommRing K] [HopfAlgebra k K] [Algebra.FiniteType k K]
    (H : Type w) [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    [Algebra K H] [IsScalarTower k K H] (hinj : Function.Injective (algebraMap K H))
    (hcomul : ∀ x : K, Coalgebra.comul (R := k) (algebraMap K H x) =
      TensorProduct.map (IsScalarTower.toAlgHom k K H).toLinearMap (IsScalarTower.toAlgHom k K
        H).toLinearMap
        (Coalgebra.comul (R := k) x))
    (hcounit : ∀ x : K, Coalgebra.counit (R := k) (algebraMap K H x) = Coalgebra.counit (R := k) x)
    [Module.Flat K H] :
    Module.FaithfullyFlat K H :=
  SpectrumSurjectivity.main K H hinj hcomul hcounit

end AbelianVarieties.NOSProofs.HopfFaithfulFlatness
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_free_subalgebra_of_isNilpotent_ker_counit.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.NilpotentHopfFreeness

open AbelianVarieties.NOSProofs.SubalgebraTensorQuotients

open scoped TensorProduct

universe u v

namespace NilpotentAugmentation

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H] (K : Subalgebra k H)

/-- The augmentation ideal of the subalgebra. -/
abbrev augK : Ideal ↥K := RingHom.ker ((Bialgebra.counitAlgHom k H).comp K.val)

/-- The ideal generated by the subalgebra augmentation ideal. -/
abbrev JH : Ideal H := Ideal.span {x : H | x ∈ K ∧ Coalgebra.counit (R := k) x = 0}

theorem mem_augK_iff (x : ↥K) : x ∈ augK K ↔ Coalgebra.counit (R := k) (x : H) = 0 := by
  rw [RingHom.mem_ker]; rfl

theorem JH_eq_map : JH K = Ideal.map (algebraMap ↥K H) (augK K) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro x ⟨hxK, hx⟩
    exact Ideal.mem_map_of_mem (algebraMap ↥K H) ((mem_augK_iff K ⟨x, hxK⟩).mpr hx)
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact Ideal.subset_span ⟨x.2, (mem_augK_iff K x).mp hx⟩

theorem restrictScalars_JH : (JH K).restrictScalars ↥K = augK K • (⊤ : Submodule ↥K H) := by
  rw [Ideal.smul_top_eq_map, ← JH_eq_map]

theorem JH_pow_eq_bot (hnil : IsNilpotent (augK K)) : ∃ n : ℕ, JH K ^ n = ⊥ := by
  obtain ⟨n, hn⟩ := hnil
  refine ⟨n, ?_⟩
  rw [JH_eq_map, ← Ideal.map_pow, hn, Submodule.zero_eq_bot, Ideal.map_bot]

theorem mk_coe_eq (x : ↥K) :
    Ideal.Quotient.mk (JH K) (x : H) = algebraMap k (H ⧸ JH K) (Coalgebra.counit (R := k) (x : H))
      :=
  TensorTorsor.π_eq_algebraMap_counit_of_mem K x.property

theorem coe_smul_quot (x : ↥K) (q : H ⧸ JH K) : x • q = Coalgebra.counit (R := k) (x : H) • q := by
  rw [Algebra.smul_def, Algebra.smul_def]
  congr 1
  exact mk_coe_eq K x

theorem eq_top_of_le_sup_smul {I : Ideal ↥K} (hI : IsNilpotent I) (N : Submodule ↥K H)
    (h : (⊤ : Submodule ↥K H) ≤ N ⊔ I • ⊤) : N = ⊤ := by
  have key : ∀ m : ℕ, (⊤ : Submodule ↥K H) ≤ N ⊔ I ^ m • ⊤ := by
    intro m
    induction m with
    | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; exact le_sup_right
    | succ m ih =>
        have h1 : I • (⊤ : Submodule ↥K H) ≤ N ⊔ I ^ (m + 1) • ⊤ := by
          calc I • (⊤ : Submodule ↥K H) ≤ I • (N ⊔ I ^ m • ⊤) := Submodule.smul_mono le_rfl ih
            _ = I • N ⊔ I ^ (m + 1) • ⊤ := by rw [Submodule.smul_sup, ← Submodule.mul_smul,
              pow_succ']
            _ ≤ N ⊔ I ^ (m + 1) • ⊤ := sup_le_sup_right Submodule.smul_le_right _
        exact h.trans (sup_le le_sup_left h1)
  obtain ⟨n, hn⟩ := hI
  have := key n
  rw [hn, Submodule.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] at this
  exact eq_top_iff.mpr this

section Core

variable {ι : Type*} (e : ι → H)

/-- The linear combination map for the chosen lifts. -/
noncomputable abbrev Λ : (ι →₀ ↥K) →ₗ[↥K] H := Finsupp.linearCombination ↥K e

theorem range_Λ_eq_top (hnil : IsNilpotent (augK K)) (b : Module.Basis ι k (H ⧸ JH K))
    (he : ∀ i, Ideal.Quotient.mk (JH K) (e i) = b i) : LinearMap.range (Λ K e) = ⊤ := by
  classical
  apply eq_top_of_le_sup_smul K hnil
  rintro h -
  let q : H →ₐ[k] H ⧸ JH K := Ideal.Quotient.mkₐ k (JH K)
  have hq : ∀ y, q y = Ideal.Quotient.mk (JH K) y := fun _ => rfl
  set c := b.repr (q h) with hc
  set h₀ : H := c.sum fun i a => a • e i with hh₀
  have hq₀ : q h₀ = q h := by
    rw [hh₀, map_finsuppSum]
    conv_rhs => rw [← b.linearCombination_repr (q h), Finsupp.linearCombination_apply]
    refine Finsupp.sum_congr fun i _ => ?_
    rw [map_smul, hq, he]
  have hdiff : h - h₀ ∈ (JH K).restrictScalars ↥K := by
    change h - h₀ ∈ JH K
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hq, map_sub, hq₀, sub_self]
  have hh₀N : h₀ ∈ LinearMap.range (Λ K e) := by
    refine ⟨c.mapRange (algebraMap k ↥K) (map_zero _), ?_⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index]
    · rw [hh₀]; exact Finsupp.sum_congr fun i _ => algebraMap_smul (↥K) (c i) (e i)
    · intro i; exact zero_smul _ _
  rw [restrictScalars_JH] at hdiff
  have : h = h₀ + (h - h₀) := by ring
  rw [this]
  exact Submodule.add_mem_sup hh₀N hdiff

/-- The scalar extension of the linear combination map. -/
noncomputable abbrev Λ' : (ι →₀ H) →ₗ[H] (H ⊗[↥K] H) :=
  Finsupp.linearCombination H (fun i => (1 : H) ⊗ₜ[↥K] e i)

theorem Λ'_surjective (hΛ : LinearMap.range (Λ K e) = ⊤) : Function.Surjective (Λ' K e) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro z -
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul h h' =>
      have hh' : h' ∈ LinearMap.range (Λ K e) := by rw [hΛ]; exact Submodule.mem_top
      obtain ⟨a, rfl⟩ := hh'
      have : h ⊗ₜ[↥K] (Λ K e a) = h • ((1 : H) ⊗ₜ[↥K] (Λ K e a)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      refine Submodule.smul_mem _ h ?_
      rw [Finsupp.linearCombination_apply, Finsupp.sum, TensorProduct.tmul_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [← TensorProduct.smul_tmul]
      have : ((a i) • (1 : H)) ⊗ₜ[↥K] e i = (algebraMap ↥K H (a i)) • ((1 : H) ⊗ₜ[↥K] e i) := by
        rw [TensorProduct.smul_tmul', Algebra.smul_def, mul_one, smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (LinearMap.mem_range.mpr ⟨Finsupp.single i 1, by rw
        [Finsupp.linearCombination_single, one_smul]⟩)

theorem mk_smul (x : ↥K) (h : H) :
    Ideal.Quotient.mk (JH K) (x • h) = Coalgebra.counit (R := k) (x : H) • Ideal.Quotient.mk (JH K)
      h := by
  rw [Algebra.smul_def, map_mul, Algebra.smul_def]
  congr 1
  exact mk_coe_eq K x

/-- The tensor map induced by the augmentation quotient. -/
noncomputable def θ : H ⊗[↥K] H →ₗ[↥K] (H ⧸ JH K) ⊗[k] (H ⧸ JH K) :=
  TensorProduct.lift
    (LinearMap.mk₂ ↥K (fun h h' => Ideal.Quotient.mk (JH K) h ⊗ₜ[k] Ideal.Quotient.mk (JH K) h')
      (fun h₁ h₂ h' => by simp only [map_add, TensorProduct.add_tmul])
      (fun x h h' => by
        rw [mk_smul, ← coe_smul_quot]
        exact (TensorProduct.smul_tmul' x _ _).symm)
      (fun h h₁ h₂ => by simp only [map_add, TensorProduct.tmul_add])
      (fun x h h' => by
        rw [mk_smul, TensorProduct.tmul_smul]
        refine ((TensorProduct.smul_tmul' x _ _).trans ?_).symm
        rw [coe_smul_quot, TensorProduct.smul_tmul']))

theorem θ_tmul (h h' : H) :
    θ K (h ⊗ₜ[↥K] h') = Ideal.Quotient.mk (JH K) h ⊗ₜ[k] Ideal.Quotient.mk (JH K) h' :=
  TensorProduct.lift.tmul _ _

theorem apply_mem_JH_of_Λ'_eq_zero (b : Module.Basis ι k (H ⧸ JH K))
    (he : ∀ i, Ideal.Quotient.mk (JH K) (e i) = b i) (m : ι →₀ H) (hm : Λ' K e m = 0) (i : ι) :
    m i ∈ JH K := by
  classical
  let Φ : (H ⧸ JH K) ⊗[k] (H ⧸ JH K) ≃ₗ[k] (ι →₀ H ⧸ JH K) :=
    (TensorProduct.congr (LinearEquiv.refl k _) b.repr).trans (TensorProduct.finsuppScalarRight k k
      (H ⧸ JH K) ι)
  have hΦ : ∀ (q : H ⧸ JH K) (j : ι), Φ (q ⊗ₜ[k] b j) = Finsupp.single j q := by
    intro q j
    simp only [Φ, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
      LinearEquiv.refl_apply, Module.Basis.repr_self, TensorProduct.finsuppScalarRight_apply_tmul,
      Finsupp.sum_single_index, one_smul, zero_smul, Finsupp.single_zero]
  have hcalc : Φ (θ K (Λ' K e m)) = m.mapRange (Ideal.Quotient.mk (JH K)) (map_zero _) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_sum]
    have : ∀ j ∈ m.support, Φ (θ K (m j • ((1 : H) ⊗ₜ[↥K] e j))) = Finsupp.single j
      (Ideal.Quotient.mk (JH K) (m j)) := by
      intro j _
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, θ_tmul, he, hΦ]
    rw [Finset.sum_congr rfl this]
    ext j
    rw [Finset.sum_apply', Finsupp.mapRange_apply]
    rw [Finset.sum_eq_single j]
    · rw [Finsupp.single_eq_same]
    · intro j' _ hj'; rw [Finsupp.single_apply, ite_eq_right hj']
    · intro hj; rw [Finsupp.single_eq_same, Finsupp.notMem_support_iff.mp hj, map_zero]
  rw [hm, map_zero, map_zero] at hcalc
  have := DFunLike.congr_fun hcalc.symm i
  rw [Finsupp.mapRange_apply, Finsupp.zero_apply] at this
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

theorem ker_Λ'_eq_bot
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hnil : IsNilpotent (augK K)) (b : Module.Basis ι k (H ⧸ JH K))
    (he : ∀ i, Ideal.Quotient.mk (JH K) (e i) = b i) : LinearMap.ker (Λ' K e) = ⊥ := by
  classical
  obtain ⟨β, -⟩ := HopfAlgebra.exists_algEquiv_subalgebraTensor_tensorQuotient_of_comul_mem_span K
    hΔ
  have : Module.Free H (H ⊗[k] (H ⧸ JH K)) := Module.Free.of_basis (Algebra.TensorProduct.basis H b)
  have : Module.Projective H (H ⊗[↥K] H) := Module.Projective.of_equiv β.toLinearEquiv.symm
  have hsurj : Function.Surjective (Λ' K e) := Λ'_surjective K e (range_Λ_eq_top K e hnil b he)
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (Λ' K e) LinearMap.id hsurj
  set M := LinearMap.ker (Λ' K e) with hM
  let p : (ι →₀ H) →ₗ[H] (ι →₀ H) := LinearMap.id - σ ∘ₗ (Λ' K e)
  have hp_mem : ∀ v, p v ∈ M := by
    intro v
    rw [hM, LinearMap.mem_ker]
    change Λ' K e (v - σ (Λ' K e v)) = 0
    rw [map_sub, ← LinearMap.comp_apply, hσ, LinearMap.id_apply, sub_self]
  have hp_fix : ∀ v ∈ M, p v = v := by
    intro v hv
    change v - σ (Λ' K e v) = v
    rw [LinearMap.mem_ker.mp hv, map_zero, sub_zero]
  have hMJ : M ≤ (JH K) • M := by
    intro v hv
    have hvJ : v ∈ (JH K) • (⊤ : Submodule H (ι →₀ H)) := by
      have hv' : v = v.sum fun i a => a • Finsupp.single i (1 : H) := by
        conv_lhs => rw [← Finsupp.sum_single v]
        exact Finsupp.sum_congr fun i _ => by rw [Finsupp.smul_single_one]
      rw [hv']
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
      exact apply_mem_JH_of_Λ'_eq_zero K e b he v (LinearMap.mem_ker.mp hv) i
    have h1 : p v ∈ Submodule.map p ((JH K) • ⊤) := Submodule.mem_map_of_mem hvJ
    rw [Submodule.map_smul'', hp_fix v hv] at h1
    refine Submodule.smul_mono le_rfl ?_ h1
    rintro _ ⟨w, -, rfl⟩
    exact hp_mem w
  have hiter : ∀ j : ℕ, M ≤ (JH K) ^ j • M := by
    intro j
    induction j with
    | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    | succ j ih =>
        calc M ≤ (JH K) ^ j • M := ih
          _ ≤ (JH K) ^ j • ((JH K) • M) := Submodule.smul_mono le_rfl hMJ
          _ = (JH K) ^ (j + 1) • M := by rw [← Submodule.mul_smul, ← pow_succ]
  obtain ⟨n, hn⟩ := JH_pow_eq_bot K hnil
  have := hiter n
  rw [hn, Submodule.bot_smul] at this
  exact le_bot_iff.mp this

theorem Λ_injective
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hnil : IsNilpotent (augK K)) (b : Module.Basis ι k (H ⧸ JH K))
    (he : ∀ i, Ideal.Quotient.mk (JH K) (e i) = b i) : Function.Injective (Λ K e) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  let a' : ι →₀ H := a.mapRange (algebraMap ↥K H) (map_zero _)
  have ha' : Λ' K e a' = (1 : H) ⊗ₜ[↥K] Λ K e a := by
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index]
    · rw [Finsupp.sum, Finsupp.sum, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.smul_tmul', algebraMap_smul, TensorProduct.smul_tmul]
    · intro i; exact zero_smul _ _
  have hker : a' ∈ LinearMap.ker (Λ' K e) := by
    rw [LinearMap.mem_ker, ha', ha, TensorProduct.tmul_zero]
  rw [ker_Λ'_eq_bot K e hΔ hnil b he, Submodule.mem_bot] at hker
  apply Finsupp.ext
  intro i
  have := DFunLike.congr_fun hker i
  rw [Finsupp.mapRange_apply, Finsupp.zero_apply] at this
  apply Subtype.ext
  change (algebraMap ↥K H) (a i) = 0
  exact this

end Core

end NilpotentAugmentation

open NilpotentAugmentation in
theorem _root_.HopfAlgebra.free_subalgebra_of_isNilpotent_ker_counit
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (_hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K)
    (hnil : IsNilpotent (RingHom.ker ((Bialgebra.counitAlgHom k H).comp K.val))) :
    Module.Free ↥K H := by
  classical
  let b := Module.Free.chooseBasis k (H ⧸ JH K)
  have hsurj := Ideal.Quotient.mk_surjective (I := JH K)
  let e : Module.Free.ChooseBasisIndex k (H ⧸ JH K) → H := fun i => (hsurj (b i)).choose
  have he : ∀ i, Ideal.Quotient.mk (JH K) (e i) = b i := fun i => (hsurj (b i)).choose_spec
  have hbij : Function.Bijective (Λ K e) :=
    ⟨Λ_injective K e hΔ hnil b he, LinearMap.range_eq_top.mp (range_Λ_eq_top K e hnil b he)⟩
  exact Module.Free.of_equiv (LinearEquiv.ofBijective (Λ K e) hbij)

end AbelianVarieties.NOSProofs.NilpotentHopfFreeness
end
